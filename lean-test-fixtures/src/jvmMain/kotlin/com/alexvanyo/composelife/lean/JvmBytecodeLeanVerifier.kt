/*
 * Copyright 2026 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.alexvanyo.composelife.lean

import java.nio.file.Files
import java.nio.file.Path
import java.security.MessageDigest
import java.util.HexFormat
import java.util.concurrent.ConcurrentHashMap
import kotlin.io.path.exists
import kotlin.io.path.writeBytes
import kotlin.io.path.writeText
import kotlin.test.assertEquals
import kotlin.test.assertTrue

/**
 * Configuration describing a compiled JVM class resource and Lean verification context for a Gradle module.
 */
data class JvmBytecodeVerificationSpec(
    val moduleDirName: String,
    val classResourcePath: String,
    val semanticsImport: String = "JvmSemantics",
    val realBytecodeNamespace: String,
    val instrType: String,
    val requiredProgs: List<String>,
    val defaultImports: List<String>,
    val defaultOpens: List<String>,
    val extraClassResourcePaths: List<String> = emptyList(),
)

data class LeanTheoremExtras(val extraImports: List<String> = emptyList(), val extraOpens: List<String> = emptyList())

/**
 * Convenience helper for JUnit/kotlin.test classes to verify a theorem against the bytecode of [spec].
 */
fun JvmBytecodeVerificationSpec.verifyTheorem(
    ownerClass: Class<*>,
    theoremName: String,
    leanBody: String,
    extraImports: List<String> = emptyList(),
    extraOpens: List<String> = emptyList(),
) {
    JvmBytecodeLeanVerifier.verifyBytecodeTheorem(
        spec = this,
        classLoader = ownerClass.classLoader,
        theoremName = theoremName,
        leanBody = leanBody,
        extras = LeanTheoremExtras(extraImports = extraImports, extraOpens = extraOpens),
    )
}

/**
 * Reusable test harness that lifts live compiled `.class` bytecode from the JVM test runtime classpath into
 * Lean 4 via `script/jvm-bytecode2lean.py`, compiles it, verifies arbitrary theorems against the real bytecode
 * with `lake env lean -DwarningAsError=true`, and audits axioms cleanly.
 */
object JvmBytecodeLeanVerifier {
    private data class CompiledBytecodeCacheKey(
        val leanDir: Path,
        val moduleDirName: String,
        val classResourcePaths: List<String>,
        val semanticsImport: String,
        val realBytecodeNamespace: String,
        val instrType: String,
        val requiredProgs: List<String>,
        val classSha256: String,
    )

    private data class TheoremCheckRequest(
        val spec: JvmBytecodeVerificationSpec,
        val leanDir: Path,
        val leanEnv: Map<String, String>,
        val tempDir: Path,
        val theoremName: String,
        val leanBody: String,
        val extraImports: List<String>,
        val extraOpens: List<String>,
    )

    private val baseLeanPathCache = ConcurrentHashMap<Path, String>()
    private val compiledBytecodeCache = ConcurrentHashMap<CompiledBytecodeCacheKey, Path>()

    /**
     * Lifts the compiled JVM `.class` described by [spec] using [classLoader], compiles it to an `.olean`,
     * proves [theoremName] defined in [leanBody] directly against the lifted `RealJvmBytecode`, and verifies
     * that only standard Lean or SAT-certified `bv_decide` LRAT axioms are used.
     */
    fun verifyBytecodeTheorem(
        spec: JvmBytecodeVerificationSpec,
        classLoader: ClassLoader,
        theoremName: String,
        leanBody: String,
        extras: LeanTheoremExtras = LeanTheoremExtras(),
    ) {
        validateLeanBody(theoremName = theoremName, leanBody = leanBody)
        val repoRoot = findRepoRoot(spec.moduleDirName)
        val leanDir = repoRoot.resolve("${spec.moduleDirName}/lean").toAbsolutePath().normalize()
        val allResourcePaths = listOf(spec.classResourcePath) + spec.extraClassResourcePaths
        val classEntries = allResourcePaths.map { path ->
            path to readCompiledClassBytes(
                classLoader = classLoader,
                classResourcePath = path,
            )
        }
        val bytecodeLibDir = getOrCompileRealBytecodeLibDir(
            repoRoot = repoRoot,
            leanDir = leanDir,
            spec = spec,
            classEntries = classEntries,
        )
        val leanEnv = buildLeanEnv(
            repoRoot = repoRoot,
            leanDir = leanDir,
            moduleDirName = spec.moduleDirName,
            bytecodeLibDir = bytecodeLibDir,
        )
        val tempDir = Files.createTempDirectory("composelife-jvm-verify-")
        try {
            val verifyOutput = checkTheoremFile(
                TheoremCheckRequest(
                    spec = spec,
                    leanDir = leanDir,
                    leanEnv = leanEnv,
                    tempDir = tempDir,
                    theoremName = theoremName,
                    leanBody = leanBody,
                    extraImports = extras.extraImports,
                    extraOpens = extras.extraOpens,
                ),
            )
            assertAxiomsAreStandard(
                theoremName = theoremName,
                leanOutput = verifyOutput,
            )
        } finally {
            tempDir.toFile().deleteRecursively()
        }
    }

    private fun getOrCompileRealBytecodeLibDir(
        repoRoot: Path,
        leanDir: Path,
        spec: JvmBytecodeVerificationSpec,
        classEntries: List<Pair<String, ByteArray>>,
    ): Path {
        val digest = MessageDigest.getInstance("SHA-256")
        classEntries.forEach { (path, bytes) ->
            digest.update(path.toByteArray())
            digest.update(0)
            digest.update(bytes)
        }
        val cacheKey = CompiledBytecodeCacheKey(
            leanDir = leanDir,
            moduleDirName = spec.moduleDirName,
            classResourcePaths = classEntries.map { it.first },
            semanticsImport = spec.semanticsImport,
            realBytecodeNamespace = spec.realBytecodeNamespace,
            instrType = spec.instrType,
            requiredProgs = spec.requiredProgs,
            classSha256 = HexFormat.of().formatHex(digest.digest()),
        )
        return compiledBytecodeCache.computeIfAbsent(cacheKey) {
            val cacheDir = Files.createTempDirectory("composelife-jvm-bytecode-cache-")
            Runtime.getRuntime().addShutdownHook(Thread { cacheDir.toFile().deleteRecursively() })
            val liftedLeanFile = liftClassToLean(
                repoRoot = repoRoot,
                spec = spec,
                workDir = cacheDir,
                classEntries = classEntries,
            )
            val libDir = cacheDir.resolve("lib")
            Files.createDirectories(libDir)
            val leanEnv = buildLeanEnv(
                repoRoot = repoRoot,
                leanDir = leanDir,
                moduleDirName = spec.moduleDirName,
                bytecodeLibDir = libDir,
            )
            compileRealBytecodeOlean(
                leanDir = leanDir,
                leanEnv = leanEnv,
                rootDir = cacheDir,
                libDir = libDir,
                liftedLeanFile = liftedLeanFile,
            )
            libDir
        }
    }

    private fun liftClassToLean(
        repoRoot: Path,
        spec: JvmBytecodeVerificationSpec,
        workDir: Path,
        classEntries: List<Pair<String, ByteArray>>,
    ): Path {
        val scriptPath = repoRoot.resolve("script/jvm-bytecode2lean.py")
        val classesDir = workDir.resolve("classes")
        val classFiles = classEntries.map { (path, bytes) ->
            classesDir.resolve(path).also { classFile ->
                Files.createDirectories(classFile.parent)
                classFile.writeBytes(bytes)
            }
        }
        val liftedLeanFile = workDir.resolve("RealJvmBytecode.lean")
        val liftCommand = buildList {
            add("python3")
            add(scriptPath.toString())
            classFiles.forEach { classFile ->
                add("--class-file")
                add(classFile.toString())
            }
            add("--import")
            add(spec.semanticsImport)
            add("--namespace")
            add(spec.realBytecodeNamespace)
            add("--instr-type")
            add(spec.instrType)
            spec.requiredProgs.forEach { prog ->
                add("--require")
                add(prog)
            }
            add("-o")
            add(liftedLeanFile.toString())
        }
        val liftOutput = runProcess(workingDir = repoRoot, command = liftCommand)
        assertTrue(
            Files.exists(liftedLeanFile),
            "Expected lifted bytecode Lean file at $liftedLeanFile.\n$liftOutput",
        )
        return liftedLeanFile
    }

    private fun buildLeanEnv(
        repoRoot: Path,
        leanDir: Path,
        moduleDirName: String,
        bytecodeLibDir: Path,
    ): Map<String, String> {
        val baseLeanPath = baseLeanPathCache.computeIfAbsent(leanDir) {
            runProcess(
                workingDir = leanDir,
                command = listOf("lake", "env", "printenv", "LEAN_PATH"),
            ).trim()
        }
        val combinedLeanPath = listOf(
            bytecodeLibDir.toString(),
            leanDir.resolve(".lake/build/lib/lean").toString(),
            repoRoot.resolve("$moduleDirName/build/generated/lean/jvm").toString(),
            baseLeanPath,
        ).filter { it.isNotEmpty() }.joinToString(":")
        return mapOf("LEAN_PATH" to combinedLeanPath)
    }

    private fun compileRealBytecodeOlean(
        leanDir: Path,
        leanEnv: Map<String, String>,
        rootDir: Path,
        libDir: Path,
        liftedLeanFile: Path,
    ) {
        runProcess(
            workingDir = leanDir,
            env = leanEnv,
            command = listOf(
                "lake",
                "env",
                "lean",
                "-DwarningAsError=true",
                "-j",
                "2",
                "-M",
                "4096",
                "--root=$rootDir",
                "-o",
                libDir.resolve("RealJvmBytecode.olean").toString(),
                liftedLeanFile.toString(),
            ),
        )
    }

    private fun checkTheoremFile(request: TheoremCheckRequest): String {
        val theoremFile = request.tempDir.resolve("VerifyTheorem.lean")
        val imports = (
            listOf("Jvm.Audit") +
                request.spec.defaultImports +
                request.extraImports +
                "RealJvmBytecode"
            ).distinct()
        val opens = (request.spec.defaultOpens + request.extraOpens).distinct()
        val theoremSource = buildString {
            imports.forEach { appendLine("import $it") }
            appendLine()
            opens.forEach { appendLine("open $it") }
            if (opens.isNotEmpty()) {
                appendLine()
            }
            appendLine(request.leanBody.trimEnd())
            appendLine()
            appendLine(buildKernelAxiomAuditSnippet(spec = request.spec, theoremName = request.theoremName))
            appendLine("#print axioms ${request.theoremName}")
        }
        theoremFile.writeText(theoremSource)
        return runProcess(
            workingDir = request.leanDir,
            env = request.leanEnv,
            command = listOf(
                "lake",
                "env",
                "lean",
                "-DwarningAsError=true",
                "-j",
                "2",
                "-M",
                "4096",
                theoremFile.toString(),
            ),
        )
    }
}

private fun readCompiledClassBytes(classLoader: ClassLoader, classResourcePath: String): ByteArray {
    val stream = classLoader.getResourceAsStream(classResourcePath)
    requireNotNull(stream) {
        "Could not locate compiled bytecode resource '$classResourcePath' on the test classpath."
    }
    val bytes = stream.use { it.readBytes() }
    val magic = byteArrayOf(0xCA.toByte(), 0xFE.toByte(), 0xBA.toByte(), 0xBE.toByte())
    assertTrue(
        bytes.size >= magic.size && bytes.copyOfRange(0, magic.size).contentEquals(magic),
        "Resource '$classResourcePath' does not have a valid JVM 0xCAFEBABE header.",
    )
    return bytes
}

private fun findRepoRoot(moduleDirName: String): Path {
    var current: Path? = Path.of(System.getProperty("user.dir")).toAbsolutePath()
    while (current != null) {
        if (current.resolve("script/jvm-bytecode2lean.py").exists() &&
            current.resolve("$moduleDirName/lean/lakefile.toml").exists()
        ) {
            return current
        }
        current = current.parent
    }
    error("Unable to locate repository root containing script/jvm-bytecode2lean.py and $moduleDirName/lean.")
}

private fun runProcess(workingDir: Path, command: List<String>, env: Map<String, String> = emptyMap()): String {
    val processBuilder = ProcessBuilder(command)
        .directory(workingDir.toFile())
        .redirectErrorStream(true)
    processBuilder.environment().putAll(env)
    val process = processBuilder.start()
    val output = process.inputStream.bufferedReader().readText()
    val exitCode = process.waitFor()
    assertEquals(
        0,
        exitCode,
        "Command `${command.joinToString(" ")}` in $workingDir failed with exit code $exitCode:\n$output",
    )
    return output
}
