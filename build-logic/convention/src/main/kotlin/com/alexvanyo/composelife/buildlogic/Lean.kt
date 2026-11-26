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

package com.alexvanyo.composelife.buildlogic

import org.gradle.api.Action
import org.gradle.api.DefaultTask
import org.gradle.api.Named
import org.gradle.api.NamedDomainObjectContainer
import org.gradle.api.file.ConfigurableFileCollection
import org.gradle.api.file.DirectoryProperty
import org.gradle.api.file.RegularFileProperty
import org.gradle.api.model.ObjectFactory
import org.gradle.api.provider.ListProperty
import org.gradle.api.provider.MapProperty
import org.gradle.api.provider.Property
import org.gradle.api.tasks.Input
import org.gradle.api.tasks.InputDirectory
import org.gradle.api.tasks.InputFile
import org.gradle.api.tasks.InputFiles
import org.gradle.api.tasks.Internal
import org.gradle.api.tasks.Optional
import org.gradle.api.tasks.OutputDirectory
import org.gradle.api.tasks.OutputFile
import org.gradle.api.tasks.PathSensitive
import org.gradle.api.tasks.PathSensitivity
import org.gradle.api.tasks.TaskAction
import org.gradle.process.ExecOperations
import org.gradle.work.DisableCachingByDefault
import java.io.File
import javax.inject.Inject

abstract class LeanExtension @Inject constructor(objects: ObjectFactory) {
    abstract val target: Property<String>

    abstract val packageName: Property<String>

    abstract val leanDirectory: DirectoryProperty

    abstract val leanBinary: Property<String>

    abstract val kotlinBytecodeClassPaths: ListProperty<String>

    /**
     * Hand-written Kotlin methods (`<internal class name>.<method>`) that are known not to lift into the verified
     * instruction subset. Every other method in [kotlinBytecodeClassPaths] must lift, and every listed method must
     * still exist and still fail to lift, so this list is an explicit, reviewed record of unverified bytecode.
     */
    abstract val kotlinBytecodeUnliftedMethods: ListProperty<String>

    val entries: NamedDomainObjectContainer<LeanCodegenEntry> =
        objects.domainObjectContainer(LeanCodegenEntry::class.java)

    fun entries(action: Action<NamedDomainObjectContainer<LeanCodegenEntry>>) {
        action.execute(entries)
    }
}

abstract class LeanCodegenEntry @Inject constructor(private val name: String) : Named {
    override fun getName(): String = name

    abstract val leanFile: Property<String>

    abstract val outputFile: RegularFileProperty

    abstract val packageName: Property<String>

    /**
     * Whether to pass `compiler.kotlin.typedArrays` when generating. It must match the `set_option` of the Lean
     * file (and of the modules it uses with primitive arrays): the backend reads the option from the command line
     * for signatures, and from the file for function bodies.
     */
    abstract val typedArrays: Property<Boolean>
}

data class LeanEntrySpec(
    val leanFile: String,
    val outputFile: String,
    val packageName: String,
    val typedArrays: Boolean,
) : java.io.Serializable

@DisableCachingByDefault(because = "Downloads external cache from Lake")
abstract class CacheLeanTask @Inject constructor(private val execOperations: ExecOperations) : DefaultTask() {
    @get:Internal
    abstract val workingDir: DirectoryProperty

    @TaskAction
    fun cache() {
        execOperations.exec {
            workingDir = this@CacheLeanTask.workingDir.get().asFile
            commandLine("lake", "exe", "cache", "get")
            isIgnoreExitValue = true
        }
    }
}

@DisableCachingByDefault(because = "Lake verification handles its own caching")
abstract class VerifyLeanTask @Inject constructor(private val execOperations: ExecOperations) : DefaultTask() {
    @get:Internal
    abstract val workingDir: DirectoryProperty

    @get:PathSensitive(PathSensitivity.RELATIVE)
    @get:InputFiles
    abstract val leanFiles: ConfigurableFileCollection

    @get:Input
    abstract val target: Property<String>

    @get:OutputFile
    abstract val stampFile: RegularFileProperty

    init {
        // The real outputs are Lake's `.lake/build` artifacts, which are too large to snapshot and are also written
        // by the bytecode tasks. Only trust the stamp while Lake's build of the target still exists, so a
        // `lake clean` (or deleted `.lake`) reruns `lake build` instead of leaving later tasks with missing oleans.
        outputs.upToDateWhen { lakeBuildArtifactsPresent() }
    }

    private fun lakeBuildArtifactsPresent(): Boolean {
        val libDir = File(workingDir.get().asFile, ".lake/build/lib")
        val libLeanDir = File(libDir, "lean")
        if (libLeanDir.listFiles { file -> file.extension == "olean" }.isNullOrEmpty()) return false
        val (libName, facet) = target.get().split(':', limit = 2).let { it[0] to it.getOrNull(1) }
        return facet != "static" || libDir.listFiles()?.any { it.name.endsWith("_$libName.a") } == true
    }

    @TaskAction
    fun verify() {
        execOperations.exec {
            workingDir = this@VerifyLeanTask.workingDir.get().asFile
            commandLine("lake", "build", "--wfail", target.get())
        }
        val stamp = stampFile.get().asFile
        stamp.parentFile.mkdirs()
        stamp.writeText("${target.get()}\n")
    }
}

@DisableCachingByDefault(because = "Lean compiler handles its own compilation caching")
abstract class GenerateLeanKotlinTask @Inject constructor(private val execOperations: ExecOperations) : DefaultTask() {
    @get:PathSensitive(PathSensitivity.RELATIVE)
    @get:InputFiles
    abstract val leanFiles: ConfigurableFileCollection

    @get:Input
    abstract val leanBinary: Property<String>

    @get:Internal
    abstract val workingDir: DirectoryProperty

    @get:Input
    abstract val packageName: Property<String>

    @get:Input
    abstract val entries: MapProperty<String, LeanEntrySpec>

    @get:OutputDirectory
    abstract val generatedSourcesDir: DirectoryProperty

    @TaskAction
    fun generate() {
        val outDir = generatedSourcesDir.get().asFile
        if (outDir.exists()) {
            outDir.deleteRecursively()
        }
        outDir.mkdirs()

        val configuredEntries = entries.get()
        if (configuredEntries.isEmpty()) {
            return
        }

        val binary = File(leanBinary.get())
        check(binary.exists() && binary.canExecute()) {
            "Lean binary not found or not executable at '${binary.absolutePath}'. " +
                "Please set the 'leanBinary' Gradle property, LEAN_BINARY environment variable, " +
                "or run ./script/build-custom-lean.sh to build the custom Lean compiler (branch av/jvm)."
        }

        val workDir = workingDir.get().asFile
        val leanPath = File(workDir, ".lake/build/lib/lean").absolutePath

        configuredEntries.forEach { (_, spec) ->
            val outFile = File(spec.outputFile)
            outFile.parentFile.mkdirs()
            execOperations.exec {
                workingDir = workDir
                environment("LEAN_PATH", leanPath)
                commandLine(
                    leanBinary.get(),
                    "-j",
                    "2",
                    "-M",
                    "4096",
                    "-DwarningAsError=true",
                    "-Dcompiler.kotlin.pruneUnreachable=true",
                    "-Dcompiler.kotlin.package=${spec.packageName}",
                    "-Dcompiler.kotlin.typedArrays=${spec.typedArrays}",
                    "-K",
                    outFile.absolutePath,
                    spec.leanFile,
                )
            }
        }
    }
}

@DisableCachingByDefault(because = "Generated Kotlin check runs during build verification")
abstract class CheckLeanGeneratedKotlinTask : DefaultTask() {
    @get:PathSensitive(PathSensitivity.RELATIVE)
    @get:InputDirectory
    abstract val generatedSourcesDir: DirectoryProperty

    @get:Input
    abstract val expectOutputs: Property<Boolean>

    @get:OutputFile
    abstract val stampFile: RegularFileProperty

    @TaskAction
    fun check() {
        val dir = generatedSourcesDir.get().asFile
        val ktFiles = if (dir.exists()) {
            dir.walkTopDown().filter { it.extension == "kt" }.toList()
        } else {
            emptyList()
        }
        if (expectOutputs.getOrElse(true)) {
            check(ktFiles.isNotEmpty()) {
                "Expected generated Kotlin files in $dir, but found none."
            }
        }
        val forbiddenPatterns = listOf(
            "BigInteger",
            "java.math",
            "import java.math",
        )
        for (file in ktFiles) {
            val content = file.readText()
            for (pattern in forbiddenPatterns) {
                if (content.contains(pattern)) {
                    error(
                        "Lean generated file ${file.name} violates formalization Rule R3: " +
                            "Production Lean code must use fixed-width types and never emit '$pattern'.",
                    )
                }
            }
        }
        val stamp = stampFile.get().asFile
        stamp.parentFile.mkdirs()
        stamp.writeText("checked ${ktFiles.size} file(s)\n")
    }
}

@DisableCachingByDefault(because = "Hygiene check runs during build verification")
abstract class CheckLeanBuildScriptHygieneTask : DefaultTask() {
    @get:PathSensitive(PathSensitivity.RELATIVE)
    @get:InputFile
    abstract val buildFile: RegularFileProperty

    @TaskAction
    fun check() {
        val content = buildFile.get().asFile.readText()
        val forbiddenTokens = listOf(
            "footerFile",
            "preambleFile",
            "-Dcompiler.kotlin.footer_file",
            "-Dcompiler.kotlin.preamble_file",
        )
        for (token in forbiddenTokens) {
            if (content.contains(token)) {
                error(
                    "Build script ${buildFile.get().asFile.name} violates formalization Rule R2: " +
                        "Found '$token'. Verbatim Kotlin code must not be constructed in build scripts.",
                )
            }
        }
    }
}

/**
 * Fails if a Lean source uses `bv_decide` or `bv_decide?` as a tactic, or declares an axiom.
 *
 * Bit-level proofs are committed as `bv_check` with a stored LRAT certificate (see `script/lean-bv-check.py`), so
 * builds never rerun the SAT solver. Both tactics add the same axioms as `bv_check`, so the axiom audit cannot tell
 * them apart. The audit accepts those axioms by their name and statement, which a hand-written `axiom` could copy;
 * rejecting `axiom` declarations leaves the tactic as the only way to add one.
 */
@DisableCachingByDefault(because = "Scanning the sources is cheaper than caching the result")
abstract class CheckLeanBvCheckTask : DefaultTask() {
    @get:PathSensitive(PathSensitivity.RELATIVE)
    @get:InputFiles
    abstract val leanFiles: ConfigurableFileCollection

    @get:OutputFile
    abstract val stampFile: RegularFileProperty

    @TaskAction
    fun check() {
        val tactic = Regex("""(?<![`.\w])bv_decide\??(?![`.\w])""")
        val axiom = Regex("""(?<![`.\w])axiom(?![`.\w])""")
        val files = leanFiles.files.sortedBy { it.path }
        val strippedByFile = files.map { file ->
            file to stripLeanCommentsAndStrings(file.readText()).lines()
        }
        fun matches(regex: Regex) = strippedByFile.flatMap { (file, lines) ->
            lines.withIndex()
                .filter { (_, line) -> regex.containsMatchIn(line) }
                .map { (index, line) -> "${file.path}:${index + 1}: ${line.trim()}" }
        }
        val uses = matches(tactic)
        if (uses.isNotEmpty()) {
            error(
                "Lean sources use bv_decide; replace it with bv_check of a stored certificate " +
                    "(run script/lean-bv-check.py on bv_decide?):\n" + uses.joinToString("\n"),
            )
        }
        val axioms = matches(axiom)
        if (axioms.isNotEmpty()) {
            error("Lean sources declare axioms, which master theorems may not depend on:\n" + axioms.joinToString("\n"))
        }
        val stamp = stampFile.get().asFile
        stamp.parentFile.mkdirs()
        stamp.writeText("scanned ${files.size} file(s)\n")
    }

    private fun stripLeanCommentsAndStrings(source: String): String = stripLeanCommentsAndStringsImpl(source)
}

private fun stripLeanCommentsAndStringsImpl(source: String): String {
    val out = StringBuilder(source.length)
    var i = 0
    while (i < source.length) {
        i = when {
            source.startsWith("--", i) -> skipLineComment(source, i, out)

            source.startsWith("/-", i) -> skipBlockComment(source, i, out)

            source.startsWith("'\\\"'", i) || source.startsWith("'\"'", i) -> {
                val len = if (source[i + 1] == '\\') 4 else 3
                repeat(len) { out.append(' ') }
                i + len
            }

            source[i] == '"' -> skipDoubleQuotedString(source, i, out)

            else -> {
                out.append(source[i])
                i + 1
            }
        }
    }
    return out.toString()
}

private fun skipLineComment(source: String, start: Int, out: StringBuilder): Int {
    var i = start
    while (i < source.length && source[i] != '\n') {
        out.append(' ')
        i++
    }
    return i
}

private fun skipBlockComment(source: String, start: Int, out: StringBuilder): Int {
    var i = start + 2
    var depth = 1
    out.append("  ")
    while (i < source.length && depth > 0) {
        when {
            source.startsWith("/-", i) -> {
                depth++
                out.append("  ")
                i += 2
            }

            source.startsWith("-/", i) -> {
                depth--
                out.append("  ")
                i += 2
            }

            else -> {
                out.append(if (source[i] == '\n') '\n' else ' ')
                i++
            }
        }
    }
    return i
}

private fun skipDoubleQuotedString(source: String, start: Int, out: StringBuilder): Int {
    out.append(' ')
    var i = start + 1
    while (i < source.length) {
        val ch = source[i]
        if (ch == '\\' && i + 1 < source.length) {
            out.append(' ')
            out.append(if (source[i + 1] == '\n') '\n' else ' ')
            i += 2
        } else {
            out.append(if (ch == '\n' && ch != '"') '\n' else ' ')
            i++
            if (ch == '"') {
                break
            }
        }
    }
    return i
}

@DisableCachingByDefault(because = "JVM bytecode verification runs Lean verification on compiled .class outputs")
abstract class VerifyLeanJvmBytecodeTask @Inject constructor(private val execOperations: ExecOperations) :
    DefaultTask() {
    @get:Internal
    abstract val workingDir: DirectoryProperty

    @get:PathSensitive(PathSensitivity.RELATIVE)
    @get:InputFiles
    abstract val leanFiles: ConfigurableFileCollection

    @get:PathSensitive(PathSensitivity.RELATIVE)
    @get:InputFile
    abstract val scriptFile: RegularFileProperty

    @get:Optional
    @get:PathSensitive(PathSensitivity.RELATIVE)
    @get:InputFiles
    abstract val classFiles: ConfigurableFileCollection

    @get:Optional
    @get:PathSensitive(PathSensitivity.RELATIVE)
    @get:InputFiles
    abstract val kotlinClassFiles: ConfigurableFileCollection

    /** The configured `kotlinBytecodeClassPaths` (relative to [desktopClassesDir]); each must exist. */
    @get:Input
    abstract val kotlinClassPathSpecs: ListProperty<String>

    @get:Internal
    abstract val desktopClassesDir: DirectoryProperty

    @get:Input
    abstract val kotlinUnliftedMethods: ListProperty<String>

    @get:Input
    abstract val moduleNamespace: Property<String>

    @get:OutputDirectory
    abstract val generatedBytecodeDir: DirectoryProperty

    @get:OutputFile
    abstract val stampFile: RegularFileProperty

    private data class BytecodeTargetSpec(
        val classFilesToLift: List<File>,
        val bytecodeOutDir: File,
        val leanFileName: String,
        val oleanRelativePath: String,
        val leanNamespace: String,
        val instrType: String,
        val qualifyNames: Boolean,
        val allowedUnlifted: List<String>,
        val proofsSubdirName: String,
        val rootProofFile: String,
        val workDir: File,
    )

    /** Fails when a configured class is missing, rather than silently lifting (and verifying) fewer classes. */
    private fun checkConfiguredClassesExist() {
        val missingClassFiles = classFiles.files.filterNot { it.isFile }
        check(missingClassFiles.isEmpty()) {
            "Expected compiled Lean-generated JVM classes are missing: $missingClassFiles"
        }
        val classesRoot = desktopClassesDir.get().asFile
        val missingKotlinPaths = kotlinClassPathSpecs.get().filter { classPath ->
            val file = File(classesRoot, classPath)
            if (classPath.endsWith("/")) {
                file.walkTopDown().none { it.isFile && it.extension == "class" }
            } else {
                !file.isFile
            }
        }
        check(missingKotlinPaths.isEmpty()) {
            "kotlinBytecodeClassPaths entries match no compiled classes under $classesRoot: $missingKotlinPaths"
        }
    }

    @TaskAction
    fun verify() {
        checkConfiguredClassesExist()
        val existingClassFiles = classFiles.files.sortedBy { it.path }
        val existingKotlinClassFiles = kotlinClassFiles.files.filter { it.isFile }.sortedBy { it.path }
        check(existingClassFiles.isNotEmpty() || existingKotlinClassFiles.isNotEmpty()) {
            "Expected compiled JVM .class files in either classFiles (${classFiles.files}) " +
                "or kotlinClassFiles (${kotlinClassFiles.files}), but found none."
        }

        val workDir = workingDir.get().asFile
        val bytecodeOutDir = generatedBytecodeDir.get().asFile
        bytecodeOutDir.mkdirs()
        val ns = moduleNamespace.get()

        if (existingClassFiles.isNotEmpty()) {
            verifyBytecodeTarget(
                BytecodeTargetSpec(
                    classFilesToLift = existingClassFiles,
                    bytecodeOutDir = bytecodeOutDir,
                    leanFileName = "JvmBytecode.lean",
                    oleanRelativePath = ".lake/build/lib/lean/JvmBytecode.olean",
                    leanNamespace = "$ns.JvmBytecode",
                    instrType = "$ns.JvmVerification.JvmInstr",
                    qualifyNames = false,
                    allowedUnlifted = emptyList(),
                    proofsSubdirName = "JvmEquiv",
                    rootProofFile = "proofs/JvmEquiv.lean",
                    workDir = workDir,
                ),
            )
        }

        if (existingKotlinClassFiles.isNotEmpty()) {
            verifyBytecodeTarget(
                BytecodeTargetSpec(
                    classFilesToLift = existingKotlinClassFiles,
                    bytecodeOutDir = bytecodeOutDir,
                    leanFileName = "KotlinJvmBytecode.lean",
                    oleanRelativePath = ".lake/build/lib/lean/KotlinJvmBytecode.olean",
                    leanNamespace = "$ns.KotlinJvmBytecode",
                    instrType = "$ns.JvmVerification.JvmInstr",
                    qualifyNames = true,
                    allowedUnlifted = kotlinUnliftedMethods.get(),
                    proofsSubdirName = "KotlinJvmEquiv",
                    rootProofFile = "proofs/KotlinJvmEquiv.lean",
                    workDir = workDir,
                ),
            )
        }

        val stamp = stampFile.get().asFile
        stamp.parentFile.mkdirs()
        stamp.writeText(
            "verified lean=${existingClassFiles.size} kotlin=${existingKotlinClassFiles.size}\n",
        )
    }

    private fun verifyBytecodeTarget(target: BytecodeTargetSpec) {
        val bytecodeLeanFile = liftBytecode(target)
        val oleanFile = compileBytecodeOlean(target, bytecodeLeanFile)

        val jvmEquivDir = File(target.workDir, "proofs/${target.proofsSubdirName}")
        if (jvmEquivDir.isDirectory) {
            compileJvmEquivSubmodules(target.workDir, jvmEquivDir, target.proofsSubdirName, oleanFile)
        }

        execOperations.exec {
            workingDir = target.workDir
            commandLine(
                "lake",
                "env",
                "lean",
                "-DwarningAsError=true",
                "-j",
                "2",
                "-M",
                "4096",
                target.rootProofFile,
            )
        }
    }

    /** Lifts the target's classes, returning the bytecode Lean file (left untouched when the lift is unchanged). */
    private fun liftBytecode(target: BytecodeTargetSpec): File {
        val bytecodeLeanFile = File(target.bytecodeOutDir, target.leanFileName)
        val liftedLeanFile = File(target.bytecodeOutDir, "${target.leanFileName}.lifted")
        val liftArgs = buildList {
            add("python3")
            add(scriptFile.get().asFile.absolutePath)
            for (cf in target.classFilesToLift) {
                add("--class-file")
                add(cf.absolutePath)
            }
            add("--import")
            add("JvmSemantics")
            add("--namespace")
            add(target.leanNamespace)
            add("--instr-type")
            add(target.instrType)
            // Every method must lift unless explicitly listed: a silently skipped method would go unverified.
            add("--strict")
            for (method in target.allowedUnlifted) {
                add("--allow-unlifted")
                add(method)
            }
            if (target.qualifyNames) add("--qualify-names")
            add("-o")
            add(liftedLeanFile.absolutePath)
        }
        execOperations.exec {
            commandLine(liftArgs)
        }
        // Keep the previous file (and its mtime) when the lift is unchanged, so the bytecode olean and the proof
        // submodules that import it are only recompiled when something they depend on actually changed.
        val bytecodeChanged = !bytecodeLeanFile.isFile || bytecodeLeanFile.readText() != liftedLeanFile.readText()
        if (bytecodeChanged) {
            liftedLeanFile.copyTo(bytecodeLeanFile, overwrite = true)
        }
        liftedLeanFile.delete()
        return bytecodeLeanFile
    }

    /** Compiles the bytecode Lean file to its olean, unless the olean is newer than it and its dependencies. */
    private fun compileBytecodeOlean(target: BytecodeTargetSpec, bytecodeLeanFile: File): File {
        val libLeanDir = File(target.workDir, ".lake/build/lib/lean")
        val oleanFile = File(target.workDir, target.oleanRelativePath)
        oleanFile.parentFile.mkdirs()
        // The lifted file imports only `JvmSemantics` (and through it `Jvm.*`), never proof or other bytecode oleans.
        val oleanDepMtime = maxOf(
            bytecodeLeanFile.lastModified(),
            maxOleanMtime(libLeanDir) { rel -> rel.startsWith("proofs/") || rel.endsWith("Bytecode.olean") },
        )
        if (!oleanFile.isFile || oleanFile.lastModified() <= oleanDepMtime) {
            execOperations.exec {
                workingDir = target.workDir
                commandLine(
                    "lake",
                    "env",
                    "lean",
                    "-j",
                    "2",
                    "-M",
                    "4096",
                    "--root=${target.bytecodeOutDir.absolutePath}",
                    "-o",
                    oleanFile.absolutePath,
                    bytecodeLeanFile.absolutePath,
                )
            }
        }
        return oleanFile
    }

    private fun compileJvmEquivSubmodules(
        workDir: File,
        jvmEquivDir: File,
        proofsSubdirName: String,
        bytecodeOlean: File,
    ) {
        val libLeanDir = File(workDir, ".lake/build/lib/lean")
        val subOleanDir = File(libLeanDir, "proofs/$proofsSubdirName")
        subOleanDir.mkdirs()

        val lratDir = File(workDir, "proofs/lrat")
        val lratMtime = if (lratDir.isDirectory) {
            lratDir.walkTopDown().filter { it.isFile }.maxOfOrNull { it.lastModified() } ?: 0L
        } else {
            0L
        }
        // Exclude this directory's own oleans, and those of the other bytecode-proof directory unless this one imports
        // it: that directory is compiled later in the same task, so counting it would make every run look stale.
        val importedSubdirs = jvmEquivDir.walkTopDown()
            .filter { it.isFile && it.extension == "lean" }
            .flatMap { file -> file.readLines().mapNotNull { proofsImportRegex.find(it)?.groupValues?.get(1) } }
            .toSet()
        val excludedPrefixes = (BYTECODE_PROOF_SUBDIRS - importedSubdirs + proofsSubdirName).map { "proofs/$it/" }
        val otherOleanMtime = maxOleanMtime(libLeanDir) { rel -> excludedPrefixes.any { rel.startsWith(it) } }
        val baseDepMtime = maxOf(bytecodeOlean.lastModified(), lratMtime, otherOleanMtime)

        val moduleFiles = jvmEquivDir.listFiles { file -> file.isFile && file.extension == "lean" }
            ?.associateBy { it.nameWithoutExtension }
            .orEmpty()
        val escapedSubdir = Regex.escape(proofsSubdirName)
        val importRegex = Regex("""^\s*import\s+proofs\.$escapedSubdir\.([A-Za-z0-9_]+)""")
        val deps = moduleFiles.mapValues { (_, file) ->
            file.readLines()
                .mapNotNull { line -> importRegex.find(line)?.groupValues?.get(1) }
                .filter { it in moduleFiles }
        }
        val ordered = topoSortModules(moduleFiles.keys.sorted(), deps, proofsSubdirName)

        for (name in ordered) {
            val leanFile = moduleFiles.getValue(name)
            val subOlean = File(subOleanDir, "$name.olean")
            val depMtime = deps.getValue(name).maxOfOrNull { dep ->
                File(subOleanDir, "$dep.olean").lastModified()
            } ?: 0L
            val requiredMtime = maxOf(leanFile.lastModified(), baseDepMtime, depMtime)
            if (!subOlean.isFile || subOlean.lastModified() <= requiredMtime) {
                execOperations.exec {
                    workingDir = workDir
                    commandLine(
                        "lake",
                        "env",
                        "lean",
                        "-DwarningAsError=true",
                        "-j",
                        "2",
                        "-M",
                        "4096",
                        "--root=${workDir.absolutePath}",
                        "-o",
                        subOlean.absolutePath,
                        leanFile.absolutePath,
                    )
                }
            }
        }
    }

    private companion object {
        val BYTECODE_PROOF_SUBDIRS = setOf("JvmEquiv", "KotlinJvmEquiv")
        val proofsImportRegex = Regex("""^\s*import\s+proofs\.([A-Za-z0-9_]+)\.""")
    }

    private fun maxOleanMtime(libLeanDir: File, excluded: (String) -> Boolean): Long = libLeanDir.walkTopDown()
        .filter { it.isFile && it.extension == "olean" && !excluded(it.toRelativeString(libLeanDir)) }
        .maxOfOrNull { it.lastModified() } ?: 0L

    private fun topoSortModules(
        names: List<String>,
        deps: Map<String, List<String>>,
        proofsSubdirName: String,
    ): List<String> {
        val state = mutableMapOf<String, Int>()
        val result = mutableListOf<String>()
        fun visit(name: String) {
            when (state[name]) {
                2 -> return
                1 -> error("Cyclic import involving proofs.$proofsSubdirName.$name")
            }
            state[name] = 1
            for (dep in deps.getValue(name).sorted()) {
                visit(dep)
            }
            state[name] = 2
            result.add(name)
        }
        for (name in names) {
            visit(name)
        }
        return result
    }
}
