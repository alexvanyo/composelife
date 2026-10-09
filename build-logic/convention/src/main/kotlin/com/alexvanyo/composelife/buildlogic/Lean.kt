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
import org.gradle.api.provider.MapProperty
import org.gradle.api.provider.Property
import org.gradle.api.tasks.Input
import org.gradle.api.tasks.InputDirectory
import org.gradle.api.tasks.InputFile
import org.gradle.api.tasks.InputFiles
import org.gradle.api.tasks.Internal
import org.gradle.api.tasks.OutputDirectory
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
}

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
    @get:PathSensitive(PathSensitivity.RELATIVE)
    @get:InputDirectory
    abstract val workingDir: DirectoryProperty

    @get:Input
    abstract val target: Property<String>

    @TaskAction
    fun verify() {
        execOperations.exec {
            workingDir = this@VerifyLeanTask.workingDir.get().asFile
            commandLine("lake", "build", "--wfail", target.get())
        }
    }
}

@DisableCachingByDefault(because = "Lean compiler handles its own compilation caching")
abstract class GenerateLeanKotlinTask @Inject constructor(private val execOperations: ExecOperations) : DefaultTask() {
    @get:PathSensitive(PathSensitivity.RELATIVE)
    @get:InputFiles
    abstract val leanFiles: ConfigurableFileCollection

    @get:Input
    abstract val leanBinary: Property<String>

    @get:PathSensitive(PathSensitivity.RELATIVE)
    @get:InputDirectory
    abstract val workingDir: DirectoryProperty

    @get:Input
    abstract val packageName: Property<String>

    @get:Input
    abstract val entries: MapProperty<String, String>

    @get:OutputDirectory
    abstract val generatedSourcesDir: DirectoryProperty

    @TaskAction
    fun generate() {
        val workDir = workingDir.get().asFile
        val leanPath = File(workDir, ".lake/build/lib/lean").absolutePath

        entries.get().forEach { (leanRelPath, outFilePath) ->
            val outFile = File(outFilePath)
            outFile.parentFile.mkdirs()
            execOperations.exec {
                workingDir = workDir
                environment("LEAN_PATH", leanPath)
                commandLine(
                    leanBinary.get(),
                    "-DwarningAsError=true",
                    "-Dcompiler.kotlin.pruneUnreachable=true",
                    "-Dcompiler.kotlin.package=${packageName.get()}",
                    "-K",
                    outFile.absolutePath,
                    leanRelPath,
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

    @TaskAction
    fun check() {
        val dir = generatedSourcesDir.get().asFile
        val ktFiles = dir.walkTopDown().filter { it.extension == "kt" }.toList()
        check(ktFiles.isNotEmpty()) {
            "Expected generated Kotlin files in $dir, but found none."
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
