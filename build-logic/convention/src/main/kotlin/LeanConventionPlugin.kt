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

import com.alexvanyo.composelife.buildlogic.CacheLeanTask
import com.alexvanyo.composelife.buildlogic.CheckLeanBuildScriptHygieneTask
import com.alexvanyo.composelife.buildlogic.CheckLeanGeneratedKotlinTask
import com.alexvanyo.composelife.buildlogic.ConventionPlugin
import com.alexvanyo.composelife.buildlogic.GenerateLeanKotlinTask
import com.alexvanyo.composelife.buildlogic.LeanExtension
import com.alexvanyo.composelife.buildlogic.VerifyLeanTask
import com.alexvanyo.composelife.buildlogic.heavyTaskLimitingBuildService
import org.gradle.api.Task
import org.gradle.language.base.plugins.LifecycleBasePlugin
import org.jetbrains.kotlin.gradle.dsl.KotlinMultiplatformExtension

class LeanConventionPlugin :
    ConventionPlugin({
        val leanExtension = extensions.create("lean", LeanExtension::class.java)

        val defaultLeanBinaryProvider = providers.gradleProperty("leanBinary")
            .orElse(providers.systemProperty("leanBinary"))
            .orElse(
                providers.provider {
                    "${System.getProperty("user.home")}/Projects/lean4/build/release/stage1/bin/lean"
                },
            )

        leanExtension.leanDirectory.convention(layout.projectDirectory.dir("lean"))
        leanExtension.leanBinary.convention(defaultLeanBinaryProvider)

        val generatedSourcesDir = layout.buildDirectory.dir("generated/sources/lean/kotlin/commonMain")

        leanExtension.entries.configureEach {
            outputFile.convention(
                layout.buildDirectory.file(
                    leanExtension.packageName.map { pkg ->
                        val packagePath = pkg.replace('.', '/')
                        val capitalizedName = name.replaceFirstChar {
                            if (it.isLowerCase()) it.titlecase() else it.toString()
                        }
                        "generated/sources/lean/kotlin/commonMain/$packagePath/${capitalizedName}Lean.kt"
                    },
                ),
            )
        }

        val cacheLean = tasks.register("cacheLean", CacheLeanTask::class.java) {
            description = "Opportunistically downloads Lean cache"
            group = LifecycleBasePlugin.VERIFICATION_GROUP
            workingDir.set(leanExtension.leanDirectory)
            usesService(heavyTaskLimitingBuildService)
        }

        val verifyLean = tasks.register("verifyLean", VerifyLeanTask::class.java) {
            description = "Formally verifies Lean logic using Lean 4 with warnings as errors (--wfail)"
            group = LifecycleBasePlugin.VERIFICATION_GROUP
            dependsOn(cacheLean)
            workingDir.set(leanExtension.leanDirectory)
            target.set(leanExtension.target)
            usesService(heavyTaskLimitingBuildService)
        }

        val generateLeanKotlin = tasks.register("generateLeanKotlin", GenerateLeanKotlinTask::class.java) {
            description = "Generates Kotlin code directly from Lean formal models"
            group = LifecycleBasePlugin.BUILD_GROUP
            dependsOn(verifyLean)
            leanFiles.from(
                leanExtension.leanDirectory.asFileTree.matching {
                    include("**/*.lean")
                    include("lakefile.toml")
                    include("lakefile.lean")
                    include("lean-toolchain")
                },
            )
            leanBinary.set(leanExtension.leanBinary)
            workingDir.set(leanExtension.leanDirectory)
            packageName.set(leanExtension.packageName)
            this.generatedSourcesDir.set(generatedSourcesDir)
            entries.set(
                provider {
                    leanExtension.entries.associate { entry ->
                        entry.leanFile.get() to entry.outputFile.get().asFile.absolutePath
                    }
                },
            )
        }

        val checkLeanGeneratedKotlin = tasks.register(
            "checkLeanGeneratedKotlin",
            CheckLeanGeneratedKotlinTask::class.java,
        ) {
            description = "Checks that generated Kotlin code contains no unbounded types (Rule R3)"
            group = LifecycleBasePlugin.VERIFICATION_GROUP
            dependsOn(generateLeanKotlin)
            this.generatedSourcesDir.set(generatedSourcesDir)
        }

        val checkLeanBuildScriptHygiene = tasks.register(
            "checkLeanBuildScriptHygiene",
            CheckLeanBuildScriptHygieneTask::class.java,
        ) {
            description = "Checks that build script contains no verbatim Kotlin code (Rule R2)"
            group = LifecycleBasePlugin.VERIFICATION_GROUP
            buildFile.set(layout.projectDirectory.file("build.gradle.kts"))
        }

        pluginManager.withPlugin("org.jetbrains.kotlin.multiplatform") {
            extensions.configure(KotlinMultiplatformExtension::class.java) {
                sourceSets.named("commonMain").configure {
                    kotlin.srcDir(generateLeanKotlin.flatMap { it.generatedSourcesDir })
                }
            }
        }

        tasks.withType(Task::class.java).named { it == LifecycleBasePlugin.CHECK_TASK_NAME }.configureEach {
            dependsOn(verifyLean, checkLeanGeneratedKotlin, checkLeanBuildScriptHygiene)
        }
    })
