/*
 * Copyright 2024 The Android Open Source Project
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

import com.alexvanyo.composelife.buildlogic.FormFactor
import com.alexvanyo.composelife.buildlogic.configureGradleManagedDevices
import com.alexvanyo.composelife.buildlogic.heavyTaskLimitingBuildService
import org.jetbrains.kotlin.gradle.ExperimentalWasmDsl

plugins {
    alias(libs.plugins.convention.kotlinMultiplatform)
    alias(libs.plugins.convention.androidLibrary)
    alias(libs.plugins.convention.androidLibraryCompose)
    alias(libs.plugins.convention.androidLibraryJacoco)
    alias(libs.plugins.convention.androidLibraryTesting)
    alias(libs.plugins.convention.detekt)
    alias(libs.plugins.convention.kotlinMultiplatformCompose)
    kotlin("plugin.serialization") version libs.versions.kotlin
    alias(libs.plugins.gradleDependenciesSorter)
}

composeCompiler {
    targetKotlinPlatforms.set(
        setOf(
            org.jetbrains.kotlin.gradle.plugin.KotlinPlatformType.androidJvm,
            org.jetbrains.kotlin.gradle.plugin.KotlinPlatformType.jvm,
            org.jetbrains.kotlin.gradle.plugin.KotlinPlatformType.wasm,
        ),
    )
}

val leanPrefixProvider = providers.exec {
    workingDir = file("lean")
    commandLine("lean", "--print-prefix")
}.standardOutput.asText.map { it.trim() }

val cacheLean by tasks.registering(Exec::class) {
    description = "Opportunistically downloads Lean cache"
    group = LifecycleBasePlugin.VERIFICATION_GROUP
    workingDir = file("lean")
    commandLine("lake", "exe", "cache", "get")
    isIgnoreExitValue = true
    usesService(heavyTaskLimitingBuildService)
}

/**
 * Path to the custom Lean 4 binary with JVM bytecode backend support.
 * Override via the Gradle property `leanJvmBinary` or system property `leanJvmBinary`.
 * Defaults to the local Lean 4 fork build at ~/Projects/lean4.
 */
val leanJvmBinaryProvider = providers.gradleProperty("leanJvmBinary")
    .orElse(providers.systemProperty("leanJvmBinary"))
    .orElse(
        providers.provider {
            "${System.getProperty("user.home")}/Projects/lean4/build/release/stage1/bin/lean"
        },
    )

val verifyLean by tasks.registering(Exec::class) {
    description = "Formally verifies session-value logic using Lean 4"
    group = LifecycleBasePlugin.VERIFICATION_GROUP
    dependsOn(cacheLean)
    workingDir = file("lean")
    commandLine("lake", "build", "SessionValue:static")
    usesService(heavyTaskLimitingBuildService)
}

/**
 * Path to the custom Lean 4 binary with Kotlin codegen backend support.
 * Override via the Gradle property `leanBinary` or system property `leanBinary`.
 * Defaults to the local Lean 4 fork build at ~/Projects/lean4.
 */
val leanBinaryProvider = providers.gradleProperty("leanBinary")
    .orElse(providers.systemProperty("leanBinary"))
    .orElse(
        providers.provider {
            "${System.getProperty("user.home")}/Projects/lean4/build/release/stage1/bin/lean"
        },
    )

abstract class GenerateLeanSessionValueKotlinTask @javax.inject.Inject constructor(
    private val execOperations: ExecOperations,
) : DefaultTask() {
    @get:InputFiles
    abstract val leanFiles: ConfigurableFileCollection

    @get:Input
    abstract val leanBinary: Property<String>

    @get:InputDirectory
    abstract val workingDir: DirectoryProperty

    @get:OutputFile
    abstract val sessionValueFile: RegularFileProperty

    @get:OutputFile
    abstract val stateMachineFile: RegularFileProperty

    @TaskAction
    fun generate() {
        val svFile = sessionValueFile.get().asFile
        svFile.parentFile.mkdirs()
        val smFile = stateMachineFile.get().asFile
        smFile.parentFile.mkdirs()
        val workDir = this@GenerateLeanSessionValueKotlinTask.workingDir.get().asFile
        val leanPath = File(workDir, ".lake/build/lib/lean").absolutePath
        execOperations.exec {
            workingDir = workDir
            environment("LEAN_PATH", leanPath)
            commandLine(
                leanBinary.get(),
                "-Dcompiler.kotlin.pruneUnreachable=true",
                "-Dcompiler.kotlin.package=com.alexvanyo.composelife.sessionvalue",
                "-K",
                svFile.absolutePath,
                "SessionValue/Basic.lean",
            )
        }
        execOperations.exec {
            workingDir = workDir
            environment("LEAN_PATH", leanPath)
            commandLine(
                leanBinary.get(),
                "-Dcompiler.kotlin.pruneUnreachable=true",
                "-Dcompiler.kotlin.package=com.alexvanyo.composelife.sessionvalue",
                "-K",
                smFile.absolutePath,
                "SessionValue/StateMachine.lean",
            )
        }
    }
}

val generateLeanSessionValueKotlin by tasks.registering(GenerateLeanSessionValueKotlinTask::class) {
    description = "Generates Kotlin code directly from Lean session-value formal model"
    group = LifecycleBasePlugin.BUILD_GROUP
    dependsOn(verifyLean)
    leanFiles.from(
        fileTree("lean") {
            include("**/*.lean")
            include("lakefile.toml")
            include("lean-toolchain")
        },
    )
    leanBinary.set(leanBinaryProvider)
    workingDir.set(layout.projectDirectory.dir("lean"))
    sessionValueFile.set(layout.buildDirectory.file("generated/sources/lean/kotlin/commonMain/com/alexvanyo/composelife/sessionvalue/SessionValueLean.kt"))
    stateMachineFile.set(layout.buildDirectory.file("generated/sources/lean/kotlin/commonMain/com/alexvanyo/composelife/sessionvalue/SessionValueStateLean.kt"))
}

kotlin {

    androidLibrary {
        namespace = "com.alexvanyo.composelife.sessionvalue"
        minSdk = 24
        configureGradleManagedDevices(enumValues<FormFactor>().toSet(), this)
    }

    jvm("desktop")

    @OptIn(ExperimentalWasmDsl::class)
    wasmJs {
        browser {
            testTask {
                useKarma {
                    useChromiumHeadless()
                }
            }
        }
    }

    sourceSets {
        val commonMain by getting {
            kotlin.srcDir(generateLeanSessionValueKotlin.map { it.sessionValueFile.get().asFile.parentFile.parentFile.parentFile.parentFile.parentFile })
            dependencies {
                api(libs.kotlinx.serialization.core)
            }
        }
        val jbMain by creating {
            dependsOn(commonMain)
            dependencies {
                api(libs.androidx.compose.runtime)
                api(libs.androidx.compose.runtime.saveable)

                implementation(projects.serialization)
            }
        }
        val androidMain by getting {
            dependsOn(jbMain)
        }
        val desktopMain by getting {
            dependsOn(jbMain)
            dependencies {
                implementation(compose.desktop.currentOs)
            }
        }
        val wasmJsMain by getting {
            dependsOn(jbMain)
        }
        val commonTest by getting {
            dependencies {
                implementation(kotlin("test"))
            }
        }
        val jbTest by creating {
            dependsOn(commonTest)
            dependencies {
                implementation(projects.injectTest)
                implementation(projects.kmpAndroidRunner)
                implementation(projects.kmpStateRestorationTester)
                implementation(projects.testActivity)
                implementation(libs.jetbrains.compose.uiTest)
                implementation(libs.kotlinx.coroutines.test)
                implementation(libs.kotlinx.io.core)
                implementation(libs.kotlinx.serialization.json)
                implementation(libs.molecule)
                implementation(libs.turbine)
            }
        }
        val desktopTest by getting {
            dependsOn(jbTest)
        }
        val androidSharedTest by getting {
            dependsOn(jbTest)
            dependencies {
                implementation(libs.androidx.compose.ui)
            }
        }
        val wasmJsTest by getting {
            dependsOn(jbTest)
            dependencies {
                implementation(libs.jetbrains.compose.ui)
            }
        }
    }
}

tasks.named("check") {
    dependsOn(verifyLean)
}




