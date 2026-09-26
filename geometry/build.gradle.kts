/*
 * Copyright 2023 The Android Open Source Project
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
    alias(libs.plugins.convention.androidLibraryKsp)
    alias(libs.plugins.convention.androidLibraryTesting)
    alias(libs.plugins.convention.detekt)
    alias(libs.plugins.convention.kotlinMultiplatformCompose)
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

val verifyLean by tasks.registering(Exec::class) {
    description = "Formally verifies geometry logic using Lean 4"
    group = LifecycleBasePlugin.VERIFICATION_GROUP
    dependsOn(cacheLean)
    workingDir = file("lean")
    commandLine("lake", "build", "Geometry:static")
    usesService(heavyTaskLimitingBuildService)
}

val compileGeometryBridgeCObject by tasks.registering(Exec::class) {
    description = "Compiles C bridge for Lean geometry engine"
    group = LifecycleBasePlugin.BUILD_GROUP
    dependsOn(verifyLean)
    workingDir = file("lean")
    inputs.file(file("lean/c/geometry_bridge.c"))
    inputs.file(file("lean/c/geometry_bridge.h"))
    val outputFile = layout.buildDirectory.file("natives/c/geometry_bridge.o")
    outputs.file(outputFile)
    doFirst {
        outputFile.get().asFile.parentFile.mkdirs()
    }
    val leanPrefix = leanPrefixProvider.get()
    commandLine(
        "clang",
        "-c",
        "-fPIC",
        "c/geometry_bridge.c",
        "-I$leanPrefix/include",
        "-o",
        outputFile.get().asFile.absolutePath,
    )
}

kotlin {
    androidLibrary {
        namespace = "com.alexvanyo.composelife.geometry"
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

    linuxX64 {
        compilations.getByName("test") {
            cinterops {
                val geometryBridge by creating {
                    definitionFile.set(file("src/linuxX64Test/cinterop/geometry_bridge.def"))
                    includeDirs(file("lean/c"))
                }
            }
        }
        binaries.withType<org.jetbrains.kotlin.gradle.plugin.mpp.TestExecutable>().configureEach {
            linkTaskProvider.configure {
                dependsOn(compileGeometryBridgeCObject)
            }
            val bridgeObj = layout.buildDirectory.file("natives/c/geometry_bridge.o").get().asFile.absolutePath
            val leanArchive = file("lean/.lake/build/lib/libGeometry_Geometry.a").absolutePath
            val leanPrefix = leanPrefixProvider.get()
            linkerOpts(
                bridgeObj,
                leanArchive,
                "-lgcc_s",
                "-L$leanPrefix/lib/lean",
                "-L$leanPrefix/lib",
                "-lleanshared",
                "-Wl,-rpath,$leanPrefix/lib/lean",
            )
        }
    }

    sourceSets {
        val commonMain by getting {
            dependencies {
                implementation(libs.androidx.annotation)
            }
        }
        val jbMain by creating {
            dependsOn(commonMain)
            dependencies {
                api(libs.jetbrains.compose.uiGeometry)
                api(libs.jetbrains.compose.uiUnit)

                implementation(libs.androidx.compose.runtime)
                implementation(libs.jetbrains.compose.uiUtil)
            }
        }
        val desktopMain by getting {
            dependsOn(jbMain)
        }
        val androidMain by getting {
            dependsOn(jbMain)
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
        }
        val desktopTest by getting {
            dependsOn(jbTest)
        }
        val androidSharedTest by getting {
            dependsOn(jbTest)
        }
        val wasmJsTest by getting {
            dependsOn(jbTest)
        }
        val linuxX64Test by getting {
            dependsOn(commonTest)
        }
    }
}

tasks.named("check") {
    dependsOn(verifyLean)
}

tasks.named("linuxX64Test") {
    dependsOn(verifyLean)
}
