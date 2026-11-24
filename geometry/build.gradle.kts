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
    alias(libs.plugins.convention.lean)
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

lean {
    target = "Geometry:static"
    packageName = "com.alexvanyo.composelife.geometry"
    entries {
        register("lineSegment") {
            leanFile = "Geometry/LineSegment.lean"
        }
    }
}

kotlin {
    android {
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

    sourceSets {
        val commonMain = getByName("commonMain") {
            dependencies {
                implementation(libs.androidx.annotation)
            }
        }
        val jbMain = create("jbMain") {
            dependsOn(commonMain)
            dependencies {
                api(libs.jetbrains.compose.uiGeometry)
                api(libs.jetbrains.compose.uiUnit)

                implementation(libs.androidx.compose.runtime)
                implementation(libs.jetbrains.compose.uiUtil)
            }
        }
        val desktopMain = getByName("desktopMain") {
            dependsOn(jbMain)
        }
        val androidMain = getByName("androidMain") {
            dependsOn(jbMain)
        }
        val wasmJsMain = getByName("wasmJsMain") {
            dependsOn(jbMain)
        }
        val commonTest = getByName("commonTest") {
            dependencies {
                implementation(kotlin("test"))
            }
        }
        val jbTest = create("jbTest") {
            dependsOn(commonTest)
        }
        val desktopTest = getByName("desktopTest") {
            dependsOn(jbTest)
        }
        val androidSharedTest = getByName("androidSharedTest") {
            dependsOn(jbTest)
        }
        val wasmJsTest = getByName("wasmJsTest") {
            dependsOn(jbTest)
        }
    }
}
