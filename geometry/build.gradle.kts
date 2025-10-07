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
import com.android.build.api.dsl.KotlinMultiplatformAndroidDeviceTestCompilation
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

kotlin {
    androidLibrary {
        namespace = "com.alexvanyo.composelife.geometry"
        minSdk = 23
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
            dependencies {
                implementation(libs.androidx.annotation)
                implementation(libs.androidx.compose.runtime)
            }
        }
        val jbMain by creating {
            dependsOn(commonMain)
            dependencies {
                implementation(libs.jetbrains.compose.uiGeometry)
                implementation(libs.jetbrains.compose.uiUnit)
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
        val commonTest by getting {}
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
    }
}
