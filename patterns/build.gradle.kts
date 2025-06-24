/*
 * Copyright 2022 The Android Open Source Project
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
    alias(libs.plugins.convention.androidLibraryKsp)
    alias(libs.plugins.convention.androidLibraryJacoco)
    alias(libs.plugins.convention.androidLibraryTesting)
    alias(libs.plugins.convention.detekt)
    alias(libs.plugins.gradleDependenciesSorter)
}

kotlin {
    androidLibrary {
        namespace = "com.alexvanyo.composelife.patterns"
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
                api(projects.algorithm)
                api(projects.sealedEnum.runtime)
            }
        }
        val jbMain by creating {
            dependsOn(commonMain)
            dependencies {
                api(libs.jetbrains.compose.uiUnit)
            }
        }
        val jvmMain by creating {
            dependsOn(jbMain)
        }
        val desktopMain by getting {
            dependsOn(jvmMain)
            configurations["kspDesktop"].dependencies.add(projects.sealedEnum.ksp)
        }
        val androidMain by getting {
            dependsOn(jvmMain)
            configurations["kspAndroid"].dependencies.add(projects.sealedEnum.ksp)
        }
        val wasmJsMain by getting {
            dependsOn(jbMain)
            configurations["kspWasmJs"].dependencies.add(projects.sealedEnum.ksp)
        }
        val commonTest by getting {}
        val jbTest by creating {
            dependsOn(commonTest)
        }
        val jvmTest by creating {
            dependsOn(jbTest)
            dependencies {
                implementation(libs.testParameterInjector.junit4)
            }
        }
        val desktopTest by getting {
            dependsOn(jvmTest)
        }
        val androidSharedTest by getting {
            dependsOn(jvmTest)
        }
        val wasmJsTest by getting {
            dependsOn(jbTest)
        }
    }
}
