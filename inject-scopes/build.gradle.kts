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

import org.jetbrains.kotlin.gradle.ExperimentalWasmDsl

plugins {
    alias(libs.plugins.convention.kotlinMultiplatform)
    alias(libs.plugins.convention.androidLibrary)
    alias(libs.plugins.convention.androidLibraryKsp)
    alias(libs.plugins.convention.detekt)
    alias(libs.plugins.gradleDependenciesSorter)
    alias(libs.plugins.metro)
}

android {
    namespace = "com.alexvanyo.composelife.kotlininjectscopes"
    defaultConfig {
        minSdk = 21
    }
}

kotlin {
    androidTarget()
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
                api(libs.kotlinInject.runtime)
                api(libs.kotlinInjectAnvil.runtime)
                api(libs.kotlinInjectAnvil.runtimeOptional)
                api(projects.entryPointRuntime)
            }
        }
        val jbMain by creating {
            dependsOn(commonMain)
        }
        val desktopMain by getting {
            dependsOn(jbMain)
            configurations["kspDesktop"].dependencies.addAll(
                listOf(
                    projects.entryPointSymbolProcessor,
                )
            )
        }
        val androidMain by getting {
            dependsOn(jbMain)
            configurations["kspAndroid"].dependencies.addAll(
                listOf(
                    projects.entryPointSymbolProcessor,
                )
            )
        }
        val wasmJsMain by getting {
            dependsOn(jbMain)
            configurations["kspWasmJs"].dependencies.addAll(
                listOf(
                    projects.entryPointSymbolProcessor,
                )
            )
        }
    }
}
