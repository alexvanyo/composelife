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
    alias(libs.plugins.convention.detekt)
    alias(libs.plugins.gradleDependenciesSorter)
    alias(libs.plugins.metro)
}

android {
    namespace = "com.alexvanyo.composelife.databasetest"
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
                api(libs.kotlinx.coroutines.core)
                api(projects.database)

                implementation(libs.kotlinx.coroutines.test)
                implementation(projects.injectScopes)
                implementation(projects.updatable)
            }
        }
        val androidMain by getting {
            dependencies {
                api(libs.kotlinx.coroutines.android)
                api(libs.sqldelight.androidDriver)
            }
        }
        val desktopMain by getting {
            dependencies {
                api(libs.sqldelight.sqliteDriver)
            }
        }
        val wasmJsMain by getting {
            dependencies {
                api(libs.sqldelight.webDriver)

                implementation(npm("@cashapp/sqldelight-sqljs-worker", libs.versions.sqldelight.get()))
                implementation(npm("sql.js", libs.versions.sqlJs.get()))
                implementation(devNpm("copy-webpack-plugin", libs.versions.webPackPlugin.get()))
            }
        }
    }
}
