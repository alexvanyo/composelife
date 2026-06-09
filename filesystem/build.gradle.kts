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
import org.jetbrains.kotlin.gradle.ExperimentalWasmDsl

plugins {
    alias(libs.plugins.convention.kotlinMultiplatform)
    alias(libs.plugins.convention.androidLibrary)
    alias(libs.plugins.convention.detekt)
    alias(libs.plugins.gradleDependenciesSorter)
    alias(libs.plugins.metro)
    alias(libs.plugins.convention.kotlinMultiplatformCompose)
}

kotlin {
    androidLibrary {
        namespace = "com.alexvanyo.composelife.filesystem"
        minSdk = 23
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
                api(libs.okio)

                implementation(libs.androidx.compose.runtime)
                implementation(libs.kotlinx.coroutines.core)
                implementation(libs.kotlinx.datetime)
                implementation(projects.dispatchers)
                implementation(projects.injectScopes)
            }
        }
        val jvmMain by creating {
            dependsOn(commonMain)
        }
        val desktopMain by getting {
            dependsOn(jvmMain)
        }
        val androidMain by getting {
            dependsOn(jvmMain)
        }
        val wasmJsMain by getting {
            dependencies {
                implementation(libs.jetbrains.compose.ui)
                implementation(libs.kotlinx.browser)
                implementation(libs.okio.fakefilesystem)
            }
        }
        val wasmJsTest by getting {
            dependencies {
                implementation(kotlin("test"))
                implementation(libs.jetbrains.compose.ui)
                implementation(libs.kotlinx.browser)
                implementation(libs.kotlinx.coroutines.test)
                implementation(projects.dispatchersTestFixtures)
            }
        }
    }
}
