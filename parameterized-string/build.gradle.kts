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
    alias(libs.plugins.convention.androidLibraryJacoco)
    alias(libs.plugins.convention.androidLibraryTesting)
    alias(libs.plugins.convention.detekt)
    alias(libs.plugins.convention.kotlinMultiplatformCompose)
    kotlin("plugin.serialization") version libs.versions.kotlin
    alias(libs.plugins.gradleDependenciesSorter)
}

kotlin {
    androidLibrary {
        namespace = "com.alexvanyo.composelife.parameterizedstring"
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
                implementation(libs.kotlinx.coroutines.core)
                implementation(projects.serialization)
            }
        }
        val jbMain by creating {
            dependsOn(commonMain)
            dependencies {
                api(libs.androidx.compose.runtime)
                api(libs.androidx.compose.runtime.saveable)
                api(libs.jetbrains.compose.uiText)
            }
        }
        val jbNonAndroidMain by creating {
            dependsOn(jbMain)
        }
        val jvmMain by creating {
            dependsOn(jbMain)
        }
        val desktopMain by getting {
            dependsOn(jbNonAndroidMain)
            dependsOn(jvmMain)
        }
        val androidMain by getting {
            dependsOn(jbMain)
            dependsOn(jvmMain)
            dependencies {
                api(libs.androidx.compose.foundation)

                implementation(libs.androidx.core)
                implementation(libs.androidx.tracing)
                implementation(libs.kotlinx.coroutines.android)
            }
        }
        val wasmJsMain by getting {
            dependsOn(jbNonAndroidMain)
            dependencies {
                implementation(libs.jetbrains.compose.ui)
            }
        }
        val commonTest by getting {
            dependencies {
                implementation(libs.kotlinx.coroutines.test)
                implementation(projects.injectTest)
                implementation(projects.kmpAndroidRunner)
                implementation(projects.kmpStateRestorationTester)
            }
        }
        val jbTest by creating {
            dependsOn(commonTest)
            dependencies {
                implementation(libs.jetbrains.compose.uiTest)
            }
        }
        val jvmTest by creating {
            dependsOn(jbTest)
        }
        val desktopTest by getting {
            dependsOn(jvmTest)
            dependencies {
                implementation(compose.desktop.currentOs)
            }
        }
        val androidSharedTest by getting {
            dependsOn(jvmTest)
            dependencies {
                implementation(libs.androidx.compose.ui)
                implementation(libs.androidx.compose.uiTest)
                implementation(libs.androidx.test.core)
                implementation(libs.androidx.test.espresso)
                implementation(projects.parameterizedStringTestResources)
                implementation(projects.testActivity)
            }
        }
        val wasmJsTest by getting {
            dependsOn(jbTest)
        }
    }
}
