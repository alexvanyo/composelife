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
    alias(libs.plugins.convention.androidLibraryJacoco)
    alias(libs.plugins.convention.androidLibraryTesting)
    alias(libs.plugins.convention.detekt)
    alias(libs.plugins.gradleDependenciesSorter)
    alias(libs.plugins.metro)
}

android {
    namespace = "com.alexvanyo.composelife.preferencestest"
    defaultConfig {
        minSdk = 21
        testInstrumentationRunner = "com.alexvanyo.composelife.test.InjectTestRunner"
    }
    configureGradleManagedDevices(enumValues<FormFactor>().toSet(), this)
}

kotlin {
    jvm("desktop")
    androidTarget()
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
                api(projects.preferences)

                implementation(libs.jetbrains.compose.runtime)
                implementation(projects.injectScopes)
            }
        }
        val jbMain by creating {
            dependsOn(commonMain)
        }
        val desktopMain by getting {
            dependsOn(jbMain)
        }
        val androidMain by getting {
            dependsOn(jbMain)
            dependencies {
                api(libs.androidx.test.junit)
            }
        }
        val commonTest by getting {
            dependencies {
                implementation(projects.dispatchersTest)
                implementation(projects.filesystemTest)
                implementation(projects.injectScopes)
                implementation(projects.injectTest)
                implementation(projects.kmpAndroidRunner)
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
            dependencies {
                implementation(libs.androidx.test.core)
                implementation(libs.androidx.test.junit)
                implementation(libs.androidx.test.runner)
            }
        }
    }
}
