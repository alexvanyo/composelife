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

plugins {
    alias(libs.plugins.convention.kotlinMultiplatform)
    alias(libs.plugins.convention.androidLibrary)
    alias(libs.plugins.convention.detekt)
    alias(libs.plugins.gradleDependenciesSorter)
}

android {
    namespace = "com.alexvanyo.composelife.injecttest"
    defaultConfig {
        minSdk = 21
    }
}

kotlin {
    androidTarget()
    jvm("desktop")

    sourceSets {
        val commonMain by getting {
            dependencies {
                api(libs.kotlinx.coroutines.test)
                api(projects.databaseTest)
                api(projects.kmpAndroidRunner)
                api(projects.preferencesTest)

                implementation(projects.injectScopes)
            }
        }
        val jbMain by creating {
            dependsOn(commonMain)
            dependencies {
                implementation(libs.kotlin.test.junit)
            }
        }
        val desktopMain by getting {
            dependsOn(jbMain)
        }
        val androidMain by getting {
            dependsOn(jbMain)
            dependencies {
                api(libs.androidx.compose.uiTestJunit4)
                api(libs.androidx.test.runner)
                api(libs.leakCanary.instrumentation)

                implementation(libs.leakCanary.android)
            }
        }
    }
}
