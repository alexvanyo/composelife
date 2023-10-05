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
    alias(libs.plugins.convention.androidLibraryCompose)
    alias(libs.plugins.convention.androidLibraryJacoco)
    alias(libs.plugins.convention.androidLibraryRoborazzi)
    alias(libs.plugins.roborazzi)
    alias(libs.plugins.convention.detekt)
}

android {
    namespace = "com.alexvanyo.composelife.ui.app.screenshots"
    defaultConfig {
        minSdk = 21
    }
}

kotlin {
    androidTarget()

    sourceSets {
        val androidMain by getting {
            dependencies {
                implementation(projects.uiApp)
                implementation(libs.androidx.activityCompose)
                implementation(libs.androidx.compose.foundation)
                implementation(libs.androidx.compose.ui)
            }
        }

        val androidUnitTest by getting {
            dependencies {
                implementation(projects.testActivity)
                implementation(libs.testParameterInjector.junit4)
                implementation(libs.androidx.compose.uiTestJunit4)
                implementation(libs.roborazzi.compose)
                implementation(libs.accompanist.testharness)
            }
        }
    }
}
