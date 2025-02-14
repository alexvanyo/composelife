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
    alias(libs.plugins.convention.detekt)
    alias(libs.plugins.gradleDependenciesSorter)
}

android {
    namespace = "com.alexvanyo.composelife.roborazzishowkasescreenshottest"
    defaultConfig {
        minSdk = 21
    }
    packagingOptions.resources.excludes.add("META-INF/versions/9/OSGI-INF/MANIFEST.MF")
}

kotlin {
    androidTarget()

    sourceSets {
        val commonMain by getting {
            dependencies {
                implementation(libs.kotlin.test)
            }
        }
        val androidMain by getting {
            dependencies {
                implementation(libs.androidx.activityCompose)
                implementation(libs.androidx.compose.foundation)
                implementation(libs.androidx.compose.uiTest)
                implementation(libs.androidx.test.core)
                implementation(libs.kotlin.test.junit)
                implementation(libs.robolectric)
                implementation(libs.roborazzi.compose)
                implementation(libs.roborazzi.core)
                implementation(libs.showkase.runtime)
                implementation(libs.testParameterInjector.junit4)
            }
        }
    }
}
