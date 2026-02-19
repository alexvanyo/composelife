/*
 * Copyright 2025 The Android Open Source Project
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
    alias(libs.plugins.metro)
}

kotlin {
    androidLibrary {
        namespace = "com.alexvanyo.composelife.apptests"
        minSdk = 23
    }

    sourceSets {
        val commonMain by getting {
            dependencies {
                api(projects.injectTest)

                implementation(projects.appImpl)
                implementation(projects.databaseTestFixtures)
                implementation(projects.dispatchersTestFixtures)
                implementation(projects.doNotKeepProcess)
                implementation(projects.filesystem)
                implementation(projects.filesystemTestFixtures)
                implementation(projects.imageLoader)
                implementation(projects.injectScopes)
                implementation(projects.logging)
                implementation(projects.network)
                implementation(projects.patterns)
                implementation(projects.preferencesTestFixtures)
                implementation(projects.resourcesApp)
                implementation(projects.strictMode)
                implementation(projects.uiApp)
                implementation(projects.uiCommon)
                implementation(projects.uiMobile)
                implementation(projects.uiSettings)
                implementation(projects.work)
                implementation(projects.workTestFixtures)
            }
        }
        val androidMain by getting {
            dependencies {
                api(libs.androidx.activityCompose)
                api(libs.androidx.appcompat)

                implementation(libs.androidx.test.core)
                implementation(libs.androidx.test.espresso)
                implementation(libs.androidx.window)
                implementation(libs.androidx.window.core)
                implementation(libs.kotlin.test.junit)
            }
        }
    }
}
