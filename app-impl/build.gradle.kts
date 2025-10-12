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

import com.alexvanyo.composelife.buildlogic.FormFactor
import com.alexvanyo.composelife.buildlogic.configureGradleManagedDevices
import com.android.build.api.dsl.KotlinMultiplatformAndroidDeviceTestCompilation

plugins {
    alias(libs.plugins.convention.kotlinMultiplatform)
    alias(libs.plugins.convention.androidLibrary)
    alias(libs.plugins.convention.androidLibraryCompose)
    alias(libs.plugins.convention.androidLibraryJacoco)
    alias(libs.plugins.convention.androidLibraryTesting)
    alias(libs.plugins.convention.detekt)
    alias(libs.plugins.gradleDependenciesSorter)
    alias(libs.plugins.metro)
}

kotlin {
    androidLibrary {
        namespace = "com.alexvanyo.composelife.appimpl"
        minSdk = 23
        compilations.withType(KotlinMultiplatformAndroidDeviceTestCompilation::class.java) {
            instrumentationRunner = "com.alexvanyo.composelife.test.InjectTestRunner"
        }
        configureGradleManagedDevices(setOf(FormFactor.Mobile), this)
        androidResources { enable = true }
    }

    sourceSets {
        val commonMain by getting {
            dependencies {
                implementation(libs.androidx.compose.runtime)
                implementation(libs.androidx.compose.runtime.retain)
                implementation(libs.kotlinx.serialization.core)
                implementation(projects.androidApplication)
                implementation(projects.doNotKeepProcess)
                implementation(projects.filesystem)
                implementation(projects.imageLoader)
                implementation(projects.injectScopes)
                implementation(projects.logging)
                implementation(projects.network)
                implementation(projects.resourcesApp)
                implementation(projects.strictMode)
                implementation(projects.uiApp)
                implementation(projects.uiCommon)
                implementation(projects.uiMobile)
                implementation(projects.work)
            }
        }
        val androidMain by getting {
            dependencies {
                implementation(libs.androidx.activityCompose)
                implementation(libs.androidx.appcompat)
                implementation(libs.androidx.core)
                implementation(libs.androidx.core.splashscreen)
                implementation(libs.androidx.lifecycle.process)
                implementation(libs.androidx.profileInstaller)
            }
        }
        val commonTest by getting {
            dependencies {
                implementation(projects.appTestFixtures)
                implementation(projects.databaseTestFixtures)
                implementation(projects.dispatchersTestFixtures)
                implementation(projects.filesystemTestFixtures)
                implementation(projects.injectTest)
                implementation(projects.patterns)
                implementation(projects.preferencesTestFixtures)
                implementation(projects.uiCommon)
                implementation(projects.workTestFixtures)
            }
        }
        val androidSharedTest by getting {
            dependsOn(commonTest)
            dependencies {
                implementation(libs.androidx.test.core)
                implementation(libs.androidx.test.espresso)
                implementation(libs.androidx.window)
            }
        }
    }
}
