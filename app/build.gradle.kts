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

import com.alexvanyo.composelife.buildlogic.useSharedTest

plugins {
    id("com.alexvanyo.composelife.kotlin.multiplatform")
    id("com.alexvanyo.composelife.android.application")
    id("com.alexvanyo.composelife.android.application.compose")
    id("com.alexvanyo.composelife.android.application.gradlemanageddevices")
    id("com.alexvanyo.composelife.android.application.jacoco")
    id("com.alexvanyo.composelife.android.application.testing")
    id("com.alexvanyo.composelife.detekt")
    kotlin("kapt")
}

android {
    namespace = "com.alexvanyo.composelife"
    sourceSets["main"].manifest.srcFile("src/androidMain/AndroidManifest.xml")
    sourceSets["debug"].manifest.srcFile("src/androidDebug/AndroidManifest.xml")
    sourceSets["staging"].manifest.srcFile("src/androidStaging/AndroidManifest.xml")
    defaultConfig {
        applicationId = "com.alexvanyo.composelife"
        minSdk = 21
        targetSdk = 33
        versionCode = 1
        versionName = "1.0"
    }
}

kotlin {
    android()

    sourceSets {
        val commonMain by getting {
            dependencies {
                implementation(projects.doNotKeepProcess)
                implementation(projects.resources)
                implementation(projects.ui)
                implementation(libs.kotlinx.serialization.core)
            }
        }
        val androidMain by getting {
            dependencies {
                implementation(libs.accompanist.systemuicontroller)
                implementation(libs.androidx.activityCompose)
                implementation(libs.androidx.core)
                implementation(libs.androidx.core.splashscreen)
                implementation(libs.androidx.lifecycle.process)
                implementation(libs.androidx.profileInstaller)
                implementation(libs.androidx.room.runtime)
                implementation(libs.dagger.hilt.android)
                configurations["kapt"].dependencies.add(libs.dagger.hilt.compiler.get())
            }
        }
        val androidDebug by getting {
            dependencies {
                implementation(libs.androidx.compose.uiTooling)
                implementation(libs.leakCanary.android)
            }
        }
        val androidStaging by getting {
            dependencies {
                implementation(libs.leakCanary.android)
            }
        }
        val commonTest by getting {
            dependencies {
                implementation(projects.databaseTest)
                implementation(projects.dispatchersTest)
                implementation(projects.patterns)
                implementation(projects.preferencesTest)

                implementation(kotlin("test"))
            }
        }
        val androidSharedTest by creating {
            dependsOn(commonTest)
            dependencies {
                implementation(libs.androidx.test.core)
                implementation(libs.androidx.test.espresso)
                implementation(libs.androidx.window)
            }
        }
        val androidTest by getting {
            if (useSharedTest != com.alexvanyo.composelife.buildlogic.SharedTestConfig.Instrumentation) {
                dependsOn(androidSharedTest)
            }
            dependencies {
                configurations["kaptTest"].dependencies.add(libs.dagger.hilt.compiler.get())
            }
        }
        val androidAndroidTest by getting {
            if (useSharedTest != com.alexvanyo.composelife.buildlogic.SharedTestConfig.Robolectric) {
                dependsOn(androidSharedTest)
            }
            dependencies {
                compileOnly(libs.apiGuardian.api)
                compileOnly(libs.google.autoValue.annotations)
                configurations["kaptAndroidTest"].dependencies.add(libs.dagger.hilt.compiler.get())
            }
        }
    }
}

kapt {
    correctErrorTypes = true
}
