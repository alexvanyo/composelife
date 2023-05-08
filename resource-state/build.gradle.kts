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

plugins {
    id("com.alexvanyo.composelife.kotlin.multiplatform")
    id("com.alexvanyo.composelife.android.library")
    id("com.alexvanyo.composelife.android.library.compose")
    id("com.alexvanyo.composelife.android.library.jacoco")
    id("com.alexvanyo.composelife.android.library.testing")
    id("com.alexvanyo.composelife.detekt")
    id("com.alexvanyo.composelife.kotlin.multiplatform.compose")
}

android {
    namespace = "com.alexvanyo.composelife.resourcestate"
    defaultConfig {
        minSdk = 21
    }
    configureGradleManagedDevices(FormFactor.All, this)
}

kotlin {
    android()
    jvm()

    sourceSets {
        val commonMain by getting {
            dependencies {
                api(libs.kotlinx.coroutines.core)
                api(libs.jetbrains.compose.foundation)
                api(libs.jetbrains.compose.runtime)
                api(libs.jetbrains.compose.ui)
            }
        }
        val jvmMain by getting {
            dependencies {
                implementation(compose.desktop.currentOs)
            }
        }
        val androidMain by getting {
            dependencies {
                api(libs.kotlinx.coroutines.android)
                implementation(libs.androidx.core)
                implementation(libs.androidx.compose.ui)
                implementation(libs.androidx.tracing)
                implementation(libs.androidx.lifecycle.viewmodel.savedstate)
            }
        }
        val commonTest by getting {
            dependencies {
                implementation(projects.kmpAndroidRunner)
                implementation(libs.kotlinx.coroutines.test)
                implementation(libs.turbine)
                implementation(libs.jetbrains.compose.uiTestJunit4)
            }
        }
        val androidSharedTest by getting {
            dependencies {
                implementation(projects.testActivity)

                implementation(libs.androidx.test.core)
                implementation(libs.androidx.test.espresso)
                implementation(libs.androidx.compose.uiTestJunit4)
            }
        }
    }
}
