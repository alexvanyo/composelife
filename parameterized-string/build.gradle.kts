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

import com.alexvanyo.composelife.buildlogic.SharedTestConfig
import com.alexvanyo.composelife.buildlogic.useSharedTest

plugins {
    id("com.alexvanyo.composelife.kotlin.multiplatform")
    id("com.alexvanyo.composelife.android.library")
    id("com.alexvanyo.composelife.android.library.compose")
    id("com.alexvanyo.composelife.android.library.gradlemanageddevices")
    id("com.alexvanyo.composelife.android.library.jacoco")
    id("com.alexvanyo.composelife.android.library.testing")
    id("com.alexvanyo.composelife.detekt")
}

android {
    namespace = "com.alexvanyo.composelife.parameterizedstring"
    sourceSets["main"].manifest.srcFile("src/androidMain/AndroidManifest.xml")
    defaultConfig {
        minSdk = 21
    }
}

kotlin {
    android()

    sourceSets {
        val commonMain by getting {
            dependencies {
                implementation(libs.kotlinx.coroutines.core)
            }
        }
        val androidMain by getting {
            dependencies {
                api(libs.androidx.compose.foundation)
                api(libs.androidx.compose.runtime)
                implementation(libs.androidx.core)
                implementation(libs.kotlinx.coroutines.android)
            }
        }
        val commonTest by getting {
            dependencies {
                implementation(kotlin("test"))
                implementation(libs.kotlinx.coroutines.test)
            }
        }
        val androidSharedTest by creating {
            dependsOn(commonTest)
            dependencies {
                implementation(projects.testActivity)
                implementation(libs.androidx.test.core)
                implementation(libs.androidx.test.espresso)
                implementation(libs.androidx.compose.uiTestJunit4)
            }
        }
        val androidTest by getting {
            if (useSharedTest != SharedTestConfig.Instrumentation) {
                dependsOn(androidSharedTest)
            }
        }
        val androidAndroidTest by getting {
            if (useSharedTest != SharedTestConfig.Robolectric) {
                dependsOn(androidSharedTest)
            }
        }
    }
}
