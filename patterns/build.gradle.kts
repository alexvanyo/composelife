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
    kotlin("multiplatform")
    id("com.alexvanyo.composelife.android.library")
    id("com.alexvanyo.composelife.android.library.gradlemanageddevices")
    id("com.alexvanyo.composelife.android.library.ksp")
    id("com.alexvanyo.composelife.android.library.jacoco")
    id("com.alexvanyo.composelife.android.library.testing")
    id("com.alexvanyo.composelife.detekt")
}

android {
    namespace = "com.alexvanyo.composelife.patterns"
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
                api(projects.algorithm)
            }
        }
        val androidMain by getting {
            dependencies {
                api(libs.androidx.compose.foundation)
                api(libs.sealedEnum.runtime)
                configurations["kspAndroid"].dependencies.add(libs.sealedEnum.ksp.get())
            }
        }
        val commonTest by getting {
            dependencies {
                implementation(kotlin("test"))
            }
        }
        val sharedAndroidTest by creating {
            dependsOn(commonTest)
        }
        val androidTest by getting {
            dependsOn(sharedAndroidTest)
        }
        val androidAndroidTest by getting {
            dependsOn(sharedAndroidTest)
        }
    }
}

dependencies {
    // TODO: Needing to do this is strange, putting it in androidTest above seems to leak it to androidAndroidTest
    testImplementation(libs.testParameterInjector.junit5)
}
