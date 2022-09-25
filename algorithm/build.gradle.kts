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
    kotlin("multiplatform")
    id("com.alexvanyo.composelife.android.library")
    id("com.alexvanyo.composelife.android.library.compose")
    id("com.alexvanyo.composelife.android.library.gradlemanageddevices")
    id("com.alexvanyo.composelife.android.library.jacoco")
    id("com.alexvanyo.composelife.android.library.ksp")
    id("com.alexvanyo.composelife.android.library.testing")
    id("com.alexvanyo.composelife.detekt")
    kotlin("kapt")
}

android {
    namespace = "com.alexvanyo.composelife.algorithm"
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
                implementation(libs.kotlinx.datetime)
                implementation(libs.kotlinx.coroutines.core)
            }
        }
        val androidMain by getting {
            dependencies {
                api(projects.parameterizedString)
                api(projects.preferences)
                api(projects.dispatchers)
                implementation(libs.androidx.compose.foundation)
                implementation(libs.androidx.compose.runtime)
                implementation(libs.kotlinx.coroutines.android)
                implementation(libs.guava.android)
                implementation(libs.sealedEnum.runtime)
                configurations["kspAndroid"].dependencies.add(libs.sealedEnum.ksp.get())
                implementation(libs.dagger.hilt.runtime)
                configurations["kapt"].dependencies.add(libs.dagger.hilt.compiler.get())
            }
        }
        val commonTest by getting {
            dependencies {
                implementation(kotlin("test"))
                implementation(libs.kotlinx.coroutines.test)
                implementation(libs.turbine)
            }
        }
        val androidSharedTest by creating {
            dependsOn(commonTest)
            dependencies {
                implementation(projects.dispatchersTest)
                implementation(projects.patterns)
                implementation(projects.preferencesTest)
                implementation(projects.testActivity)
                implementation(libs.androidx.compose.uiTestJunit4)
                implementation(libs.androidx.test.core)
                implementation(libs.androidx.test.espresso)
            }
        }
        val androidTest by getting {
            if (useSharedTest != SharedTestConfig.Instrumentation) {
                dependsOn(androidSharedTest)
            }
            dependencies {
                configurations["kaptTest"].dependencies.add(libs.dagger.hilt.compiler.get())
            }
        }
        val androidAndroidTest by getting {
            if (useSharedTest != SharedTestConfig.Robolectric) {
                dependsOn(androidSharedTest)
            }
            dependencies {
                configurations["kaptAndroidTest"].dependencies.add(libs.dagger.hilt.compiler.get())
            }
        }
    }
}

dependencies {
    // TODO: Needing to do this is strange, putting it in androidTest above seems to leak it to androidAndroidTest
    testImplementation(libs.testParameterInjector.junit5)
}

kapt {
    correctErrorTypes = true
}
