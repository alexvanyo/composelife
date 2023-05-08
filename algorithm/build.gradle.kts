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
    id("com.alexvanyo.composelife.android.library.ksp")
    id("com.alexvanyo.composelife.android.library.testing")
    id("com.alexvanyo.composelife.detekt")
    kotlin("kapt")
    id("com.alexvanyo.composelife.kotlin.multiplatform.compose")
}

android {
    namespace = "com.alexvanyo.composelife.algorithm"
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
            configurations["kapt"].dependencies.add(libs.dagger.hilt.compiler.get())
            dependencies {
                api(projects.dispatchers)
                api(projects.geometry)
                api(projects.parameterizedString)
                api(projects.preferences)
                api(projects.updatable)

                implementation(libs.androidx.annotation)
                implementation(libs.kotlinx.datetime)
                implementation(libs.kotlinx.coroutines.core)
                implementation(libs.jetbrains.compose.ui)
                implementation(libs.jetbrains.compose.runtime)
                implementation(libs.sealedEnum.runtime)
                implementation(libs.guava.android)
                implementation(libs.dagger.hilt.core)
            }
        }
        val androidMain by getting {
            configurations["kspAndroid"].dependencies.add(libs.sealedEnum.ksp.get())
            dependencies {
                implementation(libs.androidx.tracing)
                implementation(libs.kotlinx.coroutines.android)
            }
        }
        val jvmMain by getting {
            configurations["kspJvm"].dependencies.add(libs.sealedEnum.ksp.get())
        }
        val commonTest by getting {
            dependencies {
                implementation(projects.dispatchersTest)
                implementation(projects.kmpAndroidRunner)
                implementation(projects.kmpStateRestorationTester)
                implementation(projects.patterns)

                implementation(libs.kotlinx.coroutines.test)
                implementation(libs.turbine)
                implementation(libs.testParameterInjector.junit4)
            }
        }
        val androidSharedTest by getting {
            dependencies {
                implementation(projects.preferencesTest)
                implementation(projects.testActivity)

                implementation(libs.androidx.compose.uiTestJunit4)
                implementation(libs.androidx.test.core)
                implementation(libs.androidx.test.espresso)
            }
        }
        val androidUnitTest by getting {
            configurations["kaptTest"].dependencies.add(libs.dagger.hilt.compiler.get())
        }
        val androidInstrumentedTest by getting {
            configurations["kaptAndroidTest"].dependencies.add(libs.dagger.hilt.compiler.get())
        }
    }
}

kapt {
    correctErrorTypes = true
}
