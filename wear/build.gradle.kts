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
    id("com.alexvanyo.composelife.android.application")
    id("com.alexvanyo.composelife.android.application.compose")
    id("com.alexvanyo.composelife.android.application.jacoco")
    id("com.alexvanyo.composelife.android.application.ksp")
    id("com.alexvanyo.composelife.android.application.testing")
    id("com.alexvanyo.composelife.detekt")
    kotlin("kapt")
}

android {
    namespace = "com.alexvanyo.composelife.wear"
    sourceSets["main"].manifest.srcFile("src/androidMain/AndroidManifest.xml")
    defaultConfig {
        applicationId = "com.alexvanyo.composelife.wear"
        minSdk = 26
        targetSdk = 30
        versionCode = 1
        versionName = "1.0"
    }
}

kotlin {
    android()

    sourceSets {
        val commonMain by getting {
            dependencies {
                implementation(projects.algorithm)
                implementation(projects.openglRenderer)

                implementation(libs.kotlinx.datetime)
                implementation(libs.kotlinx.coroutines.core)
                implementation(libs.kotlinx.serialization.core)
            }
        }
        val androidMain by getting {
            dependencies {
                implementation(libs.androidx.compose.foundation)
                implementation(libs.androidx.compose.runtime)
                implementation(libs.androidx.core)
                implementation(libs.androidx.lifecycle.process)
                implementation(libs.androidx.lifecycle.runtime)
                implementation(libs.androidx.wear.watchface)
                implementation(libs.kotlinx.coroutines.android)
                implementation(libs.sealedEnum.runtime)
                configurations["kspAndroid"].dependencies.add(libs.sealedEnum.ksp.get())
                implementation(libs.dagger.hilt.android)
                configurations["kapt"].dependencies.add(libs.dagger.hilt.compiler.get())
            }
        }
        val androidDebug by getting {
            dependencies {
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
                implementation(kotlin("test"))
                implementation(libs.kotlinx.coroutines.test)
                implementation(libs.turbine)
            }
        }
        val androidSharedTest by creating {
            dependsOn(commonTest)
            dependencies {
                implementation(libs.androidx.compose.uiTestJunit4)
                implementation(libs.androidx.test.espresso)
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
            dependencies {
                compileOnly(libs.apiGuardian.api)
                compileOnly(libs.google.autoValue.annotations)
            }
        }
    }
}

dependencies {
    testImplementation(libs.testParameterInjector.junit4)
}

kapt {
    correctErrorTypes = true
}
