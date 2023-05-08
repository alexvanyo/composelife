/*
 * Copyright 2023 The Android Open Source Project
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
    id("com.alexvanyo.composelife.kotlin.multiplatform.compose")
}

android {
    namespace = "com.alexvanyo.composelife.ui.common"
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
                implementation(projects.geometry)
                implementation(projects.navigation)
                implementation(projects.snapshotStateSet)
                implementation(libs.androidx.annotation)
                implementation(libs.jetbrains.compose.animation)
                implementation(libs.jetbrains.compose.foundation)
                implementation(libs.jetbrains.compose.ui)
                implementation(libs.jetbrains.compose.uiToolingPreview)
                implementation(libs.jetbrains.compose.uiUtil)
                implementation(libs.kotlinx.coroutines.core)
                implementation(libs.sealedEnum.runtime)
            }
        }
        val jvmMain by getting {
            configurations["kspJvm"].dependencies.add(libs.sealedEnum.ksp.get())
            dependencies {
                implementation(compose.desktop.currentOs)
            }
        }
        val androidMain by getting {
            configurations["kspAndroid"].dependencies.add(libs.sealedEnum.ksp.get())
            dependencies {
                implementation(libs.androidx.activityCompose)
                implementation(libs.androidx.compose.foundation)
                implementation(libs.androidx.lifecycle.runtime)
                implementation(libs.androidx.core)
                implementation(libs.kotlinx.coroutines.android)
            }
        }
        val commonTest by getting {
            dependencies {
                implementation(projects.kmpAndroidRunner)
                implementation(projects.kmpStateRestorationTester)

                implementation(libs.kotlinx.coroutines.test)
                implementation(libs.jetbrains.compose.uiTestJunit4)
            }
        }
        val androidSharedTest by getting {
            dependencies {
                implementation(projects.testActivity)
            }
        }
    }
}
