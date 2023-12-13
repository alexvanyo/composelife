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
    alias(libs.plugins.convention.kotlinMultiplatform)
    alias(libs.plugins.convention.androidApplication)
    alias(libs.plugins.convention.androidApplicationCompose)
    alias(libs.plugins.convention.androidApplicationKsp)
    alias(libs.plugins.convention.detekt)
}

android {
    namespace = "com.alexvanyo.composelife.wear"
    defaultConfig {
        applicationId = "com.alexvanyo.composelife.wear"
        minSdk = 26
        targetSdk = 33
        versionCode = 1
        versionName = "1.0"
    }
    configureGradleManagedDevices(setOf(FormFactor.Wear), this)
}

kotlin {
    androidTarget()

    sourceSets {
        val commonMain by getting {
            dependencies {
                implementation(projects.injectScopes)
                implementation(projects.processLifecycle)
                implementation(projects.strictMode)
                implementation(projects.wearWatchface)

                implementation(libs.kotlinx.coroutines.core)
                implementation(libs.kotlinInject.runtime)
            }
        }
        val androidMain by getting {
            configurations["kspAndroid"].dependencies.add(libs.kotlinInject.ksp.get())
            dependencies {
                implementation(libs.androidx.activityCompose)
                implementation(libs.androidx.appcompat)
                implementation(libs.androidx.core)
                implementation(libs.androidx.lifecycle.process)
                implementation(libs.androidx.lifecycle.runtime)
                implementation(libs.kotlinx.coroutines.android)
            }
        }
        val androidDebug by creating {
            dependsOn(androidMain)
            dependencies {
                implementation(libs.leakCanary.android)
            }
        }
        val androidStaging by creating {
            dependsOn(androidMain)
            dependencies {
                implementation(libs.leakCanary.android)
            }
        }
    }
}
