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
import com.android.build.gradle.internal.tasks.ManagedDeviceSetupTask

plugins {
    alias(libs.plugins.convention.kotlinMultiplatform)
    alias(libs.plugins.convention.androidTest)
    alias(libs.plugins.convention.detekt)
    alias(libs.plugins.gradleDependenciesSorter)
    alias(libs.plugins.androidx.baselineProfile)
}

android {
    namespace = "com.alexvanyo.composelife.app.baselineprofilegenerator"
    targetProjectPath = ":app"
    configureGradleManagedDevices(setOf(FormFactor.Mobile), this)

    defaultConfig {
        minSdk = 28
    }
}

kotlin {
    androidTarget()

    sourceSets {
        val androidMain by getting {
            dependencies {
                implementation(libs.androidx.benchmark.macro.junit4)
                implementation(libs.androidx.test.junit)
                implementation(libs.androidx.test.runner)
                implementation(libs.kotlin.test.junit)
            }
        }
    }
}

baselineProfile {
    managedDevices += "aosppixel2api30"
    useConnectedDevices = false
}

afterEvaluate {
    tasks {
        if (project.properties.containsKey("androidx.baselineprofile.skipgeneration")) {
            named("aosppixel2api30Setup") {
                enabled = false
            }
        }
    }
}
