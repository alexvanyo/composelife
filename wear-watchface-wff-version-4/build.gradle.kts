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
    alias(libs.plugins.convention.androidApplication)
    alias(libs.plugins.convention.androidApplicationTesting)
    alias(libs.plugins.convention.detekt)
    alias(libs.plugins.gradleDependenciesSorter)
}

android {
    namespace = "com.alexvanyo.composelife"
    defaultConfig {
        applicationId = "com.alexvanyo.composelife.wff"
        minSdk = 36
        targetSdk = 36
        versionCode = 1
        versionName = "1.0"
    }
    configureGradleManagedDevices(setOf(FormFactor.Wear), this)

    compileOptions {
        isCoreLibraryDesugaringEnabled = false
    }
    buildTypes {
        getByName("staging") {
            isShrinkResources = false
        }
        getByName("release") {
            isShrinkResources = false
        }
    }
    lint {
        disable += listOf("UnusedResources")
    }
}

dependencies {
    implementation(projects.resourcesCommon)
    implementation(projects.wearWatchfaceWffResources)
}
