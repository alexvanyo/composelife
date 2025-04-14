/*
 * Copyright 2024 The Android Open Source Project
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
import com.slack.keeper.KeeperExtension
import com.slack.keeper.optInToKeeper

plugins {
    alias(libs.plugins.convention.kotlinMultiplatform)
    alias(libs.plugins.convention.androidApplication)
    alias(libs.plugins.convention.androidApplicationCompose)
    alias(libs.plugins.convention.androidApplicationTesting)
    alias(libs.plugins.convention.detekt)
    alias(libs.plugins.convention.kotlinMultiplatformCompose)
    kotlin("plugin.serialization") version libs.versions.kotlin
    alias(libs.plugins.gradleDependenciesSorter)
    alias(libs.plugins.keeper)
}

android {
    namespace = "com.alexvanyo.composelife.algorithm.benchmark"
    defaultConfig {
        applicationId = "com.alexvanyo.composelife.algorithm.benchmark"
        minSdk = 30
        targetSdk = 34
        versionCode = 1
        versionName = "1.0"
        testInstrumentationRunner = "androidx.benchmark.junit4.AndroidBenchmarkRunner"
        testInstrumentationRunnerArguments["androidx.benchmark.suppressErrors"] = "EMULATOR,UNLOCKED"
    }
    configureGradleManagedDevices(enumValues<FormFactor>().toSet(), this)
}

keeper {
    automaticR8RepoManagement.set(false)
    traceReferences {}
}

kotlin {
    androidTarget()

    sourceSets {
        val androidMain by getting {
            dependencies {
                implementation(libs.androidx.benchmark.micro.junit4)
            }
        }
        val commonTest by getting {
            dependencies {
                implementation(projects.algorithm)
                implementation(projects.dispatchersTest)
                implementation(projects.patterns)
            }
        }
        val androidInstrumentedTest by getting {
            dependencies {
                implementation(libs.testParameterInjector.junit4)
            }
        }
    }
}
