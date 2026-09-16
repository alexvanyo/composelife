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

plugins {
    alias(libs.plugins.convention.androidApplication)
    alias(libs.plugins.convention.androidApplicationCompose)
    alias(libs.plugins.convention.androidApplicationTesting)
    alias(libs.plugins.convention.detekt)
    alias(libs.plugins.convention.kotlinMultiplatformCompose)
    kotlin("plugin.serialization") version libs.versions.kotlin
    alias(libs.plugins.gradleDependenciesSorter)
    //alias(libs.plugins.keeper)
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
        // Built-in test platform in AGP splits runner arguments on commas in android-test-engine <= 1.0.7.
        // Avoid commas by passing individual arguments rather than a comma-separated list to suppressErrors.
        // Safe to consolidate back to suppressErrors once AGP updates its bundled android-test-engine to >= 1.0.8.
        testInstrumentationRunnerArguments["androidx.benchmark.suppressErrors"] = "EMULATOR"
        testInstrumentationRunnerArguments["androidx.benchmark.requireAot"] = "false"
        testInstrumentationRunnerArguments["androidx.benchmark.requireLockedClocks"] = "false"
    }
    testBuildType = "staging"
    configureGradleManagedDevices(enumValues<FormFactor>().toSet(), this)
}

//keeper {
//    automaticR8RepoManagement.set(false)
//    traceReferences {}
//}

dependencies {
    implementation(projects.algorithm)
    implementation(libs.androidx.benchmark.micro.junit4)
    implementation(libs.androidx.test.runner)
    implementation(libs.androidx.tracing)

    androidTestImplementation(projects.dispatchersTestFixtures)
    androidTestImplementation(projects.patterns)
    androidTestImplementation(projects.tracingTestFixtures)
    androidTestImplementation(libs.androidx.test.junit)
    androidTestImplementation(libs.junit4)
    androidTestImplementation(libs.kotlin.test.junit)
    androidTestImplementation(libs.testParameterInjector.junit4)
}

