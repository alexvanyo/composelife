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

import com.alexvanyo.composelife.buildlogic.kaptSharedTest
import com.alexvanyo.composelife.buildlogic.sharedTestImplementation

plugins {
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
    defaultConfig {
        minSdk = 21
    }
}

dependencies {
    api(projects.parameterizedString)
    api(projects.preferences)
    api(projects.dispatchers)
    implementation(libs.androidx.compose.foundation)
    implementation(libs.androidx.compose.runtime)
    implementation(libs.kotlinx.datetime)
    implementation(libs.kotlinx.coroutines.android)
    implementation(libs.kotlinx.coroutines.core)
    implementation(libs.guava.android)
    implementation(libs.sealedEnum.runtime)
    ksp(libs.sealedEnum.ksp)
    implementation(libs.dagger.hilt.runtime)
    kapt(libs.dagger.hilt.compiler)

    sharedTestImplementation(projects.dispatchersTest)
    sharedTestImplementation(projects.patterns)
    sharedTestImplementation(projects.preferencesTest)
    sharedTestImplementation(projects.testActivity)
    sharedTestImplementation(libs.androidx.compose.uiTestJunit4)
    sharedTestImplementation(libs.androidx.test.espresso)
    sharedTestImplementation(libs.kotlinx.coroutines.test)
    sharedTestImplementation(libs.turbine)
    kaptSharedTest(libs.dagger.hilt.compiler)
}
