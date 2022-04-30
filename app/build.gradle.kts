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
    id("com.alexvanyo.composelife.android.application")
    id("com.alexvanyo.composelife.android.application.compose")
    id("com.alexvanyo.composelife.android.application.gradlemanageddevices")
    id("com.alexvanyo.composelife.android.application.jacoco")
    id("com.alexvanyo.composelife.android.application.testing")
    id("com.alexvanyo.composelife.detekt")
    kotlin("kapt")
}

android {
    namespace = "com.alexvanyo.composelife"
    defaultConfig {
        applicationId = "com.alexvanyo.composelife"
        minSdk = 21
        targetSdk = 32
        versionCode = 1
        versionName = "1.0"
    }
}

dependencies {
    implementation(projects.resources)
    implementation(projects.ui)

    implementation(libs.accompanist.systemuicontroller)
    implementation(libs.androidx.activityCompose)
    implementation(libs.androidx.core)
    implementation(libs.androidx.core.splashscreen)
    implementation(libs.dagger.hilt.runtime)
    kapt(libs.dagger.hilt.compiler)

    debugImplementation(libs.androidx.compose.uiTooling)
    debugImplementation(libs.leakCanary)

    sharedTestImplementation(projects.dispatchersTest)
    sharedTestImplementation(projects.patterns)
    sharedTestImplementation(projects.preferencesTest)
    sharedTestImplementation(projects.screenshotTest)
    sharedTestImplementation(libs.androidx.compose.uiTestJunit4)
    sharedTestImplementation(libs.androidx.test.espresso)
    sharedTestImplementation(libs.androidx.test.junit)
    sharedTestImplementation(libs.kotlinx.coroutines.test)
    sharedTestImplementation(libs.turbine)
    kaptSharedTest(libs.dagger.hilt.compiler)
}

kapt {
    correctErrorTypes = true
}
