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
    alias(libs.plugins.convention.androidApplicationCompose)
    alias(libs.plugins.convention.androidApplicationJacoco)
    alias(libs.plugins.convention.androidApplicationTesting)
    alias(libs.plugins.convention.dependencyGuard)
    alias(libs.plugins.convention.detekt)
    //alias(libs.plugins.androidx.baselineProfile)
    alias(libs.plugins.gradleDependenciesSorter)
    alias(libs.plugins.metro)
}

android {
    namespace = "com.alexvanyo.composelife"
    defaultConfig {
        applicationId = "com.alexvanyo.composelife"
        minSdk = 23
        targetSdk = 35
        versionCode = 1
        versionName = "1.0"
        testInstrumentationRunner = "com.alexvanyo.composelife.test.InjectTestRunner"
    }
    configureGradleManagedDevices(setOf(FormFactor.Mobile), this)
}

//baselineProfile {
//    automaticGenerationDuringBuild = false
//    saveInSrc = true
//    dexLayoutOptimization = true
//    mergeIntoMain = true
//}

dependencies {
    implementation(libs.androidx.compose.runtime)
    implementation(libs.androidx.compose.runtime.retain)
    implementation(libs.kotlinx.serialization.core)
    implementation(projects.doNotKeepProcess)
    implementation(projects.filesystem)
    implementation(projects.imageLoader)
    implementation(projects.injectScopes)
    implementation(projects.logging)
    implementation(projects.network)
    implementation(projects.resourcesApp)
    implementation(projects.strictMode)
    implementation(projects.uiApp)
    implementation(projects.uiCommon)
    implementation(projects.uiMobile)
    implementation(projects.work)
    //baselineProfile(projects.appBaselineProfileGenerator)
    implementation(libs.androidx.activityCompose)
    implementation(libs.androidx.appcompat)
    implementation(libs.androidx.core)
    implementation(libs.androidx.core.splashscreen)
    implementation(libs.androidx.lifecycle.process)
    implementation(libs.androidx.profileInstaller)
    debugImplementation(libs.androidx.compose.uiTooling)
    debugImplementation(libs.leakCanary.android)
    stagingImplementation(libs.leakCanary.android)

    testImplementation(projects.databaseTestFixtures)
    testImplementation(projects.dispatchersTestFixtures)
    testImplementation(projects.filesystemTestFixtures)
    testImplementation(projects.injectTest)
    testImplementation(projects.patterns)
    testImplementation(projects.preferencesTestFixtures)
    testImplementation(projects.uiCommon)
    testImplementation(projects.workTestFixtures)

    testImplementation(libs.androidx.test.core)
    testImplementation(libs.androidx.test.espresso)
    testImplementation(libs.androidx.window)

    androidTestImplementation(libs.androidx.test.core)
    androidTestImplementation(libs.androidx.test.espresso)
    androidTestImplementation(libs.androidx.window)
}

dependencyGuard {
    configuration("releaseRuntimeClasspath")
}
