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
    alias(libs.plugins.convention.androidLibrary)
    alias(libs.plugins.convention.androidLibraryCompose)
    alias(libs.plugins.convention.androidLibraryJacoco)
    alias(libs.plugins.convention.androidLibraryKsp)
    alias(libs.plugins.convention.androidLibraryTesting)
    alias(libs.plugins.convention.detekt)
    alias(libs.plugins.convention.kotlinMultiplatformCompose)
    kotlin("plugin.serialization") version libs.versions.kotlin
}

android {
    namespace = "com.alexvanyo.composelife.algorithm"
    defaultConfig {
        minSdk = 21
    }
    configureGradleManagedDevices(FormFactor.All, this)
}

kotlin {
    androidTarget()
    jvm()

    sourceSets {
        val commonMain by getting {
            dependencies {
                api(projects.dispatchers)
                api(projects.geometry)
                implementation(projects.injectScopes)
                api(projects.parameterizedString)
                api(projects.preferences)
                api(projects.updatable)

                implementation(libs.androidx.annotation)
                implementation(libs.kotlinx.datetime)
                implementation(libs.kotlinx.coroutines.core)
                implementation(libs.kotlinx.serialization.json)
                implementation(libs.jetbrains.compose.ui)
                implementation(libs.jetbrains.compose.runtime)
                implementation(libs.sealedEnum.runtime)
                implementation(libs.guava.android)
                implementation(libs.kotlinInject.runtime)
            }
        }
        val androidMain by getting {
            configurations["kspAndroid"].dependencies.add(libs.kotlinInject.ksp.get())
            configurations["kspAndroid"].dependencies.add(libs.sealedEnum.ksp.get())
            dependencies {
                implementation(libs.androidx.tracing)
                implementation(libs.kotlinx.coroutines.android)
            }
        }
        val jvmMain by getting {
            configurations["kspJvm"].dependencies.add(libs.kotlinInject.ksp.get())
            configurations["kspJvm"].dependencies.add(libs.sealedEnum.ksp.get())
        }
        val commonTest by getting {
            dependencies {
                implementation(projects.dispatchersTest)
                implementation(projects.kmpAndroidRunner)
                implementation(projects.kmpStateRestorationTester)
                implementation(projects.patterns)

                implementation(libs.kotlinx.coroutines.test)
                implementation(libs.turbine)
                implementation(libs.testParameterInjector.junit4)
            }
        }
        val androidSharedTest by getting {
            dependencies {
                implementation(projects.preferencesTest)
                implementation(projects.testActivity)

                implementation(libs.androidx.compose.uiTestJunit4)
                implementation(libs.androidx.test.core)
                implementation(libs.androidx.test.espresso)
            }
        }
    }
}
