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
    id("com.alexvanyo.composelife.kotlin.multiplatform")
    id("com.alexvanyo.composelife.android.library")
    id("com.alexvanyo.composelife.android.library.jacoco")
    id("com.alexvanyo.composelife.android.library.ksp")
    id("com.alexvanyo.composelife.android.library.testing")
    id("com.alexvanyo.composelife.detekt")
    kotlin("kapt")
}

android {
    namespace = "com.alexvanyo.composelife.preferences"
    defaultConfig {
        minSdk = 21
    }
    configureGradleManagedDevices(FormFactor.All, this)
}

kotlin {
    jvm()
    android()

    sourceSets {
        val commonMain by getting {
            configurations["kapt"].dependencies.add(libs.dagger.hilt.compiler.get())
            dependencies {
                api(projects.dispatchers)
                implementation(projects.preferencesProto)
                api(projects.resourceState)
                api(projects.updatable)

                api(libs.kotlinx.coroutines.core)
                api(libs.jetbrains.compose.runtime)
                api(libs.androidx.dataStore)
                implementation(libs.androidx.dataStore.core.okio)
                implementation(libs.okio)
                api(libs.sealedEnum.runtime)

                implementation(libs.dagger.hilt.core)
            }
        }
        val androidMain by getting {
            configurations["kspAndroid"].dependencies.add(libs.sealedEnum.ksp.get())
            dependencies {
                api(libs.kotlinx.coroutines.android)
                implementation(libs.androidx.lifecycle.viewmodel)
                implementation(libs.androidx.lifecycle.viewmodel.savedstate)
                implementation(libs.dagger.hilt.android)
            }
        }
        val jvmMain by getting {
            configurations["kspJvm"].dependencies.add(libs.sealedEnum.ksp.get())
        }
        val commonTest by getting {
            dependencies {
                implementation(projects.preferencesTest)
                implementation(projects.dispatchersTest)

                implementation(libs.kotlinx.coroutines.test)
                implementation(libs.turbine)
                implementation(libs.okio.fakefilesystem)
            }
        }
        val androidSharedTest by getting {
            dependencies {
                implementation(libs.androidx.test.core)
                implementation(libs.androidx.test.junit)
                implementation(libs.androidx.test.runner)
            }
        }
    }
}

kapt {
    correctErrorTypes = true
}
