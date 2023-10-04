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

plugins {
    alias(libs.plugins.convention.kotlinMultiplatform)
    alias(libs.plugins.convention.androidLibrary)
    alias(libs.plugins.convention.androidLibraryKsp)
    alias(libs.plugins.convention.detekt)
}

android {
    namespace = "com.alexvanyo.composelife.dispatcherstest"
    defaultConfig {
        minSdk = 21
    }
}

kotlin {
    androidTarget()
    jvm()

    sourceSets {
        val commonMain by getting {
            dependencies {
                api(projects.dispatchers)
                implementation(projects.injectScopes)

                api(libs.jetbrains.compose.uiTestJunit4)
                api(libs.kotlinx.coroutines.test)
                api(libs.kotlinx.datetime)
                implementation(libs.kotlinInject.runtime)
                implementation(libs.androidx.lifecycle.viewmodel)
            }
        }
        val jvmMain by getting {
            configurations["kspJvm"].dependencies.add(libs.kotlinInject.ksp.get())
        }
        val androidMain by getting {
            configurations["kspAndroid"].dependencies.add(libs.kotlinInject.ksp.get())
            dependencies {
                api(libs.androidx.test.junit)
            }
        }
    }
}
