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
}

android {
    namespace = "com.alexvanyo.composelife.wear.watchface"
    defaultConfig {
        minSdk = 26
    }
    configureGradleManagedDevices(setOf(FormFactor.Wear), this)
}

kotlin {
    androidTarget()

    sourceSets {
        val commonMain by getting {
            dependencies {
                api(projects.algorithm)
                implementation(projects.geometry)
                implementation(projects.injectScopes)
                implementation(projects.openglRenderer)
                implementation(projects.uiWear)
                implementation(projects.wearWatchfaceConfiguration)

                implementation(libs.kotlinx.datetime)
                implementation(libs.kotlinx.coroutines.core)
                implementation(libs.kotlinInject.runtime)
            }
        }
        val androidMain by getting {
            configurations["kspAndroid"].dependencies.add(libs.kotlinInject.ksp.get())
            configurations["kspAndroid"].dependencies.add(libs.sealedEnum.ksp.get())
            dependencies {
                implementation(libs.androidx.activityCompose)
                implementation(libs.androidx.appcompat)
                implementation(libs.androidx.compose.runtime)
                implementation(libs.androidx.compose.ui)
                implementation(libs.androidx.lifecycle.runtime)
                implementation(libs.androidx.wear.compose.material)
                api(libs.androidx.wear.watchface)
                implementation(libs.androidx.wear.watchface.complications.data)
                implementation(libs.androidx.wear.watchface.complications.dataSource)
                implementation(libs.androidx.wear.watchface.complications.rendering)
                implementation(libs.androidx.wear.watchface.data)
                implementation(libs.androidx.wear.watchface.editor)
                implementation(libs.androidx.wear.watchface.style)
                implementation(libs.kotlinx.coroutines.android)
                implementation(libs.sealedEnum.runtime)
            }
        }
        val commonTest by getting {
            dependencies {
                implementation(libs.kotlinx.coroutines.test)
                implementation(libs.turbine)
            }
        }
        val androidSharedTest by getting {
            dependencies {
                implementation(libs.androidx.compose.uiTestJunit4)
                implementation(libs.androidx.test.espresso)
            }
        }
        val androidUnitTest by getting {
            dependencies {
                implementation(libs.testParameterInjector.junit4)
            }
        }
        val androidInstrumentedTest by getting {
            dependencies {
                compileOnly(libs.apiGuardian.api)
                compileOnly(libs.google.autoValue.annotations)
            }
        }
    }
}
