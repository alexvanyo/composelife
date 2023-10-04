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
}

android {
    namespace = "com.alexvanyo.composelife.ui.app"
    defaultConfig {
        minSdk = 21
    }
    configureGradleManagedDevices(setOf(FormFactor.Mobile), this)
}

kotlin {
    androidTarget()
    jvm()

    sourceSets {
        val commonMain by getting {
            dependencies {
                api(projects.algorithm)
                api(projects.clock)
                api(projects.data)
                api(projects.dispatchers)
                implementation(projects.injectScopes)
                implementation(projects.navigation)
                implementation(projects.openglRenderer)
                implementation(projects.patterns)
                implementation(projects.parameterizedString)
                api(projects.random)
                implementation(projects.resourceState)
                implementation(projects.snapshotStateSet)
                implementation(projects.uiCommon)

                implementation(libs.jetbrains.compose.material3)
                implementation(libs.jetbrains.compose.materialIconsExtended)
                implementation(libs.jetbrains.compose.ui)
                implementation(libs.jetbrains.compose.uiUtil)
                implementation(libs.kotlinx.datetime)
                implementation(libs.kotlinx.collections.immutable)
                implementation(libs.kotlinx.coroutines.core)
                implementation(libs.kotlinInject.runtime)
            }
        }
        val jvmMain by getting {
            configurations["kspJvm"].dependencies.add(libs.kotlinInject.ksp.get())
            configurations["kspJvm"].dependencies.add(libs.sealedEnum.ksp.get())
            dependencies {
                implementation(compose.desktop.currentOs)
            }
        }
        val androidMain by getting {
            configurations["kspAndroid"].dependencies.add(libs.kotlinInject.ksp.get())
            configurations["kspAndroid"].dependencies.add(libs.sealedEnum.ksp.get())
            dependencies {
                implementation(libs.androidx.activityCompose)
                implementation(libs.androidx.compose.animation)
                implementation(libs.androidx.compose.material3)
                api(libs.androidx.compose.material3.windowSizeClass)
                implementation(libs.androidx.compose.materialIconsExtended)
                implementation(libs.androidx.compose.ui)
                implementation(libs.androidx.compose.uiUtil)
                implementation(libs.androidx.poolingContainer)
                implementation(libs.androidx.compose.uiTooling)
                implementation(libs.androidx.compose.uiToolingPreview)
                implementation(libs.androidx.core)
                implementation(libs.androidx.lifecycle.runtime)
                implementation(libs.androidx.window)
                implementation(libs.kotlinx.coroutines.android)
                implementation(libs.sealedEnum.runtime)
                implementation(libs.sqldelight.androidDriver)
            }
        }
        val commonTest by getting {
            dependencies {
                implementation(projects.dispatchersTest)
                implementation(projects.injectTestActivity)
                implementation(projects.patterns)
                implementation(projects.preferencesTest)
                implementation(projects.screenshotTest)
                implementation(projects.testActivity)
                implementation(projects.kmpAndroidRunner)
                implementation(projects.kmpStateRestorationTester)

                implementation(libs.kotlinx.coroutines.test)
                implementation(libs.turbine)
            }
        }
        val androidSharedTest by getting {
            dependencies {
                implementation(libs.androidx.compose.uiTestJunit4)
                implementation(libs.androidx.test.core)
                implementation(libs.androidx.test.espresso)
                implementation(libs.androidx.test.junit)
                implementation(libs.accompanist.testharness)
            }
        }
        val androidUnitTest by getting {
            configurations["kspAndroidTest"].dependencies.add(libs.kotlinInject.ksp.get())
        }
        val androidInstrumentedTest by getting {
            configurations["kspAndroidAndroidTest"].dependencies.add(libs.kotlinInject.ksp.get())
        }
        val jvmTest by getting {
            configurations["kspJvmTest"].dependencies.add(libs.kotlinInject.ksp.get())
        }
    }
}
