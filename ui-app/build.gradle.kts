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
    id("com.alexvanyo.composelife.android.library.compose")
    id("com.alexvanyo.composelife.android.library.jacoco")
    id("com.alexvanyo.composelife.android.library.ksp")
    id("com.alexvanyo.composelife.android.library.testing")
    id("com.alexvanyo.composelife.detekt")
    kotlin("kapt")
}

android {
    namespace = "com.alexvanyo.composelife.ui.app"
    defaultConfig {
        minSdk = 21
    }
    testOptions {
        execution = "ANDROIDX_TEST_ORCHESTRATOR"
    }
    configureGradleManagedDevices(setOf(FormFactor.Mobile), this)
}

kotlin {
    android()

    sourceSets {
        val commonMain by getting {
            dependencies {
                api(projects.algorithm)
                api(projects.clock)
                api(projects.data)
                api(projects.dispatchers)
                implementation(projects.navigation)
                implementation(projects.openglRenderer)
                implementation(projects.patterns)
                api(projects.random)
                implementation(projects.resourceState)
                implementation(projects.snapshotStateSet)
                implementation(projects.uiCommon)

                implementation(libs.kotlinx.datetime)
                implementation(libs.kotlinx.collections.immutable)
                implementation(libs.kotlinx.coroutines.core)
            }
        }
        val androidMain by getting {
            configurations["kspAndroid"].dependencies.add(libs.sealedEnum.ksp.get())
            configurations["kapt"].dependencies.add(libs.dagger.hilt.compiler.get())
            dependencies {
                implementation(libs.androidx.activityCompose)
                implementation(libs.androidx.compose.material3)
                api(libs.androidx.compose.material3.windowSizeClass)
                implementation(libs.androidx.compose.materialIconsExtended)
                implementation(libs.androidx.compose.ui)
                implementation(libs.androidx.compose.uiUtil)
                implementation(libs.androidx.poolingContainer)
                implementation(libs.androidx.compose.uiToolingPreview)
                implementation(libs.androidx.core)
                implementation(libs.androidx.lifecycle.runtime)
                implementation(libs.androidx.room.runtime)
                implementation(libs.androidx.window)
                implementation(libs.kotlinx.coroutines.android)
                implementation(libs.sealedEnum.runtime)
                implementation(libs.dagger.hilt.android)
            }
        }
        val androidDebug by creating {
            dependsOn(androidMain)
            dependencies {
                implementation(libs.androidx.compose.uiTooling)
            }
        }
        val commonTest by getting {
            dependencies {
                implementation(projects.dispatchersTest)
                implementation(projects.hiltTestActivity)
                implementation(projects.patterns)
                implementation(projects.preferencesTest)
                implementation(projects.screenshotTest)

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
            configurations["kaptTest"].dependencies.add(libs.dagger.hilt.compiler.get())
        }
        val androidInstrumentedTest by getting {
            configurations["kaptAndroidTest"].dependencies.add(libs.dagger.hilt.compiler.get())
            configurations["androidTestUtil"].dependencies.add(libs.androidx.test.orchestrator.get())
        }
    }
}

kapt {
    correctErrorTypes = true
}
