/*
 * Copyright 2023 The Android Open Source Project
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
    alias(libs.plugins.convention.androidLibraryRoborazzi)
    alias(libs.plugins.convention.androidLibraryTesting)
    alias(libs.plugins.convention.detekt)
    alias(libs.plugins.convention.kotlinMultiplatformCompose)
    alias(libs.plugins.roborazzi)
    alias(libs.plugins.gradleDependenciesSorter)
}

android {
    namespace = "com.alexvanyo.composelife.ui.common.screenshottests"
    defaultConfig {
        minSdk = 21
    }
    configureGradleManagedDevices(enumValues<FormFactor>().toSet(), this)
}

kotlin {
    androidTarget()
    jvm("desktop")

    sourceSets {
        val commonMain by getting {
            dependencies {
                implementation(libs.jetbrains.compose.foundation)
                implementation(libs.jetbrains.compose.ui)
                implementation(projects.uiCommon)
            }
        }
        val androidMain by getting {
            configurations["kspAndroid"].dependencies.addAll(
                listOf(
                    libs.showkase.processor.get(),
                )
            )
            dependencies {
                implementation(libs.androidx.compose.uiTest)
                implementation(libs.androidx.compose.uiTooling)
                implementation(libs.androidx.core)
                implementation(libs.showkase.runtime)
            }
        }
        val commonTest by getting {
            dependencies {
                implementation(projects.testActivity)
            }
        }
        val jvmTest by creating {
            dependsOn(commonTest)
            dependencies {
                implementation(libs.testParameterInjector.junit4)
            }
        }
        val jbTest by creating {
            dependsOn(jvmTest)
            dependencies {
                implementation(libs.jetbrains.compose.uiTest)
            }
        }
        val desktopTest by getting {
            dependsOn(jbTest)
        }
        val androidSharedTest by getting {
            dependsOn(jbTest)
        }
        val androidUnitTest by getting {
            configurations["kspAndroidTest"].dependencies.addAll(
                listOf(
                    libs.showkase.processor.get(),
                )
            )
            dependencies {
                implementation(projects.roborazziShowkaseScreenshotTest)
            }
        }
    }
}
