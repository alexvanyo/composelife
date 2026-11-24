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
import com.android.build.api.dsl.KotlinMultiplatformAndroidDeviceTestCompilation
import kotlin.jvm.java

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

kotlin {
    android {
        namespace = "com.alexvanyo.composelife.ui.common.screenshottests"
        minSdk = 24
    }
    jvm("desktop")

    sourceSets {
        val commonMain = getByName("commonMain") {
            dependencies {
                implementation(projects.uiCommon)
                implementation(libs.jetbrains.compose.foundation)
                implementation(libs.jetbrains.compose.ui)
            }
        }
        val androidMain = getByName("androidMain") {
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
        val commonTest = getByName("commonTest") {
            dependencies {
                implementation(projects.testActivity)
            }
        }
        val jvmTest = create("jvmTest") {
            dependsOn(commonTest)
            dependencies {
                implementation(libs.testParameterInjector.junit4)
            }
        }
        val jbTest = create("jbTest") {
            dependsOn(jvmTest)
            dependencies {
                implementation(libs.jetbrains.compose.uiTest)
            }
        }
        val desktopTest = getByName("desktopTest") {
            dependsOn(jbTest)
        }
        val androidSharedTest = getByName("androidSharedTest") {
            dependsOn(jbTest)
        }
        val androidHostTest = getByName("androidHostTest") {
            configurations["kspAndroidHostTest"].dependencies.addAll(
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
