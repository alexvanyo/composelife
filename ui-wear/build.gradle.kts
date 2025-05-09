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
    alias(libs.plugins.convention.androidLibraryKsp)
    alias(libs.plugins.convention.androidLibraryRoborazzi)
    alias(libs.plugins.convention.androidLibraryTesting)
    alias(libs.plugins.convention.detekt)
    alias(libs.plugins.roborazzi)
    alias(libs.plugins.gradleDependenciesSorter)
}

android {
    namespace = "com.alexvanyo.composelife.ui.wear"
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
                api(projects.updatable)

                implementation(libs.kotlinx.coroutines.core)
                implementation(libs.kotlinx.datetime)
                implementation(libs.kotlinx.serialization.core)
                implementation(projects.logging)
                implementation(projects.navigation)
                implementation(projects.parameterizedString)
                implementation(projects.resourceState)
                implementation(projects.resourcesWear)
                implementation(projects.serialization)
                implementation(projects.uiCommon)
                implementation(projects.uiToolingPreview)
                implementation(projects.wearWatchfaceConfiguration)
            }
        }
        val androidMain by getting {
            configurations["kspAndroid"].dependencies.add(libs.sealedEnum.ksp.get())
            configurations["kspAndroid"].dependencies.add(libs.showkase.processor.get())
            dependencies {
                implementation(libs.androidx.activityCompose)
                implementation(libs.androidx.compose.foundation)
                implementation(libs.androidx.compose.runtime)
                implementation(libs.androidx.core)
                implementation(libs.androidx.wear.compose.foundation)
                implementation(libs.androidx.wear.compose.material3)
                implementation(libs.androidx.wear.compose.uiToolingPreview)
                implementation(libs.androidx.wear.watchface)
                implementation(libs.androidx.wear.watchface.complications.data)
                implementation(libs.androidx.wear.watchface.complications.dataSource)
                implementation(libs.androidx.wear.watchface.complications.rendering)
                implementation(libs.androidx.wear.watchface.data)
                implementation(libs.androidx.wear.watchface.editor)
                implementation(libs.androidx.wear.watchface.style)
                implementation(libs.kotlinx.coroutines.android)
                implementation(libs.sealedEnum.runtime)
                implementation(libs.showkase.runtime)
            }
        }
        val commonTest by getting {
            dependencies {
                implementation(libs.kotlinx.coroutines.test)
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
        val androidSharedTest by getting {
            dependsOn(jbTest)
            dependencies {
                implementation(libs.androidx.compose.uiTest)
                implementation(libs.androidx.test.core)
                implementation(libs.androidx.test.espresso)
                implementation(libs.androidx.test.junit)
            }
        }
        val androidUnitTest by getting {
            configurations["kspAndroidTest"].dependencies.add(libs.showkase.processor.get())
            dependencies {
                implementation(projects.roborazziShowkaseScreenshotTest)
            }
        }
    }
}
