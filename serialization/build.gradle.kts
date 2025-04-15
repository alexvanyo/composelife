/*
 * Copyright 2024 The Android Open Source Project
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
    alias(libs.plugins.convention.androidLibraryTesting)
    alias(libs.plugins.convention.detekt)
    alias(libs.plugins.convention.kotlinMultiplatformCompose)
    kotlin("plugin.serialization") version libs.versions.kotlin
    alias(libs.plugins.gradleDependenciesSorter)
}

android {
    namespace = "com.alexvanyo.composelife.serialization"
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
                api(libs.androidx.savedState)
                api(libs.androidx.savedState.compose)
                api(libs.jetbrains.compose.runtime)
                api(libs.jetbrains.compose.runtime.saveable)
                api(libs.kotlinx.serialization.core)
            }
        }
        val jvmMain by creating {
            dependsOn(commonMain)
            dependencies {
                api(libs.jetbrains.compose.uiGeometry)
                api(libs.jetbrains.compose.uiUnit)
                api(libs.sealedEnum.runtime)

                implementation(libs.jetbrains.compose.uiUtil)
            }
        }
        val jbMain by creating {
            dependsOn(jvmMain)
        }
        val desktopMain by getting {
            dependsOn(jbMain)
        }
        val androidMain by getting {
            dependsOn(jbMain)
        }
        val commonTest by getting {
            dependencies {
                implementation(libs.kotlinx.coroutines.test)
                implementation(projects.dispatchersTest)
                implementation(projects.kmpAndroidRunner)
                implementation(projects.kmpStateRestorationTester)
                implementation(projects.testActivity)
            }
        }
        val jvmTest by creating {
            dependsOn(commonTest)
        }
        val jbTest by creating {
            dependsOn(jvmTest)
            dependencies {
                implementation(libs.jetbrains.compose.foundation)
                implementation(libs.jetbrains.compose.uiTest)
            }
        }
        val desktopTest by getting {
            dependsOn(jbTest)
        }
        val androidSharedTest by getting {
            dependsOn(jbTest)
        }
    }
}
