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
import com.alexvanyo.composelife.buildlogic.jvmMolecule
import org.gradle.api.attributes.java.TargetJvmEnvironment.TARGET_JVM_ENVIRONMENT_ATTRIBUTE
import org.jetbrains.kotlin.gradle.InternalKotlinGradlePluginApi

plugins {
    alias(libs.plugins.convention.kotlinMultiplatform)
    alias(libs.plugins.convention.androidLibrary)
    alias(libs.plugins.convention.androidLibraryCompose)
    alias(libs.plugins.convention.androidLibraryJacoco)
    alias(libs.plugins.convention.androidLibraryKsp)
    alias(libs.plugins.convention.androidLibraryTesting)
    alias(libs.plugins.convention.detekt)
    alias(libs.plugins.convention.kotlinMultiplatformCompose)
    alias(libs.plugins.gradleDependenciesSorter)
}

android {
    namespace = "com.alexvanyo.composelife.ui.mobile"
    defaultConfig {
        minSdk = 21
    }
    configureGradleManagedDevices(setOf(FormFactor.Mobile), this)
}

kotlin {
    androidTarget()
    jvm("desktop")

    sourceSets {
        val commonMain by getting {
            dependencies {
                api(projects.preferences)

                implementation(projects.resourceState)
            }
        }
        val jvmMain by creating {
            dependsOn(commonMain)
        }
        val jbMain by creating {
            dependsOn(jvmMain)
            dependencies {
                implementation(libs.jetbrains.compose.material3)
            }
        }
        val desktopMain by getting {
            dependsOn(jbMain)
            dependencies {
                implementation(compose.desktop.currentOs)
            }
        }
        val androidMain by getting {
            dependsOn(jbMain)
            dependencies {
                implementation(libs.androidx.compose.material3)
            }
        }
        val commonTest by getting {}
        val jvmTest by creating {
            dependsOn(commonTest)
        }
        val jbTest by creating {
            dependsOn(jvmTest)
        }
        val desktopTest by getting {
            dependsOn(jbTest)
        }
        val androidSharedTest by getting {
            dependsOn(jbTest)
        }
    }
}
