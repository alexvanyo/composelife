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
    namespace = "com.alexvanyo.composelife.ui.common"
    defaultConfig {
        minSdk = 21
    }
    configureGradleManagedDevices(FormFactor.All, this)
}

kotlin {
    androidTarget()
    jvm("desktop")
    jvmMolecule(this)

    sourceSets {
        val commonMain by getting {
            dependencies {
                implementation(libs.androidx.annotation)
                implementation(libs.kotlinx.coroutines.core)
                implementation(libs.kotlinx.serialization.json)
                implementation(libs.uuid)
                implementation(projects.dispatchers)
                implementation(projects.geometry)
                implementation(projects.navigation)
                implementation(projects.snapshotStateSet)
                implementation(projects.uiToolingPreview)
                implementation(projects.updatable)
            }
        }
        val jvmMain by creating {
            dependsOn(commonMain)
            dependencies {
                implementation(libs.jetbrains.compose.uiGeometry)
                implementation(libs.jetbrains.compose.uiUnit)
                implementation(libs.jetbrains.compose.uiUtil)
                implementation(libs.sealedEnum.runtime)
            }
        }
        val moleculeMain by getting {
            dependsOn(jvmMain)
        }
        val jbMain by creating {
            dependsOn(jvmMain)
            dependencies {
                implementation(libs.jetbrains.compose.animation)
                implementation(libs.jetbrains.compose.foundation)
                implementation(libs.jetbrains.compose.materialIconsExtended)
                implementation(libs.jetbrains.compose.ui)
            }
        }
        val desktopMain by getting {
            dependsOn(jbMain)
            configurations["kspDesktop"].dependencies.add(libs.sealedEnum.ksp.get())
            dependencies {
                implementation(compose.desktop.currentOs)
            }
        }
        val androidMain by getting {
            dependsOn(jbMain)
            configurations["kspAndroid"].dependencies.add(libs.sealedEnum.ksp.get())
            dependencies {
                implementation(libs.androidx.activityCompose)
                implementation(libs.androidx.compose.foundation)
                implementation(libs.androidx.compose.materialIconsExtended)
                implementation(libs.androidx.compose.uiTooling)
                implementation(libs.androidx.core)
                implementation(libs.androidx.lifecycle.runtime)
                implementation(libs.androidx.lifecycle.runtime.compose)
                implementation(libs.kotlinx.coroutines.android)
            }
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
        val moleculeTest by getting {
            dependsOn(jvmTest)
        }
        val jbTest by creating {
            dependsOn(jvmTest)
            dependencies {
                implementation(libs.jetbrains.compose.uiTestJunit4)
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
