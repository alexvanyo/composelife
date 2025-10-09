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
import com.android.build.api.dsl.KotlinMultiplatformAndroidDeviceTestCompilation

plugins {
    alias(libs.plugins.convention.kotlinMultiplatform)
    alias(libs.plugins.convention.androidLibrary)
    alias(libs.plugins.convention.androidLibraryCompose)
    alias(libs.plugins.convention.androidLibraryJacoco)
    alias(libs.plugins.convention.androidLibraryKsp)
    alias(libs.plugins.convention.androidLibraryTesting)
    alias(libs.plugins.convention.detekt)
    alias(libs.plugins.convention.kotlinMultiplatformCompose)
    kotlin("plugin.serialization") version libs.versions.kotlin
    alias(libs.plugins.gradleDependenciesSorter)
    alias(libs.plugins.metro)
}

kotlin {
    androidLibrary {
        namespace = "com.alexvanyo.composelife.ui.settings"
        minSdk = 23
        compilations.withType(KotlinMultiplatformAndroidDeviceTestCompilation::class.java) {
            instrumentationRunner = "com.alexvanyo.composelife.test.InjectTestRunner"
        }
        configureGradleManagedDevices(setOf(FormFactor.Mobile), this)
        androidResources { enable = true }
    }
    jvm("desktop")

    sourceSets {
        val commonMain by getting {
            dependencies {
                api(projects.algorithm)
                api(projects.dispatchers)
                api(projects.uiCells)

                implementation(libs.kotlinx.collections.immutable)
                implementation(libs.kotlinx.coroutines.core)
                implementation(libs.kotlinx.datetime)
                implementation(libs.kotlinx.serialization.json)
                implementation(projects.clock)
                implementation(projects.data)
                implementation(projects.injectScopes)
                implementation(projects.logging)
                implementation(projects.navigation)
                implementation(projects.parameterizedString)
                implementation(projects.patterns)
                implementation(projects.resourceState)
                implementation(projects.serialization)
                implementation(projects.sessionValue)
                implementation(projects.uiCommon)
                implementation(projects.uiMobile)
                implementation(projects.uiToolingPreview)
                implementation(projects.work)
            }
        }
        val jbMain by creating {
            dependsOn(commonMain)
            dependencies {
                api(libs.jetbrains.compose.material3.adaptive)

                implementation(libs.androidx.lifecycle.runtime.compose)
                implementation(libs.jetbrains.compose.material3)
                implementation(libs.jetbrains.compose.materialIconsExtended)
                implementation(libs.jetbrains.compose.ui)
                implementation(libs.jetbrains.compose.uiGeometry)
                implementation(libs.jetbrains.compose.uiUtil)
            }
        }
        val desktopMain by getting {
            dependsOn(jbMain)
            configurations["kspDesktop"].dependencies.addAll(
                listOf(
                    projects.sealedEnum.ksp,
                )
            )
            dependencies {
                implementation(compose.desktop.currentOs)
            }
        }
        val androidMain by getting {
            dependsOn(jbMain)
            configurations["kspAndroid"].dependencies.addAll(
                listOf(
                    projects.sealedEnum.ksp,
                )
            )
            dependencies {
                implementation(libs.androidx.activityCompose)
                implementation(libs.androidx.compose.animation)
                implementation(libs.androidx.compose.material3)
                implementation(libs.androidx.compose.materialIconsExtended)
                implementation(libs.androidx.compose.ui)
                implementation(libs.androidx.compose.uiTooling)
                implementation(libs.androidx.compose.uiUtil)
                implementation(libs.androidx.core)
                implementation(libs.androidx.lifecycle.runtime)
                implementation(libs.androidx.navigationEvent)
                implementation(libs.androidx.poolingContainer)
                implementation(libs.androidx.window)
                implementation(libs.kotlinx.coroutines.android)
                implementation(projects.sealedEnum.runtime)
            }
        }
        val commonTest by getting {
            dependencies {
                implementation(libs.kotlinx.coroutines.test)
                implementation(libs.turbine)
                implementation(projects.dispatchersTestFixtures)
                implementation(projects.filesystemTestFixtures)
                implementation(projects.injectTest)
                implementation(projects.kmpAndroidRunner)
                implementation(projects.kmpStateRestorationTester)
                implementation(projects.networkTestFixtures)
                implementation(projects.patterns)
                implementation(projects.preferencesTestFixtures)
                implementation(projects.screenshotTest)
                implementation(projects.testActivity)
                implementation(projects.workTestFixtures)
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
            dependencies {
                implementation(libs.kotlinx.coroutines.swing)
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
    }
}
