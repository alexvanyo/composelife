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
    kotlin("plugin.serialization") version libs.versions.kotlin
    alias(libs.plugins.gradleDependenciesSorter)
    alias(libs.plugins.metro)
}

ksp {
    arg("skipPrivatePreviews", "true")
}

kotlin {
    androidLibrary {
        namespace = "com.alexvanyo.composelife.ui.app.screenshottests"
        minSdk = 23
        compilations.withType(KotlinMultiplatformAndroidDeviceTestCompilation::class.java) {
            instrumentationRunner = "com.alexvanyo.composelife.test.InjectTestRunner"
        }
        configureGradleManagedDevices(setOf(FormFactor.Mobile), this)
    }
    jvm("desktop")

    sourceSets {
        val commonMain by getting {
            dependencies {
                implementation(projects.databaseTest)
                implementation(projects.dispatchersTest)
                implementation(projects.filesystemTest)
                implementation(projects.injectScopes)
                implementation(projects.networkTest)
                implementation(projects.patterns)
                implementation(projects.preferencesTest)
                implementation(projects.randomTest)
                implementation(projects.uiApp)
                implementation(projects.uiCommon)
                implementation(projects.uiMobile)
                implementation(projects.uiToolingPreview)
                implementation(projects.work)
                implementation(projects.workTest)
            }
        }
        val jbMain by creating {
            dependsOn(commonMain)
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
            configurations["kspAndroid"].dependencies.addAll(listOf(
                libs.showkase.processor.get(),
            ))
            dependencies {
                implementation(libs.androidx.activityCompose)
                implementation(libs.androidx.compose.uiTooling)
                implementation(libs.androidx.compose.uiUtil)
                implementation(libs.androidx.core)
                implementation(libs.showkase.runtime)
            }
        }
        val commonTest by getting {
            dependencies {
                implementation(libs.kotlinx.coroutines.test)
                implementation(libs.turbine)
                implementation(projects.injectTest)
                implementation(projects.kmpAndroidRunner)
                implementation(projects.kmpStateRestorationTester)
                implementation(projects.patterns)
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
        val androidHostTest by getting {
            configurations["kspAndroidHostTest"].dependencies.addAll(listOf(
                libs.showkase.processor.get(),
            ))
            dependencies {
                implementation(projects.roborazziShowkaseScreenshotTest)
            }
        }
    }
}
