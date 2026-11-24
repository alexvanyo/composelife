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
import org.jetbrains.kotlin.gradle.ExperimentalWasmDsl

plugins {
    alias(libs.plugins.convention.kotlinMultiplatform)
    alias(libs.plugins.convention.androidLibrary)
    alias(libs.plugins.convention.androidLibraryCompose)
    alias(libs.plugins.convention.androidLibraryKsp)
    alias(libs.plugins.convention.androidLibraryTesting)
    alias(libs.plugins.convention.detekt)
    alias(libs.plugins.convention.kotlinMultiplatformCompose)
    alias(libs.plugins.gradleDependenciesSorter)
}

kotlin {
    android {
        namespace = "com.alexvanyo.composelife.ui.mobile"
        minSdk = 24
        configureGradleManagedDevices(setOf(FormFactor.Mobile), this)
    }
    jvm("desktop")
    @OptIn(ExperimentalWasmDsl::class)
    wasmJs {
        browser {
            testTask {
                useKarma {
                    useChromiumHeadless()
                }
            }
        }
    }

    sourceSets {
        val commonMain = getByName("commonMain") {
            dependencies {
                api(projects.parameterizedString)
                api(projects.preferences)
                api(libs.kotlinx.collections.immutable)

                implementation(projects.logging)
                implementation(projects.navigation)
                implementation(projects.resourceState)
                implementation(projects.serialization)
                implementation(projects.uiCommon)
                implementation(projects.uiToolingPreview)
                implementation(libs.androidx.navigationEvent)
            }
        }
        val jvmMain = create("jvmMain") {
            dependsOn(commonMain)
        }
        val jbMain = create("jbMain") {
            dependsOn(jvmMain)
            dependencies {
                implementation(libs.jetbrains.compose.material3)
                implementation(libs.jetbrains.compose.materialIconsExtended)
                implementation(libs.jetbrains.navigation3.ui)
            }
        }
        val nonAndroidMain = create("nonAndroidMain") {
            dependsOn(jbMain)
        }
        val desktopMain = getByName("desktopMain") {
            dependsOn(nonAndroidMain)
            configurations["kspDesktop"].dependencies.add(projects.sealedEnum.ksp)
            dependencies {
                implementation(compose.desktop.currentOs)
            }
        }
        val androidMain = getByName("androidMain") {
            dependsOn(jbMain)
            configurations["kspAndroid"].dependencies.add(projects.sealedEnum.ksp)
            dependencies {
                implementation(libs.androidx.activityCompose)
                implementation(libs.androidx.compose.material3)
                implementation(libs.androidx.compose.uiTooling)
                implementation(libs.androidx.xr.compose)
            }
        }
        val wasmJsMain = getByName("wasmJsMain") {
            dependsOn(nonAndroidMain)
            configurations["kspWasmJs"].dependencies.add(projects.sealedEnum.ksp)
        }
        val commonTest = getByName("commonTest") {
            dependencies {
                implementation(projects.dispatchersTestFixtures)
                implementation(projects.injectTest)
                implementation(projects.kmpAndroidRunner)
                implementation(projects.kmpStateRestorationTester)
                implementation(projects.testActivity)
                implementation(libs.kotlinx.coroutines.test)
            }
        }
        val jbTest = create("jbTest") {
            dependsOn(commonTest)
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
        val wasmJsTest = getByName("wasmJsTest") {
            dependsOn(jbTest)
        }
    }
}
