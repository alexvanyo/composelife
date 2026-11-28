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
import org.jetbrains.kotlin.gradle.ExperimentalWasmDsl

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

kotlin {
    android {
        namespace = "com.alexvanyo.composelife.serialization"
        minSdk = 24
        configureGradleManagedDevices(enumValues<FormFactor>().toSet(), this)
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
                api(projects.sealedEnum.runtime)
                api(libs.androidx.compose.runtime)
                api(libs.androidx.compose.runtime.saveable)
                api(libs.androidx.savedState)
                api(libs.androidx.savedState.compose)
                api(libs.kotlinx.serialization.core)
            }
        }
        val jbMain = create("jbMain") {
            dependsOn(commonMain)
            dependencies {
                api(libs.jetbrains.compose.uiGeometry)
                api(libs.jetbrains.compose.uiUnit)

                implementation(libs.jetbrains.compose.uiUtil)
            }
        }
        val jvmMain = create("jvmMain") {
            dependsOn(jbMain)
        }
        val desktopMain = getByName("desktopMain") {
            dependsOn(jvmMain)
        }
        val androidMain = getByName("androidMain") {
            dependsOn(jvmMain)
        }
        val wasmJsMain = getByName("wasmJsMain") {
            dependsOn(jbMain)
            dependencies {
                implementation(libs.jetbrains.compose.ui)
            }
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
                implementation(libs.jetbrains.compose.foundation)
                implementation(libs.jetbrains.compose.uiTest)
                implementation(libs.kotlinx.serialization.json)
            }
        }
        val jvmTest = create("jvmTest") {
            dependsOn(jbTest)
        }
        val desktopTest = getByName("desktopTest") {
            dependsOn(jvmTest)
            dependencies {
                implementation(compose.desktop.currentOs)
            }
        }
        val androidSharedTest = getByName("androidSharedTest") {
            dependsOn(jvmTest)
            dependencies {
                implementation(libs.androidx.compose.ui)
            }
        }
        val wasmJsTest = getByName("wasmJsTest") {
            dependsOn(jbTest)
        }
    }
}
