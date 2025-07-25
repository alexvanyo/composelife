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
import org.jetbrains.kotlin.gradle.ExperimentalWasmDsl

plugins {
    alias(libs.plugins.convention.kotlinMultiplatform)
    alias(libs.plugins.convention.androidLibrary)
    alias(libs.plugins.convention.androidLibraryJacoco)
    alias(libs.plugins.convention.androidLibraryKsp)
    alias(libs.plugins.convention.androidLibraryTesting)
    alias(libs.plugins.convention.detekt)
    kotlin("plugin.serialization") version libs.versions.kotlin
    alias(libs.plugins.gradleDependenciesSorter)
    alias(libs.plugins.metro)
}

android {
    namespace = "com.alexvanyo.composelife.preferences"
    defaultConfig {
        minSdk = 21
    }
    configureGradleManagedDevices(enumValues<FormFactor>().toSet(), this)
}

kotlin {
    jvm("desktop")
    androidTarget()
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
        val commonMain by getting {
            dependencies {
                api(libs.jetbrains.compose.runtime)
                api(libs.kotlinx.coroutines.core)
                api(libs.kotlinx.datetime)
                api(projects.dispatchers)
                api(projects.logging)
                api(projects.resourceState)
                api(projects.sessionValue)
                api(projects.updatable)

                implementation(libs.okio)
                implementation(projects.filesystem)
                implementation(projects.injectScopes)
                implementation(projects.preferencesProto)
                implementation(projects.serialization)
            }
        }
        val jbMain by creating {
            dependsOn(commonMain)
            dependencies {
                api(libs.androidx.dataStore)
                api(libs.sealedEnum.runtime)

                implementation(libs.androidx.dataStore.core.okio)
            }
        }
        val androidMain by getting {
            dependsOn(jbMain)
            configurations["kspAndroid"].dependencies.addAll(
                listOf(
                    libs.sealedEnum.ksp.get(),
                )
            )
            dependencies {
                api(libs.kotlinx.coroutines.android)
            }
        }
        val desktopMain by getting {
            dependsOn(jbMain)
            configurations["kspDesktop"].dependencies.addAll(
                listOf(
                    libs.sealedEnum.ksp.get(),
                )
            )
        }
        val commonTest by getting {
            dependencies {
                implementation(projects.dispatchersTest)
                implementation(projects.kmpAndroidRunner)
                implementation(projects.preferencesTest)
            }
        }
        val jbTest by creating {
            dependsOn(commonTest)
            dependencies {
                implementation(libs.kotlinx.coroutines.test)
                implementation(libs.okio.fakefilesystem)
                implementation(libs.turbine)
            }
        }
        val desktopTest by getting {
            dependsOn(jbTest)
        }
        val androidSharedTest by getting {
            dependsOn(jbTest)
            dependencies {
                implementation(libs.androidx.test.core)
                implementation(libs.androidx.test.junit)
                implementation(libs.androidx.test.runner)
            }
        }
    }
}
