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
import org.jetbrains.kotlin.gradle.ExperimentalWasmDsl
import kotlin.jvm.java

plugins {
    alias(libs.plugins.convention.kotlinMultiplatform)
    alias(libs.plugins.convention.androidLibrary)
    alias(libs.plugins.convention.androidLibraryCompose)
    alias(libs.plugins.convention.androidLibraryJacoco)
    alias(libs.plugins.convention.androidLibraryKsp)
    alias(libs.plugins.convention.androidLibraryTesting)
    alias(libs.plugins.convention.detekt)
    kotlin("plugin.serialization") version libs.versions.kotlin
    alias(libs.plugins.gradleDependenciesSorter)
    alias(libs.plugins.metro)
}

kotlin {
    jvm("desktop")
    androidLibrary {
        namespace = "com.alexvanyo.composelife.preferences"
        minSdk = 23
        configureGradleManagedDevices(enumValues<FormFactor>().toSet(), this)
    }
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
                api(libs.androidx.compose.runtime)
                api(libs.kotlinx.coroutines.core)
                api(libs.kotlinx.datetime)
                api(projects.dispatchers)
                api(projects.logging)
                api(projects.resourceState)
                api(projects.sealedEnum.runtime)
                api(projects.sessionValue)
                api(projects.updatable)

                implementation(libs.androidx.dataStore.core)
                implementation(libs.androidx.dataStore.core.okio)
                implementation(libs.okio)
                implementation(projects.filesystem)
                implementation(projects.injectScopes)
                implementation(projects.preferencesProto)
                implementation(projects.serialization)
            }
        }
        val jbMain by creating {
            dependsOn(commonMain)
        }
        val nonBrowserMain by creating {
            dependsOn(jbMain)
        }
        val androidMain by getting {
            dependsOn(nonBrowserMain)
            configurations["kspAndroid"].dependencies.addAll(
                listOf(
                    projects.sealedEnum.ksp,
                )
            )
            dependencies {
                api(libs.androidx.dataStore)
                api(libs.kotlinx.coroutines.android)
            }
        }
        val desktopMain by getting {
            dependsOn(nonBrowserMain)
            configurations["kspDesktop"].dependencies.addAll(
                listOf(
                    projects.sealedEnum.ksp,
                )
            )
        }
        val wasmJsMain by getting {
            dependsOn(jbMain)
            configurations["kspWasmJs"].dependencies.addAll(
                listOf(
                    projects.sealedEnum.ksp,
                )
            )
            dependencies {
                implementation(libs.kotlinx.browser)
            }
        }
        val commonTest by getting {
            dependencies {
                implementation(projects.dispatchersTestFixtures)
                implementation(projects.kmpAndroidRunner)
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
        val jvmTest by creating {
            dependsOn(jbTest)
        }
        val desktopTest by getting {
            dependsOn(jvmTest)
        }
        val androidSharedTest by getting {
            dependsOn(jvmTest)
            dependencies {
                implementation(libs.androidx.test.core)
                implementation(libs.androidx.test.junit)
                implementation(libs.androidx.test.runner)
            }
        }
        val wasmJsTest by getting {
            dependsOn(jbTest)
        }
    }
}
