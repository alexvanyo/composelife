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
    alias(libs.plugins.convention.androidLibraryCompose)
    alias(libs.plugins.convention.androidLibraryJacoco)
    alias(libs.plugins.convention.androidLibraryKsp)
    alias(libs.plugins.convention.androidLibraryTesting)
    alias(libs.plugins.convention.detekt)
    alias(libs.plugins.convention.kotlinMultiplatformCompose)
    alias(libs.plugins.convention.lean)
    kotlin("plugin.serialization") version libs.versions.kotlin
    alias(libs.plugins.gradleDependenciesSorter)
    alias(libs.plugins.metro)
    alias(libs.plugins.testBalloon)
}

composeCompiler {
    targetKotlinPlatforms.set(
        setOf(
            org.jetbrains.kotlin.gradle.plugin.KotlinPlatformType.androidJvm,
            org.jetbrains.kotlin.gradle.plugin.KotlinPlatformType.jvm,
            org.jetbrains.kotlin.gradle.plugin.KotlinPlatformType.wasm,
        ),
    )
}

lean {
    target = "Algorithm:static"
    packageName = "com.alexvanyo.composelife.algorithm"
    entries {
        register("algorithm") {
            leanFile = "Algorithm/HashLife.lean"
        }
    }
}

kotlin {
    androidLibrary {
        namespace = "com.alexvanyo.composelife.algorithm"
        minSdk = 24
        configureGradleManagedDevices(enumValues<FormFactor>().toSet(), this)
    }
    jvm("desktop") {}
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
                api(projects.geometry)
            }
        }
        val jbMain by creating {
            dependsOn(commonMain)
            dependencies {
                api(projects.dispatchers)
                api(projects.parameterizedString)
                api(projects.preferences)
                api(projects.serialization)
                api(projects.tracing)
                api(projects.updatable)

                implementation(projects.injectScopes)
                implementation(projects.sealedEnum.runtime)
                implementation(libs.androidx.annotation)
                implementation(libs.androidx.collection)
                implementation(libs.androidx.compose.runtime)
                implementation(libs.androidx.compose.runtime.retain)
                implementation(libs.jetbrains.compose.uiUnit)
                implementation(libs.kotlinx.coroutines.core)
                implementation(libs.kotlinx.datetime)
                implementation(libs.kotlinx.serialization.json)
            }
        }
        val jvmMain by creating {
            dependsOn(jbMain)
        }
        val jbNonAndroidMain by creating {
            dependsOn(jbMain)
        }
        val desktopMain by getting {
            dependsOn(jvmMain)
            dependsOn(jbNonAndroidMain)
            configurations["kspDesktop"].dependencies.addAll(
                listOf(
                    projects.sealedEnum.ksp,
                )
            )
            dependencies {
                implementation(libs.jetbrains.compose.ui)
            }
        }
        val androidMain by getting {
            dependsOn(jvmMain)
            configurations["kspAndroid"].dependencies.addAll(
                listOf(
                    projects.sealedEnum.ksp,
                )
            )
            dependencies {
                implementation(libs.androidx.tracing)
                implementation(libs.kotlinx.coroutines.android)
            }
        }
        val wasmJsMain by getting {
            dependsOn(jbNonAndroidMain)
            configurations["kspWasmJs"].dependencies.addAll(
                listOf(
                    projects.sealedEnum.ksp,
                )
            )
        }
        val commonTest by getting {
            dependencies {
                implementation(kotlin("test"))
                implementation(libs.testBalloon.framework.core)
            }
        }
        val jbTest by creating {
            dependsOn(commonTest)
            dependencies {
                implementation(projects.algorithmTestResources)
                implementation(projects.dispatchersTestFixtures)
                implementation(projects.injectTest)
                implementation(projects.kmpAndroidRunner)
                implementation(projects.kmpStateRestorationTester)
                implementation(projects.patterns)
                implementation(projects.tracingTestFixtures)
                implementation(libs.jetbrains.compose.foundation)
                implementation(libs.jetbrains.compose.uiTest)
                implementation(libs.kotlinx.coroutines.test)
                implementation(libs.turbine)
            }
        }
        val jvmTest by creating {
            dependsOn(jbTest)
        }
        val desktopTest by getting {
            dependsOn(jvmTest)
            dependencies {
                implementation(compose.desktop.currentOs)
            }
        }
        val androidSharedTest by getting {
            dependsOn(jvmTest)
            dependencies {
                implementation(projects.testActivity)
                implementation(libs.androidx.compose.uiTest)
                implementation(libs.androidx.test.core)
                implementation(libs.androidx.test.espresso)
            }
        }
    }
}
