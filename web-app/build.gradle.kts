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

plugins {
    alias(libs.plugins.convention.kotlinMultiplatform)
    alias(libs.plugins.convention.dependencyGuard)
    alias(libs.plugins.convention.detekt)
    alias(libs.plugins.convention.kotlinMultiplatformCompose)
    alias(libs.plugins.gradleDependenciesSorter)
    alias(libs.plugins.ksp)
    alias(libs.plugins.metro)
}

kotlin {
    wasmJs {
        binaries.executable()
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
                implementation(libs.androidx.compose.runtime)
                implementation(libs.androidx.compose.runtime.retain)
                implementation(libs.kotlinx.serialization.core)
                implementation(projects.data)
                implementation(projects.database)
                implementation(projects.filesystem)
                implementation(projects.imageLoader)
                implementation(projects.injectScopes)
                implementation(projects.logging)
                implementation(projects.network)
                implementation(projects.preferences)
                implementation(projects.uiApp)
                implementation(projects.uiMobile)
                implementation(projects.updatable)
            }
        }
        val wasmJsMain by getting {
            configurations["kspWasmJs"].dependencies.addAll(listOf(
                projects.sealedEnum.ksp,
            ))
        }
    }
}

dependencyGuard {
    configuration("wasmJsRuntimeClasspath")
}
