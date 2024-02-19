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
    alias(libs.plugins.convention.detekt)
    alias(libs.plugins.convention.kotlinMultiplatformCompose)
    alias(libs.plugins.gradleDependenciesSorter)
    alias(libs.plugins.ksp)
}

kotlin {
    jvm()

    sourceSets {
        val commonMain by getting {
            dependencies {
                implementation(libs.kotlinInject.runtime)
                implementation(libs.kotlinx.serialization.core)
                implementation(projects.injectScopes)
                implementation(projects.uiApp)
            }
        }
        val jvmMain by getting {
            configurations["kspJvm"].dependencies.add(libs.kotlinInject.ksp.get())
            configurations["kspJvm"].dependencies.add(libs.sealedEnum.ksp.get())
            dependencies {
                implementation(compose.desktop.currentOs)
                implementation(libs.sqldelight.sqliteDriver)
            }
        }
        val commonTest by getting {
            dependencies {
                implementation(projects.databaseTest)
                implementation(projects.dispatchersTest)
                implementation(projects.patterns)
                implementation(projects.preferencesTest)
            }
        }
    }
}

compose.desktop {
    application {
        mainClass = "com.alexvanyo.composelife.MainKt"
        buildTypes.release.proguard {
            configurationFiles.from("proguard-rules.pro")
        }
    }
}
