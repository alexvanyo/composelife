import com.alexvanyo.composelife.buildlogic.FormFactor
import com.alexvanyo.composelife.buildlogic.configureGradleManagedDevices

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

plugins {
    alias(libs.plugins.convention.kotlinMultiplatform)
    alias(libs.plugins.convention.androidLibrary)
    alias(libs.plugins.convention.androidLibraryJacoco)
    alias(libs.plugins.convention.androidLibraryKsp)
    alias(libs.plugins.convention.androidLibraryTesting)
    alias(libs.plugins.convention.detekt)
    alias(libs.plugins.gradleDependenciesSorter)
}

android {
    namespace = "com.alexvanyo.composelife.preferencestest"
    defaultConfig {
        minSdk = 21
    }
    configureGradleManagedDevices(enumValues<FormFactor>().toSet(), this)
}

kotlin {
    jvm("desktop")
    androidTarget()

    sourceSets {
        val commonMain by getting {
            dependencies {
                api(projects.preferences)

                implementation(libs.jetbrains.compose.runtime)
                implementation(libs.kotlinInject.runtime)
                implementation(projects.injectScopes)
            }
        }
        val jbMain by creating {
            dependsOn(commonMain)
        }
        val desktopMain by getting {
            dependsOn(jbMain)
            configurations["kspDesktop"].dependencies.addAll(
                listOf(
                    libs.kotlinInject.ksp.get(),
                    libs.kotlinInjectAnvil.ksp.get(),
                )
            )
        }
        val androidMain by getting {
            dependsOn(jbMain)
            configurations["kspAndroid"].dependencies.addAll(
                listOf(
                    libs.kotlinInject.ksp.get(),
                    libs.kotlinInjectAnvil.ksp.get(),
                )
            )
            dependencies {
                api(libs.androidx.test.junit)
            }
        }
        val commonTest by getting {
            dependencies {
                implementation(projects.dispatchersTest)
                implementation(projects.filesystemTest)
                implementation(projects.injectScopes)
                implementation(projects.kmpAndroidRunner)
            }
        }
        val jbTest by creating {
            dependsOn(commonTest)
        }
        val desktopTest by getting {
            dependsOn(jbTest)
            configurations["kspDesktopTest"].dependencies.addAll(
                listOf(
                    libs.kotlinInject.ksp.get(),
                    libs.kotlinInjectAnvil.ksp.get(),
                    projects.entryPointSymbolProcessor,
                )
            )
        }
        val androidSharedTest by getting {
            dependsOn(jbTest)
            dependencies {
                implementation(libs.androidx.test.core)
                implementation(libs.androidx.test.junit)
                implementation(libs.androidx.test.runner)
            }
        }
        val androidUnitTest by getting {
            configurations["kspAndroidTest"].dependencies.addAll(
                listOf(
                    libs.kotlinInject.ksp.get(),
                    libs.kotlinInjectAnvil.ksp.get(),
                    projects.entryPointSymbolProcessor,
                )
            )
        }
        val androidInstrumentedTest by getting {
            configurations["kspAndroidAndroidTest"].dependencies.addAll(
                listOf(
                    libs.kotlinInject.ksp.get(),
                    libs.kotlinInjectAnvil.ksp.get(),
                    projects.entryPointSymbolProcessor,
                )
            )
        }
    }
}
