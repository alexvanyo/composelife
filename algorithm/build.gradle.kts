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
import com.alexvanyo.composelife.buildlogic.jvmMolecule

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
}

android {
    namespace = "com.alexvanyo.composelife.algorithm"
    defaultConfig {
        minSdk = 21
    }
    configureGradleManagedDevices(enumValues<FormFactor>().toSet(), this)
}

kotlin {
    androidTarget()
    jvm("desktop")
    jvmMolecule(this)

    sourceSets {
        val commonMain by getting {
            dependencies {
                api(projects.dispatchers)
                api(projects.geometry)
                api(projects.parameterizedString)
                api(projects.preferences)
                api(projects.updatable)

                implementation(libs.androidx.annotation)
                implementation(libs.jetbrains.compose.runtime)
                implementation(libs.kotlinInject.runtime)
                implementation(libs.kotlinx.coroutines.core)
                implementation(libs.kotlinx.datetime)
                implementation(libs.kotlinx.serialization.json)
                implementation(libs.uuid)
                implementation(projects.injectScopes)
            }
        }
        val jvmMain by creating {
            dependsOn(commonMain)
            dependencies {
                implementation(libs.guava.android)
                implementation(libs.jetbrains.compose.uiUnit)
                implementation(libs.sealedEnum.runtime)
            }
        }
        val jvmNonAndroidMain by creating {
            dependsOn(jvmMain)
        }
        val moleculeMain by getting {
            dependsOn(jvmNonAndroidMain)
            configurations["kspMolecule"].dependencies.add(libs.kotlinInject.ksp.get())
            configurations["kspMolecule"].dependencies.add(libs.sealedEnum.ksp.get())
        }
        val desktopMain by getting {
            dependsOn(jvmNonAndroidMain)
            configurations["kspDesktop"].dependencies.add(libs.kotlinInject.ksp.get())
            configurations["kspDesktop"].dependencies.add(libs.sealedEnum.ksp.get())
            dependencies {
                implementation(libs.jetbrains.compose.ui)
            }
        }
        val androidMain by getting {
            dependsOn(jvmMain)
            configurations["kspAndroid"].dependencies.add(libs.kotlinInject.ksp.get())
            configurations["kspAndroid"].dependencies.add(libs.sealedEnum.ksp.get())
            dependencies {
                implementation(libs.androidx.tracing)
                implementation(libs.kotlinx.coroutines.android)
            }
        }
        val commonTest by getting {
            dependencies {
                implementation(libs.kotlinx.coroutines.test)
                implementation(libs.turbine)
                implementation(projects.dispatchersTest)
                implementation(projects.kmpAndroidRunner)
                implementation(projects.kmpStateRestorationTester)
                implementation(projects.patterns)
            }
        }
        val jvmTest by creating {
            dependsOn(commonTest)
            dependencies {
                implementation(libs.molecule)
                implementation(libs.testParameterInjector.junit4)
            }
        }
        val moleculeTest by getting {
            dependsOn(jvmTest)
        }
        val jbTest by creating {
            dependsOn(jvmTest)
            dependencies {
                implementation(libs.jetbrains.compose.foundation)
                implementation(libs.jetbrains.compose.uiTestJunit4)
            }
        }
        val desktopTest by getting {
            dependsOn(jbTest)
        }
        val androidSharedTest by getting {
            dependsOn(jbTest)
            dependencies {
                implementation(libs.androidx.compose.uiTestJunit4)
                implementation(libs.androidx.test.core)
                implementation(libs.androidx.test.espresso)
                implementation(projects.preferencesTest)
                implementation(projects.testActivity)
            }
        }
    }
}
