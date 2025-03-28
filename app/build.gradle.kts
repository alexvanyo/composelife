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

plugins {
    alias(libs.plugins.convention.kotlinMultiplatform)
    alias(libs.plugins.convention.androidApplication)
    alias(libs.plugins.convention.androidApplicationCompose)
    alias(libs.plugins.convention.androidApplicationJacoco)
    alias(libs.plugins.convention.androidApplicationKsp)
    alias(libs.plugins.convention.androidApplicationTesting)
    alias(libs.plugins.convention.dependencyGuard)
    alias(libs.plugins.convention.detekt)
    alias(libs.plugins.androidx.baselineProfile)
    alias(libs.plugins.gradleDependenciesSorter)
}

android {
    namespace = "com.alexvanyo.composelife"
    defaultConfig {
        applicationId = "com.alexvanyo.composelife"
        minSdk = 21
        targetSdk = 35
        versionCode = 1
        versionName = "1.0"
    }
    configureGradleManagedDevices(setOf(FormFactor.Mobile), this)
}

baselineProfile {
    automaticGenerationDuringBuild = false
    saveInSrc = true
    dexLayoutOptimization = true
    mergeIntoMain = true
}

kotlin {
    androidTarget()

    sourceSets {
        val commonMain by getting {
            dependencies {
                implementation(libs.circuit.retained)
                implementation(libs.kotlinInject.runtime)
                implementation(libs.kotlinx.serialization.core)
                implementation(projects.appCompatSync)
                implementation(projects.doNotKeepProcess)
                implementation(projects.entryPointRuntime)
                implementation(projects.filesystem)
                implementation(projects.imageLoader)
                implementation(projects.injectScopes)
                implementation(projects.logging)
                implementation(projects.network)
                implementation(projects.resourcesApp)
                implementation(projects.strictMode)
                implementation(projects.uiApp)
                implementation(projects.uiMobile)
                implementation(projects.work)
            }
        }
        val androidMain by getting {
            configurations["kspAndroid"].dependencies.addAll(listOf(
                libs.kotlinInject.ksp.get(),
                libs.kotlinInjectAnvil.ksp.get(),
                projects.entryPointSymbolProcessor,
            ))
            configurations["baselineProfile"].dependencies.add(projects.appBaselineProfileGenerator)
            dependencies {
                implementation(libs.androidx.activityCompose)
                implementation(libs.androidx.appcompat)
                implementation(libs.androidx.core)
                implementation(libs.androidx.core.splashscreen)
                implementation(libs.androidx.lifecycle.process)
                implementation(libs.androidx.profileInstaller)
            }
        }
        val androidDebug by creating {
            dependsOn(androidMain)
            dependencies {
                implementation(libs.androidx.compose.uiTooling)
                implementation(libs.leakCanary.android)
            }
        }
        val androidStaging by creating {
            dependsOn(androidMain)
            dependencies {
                implementation(libs.leakCanary.android)
            }
        }
        val commonTest by getting {
            dependencies {
                implementation(projects.databaseTest)
                implementation(projects.dispatchersTest)
                implementation(projects.filesystemTest)
                implementation(projects.patterns)
                implementation(projects.preferencesTest)
                implementation(projects.uiCommon)
                implementation(projects.workTest)
            }
        }
        val androidSharedTest by getting {
            dependsOn(commonTest)
            dependencies {
                implementation(libs.androidx.test.core)
                implementation(libs.androidx.test.espresso)
                implementation(libs.androidx.window)
            }
        }
        val androidUnitTest by getting {
            configurations["kspAndroidTest"].dependencies.addAll(listOf(
                libs.kotlinInject.ksp.get(),
                libs.kotlinInjectAnvil.ksp.get(),
                projects.entryPointSymbolProcessor,
            ))
        }
        val androidInstrumentedTest by getting {
            configurations["kspAndroidAndroidTest"].dependencies.addAll(listOf(
                libs.kotlinInject.ksp.get(),
                libs.kotlinInjectAnvil.ksp.get(),
                projects.entryPointSymbolProcessor,
            ))
            dependencies {
                compileOnly(libs.apiGuardian.api)
                compileOnly(libs.google.autoValue.annotations)
            }
        }
    }
}

dependencyGuard {
    configuration("releaseRuntimeClasspath")
}
