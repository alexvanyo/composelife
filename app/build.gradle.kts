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
    alias(libs.plugins.gradleDependenciesSorter)
}

android {
    namespace = "com.alexvanyo.composelife"
    defaultConfig {
        applicationId = "com.alexvanyo.composelife"
        minSdk = 21
        targetSdk = 34
        versionCode = 1
        versionName = "1.0"
    }
    configureGradleManagedDevices(setOf(FormFactor.Mobile), this)
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
                implementation(projects.injectScopes)
                implementation(projects.resourcesApp)
                implementation(projects.strictMode)
                implementation(projects.uiApp)
            }
        }
        val androidMain by getting {
            configurations["kspAndroid"].dependencies.add(libs.kotlinInject.ksp.get())
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
                implementation(projects.patterns)
                implementation(projects.preferencesTest)
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
            configurations["kspAndroidTest"].dependencies.add(libs.kotlinInject.ksp.get())
        }
        val androidInstrumentedTest by getting {
            configurations["kspAndroidAndroidTest"].dependencies.add(libs.kotlinInject.ksp.get())
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
