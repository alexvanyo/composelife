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
    id("com.alexvanyo.composelife.kotlin.multiplatform")
    id("com.alexvanyo.composelife.android.library")
    id("com.alexvanyo.composelife.android.library.jacoco")
    id("com.alexvanyo.composelife.android.library.ksp")
    id("com.alexvanyo.composelife.android.library.testing")
    id("com.alexvanyo.composelife.detekt")
}

android {
    namespace = "com.alexvanyo.composelife.preferencestest"
    defaultConfig {
        minSdk = 21
    }
    configureGradleManagedDevices(FormFactor.All, this)
}

kotlin {
    jvm()
    android()

    sourceSets {
        val commonMain by getting {
            dependencies {
                implementation(projects.kotlinInjectScopes)
                api(projects.preferences)
                implementation(libs.kotlinInject.runtime)
                implementation(libs.jetbrains.compose.runtime)
            }
        }
        val jvmMain by getting {
            configurations["kspJvm"].dependencies.add(libs.kotlinInject.ksp.get())
        }
        val androidMain by getting {
            configurations["kspAndroid"].dependencies.add(libs.kotlinInject.ksp.get())
            dependencies {
                api(libs.androidx.test.junit)
            }
        }
        val commonTest by getting {
            dependencies {
                implementation(projects.kmpAndroidRunner)
                implementation(projects.kotlinInjectScopes)
                implementation(projects.dispatchersTest)
            }
        }
        val androidSharedTest by getting {
            dependencies {
                implementation(libs.androidx.test.core)
                implementation(libs.androidx.test.junit)
                implementation(libs.androidx.test.runner)
            }
        }
        val androidUnitTest by getting {
            configurations["kspAndroidTest"].dependencies.add(libs.kotlinInject.ksp.get())
        }
        val androidInstrumentedTest by getting {
            configurations["kspAndroidAndroidTest"].dependencies.add(libs.kotlinInject.ksp.get())
        }
        val jvmTest by getting {
            configurations["kspJvmTest"].dependencies.add(libs.kotlinInject.ksp.get())
        }
    }
}
