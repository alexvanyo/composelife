import com.alexvanyo.composelife.buildlogic.useSharedTest
import org.jetbrains.kotlin.gradle.targets.jvm.tasks.KotlinJvmTest

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
    id("com.alexvanyo.composelife.android.library.compose")
    id("com.alexvanyo.composelife.android.library.testing")
    id("com.alexvanyo.composelife.detekt")
    alias(libs.plugins.jetbrainsCompose)
}

android {
    namespace = "com.alexvanyo.composelife.snapshotstateset"
    sourceSets["main"].manifest.srcFile("src/androidMain/AndroidManifest.xml")
    defaultConfig {
        minSdk = 21
    }
}

kotlin {
    android()
    jvm()

    sourceSets {
        val commonMain by getting {
            dependencies {
                api(libs.jetbrains.compose.runtime)
            }
        }
        val jvmMain by getting {
            dependencies {
                implementation(compose.desktop.currentOs)
            }
        }
        val androidMain by getting {
            dependencies {
                implementation(libs.kotlinx.coroutines.android)
                implementation(libs.androidx.core)
                implementation(libs.androidx.lifecycle.viewmodel.savedstate)
            }
        }
        val commonTest by getting {
            dependencies {
                implementation(projects.kmpAndroidRunner)
                implementation(kotlin("test"))
                implementation(libs.kotlinx.coroutines.test)
                implementation(libs.jetbrains.compose.uiTestJunit4)
            }
        }
        val androidSharedTest by creating {
            dependsOn(commonTest)
            dependencies {
                implementation(projects.testActivity)

                implementation(libs.androidx.test.core)
                implementation(libs.androidx.test.espresso)
            }
        }
        val androidTest by getting {
            if (useSharedTest != com.alexvanyo.composelife.buildlogic.SharedTestConfig.Instrumentation) {
                dependsOn(androidSharedTest)
            }
        }
        val androidAndroidTest by getting {
            if (useSharedTest != com.alexvanyo.composelife.buildlogic.SharedTestConfig.Robolectric) {
                dependsOn(androidSharedTest)
            }
        }
    }
}
