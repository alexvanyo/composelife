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
    id("com.alexvanyo.composelife.detekt")
    kotlin("kapt")
}

android {
    namespace = "com.alexvanyo.composelife.databasetest"
    defaultConfig {
        minSdk = 21
    }
}

kotlin {
    android()

    sourceSets {
        val commonMain by getting {
            dependencies {
                api(projects.database)
                implementation(projects.updatable)

                api(libs.kotlinx.coroutines.core)
                implementation(libs.kotlinx.coroutines.test)
            }
        }
        val androidMain by getting {
            configurations["kapt"].dependencies.add(libs.dagger.hilt.compiler.get())
            dependencies {
                api(libs.kotlinx.coroutines.android)
                api(libs.androidx.room.runtime)
                implementation(libs.dagger.hilt.android)
                api(libs.dagger.hilt.test)
            }
        }
    }
}
