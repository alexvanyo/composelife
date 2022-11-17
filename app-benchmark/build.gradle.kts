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
    id("com.alexvanyo.composelife.android.test")
    id("com.alexvanyo.composelife.detekt")
}

android {
    namespace = "com.alexvanyo.composelife.benchmark"
    sourceSets["main"].manifest.srcFile("src/androidMain/AndroidManifest.xml")
    targetProjectPath = ":app"
}

androidComponents {
    val runBenchmarks = findProperty("com.alexvanyo.composelife.runBenchmarks") == "true"

    beforeVariants(selector().all()) { variant ->
        // Enable the benchmark variant (with the baseline profile generation test) only if the build is specifically
        // generating it as specified by the above property.
        // Otherwise, enable the debug variant, which will be empty to ensure one variant always exists.
        variant.enable = when (variant.buildType) {
            "debug" -> !runBenchmarks
            "benchmark" -> runBenchmarks
            else -> false
        }
    }
}

kotlin {
    android()

    sourceSets {
        val androidMain by getting {
            dependencies {
                implementation(kotlin("test"))
                implementation(libs.androidx.benchmark.macro.junit4)
                implementation(libs.androidx.test.runner)
                implementation(libs.androidx.test.junit)
            }
        }
    }
}
