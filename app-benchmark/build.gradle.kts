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
    id("com.alexvanyo.composelife.android.test")
    id("com.alexvanyo.composelife.detekt")
}

android {
    namespace = "com.alexvanyo.composelife.benchmark"
    targetProjectPath = ":app"
}

androidComponents {
    val runBenchmarks = findProperty("com.alexvanyo.composelife.runBenchmarks")

    beforeVariants(selector().all()) { variant ->
        // Enable the debug variant, which will be empty to ensure one variant always exists.
        // Enable the benchmark variant (with the baseline profile generation test) only if the build is specifically
        // generating it as specified by the above property.
        variant.enable = when (variant.buildType) {
            "debug" -> true
            "benchmark" -> runBenchmarks == "true"
            else -> false
        }
    }
}

dependencies {
    implementation(libs.junit4)
    implementation(libs.androidx.benchmark.macro.junit4)
    implementation(libs.androidx.test.runner)
    implementation(libs.androidx.test.junit)
}
