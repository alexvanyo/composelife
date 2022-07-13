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

import com.alexvanyo.composelife.buildlogic.ConventionPlugin
import com.alexvanyo.composelife.buildlogic.configureKotlinAndroid
import com.android.build.gradle.internal.dsl.BaseAppModuleExtension
import org.gradle.kotlin.dsl.configure

class AndroidApplicationConventionPlugin : ConventionPlugin({
    with(pluginManager) {
        apply("com.android.application")
        apply("org.jetbrains.kotlin.android")
    }

    extensions.configure<BaseAppModuleExtension> {
        configureKotlinAndroid(this)

        signingConfigs {
            named("debug") {
                keyAlias = "debug"
                keyPassword = "android"
                storeFile = file("$rootDir/keystore/debug.jks")
                storePassword = "android"
            }
        }

        buildTypes {
            debug {
                signingConfig = signingConfigs.getByName("debug")
            }

            release {
                isMinifyEnabled = true
                isShrinkResources = true
                proguardFiles(getDefaultProguardFile("proguard-android-optimize.txt"), "proguard-rules.pro")
            }

            // Create a build type for the purposes of testing a minified build (like release is)
            create("staging") {
                isMinifyEnabled = true // minify like a release build
                isShrinkResources = true // shrink resources like a release build
                matchingFallbacks.add("release") // fallback to release for dependencies
                signingConfig = signingConfigs.getByName("debug") // sign with debug for testing
                // Use the normal proguard rules, as well as some additional staging ones just for tests (when needed)
                proguardFiles(
                    getDefaultProguardFile("proguard-android-optimize.txt"),
                    "proguard-rules.pro",
                    "staging-proguard-rules.pro"
                )
            }

            // Create a build type for the purposes of benchmarking a minified build (like release is)
            create("benchmark") {
                isMinifyEnabled = true // minify like a release build
                isShrinkResources = true // shrink resources like a release build
                matchingFallbacks.add("release") // fallback to release for dependencies
                signingConfig = signingConfigs.getByName("debug") // sign with debug for testing
                // Use the normal proguard rules, as well as some additional benchmarking ones
                proguardFiles(
                    getDefaultProguardFile("proguard-android-optimize.txt"),
                    "proguard-rules.pro",
                    "benchmark-proguard-rules.pro"
                )
            }
        }
    }
})
