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
import com.alexvanyo.composelife.buildlogic.configureAndroid
import com.alexvanyo.composelife.buildlogic.configureBadgingTasks
import com.android.build.api.dsl.ApplicationExtension
import com.android.build.api.variant.ApplicationAndroidComponentsExtension
import org.gradle.kotlin.dsl.configure
import org.gradle.kotlin.dsl.exclude
import org.gradle.kotlin.dsl.getByType

class AndroidApplicationConventionPlugin : ConventionPlugin({
    with(pluginManager) {
        apply("com.android.application")
    }

    configureBadgingTasks(extensions.getByType<ApplicationAndroidComponentsExtension>())

    tasks.named("check").configure {
        dependsOn("checkReleaseBadging")
    }

    extensions.configure<ApplicationExtension> {
        configureAndroid(this)

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
                matchingFallbacks.add("release") // fallback to release for dependencies
            }

            release {
                isMinifyEnabled = true
                isShrinkResources = true
                proguardFiles(
                    getDefaultProguardFile("proguard-android-optimize.txt"),
                    "proguard-rules.pro",
                    "release-proguard-rules.pro",
                )
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
                    "staging-proguard-rules.pro",
                )
                testProguardFiles("staging-test-proguard-rules.pro")
            }
        }
    }

    @Suppress("NoNameShadowing")
    afterEvaluate {
        configurations
            .matching { it.name.contains("debug", ignoreCase = true).not() }
            .configureEach {
                exclude(group = "androidx.compose.ui", module = "ui-tooling")
                exclude(group = "androidx.compose.ui", module = "ui-tooling-data")
            }
    }
})
