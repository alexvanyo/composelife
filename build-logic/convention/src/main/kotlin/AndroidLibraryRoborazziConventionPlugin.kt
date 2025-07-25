/*
 * Copyright 2023 The Android Open Source Project
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
import com.alexvanyo.composelife.buildlogic.configureTesting
import com.android.build.gradle.LibraryExtension
import org.gradle.api.GradleException
import org.gradle.api.artifacts.VersionCatalogsExtension
import org.jetbrains.kotlin.gradle.dsl.KotlinMultiplatformExtension

class AndroidLibraryRoborazziConventionPlugin : ConventionPlugin({
    with(pluginManager) {
        apply("com.android.library")
    }

    val libs = extensions.getByType(VersionCatalogsExtension::class.java).named("libs")

    val libraryExtension = extensions.getByType(LibraryExtension::class.java)

    configureTesting(libraryExtension)

    libraryExtension.testOptions {
        unitTests.all { test ->
            test.apply {
                systemProperty("robolectric.graphicsMode", "NATIVE")
                // Configure parameterization to either be combined, or at the test runner level
                systemProperty(
                    "com.alexvanyo.composelife.combinedScreenshotTests",
                    providers.gradleProperty("com.alexvanyo.composelife.combinedScreenshotTests")
                        .orElse("false")
                        .map {
                            when (it) {
                                "false" -> "false"
                                "true" -> "true"
                                else -> throw GradleException(
                                    "Unexpected value $it for combinedScreenshotTests!",
                                )
                            }
                        }
                        .get(),
                )
                // Increase memory and parallelize Roborazzi tests
                maxHeapSize = "2g"
                maxParallelForks = if (System.getenv("CI") == "true") 1 else 4
                forkEvery = 12
            }
        }
    }

    extensions.configure(KotlinMultiplatformExtension::class.java) {
        androidTarget()

        sourceSets.getByName("androidUnitTest") {
            dependencies {
                implementation(libs.findLibrary("roborazzi.compose").get())
                implementation(libs.findLibrary("roborazzi.core").get())
                implementation(libs.findLibrary("robolectric").get())
            }
        }
    }
})
