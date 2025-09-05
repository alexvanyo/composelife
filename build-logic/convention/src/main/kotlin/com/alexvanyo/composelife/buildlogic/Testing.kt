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

package com.alexvanyo.composelife.buildlogic

import com.android.build.api.dsl.CommonExtension
import org.gradle.api.GradleException
import org.gradle.api.Project
import org.gradle.api.artifacts.VersionCatalogsExtension
import org.gradle.api.provider.Provider
import org.jetbrains.kotlin.gradle.ExperimentalKotlinGradlePluginApi
import org.jetbrains.kotlin.gradle.dsl.KotlinMultiplatformExtension
import org.jetbrains.kotlin.gradle.plugin.KotlinSourceSetTree

fun Project.configureTesting(
    commonExtension: CommonExtension<*, *, *, *, *, *>,
) {
    commonExtension.testOptions {
        unitTests {
            isIncludeAndroidResources = true
            isReturnDefaultValues = true
        }
    }

    extensions.configure(KotlinMultiplatformExtension::class.java) {
        sourceSets.getByName("commonTest") {
            dependencies {
                implementation(kotlin("test"))
            }
        }
    }
}

enum class SharedTestConfig {
    Robolectric,
    Instrumentation,
    Both,
}

private val Project.useSharedTest: Provider<SharedTestConfig> get() =
    providers
        .gradleProperty("com.alexvanyo.composelife.useSharedTest")
        .orElse("true")
        .map {
            when (it) {
                "true" -> SharedTestConfig.Both
                "robolectric" -> SharedTestConfig.Robolectric
                "android" -> SharedTestConfig.Instrumentation
                else -> throw GradleException("Unexpected value $it for useSharedTest!")
            }
        }

@Suppress("LongMethod", "CyclomaticComplexMethod")
fun Project.configureAndroidTesting(
    commonExtension: CommonExtension<*, *, *, *, *, *>,
    testedExtension: com.android.build.gradle.TestedExtension,
) {
    commonExtension.apply {
        defaultConfig {
            testInstrumentationRunner = "androidx.test.runner.AndroidJUnitRunner"
        }

        sourceSets {
            getByName("test") {
                resources.srcDirs("src/androidSharedTest/resources")
            }
        }

        testOptions {
            unitTests.all { test ->
                test.systemProperty("robolectric.graphicsMode", "NATIVE")
            }
        }
    }

    testedExtension.apply {
        if (useSharedTest.get() == SharedTestConfig.Robolectric) {
            // TODO: Replace with gradle-api API
            testVariants.configureEach {
                connectedInstrumentTestProvider.configure {
                    doFirst {
                        throw GradleException("useSharedTest is configured to only run robolectric tests!")
                    }
                }
            }
        }
    }

    val libs = extensions.getByType(VersionCatalogsExtension::class.java).named("libs")

    extensions.configure(KotlinMultiplatformExtension::class.java) {
        @OptIn(ExperimentalKotlinGradlePluginApi::class)
        androidTarget {
            unitTestVariant.sourceSetTree.set(KotlinSourceSetTree.test)
            instrumentedTestVariant.sourceSetTree.set(KotlinSourceSetTree.test)
        }

        sourceSets.apply {
            val commonTest = getByName("commonTest")
            val androidSharedTest = create("androidSharedTest") {
                dependsOn(commonTest)
            }
            getByName("androidUnitTest") {
                if (useSharedTest.get() != SharedTestConfig.Instrumentation) {
                    dependsOn(androidSharedTest)
                }
                dependencies {
                    implementation(libs.findLibrary("robolectric").get())
                }
            }
            getByName("androidInstrumentedTest") {
                if (useSharedTest.get() != SharedTestConfig.Robolectric) {
                    dependsOn(androidSharedTest)
                }
                dependencies {
                    implementation(libs.findLibrary("androidx-test-runner").get())
                }
            }
        }
    }

    tasks.withType(org.gradle.api.tasks.testing.Test::class.java).configureEach {
        // Automatically output Robolectric logs to stdout (for ease of debugging in Android Studio)
        systemProperty("robolectric.logging", "stdout")

        if (useSharedTest.get() == SharedTestConfig.Instrumentation && this.name.contains("Unit")) {
            doFirst {
                throw GradleException("useSharedTest is configured to only run android tests!")
            }
        }
    }
}
