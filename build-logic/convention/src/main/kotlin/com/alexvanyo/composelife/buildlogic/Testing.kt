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

import com.android.build.gradle.TestedExtension
import org.gradle.api.GradleException
import org.gradle.api.Project
import org.gradle.api.artifacts.VersionCatalogsExtension
import org.gradle.kotlin.dsl.DependencyHandlerScope
import org.gradle.kotlin.dsl.dependencies
import org.gradle.kotlin.dsl.getByType
import org.gradle.kotlin.dsl.kotlin
import org.gradle.kotlin.dsl.withType

fun Project.configureTesting(
    testedExtension: TestedExtension,
) {
    testedExtension.apply {
        testOptions {
            unitTests {
                isIncludeAndroidResources = true
            }
        }
    }

    val libs = extensions.getByType<VersionCatalogsExtension>().named("libs")

    dependencies {
        add("testImplementation", libs.findLibrary("junit5.jupiter").get())
        add("testRuntimeOnly", libs.findLibrary("junit5.vintageEngine").get())

        add("androidTestImplementation", libs.findLibrary("junit4").get())
        add("androidTestRuntimeOnly", libs.findLibrary("junit5.vintageEngine").get())

        sharedTestImplementation(kotlin("test"))
    }

    tasks.withType<org.gradle.api.tasks.testing.Test>().configureEach {
        useJUnitPlatform()
    }
}

enum class SharedTestConfig {
    Robolectric,
    Instrumentation,
    Both
}

val Project.useSharedTest: SharedTestConfig get() =
    when (val useSharedTest = findProperty("com.alexvanyo.composelife.useSharedTest")) {
        null, "true" -> SharedTestConfig.Both
        "robolectric" -> SharedTestConfig.Robolectric
        "android" -> SharedTestConfig.Instrumentation
        else -> throw GradleException("Unexpected value $useSharedTest for useSharedTest!")
    }

fun Project.configureAndroidTesting(
    testedExtension: TestedExtension,
) {
    testedExtension.apply {
        defaultConfig {
            testInstrumentationRunner = "com.alexvanyo.composelife.test.HiltTestRunner"
        }

        sourceSets {
            // Setup a shared test directory for instrumentation tests and Robolectric tests
            val sharedTestDir = "src/sharedTest/kotlin"
            val sharedResDir = "src/sharedTest/res"
            val kmpSharedTestDir = "src/androidSharedTest/kotlin"
            val kmpSharedResDir = "src/androidSharedTest/res"
            if (useSharedTest != SharedTestConfig.Instrumentation) {
                getByName("test") {
                    java.srcDirs(sharedTestDir, kmpSharedTestDir)
                    res.srcDirs(sharedResDir, kmpSharedResDir)
                    resources.srcDirs("src/sharedTest/resources", "src/androidSharedTest/resources")
                }
            }
            if (useSharedTest != SharedTestConfig.Robolectric) {
                getByName("androidTest") {
                    java.srcDirs(sharedTestDir, kmpSharedTestDir)
                    res.srcDirs(sharedResDir, kmpSharedResDir)
                }
            }
        }

        if (useSharedTest == SharedTestConfig.Robolectric) {
            testVariants.configureEach {
                connectedInstrumentTestProvider.configure {
                    doFirst {
                        throw GradleException("useSharedTest is configured to only run robolectric tests!")
                    }
                }
            }
        }
    }

    val libs = extensions.getByType<VersionCatalogsExtension>().named("libs")

    dependencies {
        add("testImplementation", libs.findLibrary("robolectric").get())
        sharedTestImplementation(project(":hilt-test"))
    }

    tasks.withType<org.gradle.api.tasks.testing.Test>().configureEach {
        // Automatically output Robolectric logs to stdout (for ease of debugging in Android Studio)
        systemProperty("robolectric.logging", "stdout")

        if (useSharedTest == SharedTestConfig.Instrumentation && this.name.contains("Unit")) {
            doFirst {
                throw GradleException("useSharedTest is configured to only run android tests!")
            }
        }
    }
}

/**
 * Adds the given dependency to both `testImplementation` and `androidTestImplementation`.
 */
fun DependencyHandlerScope.sharedTestImplementation(dependencyNotation: Any) {
    add("testImplementation", dependencyNotation)
    add("androidTestImplementation", dependencyNotation)
}

/**
 * Adds the given dependency to both `kaptTest` and `kaptAndroidTest`.
 */
fun DependencyHandlerScope.kaptSharedTest(dependencyNotation: Any) {
    add("kaptTest", dependencyNotation)
    add("kaptAndroidTest", dependencyNotation)
}
