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
import org.gradle.api.NamedDomainObjectContainer
import org.gradle.api.Project
import org.gradle.api.artifacts.VersionCatalogsExtension
import org.gradle.kotlin.dsl.closureOf
import org.gradle.kotlin.dsl.configure
import org.gradle.kotlin.dsl.getByType
import org.gradle.kotlin.dsl.withType
import org.jetbrains.kotlin.gradle.dsl.KotlinMultiplatformExtension
import org.jetbrains.kotlin.gradle.plugin.KotlinSourceSet

fun Project.configureTesting(
    testedExtension: TestedExtension,
) {
    testedExtension.testOptions {
        unitTests {
            isIncludeAndroidResources = true
        }
    }

    extensions.configure<KotlinMultiplatformExtension> {
        sourceSets.configure(
            closureOf<NamedDomainObjectContainer<KotlinSourceSet>> {
                getByName("commonTest") {
                    dependencies {
                        implementation(kotlin("test"))
                    }
                }
            },
        )
    }
}

enum class SharedTestConfig {
    Robolectric,
    Instrumentation,
    Both,
}

private val Project.useSharedTest: SharedTestConfig get() =
    when (val useSharedTest = findProperty("com.alexvanyo.composelife.useSharedTest")) {
        null, "true" -> SharedTestConfig.Both
        "robolectric" -> SharedTestConfig.Robolectric
        "android" -> SharedTestConfig.Instrumentation
        else -> throw GradleException("Unexpected value $useSharedTest for useSharedTest!")
    }

@Suppress("LongMethod")
fun Project.configureAndroidTesting(
    testedExtension: TestedExtension,
) {
    testedExtension.apply {
        defaultConfig {
            testInstrumentationRunner = "com.alexvanyo.composelife.test.HiltTestRunner"
        }

        sourceSets {
            // Setup a shared test directory for instrumentation tests and Robolectric tests
            val sharedResDir = "src/androidSharedTest/res"
            if (useSharedTest != SharedTestConfig.Instrumentation) {
                getByName("test") {
                    res.srcDir(sharedResDir)
                    resources.srcDirs("src/androidSharedTest/resources")
                }
            }
            if (useSharedTest != SharedTestConfig.Robolectric) {
                getByName("androidTest") {
                    res.srcDir(sharedResDir)
                }
            }
        }

        testOptions {
            unitTests.all { test ->
                test.systemProperty("robolectric.graphicsMode", "NATIVE")
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

    extensions.configure<KotlinMultiplatformExtension> {
        android()

        sourceSets.configure(
            closureOf<NamedDomainObjectContainer<KotlinSourceSet>> {
                val commonTest = getByName("commonTest")
                val androidSharedTest = create("androidSharedTest") {
                    dependsOn(commonTest)
                    dependencies {
                        implementation(project(":hilt-test"))
                    }
                }
                getByName("androidUnitTest") {
                    if (useSharedTest != SharedTestConfig.Instrumentation) {
                        dependsOn(androidSharedTest)
                    }
                    dependencies {
                        implementation(libs.findLibrary("robolectric").get())
                    }
                }
                getByName("androidInstrumentedTest") {
                    if (useSharedTest != SharedTestConfig.Robolectric) {
                        dependsOn(androidSharedTest)
                    }
                }
            },
        )
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
