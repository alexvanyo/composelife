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

@file:Suppress("InternalAgpApiUsage")

package com.alexvanyo.composelife.buildlogic

import com.android.build.api.dsl.CommonExtension
import com.android.build.api.dsl.KotlinMultiplatformAndroidLibraryTarget
import com.android.build.api.variant.KotlinMultiplatformAndroidComponentsExtension
import com.android.build.gradle.internal.lint.AndroidLintTask
import com.android.build.gradle.internal.lint.LintModelWriterTask
import com.android.build.gradle.internal.tasks.R8Task
import dev.detekt.gradle.Detekt
import org.gradle.api.JavaVersion
import org.gradle.api.Project
import org.gradle.api.artifacts.VersionCatalogsExtension
import org.jetbrains.kotlin.gradle.dsl.JvmTarget

fun Project.configureAndroid(commonExtension: CommonExtension) {
    val libs = extensions.getByType(VersionCatalogsExtension::class.java).named("libs")

    commonExtension.apply {
        compileSdk {
            version = release(37) {
                minorApiLevel = 1
            }
        }

        lint.apply {
            warningsAsErrors = true
            disable.addAll(listOf("GradleDependency", "OldTargetApi", "AndroidGradlePluginVersion"))
            enable.addAll(listOf("UnsupportedChromeOsHardware"))
        }

        defaultConfig.vectorDrawables.useSupportLibrary = true

        buildTypes.getByName("debug") {
            isPseudoLocalesEnabled = true
        }

        compileOptions.apply {
            sourceCompatibility = JavaVersion.VERSION_11
            targetCompatibility = JavaVersion.VERSION_11
            isCoreLibraryDesugaringEnabled = true
        }

        // Workaround for https://github.com/Kotlin/kotlinx.coroutines/blob/master/kotlinx-coroutines-debug/README.md#build-failures-due-to-duplicate-resource-files
        packaging.resources.excludes.addAll(
            listOf(
                "/META-INF/AL2.0",
                "/META-INF/LGPL2.1",
                "/META-INF/LICENSE.md",
                "/META-INF/LICENSE-notice.md",
                "/META-INF/com.google.dagger_dagger.version",
            ),
        )
    }

    configurations.configureEach {
        resolutionStrategy.eachDependency {
            val version = requested.version.orEmpty()
            // Force guava to always use the android version instead of the jre version
            if (requested.group == "com.google.guava" && requested.name == "guava" && version.endsWith("jre")) {
                useVersion(version.removeSuffix("jre") + "android")
            }
        }
    }

    dependencies.add("coreLibraryDesugaring", libs.findLibrary("android.desugarJdkLibs").get())

    // Register R8 minification and Lint as heavy tasks
    tasks.withType(R8Task::class.java).configureEach {
        usesService(heavyTaskLimitingBuildService)
    }
    tasks.withType(AndroidLintTask::class.java).configureEach {
        usesService(heavyTaskLimitingBuildService)
        mustRunAfter(tasks.withType(Detekt::class.java))
    }
    tasks.withType(LintModelWriterTask::class.java).configureEach {
        usesService(heavyTaskLimitingBuildService)
        mustRunAfter(tasks.withType(Detekt::class.java))
    }
}

fun Project.configureAndroid(extension: KotlinMultiplatformAndroidLibraryTarget) {
    val libs = extensions.getByType(VersionCatalogsExtension::class.java).named("libs")

    extension.apply {
        compileSdk {
            version = release(37) {
                minorApiLevel = 1
            }
        }

        lint {
            warningsAsErrors = true
            disable.addAll(listOf("GradleDependency", "OldTargetApi", "AndroidGradlePluginVersion"))
            enable.addAll(listOf("UnsupportedChromeOsHardware"))
        }

        enableCoreLibraryDesugaring = true
        androidResources { enable = true }
        compilations.configureEach {
            compileTaskProvider.configure {
                compilerOptions {
                    jvmTarget.set(JvmTarget.JVM_11)
                }
            }
        }

        // Workaround for https://github.com/Kotlin/kotlinx.coroutines/blob/master/kotlinx-coroutines-debug/README.md#build-failures-due-to-duplicate-resource-files
        packaging {
            resources.excludes.addAll(
                listOf(
                    "/META-INF/AL2.0",
                    "/META-INF/LGPL2.1",
                    "/META-INF/LICENSE.md",
                    "/META-INF/LICENSE-notice.md",
                    "/META-INF/com.google.dagger_dagger.version",
                ),
            )
        }
    }

    extensions.configure(KotlinMultiplatformAndroidComponentsExtension::class.java) {
        onVariants { variant ->
            variant.pseudoLocalesEnabled.set(true)
        }
    }

    configurations.configureEach {
        resolutionStrategy.eachDependency {
            val version = requested.version.orEmpty()
            // Force guava to always use the android version instead of the jre version
            if (requested.group == "com.google.guava" && requested.name == "guava" && version.endsWith("jre")) {
                useVersion(version.removeSuffix("jre") + "android")
            }
        }
    }

    dependencies.add("coreLibraryDesugaring", libs.findLibrary("android.desugarJdkLibs").get())

    tasks.withType(AndroidLintTask::class.java).configureEach {
        usesService(heavyTaskLimitingBuildService)
        mustRunAfter(tasks.withType(Detekt::class.java))
    }
    tasks.withType(LintModelWriterTask::class.java).configureEach {
        usesService(heavyTaskLimitingBuildService)
        mustRunAfter(tasks.withType(Detekt::class.java))
    }
}
