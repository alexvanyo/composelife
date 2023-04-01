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
import org.gradle.api.Project
import org.gradle.api.artifacts.VersionCatalogsExtension
import org.gradle.kotlin.dsl.get
import org.gradle.kotlin.dsl.getByType
import org.gradle.kotlin.dsl.withType
import org.jetbrains.kotlin.gradle.tasks.KotlinCompile
import java.io.File

fun Project.configureAndroidCompose(
    commonExtension: CommonExtension<*, *, *, *, *>,
) {
    val libs = extensions.getByType<VersionCatalogsExtension>().named("libs")

    commonExtension.apply {
        buildFeatures {
            compose = true
        }

        composeOptions {
            kotlinCompilerExtensionVersion = libs.findVersion("androidxComposeCompiler").get().toString()
        }

        // TODO: Add metrics and report to non-test KotlinCompile tasks
        afterEvaluate {
            tasks.withType<KotlinCompile>().all {
                if (!name.contains("test", true)) {
                    kotlinOptions {
                        val metricsFolder = File(buildDir, "compose-metrics")
                        val reportsFolder = File(buildDir, "compose-reports")
                        freeCompilerArgs = freeCompilerArgs + listOf(
                            "-P",
                            "plugin:androidx.compose.compiler.plugins.kotlin:metricsDestination=${
                                metricsFolder.absolutePath
                            }",
                            "-P",
                            "plugin:androidx.compose.compiler.plugins.kotlin:reportsDestination=${
                                reportsFolder.absolutePath
                            }",
                        )
                    }
                }
            }
        }
    }

    configurations["lintChecks"].dependencies.add(libs.findLibrary("slackComposeLintChecks").get().get())
}
