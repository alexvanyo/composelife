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

fun Project.configureAndroidCompose(
    commonExtension: CommonExtension<*, *, *, *, *, *>,
) {
    val libs = extensions.getByType<VersionCatalogsExtension>().named("libs")

    commonExtension.apply {
        lint {
            // TODO: Re-enable this lint check
            disable.addAll(listOf("ComposeParameterOrder"))
        }

        buildFeatures {
            compose = true
        }

        // TODO: Add metrics and report to non-test KotlinCompile tasks
        afterEvaluate {
            tasks.withType<KotlinCompile>().configureEach {
                if (!name.contains("test", true)) {
                    compilerOptions {
                        val metricsFolder = layout.buildDirectory.dir("build/compose-metrics")
                        val reportsFolder = layout.buildDirectory.dir("build/compose-reports")
                        freeCompilerArgs.addAll(
                            "-P",
                            "plugin:androidx.compose.compiler.plugins.kotlin:metricsDestination=${
                                metricsFolder.get().asFile.absolutePath
                            }",
                            "-P",
                            "plugin:androidx.compose.compiler.plugins.kotlin:reportsDestination=${
                                reportsFolder.get().asFile.absolutePath
                            }",
                        )
                    }
                }
            }
        }
    }

    configurations["lintChecks"].dependencies.add(libs.findLibrary("slackComposeLintChecks").get().get())
}
