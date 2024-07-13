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
import com.android.build.gradle.internal.coverage.JacocoReportTask
import org.gradle.api.Project
import org.gradle.api.artifacts.VersionCatalogsExtension
import org.gradle.api.tasks.testing.Test
import org.gradle.kotlin.dsl.assign
import org.gradle.kotlin.dsl.configure
import org.gradle.kotlin.dsl.getByType
import org.gradle.kotlin.dsl.register
import org.gradle.kotlin.dsl.withType
import org.gradle.testing.jacoco.plugins.JacocoPluginExtension
import org.gradle.testing.jacoco.plugins.JacocoTaskExtension
import org.gradle.testing.jacoco.tasks.JacocoReport

@Suppress("LongMethod", "NoNameShadowing")
fun Project.configureJacocoMerge() {
    val libs = extensions.getByType<VersionCatalogsExtension>().named("libs")

    configure<JacocoPluginExtension> {
        toolVersion = libs.findVersion("jacoco").get().toString()
    }

    val variants = listOf("debug", "release")

    val sourceDirectoryFiles = subprojects
        .flatMap {
            listOf(
                it.layout.projectDirectory.dir("src/androidMain/kotlin"),
                it.layout.projectDirectory.dir("src/commonMain/kotlin"),
                it.layout.projectDirectory.dir("src/desktopMain/kotlin"),
                it.layout.projectDirectory.dir("src/jbMain/kotlin"),
                it.layout.projectDirectory.dir("src/jvmMain/kotlin"),
                it.layout.projectDirectory.dir("src/jvmNonAndroidMain/kotlin"),
            )
        }

    val createVariantUnitTestCoverageReports = variants.map { variant ->
        tasks.register("jacoco${variant.capitalizeForTaskName()}UnitTestCoverageReport", JacocoReport::class) {
            dependsOn(
                subprojects.flatMap {
                    it.getUnitTestReportTasks(variant)
                },
            )

            classDirectories.setFrom(
                subprojects.flatMap {
                    it.getUnitTestReportTasks(variant)
                        .map(JacocoReportTask::classFileCollection)
                },
            )
            sourceDirectories.setFrom(sourceDirectoryFiles)
            executionData.setFrom(
                subprojects.flatMap {
                    it.getUnitTestReportTasks(variant)
                        .map(JacocoReportTask::jacocoHostTestCoverageFile)
                },
            )

            reports {
                html.required = true
                xml.required = true
            }
        }
    }
    val createAndroidTestCoverageReport = tasks.register("jacocoAndroidTestCoverageReport", JacocoReport::class) {
        dependsOn(
            subprojects.flatMap {
                it.getAndroidTestReportTasks()
            },
        )

        classDirectories.setFrom(
            subprojects
                .map {
                    it.getAndroidTestReportTasks()
                        .map(JacocoReportTask::classFileCollection)
                },
        )
        sourceDirectories.setFrom(sourceDirectoryFiles)
        executionData.setFrom(
            subprojects
                .map {
                    it.getAndroidTestReportTasks()
                        .map(JacocoReportTask::jacocoConnectedTestsCoverageDir)
                        .map(::fileTree)
                },
        )

        reports {
            html.required = true
            xml.required = true
        }
    }

    val createUnitTestCoverageReport = tasks.register("jacocoUnitTestCoverageReport") {
        dependsOn(createVariantUnitTestCoverageReports)
    }

    tasks.register("jacocoTestCoverageReport") {
        dependsOn(createUnitTestCoverageReport)
        dependsOn(createAndroidTestCoverageReport)
    }
}

private fun Project.getUnitTestReportTasks(variant: String) =
    getTasksByName("create${variant.capitalizeForTaskName()}UnitTestCoverageReport", false)
        .filterIsInstance<JacocoReportTask>()

private fun Project.getAndroidTestReportTasks() =
    listOf(
        "debug",
        "release",
        "staging",
    ).flatMap { variant ->
        getTasksByName("createManagedDevice${variant.capitalizeForTaskName()}AndroidTestCoverageReport", false)
            .filterIsInstance<JacocoReportTask>()
    }

fun Project.configureJacoco(
    commonExtension: CommonExtension<*, *, *, *, *, *>,
) {
    val libs = extensions.getByType<VersionCatalogsExtension>().named("libs")

    commonExtension.testCoverage {
        jacocoVersion = libs.findVersion("jacoco").get().toString()
    }

    commonExtension.buildTypes.configureEach {
        enableUnitTestCoverage = true
        // TODO: Re-enable test coverage for instrumented tests https://github.com/alexvanyo/composelife/issues/2257
        // enableAndroidTestCoverage = true
    }

    tasks.withType<Test>().configureEach {
        configure<JacocoTaskExtension> {
            // Required for JaCoCo + Robolectric
            // https://github.com/robolectric/robolectric/issues/2230
            isIncludeNoLocationClasses = true

            // Required for JDK 11 with the above
            // https://github.com/gradle/gradle/issues/5184#issuecomment-391982009
            excludes = listOf("jdk.internal.*")
        }
    }
}
