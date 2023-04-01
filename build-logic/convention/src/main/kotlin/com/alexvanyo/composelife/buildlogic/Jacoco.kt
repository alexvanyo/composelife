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
import org.gradle.api.tasks.testing.Test
import org.gradle.kotlin.dsl.configure
import org.gradle.kotlin.dsl.getByType
import org.gradle.kotlin.dsl.register
import org.gradle.kotlin.dsl.withType
import org.gradle.testing.jacoco.plugins.JacocoPluginExtension
import org.gradle.testing.jacoco.plugins.JacocoTaskExtension
import org.gradle.testing.jacoco.tasks.JacocoReport

private val coverageExclusions = listOf(
    // Android
    "**/R.class",
    "**/R\$*.class",
    "**/BuildConfig.*",
    "**/Manifest*.*",

    // SealedEnum
    "**/*SealedEnum*",

    // protobuf
    "**/proto/*",
)

fun Project.configureJacocoMerge() {
    val libs = extensions.getByType<VersionCatalogsExtension>().named("libs")

    configure<JacocoPluginExtension> {
        toolVersion = libs.findVersion("jacoco").get().toString()
    }

    val variants = listOf("debug", "release")

    @Suppress("NoNameShadowing")
    val variantJacocoTestReports = variants.map { variant ->
        tasks.register("jacocoTest${variant.capitalizeForTaskName()}UnitTestReport", JacocoReport::class) {
            dependsOn(
                subprojects.mapNotNull {
                    it.tasks.findByName("create${variant.capitalizeForTaskName()}UnitTestCoverageReport")
                },
            )

            classDirectories.setFrom(
                files(
                    subprojects
                        .map {
                            fileTree("${it.buildDir}/tmp/kotlin-classes/$variant") {
                                exclude(coverageExclusions)
                            }
                        },
                ),
            )
            sourceDirectories.setFrom(
                files(
                    subprojects
                        .flatMap {
                            listOf(
                                it.projectDir.resolve("src/commonMain/kotlin"),
                                it.projectDir.resolve("src/androidMain/kotlin"),
                                it.projectDir.resolve("src/jvmMain/kotlin"),
                            )
                        },
                ),
            )
            executionData.setFrom(
                subprojects
                    .filter {
                        it.tasks.findByName("create${variant.capitalizeForTaskName()}UnitTestCoverageReport") != null
                    }
                    .map {
                        file(
                            "${it.buildDir}/outputs/unit_test_code_coverage/" +
                                "${variant}UnitTest/test${variant.capitalizeForTaskName()}UnitTest.exec",
                        )
                    },
            )

            reports {
                html.required.set(true)
                xml.required.set(true)
            }
        }
    }

    tasks.register("jacocoTestReport") {
        dependsOn(variantJacocoTestReports)
    }
}

fun Project.configureJacoco(
    commonExtension: CommonExtension<*, *, *, *, *>,
) {
    val libs = extensions.getByType<VersionCatalogsExtension>().named("libs")

    commonExtension.testCoverage {
        jacocoVersion = libs.findVersion("jacoco").get().toString()
    }

    commonExtension.buildTypes.configureEach {
        enableUnitTestCoverage = true
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
