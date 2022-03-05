package com.alexvanyo.composelife.buildlogic

import com.android.build.api.variant.AndroidComponentsExtension
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
    "**/proto/*"
)

fun Project.configureJacocoMerge() {
    configureJacocoVersion()

    val variants = listOf("debug", "release")

    val variantJacocoTestReports = variants.map { variant ->
        tasks.register("jacocoTest${variant.capitalize()}UnitTestReport", JacocoReport::class) {
            dependsOn(subprojects.mapNotNull { it.tasks.findByName("jacocoTestReport") })

            classDirectories.setFrom(
                files(
                    subprojects
                        .map {
                            fileTree("${it.buildDir}/tmp/kotlin-classes/$variant") {
                                exclude(coverageExclusions)
                            }
                        }
                )
            )
            sourceDirectories.setFrom(
                files(
                    subprojects
                        .flatMap {
                            listOf(
                                it.projectDir.resolve("src/main/java"),
                                it.projectDir.resolve("src/main/kotlin"),
                            )
                        }
                )
            )
            executionData.setFrom(
                subprojects.filter { it.tasks.findByName("jacocoTestReport") != null }.map {
                    file("${it.buildDir}/jacoco/test${variant.capitalize()}UnitTest.exec")
                }
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
    androidComponentsExtension: AndroidComponentsExtension<*, *, *>,
) {
    configureJacocoVersion()

    val jacocoTestReport = tasks.create("jacocoTestReport")

    androidComponentsExtension.onVariants { variant ->
        val testTaskName = "test${variant.name.capitalize()}UnitTest"

        val reportTask = tasks.register("jacoco${testTaskName.capitalize()}Report", JacocoReport::class) {
            dependsOn(testTaskName)

            reports {
                xml.required.set(true)
                html.required.set(true)
            }

            classDirectories.setFrom(
                fileTree("$buildDir/tmp/kotlin-classes/${variant.name}") {
                    exclude(coverageExclusions)
                }
            )

            sourceDirectories.setFrom(files("$projectDir/src/main/java", "$projectDir/src/main/kotlin"))
            executionData.setFrom(file("$buildDir/jacoco/$testTaskName.exec"))
        }

        jacocoTestReport.dependsOn(reportTask)
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

fun Project.configureJacocoVersion() {
    val libs = extensions.getByType<VersionCatalogsExtension>().named("libs")

    configure<JacocoPluginExtension> {
        toolVersion = libs.findVersion("jacoco").get().toString()
    }
}
