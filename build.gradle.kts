plugins {
    jacoco
}

buildscript {
    repositories {
        google()
        mavenCentral()
    }
    dependencies {
        classpath(libs.android.gradlePlugin)
        classpath(kotlin("gradle-plugin", libs.versions.kotlin.get()))
    }
}

jacoco {
    toolVersion = libs.versions.jacoco.get()
}

tasks {
    val variants = listOf("debug", "release")
    val projectsForCoverage = subprojects.filter { it.name in setOf("algorithm", "app", "wear") }

    val variantJacocoTestReports = variants.map { variant ->
        register("jacocoTest${variant.capitalize()}UnitTestReport", JacocoReport::class) {
            dependsOn(projectsForCoverage.mapNotNull { it.tasks.findByName("jacocoTestReport") })

            val excludes = listOf(
                // Android
                "**/R.class",
                "**/R\$*.class",
                "**/BuildConfig.*",
                "**/Manifest*.*"
            )

            classDirectories.setFrom(
                files(
                    projectsForCoverage
                        .map {
                            fileTree("${it.buildDir}/tmp/kotlin-classes/$variant") {
                                exclude(excludes)
                            }
                        }
                )
            )
            sourceDirectories.setFrom(
                files(
                    projectsForCoverage
                        .flatMap {
                            listOf(
                                it.projectDir.resolve("src/main/java"),
                                it.projectDir.resolve("src/main/kotlin"),
                            ).filter(File::exists)
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

    val jacocoTestReport by registering {
        dependsOn(variantJacocoTestReports)
    }
}

task<Delete>("clean") {
    delete(rootProject.buildDir)
}
