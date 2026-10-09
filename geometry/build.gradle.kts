/*
 * Copyright 2023 The Android Open Source Project
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

import com.alexvanyo.composelife.buildlogic.FormFactor
import com.alexvanyo.composelife.buildlogic.configureGradleManagedDevices
import com.alexvanyo.composelife.buildlogic.heavyTaskLimitingBuildService
import org.jetbrains.kotlin.gradle.ExperimentalWasmDsl

plugins {
    alias(libs.plugins.convention.kotlinMultiplatform)
    alias(libs.plugins.convention.androidLibrary)
    alias(libs.plugins.convention.androidLibraryCompose)
    alias(libs.plugins.convention.androidLibraryJacoco)
    alias(libs.plugins.convention.androidLibraryKsp)
    alias(libs.plugins.convention.androidLibraryTesting)
    alias(libs.plugins.convention.detekt)
    alias(libs.plugins.convention.kotlinMultiplatformCompose)
    alias(libs.plugins.gradleDependenciesSorter)
}

composeCompiler {
    targetKotlinPlatforms.set(
        setOf(
            org.jetbrains.kotlin.gradle.plugin.KotlinPlatformType.androidJvm,
            org.jetbrains.kotlin.gradle.plugin.KotlinPlatformType.jvm,
            org.jetbrains.kotlin.gradle.plugin.KotlinPlatformType.wasm,
        ),
    )
}

val cacheLean by tasks.registering(Exec::class) {
    description = "Opportunistically downloads Lean cache"
    group = LifecycleBasePlugin.VERIFICATION_GROUP
    workingDir = file("lean")
    commandLine("lake", "exe", "cache", "get")
    isIgnoreExitValue = true
    usesService(heavyTaskLimitingBuildService)
}

val verifyLean by tasks.registering(Exec::class) {
    description = "Formally verifies geometry logic using Lean 4"
    group = LifecycleBasePlugin.VERIFICATION_GROUP
    dependsOn(cacheLean)
    workingDir = file("lean")
    commandLine("lake", "build", "--wfail", "Geometry:static")
    usesService(heavyTaskLimitingBuildService)
}

/**
 * Path to the custom Lean 4 binary with Kotlin codegen backend support.
 * Override via the Gradle property `leanBinary` or system property `leanBinary`.
 * Defaults to the local Lean 4 fork build at ~/Projects/lean4.
 */
val leanBinaryProvider = providers.gradleProperty("leanBinary")
    .orElse(providers.systemProperty("leanBinary"))
    .orElse(
        providers.provider {
            "${System.getProperty("user.home")}/Projects/lean4/build/release/stage1/bin/lean"
        },
    )

abstract class GenerateLeanGeometryKotlinTask @javax.inject.Inject constructor(
    private val execOperations: ExecOperations,
) : DefaultTask() {
    @get:InputFiles
    abstract val leanFiles: ConfigurableFileCollection

    @get:Input
    abstract val leanBinary: Property<String>

    @get:InputDirectory
    abstract val workingDir: DirectoryProperty

    @get:OutputFile
    abstract val outputFile: RegularFileProperty

    @TaskAction
    fun generate() {
        val outFile = outputFile.get().asFile
        outFile.parentFile.mkdirs()
        val workDir = this@GenerateLeanGeometryKotlinTask.workingDir.get().asFile
        val leanPath = File(workDir, ".lake/build/lib/lean").absolutePath
        val footerFile = File(outFile.parentFile, "LineSegmentFooter.kt.tmp")
        footerFile.writeText(
            """
            /**
             * Returns all discrete grid [IntOffset]s that intersect with the polyline path defined by [points].
             */
            fun cellIntersections(points: List<Offset>): Set<IntOffset> {
                require(points.isNotEmpty()) { "Points cannot be empty!" }
                return buildSet {
                    for (i in 0 until points.size - 1) {
                        cellIntersections(points[i], points[i + 1], this)
                    }
                    if (points.size == 1) {
                        add(floor(points.first()))
                    }
                }
            }

            /**
             * Returns all discrete grid [IntOffset]s that intersect with the line segment between [start] and [end].
             */
            fun cellIntersections(start: Offset, end: Offset): Set<IntOffset> = buildSet {
                cellIntersections(start, end, this)
            }

            internal fun cellIntersections(start: Offset, end: Offset, destination: MutableSet<IntOffset>) {
                val startCell = floor(start)
                val endCell = floor(end)
                val cells = f_Geometry_rayMarchSegmentCoords(
                    start.x.toDouble(),
                    start.y.toDouble(),
                    end.x.toDouble(),
                    end.y.toDouble(),
                    startCell.x,
                    startCell.y,
                    endCell.x,
                    endCell.y,
                )
                for (cell in cells) {
                    val pair = cell as Pair<*, *>
                    destination.add(IntOffset(pair.first as Int, pair.second as Int))
                }
            }
            """.trimIndent(),
        )
        try {
            execOperations.exec {
                workingDir = workDir
                environment("LEAN_PATH", leanPath)
                commandLine(
                    leanBinary.get(),
                    "-Dcompiler.kotlin.pruneUnreachable=true",
                    "-Dcompiler.kotlin.package=com.alexvanyo.composelife.geometry",
                    "-Dcompiler.kotlin.footer_file=${footerFile.absolutePath}",
                    "-K",
                    outFile.absolutePath,
                    "Geometry/LineSegment.lean",
                )
            }
        } finally {
            footerFile.delete()
        }
    }
}

val generateLeanGeometryKotlin by tasks.registering(GenerateLeanGeometryKotlinTask::class) {
    description = "Generates Kotlin code directly from Lean geometry formal model"
    group = LifecycleBasePlugin.BUILD_GROUP
    dependsOn(verifyLean)
    leanFiles.from(
        fileTree("lean") {
            include("**/*.lean")
            include("lakefile.toml")
            include("lean-toolchain")
        },
    )
    leanBinary.set(leanBinaryProvider)
    workingDir.set(layout.projectDirectory.dir("lean"))
    outputFile.set(layout.buildDirectory.file("generated/sources/lean/kotlin/commonMain/com/alexvanyo/composelife/geometry/LineSegmentLean.kt"))
}

kotlin {
    androidLibrary {
        namespace = "com.alexvanyo.composelife.geometry"
        minSdk = 24
        configureGradleManagedDevices(enumValues<FormFactor>().toSet(), this)
    }
    jvm("desktop")
    @OptIn(ExperimentalWasmDsl::class)
    wasmJs {
        browser {
            testTask {
                useKarma {
                    useChromiumHeadless()
                }
            }
        }
    }

    sourceSets {
        val commonMain by getting {
            kotlin.srcDir(generateLeanGeometryKotlin.map { it.outputFile.get().asFile.parentFile.parentFile.parentFile.parentFile.parentFile })
            dependencies {
                implementation(libs.androidx.annotation)
            }
        }
        val jbMain by creating {
            dependsOn(commonMain)
            dependencies {
                api(libs.jetbrains.compose.uiGeometry)
                api(libs.jetbrains.compose.uiUnit)

                implementation(libs.androidx.compose.runtime)
                implementation(libs.jetbrains.compose.uiUtil)
            }
        }
        val desktopMain by getting {
            dependsOn(jbMain)
        }
        val androidMain by getting {
            dependsOn(jbMain)
        }
        val wasmJsMain by getting {
            dependsOn(jbMain)
        }
        val commonTest by getting {
            dependencies {
                implementation(kotlin("test"))
            }
        }
        val jbTest by creating {
            dependsOn(commonTest)
        }
        val desktopTest by getting {
            dependsOn(jbTest)
        }
        val androidSharedTest by getting {
            dependsOn(jbTest)
        }
        val wasmJsTest by getting {
            dependsOn(jbTest)
        }
    }
}

tasks.named("check") {
    dependsOn(verifyLean)
}
