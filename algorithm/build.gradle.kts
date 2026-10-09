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
    kotlin("plugin.serialization") version libs.versions.kotlin
    alias(libs.plugins.gradleDependenciesSorter)
    alias(libs.plugins.metro)
    alias(libs.plugins.testBalloon)
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
    description = "Formally verifies algorithm logic using Lean 4"
    group = LifecycleBasePlugin.VERIFICATION_GROUP
    dependsOn(cacheLean)
    workingDir = file("lean")
    commandLine("lake", "build", "Algorithm:static")
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

abstract class GenerateLeanAlgorithmKotlinTask @javax.inject.Inject constructor(
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
        val workDir = this@GenerateLeanAlgorithmKotlinTask.workingDir.get().asFile
        val leanPath = File(workDir, ".lake/build/lib/lean").absolutePath
        val preambleFile = File(outFile.parentFile, "AlgorithmPreamble.kt.tmp")
        val footerFile = File(outFile.parentFile, "AlgorithmFooter.kt.tmp")
        preambleFile.writeText(
            """
            import com.alexvanyo.composelife.geometry.IntOffset
            import com.alexvanyo.composelife.geometry.getMooreNeighbors
            import com.alexvanyo.composelife.model.MacroCell
            """.trimIndent(),
        )
        footerFile.writeText(
            """
            /**
             * Computes the next 2x2 [Int] generation for the given 4x4 [Int] in its center.
             */
            @Suppress("NOTHING_TO_INLINE")
            internal inline fun Int.computeNextGeneration(): Int =
                f_Algorithm_exportComputeNextGen4x4UInt(this.toUInt()).toInt()

            /**
             * Computes the 4x4 [Int] next generation for the given 8x8 64-bit Morton leaf node in its center.
             */
            fun Long.computeNextGeneration(): Int =
                f_Algorithm_exportComputeLeafNextGen8x8BranchUInt(this.toULong()).toInt()

            /**
             * Packs four 16-bit 4x4 quadrants in Morton order into an 8x8 64-bit leaf node.
             */
            internal fun packLeafNode(nw: Int, ne: Int, sw: Int, se: Int): Long =
                f_Algorithm_packLeafFrom4x4sUInt(
                    nw.toUInt(),
                    ne.toUInt(),
                    sw.toUInt(),
                    se.toUInt(),
                ).toLong()

            /**
             * Extracts the central 4x4 from an 8x8 64-bit leaf node.
             */
            internal fun centeredSubnodeLevel3(node: Long): Int =
                f_Algorithm_centeredSubnodeLevel3BitsUInt(node.toULong()).toInt()

            /**
             * Extracts the horizontal central 4x4 spanning west and east 8x8 leaf nodes.
             */
            internal fun centeredHorizontalSubnodeLevel3(w: Long, e: Long): Int =
                f_Algorithm_centeredHorizontalSubnodeLevel3BitsUInt(w.toULong(), e.toULong()).toInt()

            /**
             * Extracts the vertical central 4x4 spanning north and south 8x8 leaf nodes.
             */
            internal fun centeredVerticalSubnodeLevel3(n: Long, s: Long): Int =
                f_Algorithm_centeredVerticalSubnodeLevel3BitsUInt(n.toULong(), s.toULong()).toInt()

            /**
             * Extracts the central 4x4 from a 16x16 Level 4 node consisting of four 8x8 leaf nodes.
             */
            internal fun centeredSubSubnodeLevel4(nw: Long, ne: Long, sw: Long, se: Long): Int =
                f_Algorithm_centeredSubSubnodeLevel4BitsUInt(
                    nw.toULong(),
                    ne.toULong(),
                    sw.toULong(),
                    se.toULong(),
                ).toInt()

            /**
             * Extracts the central 4x4 from a [MacroCell.Level4Node].
             */
            internal fun centeredSubSubnodeLevel4(node: MacroCell.Level4Node): Int =
                centeredSubSubnodeLevel4(node.nw, node.ne, node.sw, node.se)

            /**
             * Computes the next generation for a 16x16 Level 4 node, returning the centered 8x8 [Long] leaf node.
             */
            internal fun computeLevel4NextGeneration(
                nw: Long,
                ne: Long,
                sw: Long,
                se: Long,
                computeLeafNextGen: (Long) -> Int = Long::computeNextGeneration,
            ): Long {
                val n00 = centeredSubnodeLevel3(nw)
                val n01 = centeredHorizontalSubnodeLevel3(nw, ne)
                val n02 = centeredSubnodeLevel3(ne)
                val n10 = centeredVerticalSubnodeLevel3(nw, sw)
                val n11 = centeredSubSubnodeLevel4(nw, ne, sw, se)
                val n12 = centeredVerticalSubnodeLevel3(ne, se)
                val n20 = centeredSubnodeLevel3(sw)
                val n21 = centeredHorizontalSubnodeLevel3(sw, se)
                val n22 = centeredSubnodeLevel3(se)

                val leafNW = packLeafNode(n00, n01, n10, n11)
                val leafNE = packLeafNode(n01, n02, n11, n12)
                val leafSW = packLeafNode(n10, n11, n20, n21)
                val leafSE = packLeafNode(n11, n12, n21, n22)

                val outNW = computeLeafNextGen(leafNW)
                val outNE = computeLeafNextGen(leafNE)
                val outSW = computeLeafNextGen(leafSW)
                val outSE = computeLeafNextGen(leafSE)

                return packLeafNode(outNW, outNE, outSW, outSE)
            }

            /**
             * Computes the next generation for a [MacroCell.Level4Node], returning the centered 8x8 [Long] leaf node.
             */
            internal fun computeLevel4NextGeneration(
                node: MacroCell.Level4Node,
                computeLeafNextGen: (Long) -> Int = Long::computeNextGeneration,
            ): MacroCell.LeafNode = computeLevel4NextGeneration(
                nw = node.nw,
                ne = node.ne,
                sw = node.sw,
                se = node.se,
                computeLeafNextGen = computeLeafNextGen,
            )

            /**
             * Pure function computing one generation of Conway's Game of Life on a set of [IntOffset]s.
             */
            fun stepGeneration(aliveCells: Set<IntOffset>): Set<IntOffset> {
                val candidates = aliveCells.flatMapTo(mutableSetOf(), IntOffset::getMooreNeighbors)
                candidates.addAll(aliveCells)
                return candidates.filterTo(mutableSetOf()) { cell ->
                    val neighborCount = cell.getMooreNeighbors().count { it in aliveCells }
                    neighborCount == 3 || (neighborCount == 2 && cell in aliveCells)
                }
            }

            /**
             * Pure function computing [step] generations of Conway's Game of Life.
             */
            tailrec fun stepGenerations(aliveCells: Set<IntOffset>, step: Int): Set<IntOffset> = if (step <= 0) {
                aliveCells
            } else {
                stepGenerations(stepGeneration(aliveCells), step - 1)
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
                    "-Dcompiler.kotlin.package=com.alexvanyo.composelife.algorithm",
                    "-Dcompiler.kotlin.preamble_file=${preambleFile.absolutePath}",
                    "-Dcompiler.kotlin.footer_file=${footerFile.absolutePath}",
                    "-K",
                    outFile.absolutePath,
                    "Algorithm/HashLife.lean",
                )
            }
        } finally {
            preambleFile.delete()
            footerFile.delete()
        }
    }
}

val generateLeanAlgorithmKotlin by tasks.registering(GenerateLeanAlgorithmKotlinTask::class) {
    description = "Generates Kotlin code directly from Lean algorithm formal model"
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
    outputFile.set(
        layout.buildDirectory.file(
            "generated/sources/lean/kotlin/commonMain/com/alexvanyo/composelife/algorithm/AlgorithmLean.kt",
        ),
    )
}

kotlin {
    androidLibrary {
        namespace = "com.alexvanyo.composelife.algorithm"
        minSdk = 24
        configureGradleManagedDevices(enumValues<FormFactor>().toSet(), this)
    }
    jvm("desktop") {}
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
            kotlin.srcDir(
                generateLeanAlgorithmKotlin.map {
                    it.outputFile.get().asFile.parentFile.parentFile.parentFile.parentFile.parentFile
                },
            )
            dependencies {
                api(projects.geometry)
            }
        }
        val jbMain by creating {
            dependsOn(commonMain)
            dependencies {
                api(projects.dispatchers)
                api(projects.parameterizedString)
                api(projects.preferences)
                api(projects.serialization)
                api(projects.tracing)
                api(projects.updatable)

                implementation(projects.injectScopes)
                implementation(projects.sealedEnum.runtime)
                implementation(libs.androidx.annotation)
                implementation(libs.androidx.collection)
                implementation(libs.androidx.compose.runtime)
                implementation(libs.androidx.compose.runtime.retain)
                implementation(libs.jetbrains.compose.uiUnit)
                implementation(libs.kotlinx.coroutines.core)
                implementation(libs.kotlinx.datetime)
                implementation(libs.kotlinx.serialization.json)
            }
        }
        val jvmMain by creating {
            dependsOn(jbMain)
        }
        val jbNonAndroidMain by creating {
            dependsOn(jbMain)
        }
        val desktopMain by getting {
            dependsOn(jvmMain)
            dependsOn(jbNonAndroidMain)
            configurations["kspDesktop"].dependencies.addAll(
                listOf(
                    projects.sealedEnum.ksp,
                )
            )
            dependencies {
                implementation(libs.jetbrains.compose.ui)
            }
        }
        val androidMain by getting {
            dependsOn(jvmMain)
            configurations["kspAndroid"].dependencies.addAll(
                listOf(
                    projects.sealedEnum.ksp,
                )
            )
            dependencies {
                implementation(libs.androidx.tracing)
                implementation(libs.kotlinx.coroutines.android)
            }
        }
        val wasmJsMain by getting {
            dependsOn(jbNonAndroidMain)
            configurations["kspWasmJs"].dependencies.addAll(
                listOf(
                    projects.sealedEnum.ksp,
                )
            )
        }
        val commonTest by getting {
            dependencies {
                implementation(kotlin("test"))
                implementation(libs.testBalloon.framework.core)
            }
        }
        val jbTest by creating {
            dependsOn(commonTest)
            dependencies {
                implementation(projects.algorithmTestResources)
                implementation(projects.dispatchersTestFixtures)
                implementation(projects.injectTest)
                implementation(projects.kmpAndroidRunner)
                implementation(projects.kmpStateRestorationTester)
                implementation(projects.patterns)
                implementation(projects.tracingTestFixtures)
                implementation(libs.jetbrains.compose.foundation)
                implementation(libs.jetbrains.compose.uiTest)
                implementation(libs.kotlinx.coroutines.test)
                implementation(libs.turbine)
            }
        }
        val jvmTest by creating {
            dependsOn(jbTest)
        }
        val desktopTest by getting {
            dependsOn(jvmTest)
            dependencies {
                implementation(compose.desktop.currentOs)
            }
        }
        val androidSharedTest by getting {
            dependsOn(jvmTest)
            dependencies {
                implementation(projects.testActivity)
                implementation(libs.androidx.compose.uiTest)
                implementation(libs.androidx.test.core)
                implementation(libs.androidx.test.espresso)
            }
        }
    }
}

tasks.named("check") {
    dependsOn(verifyLean)
}
