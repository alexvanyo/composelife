/*
 * Copyright 2024 The Android Open Source Project
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
    alias(libs.plugins.convention.androidLibraryTesting)
    alias(libs.plugins.convention.detekt)
    alias(libs.plugins.convention.kotlinMultiplatformCompose)
    kotlin("plugin.serialization") version libs.versions.kotlin
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

val leanPrefixProvider = providers.exec {
    workingDir = file("lean")
    commandLine("lean", "--print-prefix")
}.standardOutput.asText.map { it.trim() }

/**
 * Path to the custom Lean 4 binary with JVM bytecode backend support.
 * Override via the Gradle property `leanJvmBinary` or system property `leanJvmBinary`.
 * Defaults to the local Lean 4 fork build at ~/Projects/lean4.
 */
val leanJvmBinaryProvider = providers.gradleProperty("leanJvmBinary")
    .orElse(providers.systemProperty("leanJvmBinary"))
    .orElse(
        providers.provider {
            "${System.getProperty("user.home")}/Projects/lean4/build/release/stage1/bin/lean"
        },
    )

val verifyLean by tasks.registering(Exec::class) {
    description = "Formally verifies session-value logic using Lean 4"
    group = LifecycleBasePlugin.VERIFICATION_GROUP
    workingDir = file("lean")
    commandLine("lake", "build", "SessionValue:static")
    usesService(heavyTaskLimitingBuildService)
}

val compileSessionValueBridgeCObject by tasks.registering(Exec::class) {
    description = "Compiles C bridge for Lean session-value state machine"
    group = LifecycleBasePlugin.BUILD_GROUP
    dependsOn(verifyLean)
    workingDir = file("lean")
    inputs.file(file("lean/c/session_value_bridge.c"))
    inputs.file(file("lean/c/session_value_bridge.h"))
    val outputFile = layout.buildDirectory.file("natives/c/session_value_bridge.o")
    outputs.file(outputFile)
    doFirst {
        outputFile.get().asFile.parentFile.mkdirs()
    }
    val leanPrefix = leanPrefixProvider.get()
    commandLine(
        "clang",
        "-c",
        "-fPIC",
        "c/session_value_bridge.c",
        "-I$leanPrefix/include",
        "-o",
        outputFile.get().asFile.absolutePath,
    )
}

/**
 * Step 1 of JVM bytecode compilation: rebuild the .olean cache for SessionValue using the
 * custom Lean 4 binary (which has the JVM backend). The standard lean toolchain builds
 * oleans that are incompatible with the custom binary's elaborator.
 */
val lakeBuildWithJvmLean by tasks.registering(Exec::class) {
    description = "Rebuilds Lean oleans with the custom JVM-capable lean binary"
    group = LifecycleBasePlugin.BUILD_GROUP
    workingDir = file("lean")
    inputs.files(
        fileTree("lean") {
            include("**/*.lean")
            include("lakefile.toml")
            include("lean-toolchain")
        },
    )
    val leanBinary = leanJvmBinaryProvider.get()
    val lakeBinary = file(leanBinary).resolveSibling("lake").absolutePath
    environment("LEAN", leanBinary)
    commandLine(lakeBinary, "build", "SessionValue")
}

/**
 * The LEAN_PATH produced by `lake env` when using the custom lean binary.
 * Evaluated lazily at configuration time so it is available as a Provider<String>.
 */
val jvmLeanPathProvider: Provider<String> = leanJvmBinaryProvider.flatMap { leanBinary ->
    val lakeBinary = file(leanBinary).resolveSibling("lake").absolutePath
    providers.exec {
        workingDir = file("lean")
        environment("LEAN", leanBinary)
        commandLine(lakeBinary, "env")
    }.standardOutput.asText.map { output ->
        output.lines()
            .firstOrNull { it.startsWith("LEAN_PATH=") }
            ?.removePrefix("LEAN_PATH=")
            .orEmpty()
    }
}

/**
 * Compile SessionValue/Bridge.lean to JVM bytecode using the custom Lean 4 JVM backend.
 *
 * Depends on [lakeBuildWithJvmLean] to ensure oleans are built with the custom lean first.
 * The `--jvm=<file>` flag emits a standard Java 17 .class file.
 * The generated class is `lean.mod_l_SessionValue_Bridge` (verified via `javap`).
 */
abstract class CompileLeanJvmBytecodeTask @javax.inject.Inject constructor(
    private val execOperations: ExecOperations,
) : DefaultTask() {
    @get:InputFiles
    abstract val leanFiles: ConfigurableFileCollection

    @get:Input
    abstract val leanBinary: Property<String>

    @get:Input
    abstract val leanPath: Property<String>

    @get:InputDirectory
    abstract val workingDir: DirectoryProperty

    @get:OutputDirectory
    abstract val outputDir: DirectoryProperty

    @TaskAction
    fun compile() {
        val modules = listOf(
            "SessionValue/Basic.lean" to "lean/mod_l_SessionValue_Basic.class",
            "SessionValue/StateMachine.lean" to "lean/mod_l_SessionValue_StateMachine.class",
            "SessionValue/Bridge.lean" to "lean/mod_l_SessionValue_Bridge.class",
        )
        for ((leanFile, classFile) in modules) {
            val dest = outputDir.get().file(classFile).asFile
            dest.parentFile.mkdirs()
            execOperations.exec {
                workingDir = this@CompileLeanJvmBytecodeTask.workingDir.get().asFile
                environment("LEAN_PATH", leanPath.get())
                commandLine(leanBinary.get(), "--jvm=${dest.absolutePath}", leanFile)
            }
        }
    }
}

val compileLeanJvmBytecode by tasks.registering(CompileLeanJvmBytecodeTask::class) {
    description = "Compiles Lean session-value modules to JVM bytecode for oracle testing"
    group = LifecycleBasePlugin.BUILD_GROUP
    dependsOn(lakeBuildWithJvmLean)

    leanFiles.from(
        fileTree("lean") {
            include("**/*.lean")
            include("lakefile.toml")
            include("lean-toolchain")
        },
    )
    leanBinary.set(leanJvmBinaryProvider)
    leanPath.set(jvmLeanPathProvider)
    workingDir.set(layout.projectDirectory.dir("lean"))
    outputDir.set(layout.buildDirectory.dir("lean-jvm-classes"))
}


kotlin {

    androidLibrary {
        namespace = "com.alexvanyo.composelife.sessionvalue"
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

    linuxX64 {
        compilations.getByName("test") {
            cinterops {
                val sessionValueBridge by creating {
                    definitionFile.set(file("src/linuxX64Test/cinterop/session_value_bridge.def"))
                    includeDirs(file("lean/c"))
                }
            }
        }
        binaries.withType<org.jetbrains.kotlin.gradle.plugin.mpp.TestExecutable>().configureEach {
            linkTaskProvider.configure {
                dependsOn(compileSessionValueBridgeCObject)
            }
            val bridgeObj = layout.buildDirectory.file("natives/c/session_value_bridge.o").get().asFile.absolutePath
            val leanArchive = file("lean/.lake/build/lib/libSessionValue_SessionValue.a").absolutePath
            val leanPrefix = leanPrefixProvider.get()
            linkerOpts(
                bridgeObj,
                leanArchive,
                "-L$leanPrefix/lib/lean",
                "-L$leanPrefix/lib",
                "-lleanshared",
                "-Wl,-rpath,$leanPrefix/lib/lean",
            )
        }
    }

    sourceSets {
        val commonMain by getting {
            dependencies {
                api(libs.kotlinx.serialization.core)
            }
        }
        val jbMain by creating {
            dependsOn(commonMain)
            dependencies {
                api(libs.androidx.compose.runtime)
                api(libs.androidx.compose.runtime.saveable)

                implementation(projects.serialization)
            }
        }
        val androidMain by getting {
            dependsOn(jbMain)
        }
        val desktopMain by getting {
            dependsOn(jbMain)
            dependencies {
                implementation(compose.desktop.currentOs)
            }
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
            dependencies {
                implementation(projects.injectTest)
                implementation(projects.kmpAndroidRunner)
                implementation(projects.kmpStateRestorationTester)
                implementation(projects.testActivity)
                implementation(libs.jetbrains.compose.uiTest)
                implementation(libs.kotlinx.coroutines.test)
                implementation(libs.kotlinx.io.core)
                implementation(libs.kotlinx.serialization.json)
                implementation(libs.molecule)
                implementation(libs.turbine)
            }
        }
        val jvmTest by creating {
            dependsOn(jbTest)
        }
        val desktopTest by getting {
            dependsOn(jvmTest)
        }
        val androidSharedTest by getting {
            dependsOn(jvmTest)
            dependencies {
                implementation(libs.androidx.compose.ui)
            }
        }
        val wasmJsTest by getting {
            dependsOn(jbTest)
            dependencies {
                implementation(libs.jetbrains.compose.ui)
            }
        }
        val linuxX64Test by getting {
            dependsOn(commonTest)
        }
    }
}

tasks.named("check") {
    dependsOn(verifyLean)
}

tasks.named("linuxX64Test") {
    dependsOn(verifyLean)
}

// Wire the Lean JVM bytecode into the desktop test runtime classpath.
// The compileLeanJvmBytecode task emits lean/mod_l_SessionValue_Bridge.class into
// build/lean-jvm-classes/, which must be on the classpath for Class.forName() to find it.
tasks.named<Test>("desktopTest") {
    dependsOn(compileLeanJvmBytecode)
    classpath += files(layout.buildDirectory.dir("lean-jvm-classes"))
}

