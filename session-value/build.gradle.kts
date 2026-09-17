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
import com.android.build.api.dsl.KotlinMultiplatformAndroidDeviceTestCompilation
import com.dshatz.kni.bundlesPrebuiltNatives
import org.jetbrains.kotlin.gradle.ExperimentalWasmDsl
import kotlin.jvm.java

plugins {
    alias(libs.plugins.convention.kotlinMultiplatform)
    alias(libs.plugins.convention.androidLibrary)
    alias(libs.plugins.convention.androidLibraryCompose)
    alias(libs.plugins.convention.androidLibraryJacoco)
    alias(libs.plugins.convention.androidLibraryTesting)
    alias(libs.plugins.convention.detekt)
    alias(libs.plugins.convention.kotlinMultiplatformCompose)
    alias(libs.plugins.kni)
    kotlin("plugin.serialization") version libs.versions.kotlin
    alias(libs.plugins.gradleDependenciesSorter)
}

val leanPrefixProvider = providers.exec {
    commandLine("lean", "--print-prefix")
}.standardOutput.asText.map { it.trim() }

val javaHomeProvider = providers.environmentVariable("JAVA_HOME")
    .filter { it.isNotBlank() }
    .orElse(providers.systemProperty("java.home"))

val verifyLean by tasks.registering(Exec::class) {
    description = "Formally verifies session-value logic using Lean 4"
    group = LifecycleBasePlugin.VERIFICATION_GROUP
    workingDir = file("lean")
    commandLine("lake", "build", "SessionValue:static")
}

val buildSessionValueLeanSharedLibrary by tasks.registering(Exec::class) {
    description = "Compiles JNI shared library for Lean session-value state machine"
    group = LifecycleBasePlugin.BUILD_GROUP
    dependsOn(verifyLean)
    workingDir = file("lean")
    val outputDir = layout.buildDirectory.dir("natives/linuxX64")
    outputs.dir(outputDir)
    doFirst {
        outputDir.get().asFile.mkdirs()
    }
    val javaHome = javaHomeProvider.get()
    val leanPrefix = leanPrefixProvider.get()
    commandLine(
        "clang",
        "-shared",
        "-fPIC",
        "c/session_value_bridge.c",
        ".lake/build/lib/libSessionValue_SessionValue.a",
        "-I$javaHome/include",
        "-I$javaHome/include/linux",
        "-I$javaHome/include/darwin",
        "-I$leanPrefix/include",
        "-L$leanPrefix/lib/lean",
        "-L$leanPrefix/lib",
        "-lleanshared",
        "-Wl,-rpath,$leanPrefix/lib/lean",
        "-o",
        outputDir.get().file("libsessionvalue_lean.so").asFile.absolutePath,
    )
}

kotlin {
    androidLibrary {
        namespace = "com.alexvanyo.composelife.sessionvalue"
        minSdk = 24
        configureGradleManagedDevices(enumValues<FormFactor>().toSet(), this)
    }

    jvm("desktop") {
        bundlesPrebuiltNatives {
            linuxX64.add(layout.buildDirectory.dir("natives/linuxX64"))
        }
    }

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
            dependencies {
                implementation(projects.logging)
                implementation(projects.serialization)
            }
        }
        val jbMain by creating {
            dependsOn(commonMain)
            dependencies {
                api(libs.androidx.compose.runtime)
                api(libs.androidx.compose.runtime.saveable)
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
                implementation(projects.injectTest)
                implementation(projects.kmpAndroidRunner)
                implementation(projects.kmpStateRestorationTester)
                implementation(projects.testActivity)
                implementation(libs.kotlinx.coroutines.test)
                implementation(libs.kotlinx.io.core)
                implementation(libs.kotlinx.serialization.json)
                implementation(libs.molecule)
                implementation(libs.turbine)
            }
        }
        val jvmTest by creating {
            dependsOn(commonTest)
        }
        val jbTest by creating {
            dependsOn(commonTest)
            dependencies {
                implementation(libs.jetbrains.compose.uiTest)
            }
        }
        val desktopTest by getting {
            dependsOn(jbTest)
            dependencies {
                implementation(libs.kni.jni)
            }
        }
        val androidSharedTest by getting {
            dependsOn(jbTest)
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
    }
}

tasks.named("collectPrebuiltLibsJvm") {
    dependsOn(buildSessionValueLeanSharedLibrary)
}

tasks.named("check") {
    dependsOn(verifyLean)
}

tasks.named("desktopTest") {
    dependsOn(verifyLean)
}
