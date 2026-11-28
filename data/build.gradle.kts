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
import com.android.build.api.dsl.KotlinMultiplatformAndroidDeviceTestCompilation
import dev.zacsweers.metro.gradle.DiagnosticSeverity
import org.jetbrains.kotlin.gradle.ExperimentalWasmDsl

plugins {
    alias(libs.plugins.convention.kotlinMultiplatform)
    alias(libs.plugins.convention.androidLibrary)
    alias(libs.plugins.convention.androidLibraryCompose)
    alias(libs.plugins.convention.androidLibraryJacoco)
    alias(libs.plugins.convention.androidLibraryTesting)
    alias(libs.plugins.convention.detekt)
    alias(libs.plugins.gradleDependenciesSorter)
    alias(libs.plugins.metro)
}

metro {
    @OptIn(dev.zacsweers.metro.gradle.DelicateMetroGradleApi::class, dev.zacsweers.metro.gradle.RequiresIdeSupport::class)
    enableTopLevelFunctionInjection = true
    unusedGraphInputsSeverity = DiagnosticSeverity.NONE
}

kotlin {
    android {
        namespace = "com.alexvanyo.composelife.data"
        minSdk = 24
        compilations.withType(KotlinMultiplatformAndroidDeviceTestCompilation::class.java) {
            instrumentationRunner = "com.alexvanyo.composelife.test.InjectTestRunner"
        }
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
        val commonMain = getByName("commonMain") {
            dependencies {
                api(projects.database)
                api(projects.dispatchers)
                api(projects.network)
                api(libs.kotlinx.coroutines.core)

                implementation(projects.algorithm)
                implementation(projects.clock)
                implementation(projects.filesystem)
                implementation(projects.injectScopes)
                implementation(projects.logging)
                implementation(projects.timeUtil)
                implementation(projects.updatable)
                implementation(projects.work)
                implementation(libs.kotlinx.io.core)
                implementation(libs.kotlinx.io.okio)
                implementation(libs.okio)
            }
        }
        val jbMain = create("jbMain") {
            dependsOn(commonMain)
        }
        val jvmMain = create("jvmMain") {
            dependsOn(jbMain)
        }
        val desktopMain = getByName("desktopMain") {
            dependsOn(jvmMain)
        }
        val androidMain = getByName("androidMain") {
            dependsOn(jvmMain)
            dependencies {
                api(libs.kotlinx.coroutines.android)

                implementation(libs.androidx.work.runtime)
                implementation(libs.guava.android)
                implementation(libs.kotlinx.coroutines.guava)
            }
        }
        val wasmJsMain = getByName("wasmJsMain") {
            dependsOn(jbMain)
        }
        val commonTest = getByName("commonTest") {
            dependencies {
                implementation(projects.dataTestResources)
                implementation(projects.databaseTestFixtures)
                implementation(projects.dispatchersTestFixtures)
                implementation(projects.filesystemTestFixtures)
                implementation(projects.injectTest)
                implementation(projects.networkTestFixtures)
                implementation(projects.tracingTestFixtures)
                implementation(projects.workTestFixtures)
                implementation(libs.kotlinx.coroutines.test)
                implementation(libs.turbine)
            }
        }
        val jbTest = create("jbTest") {
            dependsOn(commonTest)
        }
        val jvmTest = create("jvmTest") {
            dependsOn(jbTest)
        }
        val desktopTest = getByName("desktopTest") {
            dependsOn(jvmTest)
        }
        val androidSharedTest = getByName("androidSharedTest") {
            dependsOn(jvmTest)
            dependencies {
                implementation(libs.androidx.test.core)
                implementation(libs.androidx.test.junit)
                implementation(libs.androidx.test.runner)
            }
        }
        val wasmJsTest = getByName("wasmJsTest") {
            dependsOn(jbTest)
        }
    }
}
