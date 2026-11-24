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
import kotlin.jvm.java

plugins {
    alias(libs.plugins.convention.kotlinMultiplatform)
    alias(libs.plugins.convention.androidLibrary)
    alias(libs.plugins.convention.androidLibraryCompose)
    alias(libs.plugins.convention.androidLibraryJacoco)
    alias(libs.plugins.convention.androidLibraryTesting)
    alias(libs.plugins.convention.detekt)
    alias(libs.plugins.convention.kotlinMultiplatformCompose)
    alias(libs.plugins.sqldelight)
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
        namespace = "com.alexvanyo.composelife.database"
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
                api(projects.updatable)
                api(libs.kotlinx.coroutines.core)
                api(libs.kotlinx.datetime)
                api(libs.sqldelight.coroutinesExtensions)

                implementation(projects.dispatchers)
                implementation(projects.injectScopes)
                implementation(libs.androidx.compose.runtime)
                implementation(libs.sqldelight.primitiveAdapters)
                implementation(libs.sqldelightAndroidXDriver)
            }
        }
        val androidMain = getByName("androidMain") {
            dependencies {
                api(libs.kotlinx.coroutines.android)

                implementation(libs.androidx.sqlite.framework)
            }
        }
        val desktopMain = getByName("desktopMain") {
            dependencies {
                implementation(libs.androidx.sqlite.bundled)
            }
        }
        val wasmJsMain = getByName("wasmJsMain") {
            dependencies {
                implementation(libs.androidx.sqlite.web)
                implementation(libs.jetbrains.compose.ui)
                implementation(libs.sqldelightAndroidXDriver.opfs)
            }
        }
        val commonTest = getByName("commonTest") {
            dependencies {
                implementation(projects.databaseTestFixtures)
                implementation(projects.dispatchersTestFixtures)
                implementation(projects.filesystemTestFixtures)
                implementation(projects.injectTest)
                implementation(projects.kmpAndroidRunner)
                implementation(projects.tracingTestFixtures)
                implementation(libs.kotlinx.coroutines.test)
                implementation(libs.turbine)
            }
        }
        val jvmTest = create("jvmTest") {
            dependsOn(commonTest)
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
    }
}

sqldelight {
    databases {
        create("ComposeLifeDatabase") {
            packageName.set("com.alexvanyo.composelife.database")
            schemaOutputDirectory.set(file("src/commonMain/sqldelight/databases"))
            verifyMigrations.set(true)
            verifyDefinitions.set(true)
            generateAsync = true
        }
    }
}
