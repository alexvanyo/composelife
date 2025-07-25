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
import org.jetbrains.kotlin.gradle.ExperimentalWasmDsl

plugins {
    alias(libs.plugins.convention.kotlinMultiplatform)
    alias(libs.plugins.convention.androidLibrary)
    alias(libs.plugins.convention.androidLibraryJacoco)
    alias(libs.plugins.convention.androidLibraryTesting)
    alias(libs.plugins.convention.detekt)
    alias(libs.plugins.sqldelight)
    alias(libs.plugins.gradleDependenciesSorter)
    alias(libs.plugins.metro)
}

android {
    namespace = "com.alexvanyo.composelife.database"
    defaultConfig {
        minSdk = 21
        testInstrumentationRunner = "com.alexvanyo.composelife.test.InjectTestRunner"
    }
    configureGradleManagedDevices(enumValues<FormFactor>().toSet(), this)
}

kotlin {
    androidTarget()
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
            dependencies {
                api(libs.kotlinx.coroutines.core)
                api(libs.kotlinx.datetime)
                api(libs.sqldelight.coroutinesExtensions)
                api(projects.dispatchers)
                api(projects.updatable)

                implementation(libs.sqldelight.primitiveAdapters)
                implementation(projects.injectScopes)
            }
        }
        val androidMain by getting {
            dependencies {
                api(libs.kotlinx.coroutines.android)

                implementation(libs.sqldelight.androidDriver)
            }
        }
        val desktopMain by getting {
            dependencies {
                implementation(libs.sqldelight.sqliteDriver)
            }
        }
        val wasmJsMain by getting {
            dependencies {
                implementation(libs.sqldelight.webDriver)
                implementation(npm("@cashapp/sqldelight-sqljs-worker", libs.versions.sqldelight.get()))
                implementation(npm("sql.js", libs.versions.sqlJs.get()))
            }
        }
        val commonTest by getting {
            dependencies {
                implementation(libs.kotlinx.coroutines.test)
                implementation(libs.turbine)
                implementation(projects.databaseTest)
                implementation(projects.dispatchersTest)
                implementation(projects.filesystemTest)
                implementation(projects.injectTest)
                implementation(projects.kmpAndroidRunner)
            }
        }
        val jvmTest by creating {
            dependsOn(commonTest)
        }
        val desktopTest by getting {
            dependsOn(jvmTest)
        }
        val androidSharedTest by getting {
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
