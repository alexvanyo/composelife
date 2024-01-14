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

plugins {
    alias(libs.plugins.convention.kotlinMultiplatform)
    alias(libs.plugins.convention.androidLibrary)
    alias(libs.plugins.convention.androidLibraryJacoco)
    alias(libs.plugins.convention.androidLibraryKsp)
    alias(libs.plugins.convention.androidLibraryTesting)
    alias(libs.plugins.convention.detekt)
    alias(libs.plugins.sqldelight)
    alias(libs.plugins.gradleDependenciesSorter)
}

android {
    namespace = "com.alexvanyo.composelife.database"
    defaultConfig {
        minSdk = 21
    }
    lint {
        lintConfig = file("lint.xml")
    }
    configureGradleManagedDevices(FormFactor.All, this)
}

kotlin {
    androidTarget()
    jvm()

    sourceSets {
        val commonMain by getting {
            dependencies {
                api(libs.kotlinx.coroutines.core)
                api(projects.dispatchers)
                api(projects.updatable)

                implementation(libs.kotlinInject.runtime)
                implementation(libs.sqldelight.coroutinesExtensions)
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
        val jvmMain by getting {
            dependencies {
                implementation(libs.sqldelight.sqliteDriver)
            }
        }
        val commonTest by getting {
            dependencies {
                implementation(libs.kotlinx.coroutines.test)
                implementation(libs.turbine)
                implementation(projects.databaseTest)
                implementation(projects.dispatchersTest)
                implementation(projects.kmpAndroidRunner)
            }
        }
        val androidSharedTest by getting {
            dependencies {
                implementation(libs.androidx.test.core)
                implementation(libs.androidx.test.junit)
                implementation(libs.androidx.test.runner)
            }
        }
        val androidUnitTest by getting {
            configurations["kspAndroidTest"].dependencies.add(libs.kotlinInject.ksp.get())
        }
        val androidInstrumentedTest by getting {
            configurations["kspAndroidAndroidTest"].dependencies.add(libs.kotlinInject.ksp.get())
        }
        val jvmTest by getting {
            configurations["kspJvmTest"].dependencies.add(libs.kotlinInject.ksp.get())
        }
    }
}

sqldelight {
    databases {
        create("ComposeLifeDatabase") {
            packageName.set("com.alexvanyo.composelife.database")
            schemaOutputDirectory.set(file("src/commonMain/sqldelight/databases"))
            verifyMigrations.set(true)
        }
    }
}
