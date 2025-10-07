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

import org.jetbrains.compose.desktop.application.dsl.TargetFormat

plugins {
    alias(libs.plugins.convention.kotlinMultiplatform)
    alias(libs.plugins.convention.dependencyGuard)
    alias(libs.plugins.convention.detekt)
    alias(libs.plugins.convention.kotlinMultiplatformCompose)
    alias(libs.plugins.gradleDependenciesSorter)
    alias(libs.plugins.ksp)
    alias(libs.plugins.metro)
}

kotlin {
    jvm("desktop")

    sourceSets {
        val commonMain by getting {
            dependencies {
                implementation(libs.androidx.compose.runtime)
                implementation(libs.kotlinx.serialization.core)
                implementation(projects.filesystem)
                implementation(projects.imageLoader)
                implementation(projects.injectScopes)
                implementation(projects.logging)
                implementation(projects.network)
                implementation(projects.uiApp)
                implementation(projects.uiMobile)
            }
        }
        val desktopMain by getting {
            configurations["kspDesktop"].dependencies.addAll(listOf(
                libs.sealedEnum.ksp.get(),
            ))
            dependencies {
                implementation(compose.desktop.currentOs)
                implementation(libs.kotlinx.coroutines.swing)
                implementation(libs.sqldelight.sqliteDriver)
            }
        }
        val commonTest by getting {
            dependencies {
                implementation(projects.databaseTestFixtures)
                implementation(projects.dispatchersTestFixtures)
                implementation(projects.patterns)
                implementation(projects.preferencesTestFixtures)
            }
        }
    }
}

compose.desktop {
    application {
        mainClass = "com.alexvanyo.composelife.MainKt"
        buildTypes.release.proguard {
            version = libs.versions.proguard
            configurationFiles.from("proguard-rules.pro")
        }
        nativeDistributions {
            targetFormats(TargetFormat.Deb, TargetFormat.Msi, TargetFormat.Dmg)
            packageName = "ComposeLife"
            modules("java.sql")

            linux {
                iconFile.set(file("icon.png"))
            }
            windows {
                iconFile.set(file("icon.ico"))
            }
            macOS {
                iconFile.set(file("icon.icns"))
            }
        }
    }
}

tasks.withType<JavaExec>().named { it == "run" }.configureEach {
    systemProperty("debug", "true")
}

dependencyGuard {
    configuration("desktopRuntimeClasspath")
}
