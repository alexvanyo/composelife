/*
 * Copyright 2026 The Android Open Source Project
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

plugins {
    alias(libs.plugins.convention.kotlinMultiplatform)
    alias(libs.plugins.convention.detekt)
    alias(libs.plugins.convention.kotlinMultiplatformCompose)
    alias(libs.plugins.convention.lean)
    alias(libs.plugins.gradleDependenciesSorter)
}

composeCompiler {
    targetKotlinPlatforms.set(
        setOf(
            org.jetbrains.kotlin.gradle.plugin.KotlinPlatformType.jvm,
        ),
    )
}

lean {
    target = "MosaicCalculator:static"
    packageName = "com.alexvanyo.composelife.mosaiccalculator"
    kotlinBytecodeClassPaths.addAll(
        "com/alexvanyo/composelife/mosaiccalculator/CalculatorEngineKt.class",
        "com/alexvanyo/composelife/mosaiccalculator/CalculatorScreenKt.class",
        "com/alexvanyo/composelife/mosaiccalculator/ComposableSingletons\$CalculatorScreenKt.class",
    )
}

kotlin {
    jvm("desktop")

    sourceSets {
        val commonMain by getting {
            dependencies {
                implementation(libs.androidx.compose.runtime)
                implementation(libs.mosaic.runtime)
            }
        }
        val desktopTest by getting {
            dependencies {
                implementation(projects.leanTestFixtures)
                implementation(libs.kotlin.test)
                implementation(libs.kotlinx.coroutines.test)
                implementation(libs.mosaic.testing)
            }
        }
    }
}
