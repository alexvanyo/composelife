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

import io.gitlab.arturbosch.detekt.Detekt
import org.jetbrains.kotlin.gradle.tasks.KotlinCompile

plugins {
    `kotlin-dsl`
    alias(libs.plugins.detekt)
}

group = "com.alexvanyo.composelife.buildlogic"

java {
    sourceCompatibility = JavaVersion.VERSION_17
    targetCompatibility = JavaVersion.VERSION_17
}

tasks.withType<KotlinCompile>().configureEach {
    kotlinOptions {
        jvmTarget = JavaVersion.VERSION_17.toString()
        allWarningsAsErrors = true
    }
}

detekt {
    buildUponDefaultConfig = true
    allRules = true
    autoCorrect = System.getenv("CI") != "true"
    config.setFrom("$rootDir/../config/detekt.yml")
}

tasks.withType<Detekt>().configureEach {
    jvmTarget = JavaVersion.VERSION_11.toString()
}

tasks.withType<Detekt>().all {
    tasks.getByName("check").dependsOn(this)
}

dependencies {
    implementation(libs.android.r8)
    implementation(libs.android.gradlePlugin)
    implementation(libs.android.tools.common)
    implementation(kotlin("gradle-plugin", libs.versions.kotlin.get()))
    implementation(libs.detekt.gradlePlugin)
    implementation(libs.keeper.gradlePlugin)
    implementation(libs.ksp.gradlePlugin)
    implementation(libs.paparazzi.gradlePlugin)
    implementation(libs.jetbrains.compose.gradlePlugin)
    detektPlugins(libs.detekt.formatting)
}

gradlePlugin {
    plugins {
        register("androidApplication") {
            id = "com.alexvanyo.composelife.android.application"
            implementationClass = "AndroidApplicationConventionPlugin"
        }
        register("androidApplicationCompose") {
            id = "com.alexvanyo.composelife.android.application.compose"
            implementationClass = "AndroidApplicationComposeConventionPlugin"
        }
        register("androidApplicationJacoco") {
            id = "com.alexvanyo.composelife.android.application.jacoco"
            implementationClass = "AndroidApplicationJacocoConventionPlugin"
        }
        register("androidApplicationKsp") {
            id = "com.alexvanyo.composelife.android.application.ksp"
            implementationClass = "AndroidApplicationKspConventionPlugin"
        }
        register("androidApplicationTesting") {
            id = "com.alexvanyo.composelife.android.application.testing"
            implementationClass = "AndroidApplicationTestingConventionPlugin"
        }
        register("androidLibrary") {
            id = "com.alexvanyo.composelife.android.library"
            implementationClass = "AndroidLibraryConventionPlugin"
        }
        register("androidLibraryCompose") {
            id = "com.alexvanyo.composelife.android.library.compose"
            implementationClass = "AndroidLibraryComposeConventionPlugin"
        }
        register("androidLibraryJacoco") {
            id = "com.alexvanyo.composelife.android.library.jacoco"
            implementationClass = "AndroidLibraryJacocoConventionPlugin"
        }
        register("androidLibraryKsp") {
            id = "com.alexvanyo.composelife.android.library.ksp"
            implementationClass = "AndroidLibraryKspConventionPlugin"
        }
        register("androidLibraryPaparazzi") {
            id = "com.alexvanyo.composelife.android.library.paparazzi"
            implementationClass = "AndroidLibraryPaparazziConventionPlugin"
        }
        register("androidLibraryTesting") {
            id = "com.alexvanyo.composelife.android.library.testing"
            implementationClass = "AndroidLibraryTestingConventionPlugin"
        }
        register("androidTest") {
            id = "com.alexvanyo.composelife.android.test"
            implementationClass = "AndroidTestConventionPlugin"
        }
        register("detekt") {
            id = "com.alexvanyo.composelife.detekt"
            implementationClass = "DetektConventionPlugin"
        }
        register("kotlinMultiplatformConventionPlugin") {
            id = "com.alexvanyo.composelife.kotlin.multiplatform"
            implementationClass = "KotlinMultiplatformConventionPlugin"
        }
        register("kotlinMultiplatformComposeConventionPlugin") {
            id = "com.alexvanyo.composelife.kotlin.multiplatform.compose"
            implementationClass = "KotlinMultiplatformComposeConventionPlugin"
        }
        register("mergeJacoco") {
            id = "com.alexvanyo.composelife.mergejacoco"
            implementationClass = "MergeJacocoConventionPlugin"
        }
    }
}
