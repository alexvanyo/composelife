import io.gitlab.arturbosch.detekt.Detekt
import org.jetbrains.kotlin.gradle.dsl.JvmTarget
import org.jetbrains.kotlin.gradle.tasks.KotlinCompile

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

plugins {
    // Satisfy Gradle plugin versioning alignment by adding all unversioned convention plugins here
    // (but only applying used ones)
    alias(libs.plugins.convention.androidApplication) apply false
    alias(libs.plugins.convention.androidApplicationCompose) apply false
    alias(libs.plugins.convention.androidApplicationJacoco) apply false
    alias(libs.plugins.convention.androidApplicationKsp) apply false
    alias(libs.plugins.convention.androidApplicationTesting) apply false
    alias(libs.plugins.convention.androidLibrary) apply false
    alias(libs.plugins.convention.androidLibraryCompose) apply false
    alias(libs.plugins.convention.androidLibraryJacoco) apply false
    alias(libs.plugins.convention.androidLibraryKsp) apply false
    alias(libs.plugins.convention.androidLibraryRoborazzi) apply false
    alias(libs.plugins.convention.androidLibraryTesting) apply false
    alias(libs.plugins.convention.androidTest) apply false
    alias(libs.plugins.convention.detekt) apply false
    alias(libs.plugins.convention.kotlinMultiplatform) apply false
    alias(libs.plugins.convention.kotlinMultiplatformCompose) apply false

    alias(libs.plugins.convention.mergeJacoco)
    // Ensure the correct transitive dependencies are resolved for the wire plugin in combination
    // with the other plugins applied throughout the project.
    // See https://github.com/square/wire/issues/2818#issuecomment-1924641275 for more details
    alias(libs.plugins.wire) apply false
    alias(libs.plugins.ksp) apply false
    alias(libs.plugins.compose) apply false
}

buildscript {
    repositories {
        google()
        mavenCentral()
    }
    dependencies {
        classpath(libs.android.gradlePlugin)
        classpath(kotlin("gradle-plugin", libs.versions.kotlin.get()))
    }
}

task<Delete>("clean") {
    delete(rootProject.layout.buildDirectory)
}

tasks.register("check") {
    dependsOn(
        gradle.includedBuilds.map {
            it.task(":check")
        }
    )
}

tasks.register("packageStagingAndroidTest")
tasks.register("packageDebugAndroidTest")
