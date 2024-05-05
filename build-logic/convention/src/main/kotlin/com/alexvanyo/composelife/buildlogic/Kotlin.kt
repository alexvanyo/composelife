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

package com.alexvanyo.composelife.buildlogic

import org.gradle.api.NamedDomainObjectContainer
import org.gradle.api.Project
import org.gradle.api.artifacts.VersionCatalogsExtension
import org.gradle.kotlin.dsl.closureOf
import org.gradle.kotlin.dsl.configure
import org.gradle.kotlin.dsl.getByType
import org.gradle.kotlin.dsl.withType
import org.jetbrains.kotlin.gradle.dsl.JvmTarget
import org.jetbrains.kotlin.gradle.dsl.KotlinMultiplatformExtension
import org.jetbrains.kotlin.gradle.plugin.KotlinSourceSet
import org.jetbrains.kotlin.gradle.tasks.KotlinCompile

fun Project.configureKotlin() {
    tasks.withType<KotlinCompile>().configureEach {
        compilerOptions {
            jvmTarget.set(JvmTarget.JVM_1_8)
            allWarningsAsErrors.set(true)
            freeCompilerArgs.addAll(
                "-Xcontext-receivers",
                // TODO: Remove when out of beta: https://youtrack.jetbrains.com/issue/KT-61573
                "-Xexpect-actual-classes",
            )
        }
    }

    val libs = extensions.getByType<VersionCatalogsExtension>().named("libs")

    extensions.configure<KotlinMultiplatformExtension> {
        sourceSets.configure(
            closureOf<NamedDomainObjectContainer<KotlinSourceSet>> {
                getByName("commonMain") {
                    dependencies {
                        implementation(libs.findLibrary("kermit").get())
                    }
                }
            },
        )
    }
}
