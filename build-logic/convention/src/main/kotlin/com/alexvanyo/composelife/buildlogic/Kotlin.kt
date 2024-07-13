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
import org.gradle.kotlin.dsl.assign
import org.gradle.kotlin.dsl.closureOf
import org.gradle.kotlin.dsl.configure
import org.gradle.kotlin.dsl.withType
import org.jetbrains.kotlin.gradle.dsl.JvmTarget
import org.jetbrains.kotlin.gradle.dsl.KotlinMultiplatformExtension
import org.jetbrains.kotlin.gradle.plugin.KotlinSourceSet
import org.jetbrains.kotlin.gradle.tasks.KotlinCompile

fun Project.configureKotlin() {
    tasks.withType<KotlinCompile>().configureEach {
        compilerOptions {
            jvmTarget = JvmTarget.JVM_11
            // TODO: Currently disabled due to warning for usage of context receivers
            //       https://github.com/Kotlin/KEEP/issues/367#issuecomment-2075034205
            // allWarningsAsErrors = true
        }
    }

    extensions.configure<KotlinMultiplatformExtension> {
        sourceSets.configure(
            closureOf<NamedDomainObjectContainer<KotlinSourceSet>> {
                configureEach {
                    languageSettings {
                        // TODO: Remove when out of beta: https://youtrack.jetbrains.com/issue/KT-61573
                        enableLanguageFeature("ExpectActualClasses")
                        enableLanguageFeature("ContextReceivers")
                        enableLanguageFeature("MultiDollarInterpolation")
                        optIn("kotlin.uuid.ExperimentalUuidApi")
                    }
                }
            },
        )
    }
}
