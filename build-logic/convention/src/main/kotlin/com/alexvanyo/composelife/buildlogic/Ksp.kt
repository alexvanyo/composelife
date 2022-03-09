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

import com.android.build.api.dsl.CommonExtension
import com.android.build.api.variant.AndroidComponentsExtension
import org.gradle.api.Project

fun Project.configureKsp(
    commonExtension: CommonExtension<*, *, *, *>,
    androidComponentsExtension: AndroidComponentsExtension<*, *, *>,
) {
    androidComponentsExtension.onVariants { applicationVariant ->
        commonExtension.sourceSets {
            getByName(applicationVariant.name) {
                java.srcDir(file("build/generated/ksp/${applicationVariant.name}/kotlin"))
            }
            getByName("test${applicationVariant.name.capitalize()}") {
                java.srcDir(file("build/generated/ksp/${applicationVariant.name}UnitTest/kotlin"))
            }
        }

        // TODO: Add explicit dependency to avoid "execution optimizations have been disabled to ensure correctness"
        afterEvaluate {
            tasks.getByName("lintAnalyze${applicationVariant.name.capitalize()}")
                .dependsOn("ksp${applicationVariant.name.capitalize()}UnitTestKotlin")
        }
    }
}
