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

import com.alexvanyo.composelife.buildlogic.ConventionPlugin
import com.alexvanyo.composelife.buildlogic.configureAndroid
import com.alexvanyo.composelife.buildlogic.configureKotlin
import com.android.build.api.dsl.KotlinMultiplatformAndroidLibraryTarget
import org.jetbrains.kotlin.gradle.dsl.KotlinMultiplatformExtension

class AndroidLibraryConventionPlugin : ConventionPlugin({
    with(pluginManager) {
        apply("org.jetbrains.kotlin.multiplatform")
        apply("com.android.kotlin.multiplatform.library")
    }

    configureKotlin()
    extensions.configure(KotlinMultiplatformExtension::class.java) {
        extensions.configure(KotlinMultiplatformAndroidLibraryTarget::class.java) {
            configureAndroid(this)
            lint.targetSdk = 35
            optimization.consumerKeepRules.file("consumer-rules.pro")
        }
    }
    extensions.configure(KotlinMultiplatformExtension::class.java) {
        sourceSets.configureEach {
            languageSettings {
                // TODO: Remove when out of beta: https://youtrack.jetbrains.com/issue/KT-61573
                enableLanguageFeature("ExpectActualClasses")
                enableLanguageFeature("ContextParameters")
                enableLanguageFeature("MultiDollarInterpolation")
                optIn("kotlin.uuid.ExperimentalUuidApi")
                optIn("kotlin.time.ExperimentalTime")
            }
        }
    }
})
