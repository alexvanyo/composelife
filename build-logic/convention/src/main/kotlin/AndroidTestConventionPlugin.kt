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
import com.alexvanyo.composelife.buildlogic.configureKotlinAndroid
import com.android.build.gradle.TestExtension
import org.gradle.kotlin.dsl.configure

class AndroidTestConventionPlugin : ConventionPlugin({
    with(pluginManager) {
        apply("com.android.test")
    }

    extensions.configure<TestExtension> {
        configureKotlinAndroid(this)

        defaultConfig {
            minSdk = 23
            targetSdk = 31
            testInstrumentationRunner = "androidx.test.runner.AndroidJUnitRunner"
        }

        signingConfigs {
            named("debug") {
                keyAlias = "debug"
                keyPassword = "android"
                storeFile = file("$rootDir/keystore/debug.jks")
                storePassword = "android"
            }
        }

        experimentalProperties["android.experimental.self-instrumenting"] = true

        buildTypes {
            create("benchmark") {
                matchingFallbacks.add("release") // fallback to release for dependencies
                signingConfig = signingConfigs.getByName("debug") // sign with debug for testing
            }
        }
    }
},)
