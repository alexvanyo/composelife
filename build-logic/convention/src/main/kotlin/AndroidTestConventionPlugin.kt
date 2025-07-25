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
import com.android.build.gradle.TestExtension

class AndroidTestConventionPlugin : ConventionPlugin({
    with(pluginManager) {
        apply("com.android.test")
    }

    extensions.configure(TestExtension::class.java) {
        configureAndroid(this)

        defaultConfig {
            minSdk = 23
            targetSdk = 35
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
            debug {
                signingConfig = signingConfigs.getByName("debug")
                matchingFallbacks.add("release") // fallback to release for dependencies
            }
            create("release") {
                signingConfig = signingConfigs.getByName("debug") // sign with debug for testing
            }
            create("staging") {
                matchingFallbacks.add("release") // fallback to release for dependencies
                signingConfig = signingConfigs.getByName("debug") // sign with debug for testing
            }
        }
    }
})
