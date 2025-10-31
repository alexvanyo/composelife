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
import com.alexvanyo.composelife.buildlogic.configureAndroidTesting
import com.alexvanyo.composelife.buildlogic.configureTesting
import com.android.build.api.dsl.ApplicationExtension
import com.android.build.api.variant.ApplicationAndroidComponentsExtension
import com.slack.keeper.KeeperExtension
import com.slack.keeper.optInToKeeper
import org.gradle.api.GradleException

class AndroidApplicationTestingConventionPlugin : ConventionPlugin({
    val enableKeeperProperty = providers.gradleProperty("com.alexvanyo.composelife.enableKeeper")
    val enableKeeper = enableKeeperProperty
        .orElse(defaultEnableKeeper.toString())
        .map {
            when (it) {
                "true" -> true
                "false" -> false
                else ->
                    throw GradleException("Unexpected value $it for enableKeeper!")
            }
        }

    with(pluginManager) {
        apply("com.android.application")
    }

    extensions.configure(ApplicationExtension::class.java) {
        defaultConfig {
            val testBuildTypeProperty =
                providers
                    .gradleProperty("com.alexvanyo.composelife.testBuildType")
                    .orNull
            if (testBuildTypeProperty !in setOf(null, "staging", "debug")) {
                throw GradleException("Unexpected value $testBuildTypeProperty for testBuildType!")
            }
            testBuildType = testBuildTypeProperty ?: defaultTestBuildType
        }
        configureTesting(this)
    }

    configureAndroidTesting(
        extensions.getByType(ApplicationExtension::class.java),
        extensions.getByType(ApplicationExtension::class.java),
    )

    if (enableKeeper.get()) {
        with(pluginManager) {
            apply("com.slack.keeper")
        }

        extensions.configure(ApplicationAndroidComponentsExtension::class.java) {
            beforeVariants { builder ->
                if (builder.buildType == "staging") {
                    builder.optInToKeeper()
                }
            }
        }

        extensions.configure(KeeperExtension::class.java) {
            automaticR8RepoManagement.set(false)
            traceReferences {}
        }
    }
})

/**
 * The default value to enable Keeper or not, if none is specified by the property
 * "com.alexvanyo.composelife.enableKeeper".
 */
@Suppress("TopLevelPropertyNaming")
private const val defaultEnableKeeper = true

/**
 * The default test build type, if none is specified by the property "com.alexvanyo.composelife.testBuildType".
 */
@Suppress("TopLevelPropertyNaming")
private const val defaultTestBuildType = "staging"
