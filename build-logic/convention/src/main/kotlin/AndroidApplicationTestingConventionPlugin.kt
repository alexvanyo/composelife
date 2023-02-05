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
import com.android.build.api.variant.ApplicationAndroidComponentsExtension
import com.android.build.gradle.internal.dsl.BaseAppModuleExtension
import com.slack.keeper.KeeperExtension
import com.slack.keeper.optInToKeeper
import org.gradle.api.GradleException
import org.gradle.api.artifacts.VersionCatalogsExtension
import org.gradle.kotlin.dsl.configure
import org.gradle.kotlin.dsl.dependencies
import org.gradle.kotlin.dsl.getByType

class AndroidApplicationTestingConventionPlugin : ConventionPlugin({
    val enableKeeperProperty = findProperty("com.alexvanyo.composelife.enableKeeper") as String?
    val enableKeeper = when (enableKeeperProperty) {
        "true" -> true
        "false" -> false
        null -> defaultEnableKeeper
        else -> throw GradleException("Unexpected value $enableKeeperProperty for enableKeeper!")
    }

    with(pluginManager) {
        apply("com.android.application")
    }

    val libs = extensions.getByType<VersionCatalogsExtension>().named("libs")

    extensions.configure<BaseAppModuleExtension> {
        defaultConfig {
            val testBuildTypeProperty = findProperty("com.alexvanyo.composelife.testBuildType") as String?
            if (testBuildTypeProperty !in setOf(null, "staging", "debug")) {
                throw GradleException("Unexpected value $testBuildTypeProperty for testBuildType!")
            }
            testBuildType = testBuildTypeProperty ?: defaultTestBuildType
        }

        configureTesting(this)
        configureAndroidTesting(this)
    }

    if (enableKeeper) {
        with(pluginManager) {
            apply("com.slack.keeper")
        }

        extensions.configure<ApplicationAndroidComponentsExtension> {
            beforeVariants { builder ->
                if (builder.buildType == "staging") {
                    builder.optInToKeeper()
                }
            }
        }

        extensions.configure<KeeperExtension> {
            automaticR8RepoManagement.set(false)
            traceReferences {}
        }

        dependencies {
            add("keeperR8", libs.findLibrary("android.r8").get())
        }
    }
},)

/**
 * The default value to enable Keeper or not, if none is specified by the property
 * "com.alexvanyo.composelife.enableKeeper".
 */
private const val defaultEnableKeeper = false

/**
 * The default test build type, if none is specified by the property "com.alexvanyo.composelife.testBuildType".
 */
private const val defaultTestBuildType = "debug"
