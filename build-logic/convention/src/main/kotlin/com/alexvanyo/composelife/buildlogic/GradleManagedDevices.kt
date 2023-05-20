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
import com.android.build.api.dsl.ManagedVirtualDevice
import com.android.utils.Environment
import org.gradle.api.GradleException
import org.gradle.api.Project
import org.gradle.kotlin.dsl.create
import org.gradle.kotlin.dsl.invoke

private data class GradleManagedDeviceConfig(
    val deviceName: String,
    val apiLevel: Int,
    val systemImageSource: String,
)

sealed interface FormFactor {
    object Mobile : FormFactor
    object Wear : FormFactor

    companion object {
        val All get() = setOf(Mobile, Wear)
    }
}

@Suppress("LongMethod", "CyclomaticComplexMethod", "NoNameShadowing")
fun Project.configureGradleManagedDevices(
    formFactors: Set<FormFactor>,
    commonExtension: CommonExtension<*, *, *, *, *>,
) {
    commonExtension.testOptions.managedDevices.devices {
        formFactors
            .map {
                when (it) {
                    FormFactor.Mobile -> mobileDevices
                    FormFactor.Wear -> wearDevices
                }
            }
            .flatten()
            .forEach { config ->
                create<ManagedVirtualDevice>(
                    buildString {
                        append(
                            when (config.systemImageSource) {
                                "aosp" -> "aosp"
                                "aosp-atd" -> "aospatd"
                                "google" -> "google"
                                "google-atd" -> "googleatd"
                                "google_apis_playstore" -> "googleplaystore"
                                "android-desktop" -> "desktop"
                                "android-wear" -> "wear"
                                else -> throw GradleException("Unknown system image source!")
                            },
                        )
                        append(config.deviceName)
                        append("api")
                        append(config.apiLevel)
                    }
                        .toLowerCaseAsciiOnly()
                        .replace(" ", ""),
                ) {
                    this.device = config.deviceName
                    this.apiLevel = config.apiLevel
                    this.systemImageSource = config.systemImageSource
                }
            }
    }
    // TODO: This shouldn't be necessary, there seems to be some issue with configuration caching with GMD
    //       https://issuetracker.google.com/issues/262270582
    tasks.configureEach {
        doFirst {
            Environment.initialize()
        }
    }
}

private val mobileDevices = run {
    val deviceNames = listOf(
        "Nexus 4",
        "Nexus 5",
        "Pixel C",
        "Pixel 2",
        "Pixel 3 XL",
        "Pixel 6 Pro",
        "Medium Desktop",
    )
    val apiLevels = 21..33
    val systemImageSources = listOf(
        "aosp",
        "aosp-atd",
        "google",
        "google-atd",
        "google_apis_playstore",
        "android-desktop",
    )

    deviceNames.flatMap { deviceName ->
        apiLevels.flatMap { apiLevel ->
            systemImageSources.map { systemImageSource ->
                GradleManagedDeviceConfig(
                    deviceName = deviceName,
                    apiLevel = apiLevel,
                    systemImageSource = systemImageSource,
                )
            }
        }
    }
        .filterNot {
            // ATD is only supported on some versions
            "atd" in it.systemImageSource && it.apiLevel !in 30..31
        }
        .filterNot {
            // aosp images are only supported on some versions
            it.systemImageSource == "aosp" && it.apiLevel > 31
        }
        .filterNot {
            // Desktop images only make sense on desktop devices
            (it.systemImageSource == "android-desktop" && "Desktop" !in it.deviceName) ||
                    (it.systemImageSource != "android-desktop" && "Desktop" in it.deviceName) ||
                    // Desktop images are only supported on some versions
                    (it.systemImageSource == "android-desktop" && it.apiLevel != 32)
        }
}

private val wearDevices = run {
    val deviceNames = listOf(
        "Wear OS Square",
        "Wear OS Small Round",
        "Wear OS Large Round",
    )
    val apiLevels = setOf(28, 30, 33)
    val systemImageSources = listOf(
        "android-wear"
    )

    deviceNames.flatMap { deviceName ->
        apiLevels.flatMap { apiLevel ->
            systemImageSources.map { systemImageSource ->
                GradleManagedDeviceConfig(
                    deviceName = deviceName,
                    apiLevel = apiLevel,
                    systemImageSource = systemImageSource,
                )
            }
        }
    }
}

private fun String.toLowerCaseAsciiOnly(): String =
    buildString {
        for (c in this@toLowerCaseAsciiOnly) {
            append(if (c in 'A'..'Z') c.lowercaseChar() else c)
        }
    }
