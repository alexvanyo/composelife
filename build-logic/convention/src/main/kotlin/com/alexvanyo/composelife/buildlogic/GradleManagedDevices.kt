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

import com.android.build.gradle.TestedExtension
import org.gradle.api.GradleException
import org.gradle.api.Project
import org.gradle.kotlin.dsl.create
import org.gradle.kotlin.dsl.invoke

private data class GradleManagedDeviceConfig(
    val deviceName: String,
    val apiLevel: Int,
    val systemImageSource: String,
)

fun Project.configureGradleManagedDevices(
    testedExtension: TestedExtension,
) {
    testedExtension.testOptions.managedDevices.devices {
        val deviceNames = listOf("Pixel C", "Pixel 2", "Pixel 3 XL", "Pixel 6 Pro")
        val apiLevels = listOf(27, 28, 29, 30, 31, 32, 33)
        val systemImageSources = listOf("aosp", "aosp-atd", "google")

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
                it.systemImageSource.contains("atd") && it.apiLevel !in 30..31
            }
            .filterNot {
                // aosp images are only supported on some versions
                it.systemImageSource.contains("aosp") && it.apiLevel > 31
            }
            .forEach { config ->
                create<com.android.build.api.dsl.ManagedVirtualDevice>(
                    buildString {
                        append(
                            when (config.systemImageSource) {
                                "aosp" -> "aosp"
                                "aosp-atd" -> "aospatd"
                                "google" -> "google"
                                else -> throw GradleException("Unknown system image source!")
                            }
                        )
                        append(config.deviceName)
                        append("api")
                        append(config.apiLevel)
                    }
                        .toLowerCaseAsciiOnly()
                        .replace(" ", "")
                ) {
                    this.device = config.deviceName
                    this.apiLevel = config.apiLevel
                    this.systemImageSource = config.systemImageSource
                }
            }
    }
}

private fun String.toLowerCaseAsciiOnly(): String =
    buildString {
        for (c in this@toLowerCaseAsciiOnly) {
            append(if (c in 'A'..'Z') c.toLowerCase() else c)
        }
    }
