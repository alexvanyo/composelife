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
import org.gradle.kotlin.dsl.create
import org.gradle.kotlin.dsl.invoke

data class GradleManagedDeviceConfig(
    val device: AndroidDevice,
    val apiLevel: Int,
    val systemImageSource: SystemImageSource,
)

val GradleManagedDeviceConfig.taskPrefix get() =
    buildString {
        append(
            when (systemImageSource) {
                SystemImageSource.Aosp -> "aosp"
                SystemImageSource.AospAtd -> "aospatd"
                SystemImageSource.Google -> "google"
                SystemImageSource.GoogleAtd -> "googleatd"
                SystemImageSource.GooglePlayStore -> "googleplaystore"
                SystemImageSource.AndroidDesktop -> "desktop"
                SystemImageSource.AndroidWear -> "wear"
            },
        )
        append(device)
        append("api")
        append(apiLevel)
    }
        .toLowerCaseAsciiOnly()
        .replace(" ", "")

enum class SystemImageSource {
    Aosp,
    AospAtd,
    Google,
    GoogleAtd,
    GooglePlayStore,
    AndroidDesktop,
    AndroidWear,
}

sealed interface AndroidDevice {

    enum class MobileDevice : AndroidDevice {
        Nexus4,
        Nexus5,
        PixelFold,
        PixelTablet,
        Pixel2,
        Pixel3XL,
        Pixel6Pro,
    }

    enum class DesktopDevice : AndroidDevice {
        MediumDesktop,
    }

    enum class WearDevice : AndroidDevice {
        WearOSSquare,
        WearOSSmallRound,
        WearOSLargeRound,
    }
}

enum class FormFactor {
    Mobile, Wear
}

@JvmName("configureGradleManagedDevicesFormFactors")
fun configureGradleManagedDevices(
    formFactors: Set<FormFactor>,
    commonExtension: CommonExtension<*, *, *, *, *, *>,
) = configureGradleManagedDevices(
    devices = formFactors
        .map { formFactor ->
            when (formFactor) {
                FormFactor.Mobile -> mobileDevices
                FormFactor.Wear -> wearDevices
            }
        }
        .flatten()
        .toSet(),
    commonExtension = commonExtension,
)

@Suppress("CyclomaticComplexMethod")
@JvmName("configureGradleManagedDevicesDeviceConfig")
fun configureGradleManagedDevices(
    devices: Set<GradleManagedDeviceConfig>,
    commonExtension: CommonExtension<*, *, *, *, *, *>,
) {
    commonExtension.testOptions.managedDevices.devices {
        devices
            .forEach { config ->
                create<ManagedVirtualDevice>(config.taskPrefix) {
                    this.device = when (config.device) {
                        AndroidDevice.DesktopDevice.MediumDesktop -> "Medium Desktop"
                        AndroidDevice.MobileDevice.Nexus4 -> "Nexus 4"
                        AndroidDevice.MobileDevice.Nexus5 -> "Nexus 5"
                        AndroidDevice.MobileDevice.PixelFold -> "Pixel Fold"
                        AndroidDevice.MobileDevice.PixelTablet -> "Pixel Tablet"
                        AndroidDevice.MobileDevice.Pixel2 -> "Pixel 2"
                        AndroidDevice.MobileDevice.Pixel3XL -> "Pixel 3 XL"
                        AndroidDevice.MobileDevice.Pixel6Pro -> "Pixel 6 Pro"
                        AndroidDevice.WearDevice.WearOSSquare -> "Wear OS Square"
                        AndroidDevice.WearDevice.WearOSSmallRound -> "Wear OS Small Round"
                        AndroidDevice.WearDevice.WearOSLargeRound -> "Wear OS Large Round"
                    }
                    this.apiLevel = config.apiLevel
                    this.systemImageSource = when (config.systemImageSource) {
                        SystemImageSource.Aosp -> "aosp"
                        SystemImageSource.AospAtd -> "aosp-atd"
                        SystemImageSource.Google -> "google"
                        SystemImageSource.GoogleAtd -> "google-atd"
                        SystemImageSource.GooglePlayStore -> "google_apis_playstore"
                        SystemImageSource.AndroidDesktop -> "android-desktop"
                        SystemImageSource.AndroidWear -> "android-wear"
                    }
                }
            }
    }
}

private val mobileDevices = run {
    val deviceNames =
        enumValues<AndroidDevice.MobileDevice>().toList() +
            enumValues<AndroidDevice.DesktopDevice>().toList()
    val apiLevels = 21..34
    val systemImageSources = listOf(
        SystemImageSource.Aosp,
        SystemImageSource.AospAtd,
        SystemImageSource.Google,
        SystemImageSource.GoogleAtd,
        SystemImageSource.GooglePlayStore,
        SystemImageSource.AndroidDesktop,
    )

    deviceNames.flatMap { deviceName ->
        apiLevels.flatMap { apiLevel ->
            systemImageSources.map { systemImageSource ->
                GradleManagedDeviceConfig(
                    device = deviceName,
                    apiLevel = apiLevel,
                    systemImageSource = systemImageSource,
                )
            }
        }
    }
        .filterNot {
            // aosp-atd is only supported on some versions
            it.systemImageSource == SystemImageSource.AospAtd && it.apiLevel !in 30..34
        }
        .filterNot {
            // google-atd is only supported on some versions
            it.systemImageSource == SystemImageSource.GoogleAtd && it.apiLevel !in 30..33
        }
        .filterNot {
            // Desktop images only make sense on desktop devices
            (
                it.systemImageSource == SystemImageSource.AndroidDesktop &&
                    it.device !is AndroidDevice.DesktopDevice
                ) ||
                (
                    it.systemImageSource != SystemImageSource.AndroidDesktop &&
                        it.device is AndroidDevice.DesktopDevice
                    ) ||
                // Desktop images are only supported on some versions
                (it.systemImageSource == SystemImageSource.AndroidDesktop && it.apiLevel !in 32..33)
        }
}

private val wearDevices = run {
    val deviceNames = enumValues<AndroidDevice.WearDevice>()
    val apiLevels = setOf(28, 30, 33)
    val systemImageSources = listOf(
        SystemImageSource.AndroidWear,
    )

    deviceNames.flatMap { deviceName ->
        apiLevels.flatMap { apiLevel ->
            systemImageSources.map { systemImageSource ->
                GradleManagedDeviceConfig(
                    device = deviceName,
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
