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
import org.gradle.api.Project
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
                SystemImageSource.AospTablet -> "aosptablet"
                SystemImageSource.AospAtd -> "aospatd"
                SystemImageSource.Google -> "google"
                SystemImageSource.GoogleTablet -> "googletablet"
                SystemImageSource.GoogleAtd -> "googleatd"
                SystemImageSource.GooglePlayStore -> "googleplaystore"
                SystemImageSource.GooglePlayStoreTablet -> "googleplaystoretablet"
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
    AospTablet,
    AospAtd,
    Google,
    GoogleTablet,
    GoogleAtd,
    GooglePlayStore,
    GooglePlayStoreTablet,
    AndroidDesktop,
    AndroidWear,
}

sealed interface AndroidDevice {

    enum class PhoneDevice : AndroidDevice {
        Nexus4,
        Nexus5,
        PixelFold,
        Pixel2,
        Pixel3XL,
        Pixel6Pro,
    }

    enum class TabletDevice : AndroidDevice {
        PixelTablet,
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

fun getGradleManagedDeviceConfig(
    formFactors: Set<FormFactor>,
): Set<GradleManagedDeviceConfig> = formFactors
    .map { formFactor ->
        when (formFactor) {
            FormFactor.Mobile -> mobileDevices
            FormFactor.Wear -> wearDevices
        }
    }
    .flatten()
    .toSet()

@JvmName("configureGradleManagedDevicesFormFactors")
fun Project.configureGradleManagedDevices(
    formFactors: Set<FormFactor>,
    commonExtension: CommonExtension<*, *, *, *, *, *>,
    filterForTests: Boolean = true,
) = configureGradleManagedDevices(
    devices = getGradleManagedDeviceConfig(formFactors),
    filterForTests = filterForTests,
    commonExtension = commonExtension,
)

@Suppress("CyclomaticComplexMethod")
@JvmName("configureGradleManagedDevicesDeviceConfig")
fun Project.configureGradleManagedDevices(
    devices: Set<GradleManagedDeviceConfig>,
    commonExtension: CommonExtension<*, *, *, *, *, *>,
    filterForTests: Boolean = true,
) {
    commonExtension.testOptions.managedDevices.devices {
        devices
            .filter { config ->
                !filterForTests ||
                    providers
                        .gradleProperty("com.alexvanyo.composelife.enabledGradleManagedDevices")
                        .map { config.taskPrefix in it.split(",") }
                        .orElse(true)
                        .get()
            }
            .forEach { config ->
                create<ManagedVirtualDevice>(config.taskPrefix) {
                    this.device = when (config.device) {
                        AndroidDevice.DesktopDevice.MediumDesktop -> "Medium Desktop"
                        AndroidDevice.PhoneDevice.Nexus4 -> "Nexus 4"
                        AndroidDevice.PhoneDevice.Nexus5 -> "Nexus 5"
                        AndroidDevice.PhoneDevice.PixelFold -> "Pixel Fold"
                        AndroidDevice.PhoneDevice.Pixel2 -> "Pixel 2"
                        AndroidDevice.PhoneDevice.Pixel3XL -> "Pixel 3 XL"
                        AndroidDevice.PhoneDevice.Pixel6Pro -> "Pixel 6 Pro"
                        AndroidDevice.TabletDevice.PixelTablet -> "Pixel Tablet"
                        AndroidDevice.WearDevice.WearOSSquare -> "Wear OS Square"
                        AndroidDevice.WearDevice.WearOSSmallRound -> "Wear OS Small Round"
                        AndroidDevice.WearDevice.WearOSLargeRound -> "Wear OS Large Round"
                    }
                    this.apiLevel = config.apiLevel
                    this.systemImageSource = when (config.systemImageSource) {
                        SystemImageSource.Aosp -> "aosp"
                        SystemImageSource.AospTablet -> "aosp_tablet"
                        SystemImageSource.AospAtd -> "aosp_atd"
                        SystemImageSource.Google -> "google"
                        SystemImageSource.GoogleTablet -> "google_apis_tablet"
                        SystemImageSource.GoogleAtd -> "google_atd"
                        SystemImageSource.GooglePlayStore -> "google_apis_playstore"
                        SystemImageSource.GooglePlayStoreTablet -> "google_playstore_tablet"
                        SystemImageSource.AndroidDesktop -> "android-desktop"
                        SystemImageSource.AndroidWear -> "android-wear"
                    }
                }
            }
    }
}

private val phoneDevices = run {
    val deviceNames = enumValues<AndroidDevice.PhoneDevice>().toList()
    val apiLevels = 21..35
    val systemImageSources = listOf(
        SystemImageSource.Aosp,
        SystemImageSource.AospAtd,
        SystemImageSource.Google,
        SystemImageSource.GoogleAtd,
        SystemImageSource.GooglePlayStore,
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
            it.systemImageSource == SystemImageSource.GoogleAtd && it.apiLevel !in 30..34
        }
}

private val tabletDevices = run {
    val deviceNames =
        enumValues<AndroidDevice.TabletDevice>().toList()
    val apiLevels = 21..35
    val systemImageSources = listOf(
        SystemImageSource.Aosp,
        SystemImageSource.AospTablet,
        SystemImageSource.AospAtd,
        SystemImageSource.Google,
        SystemImageSource.GoogleTablet,
        SystemImageSource.GoogleAtd,
        SystemImageSource.GooglePlayStore,
        SystemImageSource.GooglePlayStoreTablet,
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
            // aosp tablet images are only supported on some versions
            it.systemImageSource == SystemImageSource.AospTablet && it.apiLevel != 34
        }
        .filterNot {
            // google tablet images are only supported on some versions
            it.systemImageSource == SystemImageSource.AospTablet && it.apiLevel !in 34..35
        }
}

private val desktopDevices = run {
    val deviceNames = enumValues<AndroidDevice.DesktopDevice>().toList()
    val apiLevels = 32..34
    val systemImageSources = listOf(
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
}

private val mobileDevices = phoneDevices + tabletDevices + desktopDevices

private val wearDevices = run {
    val deviceNames = enumValues<AndroidDevice.WearDevice>()
    val apiLevels = setOf(28, 30, 33, 34)
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
