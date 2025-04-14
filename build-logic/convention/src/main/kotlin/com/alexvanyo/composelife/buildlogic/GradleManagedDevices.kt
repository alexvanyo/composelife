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
// TODO: https://github.com/gradle/gradle/issues/7735
@file:Suppress("InternalAgpApiUsage", "InternalGradleApiUsage")

package com.alexvanyo.composelife.buildlogic

import com.android.build.api.dsl.CommonExtension
import com.android.build.api.dsl.ManagedVirtualDevice
import com.android.build.gradle.internal.tasks.ManagedDeviceInstrumentationTestSetupTask
import com.android.build.gradle.internal.tasks.ManagedDeviceInstrumentationTestTask
import org.gradle.api.DefaultTask
import org.gradle.api.Project
import org.gradle.api.provider.Property
import org.gradle.api.services.BuildService
import org.gradle.api.services.BuildServiceParameters
import org.gradle.api.tasks.Input
import org.gradle.api.tasks.TaskAction
import org.gradle.internal.os.OperatingSystem
import org.gradle.kotlin.dsl.create
import org.gradle.kotlin.dsl.invoke
import org.gradle.kotlin.dsl.register
import org.gradle.kotlin.dsl.withType
import org.gradle.process.ExecOperations
import org.gradle.work.DisableCachingByDefault
import java.io.ByteArrayOutputStream
import java.nio.charset.Charset
import javax.inject.Inject

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
        Pixel9Pro,
        Pixel9ProFold,
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

@Suppress("CyclomaticComplexMethod", "LongMethod")
@JvmName("configureGradleManagedDevicesDeviceConfig")
fun Project.configureGradleManagedDevices(
    devices: Set<GradleManagedDeviceConfig>,
    commonExtension: CommonExtension<*, *, *, *, *, *>,
    filterForTests: Boolean = true,
) {
    commonExtension.testOptions.managedDevices.allDevices {
        devices
            .filter { config ->
                !filterForTests ||
                    providers
                        .gradleProperty("com.alexvanyo.composelife.enabledGradleManagedDevices")
                        .map { config.taskPrefix in it.split(",") }
                        .orElse(true)
                        .get()
            }
            .filter { config ->
                // Filter out incompatible devices based on API level
                val minSdk = commonExtension.defaultConfig.minSdk
                minSdk == null || config.apiLevel >= minSdk
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
                        AndroidDevice.PhoneDevice.Pixel9Pro -> "Pixel 9 Pro"
                        AndroidDevice.PhoneDevice.Pixel9ProFold -> "Pixel 9 Pro Fold"
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

                // Create a limiting build service to only allow one setup task for each device configuration to run
                // at a time
                gradle.sharedServices.registerIfAbsent(
                    LimitingBuildServiceGMDSetup.createKey(config),
                    LimitingBuildServiceGMDSetup::class.java,
                ) {
                    maxParallelUsages.set(1)
                }
            }
    }

    if (OperatingSystem.current().isLinux) {
        tasks.withType<ManagedDeviceInstrumentationTestTask> {
            val id = path
            // Manually kill the qemu process associated with this test task to reclaim resources
            finalizedBy(
                tasks.register<KillEmulatorProcessesTask>("${name}KillEmulatorProcesses") {
                    this.id.set(id)
                },
            )
        }
    }

    // Create a limiting build service to only allow an maxConcurrentDevices amount of test tasks to run at a time
    val runningLimitingService = gradle.sharedServices.registerIfAbsent(
        LimitingBuildServiceGMDRunning.KEY,
        LimitingBuildServiceGMDRunning::class.java,
    ) {
        maxParallelUsages.set(
            providers.gradleProperty("android.experimental.testOptions.managedDevices.maxConcurrentDevices")
                .map { value -> value.toIntOrNull() ?: 1 },
        )
    }
    tasks.withType<ManagedDeviceInstrumentationTestTask> {
        usesService(runningLimitingService)
    }
    tasks.withType<ManagedDeviceInstrumentationTestSetupTask> {
        usesService(
            gradle
                .sharedServices
                .registrations
                .getByName("LimitingBuildServiceGMDSetup${name.substringBefore("Setup")}")
                .service,
        )
    }
}

interface LimitingBuildServiceGMDRunning : BuildService<BuildServiceParameters.None> {
    companion object {
        const val KEY = "LimitingBuildServiceGMDRunning"
    }
}

interface LimitingBuildServiceGMDSetup : BuildService<BuildServiceParameters.None> {
    companion object {
        fun createKey(config: GradleManagedDeviceConfig): String = "LimitingBuildServiceGMDSetup${config.taskPrefix}"
    }
}

@DisableCachingByDefault
abstract class KillEmulatorProcessesTask : DefaultTask() {

    @get:Input
    abstract val id: Property<String>

    @get:Inject
    abstract val execOperations: ExecOperations

    @TaskAction
    fun taskAction() {
        val stream = ByteArrayOutputStream()
        // List all processes
        execOperations.exec {
            commandLine("ps", "-ax")
            standardOutput = stream
        }
        val emulatorPidsToKill = stream
            .toString(Charset.forName("UTF-8"))
            .lineSequence()
            // Find processes with the id that matches the path
            .filter { line -> line.contains(id.get()) }
            // Extract the process id
            .map { it.trim().split(Regex("""\s+""")).first() }
            .toList()
        emulatorPidsToKill.forEach { pid ->
            execOperations.exec {
                commandLine("kill", "-9", pid)
            }
        }
        logger.info("Killed qemu process(es) for ${id.get()}: $emulatorPidsToKill")
    }
}

private val phoneDevices = run {
    val deviceNames = enumValues<AndroidDevice.PhoneDevice>().toList()
    val apiLevels = 21..36
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
            // API 36 doesn't support non-Google images
            it.systemImageSource in setOf(SystemImageSource.Aosp, SystemImageSource.AospAtd) &&
                it.apiLevel == 36
        }
        .filterNot {
            // aosp-atd is only supported on some versions
            it.systemImageSource == SystemImageSource.AospAtd && it.apiLevel !in 30..35
        }
        .filterNot {
            // google-atd is only supported on some versions
            it.systemImageSource == SystemImageSource.GoogleAtd && it.apiLevel !in 30..35
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
    val apiLevels = setOf(28, 30, 33, 34, 35)
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
