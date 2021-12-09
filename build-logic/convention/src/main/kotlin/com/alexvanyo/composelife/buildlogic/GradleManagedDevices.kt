package com.alexvanyo.composelife.buildlogic

import com.android.build.gradle.TestedExtension
import org.gradle.api.Project
import org.gradle.kotlin.dsl.create
import org.gradle.kotlin.dsl.invoke

fun Project.configureGradleManagedDevices(
    testedExtension: TestedExtension
) {
    testedExtension.testOptions {
        val deviceNames = listOf("Pixel 2", "Pixel 3 XL")
        val apiLevels = listOf(29, 30)

        devices {
            deviceNames.forEach { deviceName ->
                apiLevels.forEach { apiLevel ->
                    create<com.android.build.api.dsl.ManagedVirtualDevice>(
                        "${deviceName}api$apiLevel"
                            .toLowerCaseAsciiOnly()
                            .replace(" ", "")
                    ) {
                        this.device = deviceName
                        this.apiLevel = apiLevel
                        this.systemImageSource = "google"
                        this.abi = "x86"
                    }
                }
            }
        }
    }
}

private fun String.toLowerCaseAsciiOnly(): String =
    buildString {
        for (c in this@toLowerCaseAsciiOnly) {
            append(if (c in 'a'..'z') c.toLowerCase() else c)
        }
    }
