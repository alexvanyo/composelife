package com.alexvanyo.composelife.buildlogic

import com.android.build.gradle.TestedExtension
import java.lang.Class
import java.lang.invoke.MethodHandles
import java.lang.reflect.Field
import java.lang.reflect.Modifier
import org.gradle.api.Project
import org.gradle.kotlin.dsl.create
import org.gradle.kotlin.dsl.invoke

fun Project.configureGradleManagedDevices(
    testedExtension: TestedExtension,
) {
    // TODO: A hacky reflection workaround to allow the emulators more time to boot
    //       https://cs.android.com/android-studio/platform/tools/base/+/mirror-goog-studio-main:build-system/gradle-core/src/main/java/com/android/build/gradle/internal/AvdSnapshotHandler.kt;l=183;drc=6592f6b20d81ab24d755eb68f852ac54c0046363
    try {
        val clazz = Class.forName("com.android.build.gradle.internal.AvdSnapshotHandlerKt")
        val field = clazz.getDeclaredField("DEVICE_BOOT_TIMEOUT_SEC")
        val lookup = MethodHandles.privateLookupIn(Field::class.java, MethodHandles.lookup())
        val handle = lookup.findVarHandle(Field::class.java, "modifiers", Int::class.java)
        field.isAccessible = true
        handle.set(field, field.modifiers and Modifier.FINAL.inv())

        field.set(null, 300L)
    } catch (illegalAccessException: IllegalAccessException) {
        // Do nothing
    }

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
            append(if (c in 'A'..'Z') c.toLowerCase() else c)
        }
    }
