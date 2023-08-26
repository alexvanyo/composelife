/*
 * Copyright 2023 The Android Open Source Project
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

package com.alexvanyo.composelife.ui.wear.util

import androidx.activity.ComponentActivity
import androidx.activity.OnBackPressedDispatcher
import androidx.activity.OnBackPressedDispatcherOwner
import androidx.activity.compose.LocalOnBackPressedDispatcherOwner
import androidx.compose.foundation.layout.Box
import androidx.compose.runtime.Composable
import androidx.compose.runtime.CompositionLocalProvider
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.platform.LocalInspectionMode
import androidx.compose.ui.platform.LocalLifecycleOwner
import androidx.compose.ui.test.junit4.createAndroidComposeRule
import androidx.compose.ui.unit.Density
import com.alexvanyo.composelife.ui.wear.theme.ComposeLifeTheme
import com.github.takahirom.roborazzi.RobolectricDeviceQualifiers
import com.github.takahirom.roborazzi.RoborazziRule
import com.github.takahirom.roborazzi.captureRoboImage
import org.junit.Rule
import org.junit.runner.Description
import org.junit.runner.RunWith
import org.robolectric.ParameterizedRobolectricTestRunner
import org.robolectric.RuntimeEnvironment
import java.io.File

@RunWith(ParameterizedRobolectricTestRunner::class)
@Suppress("UnnecessaryAbstractClass")
abstract class BaseRoborazziTest(
    private val deviceName: String,
    private val deviceQualifiers: String,
    private val fontScale: Float,
) {
    @get:Rule
    val composeTestRule = createAndroidComposeRule<ComponentActivity>()

    @get:Rule
    val roborazziRule = RoborazziRule(
        options = RoborazziRule.Options(
            outputDirectoryPath = "src/androidUnitTest/snapshots",
            outputFileProvider = { description: Description, outputDirectory: File, fileExtension: String ->
                File(
                    outputDirectory,
                    "${description.testClass.name}." +
                        "${description.methodName.takeWhile { it != '[' }}." +
                        "$deviceName." +
                        "font-$fontScale." +
                        fileExtension,
                )
            },
        ),
    )

    fun snapshot(composable: @Composable () -> Unit) {
        RuntimeEnvironment.setQualifiers(deviceQualifiers)

        captureRoboImage {
            val lifecycleOwner = LocalLifecycleOwner.current
            CompositionLocalProvider(
                LocalInspectionMode provides true,
                LocalDensity provides Density(
                    density = LocalDensity.current.density,
                    fontScale = fontScale,
                ),
                // Provide a fake OnBackPressedDispatcherOwner
                LocalOnBackPressedDispatcherOwner provides object : OnBackPressedDispatcherOwner {
                    override val onBackPressedDispatcher = OnBackPressedDispatcher()

                    override val lifecycle = lifecycleOwner.lifecycle
                },
            ) {
                ComposeLifeTheme {
                    Box {
                        composable()
                    }
                }
            }
        }
    }

    companion object {

        @JvmStatic
        @ParameterizedRobolectricTestRunner.Parameters
        fun data() = listOf(
            "WearOSSmallRound" to RobolectricDeviceQualifiers.WearOSSmallRound,
            "WearOSSquare" to RobolectricDeviceQualifiers.WearOSSquare,
        ).flatMap { (deviceName, deviceQualifiers) ->
            listOf(1.0f, 1.5f).map { fontScale ->
                arrayOf(
                    deviceName,
                    deviceQualifiers,
                    fontScale,
                )
            }
        }
    }
}
