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

package com.alexvanyo.composelife.ui.app.util

import androidx.activity.OnBackPressedDispatcher
import androidx.activity.OnBackPressedDispatcherOwner
import androidx.activity.compose.LocalOnBackPressedDispatcherOwner
import androidx.compose.foundation.isSystemInDarkTheme
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.size
import androidx.compose.runtime.Composable
import androidx.compose.runtime.CompositionLocalProvider
import androidx.compose.runtime.getValue
import androidx.compose.runtime.key
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.setValue
import androidx.compose.ui.Modifier
import androidx.compose.ui.platform.LocalInspectionMode
import androidx.compose.ui.platform.testTag
import androidx.compose.ui.test.DarkMode
import androidx.compose.ui.test.DeviceConfigurationOverride
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.FontScale
import androidx.compose.ui.test.onNodeWithTag
import androidx.compose.ui.test.runComposeUiTest
import androidx.compose.ui.test.then
import androidx.compose.ui.unit.DpSize
import androidx.compose.ui.unit.dp
import androidx.lifecycle.compose.LocalLifecycleOwner
import androidx.test.platform.graphics.HardwareRendererCompat
import com.alexvanyo.composelife.ui.app.theme.ComposeLifeTheme
import com.github.takahirom.roborazzi.captureRoboImage
import org.junit.Rule
import org.junit.rules.TestWatcher
import org.junit.runner.Description
import org.junit.runner.RunWith
import org.robolectric.ParameterizedRobolectricTestRunner
import org.robolectric.annotation.Config
import java.io.File
import kotlin.properties.Delegates
import kotlin.test.AfterTest
import kotlin.test.BeforeTest

@OptIn(ExperimentalTestApi::class)
@RunWith(ParameterizedRobolectricTestRunner::class)
@Suppress("UnnecessaryAbstractClass")
@Config(qualifiers = "w1280dp-h1280dp")
abstract class BaseRoborazziTest(
    private val roborazziParameterization: RoborazziParameterization,
) {
    lateinit var description: Description

    private var wasDrawingEnabled by Delegates.notNull<Boolean>()

    @get:Rule
    val watcher = object : TestWatcher() {
        override fun starting(description: Description) {
            super.starting(description)
            this@BaseRoborazziTest.description = description
        }
    }

    @BeforeTest
    fun setup() {
        System.setProperty("robolectric.screenshot.hwrdr.native", "true")
        wasDrawingEnabled = HardwareRendererCompat.isDrawingEnabled()
        HardwareRendererCompat.setDrawingEnabled(true)
    }

    @AfterTest
    fun teardown() {
        HardwareRendererCompat.setDrawingEnabled(wasDrawingEnabled)
    }

    fun snapshot(composable: @Composable () -> Unit) = runComposeUiTest {
        val testParameterizations = when (roborazziParameterization) {
            CombinedRoborazziParameterization -> parameterizations
            is SingleRoborazziParameterization -> listOf(roborazziParameterization)
        }

        var currentParameterization by mutableStateOf(testParameterizations.first())

        setContent {
            val lifecycleOwner = LocalLifecycleOwner.current
            DeviceConfigurationOverride(
                DeviceConfigurationOverride.DarkMode(currentParameterization.darkTheme)
                    then DeviceConfigurationOverride.FontScale(currentParameterization.fontScale),
            ) {
                CompositionLocalProvider(
                    LocalInspectionMode provides true,
                    // Provide a fake OnBackPressedDispatcherOwner
                    LocalOnBackPressedDispatcherOwner provides object : OnBackPressedDispatcherOwner {
                        override val onBackPressedDispatcher = OnBackPressedDispatcher()

                        override val lifecycle = lifecycleOwner.lifecycle
                    },
                ) {
                    ComposeLifeTheme(darkTheme = isSystemInDarkTheme()) {
                        Box(
                            modifier = Modifier.size(currentParameterization.size),
                        ) {
                            Box(
                                modifier = Modifier.testTag("contentContainer"),
                            ) {
                                key(currentParameterization) {
                                    composable()
                                }
                            }
                        }
                    }
                }
            }
        }

        testParameterizations.forEach { parameterization ->
            currentParameterization = parameterization

            waitForIdle()
            onNodeWithTag("contentContainer").captureRoboImage(
                file = File(
                    "src/androidUnitTest/snapshots",
                    "${description.testClass.name}." +
                        "${description.methodName.takeWhile { it != '[' }}." +
                        "${parameterization.size}." +
                        "${ if (parameterization.darkTheme) "dark" else "light" }." +
                        "font-${parameterization.fontScale}." +
                        "png",
                ),
            )
        }
    }

    companion object {

        @JvmStatic
        @ParameterizedRobolectricTestRunner.Parameters
        fun data() =
            // Check if we want to provide parameterization at the test level
            // This makes it easier to debug which test is failing, at the cost of speed
            if (System.getProperty("com.alexvanyo.composelife.combinedScreenshotTests").toBoolean()) {
                listOf(arrayOf(CombinedRoborazziParameterization))
            } else {
                parameterizations.map {
                    arrayOf(it)
                }
            }

        /**
         * The underlying parameterizations we want to test.
         *
         * This will either be done via test runner level parameterization, or in-test parameterization, depending
         * on the environment value determined in [data].
         */
        val parameterizations = listOf(
            DpSize(320.dp, 533.dp), // Nexus One portrait
            DpSize(393.dp, 851.dp), // Pixel 5 portrait
            DpSize(1200.dp, 800.dp), // Pixel Tablet landscape
        ).flatMap { size ->
            listOf(false, true).flatMap { darkTheme ->
                listOf(1.0f, 1.5f).map { fontScale ->
                    SingleRoborazziParameterization(
                        size = size,
                        darkTheme = darkTheme,
                        fontScale = fontScale,
                    )
                }
            }
        }
    }
}

sealed interface RoborazziParameterization

/**
 * A single, specific parameterization to run screenshot tests on.
 *
 * The argument for the [ParameterizedRobolectricTestRunner] indicating that we should perform the test for this
 * particular parameterization.
 */
data class SingleRoborazziParameterization(
    val size: DpSize,
    val darkTheme: Boolean,
    val fontScale: Float,
) : RoborazziParameterization

/**
 * The argument for the [ParameterizedRobolectricTestRunner] indicating that we should perform parameterization
 * within a single test.
 */
data object CombinedRoborazziParameterization : RoborazziParameterization
