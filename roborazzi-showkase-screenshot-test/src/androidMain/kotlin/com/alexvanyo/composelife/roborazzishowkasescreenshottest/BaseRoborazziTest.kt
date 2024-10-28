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

package com.alexvanyo.composelife.roborazzishowkasescreenshottest

import androidx.activity.OnBackPressedDispatcher
import androidx.activity.OnBackPressedDispatcherOwner
import androidx.activity.compose.LocalOnBackPressedDispatcherOwner
import androidx.annotation.RequiresApi
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
import androidx.compose.ui.test.RoundScreen
import androidx.compose.ui.test.onNodeWithTag
import androidx.compose.ui.test.runComposeUiTest
import androidx.compose.ui.test.then
import androidx.compose.ui.unit.DpSize
import androidx.lifecycle.compose.LocalLifecycleOwner
import androidx.test.platform.graphics.HardwareRendererCompat
import com.airbnb.android.showkase.models.ShowkaseBrowserComponent
import com.github.takahirom.roborazzi.captureRoboImage
import com.google.testing.junit.testparameterinjector.TestParameter
import com.google.testing.junit.testparameterinjector.TestParameterValuesProvider
import org.junit.runner.RunWith
import org.robolectric.RobolectricTestParameterInjector
import org.robolectric.annotation.Config
import java.io.File
import kotlin.properties.Delegates
import kotlin.test.AfterTest
import kotlin.test.BeforeTest
import kotlin.test.Test

/**
 * A base test class for running screenshot tests over a parameterization of components and other configurations.
 *
 * The full list of parameterizations should be given in [parameterizations], and also used as part of a
 * [TestParameterValuesProvider] passed as a [TestParameter.valuesProvider] for [roborazziParameterization].
 *
 * If specified, [contentWrapper] will wrap
 */
@OptIn(ExperimentalTestApi::class)
@RunWith(RobolectricTestParameterInjector::class)
@Config(
    qualifiers = "w1280dp-h1280dp",
    sdk = [34],
)
abstract class BaseRoborazziTest(
    private val roborazziParameterization: RoborazziParameterization,
    private val contentWrapper: @Composable (content: @Composable () -> Unit) -> Unit = { content -> content() },
) {
    abstract val parameterizations: List<SingleRoborazziParameterization>

    private var wasDrawingEnabled by Delegates.notNull<Boolean>()

    @BeforeTest
    fun setup() {
        System.setProperty("robolectric.pixelCopyRenderMode", "hardware")
        wasDrawingEnabled = HardwareRendererCompat.isDrawingEnabled()
        HardwareRendererCompat.setDrawingEnabled(true)
    }

    @AfterTest
    fun teardown() {
        HardwareRendererCompat.setDrawingEnabled(wasDrawingEnabled)
    }

    @RequiresApi(23)
    @Test
    fun previewScreenshotTest() = runComposeUiTest {
        val testParameterizations = when (roborazziParameterization) {
            CombinedRoborazziParameterization -> parameterizations
            is SingleRoborazziParameterization -> listOf(roborazziParameterization)
        }

        var currentParameterization by mutableStateOf(testParameterizations.first())

        setContent {
            val lifecycleOwner = LocalLifecycleOwner.current
            DeviceConfigurationOverride(
                DeviceConfigurationOverride.DarkMode(currentParameterization.darkTheme)
                    then DeviceConfigurationOverride.FontScale(currentParameterization.fontScale)
                    then DeviceConfigurationOverride.RoundScreen(currentParameterization.isScreenRound),
            ) {
                CompositionLocalProvider(
                    LocalInspectionMode provides true,
                    // Provide a fake OnBackPressedDispatcherOwner
                    LocalOnBackPressedDispatcherOwner provides object : OnBackPressedDispatcherOwner {
                        override val onBackPressedDispatcher = OnBackPressedDispatcher()

                        override val lifecycle = lifecycleOwner.lifecycle
                    },
                ) {
                    contentWrapper {
                        Box(
                            modifier = Modifier.size(currentParameterization.size),
                        ) {
                            Box(
                                modifier = Modifier.testTag("contentContainer"),
                            ) {
                                key(currentParameterization) {
                                    currentParameterization.showkaseBrowserComponent.component()
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
            val semanticsNodeInteraction = onNodeWithTag("contentContainer")
            semanticsNodeInteraction.captureRoboImage(
                file = File(
                    "src/androidUnitTest/snapshots",
                    "${parameterization.showkaseBrowserComponent.componentKey}." +
                        "${parameterization.size}." +
                        "${ if (parameterization.darkTheme) "dark" else "light" }." +
                        "${ if (parameterization.isScreenRound) "round" else "notRound" }." +
                        "font-${parameterization.fontScale}." +
                        "png",
                ),
            )
        }
    }
}

open class BaseRoborazziParameterizationProvider(
    val parameterizations: List<SingleRoborazziParameterization>,
) : TestParameterValuesProvider() {
    public final override fun provideValues(context: Context): List<RoborazziParameterization> =
        // Check if we want to provide parameterization at the test level
        // This makes it easier to debug which test is failing, at the cost of speed
        if (System.getProperty("com.alexvanyo.composelife.combinedScreenshotTests").toBoolean()) {
            listOf(CombinedRoborazziParameterization)
        } else {
            parameterizations
        }
}

sealed interface RoborazziParameterization

/**
 * A single, specific parameterization to run screenshot tests on.
 *
 * The argument for the [RobolectricTestParameterInjector] indicating that we should perform the test for this
 * particular parameterization.
 */
data class SingleRoborazziParameterization(
    /**
     * The component to render.
     */
    val showkaseBrowserComponent: ShowkaseBrowserComponent,
    /**
     * The size to render the component at.
     */
    val size: DpSize,
    /**
     * True if the component should be rendered in dark theme.
     */
    val darkTheme: Boolean,
    /**
     * True if the component should be rendered on a round screen.
     */
    val isScreenRound: Boolean,
    /**
     * The font scale to render the component at.
     */
    val fontScale: Float,
) : RoborazziParameterization

/**
 * The argument for the [RobolectricTestParameterInjector] indicating that we should perform parameterization
 * within a single test.
 */
data object CombinedRoborazziParameterization : RoborazziParameterization
