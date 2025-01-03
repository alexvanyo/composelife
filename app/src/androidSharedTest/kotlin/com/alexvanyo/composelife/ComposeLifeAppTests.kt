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

package com.alexvanyo.composelife

import android.app.Activity
import android.content.ClipData
import android.content.ClipboardManager
import androidx.compose.ui.graphics.toComposeRect
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.assertHasClickAction
import androidx.compose.ui.test.assertIsDisplayed
import androidx.compose.ui.test.assertIsSelected
import androidx.compose.ui.test.hasAnyAncestor
import androidx.compose.ui.test.hasContentDescription
import androidx.compose.ui.test.hasTestTag
import androidx.compose.ui.test.hasText
import androidx.compose.ui.test.isDialog
import androidx.compose.ui.test.isPopup
import androidx.compose.ui.test.onNodeWithContentDescription
import androidx.compose.ui.test.onNodeWithText
import androidx.compose.ui.test.performClick
import androidx.compose.ui.test.performScrollTo
import androidx.compose.ui.unit.Density
import androidx.core.content.getSystemService
import androidx.test.core.app.ActivityScenario
import androidx.test.espresso.Espresso
import androidx.window.core.layout.WindowSizeClass
import androidx.window.core.layout.WindowSizeClass.Companion.BREAKPOINTS_V1
import androidx.window.core.layout.computeWindowSizeClass
import androidx.window.layout.WindowMetricsCalculator
import com.alexvanyo.composelife.preferences.AlgorithmType
import com.alexvanyo.composelife.preferences.DarkThemeConfig
import com.alexvanyo.composelife.preferences.QuickAccessSetting
import com.alexvanyo.composelife.preferences.algorithmChoiceState
import com.alexvanyo.composelife.preferences.darkThemeConfigState
import com.alexvanyo.composelife.preferences.quickAccessSettingsState
import com.alexvanyo.composelife.resourcestate.ResourceState
import com.alexvanyo.composelife.test.BaseActivityInjectTest
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.test.runCurrent
import leakcanary.SkipLeakDetection
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotNull
import com.alexvanyo.composelife.ui.app.R as uiAppR
import com.alexvanyo.composelife.ui.settings.R as uiSettingsR

class ComposeLifeAppTests : BaseActivityInjectTest<TestComposeLifeApplicationComponent, MainActivity>(
    { TestComposeLifeApplicationComponent.createComponent() },
    MainActivity::class.java,
) {
    private val testDispatcher get() = applicationComponent.generalTestDispatcher

    private val preferences get() = applicationComponent.composeLifePreferences

    @SkipLeakDetection("recomposer", "Outer")
    @Test
    fun app_does_not_crash() = runAppTest(testDispatcher) {
        composeTestRule.onNodeWithContentDescription(context.getString(uiAppR.string.play)).performClick()

        composeTestRule.onNodeWithContentDescription(context.getString(uiAppR.string.pause)).performClick()

        composeTestRule.waitForIdle()
    }

    @SkipLeakDetection("recomposer", "Outer", "Inner")
    @Test
    fun app_does_not_crash_when_recreating() = runAppTest(testDispatcher) {
        composeTestRule.onNodeWithContentDescription(context.getString(uiAppR.string.play)).performClick()

        composeTestRule.onNodeWithContentDescription(context.getString(uiAppR.string.pause)).performClick()

        composeTestRule.activityRule.scenario.recreate()

        composeTestRule.waitForIdle()
    }

    @SkipLeakDetection("recomposer", "Outer", "Inner")
    @Test
    fun can_change_theme_to_dark_mode() = runAppTest(testDispatcher) {
        val windowSizeClass =
            composeTestRule.activityRule.scenario.withActivity {
                val dpSize = with(Density(this)) {
                    WindowMetricsCalculator.getOrCreate()
                        .computeCurrentWindowMetrics(this@withActivity)
                        .bounds
                        .toComposeRect()
                        .size
                        .toDpSize()
                }

                BREAKPOINTS_V1.computeWindowSizeClass(
                    widthDp = dpSize.width.value,
                    heightDp = dpSize.height.value,
                )
            }

        composeTestRule
            .onNode(
                hasAnyAncestor(hasTestTag("CellUniverseActionCard")) and
                    hasContentDescription(context.getString(uiAppR.string.expand)),
            )
            .performClick()

        composeTestRule
            .onNodeWithText(context.getString(uiAppR.string.settings))
            .performClick()

        composeTestRule
            .onNodeWithText(context.getString(uiAppR.string.settings))
            .assertIsSelected()

        composeTestRule
            .onNodeWithText(context.getString(uiSettingsR.string.see_all))
            .performClick()

        composeTestRule
            .onNodeWithText(context.getString(uiSettingsR.string.visual))
            .performClick()

        composeTestRule
            .onNodeWithText(context.getString(uiSettingsR.string.dark_theme_config))
            .performClick()

        composeTestRule
            .onNode(hasAnyAncestor(isPopup()) and hasText(context.getString(uiSettingsR.string.dark_theme)))
            .assertHasClickAction()
            .performClick()

        composeTestRule
            .onNode(isPopup())
            .assertDoesNotExist()

        assertEquals(ResourceState.Success(DarkThemeConfig.Dark), preferences.darkThemeConfigState)

        if (!windowSizeClass.isWidthAtLeastBreakpoint(WindowSizeClass.WIDTH_DP_MEDIUM_LOWER_BOUND)) {
            composeTestRule
                .onNodeWithContentDescription(context.getString(uiAppR.string.back))
                .performClick()
        }

        composeTestRule
            .onNodeWithContentDescription(context.getString(uiAppR.string.back))
            .performClick()

        composeTestRule
            .onNodeWithText(context.getString(uiAppR.string.settings))
            .assertIsSelected()

        Espresso.pressBack()

        composeTestRule
            .onNodeWithText(context.getString(uiAppR.string.speed))
            .assertIsSelected()

        Espresso.pressBack()

        composeTestRule
            .onNode(
                hasAnyAncestor(hasTestTag("CellUniverseActionCard")) and
                    hasContentDescription(context.getString(uiAppR.string.expand)),
            )
            .assertExists()
    }

    @SkipLeakDetection("recomposer", "Outer", "Inner")
    @Test
    fun can_save_theme_to_quick_access() = runAppTest(testDispatcher) {
        val windowSizeClass =
            composeTestRule.activityRule.scenario.withActivity {
                val dpSize = with(Density(this)) {
                    WindowMetricsCalculator.getOrCreate()
                        .computeCurrentWindowMetrics(this@withActivity)
                        .bounds
                        .toComposeRect()
                        .size
                        .toDpSize()
                }

                BREAKPOINTS_V1.computeWindowSizeClass(
                    widthDp = dpSize.width.value,
                    heightDp = dpSize.height.value,
                )
            }

        composeTestRule
            .onNode(
                hasAnyAncestor(hasTestTag("CellUniverseActionCard")) and
                    hasContentDescription(context.getString(uiAppR.string.expand)),
            )
            .performClick()

        composeTestRule
            .onNodeWithText(context.getString(uiAppR.string.settings))
            .performClick()

        composeTestRule
            .onNodeWithText(context.getString(uiAppR.string.settings))
            .assertIsSelected()

        composeTestRule
            .onNodeWithText(context.getString(uiSettingsR.string.see_all))
            .performClick()

        composeTestRule
            .onNodeWithText(context.getString(uiSettingsR.string.visual))
            .performClick()

        composeTestRule
            .onNode(
                hasAnyAncestor(hasTestTag("SettingUi:Setting_DarkThemeConfig")) and
                    hasContentDescription(context.getString(uiSettingsR.string.add_setting_to_quick_access)),
            )
            .performScrollTo()
            .performClick()

        assertEquals(
            ResourceState.Success(setOf(QuickAccessSetting.DarkThemeConfig)),
            preferences.quickAccessSettingsState,
        )

        if (!windowSizeClass.isWidthAtLeastBreakpoint(WindowSizeClass.WIDTH_DP_MEDIUM_LOWER_BOUND)) {
            composeTestRule
                .onNodeWithContentDescription(context.getString(uiAppR.string.back))
                .performClick()
        }

        composeTestRule
            .onNodeWithContentDescription(context.getString(uiAppR.string.back))
            .performClick()

        composeTestRule
            .onNodeWithText(context.getString(uiAppR.string.settings))
            .assertIsSelected()

        composeTestRule
            .onNodeWithText(context.getString(uiSettingsR.string.dark_theme_config))
            .performClick()

        composeTestRule
            .onNode(hasAnyAncestor(isPopup()) and hasText(context.getString(uiSettingsR.string.dark_theme)))
            .assertHasClickAction()
            .performClick()

        composeTestRule
            .onNode(isPopup())
            .assertDoesNotExist()

        assertEquals(ResourceState.Success(DarkThemeConfig.Dark), preferences.darkThemeConfigState)

        composeTestRule
            .onNode(
                hasAnyAncestor(hasTestTag("SettingUi:Setting_DarkThemeConfig")) and
                    hasContentDescription(context.getString(uiSettingsR.string.open_in_settings)),
            )
            .performScrollTo()
            .performClick()

        composeTestRule
            .onNodeWithText(context.getString(uiSettingsR.string.visual))
            .assertIsDisplayed()

        if (!windowSizeClass.isWidthAtLeastBreakpoint(WindowSizeClass.WIDTH_DP_MEDIUM_LOWER_BOUND)) {
            composeTestRule
                .onNodeWithContentDescription(context.getString(uiAppR.string.back))
                .performClick()
        }

        composeTestRule
            .onNodeWithContentDescription(context.getString(uiAppR.string.back))
            .performClick()

        composeTestRule
            .onNodeWithText(context.getString(uiAppR.string.settings))
            .assertIsSelected()

        Espresso.pressBack()

        composeTestRule
            .onNodeWithText(context.getString(uiAppR.string.speed))
            .assertIsSelected()

        Espresso.pressBack()

        composeTestRule
            .onNode(
                hasAnyAncestor(hasTestTag("CellUniverseActionCard")) and
                    hasContentDescription(context.getString(uiAppR.string.expand)),
            )
            .assertExists()
    }

    @SkipLeakDetection("recomposer", "Outer", "Inner")
    @Test
    fun can_change_algorithm_implementation_to_naive() = runAppTest(testDispatcher) {
        val windowSizeClass =
            composeTestRule.activityRule.scenario.withActivity {
                val dpSize = with(Density(this)) {
                    WindowMetricsCalculator.getOrCreate()
                        .computeCurrentWindowMetrics(this@withActivity)
                        .bounds
                        .toComposeRect()
                        .size
                        .toDpSize()
                }

                BREAKPOINTS_V1.computeWindowSizeClass(
                    widthDp = dpSize.width.value,
                    heightDp = dpSize.height.value,
                )
            }

        composeTestRule
            .onNode(
                hasAnyAncestor(hasTestTag("CellUniverseActionCard")) and
                    hasContentDescription(context.getString(uiAppR.string.expand)),
            )
            .performClick()

        composeTestRule
            .onNodeWithText(context.getString(uiAppR.string.settings))
            .performClick()

        composeTestRule
            .onNodeWithText(context.getString(uiAppR.string.settings))
            .assertIsSelected()

        composeTestRule
            .onNodeWithText(context.getString(uiSettingsR.string.see_all))
            .performClick()

        composeTestRule
            .onNodeWithText(context.getString(uiSettingsR.string.algorithm))
            .performClick()

        composeTestRule
            .onNodeWithText(context.getString(uiSettingsR.string.algorithm_implementation))
            .performClick()

        composeTestRule
            .onNode(hasAnyAncestor(isPopup()) and hasText(context.getString(uiSettingsR.string.naive_algorithm)))
            .assertHasClickAction()
            .performClick()

        composeTestRule
            .onNode(isPopup())
            .assertDoesNotExist()

        assertEquals(ResourceState.Success(AlgorithmType.NaiveAlgorithm), preferences.algorithmChoiceState)

        if (!windowSizeClass.isWidthAtLeastBreakpoint(WindowSizeClass.WIDTH_DP_MEDIUM_LOWER_BOUND)) {
            Espresso.pressBack()
            composeTestRule.waitForIdle()
        }

        Espresso.pressBack()

        composeTestRule
            .onNodeWithText(context.getString(uiAppR.string.settings))
            .assertIsSelected()

        Espresso.pressBack()

        composeTestRule
            .onNodeWithText(context.getString(uiAppR.string.speed))
            .assertIsSelected()

        Espresso.pressBack()

        composeTestRule
            .onNode(
                hasAnyAncestor(hasTestTag("CellUniverseActionCard")) and
                    hasContentDescription(context.getString(uiAppR.string.expand)),
            )
            .assertExists()
    }

    @OptIn(ExperimentalTestApi::class, ExperimentalCoroutinesApi::class)
    @SkipLeakDetection("recomposer", "Outer", "Inner")
    @Test
    fun can_watch_clipboard_and_view_deserialization_info() = runAppTest(testDispatcher) {
        val windowSizeClass =
            composeTestRule.activityRule.scenario.withActivity {
                val dpSize = with(Density(this)) {
                    WindowMetricsCalculator.getOrCreate()
                        .computeCurrentWindowMetrics(this@withActivity)
                        .bounds
                        .toComposeRect()
                        .size
                        .toDpSize()
                }

                BREAKPOINTS_V1.computeWindowSizeClass(
                    widthDp = dpSize.width.value,
                    heightDp = dpSize.height.value,
                )
            }

        val clipboardManager = context.getSystemService<ClipboardManager>()
        assertNotNull(clipboardManager)
        clipboardManager.setPrimaryClip(
            ClipData.newPlainText("test", ".X.\n..X\nXXX"),
        )

        composeTestRule
            .onNode(
                hasAnyAncestor(hasTestTag("CellUniverseActionCard")) and
                    hasContentDescription(context.getString(uiAppR.string.expand)),
            )
            .performClick()

        composeTestRule
            .onNodeWithText(context.getString(uiAppR.string.edit))
            .performClick()

        composeTestRule
            .onNodeWithText(context.getString(uiAppR.string.edit))
            .assertIsSelected()

        composeTestRule
            .onNodeWithText(context.getString(uiAppR.string.allow))
            .performClick()

        composeTestRule.waitForIdle()
        runCurrent()

        composeTestRule
            .onNodeWithContentDescription(context.getString(uiAppR.string.warnings))
            .performClick()

        if (
            windowSizeClass.isWidthAtLeastBreakpoint(WindowSizeClass.WIDTH_DP_MEDIUM_LOWER_BOUND) ||
            windowSizeClass.isHeightAtLeastBreakpoint(WindowSizeClass.HEIGHT_DP_MEDIUM_LOWER_BOUND)
        ) {
            composeTestRule
                .onNode(isDialog())
                .assertExists()
        } else {
            composeTestRule
                .onNode(isDialog())
                .assertDoesNotExist()
        }

        composeTestRule
            .onNodeWithText(context.getString(uiAppR.string.deserialization_succeeded))
            .performClick()

        Espresso.pressBack()

        composeTestRule
            .onNodeWithText(context.getString(uiAppR.string.deserialization_succeeded))
            .assertDoesNotExist()
        composeTestRule
            .onNode(isDialog())
            .assertDoesNotExist()
    }
}

private inline fun <reified A : Activity, T : Any> ActivityScenario<A>.withActivity(
    crossinline block: A.() -> T,
): T {
    var result: Result<T>? = null
    onActivity { activity ->
        result = kotlin.runCatching {
            block(activity)
        }
    }
    @Suppress("UnsafeCallOnNullableType")
    return result!!.getOrThrow()
}
