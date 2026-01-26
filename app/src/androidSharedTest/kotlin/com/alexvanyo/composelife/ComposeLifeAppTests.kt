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
import androidx.test.espresso.Espresso
import androidx.window.core.layout.WindowSizeClass
import androidx.window.core.layout.WindowSizeClass.Companion.BREAKPOINTS_V1
import androidx.window.core.layout.computeWindowSizeClass
import androidx.window.layout.WindowMetricsCalculator
import com.alexvanyo.composelife.preferences.AlgorithmType
import com.alexvanyo.composelife.preferences.ComposeLifePreferences
import com.alexvanyo.composelife.preferences.DarkThemeConfig
import com.alexvanyo.composelife.preferences.QuickAccessSetting
import com.alexvanyo.composelife.preferences.algorithmChoiceState
import com.alexvanyo.composelife.preferences.darkThemeConfigState
import com.alexvanyo.composelife.preferences.quickAccessSettingsState
import com.alexvanyo.composelife.resourcestate.ResourceState
import com.alexvanyo.composelife.scopes.ApplicationGraph
import com.alexvanyo.composelife.test.BaseActivityInjectTest
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.asContribution
import kotlinx.coroutines.ExperimentalCoroutinesApi
import leakcanary.SkipLeakDetection
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotNull
import com.alexvanyo.composelife.ui.app.R as uiAppR
import com.alexvanyo.composelife.ui.settings.R as uiSettingsR

@ContributesTo(AppScope::class)
interface ComposeLifeAppTestsCtx {
    val preferences: ComposeLifePreferences
}

// TODO: Replace with asContribution()
internal val ApplicationGraph.composeLifeAppTestsCtx: ComposeLifeAppTestsCtx get() =
    this as ComposeLifeAppTestsCtx

@OptIn(ExperimentalTestApi::class)
class ComposeLifeAppTests : BaseActivityInjectTest<MainActivity>(
    { globalGraph.asContribution<ApplicationGraph.Factory>().create(it) },
    MainActivity::class.java,
) {
    private val ctx get() = applicationGraph.composeLifeAppTestsCtx

    private val preferences get() = ctx.preferences

    @SkipLeakDetection("recomposer", "Outer")
    @Test
    fun app_does_not_crash() = runUiTest {
        onNodeWithContentDescription(activity!!.getString(uiAppR.string.play)).performClick()

        onNodeWithContentDescription(activity!!.getString(uiAppR.string.pause)).performClick()

        waitForIdle()
    }

    @SkipLeakDetection("recomposer", "Outer")
    @Test
    fun app_does_not_crash_when_recreating() = runUiTest { scenario ->
        onNodeWithContentDescription(activity!!.getString(uiAppR.string.play)).performClick()

        onNodeWithContentDescription(activity!!.getString(uiAppR.string.pause)).performClick()

        scenario.recreate()

        waitForIdle()
    }

    @SkipLeakDetection("recomposer", "Outer")
    @Test
    fun can_change_theme_to_dark_mode() = runUiTest {
        val windowSizeClass =
            activity!!.run {
                val dpSize = with(Density(this)) {
                    WindowMetricsCalculator.getOrCreate()
                        .computeCurrentWindowMetrics(this@run)
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

        onNode(
            hasAnyAncestor(hasTestTag("CellUniverseActionCard")) and
                hasContentDescription(activity!!.getString(uiAppR.string.expand)),
        )
            .performClick()

        onNodeWithText(activity!!.getString(uiAppR.string.settings))
            .performClick()

        onNodeWithText(activity!!.getString(uiAppR.string.settings))
            .assertIsSelected()

        onNodeWithText(activity!!.getString(uiSettingsR.string.see_all))
            .performClick()

        onNodeWithText(activity!!.getString(uiSettingsR.string.visual))
            .performClick()

        onNodeWithText(activity!!.getString(uiSettingsR.string.dark_theme_config))
            .performClick()

        onNode(hasAnyAncestor(isPopup()) and hasText(activity!!.getString(uiSettingsR.string.dark_theme)))
            .assertHasClickAction()
            .performClick()

        onNode(hasAnyAncestor(isPopup()) and hasText(activity!!.getString(uiSettingsR.string.dark_theme)))
            .assertDoesNotExist()

        assertEquals(ResourceState.Success(DarkThemeConfig.Dark), preferences.darkThemeConfigState)

        if (!windowSizeClass.isWidthAtLeastBreakpoint(WindowSizeClass.WIDTH_DP_MEDIUM_LOWER_BOUND)) {
            onNodeWithContentDescription(activity!!.getString(uiAppR.string.back))
                .performClick()
        }

        onNodeWithContentDescription(activity!!.getString(uiAppR.string.back))
            .performClick()

        onNodeWithText(activity!!.getString(uiAppR.string.settings))
            .assertIsSelected()

        Espresso.pressBack()

        onNodeWithText(activity!!.getString(uiAppR.string.speed))
            .assertIsSelected()

        Espresso.pressBack()

        onNode(
            hasAnyAncestor(hasTestTag("CellUniverseActionCard")) and
                hasContentDescription(activity!!.getString(uiAppR.string.expand)),
        )
            .assertExists()
    }

    @SkipLeakDetection("recomposer", "Outer")
    @Test
    fun can_save_theme_to_quick_access() = runUiTest {
        val windowSizeClass =
            activity!!.run {
                val dpSize = with(Density(this)) {
                    WindowMetricsCalculator.getOrCreate()
                        .computeCurrentWindowMetrics(this@run)
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

        onNode(
            hasAnyAncestor(hasTestTag("CellUniverseActionCard")) and
                hasContentDescription(activity!!.getString(uiAppR.string.expand)),
        )
            .performClick()

        onNodeWithText(activity!!.getString(uiAppR.string.settings))
            .performClick()

        onNodeWithText(activity!!.getString(uiAppR.string.settings))
            .assertIsSelected()

        onNodeWithText(activity!!.getString(uiSettingsR.string.see_all))
            .performClick()

        onNodeWithText(activity!!.getString(uiSettingsR.string.visual))
            .performClick()

        onNode(
            hasAnyAncestor(hasTestTag("SettingUi:Setting_DarkThemeConfig")) and
                hasContentDescription(activity!!.getString(uiSettingsR.string.add_setting_to_quick_access)),
        )
            .performScrollTo()
            .performClick()

        assertEquals(
            ResourceState.Success(setOf(QuickAccessSetting.DarkThemeConfig)),
            preferences.quickAccessSettingsState,
        )

        if (!windowSizeClass.isWidthAtLeastBreakpoint(WindowSizeClass.WIDTH_DP_MEDIUM_LOWER_BOUND)) {
            onNodeWithContentDescription(activity!!.getString(uiAppR.string.back))
                .performClick()
        }

        onNodeWithContentDescription(activity!!.getString(uiAppR.string.back))
            .performClick()

        onNodeWithText(activity!!.getString(uiAppR.string.settings))
            .assertIsSelected()

        onNodeWithText(activity!!.getString(uiSettingsR.string.dark_theme_config))
            .performClick()

        onNode(hasAnyAncestor(isPopup()) and hasText(activity!!.getString(uiSettingsR.string.dark_theme)))
            .assertHasClickAction()
            .performClick()

        onNode(hasAnyAncestor(isPopup()) and hasText(activity!!.getString(uiSettingsR.string.dark_theme)))
            .assertDoesNotExist()

        assertEquals(ResourceState.Success(DarkThemeConfig.Dark), preferences.darkThemeConfigState)

        onNode(
            hasAnyAncestor(hasTestTag("SettingUi:Setting_DarkThemeConfig")) and
                hasContentDescription(activity!!.getString(uiSettingsR.string.open_in_settings)),
        )
            .performScrollTo()
            .performClick()

        onNodeWithText(activity!!.getString(uiSettingsR.string.visual))
            .assertIsDisplayed()

        if (!windowSizeClass.isWidthAtLeastBreakpoint(WindowSizeClass.WIDTH_DP_MEDIUM_LOWER_BOUND)) {
            onNodeWithContentDescription(activity!!.getString(uiAppR.string.back))
                .performClick()
        }

        onNodeWithContentDescription(activity!!.getString(uiAppR.string.back))
            .performClick()

        onNodeWithText(activity!!.getString(uiAppR.string.settings))
            .assertIsSelected()

        Espresso.pressBack()

        onNodeWithText(activity!!.getString(uiAppR.string.speed))
            .assertIsSelected()

        Espresso.pressBack()

        onNode(
            hasAnyAncestor(hasTestTag("CellUniverseActionCard")) and
                hasContentDescription(activity!!.getString(uiAppR.string.expand)),
        )
            .assertExists()
    }

    @SkipLeakDetection("recomposer", "Outer")
    @Test
    fun can_change_algorithm_implementation_to_naive() = runUiTest {
        val windowSizeClass =
            activity!!.run {
                val dpSize = with(Density(this)) {
                    WindowMetricsCalculator.getOrCreate()
                        .computeCurrentWindowMetrics(this@run)
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

        onNode(
            hasAnyAncestor(hasTestTag("CellUniverseActionCard")) and
                hasContentDescription(activity!!.getString(uiAppR.string.expand)),
        )
            .performClick()

        onNodeWithText(activity!!.getString(uiAppR.string.settings))
            .performClick()

        onNodeWithText(activity!!.getString(uiAppR.string.settings))
            .assertIsSelected()

        onNodeWithText(activity!!.getString(uiSettingsR.string.see_all))
            .performClick()

        onNodeWithText(activity!!.getString(uiSettingsR.string.algorithm))
            .performClick()

        onNodeWithText(activity!!.getString(uiSettingsR.string.algorithm_implementation))
            .performClick()

        onNode(hasAnyAncestor(isPopup()) and hasText(activity!!.getString(uiSettingsR.string.naive_algorithm)))
            .assertHasClickAction()
            .performClick()

        onNode(hasAnyAncestor(isPopup()) and hasText(activity!!.getString(uiSettingsR.string.naive_algorithm)))
            .assertDoesNotExist()

        assertEquals(ResourceState.Success(AlgorithmType.NaiveAlgorithm), preferences.algorithmChoiceState)

        if (!windowSizeClass.isWidthAtLeastBreakpoint(WindowSizeClass.WIDTH_DP_MEDIUM_LOWER_BOUND)) {
            Espresso.pressBack()
            waitForIdle()
        }

        Espresso.pressBack()

        onNodeWithText(activity!!.getString(uiAppR.string.settings))
            .assertIsSelected()

        Espresso.pressBack()

        onNodeWithText(activity!!.getString(uiAppR.string.speed))
            .assertIsSelected()

        Espresso.pressBack()

        onNode(
            hasAnyAncestor(hasTestTag("CellUniverseActionCard")) and
                hasContentDescription(activity!!.getString(uiAppR.string.expand)),
        )
            .assertExists()
    }

    @OptIn(ExperimentalTestApi::class, ExperimentalCoroutinesApi::class)
    @SkipLeakDetection("recomposer", "Outer")
    @Test
    fun can_watch_clipboard_and_view_deserialization_info() = runUiTest {
        val windowSizeClass =
            activity!!.run {
                val dpSize = with(Density(this)) {
                    WindowMetricsCalculator.getOrCreate()
                        .computeCurrentWindowMetrics(this@run)
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

        val clipboardManager = activity!!.getSystemService<ClipboardManager>()
        assertNotNull(clipboardManager)
        clipboardManager.setPrimaryClip(
            ClipData.newPlainText("test", ".X.\n..X\nXXX"),
        )

        onNode(
            hasAnyAncestor(hasTestTag("CellUniverseActionCard")) and
                hasContentDescription(activity!!.getString(uiAppR.string.expand)),
        )
            .performClick()

        onNodeWithText(activity!!.getString(uiAppR.string.edit))
            .performClick()

        onNodeWithText(activity!!.getString(uiAppR.string.edit))
            .assertIsSelected()

        onNodeWithText(activity!!.getString(uiAppR.string.allow))
            .performClick()

        waitForIdle()

        onNodeWithContentDescription(activity!!.getString(uiAppR.string.warnings))
            .performClick()

        if (
            windowSizeClass.isWidthAtLeastBreakpoint(WindowSizeClass.WIDTH_DP_MEDIUM_LOWER_BOUND) ||
            windowSizeClass.isHeightAtLeastBreakpoint(WindowSizeClass.HEIGHT_DP_MEDIUM_LOWER_BOUND)
        ) {
            onNode(isDialog())
                .assertExists()
        } else {
            onNode(isDialog())
                .assertDoesNotExist()
        }

        onNodeWithText(activity!!.getString(uiAppR.string.deserialization_succeeded))
            .performClick()

        Espresso.pressBack()

        onNodeWithText(activity!!.getString(uiAppR.string.deserialization_succeeded))
            .assertDoesNotExist()
        onNode(isDialog())
            .assertDoesNotExist()
    }
}
