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

package com.alexvanyo.composelife.ui

import android.app.Activity
import androidx.compose.material3.windowsizeclass.ExperimentalMaterial3WindowSizeClassApi
import androidx.compose.material3.windowsizeclass.WindowSizeClass
import androidx.compose.material3.windowsizeclass.WindowWidthSizeClass
import androidx.compose.ui.graphics.toComposeRect
import androidx.compose.ui.test.assertHasClickAction
import androidx.compose.ui.test.assertIsSelected
import androidx.compose.ui.test.hasAnyAncestor
import androidx.compose.ui.test.hasContentDescription
import androidx.compose.ui.test.hasTestTag
import androidx.compose.ui.test.hasText
import androidx.compose.ui.test.isPopup
import androidx.compose.ui.test.onNodeWithContentDescription
import androidx.compose.ui.test.onNodeWithText
import androidx.compose.ui.test.performClick
import androidx.compose.ui.test.performScrollTo
import androidx.compose.ui.unit.Density
import androidx.test.core.app.ActivityScenario
import androidx.test.espresso.Espresso
import androidx.window.layout.WindowMetricsCalculator
import com.alexvanyo.composelife.MainActivity
import com.alexvanyo.composelife.preferences.AlgorithmType
import com.alexvanyo.composelife.preferences.DarkThemeConfig
import com.alexvanyo.composelife.preferences.QuickAccessSetting
import com.alexvanyo.composelife.resourcestate.ResourceState
import com.alexvanyo.composelife.test.BaseHiltTest
import dagger.hilt.android.testing.HiltAndroidTest
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.test.TestDispatcher
import leakcanary.SkipLeakDetection
import org.junit.Test
import javax.inject.Inject
import kotlin.contracts.ExperimentalContracts
import kotlin.contracts.InvocationKind
import kotlin.contracts.contract
import kotlin.test.assertEquals

@OptIn(ExperimentalCoroutinesApi::class, ExperimentalMaterial3WindowSizeClassApi::class)
@HiltAndroidTest
class ComposeLifeAppTests : BaseHiltTest<MainActivity>(MainActivity::class.java) {

    @Inject
    lateinit var testDispatcher: TestDispatcher

    @SkipLeakDetection("recomposer", "Outer")
    @Test
    fun app_does_not_crash() = runAppTest {
        composeTestRule.waitForIdle()
        testDispatcher.scheduler.runCurrent()

        composeTestRule.onNodeWithContentDescription(context.getString(R.string.play)).performClick()

        composeTestRule.onNodeWithContentDescription(context.getString(R.string.pause)).performClick()

        composeTestRule.waitForIdle()
    }

    @SkipLeakDetection("recomposer", "Outer", "Inner")
    @Test
    fun app_does_not_crash_when_recreating() = runAppTest {
        composeTestRule.waitForIdle()
        testDispatcher.scheduler.runCurrent()

        composeTestRule.onNodeWithContentDescription(context.getString(R.string.play)).performClick()

        composeTestRule.onNodeWithContentDescription(context.getString(R.string.pause)).performClick()

        composeTestRule.activityRule.scenario.recreate()

        composeTestRule.waitForIdle()
    }

    @SkipLeakDetection("recomposer", "Outer", "Inner")
    @Test
    fun can_change_theme_to_dark_mode() = runAppTest {
        val windowSizeClass = WindowSizeClass.calculateFromSize(
            composeTestRule.activityRule.scenario.withActivity {
                with(Density(this)) {
                    WindowMetricsCalculator
                        .getOrCreate()
                        .computeCurrentWindowMetrics(this@withActivity)
                        .bounds
                        .toComposeRect()
                        .size
                        .toDpSize()
                }
            },
        )

        composeTestRule.waitForIdle()
        testDispatcher.scheduler.runCurrent()

        composeTestRule
            .onNode(
                hasAnyAncestor(hasTestTag("CellUniverseActionCard")) and
                    hasContentDescription(context.getString(R.string.expand)),
            )
            .performClick()

        composeTestRule
            .onNodeWithText(context.getString(R.string.settings))
            .performClick()

        composeTestRule
            .onNodeWithText(context.getString(R.string.settings))
            .assertIsSelected()

        composeTestRule
            .onNodeWithText(context.getString(R.string.see_all))
            .performClick()

        composeTestRule
            .onNodeWithText(context.getString(R.string.visual))
            .performClick()

        composeTestRule
            .onNodeWithText(context.getString(R.string.dark_theme_config))
            .performClick()

        composeTestRule
            .onNode(hasAnyAncestor(isPopup()) and hasText(context.getString(R.string.dark_theme)))
            .assertHasClickAction()
            .performClick()

        composeTestRule
            .onNode(isPopup())
            .assertDoesNotExist()

        assertEquals(ResourceState.Success(DarkThemeConfig.Dark), preferences.darkThemeConfigState)

        when (windowSizeClass.widthSizeClass) {
            WindowWidthSizeClass.Compact -> {
                composeTestRule
                    .onNodeWithContentDescription(context.getString(R.string.back))
                    .performClick()
            }
        }

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.back))
            .performClick()

        composeTestRule
            .onNodeWithText(context.getString(R.string.settings))
            .assertIsSelected()

        Espresso.pressBack()

        composeTestRule
            .onNodeWithText(context.getString(R.string.speed))
            .assertIsSelected()

        Espresso.pressBack()

        composeTestRule
            .onNode(
                hasAnyAncestor(hasTestTag("CellUniverseActionCard")) and
                    hasContentDescription(context.getString(R.string.expand)),
            )
            .assertExists()
    }

    @SkipLeakDetection("recomposer", "Outer", "Inner")
    @Test
    fun can_save_theme_to_quick_access() = runAppTest {
        val windowSizeClass = WindowSizeClass.calculateFromSize(
            composeTestRule.activityRule.scenario.withActivity {
                with(Density(this)) {
                    WindowMetricsCalculator
                        .getOrCreate()
                        .computeCurrentWindowMetrics(this@withActivity)
                        .bounds
                        .toComposeRect()
                        .size
                        .toDpSize()
                }
            },
        )

        composeTestRule.waitForIdle()
        testDispatcher.scheduler.runCurrent()

        composeTestRule
            .onNode(
                hasAnyAncestor(hasTestTag("CellUniverseActionCard")) and
                    hasContentDescription(context.getString(R.string.expand)),
            )
            .performClick()

        composeTestRule
            .onNodeWithText(context.getString(R.string.settings))
            .performClick()

        composeTestRule
            .onNodeWithText(context.getString(R.string.settings))
            .assertIsSelected()

        composeTestRule
            .onNodeWithText(context.getString(R.string.see_all))
            .performClick()

        composeTestRule
            .onNodeWithText(context.getString(R.string.visual))
            .performClick()

        composeTestRule
            .onNode(
                hasAnyAncestor(hasTestTag("SettingUi:Setting_DarkThemeConfig")) and
                    hasContentDescription(context.getString(R.string.add_setting_to_quick_access)),
            )
            .performScrollTo()
            .performClick()

        assertEquals(
            ResourceState.Success(setOf(QuickAccessSetting.DarkThemeConfig)),
            preferences.quickAccessSettingsState,
        )

        when (windowSizeClass.widthSizeClass) {
            WindowWidthSizeClass.Compact -> {
                composeTestRule
                    .onNodeWithContentDescription(context.getString(R.string.back))
                    .performClick()
            }
        }

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.back))
            .performClick()

        composeTestRule
            .onNodeWithText(context.getString(R.string.settings))
            .assertIsSelected()

        composeTestRule
            .onNodeWithText(context.getString(R.string.dark_theme_config))
            .performClick()

        composeTestRule
            .onNode(hasAnyAncestor(isPopup()) and hasText(context.getString(R.string.dark_theme)))
            .assertHasClickAction()
            .performClick()

        composeTestRule
            .onNode(isPopup())
            .assertDoesNotExist()

        assertEquals(ResourceState.Success(DarkThemeConfig.Dark), preferences.darkThemeConfigState)

        composeTestRule
            .onNode(
                hasAnyAncestor(hasTestTag("SettingUi:Setting_DarkThemeConfig")) and
                    hasContentDescription(context.getString(R.string.open_in_settings)),
            )
            .performScrollTo()
            .performClick()

        composeTestRule
            .onNode(
                hasAnyAncestor(hasTestTag("SettingUi:Setting_DarkThemeConfig")) and
                    hasContentDescription(context.getString(R.string.open_in_settings)),
            )
            .assertDoesNotExist()

        when (windowSizeClass.widthSizeClass) {
            WindowWidthSizeClass.Compact -> {
                composeTestRule
                    .onNodeWithContentDescription(context.getString(R.string.back))
                    .performClick()
            }
        }

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.back))
            .performClick()

        composeTestRule
            .onNodeWithText(context.getString(R.string.settings))
            .assertIsSelected()

        Espresso.pressBack()

        composeTestRule
            .onNodeWithText(context.getString(R.string.speed))
            .assertIsSelected()

        Espresso.pressBack()

        composeTestRule
            .onNode(
                hasAnyAncestor(hasTestTag("CellUniverseActionCard")) and
                    hasContentDescription(context.getString(R.string.expand)),
            )
            .assertExists()
    }

    @SkipLeakDetection("recomposer", "Outer", "Inner")
    @Test
    fun can_change_algorithm_implementation_to_naive() = runAppTest {
        val windowSizeClass = WindowSizeClass.calculateFromSize(
            composeTestRule.activityRule.scenario.withActivity {
                with(Density(this)) {
                    WindowMetricsCalculator
                        .getOrCreate()
                        .computeCurrentWindowMetrics(this@withActivity)
                        .bounds
                        .toComposeRect()
                        .size
                        .toDpSize()
                }
            },
        )

        composeTestRule.waitForIdle()
        testDispatcher.scheduler.runCurrent()

        composeTestRule
            .onNode(
                hasAnyAncestor(hasTestTag("CellUniverseActionCard")) and
                    hasContentDescription(context.getString(R.string.expand)),
            )
            .performClick()

        composeTestRule
            .onNodeWithText(context.getString(R.string.settings))
            .performClick()

        composeTestRule
            .onNodeWithText(context.getString(R.string.settings))
            .assertIsSelected()

        composeTestRule
            .onNodeWithText(context.getString(R.string.see_all))
            .performClick()

        composeTestRule
            .onNodeWithText(context.getString(R.string.algorithm))
            .performClick()

        composeTestRule
            .onNodeWithText(context.getString(R.string.algorithm_implementation))
            .performClick()

        composeTestRule
            .onNode(hasAnyAncestor(isPopup()) and hasText(context.getString(R.string.naive_algorithm)))
            .assertHasClickAction()
            .performClick()

        composeTestRule
            .onNode(isPopup())
            .assertDoesNotExist()

        assertEquals(ResourceState.Success(AlgorithmType.NaiveAlgorithm), preferences.algorithmChoiceState)

        when (windowSizeClass.widthSizeClass) {
            WindowWidthSizeClass.Compact -> {
                composeTestRule
                    .onNodeWithContentDescription(context.getString(R.string.back))
                    .performClick()
            }
        }

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.back))
            .performClick()

        composeTestRule
            .onNodeWithText(context.getString(R.string.settings))
            .assertIsSelected()

        Espresso.pressBack()

        composeTestRule
            .onNodeWithText(context.getString(R.string.speed))
            .assertIsSelected()

        Espresso.pressBack()

        composeTestRule
            .onNode(
                hasAnyAncestor(hasTestTag("CellUniverseActionCard")) and
                    hasContentDescription(context.getString(R.string.expand)),
            )
            .assertExists()
    }
}

@OptIn(ExperimentalContracts::class)
private inline fun <reified A : Activity, T : Any> ActivityScenario<A>.withActivity(
    crossinline block: A.() -> T,
): T {
    contract {
        callsInPlace(block, InvocationKind.EXACTLY_ONCE)
    }
    var result: Result<T>? = null
    onActivity { activity ->
        result = kotlin.runCatching {
            block(activity)
        }
    }
    return result!!.getOrThrow()
}
