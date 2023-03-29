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

package com.alexvanyo.composelife.ui.app.action.settings

import androidx.compose.foundation.layout.BoxWithConstraints
import androidx.compose.material3.windowsizeclass.ExperimentalMaterial3WindowSizeClassApi
import androidx.compose.material3.windowsizeclass.WindowSizeClass
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.setValue
import androidx.compose.ui.semantics.SemanticsProperties
import androidx.compose.ui.test.SemanticsMatcher
import androidx.compose.ui.test.assert
import androidx.compose.ui.test.assertHasClickAction
import androidx.compose.ui.test.assertIsDisplayed
import androidx.compose.ui.test.assertIsNotSelected
import androidx.compose.ui.test.assertIsSelectable
import androidx.compose.ui.test.assertIsSelected
import androidx.compose.ui.test.hasAnyDescendant
import androidx.compose.ui.test.hasContentDescription
import androidx.compose.ui.test.hasScrollAction
import androidx.compose.ui.test.isSelectable
import androidx.compose.ui.test.onNodeWithContentDescription
import androidx.compose.ui.test.onNodeWithText
import androidx.compose.ui.test.performClick
import androidx.compose.ui.test.performScrollTo
import androidx.compose.ui.unit.DpSize
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferences
import com.alexvanyo.composelife.test.BaseUiHiltTest
import com.alexvanyo.composelife.test.TestActivity
import com.alexvanyo.composelife.ui.app.R
import com.alexvanyo.composelife.ui.app.action.ActionCardNavigation
import com.google.accompanist.testharness.TestHarness
import dagger.hilt.EntryPoints
import dagger.hilt.android.testing.HiltAndroidTest
import kotlinx.coroutines.ExperimentalCoroutinesApi
import leakcanary.SkipLeakDetection
import kotlin.test.BeforeTest
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertNull

@OptIn(ExperimentalMaterial3WindowSizeClassApi::class, ExperimentalCoroutinesApi::class)
@HiltAndroidTest
class FullscreenSettingsScreenTests : BaseUiHiltTest<TestActivity>(TestActivity::class.java) {

    private val fullscreenSettingsScreenLocalEntryPoint = object : FullscreenSettingsScreenLocalEntryPoint {
        override val preferences = LoadedComposeLifePreferences.Defaults
    }

    private lateinit var fullscreenSettingsScreenHiltEntryPoint: FullscreenSettingsScreenHiltEntryPoint

    @BeforeTest
    fun setup() {
        fullscreenSettingsScreenHiltEntryPoint =
            EntryPoints.get(composeTestRule.activity, FullscreenSettingsScreenHiltEntryPoint::class.java)
    }

    @Test
    fun show_list_screen_is_displayed_correctly_with_compact_width() = runAppTest {
        val fullscreen = ActionCardNavigation.Settings.Fullscreen(
            initialSettingsCategory = SettingsCategory.Algorithm,
            initialShowDetails = false,
            initialSettingToScrollTo = null,
        )
        var onBackButtonPressedCount = 0

        composeTestRule.setContent {
            TestHarness(
                size = DpSize(500.dp, 500.dp)
            ) {
                BoxWithConstraints {
                    val windowSizeClass = WindowSizeClass.calculateFromSize(DpSize(maxWidth, maxHeight))

                    with(fullscreenSettingsScreenHiltEntryPoint) {
                        with(fullscreenSettingsScreenLocalEntryPoint) {
                            FullscreenSettingsScreen(
                                windowSizeClass = windowSizeClass,
                                fullscreen = fullscreen,
                                onBackButtonPressed = {
                                    onBackButtonPressedCount++
                                }
                            )
                        }
                    }
                }
            }
        }

        composeTestRule
            .onNodeWithText(context.getString(R.string.algorithm))
            .performScrollTo()
            .assertIsDisplayed()
            .assertHasClickAction()
            .assert(isSelectable().not())

        composeTestRule
            .onNodeWithText(context.getString(R.string.visual))
            .performScrollTo()
            .assertIsDisplayed()
            .assertHasClickAction()
            .assert(isSelectable().not())

        composeTestRule
            .onNodeWithText(context.getString(R.string.feature_flags))
            .performScrollTo()
            .assertIsDisplayed()
            .assertHasClickAction()
            .assert(isSelectable().not())

        composeTestRule
            .onNodeWithText(context.getString(R.string.hash_life_algorithm))
            .assertDoesNotExist()

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.back))
            .assertIsDisplayed()
            .assertHasClickAction()
            .performClick()

        assertEquals(1, onBackButtonPressedCount)
    }

    @Test
    fun show_list_screen_is_displayed_correctly_with_medium_width() = runAppTest {
        val fullscreen = ActionCardNavigation.Settings.Fullscreen(
            initialSettingsCategory = SettingsCategory.Algorithm,
            initialShowDetails = false,
            initialSettingToScrollTo = null,
        )
        var onBackButtonPressedCount = 0

        composeTestRule.setContent {
            TestHarness(
                size = DpSize(700.dp, 500.dp)
            ) {
                BoxWithConstraints {
                    val windowSizeClass = WindowSizeClass.calculateFromSize(DpSize(maxWidth, maxHeight))

                    with(fullscreenSettingsScreenHiltEntryPoint) {
                        with(fullscreenSettingsScreenLocalEntryPoint) {
                            FullscreenSettingsScreen(
                                windowSizeClass = windowSizeClass,
                                fullscreen = fullscreen,
                                onBackButtonPressed = {
                                    onBackButtonPressedCount++
                                }
                            )
                        }
                    }
                }
            }
        }

        composeTestRule
            .onNodeWithText(context.getString(R.string.algorithm))
            .performScrollTo()
            .assertIsDisplayed()
            .assertHasClickAction()
            .assertIsSelectable()
            .assertIsSelected()

        composeTestRule
            .onNodeWithText(context.getString(R.string.visual))
            .performScrollTo()
            .assertIsDisplayed()
            .assertHasClickAction()
            .assertIsSelectable()
            .assertIsNotSelected()

        composeTestRule
            .onNodeWithText(context.getString(R.string.feature_flags))
            .performScrollTo()
            .assertIsDisplayed()
            .assertHasClickAction()
            .assertIsSelectable()
            .assertIsNotSelected()

        composeTestRule
            .onNodeWithText(context.getString(R.string.hash_life_algorithm))
            .assertExists()
            .assertHasClickAction()

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.back))
            .assertIsDisplayed()
            .assertHasClickAction()
            .performClick()

        assertEquals(1, onBackButtonPressedCount)
    }

    @Test
    fun show_detail_screen_is_displayed_correctly_with_compact_width() = runAppTest {
        val fullscreen = ActionCardNavigation.Settings.Fullscreen(
            initialSettingsCategory = SettingsCategory.Algorithm,
            initialShowDetails = true,
            initialSettingToScrollTo = null,
        )
        var onBackButtonPressedCount = 0

        composeTestRule.setContent {
            TestHarness(
                size = DpSize(500.dp, 500.dp)
            ) {
                BoxWithConstraints {
                    val windowSizeClass = WindowSizeClass.calculateFromSize(DpSize(maxWidth, maxHeight))

                    with(fullscreenSettingsScreenHiltEntryPoint) {
                        with(fullscreenSettingsScreenLocalEntryPoint) {
                            FullscreenSettingsScreen(
                                windowSizeClass = windowSizeClass,
                                fullscreen = fullscreen,
                                onBackButtonPressed = {
                                    onBackButtonPressedCount++
                                }
                            )
                        }
                    }
                }
            }
        }

        composeTestRule
            .onNodeWithText(context.getString(R.string.visual))
            .assertDoesNotExist()

        composeTestRule
            .onNodeWithText(context.getString(R.string.feature_flags))
            .assertDoesNotExist()

        composeTestRule
            .onNodeWithText(context.getString(R.string.hash_life_algorithm))
            .assertExists()

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.back))
            .assertIsDisplayed()
            .assertHasClickAction()
            .performClick()

        assertFalse(fullscreen.showDetails)
        assertEquals(0, onBackButtonPressedCount)
    }

    @Test
    fun show_detail_screen_is_displayed_correctly_with_medium_width() = runAppTest {
        val fullscreen = ActionCardNavigation.Settings.Fullscreen(
            initialSettingsCategory = SettingsCategory.Algorithm,
            initialShowDetails = true,
            initialSettingToScrollTo = null,
        )
        var onBackButtonPressedCount = 0

        composeTestRule.setContent {
            TestHarness(
                size = DpSize(700.dp, 500.dp)
            ) {
                BoxWithConstraints {
                    val windowSizeClass = WindowSizeClass.calculateFromSize(DpSize(maxWidth, maxHeight))

                    with(fullscreenSettingsScreenHiltEntryPoint) {
                        with(fullscreenSettingsScreenLocalEntryPoint) {
                            FullscreenSettingsScreen(
                                windowSizeClass = windowSizeClass,
                                fullscreen = fullscreen,
                                onBackButtonPressed = {
                                    onBackButtonPressedCount++
                                }
                            )
                        }
                    }
                }
            }
        }

        composeTestRule
            .onNodeWithText(context.getString(R.string.algorithm))
            .performScrollTo()
            .assertIsDisplayed()
            .assertHasClickAction()

        composeTestRule
            .onNodeWithText(context.getString(R.string.visual))
            .performScrollTo()
            .assertIsDisplayed()
            .assertHasClickAction()

        composeTestRule
            .onNodeWithText(context.getString(R.string.feature_flags))
            .performScrollTo()
            .assertIsDisplayed()
            .assertHasClickAction()

        composeTestRule
            .onNodeWithText(context.getString(R.string.hash_life_algorithm))
            .assertExists()
            .assertHasClickAction()

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.back))
            .assertIsDisplayed()
            .assertHasClickAction()
            .performClick()

        assertEquals(1, onBackButtonPressedCount)
    }

    @Test
    fun click_on_detail_is_displayed_correctly_with_compact_width() = runAppTest {
        val fullscreen = ActionCardNavigation.Settings.Fullscreen(
            initialSettingsCategory = SettingsCategory.Algorithm,
            initialShowDetails = false,
            initialSettingToScrollTo = null,
        )

        composeTestRule.setContent {
            TestHarness(
                size = DpSize(500.dp, 500.dp)
            ) {
                BoxWithConstraints {
                    val windowSizeClass = WindowSizeClass.calculateFromSize(DpSize(maxWidth, maxHeight))

                    with(fullscreenSettingsScreenHiltEntryPoint) {
                        with(fullscreenSettingsScreenLocalEntryPoint) {
                            FullscreenSettingsScreen(
                                windowSizeClass = windowSizeClass,
                                fullscreen = fullscreen,
                                onBackButtonPressed = {},
                            )
                        }
                    }
                }
            }
        }

        composeTestRule
            .onNodeWithText(context.getString(R.string.feature_flags))
            .performScrollTo()
            .performClick()

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.do_not_keep_process))
            .performScrollTo()
            .assertIsDisplayed()

        composeTestRule
            .onNodeWithText(context.getString(R.string.algorithm))
            .assertDoesNotExist()

        composeTestRule
            .onNodeWithText(context.getString(R.string.visual))
            .assertDoesNotExist()
    }

    @Test
    fun click_on_detail_is_displayed_correctly_with_medium_width() = runAppTest {
        val fullscreen = ActionCardNavigation.Settings.Fullscreen(
            initialSettingsCategory = SettingsCategory.Algorithm,
            initialShowDetails = false,
            initialSettingToScrollTo = null,
        )

        composeTestRule.setContent {
            TestHarness(
                size = DpSize(700.dp, 500.dp)
            ) {
                BoxWithConstraints {
                    val windowSizeClass = WindowSizeClass.calculateFromSize(DpSize(maxWidth, maxHeight))

                    with(fullscreenSettingsScreenHiltEntryPoint) {
                        with(fullscreenSettingsScreenLocalEntryPoint) {
                            FullscreenSettingsScreen(
                                windowSizeClass = windowSizeClass,
                                fullscreen = fullscreen,
                                onBackButtonPressed = {},
                            )
                        }
                    }
                }
            }
        }

        composeTestRule
            .onNodeWithText(context.getString(R.string.feature_flags))
            .performScrollTo()
            .performClick()

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.do_not_keep_process))
            .performScrollTo()
            .assertIsDisplayed()

        composeTestRule
            .onNodeWithText(context.getString(R.string.algorithm))
            .performScrollTo()
            .assertIsDisplayed()
            .assertIsSelectable()
            .assertIsNotSelected()

        composeTestRule
            .onNodeWithText(context.getString(R.string.visual))
            .performScrollTo()
            .assertIsDisplayed()
            .assertIsSelectable()
            .assertIsNotSelected()

        composeTestRule
            .onNodeWithText(context.getString(R.string.feature_flags))
            .performScrollTo()
            .assertIsDisplayed()
            .assertIsSelectable()
            .assertIsSelected()
    }

    @Test
    @SkipLeakDetection("appliedChanges", "Outer")
    fun no_detail_to_scroll_to_is_displayed_correctly() = runAppTest {
        val fullscreen = ActionCardNavigation.Settings.Fullscreen(
            initialSettingsCategory = SettingsCategory.Visual,
            initialShowDetails = true,
            initialSettingToScrollTo = null,
        )

        composeTestRule.setContent {
            TestHarness(
                size = DpSize(300.dp, 300.dp)
            ) {
                BoxWithConstraints {
                    val windowSizeClass = WindowSizeClass.calculateFromSize(DpSize(maxWidth, maxHeight))

                    with(fullscreenSettingsScreenHiltEntryPoint) {
                        with(fullscreenSettingsScreenLocalEntryPoint) {
                            FullscreenSettingsScreen(
                                windowSizeClass = windowSizeClass,
                                fullscreen = fullscreen,
                                onBackButtonPressed = {}
                            )
                        }
                    }
                }
            }
        }

        composeTestRule
            .onNode(
                hasScrollAction().and(
                    hasAnyDescendant(
                        hasContentDescription(
                            context.getString(R.string.corner_fraction_label_and_value, 0f)
                        )
                    )
                )
            )
            .assert(
                SemanticsMatcher("IsScrolledToTop") {
                    val range = it.config.getOrElseNullable(SemanticsProperties.VerticalScrollAxisRange) { null }
                    range != null && range.value.invoke() == 0f
                }
            )
    }

    @Test
    @SkipLeakDetection("appliedChanges", "Outer")
    fun detail_to_scroll_to_is_displayed_correctly() = runAppTest {
        val fullscreen = ActionCardNavigation.Settings.Fullscreen(
            initialSettingsCategory = SettingsCategory.Visual,
            initialShowDetails = true,
            initialSettingToScrollTo = Setting.CellShapeConfig,
        )

        composeTestRule.setContent {
            TestHarness(
                size = DpSize(300.dp, 300.dp)
            ) {
                BoxWithConstraints {
                    val windowSizeClass = WindowSizeClass.calculateFromSize(DpSize(maxWidth, maxHeight))

                    with(fullscreenSettingsScreenHiltEntryPoint) {
                        with(fullscreenSettingsScreenLocalEntryPoint) {
                            FullscreenSettingsScreen(
                                windowSizeClass = windowSizeClass,
                                fullscreen = fullscreen,
                                onBackButtonPressed = {},
                            )
                        }
                    }
                }
            }
        }

        composeTestRule.waitForIdle()

        assertNull(fullscreen.settingToScrollTo)

        composeTestRule
            .onNode(
                hasScrollAction().and(
                    hasAnyDescendant(
                        hasContentDescription(
                            context.getString(R.string.corner_fraction_label_and_value, 0f)
                        )
                    )
                )
            )
            .assert(
                SemanticsMatcher("IsNotScrolledToTop") {
                    val range = it.config.getOrElseNullable(SemanticsProperties.VerticalScrollAxisRange) { null }
                    range != null && range.value.invoke() > 0f
                }
            )
    }

    @Test
    @SkipLeakDetection("appliedChanges", "Outer")
    fun reducing_size_keeps_selected_detail() = runAppTest {
        val fullscreen = ActionCardNavigation.Settings.Fullscreen(
            initialSettingsCategory = SettingsCategory.Algorithm,
            initialShowDetails = false,
            initialSettingToScrollTo = null,
        )
        var size by mutableStateOf(DpSize(700.dp, 500.dp))

        composeTestRule.setContent {
            TestHarness(
                size = size
            ) {
                BoxWithConstraints {
                    val windowSizeClass = WindowSizeClass.calculateFromSize(DpSize(maxWidth, maxHeight))

                    with(fullscreenSettingsScreenHiltEntryPoint) {
                        with(fullscreenSettingsScreenLocalEntryPoint) {
                            FullscreenSettingsScreen(
                                windowSizeClass = windowSizeClass,
                                fullscreen = fullscreen,
                                onBackButtonPressed = {},
                            )
                        }
                    }
                }
            }
        }

        composeTestRule
            .onNodeWithText(context.getString(R.string.visual))
            .performClick()

        size = DpSize(500.dp, 500.dp)

        composeTestRule
            .onNodeWithContentDescription(
                context.getString(R.string.corner_fraction_label_and_value, 0f),
            )
            .performScrollTo()
            .assertIsDisplayed()
    }

    @Test
    @SkipLeakDetection("appliedChanges", "Outer")
    fun expanding_size_keeps_selected_detail() = runAppTest {
        val fullscreen = ActionCardNavigation.Settings.Fullscreen(
            initialSettingsCategory = SettingsCategory.Algorithm,
            initialShowDetails = false,
            initialSettingToScrollTo = null,
        )
        var size by mutableStateOf(DpSize(500.dp, 500.dp))

        composeTestRule.setContent {
            TestHarness(
                size = size
            ) {
                BoxWithConstraints {
                    val windowSizeClass = WindowSizeClass.calculateFromSize(DpSize(maxWidth, maxHeight))

                    with(fullscreenSettingsScreenHiltEntryPoint) {
                        with(fullscreenSettingsScreenLocalEntryPoint) {
                            FullscreenSettingsScreen(
                                windowSizeClass = windowSizeClass,
                                fullscreen = fullscreen,
                                onBackButtonPressed = {},
                            )
                        }
                    }
                }
            }
        }

        composeTestRule
            .onNodeWithText(context.getString(R.string.visual))
            .performClick()

        size = DpSize(700.dp, 500.dp)

        composeTestRule
            .onNodeWithContentDescription(
                context.getString(R.string.corner_fraction_label_and_value, 0f),
            )
            .performScrollTo()
            .assertIsDisplayed()

        composeTestRule
            .onNodeWithText(context.getString(R.string.visual))
            .performScrollTo()
            .assertIsDisplayed()
            .assertIsSelectable()
            .assertIsSelected()
    }
}
