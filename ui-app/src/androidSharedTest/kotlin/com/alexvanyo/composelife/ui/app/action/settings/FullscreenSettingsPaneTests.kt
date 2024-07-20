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
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.semantics.SemanticsProperties
import androidx.compose.ui.test.DeviceConfigurationOverride
import androidx.compose.ui.test.ForcedSize
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
import androidx.compose.ui.unit.IntSize
import androidx.compose.ui.unit.dp
import androidx.compose.ui.unit.toSize
import com.alexvanyo.composelife.kmpandroidrunner.KmpAndroidJUnit4
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferences
import com.alexvanyo.composelife.test.BaseUiInjectTest
import com.alexvanyo.composelife.test.InjectTestActivity
import com.alexvanyo.composelife.ui.app.ComposeLifeNavigation
import com.alexvanyo.composelife.ui.app.ComposeLifeUiNavigation
import com.alexvanyo.composelife.ui.app.R
import com.alexvanyo.composelife.ui.app.TestComposeLifeApplicationComponent
import com.alexvanyo.composelife.ui.app.createComponent
import leakcanary.SkipLeakDetection
import org.junit.runner.RunWith
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNull

@Suppress("LargeClass")
@OptIn(ExperimentalMaterial3WindowSizeClassApi::class)
@RunWith(KmpAndroidJUnit4::class)
class FullscreenSettingsPaneTests : BaseUiInjectTest<TestComposeLifeApplicationComponent, InjectTestActivity>(
    { TestComposeLifeApplicationComponent.createComponent() },
    InjectTestActivity::class.java,
) {

    private val fullscreenSettingsDetailPaneLocalEntryPoint = object : FullscreenSettingsDetailPaneLocalEntryPoint {
        override val preferences = LoadedComposeLifePreferences.Defaults
    }

    private val fullscreenSettingsDetailPaneInjectEntryPoint get() =
        composeTestRule.activity.uiComponent.entryPoint as FullscreenSettingsDetailPaneInjectEntryPoint

    private val fullScreenSettingsDetailEntryPoint get() = object :
        FullscreenSettingsDetailPaneInjectEntryPoint by fullscreenSettingsDetailPaneInjectEntryPoint,
        FullscreenSettingsDetailPaneLocalEntryPoint by fullscreenSettingsDetailPaneLocalEntryPoint {}

    @Test
    @SkipLeakDetection("appliedChanges", "Outer")
    fun show_list_screen_is_displayed_correctly_with_compact_width() = runAppTest {
        val entryPoint = fullScreenSettingsDetailEntryPoint

        var onBackButtonPressedCount = 0

        composeTestRule.setContent {
            DeviceConfigurationOverride(
                DeviceConfigurationOverride.ForcedSize(DpSize(500.dp, 500.dp)),
            ) {
                BoxWithConstraints {
                    val windowSizeClass = WindowSizeClass.calculateFromSize(
                        IntSize(constraints.maxWidth, constraints.maxHeight).toSize(),
                        LocalDensity.current,
                    )
                    val listUiNavValue = ComposeLifeUiNavigation.FullscreenSettingsList(
                        nav = ComposeLifeNavigation.FullscreenSettingsList(
                            initialSettingsCategory = SettingsCategory.Algorithm,
                        ),
                        windowSizeClass = windowSizeClass,
                        isDetailPresent = false,
                    )
                    val detailsUiNavValue = ComposeLifeUiNavigation.FullscreenSettingsDetail(
                        nav = ComposeLifeNavigation.FullscreenSettingsDetail(
                            settingsCategory = SettingsCategory.Algorithm,
                            initialSettingToScrollTo = null,
                        ),
                        listDetailInfo = listUiNavValue,
                    )

                    with(entryPoint) {
                        FullscreenSettingsPane(
                            listUiNavValue = listUiNavValue,
                            detailsUiNavValue = detailsUiNavValue,
                            onBackButtonPressed = {
                                onBackButtonPressedCount++
                            },
                            setSettingsCategory = {},
                        )
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
    @SkipLeakDetection("appliedChanges", "Outer")
    fun show_list_screen_is_displayed_correctly_with_medium_width() = runAppTest {
        val entryPoint = fullScreenSettingsDetailEntryPoint

        var onBackButtonPressedCount = 0

        composeTestRule.setContent {
            DeviceConfigurationOverride(
                DeviceConfigurationOverride.ForcedSize(DpSize(700.dp, 500.dp)),
            ) {
                BoxWithConstraints {
                    val windowSizeClass = WindowSizeClass.calculateFromSize(
                        IntSize(constraints.maxWidth, constraints.maxHeight).toSize(),
                        LocalDensity.current,
                    )
                    val listUiNavValue = ComposeLifeUiNavigation.FullscreenSettingsList(
                        nav = ComposeLifeNavigation.FullscreenSettingsList(
                            initialSettingsCategory = SettingsCategory.Algorithm,
                        ),
                        windowSizeClass = windowSizeClass,
                        isDetailPresent = false,
                    )
                    val detailsUiNavValue = ComposeLifeUiNavigation.FullscreenSettingsDetail(
                        nav = ComposeLifeNavigation.FullscreenSettingsDetail(
                            settingsCategory = SettingsCategory.Algorithm,
                            initialSettingToScrollTo = null,
                        ),
                        listDetailInfo = listUiNavValue,
                    )

                    with(entryPoint) {
                        FullscreenSettingsPane(
                            listUiNavValue = listUiNavValue,
                            detailsUiNavValue = detailsUiNavValue,
                            onBackButtonPressed = {
                                onBackButtonPressedCount++
                            },
                            setSettingsCategory = {},
                        )
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
    @SkipLeakDetection("appliedChanges", "Outer", "Inner")
    fun show_detail_screen_is_displayed_correctly_with_compact_width() = runAppTest {
        val entryPoint = fullScreenSettingsDetailEntryPoint

        var onBackButtonPressedCount = 0

        composeTestRule.setContent {
            DeviceConfigurationOverride(
                DeviceConfigurationOverride.ForcedSize(DpSize(500.dp, 500.dp)),
            ) {
                BoxWithConstraints {
                    val windowSizeClass = WindowSizeClass.calculateFromSize(
                        IntSize(constraints.maxWidth, constraints.maxHeight).toSize(),
                        LocalDensity.current,
                    )
                    val listUiNavValue = ComposeLifeUiNavigation.FullscreenSettingsList(
                        nav = ComposeLifeNavigation.FullscreenSettingsList(
                            initialSettingsCategory = SettingsCategory.Algorithm,
                        ),
                        windowSizeClass = windowSizeClass,
                        isDetailPresent = true,
                    )
                    val detailsUiNavValue = ComposeLifeUiNavigation.FullscreenSettingsDetail(
                        nav = ComposeLifeNavigation.FullscreenSettingsDetail(
                            settingsCategory = SettingsCategory.Algorithm,
                            initialSettingToScrollTo = null,
                        ),
                        listDetailInfo = listUiNavValue,
                    )

                    with(entryPoint) {
                        FullscreenSettingsPane(
                            listUiNavValue = listUiNavValue,
                            detailsUiNavValue = detailsUiNavValue,
                            onBackButtonPressed = {
                                onBackButtonPressedCount++
                            },
                            setSettingsCategory = {},
                        )
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

        assertEquals(1, onBackButtonPressedCount)
    }

    @Test
    @SkipLeakDetection("appliedChanges", "Outer")
    fun show_detail_screen_is_displayed_correctly_with_medium_width() = runAppTest {
        val entryPoint = fullScreenSettingsDetailEntryPoint

        var onBackButtonPressedCount = 0

        composeTestRule.setContent {
            DeviceConfigurationOverride(
                DeviceConfigurationOverride.ForcedSize(DpSize(700.dp, 500.dp)),
            ) {
                BoxWithConstraints {
                    val windowSizeClass = WindowSizeClass.calculateFromSize(
                        IntSize(constraints.maxWidth, constraints.maxHeight).toSize(),
                        LocalDensity.current,
                    )
                    val listUiNavValue = ComposeLifeUiNavigation.FullscreenSettingsList(
                        nav = ComposeLifeNavigation.FullscreenSettingsList(
                            initialSettingsCategory = SettingsCategory.Algorithm,
                        ),
                        windowSizeClass = windowSizeClass,
                        isDetailPresent = true,
                    )
                    val detailsUiNavValue = ComposeLifeUiNavigation.FullscreenSettingsDetail(
                        nav = ComposeLifeNavigation.FullscreenSettingsDetail(
                            settingsCategory = SettingsCategory.Algorithm,
                            initialSettingToScrollTo = null,
                        ),
                        listDetailInfo = listUiNavValue,
                    )

                    with(entryPoint) {
                        FullscreenSettingsPane(
                            listUiNavValue = listUiNavValue,
                            detailsUiNavValue = detailsUiNavValue,
                            onBackButtonPressed = {
                                onBackButtonPressedCount++
                            },
                            setSettingsCategory = {},
                        )
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
    @SkipLeakDetection("appliedChanges", "Outer")
    fun click_on_detail_is_displayed_correctly_with_compact_width() = runAppTest {
        val entryPoint = fullScreenSettingsDetailEntryPoint

        val listNavValue = ComposeLifeNavigation.FullscreenSettingsList(
            initialSettingsCategory = SettingsCategory.Algorithm,
        )
        var isDetailPresent by mutableStateOf(false)

        composeTestRule.setContent {
            DeviceConfigurationOverride(
                DeviceConfigurationOverride.ForcedSize(DpSize(500.dp, 500.dp)),
            ) {
                BoxWithConstraints {
                    val windowSizeClass = WindowSizeClass.calculateFromSize(
                        IntSize(constraints.maxWidth, constraints.maxHeight).toSize(),
                        LocalDensity.current,
                    )
                    val listUiNavValue = ComposeLifeUiNavigation.FullscreenSettingsList(
                        nav = listNavValue,
                        windowSizeClass = windowSizeClass,
                        isDetailPresent = isDetailPresent,
                    )
                    val detailsUiNavValue = ComposeLifeUiNavigation.FullscreenSettingsDetail(
                        nav = ComposeLifeNavigation.FullscreenSettingsDetail(
                            settingsCategory = listNavValue.settingsCategory,
                            initialSettingToScrollTo = null,
                        ),
                        listDetailInfo = listUiNavValue,
                    )

                    with(entryPoint) {
                        FullscreenSettingsPane(
                            listUiNavValue = listUiNavValue,
                            detailsUiNavValue = detailsUiNavValue,
                            onBackButtonPressed = {},
                            setSettingsCategory = {
                                listNavValue.settingsCategory = it
                                isDetailPresent = true
                            },
                        )
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
    @SkipLeakDetection("appliedChanges", "Outer")
    fun click_on_detail_is_displayed_correctly_with_medium_width() = runAppTest {
        val entryPoint = fullScreenSettingsDetailEntryPoint

        val listNavValue = ComposeLifeNavigation.FullscreenSettingsList(
            initialSettingsCategory = SettingsCategory.Algorithm,
        )
        var isDetailPresent by mutableStateOf(false)

        composeTestRule.setContent {
            DeviceConfigurationOverride(
                DeviceConfigurationOverride.ForcedSize(DpSize(700.dp, 500.dp)),
            ) {
                BoxWithConstraints {
                    val windowSizeClass = WindowSizeClass.calculateFromSize(
                        IntSize(constraints.maxWidth, constraints.maxHeight).toSize(),
                        LocalDensity.current,
                    )
                    val listUiNavValue = ComposeLifeUiNavigation.FullscreenSettingsList(
                        nav = listNavValue,
                        windowSizeClass = windowSizeClass,
                        isDetailPresent = isDetailPresent,
                    )
                    val detailsUiNavValue = ComposeLifeUiNavigation.FullscreenSettingsDetail(
                        nav = ComposeLifeNavigation.FullscreenSettingsDetail(
                            settingsCategory = listNavValue.settingsCategory,
                            initialSettingToScrollTo = null,
                        ),
                        listDetailInfo = listUiNavValue,
                    )

                    with(entryPoint) {
                        FullscreenSettingsPane(
                            listUiNavValue = listUiNavValue,
                            detailsUiNavValue = detailsUiNavValue,
                            onBackButtonPressed = {},
                            setSettingsCategory = {
                                listNavValue.settingsCategory = it
                                isDetailPresent = true
                            },
                        )
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
        val entryPoint = fullScreenSettingsDetailEntryPoint

        composeTestRule.setContent {
            DeviceConfigurationOverride(
                DeviceConfigurationOverride.ForcedSize(DpSize(300.dp, 300.dp)),
            ) {
                BoxWithConstraints {
                    val windowSizeClass = WindowSizeClass.calculateFromSize(
                        IntSize(constraints.maxWidth, constraints.maxHeight).toSize(),
                        LocalDensity.current,
                    )
                    val listUiNavValue = ComposeLifeUiNavigation.FullscreenSettingsList(
                        nav = ComposeLifeNavigation.FullscreenSettingsList(
                            initialSettingsCategory = SettingsCategory.Visual,
                        ),
                        windowSizeClass = windowSizeClass,
                        isDetailPresent = true,
                    )
                    val detailsUiNavValue = ComposeLifeUiNavigation.FullscreenSettingsDetail(
                        nav = ComposeLifeNavigation.FullscreenSettingsDetail(
                            settingsCategory = SettingsCategory.Visual,
                            initialSettingToScrollTo = null,
                        ),
                        listDetailInfo = listUiNavValue,
                    )

                    with(entryPoint) {
                        FullscreenSettingsPane(
                            listUiNavValue = listUiNavValue,
                            detailsUiNavValue = detailsUiNavValue,
                            onBackButtonPressed = {},
                            setSettingsCategory = {},
                        )
                    }
                }
            }
        }

        composeTestRule
            .onNode(
                hasScrollAction().and(
                    hasAnyDescendant(
                        hasContentDescription(
                            context.getString(R.string.corner_fraction_label_and_value, 0f),
                        ),
                    ),
                ),
            )
            .assert(
                SemanticsMatcher("IsScrolledToTop") {
                    val range = it.config.getOrElseNullable(SemanticsProperties.VerticalScrollAxisRange) { null }
                    range != null && range.value.invoke() == 0f
                },
            )
    }

    @Test
    @SkipLeakDetection("appliedChanges", "Outer")
    fun detail_to_scroll_to_is_displayed_correctly() = runAppTest {
        val entryPoint = fullScreenSettingsDetailEntryPoint

        val detailNavValue = ComposeLifeNavigation.FullscreenSettingsDetail(
            settingsCategory = SettingsCategory.Visual,
            initialSettingToScrollTo = Setting.CellShapeConfig,
        )

        composeTestRule.setContent {
            DeviceConfigurationOverride(
                DeviceConfigurationOverride.ForcedSize(DpSize(300.dp, 300.dp)),
            ) {
                BoxWithConstraints {
                    val windowSizeClass = WindowSizeClass.calculateFromSize(
                        IntSize(constraints.maxWidth, constraints.maxHeight).toSize(),
                        LocalDensity.current,
                    )
                    val listUiNavValue = ComposeLifeUiNavigation.FullscreenSettingsList(
                        nav = ComposeLifeNavigation.FullscreenSettingsList(
                            initialSettingsCategory = SettingsCategory.Visual,
                        ),
                        windowSizeClass = windowSizeClass,
                        isDetailPresent = true,
                    )
                    val detailsUiNavValue = ComposeLifeUiNavigation.FullscreenSettingsDetail(
                        nav = detailNavValue,
                        listDetailInfo = listUiNavValue,
                    )

                    with(entryPoint) {
                        FullscreenSettingsPane(
                            listUiNavValue = listUiNavValue,
                            detailsUiNavValue = detailsUiNavValue,
                            onBackButtonPressed = {},
                            setSettingsCategory = {},
                        )
                    }
                }
            }
        }

        composeTestRule.waitForIdle()

        assertNull(detailNavValue.settingToScrollTo)

        composeTestRule
            .onNode(
                hasScrollAction().and(
                    hasAnyDescendant(
                        hasContentDescription(
                            context.getString(R.string.corner_fraction_label_and_value, 0f),
                        ),
                    ),
                ),
            )
            .assert(
                SemanticsMatcher("IsNotScrolledToTop") {
                    val range = it.config.getOrElseNullable(SemanticsProperties.VerticalScrollAxisRange) { null }
                    range != null && range.value.invoke() > 0f
                },
            )
    }

    @Test
    @SkipLeakDetection("appliedChanges", "Outer")
    fun reducing_size_keeps_selected_detail() = runAppTest {
        val entryPoint = fullScreenSettingsDetailEntryPoint

        val listNavValue = ComposeLifeNavigation.FullscreenSettingsList(
            initialSettingsCategory = SettingsCategory.Algorithm,
        )
        var isDetailPresent by mutableStateOf(false)

        var size by mutableStateOf(DpSize(700.dp, 500.dp))

        composeTestRule.setContent {
            DeviceConfigurationOverride(
                DeviceConfigurationOverride.ForcedSize(size),
            ) {
                BoxWithConstraints {
                    val windowSizeClass = WindowSizeClass.calculateFromSize(
                        IntSize(constraints.maxWidth, constraints.maxHeight).toSize(),
                        LocalDensity.current,
                    )
                    val listUiNavValue = ComposeLifeUiNavigation.FullscreenSettingsList(
                        nav = listNavValue,
                        windowSizeClass = windowSizeClass,
                        isDetailPresent = isDetailPresent,
                    )
                    val detailsUiNavValue = ComposeLifeUiNavigation.FullscreenSettingsDetail(
                        nav = ComposeLifeNavigation.FullscreenSettingsDetail(
                            settingsCategory = listNavValue.settingsCategory,
                            initialSettingToScrollTo = null,
                        ),
                        listDetailInfo = listUiNavValue,
                    )

                    with(entryPoint) {
                        FullscreenSettingsPane(
                            listUiNavValue = listUiNavValue,
                            detailsUiNavValue = detailsUiNavValue,
                            onBackButtonPressed = {},
                            setSettingsCategory = {
                                listNavValue.settingsCategory = it
                                isDetailPresent = true
                            },
                        )
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
        val entryPoint = fullScreenSettingsDetailEntryPoint

        val listNavValue = ComposeLifeNavigation.FullscreenSettingsList(
            initialSettingsCategory = SettingsCategory.Algorithm,
        )
        var isDetailPresent by mutableStateOf(false)
        var size by mutableStateOf(DpSize(500.dp, 500.dp))

        composeTestRule.setContent {
            DeviceConfigurationOverride(
                DeviceConfigurationOverride.ForcedSize(size),
            ) {
                BoxWithConstraints {
                    val windowSizeClass = WindowSizeClass.calculateFromSize(
                        IntSize(constraints.maxWidth, constraints.maxHeight).toSize(),
                        LocalDensity.current,
                    )
                    val listUiNavValue = ComposeLifeUiNavigation.FullscreenSettingsList(
                        nav = listNavValue,
                        windowSizeClass = windowSizeClass,
                        isDetailPresent = isDetailPresent,
                    )
                    val detailsUiNavValue = ComposeLifeUiNavigation.FullscreenSettingsDetail(
                        nav = ComposeLifeNavigation.FullscreenSettingsDetail(
                            settingsCategory = listNavValue.settingsCategory,
                            initialSettingToScrollTo = null,
                        ),
                        listDetailInfo = listUiNavValue,
                    )

                    with(entryPoint) {
                        FullscreenSettingsPane(
                            listUiNavValue = listUiNavValue,
                            detailsUiNavValue = detailsUiNavValue,
                            onBackButtonPressed = {},
                            setSettingsCategory = {
                                listNavValue.settingsCategory = it
                                isDetailPresent = true
                            },
                        )
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
