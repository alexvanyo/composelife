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

package com.alexvanyo.composelife.ui.settings

import androidx.compose.foundation.layout.BoxWithConstraints
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.setValue
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.semantics.SemanticsProperties
import androidx.compose.ui.test.DeviceConfigurationOverride
import androidx.compose.ui.test.ExperimentalTestApi
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
import androidx.compose.ui.unit.dp
import androidx.window.core.layout.WindowSizeClass
import androidx.window.core.layout.WindowSizeClass.Companion.BREAKPOINTS_V1
import androidx.window.core.layout.computeWindowSizeClass
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResolver
import com.alexvanyo.composelife.scopes.ApplicationGraph
import com.alexvanyo.composelife.scopes.UiGraph
import com.alexvanyo.composelife.scopes.UiScope
import com.alexvanyo.composelife.test.BaseUiInjectTest
import com.alexvanyo.composelife.test.runUiTest
import com.alexvanyo.composelife.ui.settings.resources.Algorithm
import com.alexvanyo.composelife.ui.settings.resources.Back
import com.alexvanyo.composelife.ui.settings.resources.CornerFractionLabelAndValue
import com.alexvanyo.composelife.ui.settings.resources.DoNotKeepProcess
import com.alexvanyo.composelife.ui.settings.resources.FeatureFlags
import com.alexvanyo.composelife.ui.settings.resources.HashLifeAlgorithm
import com.alexvanyo.composelife.ui.settings.resources.Strings
import com.alexvanyo.composelife.ui.settings.resources.Visual
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.asContribution
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNull

@ContributesTo(UiScope::class)
interface FullscreenSettingsPaneTestsEntryPoint {
    val fullscreenSettingsDetailPaneEntryPoint: FullscreenSettingsDetailPaneEntryPoint
}

// TODO: Replace with asContribution()
val UiGraph.fullscreenSettingsPaneTestsEntryPoint: FullscreenSettingsPaneTestsEntryPoint get() =
    this as FullscreenSettingsPaneTestsEntryPoint

@Suppress("LargeClass")
@OptIn(ExperimentalTestApi::class)
class FullscreenSettingsPaneTests : BaseUiInjectTest(
    { globalGraph.asContribution<ApplicationGraph.Factory>().create(it) },

) {
    @Test
    fun show_list_screen_is_displayed_correctly_with_compact_width() = runUiTest { uiGraph ->
        val entryPoint = uiGraph.fullscreenSettingsPaneTestsEntryPoint

        var onBackButtonPressedCount = 0

        var settingsCategory: SettingsCategory by mutableStateOf(SettingsCategory.Algorithm)
        var isDetailPresent by mutableStateOf(false)

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            DeviceConfigurationOverride(
                DeviceConfigurationOverride.ForcedSize(DpSize(500.dp, 500.dp)),
            ) {
                BoxWithConstraints {
                    val windowSizeClass = BREAKPOINTS_V1.computeWindowSizeClass(
                        widthDp = maxWidth.value,
                        heightDp = maxHeight.value,
                    )

                    with(entryPoint.fullscreenSettingsDetailPaneEntryPoint) {
                        FullscreenSettingsPane(
                            fullscreenSettingsListPaneState = object : FullscreenSettingsListPaneState {
                                override val settingsCategory = settingsCategory

                                override val isListVisible: Boolean =
                                    !isDetailPresent || windowSizeClass.isWidthAtLeastBreakpoint(
                                        WindowSizeClass.WIDTH_DP_MEDIUM_LOWER_BOUND,
                                    )
                                override val isDetailVisible: Boolean =
                                    isDetailPresent || windowSizeClass.isWidthAtLeastBreakpoint(
                                        WindowSizeClass.WIDTH_DP_MEDIUM_LOWER_BOUND,
                                    )
                            },
                            fullscreenSettingsDetailPaneState = object : FullscreenSettingsDetailPaneState {
                                override val settingsCategory = settingsCategory
                                override val settingToScrollTo = null
                                override fun onFinishedScrollingToSetting() = Unit

                                override val isListVisible: Boolean =
                                    !isDetailPresent || windowSizeClass.isWidthAtLeastBreakpoint(
                                        WindowSizeClass.WIDTH_DP_MEDIUM_LOWER_BOUND,
                                    )
                                override val isDetailVisible: Boolean =
                                    isDetailPresent || windowSizeClass.isWidthAtLeastBreakpoint(
                                        WindowSizeClass.WIDTH_DP_MEDIUM_LOWER_BOUND,
                                    )
                            },
                            onBackButtonPressed = {
                                onBackButtonPressedCount++
                            },
                            setSettingsCategory = {
                                settingsCategory = it
                                isDetailPresent = true
                            },
                        )
                    }
                }
            }
        }

        onNodeWithText(resolver.invoke(Strings.Algorithm))
            .performScrollTo()
            .assertIsDisplayed()
            .assertHasClickAction()
            .assert(isSelectable().not())

        onNodeWithText(resolver.invoke(Strings.Visual))
            .performScrollTo()
            .assertIsDisplayed()
            .assertHasClickAction()
            .assert(isSelectable().not())

        onNodeWithText(resolver.invoke(Strings.FeatureFlags))
            .performScrollTo()
            .assertIsDisplayed()
            .assertHasClickAction()
            .assert(isSelectable().not())

        onNodeWithText(resolver.invoke(Strings.HashLifeAlgorithm))
            .assertDoesNotExist()

        onNodeWithContentDescription(resolver.invoke(Strings.Back))
            .assertIsDisplayed()
            .assertHasClickAction()
            .performClick()

        assertEquals(1, onBackButtonPressedCount)
    }

    @Test
    fun show_list_screen_is_displayed_correctly_with_medium_width() = runUiTest { uiGraph ->
        val entryPoint = uiGraph.fullscreenSettingsPaneTestsEntryPoint

        var onBackButtonPressedCount = 0

        var settingsCategory: SettingsCategory by mutableStateOf(SettingsCategory.Algorithm)
        var isDetailPresent by mutableStateOf(false)

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            DeviceConfigurationOverride(
                DeviceConfigurationOverride.ForcedSize(DpSize(700.dp, 500.dp)),
            ) {
                BoxWithConstraints {
                    val windowSizeClass = BREAKPOINTS_V1.computeWindowSizeClass(
                        widthDp = maxWidth.value,
                        heightDp = maxHeight.value,
                    )

                    with(entryPoint.fullscreenSettingsDetailPaneEntryPoint) {
                        FullscreenSettingsPane(
                            fullscreenSettingsListPaneState = object : FullscreenSettingsListPaneState {
                                override val settingsCategory = settingsCategory

                                override val isListVisible: Boolean =
                                    !isDetailPresent || windowSizeClass.isWidthAtLeastBreakpoint(
                                        WindowSizeClass.WIDTH_DP_MEDIUM_LOWER_BOUND,
                                    )
                                override val isDetailVisible: Boolean =
                                    isDetailPresent || windowSizeClass.isWidthAtLeastBreakpoint(
                                        WindowSizeClass.WIDTH_DP_MEDIUM_LOWER_BOUND,
                                    )
                            },
                            fullscreenSettingsDetailPaneState = object : FullscreenSettingsDetailPaneState {
                                override val settingsCategory = settingsCategory
                                override val settingToScrollTo = null
                                override fun onFinishedScrollingToSetting() = Unit

                                override val isListVisible: Boolean =
                                    !isDetailPresent || windowSizeClass.isWidthAtLeastBreakpoint(
                                        WindowSizeClass.WIDTH_DP_MEDIUM_LOWER_BOUND,
                                    )
                                override val isDetailVisible: Boolean =
                                    isDetailPresent || windowSizeClass.isWidthAtLeastBreakpoint(
                                        WindowSizeClass.WIDTH_DP_MEDIUM_LOWER_BOUND,
                                    )
                            },
                            onBackButtonPressed = {
                                onBackButtonPressedCount++
                            },
                            setSettingsCategory = {
                                settingsCategory = it
                                isDetailPresent = true
                            },
                        )
                    }
                }
            }
        }

        onNodeWithText(resolver.invoke(Strings.Algorithm))
            .performScrollTo()
            .assertIsDisplayed()
            .assertHasClickAction()
            .assertIsSelectable()
            .assertIsSelected()

        onNodeWithText(resolver.invoke(Strings.Visual))
            .performScrollTo()
            .assertIsDisplayed()
            .assertHasClickAction()
            .assertIsSelectable()
            .assertIsNotSelected()

        onNodeWithText(resolver.invoke(Strings.FeatureFlags))
            .performScrollTo()
            .assertIsDisplayed()
            .assertHasClickAction()
            .assertIsSelectable()
            .assertIsNotSelected()

        onNodeWithText(resolver.invoke(Strings.HashLifeAlgorithm))
            .assertExists()
            .assertHasClickAction()

        onNodeWithContentDescription(resolver.invoke(Strings.Back))
            .assertIsDisplayed()
            .assertHasClickAction()
            .performClick()

        assertEquals(1, onBackButtonPressedCount)
    }

    @Test
    fun show_detail_screen_is_displayed_correctly_with_compact_width() = runUiTest { uiGraph ->
        val entryPoint = uiGraph.fullscreenSettingsPaneTestsEntryPoint

        var onBackButtonPressedCount = 0

        var settingsCategory: SettingsCategory by mutableStateOf(SettingsCategory.Algorithm)
        var isDetailPresent by mutableStateOf(true)

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            DeviceConfigurationOverride(
                DeviceConfigurationOverride.ForcedSize(DpSize(500.dp, 500.dp)),
            ) {
                BoxWithConstraints {
                    val windowSizeClass = BREAKPOINTS_V1.computeWindowSizeClass(
                        widthDp = maxWidth.value,
                        heightDp = maxHeight.value,
                    )

                    with(entryPoint.fullscreenSettingsDetailPaneEntryPoint) {
                        FullscreenSettingsPane(
                            fullscreenSettingsListPaneState = object : FullscreenSettingsListPaneState {
                                override val settingsCategory = settingsCategory

                                override val isListVisible: Boolean =
                                    !isDetailPresent || windowSizeClass.isWidthAtLeastBreakpoint(
                                        WindowSizeClass.WIDTH_DP_MEDIUM_LOWER_BOUND,
                                    )
                                override val isDetailVisible: Boolean =
                                    isDetailPresent || windowSizeClass.isWidthAtLeastBreakpoint(
                                        WindowSizeClass.WIDTH_DP_MEDIUM_LOWER_BOUND,
                                    )
                            },
                            fullscreenSettingsDetailPaneState = object : FullscreenSettingsDetailPaneState {
                                override val settingsCategory = settingsCategory
                                override val settingToScrollTo = null
                                override fun onFinishedScrollingToSetting() = Unit

                                override val isListVisible: Boolean =
                                    !isDetailPresent || windowSizeClass.isWidthAtLeastBreakpoint(
                                        WindowSizeClass.WIDTH_DP_MEDIUM_LOWER_BOUND,
                                    )
                                override val isDetailVisible: Boolean =
                                    isDetailPresent || windowSizeClass.isWidthAtLeastBreakpoint(
                                        WindowSizeClass.WIDTH_DP_MEDIUM_LOWER_BOUND,
                                    )
                            },
                            onBackButtonPressed = {
                                onBackButtonPressedCount++
                            },
                            setSettingsCategory = {
                                settingsCategory = it
                                isDetailPresent = true
                            },
                        )
                    }
                }
            }
        }

        onNodeWithText(resolver.invoke(Strings.Visual))
            .assertDoesNotExist()

        onNodeWithText(resolver.invoke(Strings.FeatureFlags))
            .assertDoesNotExist()

        onNodeWithText(resolver.invoke(Strings.HashLifeAlgorithm))
            .assertExists()

        onNodeWithContentDescription(resolver.invoke(Strings.Back))
            .assertIsDisplayed()
            .assertHasClickAction()
            .performClick()

        assertEquals(1, onBackButtonPressedCount)
    }

    @Test
    fun show_detail_screen_is_displayed_correctly_with_medium_width() = runUiTest { uiGraph ->
        val entryPoint = uiGraph.fullscreenSettingsPaneTestsEntryPoint

        var onBackButtonPressedCount = 0

        var settingsCategory: SettingsCategory by mutableStateOf(SettingsCategory.Algorithm)
        var isDetailPresent by mutableStateOf(true)

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            DeviceConfigurationOverride(
                DeviceConfigurationOverride.ForcedSize(DpSize(700.dp, 500.dp)),
            ) {
                BoxWithConstraints {
                    val windowSizeClass = BREAKPOINTS_V1.computeWindowSizeClass(
                        widthDp = maxWidth.value,
                        heightDp = maxHeight.value,
                    )

                    with(entryPoint.fullscreenSettingsDetailPaneEntryPoint) {
                        FullscreenSettingsPane(
                            fullscreenSettingsListPaneState = object : FullscreenSettingsListPaneState {
                                override val settingsCategory = settingsCategory

                                override val isListVisible: Boolean =
                                    !isDetailPresent || windowSizeClass.isWidthAtLeastBreakpoint(
                                        WindowSizeClass.WIDTH_DP_MEDIUM_LOWER_BOUND,
                                    )
                                override val isDetailVisible: Boolean =
                                    isDetailPresent || windowSizeClass.isWidthAtLeastBreakpoint(
                                        WindowSizeClass.WIDTH_DP_MEDIUM_LOWER_BOUND,
                                    )
                            },
                            fullscreenSettingsDetailPaneState = object : FullscreenSettingsDetailPaneState {
                                override val settingsCategory = settingsCategory
                                override val settingToScrollTo = null
                                override fun onFinishedScrollingToSetting() = Unit

                                override val isListVisible: Boolean =
                                    !isDetailPresent || windowSizeClass.isWidthAtLeastBreakpoint(
                                        WindowSizeClass.WIDTH_DP_MEDIUM_LOWER_BOUND,
                                    )
                                override val isDetailVisible: Boolean =
                                    isDetailPresent || windowSizeClass.isWidthAtLeastBreakpoint(
                                        WindowSizeClass.WIDTH_DP_MEDIUM_LOWER_BOUND,
                                    )
                            },
                            onBackButtonPressed = {
                                onBackButtonPressedCount++
                            },
                            setSettingsCategory = {
                                settingsCategory = it
                                isDetailPresent = true
                            },
                        )
                    }
                }
            }
        }

        onNodeWithText(resolver.invoke(Strings.Algorithm))
            .performScrollTo()
            .assertIsDisplayed()
            .assertHasClickAction()

        onNodeWithText(resolver.invoke(Strings.Visual))
            .performScrollTo()
            .assertIsDisplayed()
            .assertHasClickAction()

        onNodeWithText(resolver.invoke(Strings.FeatureFlags))
            .performScrollTo()
            .assertIsDisplayed()
            .assertHasClickAction()

        onNodeWithText(resolver.invoke(Strings.HashLifeAlgorithm))
            .assertExists()
            .assertHasClickAction()

        onNodeWithContentDescription(resolver.invoke(Strings.Back))
            .assertIsDisplayed()
            .assertHasClickAction()
            .performClick()

        assertEquals(1, onBackButtonPressedCount)
    }

    @Test
    fun click_on_detail_is_displayed_correctly_with_compact_width() = runUiTest { uiGraph ->
        val entryPoint = uiGraph.fullscreenSettingsPaneTestsEntryPoint

        var settingsCategory: SettingsCategory by mutableStateOf(SettingsCategory.Algorithm)
        var isDetailPresent by mutableStateOf(false)

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            DeviceConfigurationOverride(
                DeviceConfigurationOverride.ForcedSize(DpSize(500.dp, 500.dp)),
            ) {
                BoxWithConstraints {
                    val windowSizeClass = BREAKPOINTS_V1.computeWindowSizeClass(
                        widthDp = maxWidth.value,
                        heightDp = maxHeight.value,
                    )

                    with(entryPoint.fullscreenSettingsDetailPaneEntryPoint) {
                        FullscreenSettingsPane(
                            fullscreenSettingsListPaneState = object : FullscreenSettingsListPaneState {
                                override val settingsCategory = settingsCategory

                                override val isListVisible: Boolean =
                                    !isDetailPresent || windowSizeClass.isWidthAtLeastBreakpoint(
                                        WindowSizeClass.WIDTH_DP_MEDIUM_LOWER_BOUND,
                                    )
                                override val isDetailVisible: Boolean =
                                    isDetailPresent || windowSizeClass.isWidthAtLeastBreakpoint(
                                        WindowSizeClass.WIDTH_DP_MEDIUM_LOWER_BOUND,
                                    )
                            },
                            fullscreenSettingsDetailPaneState = object : FullscreenSettingsDetailPaneState {
                                override val settingsCategory = settingsCategory
                                override val settingToScrollTo = null
                                override fun onFinishedScrollingToSetting() = Unit

                                override val isListVisible: Boolean =
                                    !isDetailPresent || windowSizeClass.isWidthAtLeastBreakpoint(
                                        WindowSizeClass.WIDTH_DP_MEDIUM_LOWER_BOUND,
                                    )
                                override val isDetailVisible: Boolean =
                                    isDetailPresent || windowSizeClass.isWidthAtLeastBreakpoint(
                                        WindowSizeClass.WIDTH_DP_MEDIUM_LOWER_BOUND,
                                    )
                            },
                            onBackButtonPressed = {},
                            setSettingsCategory = {
                                settingsCategory = it
                                isDetailPresent = true
                            },
                        )
                    }
                }
            }
        }

        onNodeWithText(resolver.invoke(Strings.FeatureFlags))
            .performScrollTo()
            .performClick()

        onNodeWithContentDescription(resolver.invoke(Strings.DoNotKeepProcess))
            .performScrollTo()
            .assertIsDisplayed()

        onNodeWithText(resolver.invoke(Strings.Algorithm))
            .assertDoesNotExist()

        onNodeWithText(resolver.invoke(Strings.Visual))
            .assertDoesNotExist()
    }

    @Test
    fun click_on_detail_is_displayed_correctly_with_medium_width() = runUiTest { uiGraph ->
        val entryPoint = uiGraph.fullscreenSettingsPaneTestsEntryPoint

        var settingsCategory: SettingsCategory by mutableStateOf(SettingsCategory.Algorithm)
        var isDetailPresent by mutableStateOf(false)

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            DeviceConfigurationOverride(
                DeviceConfigurationOverride.ForcedSize(DpSize(700.dp, 500.dp)),
            ) {
                BoxWithConstraints {
                    val windowSizeClass = BREAKPOINTS_V1.computeWindowSizeClass(
                        widthDp = maxWidth.value,
                        heightDp = maxHeight.value,
                    )

                    with(entryPoint.fullscreenSettingsDetailPaneEntryPoint) {
                        FullscreenSettingsPane(
                            fullscreenSettingsListPaneState = object : FullscreenSettingsListPaneState {
                                override val settingsCategory = settingsCategory

                                override val isListVisible: Boolean =
                                    !isDetailPresent || windowSizeClass.isWidthAtLeastBreakpoint(
                                        WindowSizeClass.WIDTH_DP_MEDIUM_LOWER_BOUND,
                                    )
                                override val isDetailVisible: Boolean =
                                    isDetailPresent || windowSizeClass.isWidthAtLeastBreakpoint(
                                        WindowSizeClass.WIDTH_DP_MEDIUM_LOWER_BOUND,
                                    )
                            },
                            fullscreenSettingsDetailPaneState = object : FullscreenSettingsDetailPaneState {
                                override val settingsCategory = settingsCategory
                                override val settingToScrollTo = null
                                override fun onFinishedScrollingToSetting() = Unit

                                override val isListVisible: Boolean =
                                    !isDetailPresent || windowSizeClass.isWidthAtLeastBreakpoint(
                                        WindowSizeClass.WIDTH_DP_MEDIUM_LOWER_BOUND,
                                    )
                                override val isDetailVisible: Boolean =
                                    isDetailPresent || windowSizeClass.isWidthAtLeastBreakpoint(
                                        WindowSizeClass.WIDTH_DP_MEDIUM_LOWER_BOUND,
                                    )
                            },
                            onBackButtonPressed = {},
                            setSettingsCategory = {
                                settingsCategory = it
                                isDetailPresent = true
                            },
                        )
                    }
                }
            }
        }

        onNodeWithText(resolver.invoke(Strings.FeatureFlags))
            .performScrollTo()
            .performClick()

        onNodeWithContentDescription(resolver.invoke(Strings.DoNotKeepProcess))
            .performScrollTo()
            .assertIsDisplayed()

        onNodeWithText(resolver.invoke(Strings.Algorithm))
            .performScrollTo()
            .assertIsDisplayed()
            .assertIsSelectable()
            .assertIsNotSelected()

        onNodeWithText(resolver.invoke(Strings.Visual))
            .performScrollTo()
            .assertIsDisplayed()
            .assertIsSelectable()
            .assertIsNotSelected()

        onNodeWithText(resolver.invoke(Strings.FeatureFlags))
            .performScrollTo()
            .assertIsDisplayed()
            .assertIsSelectable()
            .assertIsSelected()
    }

    @Test
    fun no_detail_to_scroll_to_is_displayed_correctly() = runUiTest { uiGraph ->
        val entryPoint = uiGraph.fullscreenSettingsPaneTestsEntryPoint

        var settingsCategory: SettingsCategory by mutableStateOf(SettingsCategory.Visual)
        var settingToScrollTo: Setting? by mutableStateOf(null)
        var isDetailPresent by mutableStateOf(true)

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            DeviceConfigurationOverride(
                DeviceConfigurationOverride.ForcedSize(DpSize(300.dp, 300.dp)),
            ) {
                with(entryPoint.fullscreenSettingsDetailPaneEntryPoint) {
                    FullscreenSettingsPane(
                        fullscreenSettingsListPaneState = object : FullscreenSettingsListPaneState {
                            override val settingsCategory = settingsCategory

                            override val isListVisible: Boolean = !isDetailPresent
                            override val isDetailVisible: Boolean = isDetailPresent
                        },
                        fullscreenSettingsDetailPaneState = object : FullscreenSettingsDetailPaneState {
                            override val settingsCategory = settingsCategory
                            override val settingToScrollTo = settingToScrollTo
                            override fun onFinishedScrollingToSetting() {
                                settingToScrollTo = null
                            }

                            override val isListVisible: Boolean = !isDetailPresent
                            override val isDetailVisible: Boolean = isDetailPresent
                        },
                        onBackButtonPressed = {},
                        setSettingsCategory = {},
                    )
                }
            }
        }

        onNode(
            hasScrollAction().and(
                hasAnyDescendant(
                    hasContentDescription(
                        resolver.invoke(Strings.CornerFractionLabelAndValue(0f)),
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
    fun detail_to_scroll_to_is_displayed_correctly() = runUiTest { uiGraph ->
        val entryPoint = uiGraph.fullscreenSettingsPaneTestsEntryPoint

        var settingsCategory: SettingsCategory by mutableStateOf(SettingsCategory.Visual)
        var settingToScrollTo: Setting? by mutableStateOf(Setting.CellShapeConfig)
        var isDetailPresent by mutableStateOf(true)

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            DeviceConfigurationOverride(
                DeviceConfigurationOverride.ForcedSize(DpSize(300.dp, 300.dp)),
            ) {
                with(entryPoint.fullscreenSettingsDetailPaneEntryPoint) {
                    FullscreenSettingsPane(
                        fullscreenSettingsListPaneState = object : FullscreenSettingsListPaneState {
                            override val settingsCategory = settingsCategory

                            override val isListVisible: Boolean = !isDetailPresent
                            override val isDetailVisible: Boolean = isDetailPresent
                        },
                        fullscreenSettingsDetailPaneState = object : FullscreenSettingsDetailPaneState {
                            override val settingsCategory = settingsCategory
                            override val settingToScrollTo = settingToScrollTo
                            override fun onFinishedScrollingToSetting() {
                                settingToScrollTo = null
                            }

                            override val isListVisible: Boolean = !isDetailPresent
                            override val isDetailVisible: Boolean = isDetailPresent
                        },
                        onBackButtonPressed = {},
                        setSettingsCategory = {},
                    )
                }
            }
        }

        waitForIdle()

        assertNull(settingToScrollTo)

        onNode(
            hasScrollAction().and(
                hasAnyDescendant(
                    hasContentDescription(
                        resolver.invoke(Strings.CornerFractionLabelAndValue(0f)),
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
    fun reducing_size_keeps_selected_detail() = runUiTest { uiGraph ->
        val entryPoint = uiGraph.fullscreenSettingsPaneTestsEntryPoint

        var settingsCategory: SettingsCategory by mutableStateOf(SettingsCategory.Algorithm)
        var isDetailPresent by mutableStateOf(false)

        var size by mutableStateOf(DpSize(700.dp, 500.dp))

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            DeviceConfigurationOverride(
                DeviceConfigurationOverride.ForcedSize(size),
            ) {
                BoxWithConstraints {
                    val windowSizeClass = BREAKPOINTS_V1.computeWindowSizeClass(
                        widthDp = maxWidth.value,
                        heightDp = maxHeight.value,
                    )

                    with(entryPoint.fullscreenSettingsDetailPaneEntryPoint) {
                        FullscreenSettingsPane(
                            fullscreenSettingsListPaneState = object : FullscreenSettingsListPaneState {
                                override val settingsCategory = settingsCategory

                                override val isListVisible: Boolean =
                                    !isDetailPresent || windowSizeClass.isWidthAtLeastBreakpoint(
                                        WindowSizeClass.WIDTH_DP_MEDIUM_LOWER_BOUND,
                                    )
                                override val isDetailVisible: Boolean =
                                    isDetailPresent || windowSizeClass.isWidthAtLeastBreakpoint(
                                        WindowSizeClass.WIDTH_DP_MEDIUM_LOWER_BOUND,
                                    )
                            },
                            fullscreenSettingsDetailPaneState = object : FullscreenSettingsDetailPaneState {
                                override val settingsCategory = settingsCategory
                                override val settingToScrollTo = null
                                override fun onFinishedScrollingToSetting() = Unit

                                override val isListVisible: Boolean =
                                    !isDetailPresent || windowSizeClass.isWidthAtLeastBreakpoint(
                                        WindowSizeClass.WIDTH_DP_MEDIUM_LOWER_BOUND,
                                    )
                                override val isDetailVisible: Boolean =
                                    isDetailPresent || windowSizeClass.isWidthAtLeastBreakpoint(
                                        WindowSizeClass.WIDTH_DP_MEDIUM_LOWER_BOUND,
                                    )
                            },
                            onBackButtonPressed = {},
                            setSettingsCategory = {
                                settingsCategory = it
                                isDetailPresent = true
                            },
                        )
                    }
                }
            }
        }

        onNodeWithText(resolver.invoke(Strings.Visual))
            .performClick()

        size = DpSize(500.dp, 500.dp)

        onNodeWithContentDescription(
            resolver.invoke(Strings.CornerFractionLabelAndValue(0f)),
        )
            .performScrollTo()
            .assertIsDisplayed()
    }

    @Test
    fun expanding_size_keeps_selected_detail() = runUiTest { uiGraph ->
        val entryPoint = uiGraph.fullscreenSettingsPaneTestsEntryPoint

        var settingsCategory: SettingsCategory by mutableStateOf(SettingsCategory.Algorithm)
        var isDetailPresent by mutableStateOf(false)
        var size by mutableStateOf(DpSize(500.dp, 500.dp))

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            DeviceConfigurationOverride(
                DeviceConfigurationOverride.ForcedSize(size),
            ) {
                BoxWithConstraints {
                    val windowSizeClass = BREAKPOINTS_V1.computeWindowSizeClass(
                        widthDp = maxWidth.value,
                        heightDp = maxHeight.value,
                    )

                    with(entryPoint.fullscreenSettingsDetailPaneEntryPoint) {
                        FullscreenSettingsPane(
                            fullscreenSettingsListPaneState = object : FullscreenSettingsListPaneState {
                                override val settingsCategory = settingsCategory

                                override val isListVisible: Boolean =
                                    !isDetailPresent || windowSizeClass.isWidthAtLeastBreakpoint(
                                        WindowSizeClass.WIDTH_DP_MEDIUM_LOWER_BOUND,
                                    )
                                override val isDetailVisible: Boolean =
                                    isDetailPresent || windowSizeClass.isWidthAtLeastBreakpoint(
                                        WindowSizeClass.WIDTH_DP_MEDIUM_LOWER_BOUND,
                                    )
                            },
                            fullscreenSettingsDetailPaneState = object : FullscreenSettingsDetailPaneState {
                                override val settingsCategory = settingsCategory
                                override val settingToScrollTo = null
                                override fun onFinishedScrollingToSetting() = Unit

                                override val isListVisible: Boolean =
                                    !isDetailPresent || windowSizeClass.isWidthAtLeastBreakpoint(
                                        WindowSizeClass.WIDTH_DP_MEDIUM_LOWER_BOUND,
                                    )
                                override val isDetailVisible: Boolean =
                                    isDetailPresent || windowSizeClass.isWidthAtLeastBreakpoint(
                                        WindowSizeClass.WIDTH_DP_MEDIUM_LOWER_BOUND,
                                    )
                            },
                            onBackButtonPressed = {},
                            setSettingsCategory = {
                                settingsCategory = it
                                isDetailPresent = true
                            },
                        )
                    }
                }
            }
        }

        onNodeWithText(resolver.invoke(Strings.Visual))
            .performClick()

        size = DpSize(700.dp, 500.dp)

        onNodeWithContentDescription(
            resolver.invoke(Strings.CornerFractionLabelAndValue(0f)),
        )
            .performScrollTo()
            .assertIsDisplayed()

        onNodeWithText(resolver.invoke(Strings.Visual))
            .performScrollTo()
            .assertIsDisplayed()
            .assertIsSelectable()
            .assertIsSelected()
    }
}
