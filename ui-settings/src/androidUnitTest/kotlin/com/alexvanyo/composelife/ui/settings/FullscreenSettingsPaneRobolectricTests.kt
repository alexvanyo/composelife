/*
 * Copyright 2024 The Android Open Source Project
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

import android.view.View
import androidx.compose.foundation.layout.BoxWithConstraints
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.setValue
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.platform.LocalView
import androidx.compose.ui.semantics.SemanticsProperties
import androidx.compose.ui.test.ExperimentalTestApi
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
import androidx.window.core.layout.WindowSizeClass
import androidx.window.core.layout.WindowSizeClass.Companion.BREAKPOINTS_V1
import androidx.window.core.layout.computeWindowSizeClass
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResolver
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferences
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
import org.robolectric.RuntimeEnvironment
import org.robolectric.annotation.Config
import org.robolectric.shadow.api.Shadow
import org.robolectric.shadows.ShadowViewRootImpl
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNull

@Suppress("LargeClass")
@OptIn(ExperimentalTestApi::class)
class FullscreenSettingsPaneRobolectricTests : BaseUiInjectTest<
    TestComposeLifeApplicationComponent,
    TestComposeLifeApplicationEntryPoint,
    TestComposeLifeUiComponent,
    >(
    TestComposeLifeApplicationComponent::createComponent,
    TestComposeLifeUiComponent.Companion::createComponent,
) {
    private val fullscreenSettingsDetailPaneLocalEntryPoint = object : FullscreenSettingsDetailPaneLocalEntryPoint {
        override val preferences = LoadedComposeLifePreferences.Defaults
    }

    @Config(qualifiers = "w500dp-h500dp")
    @Test
    fun show_list_screen_is_displayed_correctly_with_compact_width() = runUiTest { uiComponent, composeUiTest ->
        val fullscreenSettingsDetailPaneInjectEntryPoint: FullscreenSettingsDetailPaneInjectEntryPoint =
            uiComponent.entryPoint

        val entryPoint = object :
            FullscreenSettingsDetailPaneInjectEntryPoint by fullscreenSettingsDetailPaneInjectEntryPoint,
            FullscreenSettingsDetailPaneLocalEntryPoint by fullscreenSettingsDetailPaneLocalEntryPoint {}

        var onBackButtonPressedCount = 0

        var settingsCategory: SettingsCategory by mutableStateOf(SettingsCategory.Algorithm)
        var isDetailPresent by mutableStateOf(false)

        lateinit var resolver: (ParameterizedString) -> String

        composeUiTest.setContent {
            resolver = parameterizedStringResolver()
            BoxWithConstraints {
                val windowSize = DpSize(maxWidth, maxHeight)
                val windowSizeClass = with(LocalDensity.current) {
                    BREAKPOINTS_V1.computeWindowSizeClass(
                        widthDp = windowSize.width.value,
                        heightDp = windowSize.height.value,
                    )
                }

                with(entryPoint) {
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

        composeUiTest.onNodeWithText(resolver.invoke(Strings.Algorithm))
            .performScrollTo()
            .assertIsDisplayed()
            .assertHasClickAction()
            .assert(isSelectable().not())

        composeUiTest.onNodeWithText(resolver.invoke(Strings.Visual))
            .performScrollTo()
            .assertIsDisplayed()
            .assertHasClickAction()
            .assert(isSelectable().not())

        composeUiTest.onNodeWithText(resolver.invoke(Strings.FeatureFlags))
            .performScrollTo()
            .assertIsDisplayed()
            .assertHasClickAction()
            .assert(isSelectable().not())

        composeUiTest.onNodeWithText(resolver.invoke(Strings.HashLifeAlgorithm))
            .assertDoesNotExist()

        composeUiTest.onNodeWithContentDescription(resolver.invoke(Strings.Back))
            .assertIsDisplayed()
            .assertHasClickAction()
            .performClick()

        assertEquals(1, onBackButtonPressedCount)
    }

    @Config(qualifiers = "w700dp-h500dp")
    @Test
    fun show_list_screen_is_displayed_correctly_with_medium_width() = runUiTest { uiComponent, composeUiTest ->
        val fullscreenSettingsDetailPaneInjectEntryPoint: FullscreenSettingsDetailPaneInjectEntryPoint =
            uiComponent.entryPoint

        val entryPoint = object :
            FullscreenSettingsDetailPaneInjectEntryPoint by fullscreenSettingsDetailPaneInjectEntryPoint,
            FullscreenSettingsDetailPaneLocalEntryPoint by fullscreenSettingsDetailPaneLocalEntryPoint {}

        var onBackButtonPressedCount = 0

        var settingsCategory: SettingsCategory by mutableStateOf(SettingsCategory.Algorithm)
        var isDetailPresent by mutableStateOf(false)

        lateinit var resolver: (ParameterizedString) -> String

        composeUiTest.setContent {
            resolver = parameterizedStringResolver()
            BoxWithConstraints {
                val windowSize = DpSize(maxWidth, maxHeight)
                val windowSizeClass = with(LocalDensity.current) {
                    BREAKPOINTS_V1.computeWindowSizeClass(
                        widthDp = windowSize.width.value,
                        heightDp = windowSize.height.value,
                    )
                }

                with(entryPoint) {
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

        composeUiTest.onNodeWithText(resolver.invoke(Strings.Algorithm))
            .performScrollTo()
            .assertIsDisplayed()
            .assertHasClickAction()
            .assertIsSelectable()
            .assertIsSelected()

        composeUiTest.onNodeWithText(resolver.invoke(Strings.Visual))
            .performScrollTo()
            .assertIsDisplayed()
            .assertHasClickAction()
            .assertIsSelectable()
            .assertIsNotSelected()

        composeUiTest.onNodeWithText(resolver.invoke(Strings.FeatureFlags))
            .performScrollTo()
            .assertIsDisplayed()
            .assertHasClickAction()
            .assertIsSelectable()
            .assertIsNotSelected()

        composeUiTest.onNodeWithText(resolver.invoke(Strings.HashLifeAlgorithm))
            .assertExists()
            .assertHasClickAction()

        composeUiTest.onNodeWithContentDescription(resolver.invoke(Strings.Back))
            .assertIsDisplayed()
            .assertHasClickAction()
            .performClick()

        assertEquals(1, onBackButtonPressedCount)
    }

    @Config(qualifiers = "w500dp-h500dp")
    @Test
    fun show_detail_screen_is_displayed_correctly_with_compact_width() = runUiTest { uiComponent, composeUiTest ->
        val fullscreenSettingsDetailPaneInjectEntryPoint: FullscreenSettingsDetailPaneInjectEntryPoint =
            uiComponent.entryPoint

        val entryPoint = object :
            FullscreenSettingsDetailPaneInjectEntryPoint by fullscreenSettingsDetailPaneInjectEntryPoint,
            FullscreenSettingsDetailPaneLocalEntryPoint by fullscreenSettingsDetailPaneLocalEntryPoint {}

        var onBackButtonPressedCount = 0

        var settingsCategory: SettingsCategory by mutableStateOf(SettingsCategory.Algorithm)
        var isDetailPresent by mutableStateOf(true)

        lateinit var resolver: (ParameterizedString) -> String

        composeUiTest.setContent {
            resolver = parameterizedStringResolver()
            BoxWithConstraints {
                val windowSize = DpSize(maxWidth, maxHeight)
                val windowSizeClass = with(LocalDensity.current) {
                    BREAKPOINTS_V1.computeWindowSizeClass(
                        widthDp = windowSize.width.value,
                        heightDp = windowSize.height.value,
                    )
                }

                with(entryPoint) {
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

        composeUiTest.onNodeWithText(resolver.invoke(Strings.Visual))
            .assertDoesNotExist()

        composeUiTest.onNodeWithText(resolver.invoke(Strings.FeatureFlags))
            .assertDoesNotExist()

        composeUiTest.onNodeWithText(resolver.invoke(Strings.HashLifeAlgorithm))
            .assertExists()

        composeUiTest.onNodeWithContentDescription(resolver.invoke(Strings.Back))
            .assertIsDisplayed()
            .assertHasClickAction()
            .performClick()

        assertEquals(1, onBackButtonPressedCount)
    }

    @Config(qualifiers = "w700dp-h500dp")
    @Test
    fun show_detail_screen_is_displayed_correctly_with_medium_width() = runUiTest { uiComponent, composeUiTest ->
        val fullscreenSettingsDetailPaneInjectEntryPoint: FullscreenSettingsDetailPaneInjectEntryPoint =
            uiComponent.entryPoint

        val entryPoint = object :
            FullscreenSettingsDetailPaneInjectEntryPoint by fullscreenSettingsDetailPaneInjectEntryPoint,
            FullscreenSettingsDetailPaneLocalEntryPoint by fullscreenSettingsDetailPaneLocalEntryPoint {}

        var onBackButtonPressedCount = 0

        var settingsCategory: SettingsCategory by mutableStateOf(SettingsCategory.Algorithm)
        var isDetailPresent by mutableStateOf(true)

        lateinit var resolver: (ParameterizedString) -> String

        composeUiTest.setContent {
            resolver = parameterizedStringResolver()
            BoxWithConstraints {
                val windowSize = DpSize(maxWidth, maxHeight)
                val windowSizeClass = with(LocalDensity.current) {
                    BREAKPOINTS_V1.computeWindowSizeClass(
                        widthDp = windowSize.width.value,
                        heightDp = windowSize.height.value,
                    )
                }

                with(entryPoint) {
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

        composeUiTest.onNodeWithText(resolver.invoke(Strings.Algorithm))
            .performScrollTo()
            .assertIsDisplayed()
            .assertHasClickAction()

        composeUiTest.onNodeWithText(resolver.invoke(Strings.Visual))
            .performScrollTo()
            .assertIsDisplayed()
            .assertHasClickAction()

        composeUiTest.onNodeWithText(resolver.invoke(Strings.FeatureFlags))
            .performScrollTo()
            .assertIsDisplayed()
            .assertHasClickAction()

        composeUiTest.onNodeWithText(resolver.invoke(Strings.HashLifeAlgorithm))
            .assertExists()
            .assertHasClickAction()

        composeUiTest.onNodeWithContentDescription(resolver.invoke(Strings.Back))
            .assertIsDisplayed()
            .assertHasClickAction()
            .performClick()

        assertEquals(1, onBackButtonPressedCount)
    }

    @Config(qualifiers = "w500dp-h500dp")
    @Test
    fun click_on_detail_is_displayed_correctly_with_compact_width() = runUiTest { uiComponent, composeUiTest ->
        val fullscreenSettingsDetailPaneInjectEntryPoint: FullscreenSettingsDetailPaneInjectEntryPoint =
            uiComponent.entryPoint

        val entryPoint = object :
            FullscreenSettingsDetailPaneInjectEntryPoint by fullscreenSettingsDetailPaneInjectEntryPoint,
            FullscreenSettingsDetailPaneLocalEntryPoint by fullscreenSettingsDetailPaneLocalEntryPoint {}

        var settingsCategory: SettingsCategory by mutableStateOf(SettingsCategory.Algorithm)
        var isDetailPresent by mutableStateOf(false)

        lateinit var resolver: (ParameterizedString) -> String

        composeUiTest.setContent {
            resolver = parameterizedStringResolver()
            BoxWithConstraints {
                val windowSize = DpSize(maxWidth, maxHeight)
                val windowSizeClass = with(LocalDensity.current) {
                    BREAKPOINTS_V1.computeWindowSizeClass(
                        widthDp = windowSize.width.value,
                        heightDp = windowSize.height.value,
                    )
                }

                with(entryPoint) {
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

        composeUiTest.onNodeWithText(resolver.invoke(Strings.FeatureFlags))
            .performScrollTo()
            .performClick()

        composeUiTest.onNodeWithContentDescription(resolver.invoke(Strings.DoNotKeepProcess))
            .performScrollTo()
            .assertIsDisplayed()

        composeUiTest.onNodeWithText(resolver.invoke(Strings.Algorithm))
            .assertDoesNotExist()

        composeUiTest.onNodeWithText(resolver.invoke(Strings.Visual))
            .assertDoesNotExist()
    }

    @Config(qualifiers = "w700dp-h500dp")
    @Test
    fun click_on_detail_is_displayed_correctly_with_medium_width() = runUiTest { uiComponent, composeUiTest ->
        val fullscreenSettingsDetailPaneInjectEntryPoint: FullscreenSettingsDetailPaneInjectEntryPoint =
            uiComponent.entryPoint

        val entryPoint = object :
            FullscreenSettingsDetailPaneInjectEntryPoint by fullscreenSettingsDetailPaneInjectEntryPoint,
            FullscreenSettingsDetailPaneLocalEntryPoint by fullscreenSettingsDetailPaneLocalEntryPoint {}

        var settingsCategory: SettingsCategory by mutableStateOf(SettingsCategory.Algorithm)
        var isDetailPresent by mutableStateOf(false)

        lateinit var resolver: (ParameterizedString) -> String

        composeUiTest.setContent {
            resolver = parameterizedStringResolver()
            BoxWithConstraints {
                val windowSize = DpSize(maxWidth, maxHeight)
                val windowSizeClass = with(LocalDensity.current) {
                    BREAKPOINTS_V1.computeWindowSizeClass(
                        widthDp = windowSize.width.value,
                        heightDp = windowSize.height.value,
                    )
                }

                with(entryPoint) {
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

        composeUiTest.onNodeWithText(resolver.invoke(Strings.FeatureFlags))
            .performScrollTo()
            .performClick()

        composeUiTest.onNodeWithContentDescription(resolver.invoke(Strings.DoNotKeepProcess))
            .performScrollTo()
            .assertIsDisplayed()

        composeUiTest.onNodeWithText(resolver.invoke(Strings.Algorithm))
            .performScrollTo()
            .assertIsDisplayed()
            .assertIsSelectable()
            .assertIsNotSelected()

        composeUiTest.onNodeWithText(resolver.invoke(Strings.Visual))
            .performScrollTo()
            .assertIsDisplayed()
            .assertIsSelectable()
            .assertIsNotSelected()

        composeUiTest.onNodeWithText(resolver.invoke(Strings.FeatureFlags))
            .performScrollTo()
            .assertIsDisplayed()
            .assertIsSelectable()
            .assertIsSelected()
    }

    @Config(qualifiers = "w300dp-h300dp")
    @Test
    fun no_detail_to_scroll_to_is_displayed_correctly() = runUiTest { uiComponent, composeUiTest ->
        val fullscreenSettingsDetailPaneInjectEntryPoint: FullscreenSettingsDetailPaneInjectEntryPoint =
            uiComponent.entryPoint

        val entryPoint = object :
            FullscreenSettingsDetailPaneInjectEntryPoint by fullscreenSettingsDetailPaneInjectEntryPoint,
            FullscreenSettingsDetailPaneLocalEntryPoint by fullscreenSettingsDetailPaneLocalEntryPoint {}

        val settingsCategory: SettingsCategory by mutableStateOf(SettingsCategory.Visual)
        var settingToScrollTo: Setting? by mutableStateOf(null)
        val isDetailPresent by mutableStateOf(true)

        lateinit var resolver: (ParameterizedString) -> String

        composeUiTest.setContent {
            resolver = parameterizedStringResolver()
            with(entryPoint) {
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

        composeUiTest.onNode(
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

    @Config(qualifiers = "w300dp-h300dp")
    @Test
    fun detail_to_scroll_to_is_displayed_correctly() = runUiTest { uiComponent, composeUiTest ->
        val fullscreenSettingsDetailPaneInjectEntryPoint: FullscreenSettingsDetailPaneInjectEntryPoint =
            uiComponent.entryPoint

        val entryPoint = object :
            FullscreenSettingsDetailPaneInjectEntryPoint by fullscreenSettingsDetailPaneInjectEntryPoint,
            FullscreenSettingsDetailPaneLocalEntryPoint by fullscreenSettingsDetailPaneLocalEntryPoint {}

        val settingsCategory: SettingsCategory by mutableStateOf(SettingsCategory.Visual)
        var settingToScrollTo: Setting? by mutableStateOf(Setting.CellShapeConfig)
        val isDetailPresent by mutableStateOf(true)

        lateinit var resolver: (ParameterizedString) -> String

        composeUiTest.setContent {
            resolver = parameterizedStringResolver()
            with(entryPoint) {
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

        composeUiTest.waitForIdle()

        assertNull(settingToScrollTo)

        composeUiTest.onNode(
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

    @Config(qualifiers = "w700dp-h500dp")
    @Test
    fun reducing_size_keeps_selected_detail() = runUiTest { uiComponent, composeUiTest ->
        val fullscreenSettingsDetailPaneInjectEntryPoint: FullscreenSettingsDetailPaneInjectEntryPoint =
            uiComponent.entryPoint

        val entryPoint = object :
            FullscreenSettingsDetailPaneInjectEntryPoint by fullscreenSettingsDetailPaneInjectEntryPoint,
            FullscreenSettingsDetailPaneLocalEntryPoint by fullscreenSettingsDetailPaneLocalEntryPoint {}

        var settingsCategory: SettingsCategory by mutableStateOf(SettingsCategory.Algorithm)
        var isDetailPresent by mutableStateOf(false)

        lateinit var view: View
        lateinit var resolver: (ParameterizedString) -> String

        composeUiTest.setContent {
            view = LocalView.current
            resolver = parameterizedStringResolver()
            BoxWithConstraints {
                val windowSize = DpSize(maxWidth, maxHeight)
                val windowSizeClass = with(LocalDensity.current) {
                    BREAKPOINTS_V1.computeWindowSizeClass(
                        widthDp = windowSize.width.value,
                        heightDp = windowSize.height.value,
                    )
                }

                with(entryPoint) {
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

        composeUiTest.onNodeWithText(resolver.invoke(Strings.Visual))
            .performClick()

        RuntimeEnvironment.setQualifiers("w500dp-h500dp")
        Shadow.extract<ShadowViewRootImpl>(view.rootView.parent).callDispatchResized()
        composeUiTest.waitForIdle()

        composeUiTest.onNodeWithContentDescription(
            resolver.invoke(Strings.CornerFractionLabelAndValue(0f)),
        )
            .performScrollTo()
            .assertIsDisplayed()
    }

    @Config(qualifiers = "w500dp-h500dp")
    @Test
    fun expanding_size_keeps_selected_detail() = runUiTest { uiComponent, composeUiTest ->
        val fullscreenSettingsDetailPaneInjectEntryPoint: FullscreenSettingsDetailPaneInjectEntryPoint =
            uiComponent.entryPoint

        val entryPoint = object :
            FullscreenSettingsDetailPaneInjectEntryPoint by fullscreenSettingsDetailPaneInjectEntryPoint,
            FullscreenSettingsDetailPaneLocalEntryPoint by fullscreenSettingsDetailPaneLocalEntryPoint {}

        var settingsCategory: SettingsCategory by mutableStateOf(SettingsCategory.Algorithm)
        var isDetailPresent by mutableStateOf(false)

        lateinit var view: View
        lateinit var resolver: (ParameterizedString) -> String

        composeUiTest.setContent {
            view = LocalView.current
            resolver = parameterizedStringResolver()
            BoxWithConstraints {
                val windowSize = DpSize(maxWidth, maxHeight)
                val windowSizeClass = with(LocalDensity.current) {
                    BREAKPOINTS_V1.computeWindowSizeClass(
                        widthDp = windowSize.width.value,
                        heightDp = windowSize.height.value,
                    )
                }

                with(entryPoint) {
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

        composeUiTest.onNodeWithText(resolver.invoke(Strings.Visual))
            .performClick()

        RuntimeEnvironment.setQualifiers("w700dp-h500dp")
        Shadow.extract<ShadowViewRootImpl>(view.rootView.parent).callDispatchResized()
        composeUiTest.waitForIdle()

        composeUiTest.onNodeWithContentDescription(
            resolver.invoke(Strings.CornerFractionLabelAndValue(0f)),
        )
            .performScrollTo()
            .assertIsDisplayed()

        composeUiTest.onNodeWithText(resolver.invoke(Strings.Visual))
            .performScrollTo()
            .assertIsDisplayed()
            .assertIsSelectable()
            .assertIsSelected()
    }
}
