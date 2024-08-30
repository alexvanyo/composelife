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

package com.alexvanyo.composelife.ui.app.action.settings

import android.view.View
import androidx.compose.foundation.layout.BoxWithConstraints
import androidx.compose.material3.windowsizeclass.ExperimentalMaterial3WindowSizeClassApi
import androidx.compose.material3.windowsizeclass.WindowSizeClass
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
import androidx.compose.ui.unit.IntSize
import androidx.compose.ui.unit.toSize
import com.alexvanyo.composelife.kmpandroidrunner.KmpAndroidJUnit4
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResolver
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferences
import com.alexvanyo.composelife.test.BaseUiInjectTest
import com.alexvanyo.composelife.test.runUiTest
import com.alexvanyo.composelife.ui.app.ComposeLifeNavigation
import com.alexvanyo.composelife.ui.app.ComposeLifeUiNavigation
import com.alexvanyo.composelife.ui.app.TestComposeLifeApplicationComponent
import com.alexvanyo.composelife.ui.app.TestComposeLifeUiComponent
import com.alexvanyo.composelife.ui.app.createComponent
import com.alexvanyo.composelife.ui.app.resources.Algorithm
import com.alexvanyo.composelife.ui.app.resources.Back
import com.alexvanyo.composelife.ui.app.resources.CornerFractionLabelAndValue
import com.alexvanyo.composelife.ui.app.resources.DoNotKeepProcess
import com.alexvanyo.composelife.ui.app.resources.FeatureFlags
import com.alexvanyo.composelife.ui.app.resources.HashLifeAlgorithm
import com.alexvanyo.composelife.ui.app.resources.Strings
import com.alexvanyo.composelife.ui.app.resources.Visual
import org.junit.runner.RunWith
import org.robolectric.RuntimeEnvironment
import org.robolectric.annotation.Config
import org.robolectric.shadow.api.Shadow
import org.robolectric.shadows.ShadowViewRootImpl
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNull

@Suppress("LargeClass")
@OptIn(ExperimentalMaterial3WindowSizeClassApi::class, ExperimentalTestApi::class)
@RunWith(KmpAndroidJUnit4::class)
class FullscreenSettingsPaneRobolectricTests :
    BaseUiInjectTest<TestComposeLifeApplicationComponent, TestComposeLifeUiComponent>(
        TestComposeLifeApplicationComponent::createComponent,
        TestComposeLifeUiComponent::createComponent,
    ) {
    private val fullscreenSettingsDetailPaneLocalEntryPoint = object : FullscreenSettingsDetailPaneLocalEntryPoint {
        override val preferences = LoadedComposeLifePreferences.Defaults
    }

    @Config(qualifiers = "w500dp-h500dp")
    @Test
    fun show_list_screen_is_displayed_correctly_with_compact_width() = runUiTest {
        val fullscreenSettingsDetailPaneInjectEntryPoint: FullscreenSettingsDetailPaneInjectEntryPoint =
            uiComponent.entryPoint

        val entryPoint = object :
            FullscreenSettingsDetailPaneInjectEntryPoint by fullscreenSettingsDetailPaneInjectEntryPoint,
            FullscreenSettingsDetailPaneLocalEntryPoint by fullscreenSettingsDetailPaneLocalEntryPoint {}

        var onBackButtonPressedCount = 0

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
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

    @Config(qualifiers = "w700dp-h500dp")
    @Test
    fun show_list_screen_is_displayed_correctly_with_medium_width() = runUiTest {
        val fullscreenSettingsDetailPaneInjectEntryPoint: FullscreenSettingsDetailPaneInjectEntryPoint =
            uiComponent.entryPoint

        val entryPoint = object :
            FullscreenSettingsDetailPaneInjectEntryPoint by fullscreenSettingsDetailPaneInjectEntryPoint,
            FullscreenSettingsDetailPaneLocalEntryPoint by fullscreenSettingsDetailPaneLocalEntryPoint {}

        var onBackButtonPressedCount = 0

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
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

    @Config(qualifiers = "w500dp-h500dp")
    @Test
    fun show_detail_screen_is_displayed_correctly_with_compact_width() = runUiTest {
        val fullscreenSettingsDetailPaneInjectEntryPoint: FullscreenSettingsDetailPaneInjectEntryPoint =
            uiComponent.entryPoint

        val entryPoint = object :
            FullscreenSettingsDetailPaneInjectEntryPoint by fullscreenSettingsDetailPaneInjectEntryPoint,
            FullscreenSettingsDetailPaneLocalEntryPoint by fullscreenSettingsDetailPaneLocalEntryPoint {}

        var onBackButtonPressedCount = 0

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
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

    @Config(qualifiers = "w700dp-h500dp")
    @Test
    fun show_detail_screen_is_displayed_correctly_with_medium_width() = runUiTest {
        val fullscreenSettingsDetailPaneInjectEntryPoint: FullscreenSettingsDetailPaneInjectEntryPoint =
            uiComponent.entryPoint

        val entryPoint = object :
            FullscreenSettingsDetailPaneInjectEntryPoint by fullscreenSettingsDetailPaneInjectEntryPoint,
            FullscreenSettingsDetailPaneLocalEntryPoint by fullscreenSettingsDetailPaneLocalEntryPoint {}

        var onBackButtonPressedCount = 0

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
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

    @Config(qualifiers = "w500dp-h500dp")
    @Test
    fun click_on_detail_is_displayed_correctly_with_compact_width() = runUiTest {
        val fullscreenSettingsDetailPaneInjectEntryPoint: FullscreenSettingsDetailPaneInjectEntryPoint =
            uiComponent.entryPoint

        val entryPoint = object :
            FullscreenSettingsDetailPaneInjectEntryPoint by fullscreenSettingsDetailPaneInjectEntryPoint,
            FullscreenSettingsDetailPaneLocalEntryPoint by fullscreenSettingsDetailPaneLocalEntryPoint {}

        val listNavValue = ComposeLifeNavigation.FullscreenSettingsList(
            initialSettingsCategory = SettingsCategory.Algorithm,
        )
        var isDetailPresent by mutableStateOf(false)

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
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

    @Config(qualifiers = "w700dp-h500dp")
    @Test
    fun click_on_detail_is_displayed_correctly_with_medium_width() = runUiTest {
        val fullscreenSettingsDetailPaneInjectEntryPoint: FullscreenSettingsDetailPaneInjectEntryPoint =
            uiComponent.entryPoint

        val entryPoint = object :
            FullscreenSettingsDetailPaneInjectEntryPoint by fullscreenSettingsDetailPaneInjectEntryPoint,
            FullscreenSettingsDetailPaneLocalEntryPoint by fullscreenSettingsDetailPaneLocalEntryPoint {}

        val listNavValue = ComposeLifeNavigation.FullscreenSettingsList(
            initialSettingsCategory = SettingsCategory.Algorithm,
        )
        var isDetailPresent by mutableStateOf(false)

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
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

    @Config(qualifiers = "w300dp-h300dp")
    @Test
    fun no_detail_to_scroll_to_is_displayed_correctly() = runUiTest {
        val fullscreenSettingsDetailPaneInjectEntryPoint: FullscreenSettingsDetailPaneInjectEntryPoint =
            uiComponent.entryPoint

        val entryPoint = object :
            FullscreenSettingsDetailPaneInjectEntryPoint by fullscreenSettingsDetailPaneInjectEntryPoint,
            FullscreenSettingsDetailPaneLocalEntryPoint by fullscreenSettingsDetailPaneLocalEntryPoint {}

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
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

    @Config(qualifiers = "w300dp-h300dp")
    @Test
    fun detail_to_scroll_to_is_displayed_correctly() = runUiTest {
        val fullscreenSettingsDetailPaneInjectEntryPoint: FullscreenSettingsDetailPaneInjectEntryPoint =
            uiComponent.entryPoint

        val entryPoint = object :
            FullscreenSettingsDetailPaneInjectEntryPoint by fullscreenSettingsDetailPaneInjectEntryPoint,
            FullscreenSettingsDetailPaneLocalEntryPoint by fullscreenSettingsDetailPaneLocalEntryPoint {}

        val detailNavValue = ComposeLifeNavigation.FullscreenSettingsDetail(
            settingsCategory = SettingsCategory.Visual,
            initialSettingToScrollTo = Setting.CellShapeConfig,
        )

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
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

        waitForIdle()

        assertNull(detailNavValue.settingToScrollTo)

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

    @Config(qualifiers = "w700dp-h500dp")
    @Test
    fun reducing_size_keeps_selected_detail() = runUiTest {
        val fullscreenSettingsDetailPaneInjectEntryPoint: FullscreenSettingsDetailPaneInjectEntryPoint =
            uiComponent.entryPoint

        val entryPoint = object :
            FullscreenSettingsDetailPaneInjectEntryPoint by fullscreenSettingsDetailPaneInjectEntryPoint,
            FullscreenSettingsDetailPaneLocalEntryPoint by fullscreenSettingsDetailPaneLocalEntryPoint {}

        val listNavValue = ComposeLifeNavigation.FullscreenSettingsList(
            initialSettingsCategory = SettingsCategory.Algorithm,
        )
        var isDetailPresent by mutableStateOf(false)

        lateinit var view: View
        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            view = LocalView.current
            resolver = parameterizedStringResolver()
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

        onNodeWithText(resolver.invoke(Strings.Visual))
            .performClick()

        RuntimeEnvironment.setQualifiers("w500dp-h500dp")
        Shadow.extract<ShadowViewRootImpl>(view.rootView.parent).callDispatchResized()
        waitForIdle()

        onNodeWithContentDescription(
            resolver.invoke(Strings.CornerFractionLabelAndValue(0f)),
        )
            .performScrollTo()
            .assertIsDisplayed()
    }

    @Config(qualifiers = "w500dp-h500dp")
    @Test
    fun expanding_size_keeps_selected_detail() = runUiTest {
        val fullscreenSettingsDetailPaneInjectEntryPoint: FullscreenSettingsDetailPaneInjectEntryPoint =
            uiComponent.entryPoint

        val entryPoint = object :
            FullscreenSettingsDetailPaneInjectEntryPoint by fullscreenSettingsDetailPaneInjectEntryPoint,
            FullscreenSettingsDetailPaneLocalEntryPoint by fullscreenSettingsDetailPaneLocalEntryPoint {}

        val listNavValue = ComposeLifeNavigation.FullscreenSettingsList(
            initialSettingsCategory = SettingsCategory.Algorithm,
        )
        var isDetailPresent by mutableStateOf(false)

        lateinit var view: View
        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            view = LocalView.current
            resolver = parameterizedStringResolver()
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

        onNodeWithText(resolver.invoke(Strings.Visual))
            .performClick()

        RuntimeEnvironment.setQualifiers("w700dp-h500dp")
        Shadow.extract<ShadowViewRootImpl>(view.rootView.parent).callDispatchResized()
        waitForIdle()

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
