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

package com.alexvanyo.composelife.ui.app.action

import androidx.compose.runtime.snapshotFlow
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.assert
import androidx.compose.ui.test.assertHasClickAction
import androidx.compose.ui.test.assertHasNoClickAction
import androidx.compose.ui.test.assertIsDisplayed
import androidx.compose.ui.test.assertIsOff
import androidx.compose.ui.test.assertIsOn
import androidx.compose.ui.test.hasAnyAncestor
import androidx.compose.ui.test.hasContentDescription
import androidx.compose.ui.test.hasTestTag
import androidx.compose.ui.test.onNodeWithContentDescription
import androidx.compose.ui.test.onNodeWithText
import androidx.compose.ui.test.performClick
import androidx.compose.ui.test.performScrollTo
import com.alexvanyo.composelife.kmpandroidrunner.KmpAndroidJUnit4
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResolver
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferences
import com.alexvanyo.composelife.preferences.QuickAccessSetting
import com.alexvanyo.composelife.preferences.TestComposeLifePreferences
import com.alexvanyo.composelife.resourcestate.ResourceState
import com.alexvanyo.composelife.resourcestate.firstSuccess
import com.alexvanyo.composelife.test.BaseUiInjectTest2
import com.alexvanyo.composelife.test.runUiTest
import com.alexvanyo.composelife.ui.app.TestComposeLifeApplicationComponent
import com.alexvanyo.composelife.ui.app.TestComposeLifeUiComponent
import com.alexvanyo.composelife.ui.app.action.settings.InlineSettingsPane
import com.alexvanyo.composelife.ui.app.action.settings.InlineSettingsPaneInjectEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.InlineSettingsPaneLocalEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.Setting
import com.alexvanyo.composelife.ui.app.action.settings._name
import com.alexvanyo.composelife.ui.app.createComponent
import com.alexvanyo.composelife.ui.app.resources.DisableOpenGL
import com.alexvanyo.composelife.ui.app.resources.OpenInSettings
import com.alexvanyo.composelife.ui.app.resources.QuickSettingsInfo
import com.alexvanyo.composelife.ui.app.resources.RemoveSettingFromQuickAccess
import com.alexvanyo.composelife.ui.app.resources.SeeAll
import com.alexvanyo.composelife.ui.app.resources.Strings
import org.junit.runner.RunWith
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertIs

@OptIn(ExperimentalTestApi::class)
@RunWith(KmpAndroidJUnit4::class)
class InlineSettingsPaneTests : BaseUiInjectTest2<TestComposeLifeApplicationComponent, TestComposeLifeUiComponent>(
    TestComposeLifeApplicationComponent::createComponent,
    TestComposeLifeUiComponent::createComponent,
) {
    private val composeLifePreferences get() = applicationComponent.composeLifePreferences

    private val testComposeLifePreferences: TestComposeLifePreferences get() = assertIs(composeLifePreferences)

    @Test
    fun saving_settings_onboarding_is_shown_with_no_quick_access_settings_saved() = runUiTest {
        val inlineSettingsPaneInjectEntryPoint: InlineSettingsPaneInjectEntryPoint = uiComponent.entryPoint

        testComposeLifePreferences.quickAccessSettings = emptySet()
        snapshotFlow { composeLifePreferences.loadedPreferencesState }.firstSuccess()

        var onSeeMoreClickedCount = 0

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            with(inlineSettingsPaneInjectEntryPoint) {
                with(
                    object : InlineSettingsPaneLocalEntryPoint {
                        override val preferences get() =
                            assertIs<ResourceState.Success<LoadedComposeLifePreferences>>(
                                composeLifePreferences.loadedPreferencesState,
                            ).value
                    },
                ) {
                    InlineSettingsPane(
                        onSeeMoreClicked = {
                            onSeeMoreClickedCount++
                        },
                        onOpenInSettingsClicked = {},
                    )
                }
            }
        }

        onNodeWithText(resolver.invoke(Strings.QuickSettingsInfo))
            .performScrollTo()
            .assertIsDisplayed()
            .assertHasNoClickAction()

        onNodeWithText(resolver.invoke(Strings.SeeAll))
            .performScrollTo()
            .assertIsDisplayed()
            .assertHasClickAction()
            .performClick()

        assertEquals(1, onSeeMoreClickedCount)
    }

    @Test
    fun saved_opengl_setting_is_displayed_correctly() = runUiTest {
        val inlineSettingsPaneInjectEntryPoint: InlineSettingsPaneInjectEntryPoint = uiComponent.entryPoint
        testComposeLifePreferences.quickAccessSettings = setOf(QuickAccessSetting.DisableOpenGL)
        snapshotFlow { composeLifePreferences.loadedPreferencesState }.firstSuccess()

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            with(inlineSettingsPaneInjectEntryPoint) {
                with(
                    object : InlineSettingsPaneLocalEntryPoint {
                        override val preferences get() =
                            assertIs<ResourceState.Success<LoadedComposeLifePreferences>>(
                                composeLifePreferences.loadedPreferencesState,
                            ).value
                    },
                ) {
                    InlineSettingsPane(
                        onSeeMoreClicked = {},
                        onOpenInSettingsClicked = {},
                    )
                }
            }
        }

        onNode(
            hasContentDescription(resolver.invoke(Strings.RemoveSettingFromQuickAccess)) and
                hasAnyAncestor(hasTestTag("SettingUi:${Setting.DisableOpenGL._name}")),
        )
            .performScrollTo()
            .assertIsDisplayed()
            .assertIsOn()
            .assertHasClickAction()

        onNode(
            hasContentDescription(resolver.invoke(Strings.OpenInSettings)) and
                hasAnyAncestor(hasTestTag("SettingUi:${Setting.DisableOpenGL._name}")),
        )
            .performScrollTo()
            .assertIsDisplayed()
            .assertHasClickAction()

        onNodeWithContentDescription(resolver.invoke(Strings.DisableOpenGL))
            .performScrollTo()
            .assertIsDisplayed()
            .assert(hasAnyAncestor(hasTestTag("SettingUi:${Setting.DisableOpenGL._name}")))
            .assertIsOff()
            .assertHasClickAction()
    }

    @Test
    fun opening_saved_setting_functions_correctly() = runUiTest {
        val inlineSettingsPaneInjectEntryPoint: InlineSettingsPaneInjectEntryPoint = uiComponent.entryPoint
        testComposeLifePreferences.quickAccessSettings = setOf(QuickAccessSetting.DisableOpenGL)
        snapshotFlow { composeLifePreferences.loadedPreferencesState }.firstSuccess()

        var onOpenInSettingsClickedCount = 0
        var onOpenInSettingsClickedSetting: Setting? = null

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            with(inlineSettingsPaneInjectEntryPoint) {
                with(
                    object : InlineSettingsPaneLocalEntryPoint {
                        override val preferences get() =
                            assertIs<ResourceState.Success<LoadedComposeLifePreferences>>(
                                composeLifePreferences.loadedPreferencesState,
                            ).value
                    },
                ) {
                    InlineSettingsPane(
                        onSeeMoreClicked = {},
                        onOpenInSettingsClicked = {
                            onOpenInSettingsClickedCount++
                            onOpenInSettingsClickedSetting = it
                        },
                    )
                }
            }
        }

        onNode(
            hasContentDescription(resolver.invoke(Strings.OpenInSettings)) and
                hasAnyAncestor(hasTestTag("SettingUi:${Setting.DisableOpenGL._name}")),
        )
            .performScrollTo()
            .assertIsDisplayed()
            .performClick()

        assertEquals(1, onOpenInSettingsClickedCount)
        assertEquals(Setting.DisableOpenGL, onOpenInSettingsClickedSetting)
    }

    @Test
    fun removing_saved_setting_functions_correctly() = runUiTest {
        val inlineSettingsPaneInjectEntryPoint: InlineSettingsPaneInjectEntryPoint = uiComponent.entryPoint
        testComposeLifePreferences.quickAccessSettings = setOf(QuickAccessSetting.DisableOpenGL)
        snapshotFlow { composeLifePreferences.loadedPreferencesState }.firstSuccess()

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            with(inlineSettingsPaneInjectEntryPoint) {
                with(
                    object : InlineSettingsPaneLocalEntryPoint {
                        override val preferences get() =
                            assertIs<ResourceState.Success<LoadedComposeLifePreferences>>(
                                composeLifePreferences.loadedPreferencesState,
                            ).value
                    },
                ) {
                    InlineSettingsPane(
                        onSeeMoreClicked = {},
                        onOpenInSettingsClicked = {},
                    )
                }
            }
        }

        onNode(
            hasContentDescription(resolver.invoke(Strings.RemoveSettingFromQuickAccess)) and
                hasAnyAncestor(hasTestTag("SettingUi:${Setting.DisableOpenGL._name}")),
        )
            .performScrollTo()
            .assertIsDisplayed()
            .performClick()

        onNodeWithText(resolver.invoke(Strings.QuickSettingsInfo))
            .performScrollTo()
            .assertIsDisplayed()
            .assertHasNoClickAction()

        onNodeWithContentDescription(resolver.invoke(Strings.DisableOpenGL))
            .assertDoesNotExist()
    }
}
