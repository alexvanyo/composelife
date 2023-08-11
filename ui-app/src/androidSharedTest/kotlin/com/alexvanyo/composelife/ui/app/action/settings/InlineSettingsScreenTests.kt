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

import androidx.compose.runtime.snapshotFlow
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
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferences
import com.alexvanyo.composelife.preferences.QuickAccessSetting
import com.alexvanyo.composelife.preferences.TestComposeLifePreferences
import com.alexvanyo.composelife.resourcestate.ResourceState
import com.alexvanyo.composelife.resourcestate.firstSuccess
import com.alexvanyo.composelife.test.BaseUiInjectTest
import com.alexvanyo.composelife.test.InjectTestActivity
import com.alexvanyo.composelife.ui.app.R
import com.alexvanyo.composelife.ui.app.TestComposeLifeApplicationComponent
import com.alexvanyo.composelife.ui.app.create
import leakcanary.SkipLeakDetection
import org.junit.runner.RunWith
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertIs

@RunWith(KmpAndroidJUnit4::class)
class InlineSettingsScreenTests : BaseUiInjectTest<TestComposeLifeApplicationComponent, InjectTestActivity>(
    { TestComposeLifeApplicationComponent.create() },
    InjectTestActivity::class.java,
) {
    private val composeLifePreferences get() = applicationComponent.composeLifePreferences

    private val testComposeLifePreferences: TestComposeLifePreferences get() = assertIs(composeLifePreferences)

    private val inlineSettingsScreenInjectEntryPoint get() =
        composeTestRule.activity.uiComponent.entryPoint as InlineSettingsScreenInjectEntryPoint

    @Test
    @SkipLeakDetection("appliedChanges", "Outer", "Inner")
    fun saving_settings_onboarding_is_shown_with_no_quick_access_settings_saved() = runAppTest {
        testComposeLifePreferences.testSetQuickAccessSetting(emptySet())
        snapshotFlow { composeLifePreferences.loadedPreferencesState }.firstSuccess()

        var onSeeMoreClickedCount = 0

        composeTestRule.setContent {
            with(inlineSettingsScreenInjectEntryPoint) {
                with(
                    object : InlineSettingsScreenLocalEntryPoint {
                        override val preferences get() =
                            assertIs<ResourceState.Success<LoadedComposeLifePreferences>>(
                                composeLifePreferences.loadedPreferencesState,
                            ).value
                    },
                ) {
                    InlineSettingsScreen(
                        onSeeMoreClicked = {
                            onSeeMoreClickedCount++
                        },
                        onOpenInSettingsClicked = {},
                    )
                }
            }
        }

        composeTestRule
            .onNodeWithText(context.getString(R.string.quick_settings_info))
            .performScrollTo()
            .assertIsDisplayed()
            .assertHasNoClickAction()

        composeTestRule
            .onNodeWithText(context.getString(R.string.see_all))
            .performScrollTo()
            .assertIsDisplayed()
            .assertHasClickAction()
            .performClick()

        assertEquals(1, onSeeMoreClickedCount)
    }

    @Test
    @SkipLeakDetection("appliedChanges", "Outer")
    fun saved_opengl_setting_is_displayed_correctly() = runAppTest {
        testComposeLifePreferences.testSetQuickAccessSetting(
            setOf(QuickAccessSetting.DisableOpenGL),
        )
        snapshotFlow { composeLifePreferences.loadedPreferencesState }.firstSuccess()

        composeTestRule.setContent {
            with(inlineSettingsScreenInjectEntryPoint) {
                with(
                    object : InlineSettingsScreenLocalEntryPoint {
                        override val preferences get() =
                            assertIs<ResourceState.Success<LoadedComposeLifePreferences>>(
                                composeLifePreferences.loadedPreferencesState,
                            ).value
                    },
                ) {
                    InlineSettingsScreen(
                        onSeeMoreClicked = {},
                        onOpenInSettingsClicked = {},
                    )
                }
            }
        }

        composeTestRule
            .onNode(
                hasContentDescription(context.getString(R.string.remove_setting_from_quick_access)) and
                    hasAnyAncestor(hasTestTag("SettingUi:${Setting.DisableOpenGL.name}")),
            )
            .performScrollTo()
            .assertIsDisplayed()
            .assertIsOn()
            .assertHasClickAction()

        composeTestRule
            .onNode(
                hasContentDescription(context.getString(R.string.open_in_settings)) and
                    hasAnyAncestor(hasTestTag("SettingUi:${Setting.DisableOpenGL.name}")),
            )
            .performScrollTo()
            .assertIsDisplayed()
            .assertHasClickAction()

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.disable_opengl))
            .performScrollTo()
            .assertIsDisplayed()
            .assert(hasAnyAncestor(hasTestTag("SettingUi:${Setting.DisableOpenGL.name}")))
            .assertIsOff()
            .assertHasClickAction()
    }

    @Test
    @SkipLeakDetection("appliedChanges", "Outer")
    fun opening_saved_setting_functions_correctly() = runAppTest {
        testComposeLifePreferences.testSetQuickAccessSetting(
            setOf(QuickAccessSetting.DisableOpenGL),
        )
        snapshotFlow { composeLifePreferences.loadedPreferencesState }.firstSuccess()

        var onOpenInSettingsClickedCount = 0
        var onOpenInSettingsClickedSetting: Setting? = null

        composeTestRule.setContent {
            with(inlineSettingsScreenInjectEntryPoint) {
                with(
                    object : InlineSettingsScreenLocalEntryPoint {
                        override val preferences get() =
                            assertIs<ResourceState.Success<LoadedComposeLifePreferences>>(
                                composeLifePreferences.loadedPreferencesState,
                            ).value
                    },
                ) {
                    InlineSettingsScreen(
                        onSeeMoreClicked = {},
                        onOpenInSettingsClicked = {
                            onOpenInSettingsClickedCount++
                            onOpenInSettingsClickedSetting = it
                        },
                    )
                }
            }
        }

        composeTestRule
            .onNode(
                hasContentDescription(context.getString(R.string.open_in_settings)) and
                    hasAnyAncestor(hasTestTag("SettingUi:${Setting.DisableOpenGL.name}")),
            )
            .performScrollTo()
            .assertIsDisplayed()
            .performClick()

        assertEquals(1, onOpenInSettingsClickedCount)
        assertEquals(Setting.DisableOpenGL, onOpenInSettingsClickedSetting)
    }

    @Test
    @SkipLeakDetection("appliedChanges", "Outer")
    fun removing_saved_setting_functions_correctly() = runAppTest {
        testComposeLifePreferences.testSetQuickAccessSetting(
            setOf(QuickAccessSetting.DisableOpenGL),
        )
        snapshotFlow { composeLifePreferences.loadedPreferencesState }.firstSuccess()

        composeTestRule.setContent {
            with(inlineSettingsScreenInjectEntryPoint) {
                with(
                    object : InlineSettingsScreenLocalEntryPoint {
                        override val preferences get() =
                            assertIs<ResourceState.Success<LoadedComposeLifePreferences>>(
                                composeLifePreferences.loadedPreferencesState,
                            ).value
                    },
                ) {
                    InlineSettingsScreen(
                        onSeeMoreClicked = {},
                        onOpenInSettingsClicked = {},
                    )
                }
            }
        }

        composeTestRule
            .onNode(
                hasContentDescription(context.getString(R.string.remove_setting_from_quick_access)) and
                    hasAnyAncestor(hasTestTag("SettingUi:${Setting.DisableOpenGL.name}")),
            )
            .performScrollTo()
            .assertIsDisplayed()
            .performClick()

        composeTestRule
            .onNodeWithText(context.getString(R.string.quick_settings_info))
            .performScrollTo()
            .assertIsDisplayed()
            .assertHasNoClickAction()

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.disable_opengl))
            .assertDoesNotExist()
    }
}
