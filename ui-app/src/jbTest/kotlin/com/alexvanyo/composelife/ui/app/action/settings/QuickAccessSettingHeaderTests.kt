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

import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.assertIsDisplayed
import androidx.compose.ui.test.assertIsOff
import androidx.compose.ui.test.assertIsOn
import androidx.compose.ui.test.onNodeWithContentDescription
import androidx.compose.ui.test.performClick
import androidx.compose.ui.test.runComposeUiTest
import com.alexvanyo.composelife.kmpandroidrunner.KmpAndroidJUnit4
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResolver
import com.alexvanyo.composelife.ui.app.resources.AddSettingToQuickAccess
import com.alexvanyo.composelife.ui.app.resources.OpenInSettings
import com.alexvanyo.composelife.ui.app.resources.RemoveSettingFromQuickAccess
import com.alexvanyo.composelife.ui.app.resources.Strings
import org.junit.runner.RunWith
import kotlin.test.Test
import kotlin.test.assertEquals

@OptIn(ExperimentalTestApi::class)
@RunWith(KmpAndroidJUnit4::class)
class QuickAccessSettingHeaderTests {

    @Test
    fun is_favorite_without_open_in_settings_is_displayed_correctly() = runComposeUiTest {
        var setIsFavoriteResult: Boolean? = null

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            QuickAccessSettingHeader(
                isFavorite = true,
                setIsFavorite = {
                    setIsFavoriteResult = it
                },
            )
        }

        onNodeWithContentDescription(resolver(Strings.RemoveSettingFromQuickAccess))
            .assertIsOn()
            .assertIsDisplayed()
            .performClick()

        assertEquals(false, setIsFavoriteResult)

        onNodeWithContentDescription(resolver(Strings.OpenInSettings))
            .assertDoesNotExist()
    }

    @Test
    fun is_favorite_with_open_in_settings_is_displayed_correctly() = runComposeUiTest {
        var setIsFavoriteResult: Boolean? = null
        var onOpenInSettingsResult: Unit? = null

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            QuickAccessSettingHeader(
                isFavorite = true,
                setIsFavorite = {
                    setIsFavoriteResult = it
                },
                onOpenInSettingsClicked = {
                    onOpenInSettingsResult = Unit
                },
            )
        }

        onNodeWithContentDescription(resolver(Strings.RemoveSettingFromQuickAccess))
            .assertIsOn()
            .assertIsDisplayed()
            .performClick()

        assertEquals(false, setIsFavoriteResult)

        onNodeWithContentDescription(resolver(Strings.OpenInSettings))
            .assertIsDisplayed()
            .performClick()

        assertEquals(Unit, onOpenInSettingsResult)
    }

    @Test
    fun is_not_favorite_without_open_in_settings_is_displayed_correctly() = runComposeUiTest {
        var setIsFavoriteResult: Boolean? = null

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            QuickAccessSettingHeader(
                isFavorite = false,
                setIsFavorite = {
                    setIsFavoriteResult = it
                },
            )
        }

        onNodeWithContentDescription(resolver(Strings.AddSettingToQuickAccess))
            .assertIsOff()
            .assertIsDisplayed()
            .performClick()

        assertEquals(true, setIsFavoriteResult)

        onNodeWithContentDescription(resolver(Strings.OpenInSettings))
            .assertDoesNotExist()
    }

    @Test
    fun is_not_favorite_with_open_in_settings_is_displayed_correctly() = runComposeUiTest {
        var setIsFavoriteResult: Boolean? = null
        var onOpenInSettingsResult: Unit? = null

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            QuickAccessSettingHeader(
                isFavorite = false,
                setIsFavorite = {
                    setIsFavoriteResult = it
                },
                onOpenInSettingsClicked = {
                    onOpenInSettingsResult = Unit
                },
            )
        }

        onNodeWithContentDescription(resolver(Strings.AddSettingToQuickAccess))
            .assertIsOff()
            .assertIsDisplayed()
            .performClick()

        assertEquals(true, setIsFavoriteResult)

        onNodeWithContentDescription(resolver(Strings.OpenInSettings))
            .assertIsDisplayed()
            .performClick()

        assertEquals(Unit, onOpenInSettingsResult)
    }
}
