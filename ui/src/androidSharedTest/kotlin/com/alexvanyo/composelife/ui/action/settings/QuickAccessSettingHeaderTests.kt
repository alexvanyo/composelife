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

package com.alexvanyo.composelife.ui.action.settings

import android.content.Context
import androidx.activity.ComponentActivity
import androidx.compose.ui.test.assertIsDisplayed
import androidx.compose.ui.test.assertIsOff
import androidx.compose.ui.test.assertIsOn
import androidx.compose.ui.test.junit4.createAndroidComposeRule
import androidx.compose.ui.test.onNodeWithContentDescription
import androidx.compose.ui.test.performClick
import androidx.test.ext.junit.runners.AndroidJUnit4
import com.alexvanyo.composelife.ui.R
import org.junit.Rule
import org.junit.runner.RunWith
import kotlin.test.Test
import kotlin.test.assertEquals

@RunWith(AndroidJUnit4::class)
class QuickAccessSettingHeaderTests {

    @get:Rule
    val composeTestRule = createAndroidComposeRule<ComponentActivity>()

    private val context: Context get() = composeTestRule.activity

    @Test
    fun is_favorite_without_open_in_settings_is_displayed_correctly() {
        var setIsFavoriteResult: Boolean? = null

        composeTestRule.setContent {
            QuickAccessSettingHeader(
                isFavorite = true,
                setIsFavorite = {
                    setIsFavoriteResult = it
                },
            )
        }

        composeTestRule.onNodeWithContentDescription(context.getString(R.string.remove_setting_from_quick_access))
            .assertIsOn()
            .assertIsDisplayed()
            .performClick()

        assertEquals(false, setIsFavoriteResult)

        composeTestRule.onNodeWithContentDescription(context.getString(R.string.open_in_settings))
            .assertDoesNotExist()
    }

    @Test
    fun is_favorite_with_open_in_settings_is_displayed_correctly() {
        var setIsFavoriteResult: Boolean? = null
        var onOpenInSettingsResult: Unit? = null

        composeTestRule.setContent {
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

        composeTestRule.onNodeWithContentDescription(context.getString(R.string.remove_setting_from_quick_access))
            .assertIsOn()
            .assertIsDisplayed()
            .performClick()

        assertEquals(false, setIsFavoriteResult)

        composeTestRule.onNodeWithContentDescription(context.getString(R.string.open_in_settings))
            .assertIsDisplayed()
            .performClick()

        assertEquals(Unit, onOpenInSettingsResult)
    }

    @Test
    fun is_not_favorite_without_open_in_settings_is_displayed_correctly() {
        var setIsFavoriteResult: Boolean? = null

        composeTestRule.setContent {
            QuickAccessSettingHeader(
                isFavorite = false,
                setIsFavorite = {
                    setIsFavoriteResult = it
                },
            )
        }

        composeTestRule.onNodeWithContentDescription(context.getString(R.string.add_setting_to_quick_access))
            .assertIsOff()
            .assertIsDisplayed()
            .performClick()

        assertEquals(true, setIsFavoriteResult)

        composeTestRule.onNodeWithContentDescription(context.getString(R.string.open_in_settings))
            .assertDoesNotExist()
    }

    @Test
    fun is_not_favorite_with_open_in_settings_is_displayed_correctly() {
        var setIsFavoriteResult: Boolean? = null
        var onOpenInSettingsResult: Unit? = null

        composeTestRule.setContent {
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

        composeTestRule.onNodeWithContentDescription(context.getString(R.string.add_setting_to_quick_access))
            .assertIsOff()
            .assertIsDisplayed()
            .performClick()

        assertEquals(true, setIsFavoriteResult)

        composeTestRule.onNodeWithContentDescription(context.getString(R.string.open_in_settings))
            .assertIsDisplayed()
            .performClick()

        assertEquals(Unit, onOpenInSettingsResult)
    }
}
