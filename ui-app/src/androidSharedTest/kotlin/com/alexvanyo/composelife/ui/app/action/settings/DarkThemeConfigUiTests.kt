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

import android.content.Context
import androidx.activity.ComponentActivity
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.setValue
import androidx.compose.ui.test.assertHasClickAction
import androidx.compose.ui.test.hasAnyAncestor
import androidx.compose.ui.test.hasText
import androidx.compose.ui.test.isPopup
import androidx.compose.ui.test.junit4.createAndroidComposeRule
import androidx.compose.ui.test.onNodeWithText
import androidx.compose.ui.test.performClick
import androidx.test.ext.junit.runners.AndroidJUnit4
import com.alexvanyo.composelife.preferences.DarkThemeConfig
import com.alexvanyo.composelife.ui.app.R
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.test.runTest
import leakcanary.SkipLeakDetection
import org.junit.Rule
import org.junit.runner.RunWith
import kotlin.test.Test
import kotlin.test.assertEquals

@OptIn(ExperimentalCoroutinesApi::class)
@RunWith(AndroidJUnit4::class)
class DarkThemeConfigUiTests {

    @get:Rule
    val composeTestRule = createAndroidComposeRule<ComponentActivity>()

    private val context: Context get() = composeTestRule.activity

    @Test
    fun follow_system_is_displayed_correctly() = runTest {
        composeTestRule.setContent {
            DarkThemeConfigUi(
                darkThemeConfig = DarkThemeConfig.FollowSystem,
                setDarkThemeConfig = {},
            )
        }

        composeTestRule
            .onNodeWithText(context.getString(R.string.follow_system))
            .assertExists()
            .assertHasClickAction()
    }

    @Test
    fun light_is_displayed_correctly() = runTest {
        composeTestRule.setContent {
            DarkThemeConfigUi(
                darkThemeConfig = DarkThemeConfig.Light,
                setDarkThemeConfig = {},
            )
        }

        composeTestRule
            .onNodeWithText(context.getString(R.string.light_theme))
            .assertExists()
            .assertHasClickAction()
    }

    @Test
    fun dark_is_displayed_correctly() = runTest {
        composeTestRule.setContent {
            DarkThemeConfigUi(
                darkThemeConfig = DarkThemeConfig.Dark,
                setDarkThemeConfig = {},
            )
        }

        composeTestRule
            .onNodeWithText(context.getString(R.string.dark_theme))
            .assertExists()
            .assertHasClickAction()
    }

    @SkipLeakDetection("https://issuetracker.google.com/issues/206177594", "Inner")
    @Test
    fun dark_theme_config_popup_displays_options() = runTest {
        var darkThemeConfig: DarkThemeConfig by mutableStateOf(DarkThemeConfig.FollowSystem)

        composeTestRule.setContent {
            DarkThemeConfigUi(
                darkThemeConfig = darkThemeConfig,
                setDarkThemeConfig = { darkThemeConfig = it },
            )
        }

        composeTestRule
            .onNodeWithText(context.getString(R.string.follow_system))
            .performClick()

        composeTestRule
            .onNode(hasAnyAncestor(isPopup()) and hasText(context.getString(R.string.light_theme)))
            .assertHasClickAction()
            .performClick()

        assertEquals(DarkThemeConfig.Light, darkThemeConfig)

        composeTestRule
            .onNode(isPopup())
            .assertDoesNotExist()

        composeTestRule
            .onNodeWithText(context.getString(R.string.light_theme))
            .assertExists()
            .assertHasClickAction()
    }
}
