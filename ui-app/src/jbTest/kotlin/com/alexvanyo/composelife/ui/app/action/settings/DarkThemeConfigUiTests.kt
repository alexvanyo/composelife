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

import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.setValue
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.assertHasClickAction
import androidx.compose.ui.test.hasAnyAncestor
import androidx.compose.ui.test.hasText
import androidx.compose.ui.test.isPopup
import androidx.compose.ui.test.onNodeWithText
import androidx.compose.ui.test.performClick
import androidx.compose.ui.test.runComposeUiTest
import com.alexvanyo.composelife.kmpandroidrunner.KmpAndroidJUnit4
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResolver
import com.alexvanyo.composelife.preferences.DarkThemeConfig
import com.alexvanyo.composelife.ui.app.resources.DarkTheme
import com.alexvanyo.composelife.ui.app.resources.FollowSystem
import com.alexvanyo.composelife.ui.app.resources.LightTheme
import com.alexvanyo.composelife.ui.app.resources.Strings
import org.junit.runner.RunWith
import kotlin.test.Test
import kotlin.test.assertEquals

@OptIn(ExperimentalTestApi::class)
@RunWith(KmpAndroidJUnit4::class)
class DarkThemeConfigUiTests {

    @Test
    fun follow_system_is_displayed_correctly() = runComposeUiTest {
        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            DarkThemeConfigUi(
                darkThemeConfig = DarkThemeConfig.FollowSystem,
                setDarkThemeConfig = {},
            )
        }

        onNodeWithText(resolver(Strings.FollowSystem))
            .assertExists()
            .assertHasClickAction()
    }

    @Test
    fun light_is_displayed_correctly() = runComposeUiTest {
        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            DarkThemeConfigUi(
                darkThemeConfig = DarkThemeConfig.Light,
                setDarkThemeConfig = {},
            )
        }

        onNodeWithText(resolver(Strings.LightTheme))
            .assertExists()
            .assertHasClickAction()
    }

    @Test
    fun dark_is_displayed_correctly() = runComposeUiTest {
        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            DarkThemeConfigUi(
                darkThemeConfig = DarkThemeConfig.Dark,
                setDarkThemeConfig = {},
            )
        }

        onNodeWithText(resolver(Strings.DarkTheme))
            .assertExists()
            .assertHasClickAction()
    }

    @Test
    fun dark_theme_config_popup_displays_options() = runComposeUiTest {
        var darkThemeConfig: DarkThemeConfig by mutableStateOf(DarkThemeConfig.FollowSystem)

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            DarkThemeConfigUi(
                darkThemeConfig = darkThemeConfig,
                setDarkThemeConfig = { darkThemeConfig = it },
            )
        }

        onNodeWithText(resolver(Strings.FollowSystem))
            .performClick()

        onNode(hasAnyAncestor(isPopup()) and hasText(resolver(Strings.LightTheme)))
            .assertHasClickAction()
            .performClick()

        assertEquals(DarkThemeConfig.Light, darkThemeConfig)

        onNode(isPopup())
            .assertDoesNotExist()

        onNodeWithText(resolver(Strings.LightTheme))
            .assertExists()
            .assertHasClickAction()
    }
}
