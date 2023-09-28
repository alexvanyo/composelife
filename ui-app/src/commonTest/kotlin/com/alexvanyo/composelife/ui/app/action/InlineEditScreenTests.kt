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
import com.alexvanyo.composelife.preferences.ToolConfig
import com.alexvanyo.composelife.ui.app.resources.Draw
import com.alexvanyo.composelife.ui.app.resources.Erase
import com.alexvanyo.composelife.ui.app.resources.None
import com.alexvanyo.composelife.ui.app.resources.Pan
import com.alexvanyo.composelife.ui.app.resources.Select
import com.alexvanyo.composelife.ui.app.resources.Strings
import org.junit.runner.RunWith
import kotlin.test.Test
import kotlin.test.assertEquals

@OptIn(ExperimentalTestApi::class)
@RunWith(KmpAndroidJUnit4::class)
class InlineEditScreenTests {

    @Test
    fun touch_config_pan_is_displayed_correctly() = runComposeUiTest {
        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            InlineEditScreen(
                touchToolConfig = ToolConfig.Pan,
                setTouchToolConfig = {},
                stylusToolConfig = ToolConfig.None,
                setStylusToolConfig = {},
                mouseToolConfig = ToolConfig.None,
                setMouseToolConfig = {},
            )
        }

        onNodeWithText(resolver(Strings.Pan))
            .assertExists()
            .assertHasClickAction()
    }

    @Test
    fun touch_config_draw_is_displayed_correctly() = runComposeUiTest {
        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            InlineEditScreen(
                touchToolConfig = ToolConfig.Draw,
                setTouchToolConfig = {},
                stylusToolConfig = ToolConfig.None,
                setStylusToolConfig = {},
                mouseToolConfig = ToolConfig.None,
                setMouseToolConfig = {},
            )
        }

        onNodeWithText(resolver(Strings.Draw))
            .assertExists()
            .assertHasClickAction()
    }

    @Test
    fun touch_config_erase_is_displayed_correctly() = runComposeUiTest {
        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            InlineEditScreen(
                touchToolConfig = ToolConfig.Erase,
                setTouchToolConfig = {},
                stylusToolConfig = ToolConfig.None,
                setStylusToolConfig = {},
                mouseToolConfig = ToolConfig.None,
                setMouseToolConfig = {},
            )
        }

        onNodeWithText(resolver(Strings.Erase))
            .assertExists()
            .assertHasClickAction()
    }

    @Test
    fun touch_config_select_is_displayed_correctly() = runComposeUiTest {
        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            InlineEditScreen(
                touchToolConfig = ToolConfig.Select,
                setTouchToolConfig = {},
                stylusToolConfig = ToolConfig.None,
                setStylusToolConfig = {},
                mouseToolConfig = ToolConfig.None,
                setMouseToolConfig = {},
            )
        }

        onNodeWithText(resolver(Strings.Select))
            .assertExists()
            .assertHasClickAction()
    }

    @Test
    fun touch_config_none_is_displayed_correctly() = runComposeUiTest {
        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            InlineEditScreen(
                touchToolConfig = ToolConfig.None,
                setTouchToolConfig = {},
                stylusToolConfig = ToolConfig.Draw,
                setStylusToolConfig = {},
                mouseToolConfig = ToolConfig.Draw,
                setMouseToolConfig = {},
            )
        }

        onNodeWithText(resolver(Strings.None))
            .assertExists()
            .assertHasClickAction()
    }

    @Test
    fun touch_config_popup_displays_options() = runComposeUiTest {
        var touchToolConfig: ToolConfig by mutableStateOf(ToolConfig.Pan)

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            InlineEditScreen(
                touchToolConfig = touchToolConfig,
                setTouchToolConfig = { touchToolConfig = it },
                stylusToolConfig = ToolConfig.None,
                setStylusToolConfig = {},
                mouseToolConfig = ToolConfig.None,
                setMouseToolConfig = {},
            )
        }

        onNodeWithText(resolver(Strings.Pan))
            .performClick()

        onNode(hasAnyAncestor(isPopup()) and hasText(resolver(Strings.Draw)))
            .assertHasClickAction()
            .performClick()

        assertEquals(ToolConfig.Draw, touchToolConfig)

        onNode(isPopup())
            .assertDoesNotExist()

        onNodeWithText(resolver(Strings.Draw))
            .assertExists()
            .assertHasClickAction()
    }
}
