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
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.setValue
import androidx.compose.ui.test.assertHasClickAction
import androidx.compose.ui.test.assertIsOff
import androidx.compose.ui.test.assertIsOn
import androidx.compose.ui.test.junit4.createAndroidComposeRule
import androidx.compose.ui.test.onNodeWithContentDescription
import androidx.compose.ui.test.performClick
import androidx.test.ext.junit.runners.AndroidJUnit4
import com.alexvanyo.composelife.ui.R
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.test.runTest
import org.junit.Rule
import org.junit.Test
import org.junit.runner.RunWith
import kotlin.test.assertFalse
import kotlin.test.assertTrue

@OptIn(ExperimentalCoroutinesApi::class)
@RunWith(AndroidJUnit4::class)
class DisableAGSLUiTests {

    @get:Rule
    val composeTestRule = createAndroidComposeRule<ComponentActivity>()

    private val context: Context get() = composeTestRule.activity

    @Test
    fun disable_is_displayed_correctly() = runTest {
        composeTestRule.setContent {
            DisableAGSLUi(
                disableAGSL = true,
                setDisableAGSL = {},
            )
        }

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.disable_agsl))
            .assertExists()
            .assertIsOn()
            .assertHasClickAction()
    }

    @Test
    fun disable_will_update_correctly() = runTest {
        var disableAGSL by mutableStateOf(true)

        composeTestRule.setContent {
            DisableAGSLUi(
                disableAGSL = disableAGSL,
                setDisableAGSL = { disableAGSL = it },
            )
        }

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.disable_agsl))
            .performClick()

        assertFalse(disableAGSL)
    }

    @Test
    fun enable_is_displayed_correctly() = runTest {
        composeTestRule.setContent {
            DisableAGSLUi(
                disableAGSL = false,
                setDisableAGSL = {},
            )
        }

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.disable_agsl))
            .assertExists()
            .assertIsOff()
            .assertHasClickAction()
    }

    @Test
    fun enable_will_update_correctly() = runTest {
        var disableAGSL by mutableStateOf(false)

        composeTestRule.setContent {
            DisableAGSLUi(
                disableAGSL = disableAGSL,
                setDisableAGSL = { disableAGSL = it },
            )
        }

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.disable_agsl))
            .performClick()

        assertTrue(disableAGSL)
    }
}
