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

package com.alexvanyo.composelife.ui.app.info

import androidx.compose.foundation.layout.Column
import androidx.compose.ui.test.assertIsDisplayed
import androidx.compose.ui.test.assertIsOff
import androidx.compose.ui.test.assertIsOn
import androidx.compose.ui.test.assertIsToggleable
import androidx.compose.ui.test.isToggleable
import androidx.compose.ui.test.junit4.StateRestorationTester
import androidx.compose.ui.test.junit4.createComposeRule
import androidx.compose.ui.test.onNodeWithText
import androidx.compose.ui.test.performClick
import androidx.test.ext.junit.runners.AndroidJUnit4
import org.junit.Rule
import org.junit.runner.RunWith
import kotlin.test.Test
import kotlin.test.assertFalse
import kotlin.test.assertTrue

@RunWith(AndroidJUnit4::class)
class CellUniverseInfoItemTests {

    @get:Rule
    val composeTestRule = createComposeRule()

    @Test
    fun can_check_while_editing() {
        val cellUniverseInfoItemState = CellUniverseInfoItemState()

        composeTestRule.setContent {
            Column {
                InfoItem(
                    cellUniverseInfoItemContent = CellUniverseInfoItemContent(cellUniverseInfoItemState) { "Test" },
                    isEditing = true,
                )
            }
        }

        composeTestRule.onNodeWithText("Test")
            .assertIsToggleable()
            .assertIsOn()
            .performClick()

        assertFalse(cellUniverseInfoItemState.isChecked)

        composeTestRule.onNodeWithText("Test").assertIsOff()
    }

    @Test
    fun can_uncheck_while_editing() {
        val cellUniverseInfoItemState = CellUniverseInfoItemState(isChecked = false)

        composeTestRule.setContent {
            Column {
                InfoItem(
                    cellUniverseInfoItemContent = CellUniverseInfoItemContent(cellUniverseInfoItemState) { "Test" },
                    isEditing = true,
                )
            }
        }

        composeTestRule.onNodeWithText("Test")
            .assertIsToggleable()
            .assertIsOff()
            .performClick()

        assertTrue(cellUniverseInfoItemState.isChecked)

        composeTestRule.onNodeWithText("Test").assertIsOn()
    }

    @Test
    fun unchecked_item_is_hidden_while_not_editing() {
        val cellUniverseInfoItemState = CellUniverseInfoItemState(isChecked = false)

        composeTestRule.setContent {
            Column {
                InfoItem(
                    cellUniverseInfoItemContent = CellUniverseInfoItemContent(cellUniverseInfoItemState) { "Test" },
                    isEditing = false,
                )
            }
        }

        composeTestRule.onNodeWithText("Test").assertDoesNotExist()
    }

    @Test
    fun checkbox_is_hidden_for_checked_item_is_hidden_while_not_editing() {
        val cellUniverseInfoItemState = CellUniverseInfoItemState(isChecked = true)

        composeTestRule.setContent {
            Column {
                InfoItem(
                    cellUniverseInfoItemContent = CellUniverseInfoItemContent(cellUniverseInfoItemState) { "Test" },
                    isEditing = false,
                )
            }
        }

        composeTestRule.onNodeWithText("Test").assertIsDisplayed()
        composeTestRule.onNode(isToggleable()).assertDoesNotExist()
    }

    @Test
    fun is_checked_state_is_saved() {
        val stateRestorationTester = StateRestorationTester(composeTestRule)

        stateRestorationTester.setContent {
            val cellUniverseInfoItemState = rememberCellUniverseInfoItemState()

            Column {
                InfoItem(
                    cellUniverseInfoItemContent = CellUniverseInfoItemContent(cellUniverseInfoItemState) { "Test" },
                    isEditing = true,
                )
            }
        }

        composeTestRule.onNodeWithText("Test")
            .assertIsToggleable()
            .assertIsOn()
            .performClick()

        composeTestRule.onNodeWithText("Test").assertIsOff()

        stateRestorationTester.emulateSavedInstanceStateRestore()

        composeTestRule.onNodeWithText("Test").assertIsOff()
    }
}
