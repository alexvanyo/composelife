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
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.assertIsDisplayed
import androidx.compose.ui.test.assertIsOff
import androidx.compose.ui.test.assertIsOn
import androidx.compose.ui.test.assertIsToggleable
import androidx.compose.ui.test.isToggleable
import androidx.compose.ui.test.onNodeWithText
import androidx.compose.ui.test.performClick
import androidx.compose.ui.test.runComposeUiTest
import com.alexvanyo.composelife.kmpandroidrunner.KmpAndroidJUnit4
import com.alexvanyo.composelife.kmpstaterestorationtester.KmpStateRestorationTester
import com.alexvanyo.composelife.ui.util.TargetState
import org.junit.runner.RunWith
import kotlin.test.Test
import kotlin.test.assertFalse
import kotlin.test.assertTrue

@OptIn(ExperimentalTestApi::class)
@RunWith(KmpAndroidJUnit4::class)
class CellUniverseInfoItemTests {

    @Test
    fun can_check_while_editing() = runComposeUiTest {
        val cellUniverseInfoItemState = CellUniverseInfoItemState()

        setContent {
            Column {
                InfoItem(
                    cellUniverseInfoItemContent = CellUniverseInfoItemContent(cellUniverseInfoItemState) { "Test" },
                    editingTargetState = TargetState.Single(true),
                )
            }
        }

        onNodeWithText("Test")
            .assertIsToggleable()
            .assertIsOn()
            .performClick()

        assertFalse(cellUniverseInfoItemState.isChecked)

        onNodeWithText("Test").assertIsOff()
    }

    @Test
    fun can_uncheck_while_editing() = runComposeUiTest {
        val cellUniverseInfoItemState = CellUniverseInfoItemState(isChecked = false)

        setContent {
            Column {
                InfoItem(
                    cellUniverseInfoItemContent = CellUniverseInfoItemContent(cellUniverseInfoItemState) { "Test" },
                    editingTargetState = TargetState.Single(true),
                )
            }
        }

        onNodeWithText("Test")
            .assertIsToggleable()
            .assertIsOff()
            .performClick()

        assertTrue(cellUniverseInfoItemState.isChecked)

        onNodeWithText("Test").assertIsOn()
    }

    @Test
    fun unchecked_item_is_hidden_while_not_editing() = runComposeUiTest {
        val cellUniverseInfoItemState = CellUniverseInfoItemState(isChecked = false)

        setContent {
            Column {
                InfoItem(
                    cellUniverseInfoItemContent = CellUniverseInfoItemContent(cellUniverseInfoItemState) { "Test" },
                    editingTargetState = TargetState.Single(false),
                )
            }
        }

        onNodeWithText("Test").assertDoesNotExist()
    }

    @Test
    fun checkbox_is_hidden_for_checked_item_is_hidden_while_not_editing() = runComposeUiTest {
        val cellUniverseInfoItemState = CellUniverseInfoItemState(isChecked = true)

        setContent {
            Column {
                InfoItem(
                    cellUniverseInfoItemContent = CellUniverseInfoItemContent(cellUniverseInfoItemState) { "Test" },
                    editingTargetState = TargetState.Single(false),
                )
            }
        }

        onNodeWithText("Test").assertIsDisplayed()
        onNode(isToggleable()).assertDoesNotExist()
    }

    @Test
    fun is_checked_state_is_saved() = runComposeUiTest {
        val stateRestorationTester = KmpStateRestorationTester(this)

        stateRestorationTester.setContent {
            val cellUniverseInfoItemState = rememberCellUniverseInfoItemState()

            Column {
                InfoItem(
                    cellUniverseInfoItemContent = CellUniverseInfoItemContent(cellUniverseInfoItemState) { "Test" },
                    editingTargetState = TargetState.Single(true),
                )
            }
        }

        onNodeWithText("Test")
            .assertIsToggleable()
            .assertIsOn()
            .performClick()

        onNodeWithText("Test").assertIsOff()

        stateRestorationTester.emulateSavedInstanceStateRestore()

        onNodeWithText("Test").assertIsOff()
    }
}
