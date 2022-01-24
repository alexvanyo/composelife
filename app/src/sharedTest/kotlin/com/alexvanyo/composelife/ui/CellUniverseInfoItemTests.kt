package com.alexvanyo.composelife.ui

import androidx.compose.foundation.layout.Column
import androidx.compose.ui.test.assertIsDisplayed
import androidx.compose.ui.test.assertIsOff
import androidx.compose.ui.test.assertIsOn
import androidx.compose.ui.test.isToggleable
import androidx.compose.ui.test.junit4.StateRestorationTester
import androidx.compose.ui.test.junit4.createComposeRule
import androidx.compose.ui.test.onNodeWithText
import androidx.compose.ui.test.performClick
import androidx.test.ext.junit.runners.AndroidJUnit4
import org.junit.Assert.assertFalse
import org.junit.Assert.assertTrue
import org.junit.Rule
import org.junit.Test
import org.junit.runner.RunWith

@RunWith(AndroidJUnit4::class)
class CellUniverseInfoItemTests {

    @get:Rule
    val composeTestRule = createComposeRule()

    @Test
    fun editing_preview() {
        composeTestRule.setContent {
            CellUniverseInfoItemEditingPreview()
        }
    }

    @Test
    fun not_editing_preview() {
        composeTestRule.setContent {
            CellUniverseInfoItemNotEditingPreview()
        }
    }

    @Test
    fun can_check_while_editing() {
        val cellUniverseInfoItemState = CellUniverseInfoItemState()

        composeTestRule.setContent {
            Column {
                InfoItem(
                    cellUniverseInfoItemContent = CellUniverseInfoItemContent(cellUniverseInfoItemState) { "Test" },
                    isEditing = true
                )
            }
        }

        composeTestRule.onNode(isToggleable()).assertIsOn().performClick()

        assertFalse(cellUniverseInfoItemState.isChecked)

        composeTestRule.onNode(isToggleable()).assertIsOff()
    }

    @Test
    fun can_uncheck_while_editing() {
        val cellUniverseInfoItemState = CellUniverseInfoItemState(isChecked = false)

        composeTestRule.setContent {
            Column {
                InfoItem(
                    cellUniverseInfoItemContent = CellUniverseInfoItemContent(cellUniverseInfoItemState) { "Test" },
                    isEditing = true
                )
            }
        }

        composeTestRule.onNode(isToggleable()).assertIsOff().performClick()

        assertTrue(cellUniverseInfoItemState.isChecked)

        composeTestRule.onNode(isToggleable()).assertIsOn()
    }

    @Test
    fun unchecked_item_is_hidden_while_not_editing() {
        val cellUniverseInfoItemState = CellUniverseInfoItemState(isChecked = false)

        composeTestRule.setContent {
            Column {
                InfoItem(
                    cellUniverseInfoItemContent = CellUniverseInfoItemContent(cellUniverseInfoItemState) { "Test" },
                    isEditing = false
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
                    isEditing = false
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
                    isEditing = true
                )
            }
        }

        composeTestRule.onNode(isToggleable()).assertIsOn().performClick()
        composeTestRule.onNode(isToggleable()).assertIsOff()

        stateRestorationTester.emulateSavedInstanceStateRestore()

        composeTestRule.onNode(isToggleable()).assertIsOff()
    }
}
