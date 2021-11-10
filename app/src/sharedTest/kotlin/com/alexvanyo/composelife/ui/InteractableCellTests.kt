package com.alexvanyo.composelife.ui

import androidx.compose.foundation.layout.size
import androidx.compose.ui.Modifier
import androidx.compose.ui.test.junit4.createComposeRule
import androidx.compose.ui.test.onNodeWithContentDescription
import androidx.compose.ui.test.performClick
import androidx.compose.ui.unit.dp
import androidx.test.ext.junit.runners.AndroidJUnit4
import org.junit.Assert.assertEquals
import org.junit.Rule
import org.junit.Test
import org.junit.runner.RunWith

@RunWith(AndroidJUnit4::class)
class InteractableCellTests {

    @get:Rule
    val composeTestRule = createComposeRule()

    @Test
    fun alive_cell_calls_correct_function() {
        var onValueChangeResult: Boolean? = null

        composeTestRule.setContent {
            InteractableCell(
                modifier = Modifier
                    .size(32.dp),
                isAlive = true,
                contentDescription = "test cell",
                onValueChange = { onValueChangeResult = it }
            )
        }

        composeTestRule.onNodeWithContentDescription("test cell").performClick()

        assertEquals(false, onValueChangeResult)
    }

    @Test
    fun dead_cell_calls_correct_function() {
        var onValueChangeResult: Boolean? = null

        composeTestRule.setContent {
            InteractableCell(
                modifier = Modifier
                    .size(32.dp),
                isAlive = false,
                contentDescription = "test cell",
                onValueChange = { onValueChangeResult = it }
            )
        }

        composeTestRule.onNodeWithContentDescription("test cell").performClick()

        assertEquals(true, onValueChangeResult)
    }
}
