package com.alexvanyo.composelife.ui

import androidx.compose.foundation.layout.size
import androidx.compose.ui.Modifier
import androidx.compose.ui.test.assertIsOff
import androidx.compose.ui.test.assertIsOn
import androidx.compose.ui.test.junit4.createComposeRule
import androidx.compose.ui.test.onNodeWithContentDescription
import androidx.compose.ui.test.performClick
import androidx.compose.ui.unit.dp
import androidx.test.ext.junit.runners.AndroidJUnit4
import com.alexvanyo.composelife.preferences.CurrentShape
import org.junit.Rule
import org.junit.Test
import org.junit.runner.RunWith
import kotlin.test.assertEquals

@RunWith(AndroidJUnit4::class)
class InteractableCellTests {

    @get:Rule
    val composeTestRule = createComposeRule()

    @Test
    fun alive_cell_preview() {
        composeTestRule.setContent {
            AliveCellPreview()
        }
    }

    @Test
    fun dead_cell_preview() {
        composeTestRule.setContent {
            DeadCellPreview()
        }
    }

    @Test
    fun alive_cell_calls_correct_function() {
        var onValueChangeResult: Boolean? = null

        composeTestRule.setContent {
            InteractableCell(
                modifier = Modifier
                    .size(32.dp),
                isAlive = true,
                shape = CurrentShape.RoundRectangle(
                    sizeFraction = 1f,
                    cornerFraction = 0f
                ),
                contentDescription = "test cell",
                onValueChange = { onValueChangeResult = it }
            )
        }

        composeTestRule.onNodeWithContentDescription("test cell")
            .assertIsOn()
            .performClick()

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
                shape = CurrentShape.RoundRectangle(
                    sizeFraction = 1f,
                    cornerFraction = 0f
                ),
                contentDescription = "test cell",
                onValueChange = { onValueChangeResult = it }
            )
        }

        composeTestRule.onNodeWithContentDescription("test cell")
            .assertIsOff()
            .performClick()

        assertEquals(true, onValueChangeResult)
    }
}
