package com.alexvanyo.composelife.ui

import android.app.Application
import androidx.compose.ui.test.assertIsOff
import androidx.compose.ui.test.assertIsOn
import androidx.compose.ui.test.click
import androidx.compose.ui.test.junit4.createComposeRule
import androidx.compose.ui.test.onNodeWithContentDescription
import androidx.compose.ui.test.performTouchInput
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.IntRect
import androidx.compose.ui.unit.dp
import androidx.test.core.app.ApplicationProvider
import androidx.test.ext.junit.runners.AndroidJUnit4
import com.alexvanyo.composelife.R
import com.alexvanyo.composelife.data.model.MutableGameOfLifeState
import com.alexvanyo.composelife.data.model.toCellState
import org.junit.Assert.assertEquals
import org.junit.Rule
import org.junit.Test
import org.junit.runner.RunWith

@RunWith(AndroidJUnit4::class)
class InteractableCellsTests {

    @get:Rule
    val composeTestRule = createComposeRule()

    private val applicationContext = ApplicationProvider.getApplicationContext<Application>()

    @Test
    fun cells_are_displayed_correctly() {
        val mutableGameOfLifeState = MutableGameOfLifeState(
            cellState = setOf(
                0 to 0,
                0 to 2,
                0 to 4,
                2 to 0,
                2 to 2,
                2 to 4,
                4 to 0,
                4 to 2,
                4 to 4
            ).toCellState()
        )

        composeTestRule.setContent {
            InteractableCells(
                gameOfLifeState = mutableGameOfLifeState,
                scaledCellDpSize = 10.dp,
                cellWindow = IntRect(
                    IntOffset(0, 0),
                    IntOffset(8, 8)
                ),
            )
        }

        composeTestRule
            .onNodeWithContentDescription(
                applicationContext.getString(R.string.cell_content_description, 0, 0)
            )
            .assertIsOn()

        composeTestRule
            .onNodeWithContentDescription(
                applicationContext.getString(R.string.cell_content_description, 0, 1)
            )
            .assertIsOff()

        composeTestRule
            .onNodeWithContentDescription(
                applicationContext.getString(R.string.cell_content_description, 0, 2)
            )
            .assertIsOn()

        composeTestRule
            .onNodeWithContentDescription(
                applicationContext.getString(R.string.cell_content_description, 0, 3)
            )
            .assertIsOff()

        composeTestRule
            .onNodeWithContentDescription(
                applicationContext.getString(R.string.cell_content_description, 0, 4)
            )
            .assertIsOn()

        composeTestRule
            .onNodeWithContentDescription(
                applicationContext.getString(R.string.cell_content_description, 2, 0)
            )
            .assertIsOn()

        composeTestRule
            .onNodeWithContentDescription(
                applicationContext.getString(R.string.cell_content_description, 2, 1)
            )
            .assertIsOff()

        composeTestRule
            .onNodeWithContentDescription(
                applicationContext.getString(R.string.cell_content_description, 2, 2)
            )
            .assertIsOn()

        composeTestRule
            .onNodeWithContentDescription(
                applicationContext.getString(R.string.cell_content_description, 2, 3)
            )
            .assertIsOff()

        composeTestRule
            .onNodeWithContentDescription(
                applicationContext.getString(R.string.cell_content_description, 2, 4)
            )
            .assertIsOn()

        composeTestRule
            .onNodeWithContentDescription(
                applicationContext.getString(R.string.cell_content_description, 8, 8)
            )
            .assertExists()

        composeTestRule
            .onNodeWithContentDescription(
                applicationContext.getString(R.string.cell_content_description, -1, -1)
            )
            .assertDoesNotExist()

        composeTestRule
            .onNodeWithContentDescription(
                applicationContext.getString(R.string.cell_content_description, 9, 9)
            )
            .assertDoesNotExist()
    }

    @Test
    fun clicking_on_cell_updates_state() {
        val mutableGameOfLifeState = MutableGameOfLifeState(
            cellState = setOf(
                0 to 0,
                0 to 2,
                0 to 4,
                2 to 0,
                2 to 2,
                2 to 4,
                4 to 0,
                4 to 2,
                4 to 4
            ).toCellState()
        )

        composeTestRule.setContent {
            InteractableCells(
                gameOfLifeState = mutableGameOfLifeState,
                scaledCellDpSize = 10.dp,
                cellWindow = IntRect(
                    IntOffset(0, 0),
                    IntOffset(8, 8)
                )
            )
        }

        composeTestRule
            .onNodeWithContentDescription(
                applicationContext.getString(R.string.cell_content_description, 2, 4)
            )
            .assertIsOn()
            .performTouchInput { click(topLeft) }

        assertEquals(
            setOf(
                0 to 0,
                0 to 2,
                0 to 4,
                2 to 0,
                2 to 2,
                4 to 0,
                4 to 2,
                4 to 4
            ).toCellState(),
            mutableGameOfLifeState.cellState
        )
    }
}
