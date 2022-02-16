package com.alexvanyo.composelife.ui

import androidx.compose.foundation.layout.size
import androidx.compose.ui.Modifier
import androidx.compose.ui.test.assertIsOn
import androidx.compose.ui.test.click
import androidx.compose.ui.test.junit4.createComposeRule
import androidx.compose.ui.test.onNodeWithContentDescription
import androidx.compose.ui.test.performClick
import androidx.compose.ui.test.performTouchInput
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.R
import com.alexvanyo.composelife.algorithm.HashLifeAlgorithm
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.dispatchers.dateTimeClock
import com.alexvanyo.composelife.model.rememberTemporalGameOfLifeState
import com.alexvanyo.composelife.model.rememberTemporalGameOfLifeStateMutator
import com.alexvanyo.composelife.patterns.SixLongLinePattern
import com.alexvanyo.composelife.test.BaseAndroidTest
import dagger.hilt.android.testing.BindValue
import dagger.hilt.android.testing.HiltAndroidTest
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.test.runTest
import org.junit.Rule
import org.junit.Test
import javax.inject.Inject

@OptIn(ExperimentalCoroutinesApi::class)
@HiltAndroidTest
class InteractiveCellUniverseTests : BaseAndroidTest() {

    @get:Rule
    val composeTestRule = createComposeRule()

    @BindValue
    val fileProvider = preferencesRule.fileProvider

    @Inject
    lateinit var dispatchers: ComposeLifeDispatchers

    @Test
    fun six_long_line_evolves_correctly() = runTest {
        val hashLifeAlgorithm = HashLifeAlgorithm(
            dispatchers = dispatchers
        )

        composeTestRule.mainClock.autoAdvance = false

        composeTestRule.setContent {
            val temporalGameOfLifeState = rememberTemporalGameOfLifeState(
                targetStepsPerSecond = 0.001
            )

            rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = hashLifeAlgorithm,
                clock = composeTestRule.mainClock.dateTimeClock
            )

            InteractiveCellUniverse(
                temporalGameOfLifeState = temporalGameOfLifeState,
                modifier = Modifier.size(480.dp)
            )
        }

        composeTestRule.awaitIdle()

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.pause))
            .performClick()

        SixLongLinePattern.seedCellState.offsetBy(IntOffset(-4, -3)).aliveCells.forEach { cell ->
            composeTestRule
                .onNodeWithContentDescription(
                    context.getString(R.string.cell_content_description, cell.x, cell.y)
                )
                .performTouchInput { click(topLeft) }
        }

        composeTestRule.awaitIdle()

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.play))
            .performClick()

        composeTestRule.awaitIdle()

        composeTestRule.mainClock.advanceTimeBy(16)

        SixLongLinePattern.cellStates.forEach { expectedCellState ->
            composeTestRule.mainClock.advanceTimeBy(1_000_000 - 16)
            testScheduler.runCurrent()
            composeTestRule.awaitIdle()
            composeTestRule.mainClock.advanceTimeBy(16)
            composeTestRule.awaitIdle()

            expectedCellState.offsetBy(IntOffset(-4, -3)).aliveCells.forEach { cell ->
                composeTestRule
                    .onNodeWithContentDescription(
                        context.getString(R.string.cell_content_description, cell.x, cell.y)
                    )
                    .assertIsOn()
            }
        }
    }

    @Test
    fun six_long_line_evolves_correctly_with_step() = runTest {
        val hashLifeAlgorithm = HashLifeAlgorithm(
            dispatchers = dispatchers
        )

        composeTestRule.mainClock.autoAdvance = false

        composeTestRule.setContent {
            val temporalGameOfLifeState = rememberTemporalGameOfLifeState(
                targetStepsPerSecond = 0.001
            )

            rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = hashLifeAlgorithm,
                clock = composeTestRule.mainClock.dateTimeClock
            )

            InteractiveCellUniverse(
                temporalGameOfLifeState = temporalGameOfLifeState,
                modifier = Modifier.size(480.dp)
            )
        }

        composeTestRule.awaitIdle()

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.pause))
            .performClick()

        composeTestRule.awaitIdle()

        SixLongLinePattern.seedCellState.offsetBy(IntOffset(-4, -3)).aliveCells.forEach { cell ->
            composeTestRule
                .onNodeWithContentDescription(
                    context.getString(R.string.cell_content_description, cell.x, cell.y)
                )
                .performTouchInput { click(topLeft) }
        }

        composeTestRule.awaitIdle()

        SixLongLinePattern.cellStates.forEach { expectedCellState ->
            composeTestRule
                .onNodeWithContentDescription(context.getString(R.string.step))
                .performClick()

            testScheduler.runCurrent()
            composeTestRule.awaitIdle()
            composeTestRule.mainClock.advanceTimeByFrame()
            composeTestRule.awaitIdle()

            expectedCellState.offsetBy(IntOffset(-4, -3)).aliveCells.forEach { cell ->
                composeTestRule
                    .onNodeWithContentDescription(
                        context.getString(R.string.cell_content_description, cell.x, cell.y)
                    )
                    .assertIsOn()
            }
        }
    }
}
