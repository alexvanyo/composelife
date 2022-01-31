package com.alexvanyo.composelife.ui

import android.content.Context
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
import androidx.test.ext.junit.runners.AndroidJUnit4
import com.alexvanyo.composelife.R
import com.alexvanyo.composelife.algorithm.HashLifeAlgorithm
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.dispatchers.dateTimeClock
import com.alexvanyo.composelife.model.rememberTemporalGameOfLifeState
import com.alexvanyo.composelife.model.rememberTemporalGameOfLifeStateMutator
import com.alexvanyo.composelife.patterns.SixLongLinePattern
import dagger.hilt.android.qualifiers.ApplicationContext
import dagger.hilt.android.testing.HiltAndroidRule
import dagger.hilt.android.testing.HiltAndroidTest
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.test.TestDispatcher
import kotlinx.coroutines.test.resetMain
import kotlinx.coroutines.test.runTest
import kotlinx.coroutines.test.setMain
import org.junit.After
import org.junit.Before
import org.junit.Rule
import org.junit.Test
import org.junit.runner.RunWith
import javax.inject.Inject

@OptIn(ExperimentalCoroutinesApi::class)
@HiltAndroidTest
@RunWith(AndroidJUnit4::class)
class InteractiveCellUniverseTests {

    @get:Rule
    val hiltAndroidRule = HiltAndroidRule(this)

    @get:Rule
    val composeTestRule = createComposeRule()

    @Inject
    @ApplicationContext
    lateinit var context: Context

    @Inject
    lateinit var testDispatcher: TestDispatcher

    @Inject
    lateinit var dispatchers: ComposeLifeDispatchers

    @Before
    fun setup() {
        hiltAndroidRule.inject()
        Dispatchers.setMain(testDispatcher)
    }

    @After
    fun teardown() {
        Dispatchers.resetMain()
    }

    @Test
    @OptIn(ExperimentalCoroutinesApi::class)
    fun six_long_line_evolves_correctly() = runTest {
        composeTestRule.mainClock.autoAdvance = false

        composeTestRule.setContent {
            val temporalGameOfLifeState = rememberTemporalGameOfLifeState(
                targetStepsPerSecond = 0.001
            )

            rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = HashLifeAlgorithm(
                    dispatchers = dispatchers
                ),
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
