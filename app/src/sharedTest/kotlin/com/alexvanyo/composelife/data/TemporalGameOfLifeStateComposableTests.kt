package com.alexvanyo.composelife.data

import androidx.compose.runtime.SideEffect
import androidx.compose.ui.test.junit4.StateRestorationTester
import androidx.compose.ui.test.junit4.createComposeRule
import androidx.test.ext.junit.runners.AndroidJUnit4
import com.alexvanyo.composelife.data.patterns.PondPattern
import com.alexvanyo.composelife.data.patterns.SixLongLinePattern
import com.alexvanyo.composelife.testutil.schedulerClock
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.test.StandardTestDispatcher
import kotlinx.coroutines.test.runTest
import org.junit.Assert.assertEquals
import org.junit.Rule
import org.junit.Test
import org.junit.runner.RunWith

@OptIn(ExperimentalCoroutinesApi::class)
@RunWith(AndroidJUnit4::class)
class TemporalGameOfLifeStateComposableTests {

    @get:Rule
    val composeTestRule = createComposeRule()

    @Test
    fun state_is_instance_state_saved_correctly() {
        val stateRestorationTester = StateRestorationTester(composeTestRule)

        // Extract the state from composition just for testing
        var extractedState: TemporalGameOfLifeState? = null

        stateRestorationTester.setContent {
            val temporalGameOfLifeState = rememberTemporalGameOfLifeState(
                cellState = PondPattern.seedCellState,
                isRunning = false,
                generationsPerStep = 5,
                targetStepsPerSecond = 30.0
            )

            SideEffect {
                extractedState = temporalGameOfLifeState
            }
        }

        stateRestorationTester.emulateSavedInstanceStateRestore()

        val restoredState = requireNotNull(extractedState)

        assertEquals(PondPattern.seedCellState, restoredState.cellState)
        assertEquals(TemporalGameOfLifeState.EvolutionStatus.Paused, restoredState.status)
        assertEquals(5, restoredState.generationsPerStep)
        assertEquals(30.0, restoredState.targetStepsPerSecond, 0.0001)
    }

    @Test
    fun state_is_advanced_correctly() = runTest {
        val dispatcher = StandardTestDispatcher(testScheduler)

        val temporalGameOfLifeState = TemporalGameOfLifeState(
            cellState = SixLongLinePattern.seedCellState,
            isRunning = true,
            generationsPerStep = 1,
            targetStepsPerSecond = 10.0
        )

        composeTestRule.setContent {
            rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = NaiveGameOfLifeAlgorithm(
                    backgroundDispatcher = dispatcher
                ),
                clock = schedulerClock
            )
        }

        composeTestRule.waitForIdle()

        assertEquals(SixLongLinePattern.seedCellState, temporalGameOfLifeState.cellState)
        assertEquals(
            TemporalGameOfLifeState.EvolutionStatus.Running(
                averageGenerationsPerSecond = 0.0
            ),
            temporalGameOfLifeState.status
        )

        SixLongLinePattern.cellStates.forEach { expectedCellState ->
            testScheduler.advanceTimeBy(100)
            composeTestRule.mainClock.advanceTimeBy(milliseconds = 100, ignoreFrameDuration = true)
            testScheduler.runCurrent()
            composeTestRule.awaitIdle()

            assertEquals(expectedCellState, temporalGameOfLifeState.cellState)
            assertEquals(
                TemporalGameOfLifeState.EvolutionStatus.Running(
                    averageGenerationsPerSecond = 10.0
                ),
                temporalGameOfLifeState.status
            )
        }
    }
}
