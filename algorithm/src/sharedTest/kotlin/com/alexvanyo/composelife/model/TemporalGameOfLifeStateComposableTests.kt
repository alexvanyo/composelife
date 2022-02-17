package com.alexvanyo.composelife.model

import androidx.compose.ui.test.junit4.StateRestorationTester
import androidx.compose.ui.test.junit4.createComposeRule
import androidx.test.ext.junit.runners.AndroidJUnit4
import com.alexvanyo.composelife.algorithm.HashLifeAlgorithm
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.dispatchers.dateTimeClock
import com.alexvanyo.composelife.patterns.PondPattern
import com.alexvanyo.composelife.patterns.SixLongLinePattern
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
import kotlin.test.assertEquals
import kotlin.test.assertIs

@OptIn(ExperimentalCoroutinesApi::class)
@HiltAndroidTest
@RunWith(AndroidJUnit4::class)
class TemporalGameOfLifeStateComposableTests {

    @get:Rule
    val hiltAndroidRule = HiltAndroidRule(this)

    @get:Rule
    val composeTestRule = createComposeRule()

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
    fun state_is_instance_state_saved_correctly() = runTest {
        val stateRestorationTester = StateRestorationTester(composeTestRule)

        // Extract the state from composition for testing
        var extractedState: TemporalGameOfLifeState?

        stateRestorationTester.setContent {
            extractedState = rememberTemporalGameOfLifeState(
                cellState = PondPattern.seedCellState,
                isRunning = false,
                generationsPerStep = 5,
                targetStepsPerSecond = 30.0
            )
        }

        composeTestRule.awaitIdle()
        extractedState = null

        stateRestorationTester.emulateSavedInstanceStateRestore()
        composeTestRule.awaitIdle()

        val restoredState = requireNotNull(extractedState)

        assertEquals(PondPattern.seedCellState, restoredState.cellState)
        assertEquals(TemporalGameOfLifeState.EvolutionStatus.Paused, restoredState.status)
        assertEquals(5, restoredState.generationsPerStep)
        assertEquals(30.0, restoredState.targetStepsPerSecond, 0.0001)
    }

    @Test
    fun state_is_advanced_correctly() = runTest {
        val temporalGameOfLifeState = TemporalGameOfLifeState(
            cellState = SixLongLinePattern.seedCellState,
            isRunning = true,
            generationsPerStep = 1,
            targetStepsPerSecond = 60.0
        )

        val hashLifeAlgorithm = HashLifeAlgorithm(
            dispatchers = dispatchers
        )

        composeTestRule.mainClock.autoAdvance = false

        composeTestRule.setContent {
            rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = hashLifeAlgorithm,
                clock = composeTestRule.mainClock.dateTimeClock
            )
        }

        composeTestRule.awaitIdle()

        assertEquals(SixLongLinePattern.seedCellState, temporalGameOfLifeState.cellState)
        assertEquals(
            TemporalGameOfLifeState.EvolutionStatus.Running(
                averageGenerationsPerSecond = 0.0
            ),
            temporalGameOfLifeState.status
        )

        SixLongLinePattern.cellStates.forEach { expectedCellState ->
            composeTestRule.mainClock.advanceTimeBy(16)
            testScheduler.runCurrent()
            composeTestRule.awaitIdle()

            assertEquals(expectedCellState, temporalGameOfLifeState.cellState)
            temporalGameOfLifeState.status.let { status ->
                assertIs<TemporalGameOfLifeState.EvolutionStatus.Running>(status)
                assertEquals(62.5, status.averageGenerationsPerSecond, 0.001)
            }
        }
    }

    @Test
    fun state_is_advanced_correctly_with_step() = runTest {
        val temporalGameOfLifeState = TemporalGameOfLifeState(
            cellState = SixLongLinePattern.seedCellState,
            isRunning = false,
            generationsPerStep = 1,
            targetStepsPerSecond = 60.0
        )

        val hashLifeAlgorithm = HashLifeAlgorithm(
            dispatchers = dispatchers
        )

        composeTestRule.mainClock.autoAdvance = false

        composeTestRule.setContent {
            rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = hashLifeAlgorithm,
                clock = composeTestRule.mainClock.dateTimeClock
            )
        }

        composeTestRule.awaitIdle()

        assertEquals(SixLongLinePattern.seedCellState, temporalGameOfLifeState.cellState)
        assertEquals(
            TemporalGameOfLifeState.EvolutionStatus.Paused,
            temporalGameOfLifeState.status
        )

        SixLongLinePattern.cellStates.forEach { expectedCellState ->
            temporalGameOfLifeState.step()
            testScheduler.runCurrent()
            composeTestRule.awaitIdle()

            assertEquals(expectedCellState, temporalGameOfLifeState.cellState)
            assertEquals(TemporalGameOfLifeState.EvolutionStatus.Paused, temporalGameOfLifeState.status)
        }
    }
}
