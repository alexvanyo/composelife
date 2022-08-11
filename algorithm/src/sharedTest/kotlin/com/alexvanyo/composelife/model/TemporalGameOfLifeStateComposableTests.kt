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

package com.alexvanyo.composelife.model

import androidx.compose.runtime.LaunchedEffect
import androidx.compose.ui.test.junit4.StateRestorationTester
import androidx.compose.ui.test.junit4.createComposeRule
import androidx.test.ext.junit.runners.AndroidJUnit4
import com.alexvanyo.composelife.algorithm.HashLifeAlgorithm
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.dispatchers.clock
import com.alexvanyo.composelife.patterns.PondPattern
import com.alexvanyo.composelife.patterns.SixLongLinePattern
import dagger.hilt.android.testing.HiltAndroidRule
import dagger.hilt.android.testing.HiltAndroidTest
import kotlinx.coroutines.CoroutineStart
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.launch
import kotlinx.coroutines.test.TestDispatcher
import kotlinx.coroutines.test.runTest
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
    }

    @Test
    fun state_is_instance_state_saved_correctly() = runTest {
        val stateRestorationTester = StateRestorationTester(composeTestRule)

        // Extract the state from composition for testing
        var extractedState: TemporalGameOfLifeState?

        stateRestorationTester.setContent {
            extractedState = rememberTemporalGameOfLifeState(
                seedCellState = PondPattern.seedCellState,
                isRunning = false,
                generationsPerStep = 5,
                targetStepsPerSecond = 30.0,
            )
        }

        composeTestRule.waitForIdle()
        extractedState = null

        stateRestorationTester.emulateSavedInstanceStateRestore()
        composeTestRule.waitForIdle()

        val restoredState = requireNotNull(extractedState)

        assertEquals(PondPattern.seedCellState, restoredState.cellState)
        assertEquals(TemporalGameOfLifeState.EvolutionStatus.Paused, restoredState.status)
        assertEquals(5, restoredState.generationsPerStep)
        assertEquals(30.0, restoredState.targetStepsPerSecond, 0.0001)
    }

    @Test
    fun state_is_advanced_correctly() = runTest {
        val temporalGameOfLifeState = TemporalGameOfLifeState(
            seedCellState = SixLongLinePattern.seedCellState,
            isRunning = true,
            generationsPerStep = 1,
            targetStepsPerSecond = 60.0,
        )

        val hashLifeAlgorithm = HashLifeAlgorithm(
            dispatchers = dispatchers,
        )

        composeTestRule.setContent {
            val temporalGameOfLifeStateMutator = rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = hashLifeAlgorithm,
                clock = testDispatcher.scheduler.clock,
                dispatchers = dispatchers,
            )

            LaunchedEffect(temporalGameOfLifeStateMutator) {
                temporalGameOfLifeStateMutator.update()
            }
        }

        assertEquals(SixLongLinePattern.seedCellState, temporalGameOfLifeState.cellState)
        assertEquals(
            TemporalGameOfLifeState.EvolutionStatus.Running(
                averageGenerationsPerSecond = 0.0,
            ),
            temporalGameOfLifeState.status,
        )

        SixLongLinePattern.cellStates.forEach { expectedCellState ->
            testDispatcher.scheduler.advanceTimeBy(16)
            testDispatcher.scheduler.runCurrent()
            composeTestRule.waitForIdle()

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
            seedCellState = SixLongLinePattern.seedCellState,
            isRunning = false,
            generationsPerStep = 1,
            targetStepsPerSecond = 60.0,
        )

        val hashLifeAlgorithm = HashLifeAlgorithm(
            dispatchers = dispatchers,
        )

        composeTestRule.setContent {
            val temporalGameOfLifeStateMutator = rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = hashLifeAlgorithm,
                clock = testDispatcher.scheduler.clock,
                dispatchers = dispatchers,
            )

            LaunchedEffect(temporalGameOfLifeStateMutator) {
                temporalGameOfLifeStateMutator.update()
            }
        }

        composeTestRule.waitForIdle()

        assertEquals(SixLongLinePattern.seedCellState, temporalGameOfLifeState.cellState)
        assertEquals(
            TemporalGameOfLifeState.EvolutionStatus.Paused,
            temporalGameOfLifeState.status,
        )

        SixLongLinePattern.cellStates.forEach { expectedCellState ->
            launch(start = CoroutineStart.UNDISPATCHED) { temporalGameOfLifeState.step() }
            testDispatcher.scheduler.runCurrent()
            composeTestRule.waitForIdle()

            assertEquals(expectedCellState, temporalGameOfLifeState.cellState)
            assertEquals(TemporalGameOfLifeState.EvolutionStatus.Paused, temporalGameOfLifeState.status)
        }
    }
}
