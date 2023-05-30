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

import androidx.compose.foundation.clickable
import androidx.compose.foundation.text.BasicText
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.runtime.setValue
import androidx.compose.ui.Modifier
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.onNodeWithText
import androidx.compose.ui.test.performClick
import androidx.compose.ui.test.runComposeUiTest
import com.alexvanyo.composelife.algorithm.HashLifeAlgorithm
import com.alexvanyo.composelife.dispatchers.TestComposeLifeDispatchers
import com.alexvanyo.composelife.dispatchers.clock
import com.alexvanyo.composelife.kmpandroidrunner.KmpAndroidJUnit4
import com.alexvanyo.composelife.kmpstaterestorationtester.KmpStateRestorationTester
import com.alexvanyo.composelife.patterns.PondPattern
import com.alexvanyo.composelife.patterns.SingleCellPattern
import com.alexvanyo.composelife.patterns.SixLongLinePattern
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.launch
import kotlinx.coroutines.test.StandardTestDispatcher
import org.junit.runner.RunWith
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertIs

@OptIn(ExperimentalCoroutinesApi::class, ExperimentalTestApi::class)
@RunWith(KmpAndroidJUnit4::class)
class TemporalGameOfLifeStateComposableTests {

    private val testDispatcher = StandardTestDispatcher()

    private val dispatchers = TestComposeLifeDispatchers(testDispatcher)

    @Test
    fun state_is_instance_state_saved_correctly() = runComposeUiTest {
        val stateRestorationTester = KmpStateRestorationTester(this)

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

        waitForIdle()
        extractedState = null

        stateRestorationTester.emulateSavedInstanceStateRestore()
        waitForIdle()

        val restoredState = requireNotNull(extractedState)

        assertEquals(PondPattern.seedCellState, restoredState.cellState)
        assertEquals(TemporalGameOfLifeState.EvolutionStatus.Paused, restoredState.status)
        assertEquals(5, restoredState.generationsPerStep)
        assertEquals(30.0, restoredState.targetStepsPerSecond, 0.0001)
    }

    @Test
    fun state_is_advanced_correctly() = runComposeUiTest {
        val temporalGameOfLifeState = TemporalGameOfLifeState(
            seedCellState = SixLongLinePattern.seedCellState,
            isRunning = true,
            generationsPerStep = 1,
            targetStepsPerSecond = 60.0,
        )

        val hashLifeAlgorithm = HashLifeAlgorithm(
            dispatchers = dispatchers,
        )

        setContent {
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
            testDispatcher.scheduler.runCurrent()
            waitForIdle()
            testDispatcher.scheduler.advanceTimeBy(16)
            testDispatcher.scheduler.runCurrent()
            waitForIdle()

            assertEquals(expectedCellState, temporalGameOfLifeState.cellState)
            temporalGameOfLifeState.status.let { status ->
                assertIs<TemporalGameOfLifeState.EvolutionStatus.Running>(status)
                assertEquals(62.5, status.averageGenerationsPerSecond, 0.001)
            }
        }
    }

    @Test
    fun pausing_evolution_is_correct() = runComposeUiTest {
        val temporalGameOfLifeState = TemporalGameOfLifeState(
            seedCellState = SixLongLinePattern.seedCellState,
            isRunning = true,
            generationsPerStep = 1,
            targetStepsPerSecond = 60.0,
        )

        val hashLifeAlgorithm = HashLifeAlgorithm(
            dispatchers = dispatchers,
        )

        setContent {
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

        testDispatcher.scheduler.advanceTimeBy(8)
        testDispatcher.scheduler.runCurrent()
        waitForIdle()

        assertEquals(SixLongLinePattern.seedCellState, temporalGameOfLifeState.cellState)
        temporalGameOfLifeState.status.let { status ->
            assertIs<TemporalGameOfLifeState.EvolutionStatus.Running>(status)
            assertEquals(0.0, status.averageGenerationsPerSecond, 0.001)
        }

        testDispatcher.scheduler.runCurrent()
        waitForIdle()
        testDispatcher.scheduler.advanceTimeBy(8)
        testDispatcher.scheduler.runCurrent()
        waitForIdle()

        assertEquals(SixLongLinePattern.cellStates[0], temporalGameOfLifeState.cellState)
        temporalGameOfLifeState.status.let { status ->
            assertIs<TemporalGameOfLifeState.EvolutionStatus.Running>(status)
            assertEquals(62.5, status.averageGenerationsPerSecond, 0.001)
        }

        testDispatcher.scheduler.runCurrent()
        waitForIdle()
        testDispatcher.scheduler.advanceTimeBy(8)
        testDispatcher.scheduler.runCurrent()
        waitForIdle()

        assertEquals(SixLongLinePattern.cellStates[0], temporalGameOfLifeState.cellState)
        temporalGameOfLifeState.status.let { status ->
            assertIs<TemporalGameOfLifeState.EvolutionStatus.Running>(status)
            assertEquals(62.5, status.averageGenerationsPerSecond, 0.001)
        }

        testDispatcher.scheduler.runCurrent()
        waitForIdle()
        testDispatcher.scheduler.advanceTimeBy(8)
        testDispatcher.scheduler.runCurrent()
        waitForIdle()

        assertEquals(SixLongLinePattern.cellStates[1], temporalGameOfLifeState.cellState)
        temporalGameOfLifeState.status.let { status ->
            assertIs<TemporalGameOfLifeState.EvolutionStatus.Running>(status)
            assertEquals(62.5, status.averageGenerationsPerSecond, 0.001)
        }

        temporalGameOfLifeState.setIsRunning(false)

        testDispatcher.scheduler.runCurrent()
        waitForIdle()
        testDispatcher.scheduler.advanceTimeBy(1000)
        testDispatcher.scheduler.runCurrent()
        waitForIdle()

        assertEquals(SixLongLinePattern.cellStates[1], temporalGameOfLifeState.cellState)
        assertIs<TemporalGameOfLifeState.EvolutionStatus.Paused>(temporalGameOfLifeState.status)
    }

    @Test
    fun target_steps_evolution_is_correct() = runComposeUiTest {
        val temporalGameOfLifeState = TemporalGameOfLifeState(
            seedCellState = SixLongLinePattern.seedCellState,
            isRunning = true,
            generationsPerStep = 1,
            targetStepsPerSecond = 60.0,
        )

        val hashLifeAlgorithm = HashLifeAlgorithm(
            dispatchers = dispatchers,
        )

        setContent {
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

        testDispatcher.scheduler.advanceTimeBy(8)
        testDispatcher.scheduler.runCurrent()
        waitForIdle()

        assertEquals(SixLongLinePattern.seedCellState, temporalGameOfLifeState.cellState)
        temporalGameOfLifeState.status.let { status ->
            assertIs<TemporalGameOfLifeState.EvolutionStatus.Running>(status)
            assertEquals(0.0, status.averageGenerationsPerSecond, 0.001)
        }

        testDispatcher.scheduler.runCurrent()
        waitForIdle()
        testDispatcher.scheduler.advanceTimeBy(8)
        testDispatcher.scheduler.runCurrent()
        waitForIdle()

        assertEquals(SixLongLinePattern.cellStates[0], temporalGameOfLifeState.cellState)
        temporalGameOfLifeState.status.let { status ->
            assertIs<TemporalGameOfLifeState.EvolutionStatus.Running>(status)
            assertEquals(62.5, status.averageGenerationsPerSecond, 0.001)
        }

        testDispatcher.scheduler.runCurrent()
        waitForIdle()
        testDispatcher.scheduler.advanceTimeBy(8)
        testDispatcher.scheduler.runCurrent()
        waitForIdle()

        assertEquals(SixLongLinePattern.cellStates[0], temporalGameOfLifeState.cellState)
        temporalGameOfLifeState.status.let { status ->
            assertIs<TemporalGameOfLifeState.EvolutionStatus.Running>(status)
            assertEquals(62.5, status.averageGenerationsPerSecond, 0.001)
        }

        testDispatcher.scheduler.runCurrent()
        waitForIdle()
        testDispatcher.scheduler.advanceTimeBy(8)
        testDispatcher.scheduler.runCurrent()
        waitForIdle()

        assertEquals(SixLongLinePattern.cellStates[1], temporalGameOfLifeState.cellState)
        temporalGameOfLifeState.status.let { status ->
            assertIs<TemporalGameOfLifeState.EvolutionStatus.Running>(status)
            assertEquals(62.5, status.averageGenerationsPerSecond, 0.001)
        }

        temporalGameOfLifeState.targetStepsPerSecond = 10.0

        testDispatcher.scheduler.runCurrent()
        waitForIdle()
        testDispatcher.scheduler.advanceTimeBy(50)
        testDispatcher.scheduler.runCurrent()
        waitForIdle()

        assertEquals(SixLongLinePattern.cellStates[1], temporalGameOfLifeState.cellState)
        temporalGameOfLifeState.status.let { status ->
            assertIs<TemporalGameOfLifeState.EvolutionStatus.Running>(status)
            assertEquals(62.5, status.averageGenerationsPerSecond, 0.001)
        }

        testDispatcher.scheduler.runCurrent()
        waitForIdle()
        testDispatcher.scheduler.advanceTimeBy(50)
        testDispatcher.scheduler.runCurrent()
        waitForIdle()

        assertEquals(SixLongLinePattern.cellStates[2], temporalGameOfLifeState.cellState)
        temporalGameOfLifeState.status.let { status ->
            assertIs<TemporalGameOfLifeState.EvolutionStatus.Running>(status)
            assertEquals(22.727, status.averageGenerationsPerSecond, 0.001)
        }
    }

    @Test
    fun setting_evolution_is_correct() = runComposeUiTest {
        val temporalGameOfLifeState = TemporalGameOfLifeState(
            seedCellState = SixLongLinePattern.seedCellState,
            isRunning = true,
            generationsPerStep = 1,
            targetStepsPerSecond = 60.0,
        )

        val hashLifeAlgorithm = HashLifeAlgorithm(
            dispatchers = dispatchers,
        )

        setContent {
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

        testDispatcher.scheduler.advanceTimeBy(8)
        testDispatcher.scheduler.runCurrent()
        waitForIdle()

        assertEquals(SixLongLinePattern.seedCellState, temporalGameOfLifeState.cellState)
        temporalGameOfLifeState.status.let { status ->
            assertIs<TemporalGameOfLifeState.EvolutionStatus.Running>(status)
            assertEquals(0.0, status.averageGenerationsPerSecond, 0.001)
        }

        testDispatcher.scheduler.runCurrent()
        waitForIdle()
        testDispatcher.scheduler.advanceTimeBy(8)
        testDispatcher.scheduler.runCurrent()
        waitForIdle()

        assertEquals(SixLongLinePattern.cellStates[0], temporalGameOfLifeState.cellState)
        temporalGameOfLifeState.status.let { status ->
            assertIs<TemporalGameOfLifeState.EvolutionStatus.Running>(status)
            assertEquals(62.5, status.averageGenerationsPerSecond, 0.001)
        }

        testDispatcher.scheduler.runCurrent()
        waitForIdle()
        testDispatcher.scheduler.advanceTimeBy(8)
        testDispatcher.scheduler.runCurrent()
        waitForIdle()

        assertEquals(SixLongLinePattern.cellStates[0], temporalGameOfLifeState.cellState)
        temporalGameOfLifeState.status.let { status ->
            assertIs<TemporalGameOfLifeState.EvolutionStatus.Running>(status)
            assertEquals(62.5, status.averageGenerationsPerSecond, 0.001)
        }

        testDispatcher.scheduler.runCurrent()
        waitForIdle()
        testDispatcher.scheduler.advanceTimeBy(8)
        testDispatcher.scheduler.runCurrent()
        waitForIdle()

        assertEquals(SixLongLinePattern.cellStates[1], temporalGameOfLifeState.cellState)
        temporalGameOfLifeState.status.let { status ->
            assertIs<TemporalGameOfLifeState.EvolutionStatus.Running>(status)
            assertEquals(62.5, status.averageGenerationsPerSecond, 0.001)
        }

        temporalGameOfLifeState.cellState = SingleCellPattern.seedCellState

        testDispatcher.scheduler.runCurrent()
        waitForIdle()
        testDispatcher.scheduler.advanceTimeBy(8)
        testDispatcher.scheduler.runCurrent()
        waitForIdle()

        assertEquals(SingleCellPattern.seedCellState, temporalGameOfLifeState.cellState)
        temporalGameOfLifeState.status.let { status ->
            assertIs<TemporalGameOfLifeState.EvolutionStatus.Running>(status)
            assertEquals(62.5, status.averageGenerationsPerSecond, 0.001)
        }

        testDispatcher.scheduler.runCurrent()
        waitForIdle()
        testDispatcher.scheduler.advanceTimeBy(8)
        testDispatcher.scheduler.runCurrent()
        waitForIdle()

        assertEquals(SingleCellPattern.cellStates[0], temporalGameOfLifeState.cellState)
        temporalGameOfLifeState.status.let { status ->
            assertIs<TemporalGameOfLifeState.EvolutionStatus.Running>(status)
            assertEquals(62.5, status.averageGenerationsPerSecond, 0.001)
        }
    }

    @Test
    fun multiple_evolutions_is_correct() = runComposeUiTest {
        val temporalGameOfLifeState = TemporalGameOfLifeState(
            seedCellState = SixLongLinePattern.seedCellState,
            isRunning = true,
            generationsPerStep = 1,
            targetStepsPerSecond = 60.0,
        )

        val hashLifeAlgorithm = HashLifeAlgorithm(
            dispatchers = dispatchers,
        )

        var runFirstMutator by mutableStateOf(true)

        setContent {
            val temporalGameOfLifeStateMutator = rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = hashLifeAlgorithm,
                clock = testDispatcher.scheduler.clock,
                dispatchers = dispatchers,
            )

            if (runFirstMutator) {
                LaunchedEffect(temporalGameOfLifeStateMutator) {
                    temporalGameOfLifeStateMutator.update()
                }
            }

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

        testDispatcher.scheduler.advanceTimeBy(8)
        testDispatcher.scheduler.runCurrent()
        waitForIdle()

        assertEquals(SixLongLinePattern.seedCellState, temporalGameOfLifeState.cellState)
        temporalGameOfLifeState.status.let { status ->
            assertIs<TemporalGameOfLifeState.EvolutionStatus.Running>(status)
            assertEquals(0.0, status.averageGenerationsPerSecond, 0.001)
        }

        testDispatcher.scheduler.runCurrent()
        waitForIdle()
        testDispatcher.scheduler.advanceTimeBy(8)
        testDispatcher.scheduler.runCurrent()
        waitForIdle()

        assertEquals(SixLongLinePattern.cellStates[0], temporalGameOfLifeState.cellState)
        temporalGameOfLifeState.status.let { status ->
            assertIs<TemporalGameOfLifeState.EvolutionStatus.Running>(status)
            assertEquals(62.5, status.averageGenerationsPerSecond, 0.001)
        }

        testDispatcher.scheduler.runCurrent()
        waitForIdle()
        testDispatcher.scheduler.advanceTimeBy(8)
        testDispatcher.scheduler.runCurrent()
        waitForIdle()

        assertEquals(SixLongLinePattern.cellStates[0], temporalGameOfLifeState.cellState)
        temporalGameOfLifeState.status.let { status ->
            assertIs<TemporalGameOfLifeState.EvolutionStatus.Running>(status)
            assertEquals(62.5, status.averageGenerationsPerSecond, 0.001)
        }

        testDispatcher.scheduler.runCurrent()
        waitForIdle()
        testDispatcher.scheduler.advanceTimeBy(8)
        testDispatcher.scheduler.runCurrent()
        waitForIdle()

        assertEquals(SixLongLinePattern.cellStates[1], temporalGameOfLifeState.cellState)
        temporalGameOfLifeState.status.let { status ->
            assertIs<TemporalGameOfLifeState.EvolutionStatus.Running>(status)
            assertEquals(62.5, status.averageGenerationsPerSecond, 0.001)
        }

        runFirstMutator = false

        testDispatcher.scheduler.runCurrent()
        waitForIdle()
        testDispatcher.scheduler.advanceTimeBy(8)
        testDispatcher.scheduler.runCurrent()
        waitForIdle()

        assertEquals(SixLongLinePattern.cellStates[1], temporalGameOfLifeState.cellState)
        temporalGameOfLifeState.status.let { status ->
            assertIs<TemporalGameOfLifeState.EvolutionStatus.Running>(status)
            assertEquals(62.5, status.averageGenerationsPerSecond, 0.001)
        }

        testDispatcher.scheduler.runCurrent()
        waitForIdle()
        testDispatcher.scheduler.advanceTimeBy(8)
        testDispatcher.scheduler.runCurrent()
        waitForIdle()

        assertEquals(SixLongLinePattern.cellStates[2], temporalGameOfLifeState.cellState)
        temporalGameOfLifeState.status.let { status ->
            assertIs<TemporalGameOfLifeState.EvolutionStatus.Running>(status)
            assertEquals(62.5, status.averageGenerationsPerSecond, 0.001)
        }
    }

    @Test
    fun state_is_advanced_correctly_with_step() = runComposeUiTest {
        val temporalGameOfLifeState = TemporalGameOfLifeState(
            seedCellState = SixLongLinePattern.seedCellState,
            isRunning = false,
            generationsPerStep = 1,
            targetStepsPerSecond = 60.0,
        )

        val hashLifeAlgorithm = HashLifeAlgorithm(
            dispatchers = dispatchers,
        )

        setContent {
            val temporalGameOfLifeStateMutator = rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = hashLifeAlgorithm,
                clock = testDispatcher.scheduler.clock,
                dispatchers = dispatchers,
            )

            LaunchedEffect(temporalGameOfLifeStateMutator) {
                temporalGameOfLifeStateMutator.update()
            }

            val coroutineScope = rememberCoroutineScope()

            BasicText(
                text = "Step",
                modifier = Modifier.clickable {
                    coroutineScope.launch {
                        temporalGameOfLifeState.step()
                    }
                },
            )
        }

        assertEquals(SixLongLinePattern.seedCellState, temporalGameOfLifeState.cellState)
        assertEquals(
            TemporalGameOfLifeState.EvolutionStatus.Paused,
            temporalGameOfLifeState.status,
        )

        SixLongLinePattern.cellStates.forEach { expectedCellState ->
            testDispatcher.scheduler.runCurrent()
            waitForIdle()
            onNodeWithText("Step").performClick()
            testDispatcher.scheduler.runCurrent()
            waitForIdle()

            assertEquals(expectedCellState, temporalGameOfLifeState.cellState)
            assertEquals(TemporalGameOfLifeState.EvolutionStatus.Paused, temporalGameOfLifeState.status)
        }
    }
}
