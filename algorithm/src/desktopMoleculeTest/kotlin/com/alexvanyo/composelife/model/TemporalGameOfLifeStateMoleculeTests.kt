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

import androidx.compose.runtime.BroadcastFrameClock
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.setValue
import app.cash.molecule.RecompositionMode
import app.cash.molecule.moleculeFlow
import app.cash.turbine.test
import com.alexvanyo.composelife.algorithm.HashLifeAlgorithm
import com.alexvanyo.composelife.dispatchers.TestComposeLifeDispatchers
import com.alexvanyo.composelife.dispatchers.clock
import com.alexvanyo.composelife.patterns.SingleCellPattern
import com.alexvanyo.composelife.patterns.SixLongLinePattern
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.test.StandardTestDispatcher
import kotlinx.coroutines.test.advanceTimeBy
import kotlinx.coroutines.test.runCurrent
import kotlinx.coroutines.test.runTest
import kotlinx.coroutines.withContext
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertIs

@OptIn(ExperimentalCoroutinesApi::class)
class TemporalGameOfLifeStateMoleculeTests {

    private val testDispatcher = StandardTestDispatcher()

    private val dispatchers = TestComposeLifeDispatchers(
        generalTestDispatcher = testDispatcher,
        cellTickerTestDispatcher = testDispatcher,
    )

    @Test
    fun state_is_advanced_correctly() = runTest(testDispatcher + BroadcastFrameClock()) {
        val hashLifeAlgorithm = HashLifeAlgorithm(
            dispatchers = dispatchers,
        )

        moleculeFlow(RecompositionMode.ContextClock) {
            val temporalGameOfLifeState = TemporalGameOfLifeState(
                seedCellState = SixLongLinePattern.seedCellState,
                isRunning = true,
                generationsPerStep = 1,
                targetStepsPerSecond = 60.0,
            )

            val temporalGameOfLifeStateMutator = rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = hashLifeAlgorithm,
                clock = testDispatcher.scheduler.clock,
                dispatchers = dispatchers,
            )

            LaunchedEffect(temporalGameOfLifeStateMutator) {
                withContext(testDispatcher) {
                    temporalGameOfLifeStateMutator.update()
                }
            }
            temporalGameOfLifeState
        }
            .test {
                val temporalGameOfLifeState = awaitItem()

                assertEquals(SixLongLinePattern.seedCellState, temporalGameOfLifeState.cellState)
                assertEquals(
                    TemporalGameOfLifeState.EvolutionStatus.Running(
                        averageGenerationsPerSecond = 0.0,
                    ),
                    temporalGameOfLifeState.status,
                )

                SixLongLinePattern.cellStates.forEach { expectedCellState ->
                    advanceTimeBy(17)
                    runCurrent()

                    assertEquals(expectedCellState, temporalGameOfLifeState.cellState)
                    temporalGameOfLifeState.status.let { status ->
                        assertIs<TemporalGameOfLifeState.EvolutionStatus.Running>(status)
                        assertEquals(58.824, status.averageGenerationsPerSecond, 0.001)
                    }
                }
            }
    }

    @Test
    fun pausing_evolution_is_correct() = runTest(testDispatcher + BroadcastFrameClock()) {
        val hashLifeAlgorithm = HashLifeAlgorithm(
            dispatchers = dispatchers,
        )

        moleculeFlow(RecompositionMode.ContextClock) {
            val temporalGameOfLifeState = TemporalGameOfLifeState(
                seedCellState = SixLongLinePattern.seedCellState,
                isRunning = true,
                generationsPerStep = 1,
                targetStepsPerSecond = 60.0,
            )

            val temporalGameOfLifeStateMutator = rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = hashLifeAlgorithm,
                clock = testDispatcher.scheduler.clock,
                dispatchers = dispatchers,
            )

            LaunchedEffect(temporalGameOfLifeStateMutator) {
                withContext(testDispatcher) {
                    temporalGameOfLifeStateMutator.update()
                }
            }
            temporalGameOfLifeState
        }
            .test {
                val temporalGameOfLifeState = awaitItem()

                assertEquals(SixLongLinePattern.seedCellState, temporalGameOfLifeState.cellState)
                assertEquals(
                    TemporalGameOfLifeState.EvolutionStatus.Running(
                        averageGenerationsPerSecond = 0.0,
                    ),
                    temporalGameOfLifeState.status,
                )

                advanceTimeBy(8)
                runCurrent()

                assertEquals(SixLongLinePattern.seedCellState, temporalGameOfLifeState.cellState)
                temporalGameOfLifeState.status.let { status ->
                    assertIs<TemporalGameOfLifeState.EvolutionStatus.Running>(status)
                    assertEquals(0.0, status.averageGenerationsPerSecond, 0.001)
                }

                advanceTimeBy(9)
                runCurrent()

                assertEquals(SixLongLinePattern.cellStates[0], temporalGameOfLifeState.cellState)
                temporalGameOfLifeState.status.let { status ->
                    assertIs<TemporalGameOfLifeState.EvolutionStatus.Running>(status)
                    assertEquals(58.824, status.averageGenerationsPerSecond, 0.001)
                }

                advanceTimeBy(8)
                runCurrent()

                assertEquals(SixLongLinePattern.cellStates[0], temporalGameOfLifeState.cellState)
                temporalGameOfLifeState.status.let { status ->
                    assertIs<TemporalGameOfLifeState.EvolutionStatus.Running>(status)
                    assertEquals(58.824, status.averageGenerationsPerSecond, 0.001)
                }

                advanceTimeBy(9)
                runCurrent()

                assertEquals(SixLongLinePattern.cellStates[1], temporalGameOfLifeState.cellState)
                temporalGameOfLifeState.status.let { status ->
                    assertIs<TemporalGameOfLifeState.EvolutionStatus.Running>(status)
                    assertEquals(58.824, status.averageGenerationsPerSecond, 0.001)
                }

                temporalGameOfLifeState.setIsRunning(false)

                advanceTimeBy(1000)
                runCurrent()

                assertEquals(SixLongLinePattern.cellStates[1], temporalGameOfLifeState.cellState)
                assertIs<TemporalGameOfLifeState.EvolutionStatus.Paused>(temporalGameOfLifeState.status)
            }
    }

    @Test
    fun target_steps_evolution_is_correct() = runTest(testDispatcher + BroadcastFrameClock()) {
        val hashLifeAlgorithm = HashLifeAlgorithm(
            dispatchers = dispatchers,
        )

        moleculeFlow(RecompositionMode.ContextClock) {
            val temporalGameOfLifeState = TemporalGameOfLifeState(
                seedCellState = SixLongLinePattern.seedCellState,
                isRunning = true,
                generationsPerStep = 1,
                targetStepsPerSecond = 60.0,
            )

            val temporalGameOfLifeStateMutator = rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = hashLifeAlgorithm,
                clock = testDispatcher.scheduler.clock,
                dispatchers = dispatchers,
            )

            LaunchedEffect(temporalGameOfLifeStateMutator) {
                withContext(testDispatcher) {
                    temporalGameOfLifeStateMutator.update()
                }
            }
            temporalGameOfLifeState
        }
            .test {
                val temporalGameOfLifeState = awaitItem()

                assertEquals(SixLongLinePattern.seedCellState, temporalGameOfLifeState.cellState)
                assertEquals(
                    TemporalGameOfLifeState.EvolutionStatus.Running(
                        averageGenerationsPerSecond = 0.0,
                    ),
                    temporalGameOfLifeState.status,
                )

                advanceTimeBy(8)
                runCurrent()

                assertEquals(SixLongLinePattern.seedCellState, temporalGameOfLifeState.cellState)
                temporalGameOfLifeState.status.let { status ->
                    assertIs<TemporalGameOfLifeState.EvolutionStatus.Running>(status)
                    assertEquals(0.0, status.averageGenerationsPerSecond, 0.001)
                }

                advanceTimeBy(9)
                runCurrent()

                assertEquals(SixLongLinePattern.cellStates[0], temporalGameOfLifeState.cellState)
                temporalGameOfLifeState.status.let { status ->
                    assertIs<TemporalGameOfLifeState.EvolutionStatus.Running>(status)
                    assertEquals(58.824, status.averageGenerationsPerSecond, 0.001)
                }

                advanceTimeBy(8)
                runCurrent()

                assertEquals(SixLongLinePattern.cellStates[0], temporalGameOfLifeState.cellState)
                temporalGameOfLifeState.status.let { status ->
                    assertIs<TemporalGameOfLifeState.EvolutionStatus.Running>(status)
                    assertEquals(58.824, status.averageGenerationsPerSecond, 0.001)
                }

                advanceTimeBy(9)
                runCurrent()

                assertEquals(SixLongLinePattern.cellStates[1], temporalGameOfLifeState.cellState)
                temporalGameOfLifeState.status.let { status ->
                    assertIs<TemporalGameOfLifeState.EvolutionStatus.Running>(status)
                    assertEquals(58.824, status.averageGenerationsPerSecond, 0.001)
                }

                temporalGameOfLifeState.targetStepsPerSecond = 10.0

                advanceTimeBy(50)
                runCurrent()

                assertEquals(SixLongLinePattern.cellStates[1], temporalGameOfLifeState.cellState)
                temporalGameOfLifeState.status.let { status ->
                    assertIs<TemporalGameOfLifeState.EvolutionStatus.Running>(status)
                    assertEquals(58.824, status.averageGenerationsPerSecond, 0.001)
                }

                advanceTimeBy(50)
                runCurrent()

                assertEquals(SixLongLinePattern.cellStates[2], temporalGameOfLifeState.cellState)
                temporalGameOfLifeState.status.let { status ->
                    assertIs<TemporalGameOfLifeState.EvolutionStatus.Running>(status)
                    assertEquals(22.388, status.averageGenerationsPerSecond, 0.001)
                }
            }
    }

    @Test
    fun setting_evolution_is_correct() = runTest(testDispatcher + BroadcastFrameClock()) {
        val hashLifeAlgorithm = HashLifeAlgorithm(
            dispatchers = dispatchers,
        )

        moleculeFlow(RecompositionMode.ContextClock) {
            val temporalGameOfLifeState = TemporalGameOfLifeState(
                seedCellState = SixLongLinePattern.seedCellState,
                isRunning = true,
                generationsPerStep = 1,
                targetStepsPerSecond = 60.0,
            )

            val temporalGameOfLifeStateMutator = rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = hashLifeAlgorithm,
                clock = testDispatcher.scheduler.clock,
                dispatchers = dispatchers,
            )

            LaunchedEffect(temporalGameOfLifeStateMutator) {
                withContext(testDispatcher) {
                    temporalGameOfLifeStateMutator.update()
                }
            }
            temporalGameOfLifeState
        }
            .test {
                val temporalGameOfLifeState = awaitItem()

                assertEquals(SixLongLinePattern.seedCellState, temporalGameOfLifeState.cellState)
                assertEquals(
                    TemporalGameOfLifeState.EvolutionStatus.Running(
                        averageGenerationsPerSecond = 0.0,
                    ),
                    temporalGameOfLifeState.status,
                )

                advanceTimeBy(8)
                runCurrent()

                assertEquals(SixLongLinePattern.seedCellState, temporalGameOfLifeState.cellState)
                temporalGameOfLifeState.status.let { status ->
                    assertIs<TemporalGameOfLifeState.EvolutionStatus.Running>(status)
                    assertEquals(0.0, status.averageGenerationsPerSecond, 0.001)
                }

                advanceTimeBy(9)
                runCurrent()

                assertEquals(SixLongLinePattern.cellStates[0], temporalGameOfLifeState.cellState)
                temporalGameOfLifeState.status.let { status ->
                    assertIs<TemporalGameOfLifeState.EvolutionStatus.Running>(status)
                    assertEquals(58.824, status.averageGenerationsPerSecond, 0.001)
                }

                advanceTimeBy(8)
                runCurrent()

                assertEquals(SixLongLinePattern.cellStates[0], temporalGameOfLifeState.cellState)
                temporalGameOfLifeState.status.let { status ->
                    assertIs<TemporalGameOfLifeState.EvolutionStatus.Running>(status)
                    assertEquals(58.824, status.averageGenerationsPerSecond, 0.001)
                }

                advanceTimeBy(9)
                runCurrent()

                assertEquals(SixLongLinePattern.cellStates[1], temporalGameOfLifeState.cellState)
                temporalGameOfLifeState.status.let { status ->
                    assertIs<TemporalGameOfLifeState.EvolutionStatus.Running>(status)
                    assertEquals(58.824, status.averageGenerationsPerSecond, 0.001)
                }

                temporalGameOfLifeState.cellState = SingleCellPattern.seedCellState

                advanceTimeBy(8)
                runCurrent()

                assertEquals(SingleCellPattern.seedCellState, temporalGameOfLifeState.cellState)
                temporalGameOfLifeState.status.let { status ->
                    assertIs<TemporalGameOfLifeState.EvolutionStatus.Running>(status)
                    assertEquals(58.824, status.averageGenerationsPerSecond, 0.001)
                }

                advanceTimeBy(9)
                runCurrent()

                assertEquals(SingleCellPattern.cellStates[0], temporalGameOfLifeState.cellState)
                temporalGameOfLifeState.status.let { status ->
                    assertIs<TemporalGameOfLifeState.EvolutionStatus.Running>(status)
                    assertEquals(58.824, status.averageGenerationsPerSecond, 0.001)
                }
            }
    }

    @Test
    fun multiple_evolutions_is_correct() = runTest(testDispatcher + BroadcastFrameClock()) {
        val hashLifeAlgorithm = HashLifeAlgorithm(
            dispatchers = dispatchers,
        )

        var runFirstMutator by mutableStateOf(true)

        moleculeFlow(RecompositionMode.ContextClock) {
            val temporalGameOfLifeState = TemporalGameOfLifeState(
                seedCellState = SixLongLinePattern.seedCellState,
                isRunning = true,
                generationsPerStep = 1,
                targetStepsPerSecond = 60.0,
            )

            val temporalGameOfLifeStateMutator = rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = hashLifeAlgorithm,
                clock = testDispatcher.scheduler.clock,
                dispatchers = dispatchers,
            )

            if (runFirstMutator) {
                LaunchedEffect(temporalGameOfLifeStateMutator) {
                    withContext(testDispatcher) {
                        temporalGameOfLifeStateMutator.update()
                    }
                }
            }

            LaunchedEffect(temporalGameOfLifeStateMutator) {
                withContext(testDispatcher) {
                    temporalGameOfLifeStateMutator.update()
                }
            }
            temporalGameOfLifeState
        }
            .test {
                val temporalGameOfLifeState = awaitItem()

                assertEquals(SixLongLinePattern.seedCellState, temporalGameOfLifeState.cellState)
                assertEquals(
                    TemporalGameOfLifeState.EvolutionStatus.Running(
                        averageGenerationsPerSecond = 0.0,
                    ),
                    temporalGameOfLifeState.status,
                )

                advanceTimeBy(8)
                runCurrent()

                assertEquals(SixLongLinePattern.seedCellState, temporalGameOfLifeState.cellState)
                temporalGameOfLifeState.status.let { status ->
                    assertIs<TemporalGameOfLifeState.EvolutionStatus.Running>(status)
                    assertEquals(0.0, status.averageGenerationsPerSecond, 0.001)
                }

                advanceTimeBy(9)
                runCurrent()

                assertEquals(SixLongLinePattern.cellStates[0], temporalGameOfLifeState.cellState)
                temporalGameOfLifeState.status.let { status ->
                    assertIs<TemporalGameOfLifeState.EvolutionStatus.Running>(status)
                    assertEquals(58.824, status.averageGenerationsPerSecond, 0.001)
                }

                advanceTimeBy(8)
                runCurrent()

                assertEquals(SixLongLinePattern.cellStates[0], temporalGameOfLifeState.cellState)
                temporalGameOfLifeState.status.let { status ->
                    assertIs<TemporalGameOfLifeState.EvolutionStatus.Running>(status)
                    assertEquals(58.824, status.averageGenerationsPerSecond, 0.001)
                }

                advanceTimeBy(9)
                runCurrent()

                assertEquals(SixLongLinePattern.cellStates[1], temporalGameOfLifeState.cellState)
                temporalGameOfLifeState.status.let { status ->
                    assertIs<TemporalGameOfLifeState.EvolutionStatus.Running>(status)
                    assertEquals(58.824, status.averageGenerationsPerSecond, 0.001)
                }

                runFirstMutator = false

                advanceTimeBy(8)
                runCurrent()

                assertEquals(SixLongLinePattern.cellStates[1], temporalGameOfLifeState.cellState)
                temporalGameOfLifeState.status.let { status ->
                    assertIs<TemporalGameOfLifeState.EvolutionStatus.Running>(status)
                    assertEquals(58.824, status.averageGenerationsPerSecond, 0.001)
                }

                advanceTimeBy(9)
                runCurrent()

                assertEquals(SixLongLinePattern.cellStates[2], temporalGameOfLifeState.cellState)
                temporalGameOfLifeState.status.let { status ->
                    assertIs<TemporalGameOfLifeState.EvolutionStatus.Running>(status)
                    assertEquals(58.824, status.averageGenerationsPerSecond, 0.001)
                }
            }
    }

    @Test
    fun state_is_advanced_correctly_with_step() = runTest(testDispatcher + BroadcastFrameClock()) {
        val hashLifeAlgorithm = HashLifeAlgorithm(
            dispatchers = dispatchers,
        )

        moleculeFlow(RecompositionMode.ContextClock) {
            val temporalGameOfLifeState = TemporalGameOfLifeState(
                seedCellState = SixLongLinePattern.seedCellState,
                isRunning = false,
                generationsPerStep = 1,
                targetStepsPerSecond = 60.0,
            )

            val temporalGameOfLifeStateMutator = rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = hashLifeAlgorithm,
                clock = testDispatcher.scheduler.clock,
                dispatchers = dispatchers,
            )

            LaunchedEffect(temporalGameOfLifeStateMutator) {
                withContext(testDispatcher) {
                    temporalGameOfLifeStateMutator.update()
                }
            }
            temporalGameOfLifeState
        }
            .test {
                val temporalGameOfLifeState = awaitItem()

                assertEquals(SixLongLinePattern.seedCellState, temporalGameOfLifeState.cellState)
                assertEquals(
                    TemporalGameOfLifeState.EvolutionStatus.Paused,
                    temporalGameOfLifeState.status,
                )

                SixLongLinePattern.cellStates.forEach { expectedCellState ->
                    temporalGameOfLifeState.step()
                    runCurrent()

                    assertEquals(expectedCellState, temporalGameOfLifeState.cellState)
                    assertEquals(TemporalGameOfLifeState.EvolutionStatus.Paused, temporalGameOfLifeState.status)
                }
            }
    }
}
