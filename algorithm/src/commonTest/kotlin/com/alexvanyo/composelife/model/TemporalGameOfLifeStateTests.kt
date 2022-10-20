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

import androidx.compose.runtime.snapshotFlow
import androidx.compose.runtime.snapshots.Snapshot
import app.cash.turbine.test
import com.alexvanyo.composelife.algorithm.NaiveGameOfLifeAlgorithm
import com.alexvanyo.composelife.dispatchers.TestComposeLifeDispatchers
import com.alexvanyo.composelife.dispatchers.schedulerClock
import com.alexvanyo.composelife.patterns.SingleCellPattern
import com.alexvanyo.composelife.patterns.SixLongLinePattern
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.launch
import kotlinx.coroutines.test.StandardTestDispatcher
import kotlinx.coroutines.test.TestCoroutineScheduler
import kotlinx.coroutines.test.advanceTimeBy
import kotlinx.coroutines.test.resetMain
import kotlinx.coroutines.test.runCurrent
import kotlinx.coroutines.test.runTest
import kotlinx.coroutines.test.setMain
import kotlin.test.AfterTest
import kotlin.test.BeforeTest
import kotlin.test.Test
import kotlin.test.assertEquals

@OptIn(ExperimentalCoroutinesApi::class)
class TemporalGameOfLifeStateTests {

    private val scheduler = TestCoroutineScheduler()
    private val testDispatcher = StandardTestDispatcher(scheduler)
    private val dispatchers = TestComposeLifeDispatchers(testDispatcher)

    @BeforeTest
    fun setup() {
        Dispatchers.setMain(testDispatcher)
    }

    @AfterTest
    fun teardown() {
        Dispatchers.resetMain()
    }

    @Test
    fun initial_values_are_correct_when_not_running() {
        val gameOfLifeState = TemporalGameOfLifeState(
            isRunning = false,
        )

        assertEquals(emptyCellState(), gameOfLifeState.cellState)
        assertEquals(1, gameOfLifeState.generationsPerStep)
        assertEquals(60.0, gameOfLifeState.targetStepsPerSecond)
        assertEquals(TemporalGameOfLifeState.EvolutionStatus.Paused, gameOfLifeState.status)
    }

    @Test
    fun initial_values_are_correct_when_running() {
        val gameOfLifeState = TemporalGameOfLifeState(
            seedCellState = SixLongLinePattern.seedCellState,
            isRunning = true,
        )

        assertEquals(SixLongLinePattern.seedCellState, gameOfLifeState.cellState)
        assertEquals(1, gameOfLifeState.generationsPerStep)
        assertEquals(60.0, gameOfLifeState.targetStepsPerSecond)
        assertEquals(
            TemporalGameOfLifeState.EvolutionStatus.Running(
                averageGenerationsPerSecond = 0.0,
            ),
            gameOfLifeState.status,
        )
    }

    @Test
    fun simple_evolution_is_correct() = runTest(testDispatcher) {
        val gameOfLifeState = TemporalGameOfLifeState(
            seedCellState = SixLongLinePattern.seedCellState,
            isRunning = true,
        )

        snapshotFlow {
            gameOfLifeState.cellState
        }
            .test {
                val mutatorJob = launch {
                    with(NaiveGameOfLifeAlgorithm(dispatchers)) {
                        with(dispatchers) {
                            with(schedulerClock) {
                                gameOfLifeState.evolve()
                            }
                        }
                    }
                }

                runCurrent()
                Snapshot.sendApplyNotifications()
                assertEquals(SixLongLinePattern.seedCellState, awaitItem())

                SixLongLinePattern.cellStates.dropLastWhile { it == emptyCellState() }.forEach { cellState ->
                    advanceTimeBy(8)
                    runCurrent()
                    Snapshot.sendApplyNotifications()
                    runCurrent()
                    expectNoEvents()

                    advanceTimeBy(8)
                    runCurrent()
                    Snapshot.sendApplyNotifications()
                    runCurrent()
                    assertEquals(cellState, awaitItem())
                }

                mutatorJob.cancel()
            }
    }

    @Test
    fun pausing_evolution_is_correct() = runTest(testDispatcher) {
        val gameOfLifeState = TemporalGameOfLifeState(
            seedCellState = SixLongLinePattern.seedCellState,
            isRunning = true,
        )

        snapshotFlow {
            gameOfLifeState.cellState
        }
            .test {
                val mutatorJob = launch {
                    with(NaiveGameOfLifeAlgorithm(dispatchers)) {
                        with(dispatchers) {
                            with(schedulerClock) {
                                gameOfLifeState.evolve()
                            }
                        }
                    }
                }

                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                assertEquals(SixLongLinePattern.seedCellState, awaitItem())

                advanceTimeBy(8)
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                advanceTimeBy(8)
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                assertEquals(SixLongLinePattern.cellStates[0], awaitItem())

                advanceTimeBy(8)
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                gameOfLifeState.setIsRunning(false)
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                advanceTimeBy(8)
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                advanceTimeBy(1000)
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                gameOfLifeState.setIsRunning(true)
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                advanceTimeBy(8)
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                advanceTimeBy(8)
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                assertEquals(SixLongLinePattern.cellStates[1], awaitItem())

                mutatorJob.cancel()
                cancel()
            }
    }

    @Test
    fun stepping_evolution_is_correct() = runTest(testDispatcher) {
        val gameOfLifeState = TemporalGameOfLifeState(
            seedCellState = SixLongLinePattern.seedCellState,
            isRunning = true,
        )

        snapshotFlow {
            gameOfLifeState.cellState
        }
            .test {
                val mutatorJob = launch {
                    with(NaiveGameOfLifeAlgorithm(dispatchers)) {
                        with(dispatchers) {
                            with(schedulerClock) {
                                gameOfLifeState.evolve()
                            }
                        }
                    }
                }

                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                assertEquals(SixLongLinePattern.seedCellState, awaitItem())

                advanceTimeBy(8)
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                advanceTimeBy(8)
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                assertEquals(SixLongLinePattern.cellStates[0], awaitItem())

                advanceTimeBy(8)
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                gameOfLifeState.generationsPerStep = 2
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                advanceTimeBy(8)
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                advanceTimeBy(8)
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                assertEquals(SixLongLinePattern.cellStates[2], awaitItem())

                advanceTimeBy(8)
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                gameOfLifeState.generationsPerStep = 4
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                advanceTimeBy(8)
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                advanceTimeBy(8)
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                assertEquals(SixLongLinePattern.cellStates[6], awaitItem())

                mutatorJob.cancel()
            }
    }

    @Test
    fun target_steps_evolution_is_correct() = runTest(testDispatcher) {
        val gameOfLifeState = TemporalGameOfLifeState(
            seedCellState = SixLongLinePattern.seedCellState,
            isRunning = true,
        )

        snapshotFlow {
            gameOfLifeState.cellState
        }
            .test {
                val mutatorJob = launch {
                    with(NaiveGameOfLifeAlgorithm(dispatchers)) {
                        with(dispatchers) {
                            with(schedulerClock) {
                                gameOfLifeState.evolve()
                            }
                        }
                    }
                }

                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                assertEquals(SixLongLinePattern.seedCellState, awaitItem())

                advanceTimeBy(8)
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                advanceTimeBy(8)
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                assertEquals(SixLongLinePattern.cellStates[0], awaitItem())

                advanceTimeBy(8)
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                gameOfLifeState.targetStepsPerSecond = 10.0
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                advanceTimeBy(50)
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                advanceTimeBy(50)
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                assertEquals(SixLongLinePattern.cellStates[1], awaitItem())

                advanceTimeBy(50)
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                gameOfLifeState.targetStepsPerSecond = 1.0
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                advanceTimeBy(500)
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                advanceTimeBy(500)
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                assertEquals(SixLongLinePattern.cellStates[2], awaitItem())

                mutatorJob.cancel()
            }
    }

    @Test
    fun setting_evolution_is_correct() = runTest(testDispatcher) {
        val gameOfLifeState = TemporalGameOfLifeState(
            seedCellState = SixLongLinePattern.seedCellState,
            isRunning = true,
        )

        snapshotFlow {
            gameOfLifeState.cellState
        }
            .test {
                val mutatorJob = launch {
                    with(NaiveGameOfLifeAlgorithm(dispatchers)) {
                        with(dispatchers) {
                            with(schedulerClock) {
                                gameOfLifeState.evolve()
                            }
                        }
                    }
                }

                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                assertEquals(SixLongLinePattern.seedCellState, awaitItem())

                advanceTimeBy(8)
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                advanceTimeBy(8)
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                assertEquals(SixLongLinePattern.cellStates[0], awaitItem())

                advanceTimeBy(8)
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                gameOfLifeState.cellState = SingleCellPattern.seedCellState
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                assertEquals(SingleCellPattern.seedCellState, awaitItem())

                advanceTimeBy(8)
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                advanceTimeBy(8)
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                assertEquals(SingleCellPattern.cellStates[0], awaitItem())

                mutatorJob.cancel()
            }
    }

    @Test
    fun multiple_evolutions_are_correct() = runTest(testDispatcher) {
        val gameOfLifeState = TemporalGameOfLifeState(
            seedCellState = SixLongLinePattern.seedCellState,
            isRunning = true,
        )

        snapshotFlow {
            gameOfLifeState.cellState
        }
            .test {
                val mutatorJob1 = launch {
                    with(NaiveGameOfLifeAlgorithm(dispatchers)) {
                        with(dispatchers) {
                            with(schedulerClock) {
                                gameOfLifeState.evolve()
                            }
                        }
                    }
                }

                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                assertEquals(SixLongLinePattern.seedCellState, awaitItem())

                advanceTimeBy(8)
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                advanceTimeBy(8)
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                assertEquals(SixLongLinePattern.cellStates[0], awaitItem())

                val mutatorJob2 = launch(testDispatcher) {
                    with(NaiveGameOfLifeAlgorithm(dispatchers)) {
                        with(dispatchers) {
                            with(schedulerClock) {
                                gameOfLifeState.evolve()
                            }
                        }
                    }
                }

                advanceTimeBy(8)
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                advanceTimeBy(8)
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                assertEquals(SixLongLinePattern.cellStates[1], awaitItem())

                advanceTimeBy(8)
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                advanceTimeBy(8)
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                assertEquals(SixLongLinePattern.cellStates[2], awaitItem())

                advanceTimeBy(8)
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                mutatorJob1.cancel()

                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                advanceTimeBy(8)
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                advanceTimeBy(8)
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                assertEquals(SixLongLinePattern.cellStates[3], awaitItem())

                advanceTimeBy(8)
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                advanceTimeBy(8)
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                assertEquals(SixLongLinePattern.cellStates[4], awaitItem())

                mutatorJob2.cancel()
            }
    }
}
