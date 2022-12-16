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
import kotlinx.coroutines.channels.Channel
import kotlinx.coroutines.flow.Flow
import kotlinx.coroutines.flow.buffer
import kotlinx.coroutines.flow.channelFlow
import kotlinx.coroutines.flow.emptyFlow
import kotlinx.coroutines.flow.flatMapLatest
import kotlinx.coroutines.isActive
import kotlinx.coroutines.launch
import kotlinx.coroutines.test.StandardTestDispatcher
import kotlinx.coroutines.test.TestCoroutineScheduler
import kotlinx.coroutines.test.advanceTimeBy
import kotlinx.coroutines.test.resetMain
import kotlinx.coroutines.test.runCurrent
import kotlinx.coroutines.test.runTest
import kotlinx.coroutines.test.setMain
import kotlinx.datetime.Clock
import kotlin.test.AfterTest
import kotlin.test.BeforeTest
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.time.Duration.Companion.seconds

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
            targetStepsPerSecond = 100.0,
        )
        val testTimeTickerFactory = TestTimeTickerFactory(schedulerClock)

        snapshotFlow {
            gameOfLifeState.cellState
        }
            .test {
                val mutatorJob = launch {
                    with(NaiveGameOfLifeAlgorithm(dispatchers)) {
                        with(dispatchers) {
                            with(schedulerClock) {
                                with(testTimeTickerFactory) {
                                    gameOfLifeState.evolve()
                                }
                            }
                        }
                    }
                }

                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                assertEquals(SixLongLinePattern.seedCellState, awaitItem())

                SixLongLinePattern.cellStates.dropLastWhile { it == emptyCellState() }.forEach { cellState ->
                    advanceTimeBy(5)
                    testTimeTickerFactory.updateTime()
                    runCurrent()
                    Snapshot.sendApplyNotifications()
                    runCurrent()
                    println("checking at ${schedulerClock.now()}")
                    expectNoEvents()

                    advanceTimeBy(5)
                    testTimeTickerFactory.updateTime()
                    runCurrent()
                    Snapshot.sendApplyNotifications()
                    runCurrent()
                    println("checking at ${schedulerClock.now()}")
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
            targetStepsPerSecond = 100.0,
        )
        val testTimeTickerFactory = TestTimeTickerFactory(schedulerClock)

        snapshotFlow {
            gameOfLifeState.cellState
        }
            .test {
                val mutatorJob = launch {
                    with(NaiveGameOfLifeAlgorithm(dispatchers)) {
                        with(dispatchers) {
                            with(schedulerClock) {
                                with(testTimeTickerFactory) {
                                    gameOfLifeState.evolve()
                                }
                            }
                        }
                    }
                }

                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                assertEquals(SixLongLinePattern.seedCellState, awaitItem())

                advanceTimeBy(5)
                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                advanceTimeBy(5)
                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                assertEquals(SixLongLinePattern.cellStates[0], awaitItem())

                advanceTimeBy(5)
                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                gameOfLifeState.setIsRunning(false)

                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                advanceTimeBy(5)
                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                advanceTimeBy(1000)
                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                gameOfLifeState.setIsRunning(true)

                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                advanceTimeBy(5)
                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                advanceTimeBy(5)
                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                assertEquals(SixLongLinePattern.cellStates[1], awaitItem())

                mutatorJob.cancel()
            }
    }

    @Test
    fun stepping_evolution_is_correct() = runTest(testDispatcher) {
        val gameOfLifeState = TemporalGameOfLifeState(
            seedCellState = SixLongLinePattern.seedCellState,
            isRunning = true,
            targetStepsPerSecond = 100.0,
        )
        val testTimeTickerFactory = TestTimeTickerFactory(schedulerClock)

        snapshotFlow {
            gameOfLifeState.cellState
        }
            .test {
                val mutatorJob = launch {
                    with(NaiveGameOfLifeAlgorithm(dispatchers)) {
                        with(dispatchers) {
                            with(schedulerClock) {
                                with(testTimeTickerFactory) {
                                    gameOfLifeState.evolve()
                                }
                            }
                        }
                    }
                }

                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                assertEquals(SixLongLinePattern.seedCellState, awaitItem())

                advanceTimeBy(5)
                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                advanceTimeBy(5)
                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                assertEquals(SixLongLinePattern.cellStates[0], awaitItem())

                advanceTimeBy(5)
                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                gameOfLifeState.generationsPerStep = 2

                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                advanceTimeBy(5)
                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                advanceTimeBy(5)
                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                assertEquals(SixLongLinePattern.cellStates[2], awaitItem())

                advanceTimeBy(5)
                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                gameOfLifeState.generationsPerStep = 4
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                advanceTimeBy(5)
                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                advanceTimeBy(5)
                testTimeTickerFactory.updateTime()
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
            targetStepsPerSecond = 100.0,
        )
        val testTimeTickerFactory = TestTimeTickerFactory(schedulerClock)

        snapshotFlow {
            gameOfLifeState.cellState
        }
            .test {
                val mutatorJob = launch {
                    with(NaiveGameOfLifeAlgorithm(dispatchers)) {
                        with(dispatchers) {
                            with(schedulerClock) {
                                with(testTimeTickerFactory) {
                                    gameOfLifeState.evolve()
                                }
                            }
                        }
                    }
                }

                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                assertEquals(SixLongLinePattern.seedCellState, awaitItem())

                advanceTimeBy(5)
                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                println("checking at ${schedulerClock.now()}")
                expectNoEvents()

                advanceTimeBy(5)
                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                println("checking at ${schedulerClock.now()}")
                assertEquals(SixLongLinePattern.cellStates[0], awaitItem())

                advanceTimeBy(5)
                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                println("checking at ${schedulerClock.now()}")
                expectNoEvents()

                gameOfLifeState.targetStepsPerSecond = 10.0

                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                println("checking at ${schedulerClock.now()}")
                expectNoEvents()

                advanceTimeBy(50)
                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                println("checking at ${schedulerClock.now()}")
                expectNoEvents()

                advanceTimeBy(50)
                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                println("checking at ${schedulerClock.now()}")
                assertEquals(SixLongLinePattern.cellStates[1], awaitItem())

                advanceTimeBy(50)
                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                println("checking at ${schedulerClock.now()}")
                expectNoEvents()

                gameOfLifeState.targetStepsPerSecond = 1.0
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                println("checking at ${schedulerClock.now()}")
                expectNoEvents()

                advanceTimeBy(500)
                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                println("checking at ${schedulerClock.now()}")
                expectNoEvents()

                advanceTimeBy(500)
                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                println("checking at ${schedulerClock.now()}")
                assertEquals(SixLongLinePattern.cellStates[2], awaitItem())

                mutatorJob.cancel()
            }
    }

    @Test
    fun setting_evolution_is_correct() = runTest(testDispatcher) {
        val gameOfLifeState = TemporalGameOfLifeState(
            seedCellState = SixLongLinePattern.seedCellState,
            isRunning = true,
            targetStepsPerSecond = 100.0,
        )
        val testTimeTickerFactory = TestTimeTickerFactory(schedulerClock)

        snapshotFlow {
            gameOfLifeState.cellState
        }
            .test {
                val mutatorJob = launch {
                    with(NaiveGameOfLifeAlgorithm(dispatchers)) {
                        with(dispatchers) {
                            with(schedulerClock) {
                                with(testTimeTickerFactory) {
                                    gameOfLifeState.evolve()
                                }
                            }
                        }
                    }
                }

                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                println("checking at ${schedulerClock.now()}")
                assertEquals(SixLongLinePattern.seedCellState, awaitItem())

                advanceTimeBy(5)
                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                println("checking at ${schedulerClock.now()}")
                expectNoEvents()

                advanceTimeBy(5)
                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                println("checking at ${schedulerClock.now()}")
                assertEquals(SixLongLinePattern.cellStates[0], awaitItem())

                advanceTimeBy(5)
                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                println("checking at ${schedulerClock.now()}")
                expectNoEvents()

                gameOfLifeState.cellState = SingleCellPattern.seedCellState

                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                println("checking at ${schedulerClock.now()}")
                assertEquals(SingleCellPattern.seedCellState, awaitItem())

                advanceTimeBy(5)
                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                println("checking at ${schedulerClock.now()}")
                expectNoEvents()

                advanceTimeBy(5)
                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                println("checking at ${schedulerClock.now()}")
                assertEquals(SingleCellPattern.cellStates[0], awaitItem())

                mutatorJob.cancel()
            }
    }

    @Test
    fun multiple_evolutions_are_correct() = runTest(testDispatcher) {
        val gameOfLifeState = TemporalGameOfLifeState(
            seedCellState = SixLongLinePattern.seedCellState,
            isRunning = true,
            targetStepsPerSecond = 100.0,
        )
        val testTimeTickerFactory = TestTimeTickerFactory(schedulerClock)

        snapshotFlow {
            gameOfLifeState.cellState
        }
            .test {
                val mutatorJob1 = launch {
                    with(NaiveGameOfLifeAlgorithm(dispatchers)) {
                        with(dispatchers) {
                            with(schedulerClock) {
                                with(testTimeTickerFactory) {
                                    gameOfLifeState.evolve()
                                }
                            }
                        }
                    }
                }

                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                assertEquals(SixLongLinePattern.seedCellState, awaitItem())

                advanceTimeBy(5)
                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                advanceTimeBy(5)
                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                assertEquals(SixLongLinePattern.cellStates[0], awaitItem())

                val mutatorJob2 = launch(testDispatcher) {
                    with(NaiveGameOfLifeAlgorithm(dispatchers)) {
                        with(dispatchers) {
                            with(schedulerClock) {
                                with(testTimeTickerFactory) {
                                    gameOfLifeState.evolve()
                                }
                            }
                        }
                    }
                }

                advanceTimeBy(5)
                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                advanceTimeBy(5)
                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                assertEquals(SixLongLinePattern.cellStates[1], awaitItem())

                advanceTimeBy(5)
                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                advanceTimeBy(5)
                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                assertEquals(SixLongLinePattern.cellStates[2], awaitItem())

                advanceTimeBy(5)
                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                mutatorJob1.cancel()

                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                advanceTimeBy(5)
                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                advanceTimeBy(5)
                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                assertEquals(SixLongLinePattern.cellStates[3], awaitItem())

                advanceTimeBy(5)
                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                expectNoEvents()

                advanceTimeBy(5)
                testTimeTickerFactory.updateTime()
                runCurrent()
                Snapshot.sendApplyNotifications()
                runCurrent()
                assertEquals(SixLongLinePattern.cellStates[4], awaitItem())

                mutatorJob2.cancel()
            }
    }
}

class TestTimeTickerFactory(
    private val clock: Clock,
) : TimeTickerFactory {
    private val tickChannel = Channel<Unit>(capacity = Channel.CONFLATED)

    suspend fun updateTime() {
        tickChannel.send(Unit)
    }

    @OptIn(ExperimentalCoroutinesApi::class)
    override fun timeTicker(configFlow: Flow<TimeTickerConfig>): Flow<Unit> =
        configFlow
            .flatMapLatest { (isRunning, targetStepsPerSecond) ->
                if (isRunning) {
                    channelFlow {
                        while (isActive) {
                            val targetDelay = 1.seconds / targetStepsPerSecond
                            val targetTime = clock.now() + targetDelay
                            while (clock.now() < targetTime) {
                                tickChannel.receive()
                            }
                            send(Unit)
                        }
                    }
                        .buffer(0) // No buffer, so the ticks are only consumed upon a cell state being computed
                } else {
                    emptyFlow()
                }
            }
            .buffer(0) // No buffer, so the ticks are only consumed upon a cell state being computed
}
