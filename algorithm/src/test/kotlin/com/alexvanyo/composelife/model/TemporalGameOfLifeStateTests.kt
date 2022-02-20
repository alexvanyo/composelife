package com.alexvanyo.composelife.model

import androidx.compose.runtime.snapshotFlow
import androidx.compose.runtime.snapshots.Snapshot
import app.cash.turbine.test
import com.alexvanyo.composelife.algorithm.NaiveGameOfLifeAlgorithm
import com.alexvanyo.composelife.dispatchers.TestComposeLifeDispatchers
import com.alexvanyo.composelife.dispatchers.schedulerClock
import com.alexvanyo.composelife.patterns.SingleCellPattern
import com.alexvanyo.composelife.patterns.SixLongLinePattern
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.launch
import kotlinx.coroutines.test.StandardTestDispatcher
import kotlinx.coroutines.test.advanceTimeBy
import kotlinx.coroutines.test.runCurrent
import kotlinx.coroutines.test.runTest
import org.junit.jupiter.api.Test
import kotlin.test.assertEquals

@OptIn(ExperimentalCoroutinesApi::class)
class TemporalGameOfLifeStateTests {

    @Test
    fun `initial values are correct when not running`() {
        val gameOfLifeState = TemporalGameOfLifeState(
            isRunning = false
        )

        assertEquals(emptyCellState(), gameOfLifeState.cellState)
        assertEquals(1, gameOfLifeState.generationsPerStep)
        assertEquals(60.0, gameOfLifeState.targetStepsPerSecond)
        assertEquals(TemporalGameOfLifeState.EvolutionStatus.Paused, gameOfLifeState.status)
    }

    @Test
    fun `initial values are correct when running`() {
        val gameOfLifeState = TemporalGameOfLifeState(
            cellState = SixLongLinePattern.seedCellState,
            isRunning = true
        )

        assertEquals(SixLongLinePattern.seedCellState, gameOfLifeState.cellState)
        assertEquals(1, gameOfLifeState.generationsPerStep)
        assertEquals(60.0, gameOfLifeState.targetStepsPerSecond)
        assertEquals(
            TemporalGameOfLifeState.EvolutionStatus.Running(
                averageGenerationsPerSecond = 0.0
            ),
            gameOfLifeState.status
        )
    }

    @Test
    fun `simple evolution is correct`() = runTest {
        val gameOfLifeState = TemporalGameOfLifeState(
            cellState = SixLongLinePattern.seedCellState,
            isRunning = true
        )

        snapshotFlow {
            gameOfLifeState.cellState
        }
            .test {
                val mutatorJob = launch {
                    val dispatchers = TestComposeLifeDispatchers(StandardTestDispatcher(testScheduler))
                    TemporalGameOfLifeStateMutator(
                        coroutineScope = this,
                        gameOfLifeAlgorithm = NaiveGameOfLifeAlgorithm(dispatchers),
                        clock = schedulerClock,
                        dispatchers = dispatchers,
                        temporalGameOfLifeState = gameOfLifeState
                    )
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
    fun `pausing evolution is correct`() = runTest {
        val gameOfLifeState = TemporalGameOfLifeState(
            cellState = SixLongLinePattern.seedCellState,
            isRunning = true
        )

        snapshotFlow {
            gameOfLifeState.cellState
        }
            .test {
                val mutatorJob = launch {
                    val dispatchers = TestComposeLifeDispatchers(StandardTestDispatcher(testScheduler))
                    TemporalGameOfLifeStateMutator(
                        coroutineScope = this,
                        gameOfLifeAlgorithm = NaiveGameOfLifeAlgorithm(dispatchers),
                        clock = schedulerClock,
                        dispatchers = dispatchers,
                        temporalGameOfLifeState = gameOfLifeState
                    )
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
    fun `stepping evolution is correct`() = runTest {
        val gameOfLifeState = TemporalGameOfLifeState(
            cellState = SixLongLinePattern.seedCellState,
            isRunning = true
        )

        snapshotFlow {
            gameOfLifeState.cellState
        }
            .test {
                val mutatorJob = launch {
                    val dispatchers = TestComposeLifeDispatchers(StandardTestDispatcher(testScheduler))
                    TemporalGameOfLifeStateMutator(
                        coroutineScope = this,
                        gameOfLifeAlgorithm = NaiveGameOfLifeAlgorithm(dispatchers),
                        clock = schedulerClock,
                        dispatchers = dispatchers,
                        temporalGameOfLifeState = gameOfLifeState
                    )
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
    fun `target steps evolution is correct`() = runTest {
        val gameOfLifeState = TemporalGameOfLifeState(
            cellState = SixLongLinePattern.seedCellState,
            isRunning = true
        )

        snapshotFlow {
            gameOfLifeState.cellState
        }
            .test {
                val mutatorJob = launch {
                    val dispatchers = TestComposeLifeDispatchers(StandardTestDispatcher(testScheduler))
                    TemporalGameOfLifeStateMutator(
                        coroutineScope = this,
                        gameOfLifeAlgorithm = NaiveGameOfLifeAlgorithm(dispatchers),
                        clock = schedulerClock,
                        dispatchers = dispatchers,
                        temporalGameOfLifeState = gameOfLifeState
                    )
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
    fun `setting evolution is correct`() = runTest {
        val gameOfLifeState = TemporalGameOfLifeState(
            cellState = SixLongLinePattern.seedCellState,
            isRunning = true
        )

        snapshotFlow {
            gameOfLifeState.cellState
        }
            .test {
                val mutatorJob = launch {
                    val dispatchers = TestComposeLifeDispatchers(StandardTestDispatcher(testScheduler))
                    TemporalGameOfLifeStateMutator(
                        coroutineScope = this,
                        gameOfLifeAlgorithm = NaiveGameOfLifeAlgorithm(dispatchers),
                        clock = schedulerClock,
                        dispatchers = dispatchers,
                        temporalGameOfLifeState = gameOfLifeState
                    )
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
    fun `multiple evolutions are correct`() = runTest {
        val gameOfLifeState = TemporalGameOfLifeState(
            cellState = SixLongLinePattern.seedCellState,
            isRunning = true
        )

        snapshotFlow {
            gameOfLifeState.cellState
        }
            .test {
                val mutatorJob1 = launch {
                    val dispatchers = TestComposeLifeDispatchers(StandardTestDispatcher(testScheduler))
                    TemporalGameOfLifeStateMutator(
                        coroutineScope = this,
                        gameOfLifeAlgorithm = NaiveGameOfLifeAlgorithm(dispatchers),
                        clock = schedulerClock,
                        dispatchers = dispatchers,
                        temporalGameOfLifeState = gameOfLifeState
                    )
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

                val mutatorJob2 = launch {
                    val dispatchers = TestComposeLifeDispatchers(StandardTestDispatcher(testScheduler))
                    TemporalGameOfLifeStateMutator(
                        coroutineScope = this,
                        gameOfLifeAlgorithm = NaiveGameOfLifeAlgorithm(dispatchers),
                        clock = schedulerClock,
                        dispatchers = dispatchers,
                        temporalGameOfLifeState = gameOfLifeState
                    )
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
