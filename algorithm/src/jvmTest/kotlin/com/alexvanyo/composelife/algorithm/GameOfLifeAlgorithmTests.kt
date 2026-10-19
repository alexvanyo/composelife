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

package com.alexvanyo.composelife.algorithm

import androidx.compose.ui.unit.IntOffset
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.dispatchers.TestComposeLifeDispatchers
import com.alexvanyo.composelife.model.CellState
import com.alexvanyo.composelife.model.assertCellStateEquals
import com.alexvanyo.composelife.model.toHashLifeCellState
import com.alexvanyo.composelife.patterns.BlomPattern
import com.alexvanyo.composelife.patterns.GameOfLifeTestPattern
import com.alexvanyo.composelife.patterns.Pattern52448M
import com.alexvanyo.composelife.patterns.RPentominoPattern
import com.alexvanyo.composelife.patterns.values
import com.alexvanyo.composelife.preferences.AlgorithmType
import com.alexvanyo.composelife.preferences.TestComposeLifePreferences
import com.alexvanyo.composelife.preferences.setAlgorithmChoice
import com.alexvanyo.composelife.tracing.TestTraceDriver
import de.infix.testBalloon.framework.core.Test.ExecutionScope
import de.infix.testBalloon.framework.core.TestBalloonExperimentalApi
import de.infix.testBalloon.framework.core.TestConfig
import de.infix.testBalloon.framework.core.testScope
import de.infix.testBalloon.framework.core.testSuite
import kotlinx.coroutines.CoroutineDispatcher
import kotlinx.coroutines.Job
import kotlinx.coroutines.currentCoroutineContext
import kotlinx.coroutines.delay
import kotlinx.coroutines.flow.collectIndexed
import kotlinx.coroutines.flow.onEach
import kotlinx.coroutines.flow.take
import kotlinx.coroutines.launch
import kotlin.coroutines.ContinuationInterceptor
import kotlin.random.Random
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith
import kotlin.time.Duration
import kotlin.time.Duration.Companion.milliseconds

private class GameOfLifeAlgorithmFactory(
    val algorithmName: String,
    val factory: ExecutionScope.(ComposeLifeDispatchers) -> Pair<GameOfLifeAlgorithm, Job>,
) {
    override fun toString(): String = algorithmName
}

private class CellStateMapper(val name: String, val mapper: (CellState) -> CellState) {
    override fun toString(): String = name
}

@OptIn(TestBalloonExperimentalApi::class)
val GameOfLifeAlgorithmTests by testSuite(
    testConfig = TestConfig.testScope(true, Duration.INFINITE),
) {

    val algorithmFactories =
        listOf(
            GameOfLifeAlgorithmFactory("Naive Algorithm") {
                NaiveGameOfLifeAlgorithm(it) to Job().apply { complete() }
            },
            GameOfLifeAlgorithmFactory("HashLife Algorithm") {
                HashLifeAlgorithm(
                    dispatchers = it,
                    tracer = TestTraceDriver().tracer,
                ) to Job().apply { complete() }
            },
            GameOfLifeAlgorithmFactory("Lean HashLife Algorithm") {
                LeanHashLifeAlgorithm(
                    dispatchers = it,
                    tracer = TestTraceDriver().tracer,
                ) to Job().apply { complete() }
            },
            GameOfLifeAlgorithmFactory("Flat Lean HashLife Algorithm") {
                FlatLeanHashLifeAlgorithm(
                    dispatchers = it,
                    tracer = TestTraceDriver().tracer,
                ) to Job().apply { complete() }
            },
            GameOfLifeAlgorithmFactory("Flat Lean HashLife Algorithm (Tiny Arena)") {
                FlatLeanHashLifeAlgorithm(
                    dispatchers = it,
                    tracer = TestTraceDriver().tracer,
                    initialCapacityPow2 = 6,
                    maxCapacityPow2 = 8,
                ) to Job().apply { complete() }
            },
            GameOfLifeAlgorithmFactory("Configurable Algorithm") {
                val preferences = TestComposeLifePreferences()

                val job =
                    launch {
                        while (true) {
                            preferences.setAlgorithmChoice(AlgorithmType.HashLifeAlgorithm)
                            delay(10)
                            preferences.setAlgorithmChoice(AlgorithmType.LeanHashLifeAlgorithm)
                            delay(10)
                            preferences.setAlgorithmChoice(AlgorithmType.FlatLeanHashLifeAlgorithm)
                            delay(10)
                            preferences.setAlgorithmChoice(AlgorithmType.NaiveAlgorithm)
                            delay(10)
                        }
                    }

                ConfigurableGameOfLifeAlgorithm(
                    preferences = preferences,
                    naiveGameOfLifeAlgorithm = NaiveGameOfLifeAlgorithm(it),
                    hashLifeAlgorithm = HashLifeAlgorithm(
                        dispatchers = it,
                        tracer = TestTraceDriver().tracer,
                    ),
                    leanHashLifeAlgorithm = LeanHashLifeAlgorithm(
                        dispatchers = it,
                        tracer = TestTraceDriver().tracer,
                    ),
                    flatLeanHashLifeAlgorithm = FlatLeanHashLifeAlgorithm(
                        dispatchers = it,
                        tracer = TestTraceDriver().tracer,
                    ),
                ) to job
            },
        )
    val cellStateMappers =
        listOf(
            CellStateMapper("Identity") { cellState ->
                cellState
            },
            CellStateMapper("Flip across x-axis") { cellState ->
                CellState(cellState.aliveCells.map { cell -> IntOffset(cell.x, -cell.y) }.toSet())
            },
            CellStateMapper("Flip across y-axis") { cellState ->
                CellState(cellState.aliveCells.map { cell -> IntOffset(-cell.x, cell.y) }.toSet())
            },
            CellStateMapper("Flip across x = y") { cellState ->
                CellState(cellState.aliveCells.map { cell -> IntOffset(cell.y, cell.x) }.toSet())
            },
            CellStateMapper("Translate by an arbitrary amount") { cellState ->
                CellState(cellState.aliveCells.map { cell -> cell + IntOffset(157, 72) }.toSet())
            },
        )

    val testPatterns: List<GameOfLifeTestPattern> = GameOfLifeTestPattern.values
    algorithmFactories.forEach { algorithmFactory ->
        testSuite(name = algorithmFactory.toString()) {
            cellStateMappers.forEach { cellStateMapper ->
                testSuite(name = cellStateMapper.toString()) {
                    testPatterns.forEach { testPattern ->
                        // Skip patterns that take too long to verify
                        if (testPattern is Pattern52448M || testPattern is BlomPattern) {
                            return@forEach
                        }
                        if (algorithmFactory.algorithmName != "HashLife Algorithm" &&
                            testPattern is RPentominoPattern
                        ) {
                            return@forEach
                        }

                        testSuite(testPattern.toString()) {
                            test("one_generation_step_flow") {
                                @OptIn(ExperimentalStdlibApi::class)
                                val dispatcher =
                                    currentCoroutineContext()[ContinuationInterceptor] as CoroutineDispatcher
                                val (algorithm, job) =
                                    algorithmFactory.factory(
                                        this,
                                        TestComposeLifeDispatchers(
                                            generalTestDispatcher = dispatcher,
                                            cellTickerTestDispatcher = dispatcher,
                                        ),
                                    )

                                algorithm
                                    .computeGenerationsWithStep(
                                        originalCellState = cellStateMapper.mapper(testPattern.seedCellState),
                                        step = 1,
                                    ).onEach {
                                        delay(10.milliseconds)
                                    }.take(testPattern.maxGenerationCellState)
                                    .collectIndexed { index, value ->
                                        testPattern.cellStates[index + 1]?.let { expectedCellState ->
                                            assertCellStateEquals(
                                                cellStateMapper.mapper(expectedCellState),
                                                value,
                                            )
                                        }
                                    }

                                job.cancel()
                            }

                            test("two_generation_step_flow") {
                                @OptIn(ExperimentalStdlibApi::class)
                                val dispatcher =
                                    currentCoroutineContext()[ContinuationInterceptor] as CoroutineDispatcher
                                val (algorithm, job) =
                                    algorithmFactory.factory(
                                        this,
                                        TestComposeLifeDispatchers(
                                            generalTestDispatcher = dispatcher,
                                            cellTickerTestDispatcher = dispatcher,
                                        ),
                                    )

                                algorithm
                                    .computeGenerationsWithStep(
                                        originalCellState = cellStateMapper.mapper(testPattern.seedCellState),
                                        step = 2,
                                    ).onEach {
                                        delay(10.milliseconds)
                                    }.take(testPattern.maxGenerationCellState / 2)
                                    .collectIndexed { index, value ->
                                        testPattern.cellStates[(index + 1) * 2]?.let { expectedCellState ->
                                            assertCellStateEquals(
                                                cellStateMapper.mapper(expectedCellState),
                                                value,
                                            )
                                        }
                                    }

                                job.cancel()
                            }

                            test("subsequent_one_generation_step") {
                                @OptIn(ExperimentalStdlibApi::class)
                                val dispatcher =
                                    currentCoroutineContext()[ContinuationInterceptor] as CoroutineDispatcher
                                val (algorithm, job) =
                                    algorithmFactory.factory(
                                        this,
                                        TestComposeLifeDispatchers(
                                            generalTestDispatcher = dispatcher,
                                            cellTickerTestDispatcher = dispatcher,
                                        ),
                                    )

                                var previous = cellStateMapper.mapper(testPattern.seedCellState)

                                repeat(testPattern.maxGenerationCellState) { index ->
                                    val current = algorithm.computeNextGeneration(previous)
                                    testPattern.cellStates[index + 1]?.let { expectedCellState ->
                                        assertCellStateEquals(
                                            cellStateMapper.mapper(expectedCellState),
                                            current,
                                        )
                                    }
                                    previous = current
                                }

                                job.cancel()
                            }

                            test("subsequent_two_generation_step") {
                                @OptIn(ExperimentalStdlibApi::class)
                                val dispatcher =
                                    currentCoroutineContext()[ContinuationInterceptor] as CoroutineDispatcher
                                val (algorithm, job) =
                                    algorithmFactory.factory(
                                        this,
                                        TestComposeLifeDispatchers(
                                            generalTestDispatcher = dispatcher,
                                            cellTickerTestDispatcher = dispatcher,
                                        ),
                                    )

                                var previous = cellStateMapper.mapper(testPattern.seedCellState)

                                repeat(testPattern.maxGenerationCellState / 2) { index ->
                                    val current = algorithm.computeGenerationWithStep(previous, 2)
                                    testPattern.cellStates[(index + 1) * 2]?.let { expectedCellState ->
                                        assertCellStateEquals(
                                            cellStateMapper.mapper(expectedCellState),
                                            current,
                                        )
                                    }
                                    previous = current
                                }

                                job.cancel()
                            }
                        }
                    }
                }
            }
        }
    }

    test("flat_lean_hashlife_sparse_wide_span") {
        @OptIn(ExperimentalStdlibApi::class)
        val dispatcher =
            currentCoroutineContext()[ContinuationInterceptor] as CoroutineDispatcher
        val dispatchers = TestComposeLifeDispatchers(
            generalTestDispatcher = dispatcher,
            cellTickerTestDispatcher = dispatcher,
        )
        val algorithm = FlatLeanHashLifeAlgorithm(
            dispatchers = dispatchers,
            tracer = TestTraceDriver().tracer,
        )
        val block1 = setOf(
            IntOffset(0, 0),
            IntOffset(1, 0),
            IntOffset(0, 1),
            IntOffset(1, 1),
        )
        val block2 = setOf(
            IntOffset(300_000, 300_000),
            IntOffset(300_001, 300_000),
            IntOffset(300_000, 300_001),
            IntOffset(300_001, 300_001),
        )
        val state = CellState(block1 + block2)
        val stepped = algorithm.computeGenerationWithStep(state, 1)
        assertEquals(8, stepped.aliveCells.size)
        assertEquals(state.aliveCells, stepped.aliveCells.toSet())
    }

    test("flat_lean_hashlife_differential_random_soup") {
        @OptIn(ExperimentalStdlibApi::class)
        val dispatcher =
            currentCoroutineContext()[ContinuationInterceptor] as CoroutineDispatcher
        val dispatchers = TestComposeLifeDispatchers(
            generalTestDispatcher = dispatcher,
            cellTickerTestDispatcher = dispatcher,
        )
        val flatAlgorithm = FlatLeanHashLifeAlgorithm(
            dispatchers = dispatchers,
            tracer = TestTraceDriver().tracer,
        )
        val referenceAlgorithm = HashLifeAlgorithm(
            dispatchers = dispatchers,
            tracer = TestTraceDriver().tracer,
        )

        val random = Random(42)
        val aliveCells = mutableSetOf<IntOffset>()
        for (x in 0 until 48) {
            for (y in 0 until 48) {
                if (random.nextDouble() < 0.35) {
                    aliveCells.add(IntOffset(x, y))
                }
            }
        }
        var flatState: CellState = CellState(aliveCells)
        var refState: CellState = CellState(aliveCells)

        repeat(25) {
            flatState = flatAlgorithm.computeGenerationWithStep(flatState, 1)
            refState = referenceAlgorithm.computeGenerationWithStep(refState, 1)
            assertCellStateEquals(refState, flatState)
        }
    }

    test("flat_lean_hashlife_capacity_overflow_terminates_explicitly") {
        @OptIn(ExperimentalStdlibApi::class)
        val dispatcher =
            currentCoroutineContext()[ContinuationInterceptor] as CoroutineDispatcher
        val dispatchers = TestComposeLifeDispatchers(
            generalTestDispatcher = dispatcher,
            cellTickerTestDispatcher = dispatcher,
        )
        val tinyAlgorithm = FlatLeanHashLifeAlgorithm(
            dispatchers = dispatchers,
            tracer = TestTraceDriver().tracer,
            initialCapacityPow2 = 6,
            maxCapacityPow2 = 8,
        )
        val random = Random(12345)
        val aliveCells = mutableSetOf<IntOffset>()
        for (x in 0 until 200) {
            for (y in 0 until 200) {
                if (random.nextDouble() < 0.5) {
                    aliveCells.add(IntOffset(x, y))
                }
            }
        }
        val state = CellState(aliveCells)
        assertFailsWith<FlatHashLifeArenaException> {
            tinyAlgorithm.computeGenerationWithStep(state, 1)
        }

        // Prove recovery: subsequent calls on the same instance work normally
        val glider = CellState(
            setOf(
                IntOffset(2, 0),
                IntOffset(0, 1),
                IntOffset(2, 1),
                IntOffset(1, 2),
                IntOffset(2, 2),
            ),
        )
        val referenceAlgorithm = HashLifeAlgorithm(
            dispatchers = dispatchers,
            tracer = TestTraceDriver().tracer,
        )
        val steppedGlider = tinyAlgorithm.computeGenerationWithStep(glider, 1)
        val expectedGlider = referenceAlgorithm.computeGenerationWithStep(glider, 1)
        assertCellStateEquals(expectedGlider, steppedGlider)
    }

    test("flat_lean_hashlife_imports_repetitive_hashlife_cell_state_correctly") {
        @OptIn(ExperimentalStdlibApi::class)
        val dispatcher =
            currentCoroutineContext()[ContinuationInterceptor] as CoroutineDispatcher
        val dispatchers = TestComposeLifeDispatchers(
            generalTestDispatcher = dispatcher,
            cellTickerTestDispatcher = dispatcher,
        )
        val algorithm = FlatLeanHashLifeAlgorithm(
            dispatchers = dispatchers,
            tracer = TestTraceDriver().tracer,
            initialCapacityPow2 = 10,
        )
        // 2,048x2,048 grid of 2x2 blocks (each block is 2x2 cells at every 16th coordinate)
        val blockCells = mutableSetOf<IntOffset>()
        for (x in 0 until 128) {
            for (y in 0 until 128) {
                val bx = x * 16
                val by = y * 16
                blockCells.add(IntOffset(bx, by))
                blockCells.add(IntOffset(bx + 1, by))
                blockCells.add(IntOffset(bx, by + 1))
                blockCells.add(IntOffset(bx + 1, by + 1))
            }
        }
        val hashLifeState = CellState(blockCells).toHashLifeCellState()
        val stepped = algorithm.computeGenerationWithStep(hashLifeState, 1)
        assertEquals(blockCells.size, stepped.aliveCells.size)
        assertEquals(blockCells, stepped.aliveCells.toSet())
    }

    test("flat_lean_hashlife_imports_level_4_hashlife_cell_state_with_offset") {
        @OptIn(ExperimentalStdlibApi::class)
        val dispatcher =
            currentCoroutineContext()[ContinuationInterceptor] as CoroutineDispatcher
        val dispatchers = TestComposeLifeDispatchers(
            generalTestDispatcher = dispatcher,
            cellTickerTestDispatcher = dispatcher,
        )
        val algorithm = FlatLeanHashLifeAlgorithm(
            dispatchers = dispatchers,
            tracer = TestTraceDriver().tracer,
        )
        val referenceAlgorithm = HashLifeAlgorithm(
            dispatchers = dispatchers,
            tracer = TestTraceDriver().tracer,
        )
        val glider = CellState(
            setOf(
                IntOffset(2, 0),
                IntOffset(0, 1),
                IntOffset(2, 1),
                IntOffset(1, 2),
                IntOffset(2, 2),
            ).map { it + IntOffset(157, -72) }.toSet(),
        )
        val hashLifeState = glider.toHashLifeCellState()
        assertEquals(4u, hashLifeState.macroCell.level())

        assertCellStateEquals(glider, algorithm.computeGenerationWithStep(hashLifeState, 0))
        assertCellStateEquals(
            referenceAlgorithm.computeGenerationWithStep(glider, 1),
            algorithm.computeGenerationWithStep(hashLifeState, 1),
        )
    }

    test("flat_lean_hashlife_out_of_range_generation_fails_explicitly") {
        @OptIn(ExperimentalStdlibApi::class)
        val dispatcher =
            currentCoroutineContext()[ContinuationInterceptor] as CoroutineDispatcher
        val dispatchers = TestComposeLifeDispatchers(
            generalTestDispatcher = dispatcher,
            cellTickerTestDispatcher = dispatcher,
        )
        val algorithm = FlatLeanHashLifeAlgorithm(
            dispatchers = dispatchers,
            tracer = TestTraceDriver().tracer,
        )
        val block1 = setOf(
            IntOffset(0, 0),
            IntOffset(1, 0),
            IntOffset(0, 1),
            IntOffset(1, 1),
        )
        val block2 = block1.map { it + IntOffset(600_000_000, 0) }.toSet()
        val state = CellState(block1 + block2)
        assertFailsWith<FlatHashLifeArenaException> {
            algorithm.computeGenerationWithStep(state, 1)
        }
    }

    test("configurable_algorithm_falls_back_on_flat_lean_capacity_overflow") {
        @OptIn(ExperimentalStdlibApi::class)
        val dispatcher =
            currentCoroutineContext()[ContinuationInterceptor] as CoroutineDispatcher
        val dispatchers = TestComposeLifeDispatchers(
            generalTestDispatcher = dispatcher,
            cellTickerTestDispatcher = dispatcher,
        )
        val preferences = TestComposeLifePreferences()
        preferences.setAlgorithmChoice(AlgorithmType.FlatLeanHashLifeAlgorithm)

        val tinyFlatAlgorithm = FlatLeanHashLifeAlgorithm(
            dispatchers = dispatchers,
            tracer = TestTraceDriver().tracer,
            initialCapacityPow2 = 6,
            maxCapacityPow2 = 8,
        )
        val hashLifeAlgorithm = HashLifeAlgorithm(
            dispatchers = dispatchers,
            tracer = TestTraceDriver().tracer,
        )
        val configurableAlgorithm = ConfigurableGameOfLifeAlgorithm(
            preferences = preferences,
            naiveGameOfLifeAlgorithm = NaiveGameOfLifeAlgorithm(
                dispatchers = dispatchers,
            ),
            hashLifeAlgorithm = hashLifeAlgorithm,
            leanHashLifeAlgorithm = LeanHashLifeAlgorithm(
                dispatchers = dispatchers,
                tracer = TestTraceDriver().tracer,
            ),
            flatLeanHashLifeAlgorithm = tinyFlatAlgorithm,
        )

        val random = Random(12345)
        val aliveCells = mutableSetOf<IntOffset>()
        for (x in 0 until 200) {
            for (y in 0 until 200) {
                if (random.nextDouble() < 0.5) {
                    aliveCells.add(IntOffset(x, y))
                }
            }
        }
        val largeState = CellState(aliveCells)

        val stepped = configurableAlgorithm.computeGenerationWithStep(largeState, 1)
        val expected = hashLifeAlgorithm.computeGenerationWithStep(largeState, 1)
        assertCellStateEquals(expected, stepped)
    }
}
