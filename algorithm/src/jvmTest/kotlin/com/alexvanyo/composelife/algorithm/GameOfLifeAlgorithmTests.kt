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
import com.alexvanyo.composelife.patterns.BlomPattern
import com.alexvanyo.composelife.patterns.GameOfLifeTestPattern
import com.alexvanyo.composelife.patterns.Pattern52448M
import com.alexvanyo.composelife.patterns.RPentominoPattern
import com.alexvanyo.composelife.patterns.values
import com.alexvanyo.composelife.preferences.AlgorithmType
import com.alexvanyo.composelife.preferences.TestComposeLifePreferences
import com.alexvanyo.composelife.preferences.setAlgorithmChoice
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
import kotlin.time.Duration
import kotlin.time.Duration.Companion.milliseconds

private class GameOfLifeAlgorithmFactory(
    val algorithmName: String,
    val factory: ExecutionScope.(ComposeLifeDispatchers) -> Pair<GameOfLifeAlgorithm, Job>,
) {
    override fun toString(): String = algorithmName
}

private class CellStateMapper(
    val name: String,
    val mapper: (CellState) -> CellState,
) {
    override fun toString(): String = name
}

@OptIn(TestBalloonExperimentalApi::class)
val GameOfLifeAlgorithmTests by testSuite(
    testConfig = TestConfig.testScope(true, Duration.INFINITE),
) {

    val algorithmFactories = listOf(
        GameOfLifeAlgorithmFactory("Naive Algorithm") {
            NaiveGameOfLifeAlgorithm(it) to Job().apply { complete() }
        },
        GameOfLifeAlgorithmFactory("HashLife Algorithm") {
            HashLifeAlgorithm(it) to Job().apply { complete() }
        },
        GameOfLifeAlgorithmFactory("Configurable Algorithm") {
            val preferences = TestComposeLifePreferences()

            val job = launch {
                while (true) {
                    preferences.setAlgorithmChoice(AlgorithmType.HashLifeAlgorithm)
                    delay(10)
                    preferences.setAlgorithmChoice(AlgorithmType.NaiveAlgorithm)
                    delay(10)
                }
            }

            ConfigurableGameOfLifeAlgorithm(
                preferences = preferences,
                naiveGameOfLifeAlgorithm = NaiveGameOfLifeAlgorithm(it),
                hashLifeAlgorithm = HashLifeAlgorithm(it),
            ) to job
        },
    )
    val cellStateMappers = listOf(
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
                            testPattern is RPentominoPattern) {
                            return@forEach
                        }

                        testSuite(testPattern.toString()) {
                            test("one_generation_step_flow") {
                                @OptIn(ExperimentalStdlibApi::class)
                                val dispatcher = currentCoroutineContext()[CoroutineDispatcher]!!
                                val (algorithm, job) = algorithmFactory.factory(
                                    this,
                                    TestComposeLifeDispatchers(
                                        generalTestDispatcher = dispatcher,
                                        cellTickerTestDispatcher = dispatcher,
                                    ),
                                )

                                algorithm.computeGenerationsWithStep(
                                    originalCellState = cellStateMapper.mapper(testPattern.seedCellState),
                                    step = 1,
                                )
                                    .onEach {
                                        delay(10.milliseconds)
                                    }
                                    .take(testPattern.maxGenerationCellState)
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
                                val dispatcher = currentCoroutineContext()[CoroutineDispatcher]!!
                                val (algorithm, job) = algorithmFactory.factory(
                                    this,
                                    TestComposeLifeDispatchers(
                                        generalTestDispatcher = dispatcher,
                                        cellTickerTestDispatcher = dispatcher,
                                    ),
                                )

                                algorithm.computeGenerationsWithStep(
                                    originalCellState = cellStateMapper.mapper(testPattern.seedCellState),
                                    step = 2,
                                )
                                    .onEach {
                                        delay(10.milliseconds)
                                    }
                                    .take(testPattern.maxGenerationCellState / 2)
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
                                val dispatcher = currentCoroutineContext()[CoroutineDispatcher]!!
                                val (algorithm, job) = algorithmFactory.factory(
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
                                val dispatcher = currentCoroutineContext()[CoroutineDispatcher]!!
                                val (algorithm, job) = algorithmFactory.factory(
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
}
