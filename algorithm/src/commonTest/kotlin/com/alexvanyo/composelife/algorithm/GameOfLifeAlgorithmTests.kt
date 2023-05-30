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
import com.alexvanyo.composelife.patterns.GameOfLifeTestPattern
import com.alexvanyo.composelife.patterns.GameOfLifeTestPatternEnum
import com.alexvanyo.composelife.patterns.sealedObject
import com.alexvanyo.composelife.preferences.AlgorithmType
import com.alexvanyo.composelife.preferences.TestComposeLifePreferences
import com.google.testing.junit.testparameterinjector.TestParameter
import com.google.testing.junit.testparameterinjector.TestParameterInjector
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.Job
import kotlinx.coroutines.delay
import kotlinx.coroutines.flow.onEach
import kotlinx.coroutines.flow.take
import kotlinx.coroutines.flow.toList
import kotlinx.coroutines.launch
import kotlinx.coroutines.test.StandardTestDispatcher
import kotlinx.coroutines.test.TestScope
import kotlinx.coroutines.test.runCurrent
import kotlinx.coroutines.test.runTest
import org.junit.runner.RunWith
import kotlin.test.Test
import kotlin.test.assertEquals

@OptIn(ExperimentalCoroutinesApi::class)
@RunWith(TestParameterInjector::class)
class GameOfLifeAlgorithmTests {

    class GameOfLifeAlgorithmFactory(
        private val algorithmName: String,
        val factory: TestScope.(dispatchers: ComposeLifeDispatchers) -> Pair<GameOfLifeAlgorithm, Job>,
    ) {
        override fun toString(): String = algorithmName

        class Provider : TestParameter.TestParameterValuesProvider {
            override fun provideValues() =
                listOf(
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

                        runCurrent()

                        ConfigurableGameOfLifeAlgorithm(
                            preferences = preferences,
                            naiveGameOfLifeAlgorithm = NaiveGameOfLifeAlgorithm(it),
                            hashLifeAlgorithm = HashLifeAlgorithm(it),
                        ) to job
                    },
                )
        }
    }

    class CellStateMapper(
        private val name: String,
        val mapper: (CellState) -> CellState,
    ) {
        override fun toString(): String = name

        class Provider : TestParameter.TestParameterValuesProvider {
            override fun provideValues() =
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
        }
    }

    @TestParameter
    lateinit var testPatternEnum: GameOfLifeTestPatternEnum

    private val testPattern: GameOfLifeTestPattern get() = testPatternEnum.sealedObject

    @TestParameter(valuesProvider = GameOfLifeAlgorithmFactory.Provider::class)
    lateinit var algorithmFactory: GameOfLifeAlgorithmFactory

    @TestParameter(valuesProvider = CellStateMapper.Provider::class)
    lateinit var cellStateMapper: CellStateMapper

    @Test
    fun one_generation_step_flow() = runTest {
        val (algorithm, job) = algorithmFactory.factory(
            this,
            TestComposeLifeDispatchers(
                StandardTestDispatcher(testScheduler),
            ),
        )

        assertEquals(
            testPattern.cellStates.map { cellStateMapper.mapper(it) },
            algorithm.computeGenerationsWithStep(
                originalCellState = cellStateMapper.mapper(testPattern.seedCellState),
                step = 1,
            )
                .onEach {
                    testScheduler.advanceTimeBy(10)
                    testScheduler.runCurrent()
                }
                .take(testPattern.cellStates.size)
                .toList(),
        )

        job.cancel()
    }

    @Test
    fun two_generation_step_flow() = runTest {
        val (algorithm, job) = algorithmFactory.factory(
            this,
            TestComposeLifeDispatchers(
                StandardTestDispatcher(testScheduler),
            ),
        )

        assertEquals(
            testPattern.cellStates
                .filterIndexed { index, _ -> index.rem(2) == 1 }
                .map { cellStateMapper.mapper(it) },
            algorithm.computeGenerationsWithStep(
                originalCellState = cellStateMapper.mapper(testPattern.seedCellState),
                step = 2,
            )
                .onEach {
                    testScheduler.advanceTimeBy(10)
                    testScheduler.runCurrent()
                }
                .take(testPattern.cellStates.size / 2)
                .toList(),
        )

        job.cancel()
    }

    @Test
    fun subsequent_one_generation_step() = runTest {
        val (algorithm, job) = algorithmFactory.factory(
            this,
            TestComposeLifeDispatchers(
                StandardTestDispatcher(testScheduler),
            ),
        )

        val actualCellStates = (1..testPattern.cellStates.size)
            .scan(cellStateMapper.mapper(testPattern.seedCellState)) { previousCellState, _ ->
                algorithm.computeNextGeneration(previousCellState)
            }
            .drop(1)

        assertEquals(
            testPattern.cellStates.map { cellStateMapper.mapper(it) },
            actualCellStates,
        )

        job.cancel()
    }

    @Test
    fun subsequent_two_generation_step() = runTest {
        val (algorithm, job) = algorithmFactory.factory(
            this,
            TestComposeLifeDispatchers(
                StandardTestDispatcher(testScheduler),
            ),
        )

        val actualCellStates = (1..testPattern.cellStates.size / 2)
            .scan(cellStateMapper.mapper(testPattern.seedCellState)) { previousCellState, _ ->
                algorithm.computeGenerationWithStep(previousCellState, 2)
            }
            .drop(1)

        assertEquals(
            testPattern.cellStates
                .filterIndexed { index, _ -> index.rem(2) == 1 }
                .map { cellStateMapper.mapper(it) },
            actualCellStates,
        )

        job.cancel()
    }
}
