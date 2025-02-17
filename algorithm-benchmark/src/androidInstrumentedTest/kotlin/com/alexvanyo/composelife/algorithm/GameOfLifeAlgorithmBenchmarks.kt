/*
 * Copyright 2024 The Android Open Source Project
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

import androidx.benchmark.junit4.BenchmarkRule
import androidx.benchmark.junit4.measureRepeated
import androidx.compose.ui.unit.IntOffset
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.dispatchers.TestComposeLifeDispatchers
import com.alexvanyo.composelife.model.CellState
import com.alexvanyo.composelife.patterns.GameOfLifeTestPattern
import com.alexvanyo.composelife.patterns.GosperGliderGunPattern
import com.google.testing.junit.testparameterinjector.TestParameter
import com.google.testing.junit.testparameterinjector.TestParameterInjector
import com.google.testing.junit.testparameterinjector.TestParameterValuesProvider
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.flow.take
import kotlinx.coroutines.runBlocking
import kotlinx.coroutines.test.UnconfinedTestDispatcher
import org.junit.Rule
import org.junit.runner.RunWith
import kotlin.test.Test

@RunWith(TestParameterInjector::class)
class GameOfLifeAlgorithmBenchmarks {

    @get:Rule
    val benchmarkRule = BenchmarkRule()

    class GameOfLifeAlgorithmFactory(
        private val algorithmName: String,
        val factory: (dispatchers: ComposeLifeDispatchers) -> GameOfLifeAlgorithm,
    ) {
        override fun toString(): String = algorithmName

        class Provider : TestParameterValuesProvider() {
            override fun provideValues(context: Context?) =
                listOf(
                    GameOfLifeAlgorithmFactory("Naive Algorithm") {
                        NaiveGameOfLifeAlgorithm(it)
                    },
                    GameOfLifeAlgorithmFactory("HashLife Algorithm") {
                        HashLifeAlgorithm(it)
                    },
                )
        }
    }

    class CellStateMapper(
        private val name: String,
        val mapper: (CellState) -> CellState,
    ) {
        override fun toString(): String = name

        class Provider : TestParameterValuesProvider() {
            override fun provideValues(context: Context?) =
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

    private val testPattern: GameOfLifeTestPattern = GosperGliderGunPattern

    @TestParameter(valuesProvider = GameOfLifeAlgorithmFactory.Provider::class)
    lateinit var algorithmFactory: GameOfLifeAlgorithmFactory

    @TestParameter(valuesProvider = CellStateMapper.Provider::class)
    lateinit var cellStateMapper: CellStateMapper

    @Test
    fun generations_100() {
        @OptIn(ExperimentalCoroutinesApi::class)
        val testDispatcher = UnconfinedTestDispatcher()

        benchmarkRule.measureRepeated {
            runBlocking {
                val algorithm = runWithMeasurementDisabled {
                    algorithmFactory.factory(
                        TestComposeLifeDispatchers(
                            generalTestDispatcher = testDispatcher,
                            cellTickerTestDispatcher = testDispatcher,
                        ),
                    )
                }
                val originalCellState = runWithMeasurementDisabled {
                    cellStateMapper.mapper(testPattern.seedCellState)
                }

                algorithm.computeGenerationsWithStep(
                    originalCellState = originalCellState,
                    step = 1,
                )
                    .take(100)
                    .collect {}
            }
        }
    }
}
