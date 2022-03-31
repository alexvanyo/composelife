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

import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.dispatchers.TestComposeLifeDispatchers
import com.alexvanyo.composelife.patterns.GameOfLifeTestPattern
import com.alexvanyo.composelife.patterns.values
import com.alexvanyo.composelife.preferences.AlgorithmType
import com.alexvanyo.composelife.preferences.TestComposeLifePreferences
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
import org.junit.jupiter.api.extension.ExtensionContext
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.ArgumentsProvider
import org.junit.jupiter.params.provider.ArgumentsSource
import java.util.stream.Stream
import kotlin.test.assertEquals

@OptIn(ExperimentalCoroutinesApi::class)
class GameOfLifeAlgorithmTests {

    class GameOfLifeAlgorithmFactory(
        val algorithmName: String,
        val factory: TestScope.(dispatchers: ComposeLifeDispatchers) -> Pair<GameOfLifeAlgorithm, Job>,
    ) {
        override fun toString(): String = algorithmName
    }

    class GameOfLifeAlgorithmTestArguments(
        val algorithmFactory: GameOfLifeAlgorithmFactory,
        val testPattern: GameOfLifeTestPattern,
    ) {
        override fun toString(): String = "algo: ${algorithmFactory.algorithmName}, pattern: ${testPattern.patternName}"
    }

    class GameOfLifeAlgorithmTestProvider : ArgumentsProvider {
        override fun provideArguments(context: ExtensionContext?): Stream<out Arguments> {
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

                    runCurrent()

                    ConfigurableGameOfLifeAlgorithm(
                        preferences = preferences,
                        naiveGameOfLifeAlgorithm = NaiveGameOfLifeAlgorithm(it),
                        hashLifeAlgorithm = HashLifeAlgorithm(it),
                    ) to job
                },
            )

            return algorithmFactories.flatMap { algorithmFactory ->
                GameOfLifeTestPattern.values.map { testPattern ->
                    GameOfLifeAlgorithmTestArguments(
                        algorithmFactory = algorithmFactory,
                        testPattern = testPattern,
                    )
                }
            }
                .stream()
                .map(Arguments::of)
        }
    }

    @ParameterizedTest(name = "{displayName}: {0}")
    @ArgumentsSource(GameOfLifeAlgorithmTestProvider::class)
    fun `one generation step flow`(args: GameOfLifeAlgorithmTestArguments) = runTest {
        val (algorithm, job) = args.algorithmFactory.factory(
            this,
            TestComposeLifeDispatchers(
                StandardTestDispatcher(testScheduler),
            ),
        )

        assertEquals(
            args.testPattern.cellStates,
            algorithm.computeGenerationsWithStep(
                originalCellState = args.testPattern.seedCellState,
                step = 1,
            )
                .onEach {
                    testScheduler.advanceTimeBy(10)
                    testScheduler.runCurrent()
                }
                .take(args.testPattern.cellStates.size)
                .toList(),
        )

        job.cancel()
    }

    @ParameterizedTest(name = "{displayName}: {0}")
    @ArgumentsSource(GameOfLifeAlgorithmTestProvider::class)
    fun `two generation step flow`(args: GameOfLifeAlgorithmTestArguments) = runTest {
        val (algorithm, job) = args.algorithmFactory.factory(
            this,
            TestComposeLifeDispatchers(
                StandardTestDispatcher(testScheduler),
            ),
        )

        assertEquals(
            args.testPattern.cellStates.filterIndexed { index, _ -> index.rem(2) == 1 },
            algorithm.computeGenerationsWithStep(
                originalCellState = args.testPattern.seedCellState,
                step = 2,
            )
                .onEach {
                    testScheduler.advanceTimeBy(10)
                    testScheduler.runCurrent()
                }
                .take(args.testPattern.cellStates.size / 2)
                .toList(),
        )

        job.cancel()
    }

    @ParameterizedTest(name = "{displayName}: {0}")
    @ArgumentsSource(GameOfLifeAlgorithmTestProvider::class)
    fun `subsequent one generation step`(args: GameOfLifeAlgorithmTestArguments) = runTest {
        val (algorithm, job) = args.algorithmFactory.factory(
            this,
            TestComposeLifeDispatchers(
                StandardTestDispatcher(testScheduler),
            ),
        )

        val actualCellStates = (1..args.testPattern.cellStates.size)
            .scan(args.testPattern.seedCellState) { previousCellState, _ ->
                algorithm.computeNextGeneration(previousCellState)
            }
            .drop(1)

        assertEquals(
            args.testPattern.cellStates,
            actualCellStates,
        )

        job.cancel()
    }

    @ParameterizedTest(name = "{displayName}: {0}")
    @ArgumentsSource(GameOfLifeAlgorithmTestProvider::class)
    fun `subsequent two generation step`(args: GameOfLifeAlgorithmTestArguments) = runTest {
        val (algorithm, job) = args.algorithmFactory.factory(
            this,
            TestComposeLifeDispatchers(
                StandardTestDispatcher(testScheduler),
            ),
        )

        val actualCellStates = (1..args.testPattern.cellStates.size / 2)
            .scan(args.testPattern.seedCellState) { previousCellState, _ ->
                algorithm.computeGenerationWithStep(previousCellState, 2)
            }
            .drop(1)

        assertEquals(
            args.testPattern.cellStates.filterIndexed { index, _ -> index.rem(2) == 1 },
            actualCellStates,
        )

        job.cancel()
    }
}
