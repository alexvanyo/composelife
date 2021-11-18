package com.alexvanyo.composelife.data

import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.flow.take
import kotlinx.coroutines.flow.toList
import kotlinx.coroutines.test.TestCoroutineDispatcher
import kotlinx.coroutines.test.TestCoroutineScope
import kotlinx.coroutines.test.runBlockingTest
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.extension.ExtensionContext
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.ArgumentsProvider
import org.junit.jupiter.params.provider.ArgumentsSource
import java.util.stream.Stream

@OptIn(ExperimentalCoroutinesApi::class)
class GameOfLifeAlgorithmTests {

    private val testCoroutineDispatcher = TestCoroutineDispatcher()

    private val testCoroutineScope = TestCoroutineScope(testCoroutineDispatcher)

    class GameOfLifeAlgorithmFactory(
        val algorithmName: String,
        val factory: (testCoroutineDispatcher: TestCoroutineDispatcher) -> GameOfLifeAlgorithm
    ) {
        override fun toString(): String = algorithmName
    }

    class GameOfLifeAlgorithmTestArguments(
        val algorithmFactory: GameOfLifeAlgorithmFactory,
        val testPattern: GameOfLifeTestPattern
    ) {
        override fun toString(): String = "algo: ${algorithmFactory.algorithmName}, pattern: ${testPattern.patternName}"
    }

    class GameOfLifeAlgorithmTestProvider : ArgumentsProvider {
        override fun provideArguments(context: ExtensionContext?): Stream<out Arguments> {
            val algorithmFactories = listOf(
                GameOfLifeAlgorithmFactory("Naive Algorithm") { NaiveGameOfLifeAlgorithm(it) }
            )

            return algorithmFactories.flatMap { algorithmFactory ->
                GameOfLifeTestPattern.values.map { testPattern ->
                    GameOfLifeAlgorithmTestArguments(
                        algorithmFactory = algorithmFactory,
                        testPattern = testPattern
                    )
                }
            }
                .stream()
                .map(Arguments::of)
        }
    }

    @ParameterizedTest(name = "{displayName}: {0}")
    @ArgumentsSource(GameOfLifeAlgorithmTestProvider::class)
    fun `one generation step flow`(args: GameOfLifeAlgorithmTestArguments) {
        testCoroutineScope.runBlockingTest {
            val algorithm = args.algorithmFactory.factory(testCoroutineDispatcher)

            assertEquals(
                args.testPattern.cellStates,
                algorithm.computeGenerationsWithStep(
                    originalCellState = args.testPattern.seedCellState,
                    step = 1
                )
                    .take(args.testPattern.cellStates.size)
                    .toList()
            )
        }
    }

    @ParameterizedTest(name = "{displayName}: {0}")
    @ArgumentsSource(GameOfLifeAlgorithmTestProvider::class)
    fun `two generation step flow`(args: GameOfLifeAlgorithmTestArguments) {
        testCoroutineScope.runBlockingTest {
            val algorithm = args.algorithmFactory.factory(testCoroutineDispatcher)

            assertEquals(
                args.testPattern.cellStates.filterIndexed { index, _ -> index.rem(2) == 1 },
                algorithm.computeGenerationsWithStep(
                    originalCellState = args.testPattern.seedCellState,
                    step = 2
                )
                    .take(args.testPattern.cellStates.size / 2)
                    .toList()
            )
        }
    }

    @ParameterizedTest(name = "{displayName}: {0}")
    @ArgumentsSource(GameOfLifeAlgorithmTestProvider::class)
    fun `subsequent one generation step`(args: GameOfLifeAlgorithmTestArguments) {
        testCoroutineScope.runBlockingTest {
            val algorithm = args.algorithmFactory.factory(testCoroutineDispatcher)

            val actualCellStates = (1..args.testPattern.cellStates.size)
                .scan(args.testPattern.seedCellState) { previousCellState, _ ->
                    algorithm.computeNextGeneration(previousCellState)
                }
                .drop(1)

            assertEquals(
                args.testPattern.cellStates,
                actualCellStates
            )
        }
    }

    @ParameterizedTest(name = "{displayName}: {0}")
    @ArgumentsSource(GameOfLifeAlgorithmTestProvider::class)
    fun `subsequent two generation step`(args: GameOfLifeAlgorithmTestArguments) {
        testCoroutineScope.runBlockingTest {
            val algorithm = args.algorithmFactory.factory(testCoroutineDispatcher)

            val actualCellStates = (1..args.testPattern.cellStates.size / 2)
                .scan(args.testPattern.seedCellState) { previousCellState, _ ->
                    algorithm.computeGenerationWithStep(previousCellState, 2)
                }
                .drop(1)

            assertEquals(
                args.testPattern.cellStates.filterIndexed { index, _ -> index.rem(2) == 1 },
                actualCellStates
            )
        }
    }
}
