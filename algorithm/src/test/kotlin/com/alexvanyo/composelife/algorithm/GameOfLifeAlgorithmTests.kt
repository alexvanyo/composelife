package com.alexvanyo.composelife.algorithm

import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.dispatchers.TestComposeLifeDispatchers
import com.alexvanyo.composelife.patterns.GameOfLifeTestPattern
import com.alexvanyo.composelife.patterns.values
import com.alexvanyo.composelife.preferences.ComposeLifePreferences
import com.alexvanyo.composelife.preferences.proto.Algorithm
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.delay
import kotlinx.coroutines.flow.Flow
import kotlinx.coroutines.flow.flow
import kotlinx.coroutines.flow.onEach
import kotlinx.coroutines.flow.take
import kotlinx.coroutines.flow.toList
import kotlinx.coroutines.test.StandardTestDispatcher
import kotlinx.coroutines.test.runTest
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.extension.ExtensionContext
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.ArgumentsProvider
import org.junit.jupiter.params.provider.ArgumentsSource
import java.util.stream.Stream

@OptIn(ExperimentalCoroutinesApi::class)
class GameOfLifeAlgorithmTests {

    class GameOfLifeAlgorithmFactory(
        val algorithmName: String,
        val factory: (dispatchers: ComposeLifeDispatchers) -> GameOfLifeAlgorithm,
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
                GameOfLifeAlgorithmFactory("Naive Algorithm") { NaiveGameOfLifeAlgorithm(it) },
                GameOfLifeAlgorithmFactory("HashLife Algorithm") { HashLifeAlgorithm(it) },
                GameOfLifeAlgorithmFactory("Configurable Algorithm") {
                    ConfigurableGameOfLifeAlgorithm(
                        preferences = object : ComposeLifePreferences {
                            override val algorithmChoice: Flow<Algorithm> = flow {
                                while (true) {
                                    emit(Algorithm.HASHLIFE)
                                    delay(10)
                                    emit(Algorithm.NAIVE)
                                    delay(10)
                                }
                            }

                            override suspend fun setAlgorithmChoice(algorithm: Algorithm) = Unit
                        },
                        naiveGameOfLifeAlgorithm = NaiveGameOfLifeAlgorithm(it),
                        hashLifeAlgorithm = HashLifeAlgorithm(it)
                    )
                }
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
    fun `one generation step flow`(args: GameOfLifeAlgorithmTestArguments) = runTest {
        val algorithm = args.algorithmFactory.factory(TestComposeLifeDispatchers(StandardTestDispatcher(testScheduler)))

        assertEquals(
            args.testPattern.cellStates,
            algorithm.computeGenerationsWithStep(
                originalCellState = args.testPattern.seedCellState,
                step = 1
            )
                .onEach {
                    testScheduler.advanceTimeBy(10)
                    testScheduler.runCurrent()
                }
                .take(args.testPattern.cellStates.size)
                .toList()
        )
    }

    @ParameterizedTest(name = "{displayName}: {0}")
    @ArgumentsSource(GameOfLifeAlgorithmTestProvider::class)
    fun `two generation step flow`(args: GameOfLifeAlgorithmTestArguments) = runTest {
        val algorithm = args.algorithmFactory.factory(TestComposeLifeDispatchers(StandardTestDispatcher(testScheduler)))

        assertEquals(
            args.testPattern.cellStates.filterIndexed { index, _ -> index.rem(2) == 1 },
            algorithm.computeGenerationsWithStep(
                originalCellState = args.testPattern.seedCellState,
                step = 2
            )
                .onEach {
                    testScheduler.advanceTimeBy(10)
                    testScheduler.runCurrent()
                }
                .take(args.testPattern.cellStates.size / 2)
                .toList()
        )
    }

    @ParameterizedTest(name = "{displayName}: {0}")
    @ArgumentsSource(GameOfLifeAlgorithmTestProvider::class)
    fun `subsequent one generation step`(args: GameOfLifeAlgorithmTestArguments) = runTest {
        val algorithm = args.algorithmFactory.factory(TestComposeLifeDispatchers(StandardTestDispatcher(testScheduler)))

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

    @ParameterizedTest(name = "{displayName}: {0}")
    @ArgumentsSource(GameOfLifeAlgorithmTestProvider::class)
    fun `subsequent two generation step`(args: GameOfLifeAlgorithmTestArguments) = runTest {
        val algorithm = args.algorithmFactory.factory(TestComposeLifeDispatchers(StandardTestDispatcher(testScheduler)))

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
