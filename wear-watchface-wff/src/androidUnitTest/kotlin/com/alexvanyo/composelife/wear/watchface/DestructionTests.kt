/*
 * Copyright 2025 The Android Open Source Project
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

package com.alexvanyo.composelife.wear.watchface

import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.IntRect
import androidx.compose.ui.unit.IntSize
import com.alexvanyo.composelife.algorithm.HashLifeAlgorithm
import com.alexvanyo.composelife.dispatchers.TestComposeLifeDispatchers
import com.alexvanyo.composelife.model.CellState
import com.alexvanyo.composelife.model.CellWindow
import com.alexvanyo.composelife.model.DeserializationResult
import com.alexvanyo.composelife.model.RunLengthEncodedCellStateSerializer
import com.alexvanyo.composelife.model.emptyCellState
import com.alexvanyo.composelife.model.toCellState
import com.google.testing.junit.testparameterinjector.TestParameter
import com.google.testing.junit.testparameterinjector.TestParameterValuesProvider
import kotlinx.coroutines.flow.any
import kotlinx.coroutines.flow.drop
import kotlinx.coroutines.flow.take
import kotlinx.coroutines.flow.toList
import kotlinx.coroutines.flow.withIndex
import kotlinx.coroutines.test.StandardTestDispatcher
import kotlinx.coroutines.test.runTest
import kotlinx.datetime.LocalTime
import org.junit.runner.RunWith
import org.robolectric.RobolectricTestParameterInjector
import java.io.File
import kotlin.random.Random
import kotlin.random.nextInt
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.time.Duration

@RunWith(RobolectricTestParameterInjector::class)
class DestructionTests {
    private val testDispatcher = StandardTestDispatcher()

    private val algorithm = HashLifeAlgorithm(
        TestComposeLifeDispatchers(testDispatcher, testDispatcher)
    )

    class TargetTimeDigits(
        val timeDigits: TimeDigits,
    ) {
        override fun toString(): String = timeDigits.toString()

        class Provider : TestParameterValuesProvider() {
            override fun provideValues(context: Context?) =
                (0..23).flatMap { hour ->
                    (0..59).flatMap { minute ->
                        listOf(false, true).map { use24HourFormat ->
                            TargetTimeDigits(
                                timeDigits = createTimeDigits(
                                    localTime = LocalTime(hour = hour, minute = minute),
                                    use24HourFormat = use24HourFormat,
                                ),
                            )
                        }
                    }
                }.toSet().toList()
        }
    }

    @TestParameter(valuesProvider = TargetTimeDigits.Provider::class)
    lateinit var targetTimeDigits: TargetTimeDigits

    private val TARGET_POPULATION = 200
    private val MAX_PHASE = 2
    private val MAX_GENERATIONS = 300

    val solutionCellStateFile get() =
        File("src/androidUnitTest/resources/solutions/${targetTimeDigits.timeDigits.firstDigit.char}${targetTimeDigits.timeDigits.secondDigit.char}:${targetTimeDigits.timeDigits.thirdDigit.char}${targetTimeDigits.timeDigits.fourthDigit.char}.rle")
    val solutionImagesDirectory get() =
        File("src/androidUnitTest/resources/solutions/${targetTimeDigits.timeDigits.firstDigit.char}${targetTimeDigits.timeDigits.secondDigit.char}:${targetTimeDigits.timeDigits.thirdDigit.char}${targetTimeDigits.timeDigits.fourthDigit.char}")

    @Test
    fun destructionIsCorrect() = runTest(testDispatcher, timeout = Duration.INFINITE) {
        var solution: CellState? = if (solutionCellStateFile.exists()) {
            solutionCellStateFile.useLines {
                val deserializationResult =
                    RunLengthEncodedCellStateSerializer.deserializeToCellState(it)
                when (deserializationResult) {
                    is DeserializationResult.Successful -> deserializationResult.cellState
                    is DeserializationResult.Unsuccessful -> error("Could not deserialize")
                }
            }
        } else {
            null
        }
        var solutionCount = 0

        while (solution == null) {
            solutionCount++
            val testCellState = createTimeCellState(targetTimeDigits.timeDigits).union(createRandomGliders())
            val (generation, minimumSize) = isDestructionAchieved(
                timeDigits = targetTimeDigits.timeDigits,
                cellState = testCellState,
                maxGenerations = MAX_GENERATIONS,
            )
            if (
                minimumSize <= TARGET_POPULATION &&
                isRepeatingAtEnd(
                    maxPhase = MAX_PHASE,
                    cellState = testCellState,
                    startGeneration = generation,
                    maxGenerations = MAX_GENERATIONS,
                )
            ) {
                solution = testCellState
            }
        }
        assertEquals(
            createTimeCellState(targetTimeDigits.timeDigits).aliveCells,
            solution.getAliveCellsInWindow(
                CellWindow(IntRect(IntOffset(0, 0), IntSize(70, 70)))
            ).toSet()
        )
        val runLengthEncodingLines = RunLengthEncodedCellStateSerializer.serializeToString(solution)

        println(runLengthEncodingLines.joinToString(""))

        solutionCellStateFile.bufferedWriter().use { bufferedWriter ->
            runLengthEncodingLines.forEach { line ->
                bufferedWriter.write(line)
                bufferedWriter.newLine()
            }
        }

        solutionImagesDirectory.mkdir()
        algorithm.computeGenerationsWithStep(solution, 1)
            .take(MAX_GENERATIONS)
            .withIndex()
            .collect { (index, cellState) ->
                solutionImagesDirectory
                    .resolve("frame_$index.xml")
                    .bufferedWriter()
                    .use { bufferedWriter ->
                        bufferedWriter.write("""<vector xmlns:android="http://schemas.android.com/apk/res/android" android:width="70dp" android:height="70dp" android:viewportWidth="70" android:viewportHeight="70">""")
                        bufferedWriter.newLine()

                        repeat(70) { y ->
                            repeat(70) { x ->
                                if (IntOffset(x + 1, y + 1) in cellState.aliveCells) {
                                    bufferedWriter.write("""<path android:pathData="M${x},${y}h1v1h-1z" android:fillColor="#FFF"/>""")
                                    bufferedWriter.newLine()
                                }
                            }
                        }

                        bufferedWriter.write("""</vector>""")
                        bufferedWriter.newLine()
                    }
            }
    }

    private suspend fun isDestructionAchieved(
        timeDigits: TimeDigits,
        cellState: CellState,
        maxGenerations: Int,
    ): IndexedValue<Int> {
        val timeCellState = createTimeCellState(timeDigits)
        return algorithm.computeGenerationsWithStep(
            cellState,
            1,
        )
            .take(maxGenerations)
            .toList()
            .map {
                val aliveCellsInViewport = it.getAliveCellsInWindow(
                    CellWindow(IntRect(IntOffset(0, 0), IntSize(70, 70)))
                ).toSet()
                val aliveCellsInOriginalDigits = aliveCellsInViewport.intersect(timeCellState.aliveCells)
                aliveCellsInViewport.size + aliveCellsInOriginalDigits.size
            }
            .withIndex()
            .minBy { (_, value) -> value }
    }

    private suspend fun isRepeatingAtEnd(
        maxPhase: Int,
        cellState: CellState,
        startGeneration: Int,
        maxGenerations: Int,
    ): Boolean {
        val mostRecentGenerationMap: MutableMap<Set<IntOffset>, Int> = mutableMapOf()
        return algorithm.computeGenerationsWithStep(
            cellState,
            1,
        )
            .take(maxGenerations)
            .drop(startGeneration)
            .withIndex()
            .any { (index, cellState) ->
                val aliveCellsInViewport = cellState.getAliveCellsInWindow(
                    CellWindow(IntRect(IntOffset(0, 0), IntSize(70, 70)))
                ).toSet()
                val mostRecentGeneration = mostRecentGenerationMap[aliveCellsInViewport]
                if (mostRecentGeneration != null && index - mostRecentGeneration <= maxPhase) {
                    true
                } else {
                    mostRecentGenerationMap[aliveCellsInViewport] = index
                    false
                }
            }
    }
}

private fun createTimeCellState(
    timeDigits: TimeDigits,
): CellState = timeDigits.firstDigit.cellState
    .union(timeDigits.secondDigit.cellState.offsetBy(IntOffset(14, 0)))
    .union(timeDigits.thirdDigit.cellState.offsetBy(IntOffset(32, 0)))
    .union(timeDigits.fourthDigit.cellState.offsetBy(IntOffset(46, 0)))
    .union(
        """
            |OO
            |OO
            |..
            |..
            |OO
            |OO
        """.toCellState(IntOffset(27, 6)),
    )
    .offsetBy(IntOffset(8, 26))


private fun createRandomGliders(): CellState {
    val gliderDirections = listOf(
        """
            |.O.
            |..O
            |OOO
        """,
        """
            |O..
            |.OO
            |OO.
        """,
        """
            |.OO
            |O.O
            |..O
        """,
        """
            |.O.
            |.OO
            |O.O
        """,
        """
            |OOO
            |O..
            |.O.
        """,
        """
            |.OO
            |OO.
            |..O
        """,
        """
            |OO.
            |O.O
            |O..
        """,
        """
            |.O.
            |OO.
            |O.O
        """
    )

    return CellState(
        notRoundRandomPointPool
            .shuffled()
            .take(Random.nextInt(2..30))
            .flatMap { point ->
                gliderDirections.random().toCellState(point).aliveCells
            }
            .toSet(),
    )
}

val notRoundRandomPointPool =
    CellWindow(
        IntRect(
            IntOffset(-60, -60),
            IntSize(191, 191),
        ),
    )
        .containedPoints()
        .filter {
            it.x !in -5..74 && it.y !in -5..74
        }

fun createTimeDigits(localTime: LocalTime, use24HourFormat: Boolean): TimeDigits {
    val clockHour = localTime.hour.rem(12)
    val displayHour = if (use24HourFormat) {
        localTime.hour
    } else if (clockHour == 0) {
        12
    } else {
        clockHour
    }

    val hourTensPlace = displayHour / 10
    val firstDigit = if (hourTensPlace == 0 && !use24HourFormat) {
        GameOfLifeSegmentChar.Blank
    } else {
        GameOfLifeSegmentChar.fromChar(hourTensPlace)
    }
    val secondDigit = GameOfLifeSegmentChar.fromChar(displayHour.rem(10))
    val thirdDigit = GameOfLifeSegmentChar.fromChar(localTime.minute / 10)
    val fourthDigit = GameOfLifeSegmentChar.fromChar(localTime.minute.rem(10))

    return TimeDigits(
        firstDigit = firstDigit,
        secondDigit = secondDigit,
        thirdDigit = thirdDigit,
        fourthDigit = fourthDigit,
    )
}

data class TimeDigits(
    val firstDigit: GameOfLifeSegmentChar,
    val secondDigit: GameOfLifeSegmentChar,
    val thirdDigit: GameOfLifeSegmentChar,
    val fourthDigit: GameOfLifeSegmentChar,
)

sealed class GameOfLifeSegmentChar(
    val cellState: CellState,
) {
    data object Zero : GameOfLifeSegmentChar(segA.union(segB).union(segC).union(segD).union(segE).union(segF))
    data object One : GameOfLifeSegmentChar(segB.union(segC))
    data object Two : GameOfLifeSegmentChar(segA.union(segB).union(segD).union(segE).union(segG))
    data object Three : GameOfLifeSegmentChar(segA.union(segB).union(segC).union(segD).union(segG))
    data object Four : GameOfLifeSegmentChar(segB.union(segC).union(segF).union(segG))
    data object Five : GameOfLifeSegmentChar(segA.union(segC).union(segD).union(segF).union(segG))
    data object Six : GameOfLifeSegmentChar(segA.union(segC).union(segD).union(segE).union(segF).union(segG))
    data object Seven : GameOfLifeSegmentChar(segA.union(segB).union(segC))
    data object Eight : GameOfLifeSegmentChar(
        segA.union(segB).union(segC).union(segD).union(segE).union(segF).union(segG),
    )
    data object Nine : GameOfLifeSegmentChar(segA.union(segB).union(segC).union(segD).union(segF).union(segG))
    data object Blank : GameOfLifeSegmentChar(emptyCellState())

    companion object {
        fun fromChar(digit: Int): GameOfLifeSegmentChar {
            return when (digit) {
                0 -> Zero
                1 -> One
                2 -> Two
                3 -> Three
                4 -> Four
                5 -> Five
                6 -> Six
                7 -> Seven
                8 -> Eight
                9 -> Nine
                else -> throw IllegalArgumentException("input wasn't a digit!")
            }
        }
    }
}

val GameOfLifeSegmentChar.char: Char
    get() = when (this) {
        GameOfLifeSegmentChar.Zero -> '0'
        GameOfLifeSegmentChar.One -> '1'
        GameOfLifeSegmentChar.Two -> '2'
        GameOfLifeSegmentChar.Three -> '3'
        GameOfLifeSegmentChar.Four -> '4'
        GameOfLifeSegmentChar.Five -> '5'
        GameOfLifeSegmentChar.Six -> '6'
        GameOfLifeSegmentChar.Seven -> '7'
        GameOfLifeSegmentChar.Eight -> '8'
        GameOfLifeSegmentChar.Nine -> '9'
        GameOfLifeSegmentChar.Blank -> ' '
    }

private val segA = """
    |OO.OO.O.OO
    |OO.O.OO.OO
    |..........
    |..........
    |..........
    |..........
    |..........
    |..........
    |..........
    |..........
    |..........
    |..........
    |..........
    |..........
    |..........
    |..........
    |..........
    |..........
""".toCellState()

private val segB = """
    |........OO
    |........OO
    |..........
    |..........
    |........OO
    |........OO
    |..........
    |..........
    |........OO
    |........OO
    |..........
    |..........
    |..........
    |..........
    |..........
    |..........
    |..........
    |..........
""".toCellState()

private val segC = """
    |..........
    |..........
    |..........
    |..........
    |..........
    |..........
    |..........
    |..........
    |........OO
    |........OO
    |..........
    |..........
    |........OO
    |........OO
    |..........
    |..........
    |........OO
    |........OO
""".toCellState()

private val segD = """
    |..........
    |..........
    |..........
    |..........
    |..........
    |..........
    |..........
    |..........
    |..........
    |..........
    |..........
    |..........
    |..........
    |..........
    |..........
    |..........
    |OO.OO.O.OO
    |OO.O.OO.OO
""".toCellState()

private val segE = """
    |..........
    |..........
    |..........
    |..........
    |..........
    |..........
    |..........
    |..........
    |OO........
    |OO........
    |..........
    |..........
    |OO........
    |OO........
    |..........
    |..........
    |OO........
    |OO........
""".toCellState()

private val segF = """
    |OO........
    |OO........
    |..........
    |..........
    |OO........
    |OO........
    |..........
    |..........
    |OO........
    |OO........
    |..........
    |..........
    |..........
    |..........
    |..........
    |..........
    |..........
    |..........
""".toCellState()

private val segG = """
    |..........
    |..........
    |..........
    |..........
    |..........
    |..........
    |..........
    |..........
    |OO.O.OO.OO
    |OO.OO.O.OO
    |..........
    |..........
    |..........
    |..........
    |..........
    |..........
    |..........
    |..........
""".toCellState()

