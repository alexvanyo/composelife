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
import com.alexvanyo.composelife.algorithm.GameOfLifeAlgorithm
import com.alexvanyo.composelife.algorithm.HashLifeAlgorithm
import com.alexvanyo.composelife.dispatchers.TestComposeLifeDispatchers
import com.alexvanyo.composelife.geometry.getVonNeumannNeighbors
import com.alexvanyo.composelife.model.CellState
import com.alexvanyo.composelife.model.CellWindow
import com.alexvanyo.composelife.model.DeserializationResult
import com.alexvanyo.composelife.model.RunLengthEncodedCellStateSerializer
import com.alexvanyo.composelife.model.emptyCellState
import com.alexvanyo.composelife.model.toCellState
import de.infix.testBalloon.framework.core.TestCompartment
import de.infix.testBalloon.framework.core.testSuite
import kotlinx.coroutines.CoroutineDispatcher
import kotlinx.coroutines.currentCoroutineContext
import kotlinx.coroutines.flow.any
import kotlinx.coroutines.flow.drop
import kotlinx.coroutines.flow.take
import kotlinx.coroutines.flow.toList
import kotlinx.coroutines.flow.withIndex
import java.io.File
import kotlin.random.Random
import kotlin.random.nextInt
import kotlin.test.assertEquals

private val hourPrefixes = listOf(
    "00", "01", "02", "03", "04", "05", "06", "07", "08", "09",
    "10", "11", "12", "13", "14", "15", "16", "17", "18", "19",
    "20", "21", "22", "23",
    "_1", "_2", "_3", "_4", "_5", "_6", "_7", "_8", "_9",
)

val DestructionTests by testSuite(
    compartment = { TestCompartment.Concurrent },
) {
    hourPrefixes.forEach { hourPrefix ->
        testSuite(hourPrefix) {
            (0..59).forEach { minute ->
                test(
                    minute.toString().padStart(2, '0'),
                ) {
                    @OptIn(ExperimentalStdlibApi::class)
                    val dispatcher = currentCoroutineContext()[CoroutineDispatcher]!!
                    val algorithm = HashLifeAlgorithm(
                        TestComposeLifeDispatchers(
                            generalTestDispatcher = dispatcher,
                            cellTickerTestDispatcher = dispatcher,
                        ),
                        generationsToCache = 64,
                    )

                    destructionIsCorrect(algorithm, hourPrefix, minute)
                }
            }
        }
    }
}

private const val TARGET_POPULATION = 200
private const val MAX_PHASE = 2
private const val MAX_GENERATIONS = 300
private const val CUSTOM_CODE_POINT_START = 0x4E00

private suspend fun destructionIsCorrect(
    algorithm: GameOfLifeAlgorithm,
    hourPrefix: String,
    minute: Int,
) {
    val timeDigits = createTimeDigits(hourPrefix, minute)

    val solutionCellStateFile =
        File(
            "src/jvmTest/resources/solutions/" +
                "${timeDigits.firstDigit.fileChar}" +
                "${timeDigits.secondDigit.fileChar}:" +
                "${timeDigits.thirdDigit.fileChar}" +
                "${timeDigits.fourthDigit.fileChar}.rle",
        )
    val solutionFontFile =
        File(
            "build/wff/minuteSfd/" +
                "${timeDigits.firstDigit.fileChar}" +
                "${timeDigits.secondDigit.fileChar}:" +
                "${timeDigits.thirdDigit.fileChar}" +
                "${timeDigits.fourthDigit.fileChar}.sfd",
        )

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
        val testCellState = createTimeCellState(timeDigits).union(createRandomGliders())
        val (generation, minimumSize) = isDestructionAchieved(
            algorithm = algorithm,
            timeDigits = timeDigits,
            cellState = testCellState,
            maxGenerations = MAX_GENERATIONS,
        )
        if (
            minimumSize <= TARGET_POPULATION &&
            isRepeatingAtEnd(
                algorithm = algorithm,
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
        createTimeCellState(timeDigits).aliveCells,
        solution.getAliveCellsInWindow(
            CellWindow(IntRect(IntOffset(0, 0), IntSize(70, 70))),
        ).toSet(),
    )
    val runLengthEncodingLines = RunLengthEncodedCellStateSerializer.serializeToString(solution)

    solutionFontFile.parentFile!!.mkdirs()
    solutionFontFile.bufferedWriter().use { bufferedWriter ->
        algorithm.computeGenerationsWithStep(solution, 1)
            .take(MAX_GENERATIONS)
            .withIndex()
            .collect { (index, cellState) ->
                bufferedWriter.write(
                    "StartChar: custom_" +
                        "${timeDigits.thirdDigit.char}_" +
                        "${timeDigits.fourthDigit.char}_" +
                        index.toString().padStart(3, '0').toCharArray().joinToString("_"),
                )
                bufferedWriter.newLine()

                bufferedWriter.write(
                    "Encoding: ${CUSTOM_CODE_POINT_START + 300 * minute + index} " +
                        "${CUSTOM_CODE_POINT_START + 300 * minute + index} " +
                        "${300 * minute + index}",
                )
                bufferedWriter.newLine()
                bufferedWriter.write("Width: 70")
                bufferedWriter.newLine()
                bufferedWriter.write("Flags: H")
                bufferedWriter.newLine()
                bufferedWriter.write("LayerCount: 2")
                bufferedWriter.newLine()
                bufferedWriter.write("Fore")
                bufferedWriter.newLine()
                bufferedWriter.write("SplineSet")
                bufferedWriter.newLine()
                createContours(
                    cellState.getAliveCellsInWindow(
                        CellWindow(IntRect(IntOffset(1, 1), IntSize(70, 70))),
                    ).toSet(),
                )
                    .map { contour ->
                        contour.map {
                            IntOffset(it.x, 70 - it.y)
                        }
                    }
                    .forEach { contour ->
                        bufferedWriter.write("${contour.last().x - 1} ${contour.last().y - 1} m 1")
                        bufferedWriter.newLine()
                        contour.forEach { corner ->
                            bufferedWriter.write(" ${corner.x - 1} ${corner.y - 1} l 1")
                            bufferedWriter.newLine()
                        }
                    }
                bufferedWriter.write("EndSplineSet")
                bufferedWriter.newLine()
                bufferedWriter.write("EndChar")
                bufferedWriter.newLine()
                bufferedWriter.newLine()
            }
    }

    solutionCellStateFile.parentFile!!.mkdirs()
    solutionCellStateFile.bufferedWriter().use { bufferedWriter ->
        runLengthEncodingLines.forEach { line ->
            bufferedWriter.write(line)
            bufferedWriter.newLine()
        }
    }
}

private suspend fun isDestructionAchieved(
    algorithm: GameOfLifeAlgorithm,
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
                CellWindow(IntRect(IntOffset(0, 0), IntSize(70, 70))),
            ).toSet()
            val aliveCellsInOriginalDigits = aliveCellsInViewport.intersect(timeCellState.aliveCells)
            aliveCellsInViewport.size + aliveCellsInOriginalDigits.size
        }
        .withIndex()
        .minBy { (_, value) -> value }
}

private suspend fun isRepeatingAtEnd(
    algorithm: GameOfLifeAlgorithm,
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
                CellWindow(IntRect(IntOffset(0, 0), IntSize(70, 70))),
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

private fun createContours(aliveCells: Set<IntOffset>): List<List<IntOffset>> {
    val connectedComponents = buildList {
        val remainingAliveCells = aliveCells.toMutableSet()
        while (remainingAliveCells.isNotEmpty()) {
            add(
                buildSet {
                    val searchQueue = ArrayDeque<IntOffset>()
                    val initialCell = remainingAliveCells.first()
                    remainingAliveCells.remove(initialCell)
                    searchQueue.add(initialCell)

                    while (searchQueue.isNotEmpty()) {
                        val cell = searchQueue.removeFirst()
                        add(cell)
                        cell.getVonNeumannNeighbors().forEach { orthogonalCell ->
                            if (orthogonalCell in remainingAliveCells) {
                                remainingAliveCells.remove(orthogonalCell)
                                searchQueue.add(orthogonalCell)
                            }
                        }
                    }
                },
            )
        }
    }

    return connectedComponents.flatMap { connectedComponent ->
        val edges = connectedComponent.flatMap { cell ->
            cell.getVonNeumannNeighbors()
                .filterNot(connectedComponent::contains)
                .map { Edge(cell, it) }
        }

        val edgeContours = buildList {
            val remainingEdges = edges.toMutableSet()
            while (remainingEdges.isNotEmpty()) {
                add(
                    buildList {
                        val initialEdge = remainingEdges.first()
                        remainingEdges.remove(initialEdge)
                        add(initialEdge)
                        var currentEdge = initialEdge
                        do {
                            val neighborEdge =
                                currentEdge.possibleClockwiseNeighbors(
                                    connectedComponent,
                                ).single(edges::contains)
                            checkNotNull(neighborEdge)
                            if (neighborEdge != initialEdge) {
                                remainingEdges.remove(neighborEdge)
                                add(neighborEdge)
                            }
                            currentEdge = neighborEdge
                        } while (currentEdge != initialEdge)
                    },
                )
            }
        }

        val outerEdge = edges
            .filter { it.normalDirection == Direction.Up }
            .minBy { it.insideCell.y }

        edgeContours.map { contour ->
            var isOuterEdge = false
            buildList {
                // Find initial corner
                var index = 0
                while (getCornerPointOnNeighboringEdgesOrNull(
                        contour[index],
                        contour[index + 1],
                        connectedComponent,
                    ) == null) {
                    index++
                }
                val initialCornerIndex = index
                do {
                    if (contour[index.mod(contour.size)] == outerEdge) {
                        isOuterEdge = true
                    }
                    val cornerPoint = getCornerPointOnNeighboringEdgesOrNull(
                        contour[index.mod(contour.size)],
                        contour[(index + 1).mod(contour.size)],
                        connectedComponent,
                    )
                    if (cornerPoint != null) {
                        add(cornerPoint)
                    }
                    index++
                } while (initialCornerIndex != index.mod(contour.size))
            }
                .let { if (isOuterEdge) it.reversed() else it }
        }
    }
}

private val GameOfLifeSegmentChar.fileChar get() =
    when (this) {
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
        GameOfLifeSegmentChar.Blank -> '_'
    }

private data class Edge(
    val insideCell: IntOffset,
    val outsideCell: IntOffset,
)

private val Edge.normalDirection: Direction get() =
    unitIntOffsetToDirection(outsideCell - insideCell)

private enum class Direction(
    val intOffset: IntOffset,
) {
    Left(
        IntOffset(-1, 0),
    ),
    Right(
        IntOffset(1, 0),
    ),
    Up(
        IntOffset(0, -1),
    ),
    Down(
        IntOffset(0, 1),
    ),
}

private operator fun IntOffset.plus(direction: Direction): IntOffset = this + direction.intOffset

private fun Edge.possibleClockwiseNeighbors(connectedComponent: Set<IntOffset>): List<Edge?> {
    return when (normalDirection) {
        Direction.Left -> listOf(
            if (insideCell + Direction.Up in connectedComponent) {
                Edge(
                    insideCell + Direction.Up + Direction.Left,
                    outsideCell,
                )
            } else {
                null
            },
            Edge(insideCell + Direction.Up, outsideCell + Direction.Up),
            Edge(insideCell, insideCell + Direction.Up),
        )
        Direction.Right -> listOf(
            if (insideCell + Direction.Down in connectedComponent) {
                Edge(
                    insideCell + Direction.Down + Direction.Right,
                    outsideCell,
                )
            } else {
                null
            },
            Edge(insideCell + Direction.Down, outsideCell + Direction.Down),
            Edge(insideCell, insideCell + Direction.Down),
        )
        Direction.Up -> listOf(
            if (insideCell + Direction.Right in connectedComponent) {
                Edge(
                    insideCell + Direction.Right + Direction.Up,
                    outsideCell,
                )
            } else {
                null
            },
            Edge(insideCell + Direction.Right, outsideCell + Direction.Right),
            Edge(insideCell, insideCell + Direction.Right),
        )
        Direction.Down -> listOf(
            if (insideCell + Direction.Left in connectedComponent) {
                Edge(
                    insideCell + Direction.Left + Direction.Down,
                    outsideCell,
                )
            } else {
                null
            },
            Edge(insideCell + Direction.Left, outsideCell + Direction.Left),
            Edge(insideCell, insideCell + Direction.Left),
        )
    }
}

private fun unitIntOffsetToDirection(intOffset: IntOffset): Direction =
    when (intOffset) {
        IntOffset(-1, 0) -> Direction.Left
        IntOffset(1, 0) -> Direction.Right
        IntOffset(0, -1) -> Direction.Up
        IntOffset(0, 1) -> Direction.Down
        else -> error("Unexpected non-unit length IntOffset")
    }

private fun getCornerPointOnNeighboringEdgesOrNull(
    a: Edge,
    b: Edge,
    connectedComponent: Set<IntOffset>,
): IntOffset? =
    when (a.possibleClockwiseNeighbors(connectedComponent).indexOf(b)) {
        0, 2 -> when (a.normalDirection) {
            Direction.Left -> a.insideCell
            Direction.Right -> a.insideCell + Direction.Right + Direction.Down
            Direction.Up -> a.insideCell + Direction.Right
            Direction.Down -> a.insideCell + Direction.Down
        }
        1 -> null
        else -> error("Edges were not neighbors")
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
        """,
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

fun createTimeDigits(hourPrefix: String, minute: Int): TimeDigits {
    val firstDigit = if (hourPrefix.first() == '_') {
        GameOfLifeSegmentChar.Blank
    } else {
        GameOfLifeSegmentChar.fromChar(hourPrefix.first().digitToInt())
    }
    val secondDigit = GameOfLifeSegmentChar.fromChar(hourPrefix[1].digitToInt())
    val thirdDigit = GameOfLifeSegmentChar.fromChar(minute / 10)
    val fourthDigit = GameOfLifeSegmentChar.fromChar(minute.rem(10))

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
