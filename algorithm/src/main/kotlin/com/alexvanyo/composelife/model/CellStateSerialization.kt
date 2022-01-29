package com.alexvanyo.composelife.model

import androidx.compose.ui.unit.IntOffset
import com.alexvanyo.composelife.algorithm.R
import com.alexvanyo.composelife.model.CellStateSerializer.DeserializationResult
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import com.livefront.sealedenum.GenSealedEnum

interface CellStateSerializer {
    fun deserializeToCellState(lines: Sequence<String>): DeserializationResult

    fun serializeToString(cellState: CellState): Sequence<String>

    sealed interface DeserializationResult {
        val warnings: List<ParameterizedString>

        data class Successful(
            override val warnings: List<ParameterizedString>,
            val cellState: CellState,
        ) : DeserializationResult

        data class Unsuccessful(
            override val warnings: List<ParameterizedString>,
            val errors: List<ParameterizedString>,
        ) : DeserializationResult
    }
}

sealed interface CellStateFormat {

    sealed interface FixedFormat {
        object Plaintext : CellStateFormat

        @GenSealedEnum(generateEnum = true)
        companion object
    }

    @GenSealedEnum(generateEnum = true)
    companion object
}

class PlaintextCellStateSerializer : CellStateSerializer {

    @Suppress("LongMethod")
    override fun deserializeToCellState(lines: Sequence<String>): DeserializationResult {
        val warnings = mutableListOf<ParameterizedString>()
        val points = mutableSetOf<IntOffset>()

        var expectedRowLength: Int? = null
        var longestRowIndex: Int? = null

        var lineIndex = 0
        var rowIndex = 0

        val iterator = lines.iterator()

        while (iterator.hasNext()) {
            val line = iterator.next()

            when (line.firstOrNull()) {
                '!' -> {
                    // Comment line, continue
                }
                null -> {
                    if (iterator.hasNext()) {
                        warnings.add(ParameterizedString(R.string.unexpected_blank_line, lineIndex + 1))
                    }
                }
                else -> {
                    if (expectedRowLength == null) {
                        expectedRowLength = line.length
                        longestRowIndex = rowIndex
                    } else if (line.length > expectedRowLength) {
                        warnings.add(ParameterizedString(R.string.unexpected_short_line, longestRowIndex!! + 1))
                        expectedRowLength = line.length
                        longestRowIndex = rowIndex
                    }

                    points.addAll(
                        line.withIndex()
                            .filter { (columnIndex, c) ->
                                when (c) {
                                    '.' -> false
                                    'O' -> true
                                    else -> {
                                        warnings.add(
                                            ParameterizedString(
                                                R.string.unexpected_character,
                                                lineIndex + 1,
                                                columnIndex + 1
                                            )
                                        )
                                        when (c) {
                                            ' ' -> false
                                            else -> true
                                        }
                                    }
                                }
                            }
                            .map { (columnIndex, _) -> IntOffset(columnIndex, rowIndex) }
                    )

                    rowIndex++
                }
            }

            lineIndex++
        }

        return DeserializationResult.Successful(
            warnings = warnings,
            cellState = CellState(points)
        )
    }

    override fun serializeToString(cellState: CellState): Sequence<String> {
        val minX = cellState.aliveCells.map { it.x }.minOrNull() ?: 0
        val maxX = cellState.aliveCells.map { it.x }.maxOrNull() ?: 0
        val minY = cellState.aliveCells.map { it.y }.minOrNull() ?: 0
        val maxY = cellState.aliveCells.map { it.y }.maxOrNull() ?: 0

        return sequence {
            (minY..maxY).forEach { y ->
                val line = buildString {
                    (minX..maxX).forEach { x ->
                        append(
                            if (IntOffset(x, y) in cellState.aliveCells) {
                                'O'
                            } else {
                                '.'
                            }
                        )
                    }
                }
                yield("$line\n")
            }
        }
    }
}
