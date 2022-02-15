package com.alexvanyo.composelife.model

import com.alexvanyo.composelife.algorithm.R
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test

class PlaintextCellStateSerializerTests {

    private val serializer = PlaintextCellStateSerializer()

    @Test
    fun `basic deserialization is correct`() {
        assertEquals(
            CellStateSerializer.DeserializationResult.Successful(
                warnings = emptyList(),
                cellState = setOf(
                    0 to 0,
                    2 to 0,
                    4 to 0,
                    0 to 2,
                    2 to 2,
                    4 to 2,
                    0 to 4,
                    2 to 4,
                    4 to 4
                ).toCellState(),
            ),
            serializer.deserializeToCellState(
                """
                |O.O.O.
                |......
                |O.O.O.
                |......
                |O.O.O.
                |......
                |
                """.trimMargin().lineSequence()
            )
        )
    }

    @Test
    fun `deserialization with comments is correct`() {
        assertEquals(
            CellStateSerializer.DeserializationResult.Successful(
                warnings = emptyList(),
                cellState = setOf(
                    0 to 0,
                    2 to 0,
                    4 to 0,
                    0 to 2,
                    2 to 2,
                    4 to 2,
                    0 to 4,
                    2 to 4,
                    4 to 4
                ).toCellState(),
            ),
            serializer.deserializeToCellState(
                """
                |! comment 1
                |! comment 2
                |O.O.O.
                |......
                |! comment 3
                |O.O.O.
                |......
                |O.O.O.
                |......
                |! comment 4
                |
                """.trimMargin().lineSequence()
            )
        )
    }

    @Test
    fun `deserialization with comments and warnings is correct`() {
        assertEquals(
            CellStateSerializer.DeserializationResult.Successful(
                warnings = listOf(
                    ParameterizedString(R.string.unexpected_blank_line, 3),
                    ParameterizedString(R.string.unexpected_character, '0', 4, 1),
                    ParameterizedString(R.string.unexpected_character, '0', 4, 3),
                    ParameterizedString(R.string.unexpected_character, '0', 4, 5),
                    ParameterizedString(R.string.unexpected_short_line, 4),
                    ParameterizedString(R.string.unexpected_character, '0', 7, 1),
                    ParameterizedString(R.string.unexpected_character, '0', 7, 3),
                    ParameterizedString(R.string.unexpected_character, '0', 7, 5),
                    ParameterizedString(R.string.unexpected_short_line, 9),
                    ParameterizedString(R.string.unexpected_character, '0', 9, 1),
                    ParameterizedString(R.string.unexpected_character, ' ', 9, 2),
                    ParameterizedString(R.string.unexpected_character, '0', 9, 3),
                    ParameterizedString(R.string.unexpected_character, ' ', 9, 4),
                    ParameterizedString(R.string.unexpected_character, '0', 9, 5),
                ),
                cellState = setOf(
                    0 to 0,
                    2 to 0,
                    4 to 0,
                    0 to 2,
                    2 to 2,
                    4 to 2,
                    0 to 4,
                    2 to 4,
                    4 to 4
                ).toCellState(),
            ),
            serializer.deserializeToCellState(
                """
                |! comment 1
                |! comment 2
                |
                |0.0.0
                |......
                |! comment 3
                |0.0.0.
                |......
                |0 0 0
                |......
                |! comment 4
                |
                """.trimMargin().lineSequence()
            )
        )
    }

    @Test
    fun `basic serialization is correct`() {
        assertEquals(
            """
            |O.O.O
            |.....
            |O.O.O
            |.....
            |O.O.O
            |
            """.trimMargin(),
            serializer.serializeToString(
                setOf(
                    0 to 0,
                    2 to 0,
                    4 to 0,
                    0 to 2,
                    2 to 2,
                    4 to 2,
                    0 to 4,
                    2 to 4,
                    4 to 4
                ).toCellState()
            ).joinToString("")
        )
    }
}
