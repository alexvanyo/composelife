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

package com.alexvanyo.composelife.model

import kotlin.test.Test
import kotlin.test.assertEquals

class RunLengthEncodingCellStateSerializerTests {

    private val serializer = RunLengthEncodedCellStateSerializer

    @Test
    fun basic_deserialization_is_correct() {
        assertEquals(
            DeserializationResult.Successful(
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
                    4 to 4,
                ).toCellState(),
                format = CellStateFormat.FixedFormat.RunLengthEncoding,
            ),
            serializer.deserializeToCellState(
                """
                |x = 5, y = 5, rule = B3/S23
                |obobo2${'$'}obobo2${'$'}obobo!
                """.trimMargin().lineSequence(),
            ),
        )
    }

    @Test
    fun deserialization_with_comments_is_correct() {
        assertEquals(
            DeserializationResult.Successful(
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
                    4 to 4,
                ).toCellState(),
                format = CellStateFormat.FixedFormat.RunLengthEncoding,
            ),
            serializer.deserializeToCellState(
                """
                |#C This is a comment
                |x = 5, y = 5, rule = B3/S23
                |obobo2${'$'}obobo2${'$'}obobo!
                """.trimMargin().lineSequence(),
            ),
        )
    }

    @Test
    fun deserialization_with_top_left_offset_with_R_is_correct() {
        assertEquals(
            DeserializationResult.Successful(
                warnings = emptyList(),
                cellState = setOf(
                    -3 to 7,
                    -1 to 7,
                    1 to 7,
                    -3 to 9,
                    -1 to 9,
                    1 to 9,
                    -3 to 11,
                    -1 to 11,
                    1 to 11,
                ).toCellState(),
                format = CellStateFormat.FixedFormat.RunLengthEncoding,
            ),
            serializer.deserializeToCellState(
                """
                |#R -3 7
                |x = 5, y = 5, rule = B3/S23
                |obobo2${'$'}obobo2${'$'}obobo!
                """.trimMargin().lineSequence(),
            ),
        )
    }

    @Test
    fun deserialization_with_top_left_offset_with_P_is_correct() {
        assertEquals(
            DeserializationResult.Successful(
                warnings = emptyList(),
                cellState = setOf(
                    -3 to 7,
                    -1 to 7,
                    1 to 7,
                    -3 to 9,
                    -1 to 9,
                    1 to 9,
                    -3 to 11,
                    -1 to 11,
                    1 to 11,
                ).toCellState(),
                format = CellStateFormat.FixedFormat.RunLengthEncoding,
            ),
            serializer.deserializeToCellState(
                """
                |#P -3 7
                |x = 5, y = 5, rule = B3/S23
                |obobo2${'$'}obobo2${'$'}obobo!
                """.trimMargin().lineSequence(),
            ),
        )
    }

    @Test
    fun basic_serialization_is_correct() {
        assertEquals(
            """
            |#R 0 0
            |x = 5, y = 5, rule = B3/S23
            |obobo2${'$'}obobo2${'$'}obobo!
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
                    4 to 4,
                ).toCellState(),
            ).joinToString("\n"),
        )
    }

    @Test
    fun gosper_glider_gun_serialization_is_correct() {
        assertEquals(
            """
            |#R 0 0
            |x = 36, y = 9, rule = B3/S23
            |24bo${'$'}22bobo${'$'}12b2o6b2o12b2o${'$'}11bo3bo4b2o12b2o${'$'}2o8bo5bo3b2o${'$'}2o8bo3bob2o4b
            |obo${'$'}10bo5bo7bo${'$'}11bo3bo${'$'}12b2o!
            """.trimMargin(),
            serializer.serializeToString(
                """
                |........................O...........
                |......................O.O...........
                |............OO......OO............OO
                |...........O...O....OO............OO
                |OO........O.....O...OO..............
                |OO........O...O.OO....O.O...........
                |..........O.....O.......O...........
                |...........O...O....................
                |............OO......................
                """.toCellState(),
            ).joinToString("\n"),
        )
    }

    @Test
    fun slow_puffer_serialization_is_correct() {
        assertEquals(
            """
            |#R 0 0
            |x = 82, y = 73, rule = B3/S23
            |76b2o${'$'}75b2ob4o${'$'}76b6o${'$'}77b4o${'$'}64b3o${'$'}63b5o${'$'}62b2ob3o${'$'}52b2o9b2o${'$'}51b2ob4o${'$'}52b
            |6o${'$'}53b4o3${'$'}44b2o${'$'}43b2ob2o26b2o${'$'}44b4o24bo4bo${'$'}45b2o24bo${'$'}24b6o41bo5bo${'$'}24bo
            |5bo40b6o${'$'}24bo${'$'}25bo4bo${'$'}27b2o2${'$'}54b4o${'$'}53b6o${'$'}52b2ob4o${'$'}3bo49b2o${'$'}bo3bo${'$'}o${'$'}o4b
            |o${'$'}5o3${'$'}20bo${'$'}b2o10b2obo2bobo${'$'}2ob3o6bobob4obo${'$'}b4o3b3obo${'$'}2b2o8bobob4obo${'$'}
            |13b2obo2bobo${'$'}5b2o13bo${'$'}3bo4bo${'$'}2bo${'$'}2bo5bo${'$'}2b6o3${'$'}53b2o${'$'}52b2ob4o${'$'}53b6o${'$'}54b
            |4o2${'$'}27b2o${'$'}25bo4bo${'$'}24bo${'$'}24bo5bo40b6o${'$'}24b6o41bo5bo${'$'}45b2o24bo${'$'}44b4o24bo4b
            |o${'$'}43b2ob2o26b2o${'$'}44b2o3${'$'}53b4o${'$'}52b6o${'$'}51b2ob4o${'$'}52b2o9b2o${'$'}62b2ob3o${'$'}63b5o${'$'}
            |64b3o${'$'}77b4o${'$'}76b6o${'$'}75b2ob4o${'$'}76b2o!
            """.trimMargin(),
            serializer.serializeToString(
                """
                |............................................................................OO....
                |...........................................................................OO.OOOO
                |............................................................................OOOOOO
                |.............................................................................OOOO.
                |................................................................OOO...............
                |...............................................................OOOOO..............
                |..............................................................OO.OOO..............
                |....................................................OO.........OO.................
                |...................................................OO.OOOO........................
                |....................................................OOOOOO........................
                |.....................................................OOOO.........................
                |..................................................................................
                |..................................................................................
                |............................................OO....................................
                |...........................................OO.OO..........................OO......
                |............................................OOOO........................O....O....
                |.............................................OO........................O..........
                |........................OOOOOO.........................................O.....O....
                |........................O.....O........................................OOOOOO.....
                |........................O.........................................................
                |.........................O....O...................................................
                |...........................OO.....................................................
                |..................................................................................
                |......................................................OOOO........................
                |.....................................................OOOOOO.......................
                |....................................................OO.OOOO.......................
                |...O.................................................OO...........................
                |.O...O............................................................................
                |O.................................................................................
                |O....O............................................................................
                |OOOOO.............................................................................
                |..................................................................................
                |..................................................................................
                |....................O.............................................................
                |.OO..........OO.O..O.O............................................................
                |OO.OOO......O.O.OOOO.O............................................................
                |.OOOO...OOO.O.....................................................................
                |..OO........O.O.OOOO.O............................................................
                |.............OO.O..O.O............................................................
                |.....OO.............O.............................................................
                |...O....O.........................................................................
                |..O...............................................................................
                |..O.....O.........................................................................
                |..OOOOOO..........................................................................
                |..................................................................................
                |..................................................................................
                |.....................................................OO...........................
                |....................................................OO.OOOO.......................
                |.....................................................OOOOOO.......................
                |......................................................OOOO........................
                |..................................................................................
                |...........................OO.....................................................
                |.........................O....O...................................................
                |........................O.........................................................
                |........................O.....O........................................OOOOOO.....
                |........................OOOOOO.........................................O.....O....
                |.............................................OO........................O..........
                |............................................OOOO........................O....O....
                |...........................................OO.OO..........................OO......
                |............................................OO....................................
                |..................................................................................
                |..................................................................................
                |.....................................................OOOO.........................
                |....................................................OOOOOO........................
                |...................................................OO.OOOO........................
                |....................................................OO.........OO.................
                |..............................................................OO.OOO..............
                |...............................................................OOOOO..............
                |................................................................OOO...............
                |.............................................................................OOOO.
                |............................................................................OOOOOO
                |...........................................................................OO.OOOO
                |............................................................................OO....
                """.toCellState(),
            ).joinToString("\n"),
        )
    }

    @Test
    fun slow_puffer_deserialization_is_correct() {
        assertEquals(
            DeserializationResult.Successful(
                warnings = emptyList(),
                cellState = """
                |............................................................................OO....
                |...........................................................................OO.OOOO
                |............................................................................OOOOOO
                |.............................................................................OOOO.
                |................................................................OOO...............
                |...............................................................OOOOO..............
                |..............................................................OO.OOO..............
                |....................................................OO.........OO.................
                |...................................................OO.OOOO........................
                |....................................................OOOOOO........................
                |.....................................................OOOO.........................
                |..................................................................................
                |..................................................................................
                |............................................OO....................................
                |...........................................OO.OO..........................OO......
                |............................................OOOO........................O....O....
                |.............................................OO........................O..........
                |........................OOOOOO.........................................O.....O....
                |........................O.....O........................................OOOOOO.....
                |........................O.........................................................
                |.........................O....O...................................................
                |...........................OO.....................................................
                |..................................................................................
                |......................................................OOOO........................
                |.....................................................OOOOOO.......................
                |....................................................OO.OOOO.......................
                |...O.................................................OO...........................
                |.O...O............................................................................
                |O.................................................................................
                |O....O............................................................................
                |OOOOO.............................................................................
                |..................................................................................
                |..................................................................................
                |....................O.............................................................
                |.OO..........OO.O..O.O............................................................
                |OO.OOO......O.O.OOOO.O............................................................
                |.OOOO...OOO.O.....................................................................
                |..OO........O.O.OOOO.O............................................................
                |.............OO.O..O.O............................................................
                |.....OO.............O.............................................................
                |...O....O.........................................................................
                |..O...............................................................................
                |..O.....O.........................................................................
                |..OOOOOO..........................................................................
                |..................................................................................
                |..................................................................................
                |.....................................................OO...........................
                |....................................................OO.OOOO.......................
                |.....................................................OOOOOO.......................
                |......................................................OOOO........................
                |..................................................................................
                |...........................OO.....................................................
                |.........................O....O...................................................
                |........................O.........................................................
                |........................O.....O........................................OOOOOO.....
                |........................OOOOOO.........................................O.....O....
                |.............................................OO........................O..........
                |............................................OOOO........................O....O....
                |...........................................OO.OO..........................OO......
                |............................................OO....................................
                |..................................................................................
                |..................................................................................
                |.....................................................OOOO.........................
                |....................................................OOOOOO........................
                |...................................................OO.OOOO........................
                |....................................................OO.........OO.................
                |..............................................................OO.OOO..............
                |...............................................................OOOOO..............
                |................................................................OOO...............
                |.............................................................................OOOO.
                |............................................................................OOOOOO
                |...........................................................................OO.OOOO
                |............................................................................OO....
                """.toCellState(),
                format = CellStateFormat.FixedFormat.RunLengthEncoding,
            ),
            serializer.deserializeToCellState(
                """
                |#R 0 0
                |x = 82, y = 73, rule = 23/3
                |76b2o4b${'$'}75b2ob4o${'$'}76b6o${'$'}77b4ob${'$'}64b3o15b${'$'}63b5o14b${'$'}62b2ob3o14b${'$'}52b2o9b2o
                |17b${'$'}51b2ob4o24b${'$'}52b6o24b${'$'}53b4o25b3${'$'}44b2o36b${'$'}43b2ob2o26b2o6b${'$'}44b4o24bo
                |4bo4b${'$'}45b2o24bo10b${'$'}24b6o41bo5bo4b${'$'}24bo5bo40b6o5b${'$'}24bo57b${'$'}25bo4bo51b${'$'}
                |27b2o53b2${'$'}54b4o24b${'$'}53b6o23b${'$'}52b2ob4o23b${'$'}3bo49b2o27b${'$'}bo3bo76b${'$'}o81b${'$'}o4bo
                |76b${'$'}5o77b3${'$'}20bo61b${'$'}b2o10b2obo2bobo60b${'$'}2ob3o6bobob4obo60b${'$'}b4o3b3obo69b${'$'}
                |2b2o8bobob4obo60b${'$'}13b2obo2bobo60b${'$'}5b2o13bo61b${'$'}3bo4bo73b${'$'}2bo79b${'$'}2bo5bo
                |73b${'$'}2b6o74b3${'$'}53b2o27b${'$'}52b2ob4o23b${'$'}53b6o23b${'$'}54b4o24b2${'$'}27b2o53b${'$'}25bo4bo
                |51b${'$'}24bo57b${'$'}24bo5bo40b6o5b${'$'}24b6o41bo5bo4b${'$'}45b2o24bo10b${'$'}44b4o24bo4bo4b${'$'}
                |43b2ob2o26b2o6b${'$'}44b2o36b3${'$'}53b4o25b${'$'}52b6o24b${'$'}51b2ob4o24b${'$'}52b2o9b2o17b${'$'}
                |62b2ob3o14b${'$'}63b5o14b${'$'}64b3o15b${'$'}77b4ob${'$'}76b6o${'$'}75b2ob4o${'$'}76b2o!
                """.trimMargin().lineSequence(),
            ),
        )
    }
}
