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

package com.alexvanyo.composelife.patterns

import com.alexvanyo.composelife.model.RunLengthEncodedCellStateSerializer
import com.alexvanyo.composelife.model.emptyCellState
import com.alexvanyo.composelife.model.toCellState

data object SingleCellPattern : GameOfLifeTestPattern(
    patternName = "Single cell",
    """
    |O
    """.toCellState(),
    List(50) { emptyCellState() },
)

data object SixLongLinePattern : GameOfLifeTestPattern(
    patternName = "Six long line",
    """
    |........
    |........
    |..OOOOOO
    |........
    |........
    """.toCellState(),
    listOf(
        """
        |.......
        |...OOOO
        |...OOOO
        |...OOOO
        |.......
        """.toCellState(),
        """
        |....OO..
        |...O..O.
        |..O....O
        |...O..O.
        |....OO..
        """.toCellState(),
        """
        |....OO..
        |...OOOO.
        |..OO..OO
        |...OOOO.
        |....OO..
        """.toCellState(),
        """
        |...O..O.
        |..O....O
        |..O....O
        |..O....O
        |...O..O.
        """.toCellState(),
        """
        |.........
        |..OO..OO.
        |.OOO..OOO
        |..OO..OO.
        |.........
        """.toCellState(),
        """
        |.........
        |.O.O..O.O
        |.O..OO..O
        |.O.O..O.O
        |.........
        """.toCellState(),
        """
        |..........
        |..O.OO.O..
        |OO.OOOO.OO
        |..O.OO.O..
        |..........
        """.toCellState(),
        """
        |.........
        |.OO....OO
        |.O......O
        |.OO....OO
        |.........
        """.toCellState(),
        """
        |..........
        |.OO....OO.
        |O........O
        |.OO....OO.
        |..........
        """.toCellState(),
        """
        |..........
        |.O......O.
        |O........O
        |.O......O.
        |..........
        """.toCellState(),
        """
        |..........
        |..........
        |OO......OO
        |..........
        |..........
        """.toCellState(),
    ) + List(50) { emptyCellState() },
)

data object GosperGliderGunPattern : GameOfLifeTestPattern(
    patternName = "Gosper glider gun",
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
    listOf(
        """
        x = 36, y = 9, rule = B3/S23
        23bo${'$'}21bobo${'$'}12bo7bobo11b2o${'$'}11b2o6bo2bo11b2o${'$'}2o8b2o4b2o2bobo${'$'}2o7b3o4b2o
        3bobo${'$'}10b2o4b2o5bo${'$'}11b2o${'$'}12bo!
        """.trimIndent().toCellState(fixedFormatCellStateSerializer = RunLengthEncodedCellStateSerializer),
        """
        x = 36, y = 9, rule = B3/S23
        22bo${'$'}21bobo${'$'}11b2o7bob2o10b2o${'$'}10bobo6b2ob2o10b2o${'$'}2o7bo6b3obob2o${'$'}2o7bo2b
        o2bo2bo2bobo${'$'}9bo6b2o4bo${'$'}10bobo${'$'}11b2o!
        """.trimIndent().toCellState(fixedFormatCellStateSerializer = RunLengthEncodedCellStateSerializer),
    ),
)
