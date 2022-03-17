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

import com.alexvanyo.composelife.model.emptyCellState
import com.alexvanyo.composelife.model.toCellState

object SingleCellPattern : GameOfLifeTestPattern(
    patternName = "Single cell",
    """
    |O
    """.toCellState(),
    List(50) { emptyCellState() }
)

object SixLongLinePattern : GameOfLifeTestPattern(
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
        """.toCellState()
    ) + List(50) { emptyCellState() }
)
