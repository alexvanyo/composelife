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

import androidx.compose.ui.unit.IntOffset
import com.alexvanyo.composelife.model.CellState
import com.alexvanyo.composelife.model.toCellState

sealed class SpaceshipPatterns(
    patternName: String,
    seedCellState: CellState,
    otherCellStates: List<CellState>,
    offset: IntOffset,
) : GameOfLifeTestPattern(
    patternName = patternName,
    seedCellState = seedCellState,
    cellStates = List(spaceshipTestGenerations) {
        val repeatingCellStates = otherCellStates + seedCellState
        repeatingCellStates[it.mod(repeatingCellStates.size)]
            .offsetBy(offset * ((it + 1) / repeatingCellStates.size).toFloat())
    },
) {
    companion object {
        const val spaceshipTestGenerations = 100
    }
}

object GliderPattern : SpaceshipPatterns(
    patternName = "Glider",
    """
    |..O.
    |O.O.
    |.OO.
    |....
    """.toCellState(),
    listOf(
        """
        |.O..
        |..OO
        |.OO.
        |....
        """.toCellState(),
        """
        |..O..
        |...O.
        |.OOO.
        |.....
        """.toCellState(),
        """
        |....
        |.O.O
        |..OO
        |..O.
        """.toCellState(),
    ),
    offset = IntOffset(1, 1),
)

object LightweightSpaceshipPattern : SpaceshipPatterns(
    patternName = "Lightweight Spaceship",
    """
    |...O..O
    |..O....
    |..O...O
    |..OOOO.
    |.......
    """.toCellState(),
    listOf(
        """
        |.......
        |..OO...
        |.OO.OO.
        |..OOOO.
        |...OO..
        """.toCellState(),
        """
        |.......
        |.OOOO..
        |.O...O.
        |.O.....
        |..O..O.
        """.toCellState(),
        """
        |..OO...
        |.OOOO..
        |OO.OO..
        |.OO....
        |.......
        """.toCellState(),
    ),
    offset = IntOffset(-2, 0),
)
