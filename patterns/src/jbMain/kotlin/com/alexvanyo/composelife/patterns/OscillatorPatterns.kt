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

import androidx.compose.ui.unit.IntRect
import com.alexvanyo.composelife.model.CellState
import com.alexvanyo.composelife.model.CellWindow
import com.alexvanyo.composelife.model.toCellState
import com.livefront.sealedenum.GenSealedEnum

sealed class OscillatorPattern(
    patternName: String,
    seedCellState: CellState,
    internal val otherCellStates: List<CellState>,
    val boundingBox: CellWindow,
) : GameOfLifeTestPattern(
    patternName = patternName,
    seedCellState = seedCellState,
    cellStates = List(oscillatorTestGenerations) {
        val repeatingCellStates = otherCellStates + seedCellState
        repeatingCellStates[it.mod(repeatingCellStates.size)]
    },
) {
    /**
     * The period of the oscillating pattern.
     */
    val period = otherCellStates.size + 1

    @GenSealedEnum(generateEnum = true)
    companion object {
        const val oscillatorTestGenerations = 50
    }
}

data object BlinkerPattern : OscillatorPattern(
    patternName = "Blinker",
    """
    |...
    |OOO
    |...
    """.toCellState(),
    listOf(
        """
        |.O.
        |.O.
        |.O.
        """.toCellState(),
    ),
    CellWindow(
        IntRect(
            left = 0,
            top = 0,
            right = 3,
            bottom = 3,
        ),
    ),
)

data object ToadPattern : OscillatorPattern(
    patternName = "Toad",
    """
    |.OO.
    |O...
    |...O
    |.OO.
    """.toCellState(),
    listOf(
        """
        |.O..
        |.OO.
        |.OO.
        |..O.
        """.toCellState(),
    ),
    CellWindow(
        IntRect(
            left = 0,
            top = 0,
            right = 4,
            bottom = 4,
        ),
    ),
)

data object BeaconPattern : OscillatorPattern(
    patternName = "Beacon",
    """
    |OO..
    |O...
    |...O
    |..OO
    """.toCellState(),
    listOf(
        """
        |OO..
        |OO..
        |..OO
        |..OO
        """.toCellState(),
    ),
    CellWindow(
        IntRect(
            left = 0,
            top = 0,
            right = 4,
            bottom = 4,
        ),
    ),
)

data object PulsarPattern : OscillatorPattern(
    patternName = "Pulsar",
    """
    |...............
    |...OOO...OOO...
    |...............
    |.O....O.O....O.
    |.O....O.O....O.
    |.O....O.O....O.
    |...OOO...OOO...
    |...............
    |...OOO...OOO...
    |.O....O.O....O.
    |.O....O.O....O.
    |.O....O.O....O.
    |...............
    |...OOO...OOO...
    |...............
    """.toCellState(),
    listOf(
        """
        |....O.....O....
        |....O.....O....
        |....OO...OO....
        |...............
        |OOO..OO.OO..OOO
        |..O.O.O.O.O.O..
        |....OO...OO....
        |...............
        |....OO...OO....
        |..O.O.O.O.O.O..
        |OOO..OO.OO..OOO
        |...............
        |....OO...OO....
        |....O.....O....
        |....O.....O....
        """.toCellState(),
        """
        |...............
        |...OO.....OO...
        |....OO...OO....
        |.O..O.O.O.O..O.
        |.OOO.OO.OO.OOO.
        |..O.O.O.O.O.O..
        |...OOO...OOO...
        |...............
        |...OOO...OOO...
        |..O.O.O.O.O.O..
        |.OOO.OO.OO.OOO.
        |.O..O.O.O.O..O.
        |....OO...OO....
        |...OO.....OO...
        |...............
        """.toCellState(),
    ),
    CellWindow(
        IntRect(
            left = 0,
            top = 0,
            right = 15,
            bottom = 15,
        ),
    ),
)
