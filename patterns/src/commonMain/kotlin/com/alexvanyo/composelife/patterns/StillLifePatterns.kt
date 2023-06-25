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

import com.alexvanyo.composelife.model.CellState
import com.alexvanyo.composelife.model.emptyCellState
import com.alexvanyo.composelife.model.toCellState

sealed class StillLifePattern(
    patternName: String,
    cellState: CellState,
) : GameOfLifeTestPattern(
    patternName = patternName,
    seedCellState = cellState,
    cellStates = List(stillLifeTestGenerations) { cellState },
) {
    companion object {
        const val stillLifeTestGenerations = 50
    }
}

object EmptyPattern : StillLifePattern(
    patternName = "Empty",
    cellState = emptyCellState(),
)

object BlockPattern : StillLifePattern(
    patternName = "Block",
    """
    |OO
    |OO
    """.toCellState(),
)

object TubPattern : StillLifePattern(
    patternName = "Tub",
    """
    |.O.
    |O.O
    |.O.
    """.toCellState(),
)

object BeeHivePattern : StillLifePattern(
    patternName = "Bee-hive",
    """
    |.OO.
    |O..O
    |.OO.
    """.toCellState(),
)

object PondPattern : StillLifePattern(
    patternName = "Pond",
    """
    |.OO.
    |O..O
    |O..O
    |.OO.
    """.toCellState(),
)

object HatPattern : StillLifePattern(
    patternName = "Hat",
    """
    |..O..
    |.O.O.
    |.O.O.
    |OO.OO
    """.toCellState(),
)

object HoneycombPattern : StillLifePattern(
    patternName = "Honeycomb",
    """
    |..OO..
    |.O..O.
    |O.OO.O
    |.O..O.
    |..OO..
    """.toCellState(),
)
