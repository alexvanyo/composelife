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
    cellStates = List(stillLifeTestGenerations) { cellState }
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
