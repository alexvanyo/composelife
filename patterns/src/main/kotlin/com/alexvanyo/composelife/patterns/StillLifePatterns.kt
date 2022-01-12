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
    |XX
    |XX
    """.toCellState(),
)

object TubPattern : StillLifePattern(
    patternName = "Tub",
    """
    | X
    |X X
    | X
    """.toCellState(),
)

object BeeHivePattern : StillLifePattern(
    patternName = "Bee-hive",
    """
    | XX
    |X  X
    | XX
    """.toCellState(),
)

object PondPattern : StillLifePattern(
    patternName = "Pond",
    """
    | XX
    |X  X
    |X  X
    | XX
    """.toCellState(),
)
