package com.alexvanyo.composelife.data

import com.alexvanyo.composelife.data.model.emptyCellState
import com.alexvanyo.composelife.data.model.toCellState

object EmptyPattern : GameOfLifeTestPattern(
    patternName = "Empty",
    seedCellState = emptyCellState(),
    cellStates = List(50) { emptyCellState() }
)

object BlockPattern : GameOfLifeTestPattern(
    patternName = "Block",
    """
    |XX
    |XX
    """.toCellState(),
    List(50) {
        """
        |XX
        |XX
        """.toCellState()
    }
)

object BeeHivePattern : GameOfLifeTestPattern(
    patternName = "Bee-hive",
    """
    | XX
    |X  X
    | XX
    """.toCellState(),
    List(50) {
        """
        | XX
        |X  X
        | XX
        """.toCellState()
    }
)
