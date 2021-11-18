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
    seedCellState = setOf(
        1 to 1,
        1 to 2,
        2 to 1,
        2 to 2
    ).toCellState(),
    cellStates = List(50) {
        setOf(
            1 to 1,
            1 to 2,
            2 to 1,
            2 to 2
        ).toCellState()
    }
)

object BeeHivePattern : GameOfLifeTestPattern(
    patternName = "Bee-hive",
    seedCellState = setOf(
        -1 to -1,
        0 to -2,
        1 to -2,
        2 to -1,
        0 to 0,
        1 to 0
    ).toCellState(),
    cellStates = List(50) {
        setOf(
            -1 to -1,
            0 to -2,
            1 to -2,
            2 to -1,
            0 to 0,
            1 to 0
        ).toCellState()
    }
)
