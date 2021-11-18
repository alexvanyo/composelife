package com.alexvanyo.composelife.data

import com.alexvanyo.composelife.data.model.emptyCellState
import com.alexvanyo.composelife.data.model.toCellState

object SingleCellPattern : GameOfLifeTestPattern(
    patternName = "Single cell",
    seedCellState = setOf(1 to 1).toCellState(),
    cellStates = List(50) { emptyCellState() }
)

object SixLongLinePattern : GameOfLifeTestPattern(
    patternName = "Six long line",
    seedCellState = setOf(
        0 to 0,
        0 to 1,
        0 to 2,
        0 to 3,
        0 to 4,
        0 to 5,
    ).toCellState(),
    cellStates = listOf(
        setOf(
            -1 to 1,
            0 to 1,
            1 to 1,
            -1 to 2,
            0 to 2,
            1 to 2,
            -1 to 3,
            0 to 3,
            1 to 3,
            -1 to 4,
            0 to 4,
            1 to 4
        ).toCellState(),
        setOf(
            0 to 0,
            -1 to 1,
            1 to 1,
            -2 to 2,
            2 to 2,
            -2 to 3,
            2 to 3,
            -1 to 4,
            1 to 4,
            0 to 5
        ).toCellState(),
        setOf(
            0 to 0,
            -1 to 1,
            0 to 1,
            1 to 1,
            -2 to 2,
            -1 to 2,
            1 to 2,
            2 to 2,
            -2 to 3,
            -1 to 3,
            1 to 3,
            2 to 3,
            -1 to 4,
            0 to 4,
            1 to 4,
            0 to 5
        ).toCellState(),
        setOf(
            -1 to 0,
            0 to 0,
            1 to 0,
            -2 to 1,
            2 to 1,
            -2 to 4,
            2 to 4,
            -1 to 5,
            0 to 5,
            1 to 5
        ).toCellState(),
        setOf(
            0 to -1,
            -1 to 0,
            0 to 0,
            1 to 0,
            -1 to 1,
            0 to 1,
            1 to 1,
            -1 to 4,
            0 to 4,
            1 to 4,
            -1 to 5,
            0 to 5,
            1 to 5,
            0 to 6
        ).toCellState(),
        setOf(
            -1 to -1,
            0 to -1,
            1 to -1,
            -1 to 1,
            1 to 1,
            0 to 2,
            0 to 3,
            -1 to 4,
            1 to 4,
            -1 to 6,
            0 to 6,
            1 to 6
        ).toCellState(),
        setOf(
            0 to -2,
            0 to -1,
            -1 to 0,
            1 to 0,
            0 to 1,
            -1 to 2,
            0 to 2,
            1 to 2,
            -1 to 3,
            0 to 3,
            1 to 3,
            0 to 4,
            -1 to 5,
            1 to 5,
            0 to 6,
            0 to 7
        ).toCellState(),
        setOf(
            -1 to -1,
            0 to -1,
            1 to -1,
            -1 to 0,
            1 to 0,
            -1 to 5,
            1 to 5,
            -1 to 6,
            0 to 6,
            1 to 6
        ).toCellState(),
        setOf(
            0 to -2,
            -1 to -1,
            1 to -1,
            -1 to 0,
            1 to 0,
            -1 to 5,
            1 to 5,
            -1 to 6,
            1 to 6,
            0 to 7
        ).toCellState(),
        setOf(
            0 to -2,
            -1 to -1,
            1 to -1,
            -1 to 6,
            1 to 6,
            0 to 7
        ).toCellState(),
        setOf(
            0 to -2,
            0 to -1,
            0 to 6,
            0 to 7
        ).toCellState(),
    ) + List(50) { emptyCellState() }
)
