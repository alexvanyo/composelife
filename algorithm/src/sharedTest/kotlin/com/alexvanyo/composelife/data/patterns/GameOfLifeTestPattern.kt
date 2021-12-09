package com.alexvanyo.composelife.data.patterns

import com.alexvanyo.composelife.data.model.CellState
import com.livefront.sealedenum.GenSealedEnum

sealed class GameOfLifeTestPattern(
    val patternName: String,
    val seedCellState: CellState,
    val cellStates: List<CellState>
) {
    override fun toString() = patternName

    @GenSealedEnum
    companion object
}
