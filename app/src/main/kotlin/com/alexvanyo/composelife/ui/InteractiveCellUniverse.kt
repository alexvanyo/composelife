package com.alexvanyo.composelife.ui

import androidx.compose.foundation.layout.Box
import androidx.compose.runtime.Composable
import androidx.compose.ui.Modifier
import com.alexvanyo.composelife.model.TemporalGameOfLifeState

/**
 * An interactive cell universe displaying the given [temporalGameOfLifeState] and the controls for adjusting how it
 * evolves.
 */
@Composable
fun InteractiveCellUniverse(
    temporalGameOfLifeState: TemporalGameOfLifeState,
    modifier: Modifier = Modifier,
    cellWindowState: CellWindowState = rememberCellWindowState(),
) {
    Box(modifier = modifier) {
        MutableCellWindow(
            gameOfLifeState = temporalGameOfLifeState,
            cellWindowState = cellWindowState
        )
        InteractiveCellUniverseOverlay(
            temporalGameOfLifeState = temporalGameOfLifeState,
            cellWindowState = cellWindowState
        )
    }
}
