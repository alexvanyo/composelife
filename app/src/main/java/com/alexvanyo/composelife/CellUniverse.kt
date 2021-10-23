package com.alexvanyo.composelife

import androidx.compose.material.Text
import androidx.compose.runtime.Composable
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.tooling.preview.Preview

@Composable
fun CellUniverse(
    gameOfLifeState: MutableGameOfLifeState
) {
    val cellWindowState = rememberCellWindowState()

    CellWindow(
        gameOfLifeState = gameOfLifeState,
        cellWindowState = cellWindowState
    )

    Text(
        text = "Offset: ${cellWindowState.offset}",
        color = Color.White,
    )
}

@Preview(
    widthDp = 1000,
    heightDp = 1000,
)
@Composable
fun CellUniversePreview() {
    CellUniverse(
        gameOfLifeState = MutableGameOfLifeState(
            setOf(
                0 to 0,
                0 to 2,
                0 to 4,
                2 to 0,
                2 to 2,
                2 to 4,
                4 to 0,
                4 to 2,
                4 to 4,
            )
        )
    )
}
