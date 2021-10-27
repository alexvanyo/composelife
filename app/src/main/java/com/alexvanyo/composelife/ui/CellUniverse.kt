package com.alexvanyo.composelife.ui

import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.Spacer
import androidx.compose.foundation.layout.fillMaxWidth
import androidx.compose.material.Surface
import androidx.compose.material.Text
import androidx.compose.runtime.Composable
import androidx.compose.ui.Modifier
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.tooling.preview.Preview
import com.alexvanyo.composelife.data.model.MutableGameOfLifeState
import com.google.accompanist.insets.statusBarsHeight

@Composable
fun CellUniverse(
    gameOfLifeState: MutableGameOfLifeState
) {
    val cellWindowState = rememberCellWindowState()

    Box {
        MutableCellWindow(
            gameOfLifeState = gameOfLifeState,
            cellWindowState = cellWindowState
        )

        Surface(color = Color(0f, 0f, 0f, 0.3f)) {
            Column {
                Spacer(
                    modifier = Modifier
                        .fillMaxWidth()
                        .statusBarsHeight()
                )

                Text(
                    text = "Offset: ${cellWindowState.offset}",
                )
            }
        }
    }
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
