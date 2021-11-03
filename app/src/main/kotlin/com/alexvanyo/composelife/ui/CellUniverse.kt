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
import com.alexvanyo.composelife.data.TemporalGameOfLifeState
import com.google.accompanist.insets.statusBarsHeight

@Composable
fun CellUniverse(
    gameOfLifeState: TemporalGameOfLifeState
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
                    text = "Offset: ${cellWindowState.offset}, Scale: ${cellWindowState.scale}",
                )

                val evolutionStatus = gameOfLifeState.status

                Text(
                    text = when (evolutionStatus) {
                        TemporalGameOfLifeState.EvolutionStatus.Paused -> "Paused"
                        is TemporalGameOfLifeState.EvolutionStatus.Running ->
                            "GPS: ${evolutionStatus.averageGenerationsPerSecond}"
                    }
                )
            }
        }
    }
}
