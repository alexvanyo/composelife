package com.alexvanyo.composelife.ui

import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.Spacer
import androidx.compose.foundation.layout.fillMaxWidth
import androidx.compose.foundation.layout.padding
import androidx.compose.material.Icon
import androidx.compose.material.IconToggleButton
import androidx.compose.material.Surface
import androidx.compose.material.Text
import androidx.compose.material.icons.Icons
import androidx.compose.material.icons.filled.Pause
import androidx.compose.material.icons.filled.PlayArrow
import androidx.compose.runtime.Composable
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.res.stringResource
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.R
import com.alexvanyo.composelife.model.TemporalGameOfLifeState
import com.google.accompanist.insets.navigationBarsHeight
import com.google.accompanist.insets.statusBarsHeight

@Suppress("LongMethod")
@Composable
fun InteractiveCellUniverse(
    temporalGameOfLifeState: TemporalGameOfLifeState,
    modifier: Modifier = Modifier,
) {
    val cellWindowState = rememberCellWindowState()

    Box(modifier = modifier) {
        MutableCellWindow(
            gameOfLifeState = temporalGameOfLifeState,
            cellWindowState = cellWindowState
        )

        val evolutionStatus = temporalGameOfLifeState.status

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

                Text(
                    text = when (evolutionStatus) {
                        TemporalGameOfLifeState.EvolutionStatus.Paused -> "Paused"
                        is TemporalGameOfLifeState.EvolutionStatus.Running ->
                            "GPS: ${evolutionStatus.averageGenerationsPerSecond}"
                    }
                )
            }
        }

        Surface(
            color = Color(0f, 0f, 0f, 0.3f),
            modifier = Modifier.align(Alignment.BottomCenter)
        ) {
            Column {
                val isRunning = when (evolutionStatus) {
                    TemporalGameOfLifeState.EvolutionStatus.Paused -> false
                    is TemporalGameOfLifeState.EvolutionStatus.Running -> true
                }

                IconToggleButton(
                    checked = isRunning,
                    onCheckedChange = temporalGameOfLifeState::setIsRunning,
                    modifier = Modifier
                        .fillMaxWidth()
                        .padding(16.dp)
                ) {
                    Icon(
                        imageVector = if (isRunning) {
                            Icons.Filled.Pause
                        } else {
                            Icons.Filled.PlayArrow
                        },
                        contentDescription = if (isRunning) {
                            stringResource(id = R.string.pause)
                        } else {
                            stringResource(id = R.string.play)
                        }
                    )
                }

                Spacer(
                    modifier = Modifier
                        .fillMaxWidth()
                        .navigationBarsHeight()
                )
            }
        }
    }
}
