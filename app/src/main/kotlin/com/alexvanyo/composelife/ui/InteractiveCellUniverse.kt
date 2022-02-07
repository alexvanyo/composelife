package com.alexvanyo.composelife.ui

import androidx.compose.foundation.layout.Arrangement
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.Row
import androidx.compose.foundation.layout.Spacer
import androidx.compose.foundation.layout.padding
import androidx.compose.foundation.layout.systemBarsPadding
import androidx.compose.material.Card
import androidx.compose.material.Icon
import androidx.compose.material.IconToggleButton
import androidx.compose.material.icons.Icons
import androidx.compose.material.icons.filled.Pause
import androidx.compose.material.icons.filled.PlayArrow
import androidx.compose.runtime.Composable
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.res.stringResource
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.R
import com.alexvanyo.composelife.model.TemporalGameOfLifeState

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

        Column(
            horizontalAlignment = Alignment.CenterHorizontally,
            modifier = Modifier.systemBarsPadding()
        ) {
            CellUniverseInfoCard(
                cellWindowState = cellWindowState,
                evolutionStatus = evolutionStatus,
                modifier = Modifier
                    .align(Alignment.End)
                    .padding(8.dp)
            )

            Spacer(modifier = Modifier.weight(1f))

            CellUniverseActionCard(
                isRunning = when (evolutionStatus) {
                    TemporalGameOfLifeState.EvolutionStatus.Paused -> false
                    is TemporalGameOfLifeState.EvolutionStatus.Running -> true
                },
                setIsRunning = temporalGameOfLifeState::setIsRunning,
                modifier = Modifier.padding(8.dp)
            )
        }
    }
}

@Composable
fun CellUniverseActionCard(
    isRunning: Boolean,
    setIsRunning: (Boolean) -> Unit,
    modifier: Modifier = Modifier,
) {
    Card(modifier = modifier) {
        Row(
            horizontalArrangement = Arrangement.spacedBy(8.dp),
            modifier = Modifier.padding(8.dp),
        ) {
            IconToggleButton(
                checked = isRunning,
                onCheckedChange = setIsRunning,
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
        }
    }
}
