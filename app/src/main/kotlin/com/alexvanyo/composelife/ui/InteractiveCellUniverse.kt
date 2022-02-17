package com.alexvanyo.composelife.ui

import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.Spacer
import androidx.compose.foundation.layout.padding
import androidx.compose.foundation.layout.systemBarsPadding
import androidx.compose.runtime.Composable
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.platform.testTag
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.model.TemporalGameOfLifeState

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
                    .testTag("CellUniverseInfoCard")
            )

            Spacer(modifier = Modifier.weight(1f))

            CellUniverseActionCard(
                temporalGameOfLifeState = temporalGameOfLifeState,
                modifier = Modifier.padding(8.dp).testTag("CellUniverseActionCard")
            )
        }
    }
}
