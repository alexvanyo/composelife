package com.alexvanyo.composelife.algorithm

import com.alexvanyo.composelife.model.CellState
import com.alexvanyo.composelife.preferences.ComposeLifePreferences
import com.alexvanyo.composelife.preferences.proto.Algorithm
import kotlinx.coroutines.channels.Channel
import kotlinx.coroutines.currentCoroutineContext
import kotlinx.coroutines.flow.Flow
import kotlinx.coroutines.flow.SharingStarted
import kotlinx.coroutines.flow.buffer
import kotlinx.coroutines.flow.channelFlow
import kotlinx.coroutines.flow.first
import kotlinx.coroutines.flow.map
import kotlinx.coroutines.flow.shareIn
import kotlinx.coroutines.isActive
import javax.inject.Inject

class ConfigurableGameOfLifeAlgorithm @Inject constructor(
    preferences: ComposeLifePreferences,
    private val naiveGameOfLifeAlgorithm: NaiveGameOfLifeAlgorithm,
    private val hashLifeAlgorithm: HashLifeAlgorithm,
) : GameOfLifeAlgorithm {

    private val currentAlgorithm = preferences.algorithmChoice.map {
        when (it) {
            Algorithm.UNKNOWN, Algorithm.DEFAULT, Algorithm.HASHLIFE, Algorithm.UNRECOGNIZED -> hashLifeAlgorithm
            Algorithm.NAIVE -> naiveGameOfLifeAlgorithm
        }
    }

    override suspend fun computeGenerationWithStep(cellState: CellState, step: Int): CellState =
        currentAlgorithm.first().computeGenerationWithStep(
            cellState = cellState,
            step = step
        )

    override fun computeGenerationsWithStep(originalCellState: CellState, step: Int): Flow<CellState> =
        channelFlow {
            val currentAlgorithm = this@ConfigurableGameOfLifeAlgorithm.currentAlgorithm.shareIn(
                scope = this,
                started = SharingStarted.Eagerly,
                replay = 1
            )

            var cellState = originalCellState
            while (currentCoroutineContext().isActive) {
                cellState = currentAlgorithm.first().computeGenerationWithStep(
                    cellState = cellState,
                    step = step
                )
                send(cellState)
            }
        }
            .buffer(Channel.RENDEZVOUS)
}
