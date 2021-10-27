package com.alexvanyo.composelife.data

import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.setValue
import androidx.compose.runtime.snapshotFlow
import com.alexvanyo.composelife.data.model.CellState
import com.alexvanyo.composelife.data.model.MutableGameOfLifeState
import com.alexvanyo.composelife.data.model.emptyCellState
import kotlinx.coroutines.CompletableDeferred
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.Deferred
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.async
import kotlinx.coroutines.coroutineScope
import kotlinx.coroutines.delay
import kotlinx.coroutines.flow.launchIn
import kotlinx.coroutines.flow.onEach
import kotlinx.coroutines.flow.transformLatest
import kotlinx.coroutines.withContext
import kotlin.time.Duration
import kotlin.time.ExperimentalTime

/**
 * A [MutableGameOfLifeState] that changes itself based on the passage of time, naturally evolving by generations.
 */
interface TemporalGameOfLifeState : MutableGameOfLifeState {
    var isRunning: Boolean
    var generationsPerStep: Int
    var targetStepsPerSecond: Double
}

fun TemporalGameOfLifeState(
    coroutineScope: CoroutineScope,
    gameOfLifeAlgorithm: GameOfLifeAlgorithm,
    cellState: CellState = emptyCellState(),
    isRunning: Boolean = true,
    generationsPerStep: Int = 1,
    targetStepsPerSecond: Double = 60.0
): TemporalGameOfLifeState = TemporalGameOfLifeStateImpl(
    coroutineScope = coroutineScope,
    gameOfLifeAlgorithm = gameOfLifeAlgorithm,
    cellState = cellState,
    isRunning = isRunning,
    generationsPerStep = generationsPerStep,
    targetStepsPerSecond = targetStepsPerSecond
)

@OptIn(ExperimentalCoroutinesApi::class)
private class TemporalGameOfLifeStateImpl(
    private val coroutineScope: CoroutineScope,
    private val gameOfLifeAlgorithm: GameOfLifeAlgorithm,
    cellState: CellState,
    isRunning: Boolean,
    generationsPerStep: Int,
    targetStepsPerSecond: Double
) : TemporalGameOfLifeState {

    override var cellState by mutableStateOf(cellState)

    override var isRunning: Boolean by mutableStateOf(isRunning)

    override var generationsPerStep: Int by mutableStateOf(generationsPerStep)

    override var targetStepsPerSecond: Double by mutableStateOf(targetStepsPerSecond)

    init {
        // TODO: Allow buffering and parallelization of computing new generations
        snapshotFlow {
            getCellUpdateAsync(
                cellState = this.cellState,
                isRunning = this.isRunning,
                generationsPerStep = this.generationsPerStep,
                targetStepsPerSecond = this.targetStepsPerSecond
            )
        }
            .transformLatest {
                emit(it())
            }
            .onEach {
                this.cellState = it
            }
            .launchIn(coroutineScope)
    }

    @OptIn(ExperimentalTime::class)
    private fun getCellUpdateAsync(
        cellState: CellState,
        isRunning: Boolean,
        generationsPerStep: Int,
        targetStepsPerSecond: Double
    ): suspend () -> CellState =
        if (isRunning) {
            {
                coroutineScope {
                    delay(Duration.Companion.seconds(1) / targetStepsPerSecond)
                    withContext(Dispatchers.Default) {
                        gameOfLifeAlgorithm.computeGenerationWithStep(cellState, generationsPerStep)
                    }
                }
            }
        } else {
            { cellState }
        }
}
