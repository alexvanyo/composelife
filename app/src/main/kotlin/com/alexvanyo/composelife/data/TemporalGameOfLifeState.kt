package com.alexvanyo.composelife.data

import androidx.annotation.FloatRange
import androidx.annotation.IntRange
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.setValue
import androidx.compose.runtime.snapshotFlow
import com.alexvanyo.composelife.data.model.CellState
import com.alexvanyo.composelife.data.model.MutableGameOfLifeState
import com.alexvanyo.composelife.data.model.emptyCellState
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.coroutineScope
import kotlinx.coroutines.delay
import kotlinx.coroutines.flow.launchIn
import kotlinx.coroutines.flow.onEach
import kotlinx.coroutines.flow.transformLatest
import kotlinx.coroutines.withContext
import kotlinx.datetime.Clock
import kotlinx.datetime.Instant
import kotlin.time.Duration
import kotlin.time.DurationUnit
import kotlin.time.ExperimentalTime

/**
 * A [MutableGameOfLifeState] that can change itself based on the passage of time, naturally evolving by generations.
 */
interface TemporalGameOfLifeState : MutableGameOfLifeState {

    /**
     * The current status of temporal evolution.
     */
    val status: EvolutionStatus

    /**
     * The number of generations to compute per step.
     */
    @setparam:IntRange(from = 1)
    var generationsPerStep: Int

    /**
     * The target number of steps to compute per second. Assuming this target can be met, the number of generations
     * per second is given by `generationsPerStep * targetStepsPerSecond`
     */
    var targetStepsPerSecond: Double

    /**
     * Pauses or resumes execution of temporal evolution.
     */
    fun setIsRunning(isRunning: Boolean)

    /**
     * A description of the current status of evolution.
     */
    sealed interface EvolutionStatus {

        /**
         * Temporal evolution is paused.
         */
        object Paused : EvolutionStatus

        /**
         * Temporal evolution is running, with the given [averageGenerationsPerSecond].
         */
        data class Running(
            val averageGenerationsPerSecond: Double
        ) : EvolutionStatus
    }
}

fun TemporalGameOfLifeState(
    coroutineScope: CoroutineScope,
    gameOfLifeAlgorithm: GameOfLifeAlgorithm,
    cellState: CellState = emptyCellState(),
    isRunning: Boolean = true,
    @IntRange(from = 1)
    generationsPerStep: Int = 1,
    @FloatRange(from = 0.0, fromInclusive = false)
    targetStepsPerSecond: Double = 60.0
): TemporalGameOfLifeState = TemporalGameOfLifeStateImpl(
    coroutineScope = coroutineScope,
    gameOfLifeAlgorithm = gameOfLifeAlgorithm,
    cellState = cellState,
    isRunning = isRunning,
    generationsPerStep = generationsPerStep,
    targetStepsPerSecond = targetStepsPerSecond
)

@OptIn(ExperimentalCoroutinesApi::class, ExperimentalTime::class)
private class TemporalGameOfLifeStateImpl(
    coroutineScope: CoroutineScope,
    private val gameOfLifeAlgorithm: GameOfLifeAlgorithm,
    cellState: CellState,
    isRunning: Boolean,
    generationsPerStep: Int,
    targetStepsPerSecond: Double
) : TemporalGameOfLifeState {

    override var cellState by mutableStateOf(cellState)

    override var generationsPerStep: Int by mutableStateOf(generationsPerStep)

    override var targetStepsPerSecond: Double by mutableStateOf(targetStepsPerSecond)

    override val status: TemporalGameOfLifeState.EvolutionStatus
        get() = if (isRunning) {
            TemporalGameOfLifeState.EvolutionStatus.Running(
                averageGenerationsPerSecond = averageGenerationsPerSecond
            )
        } else {
            TemporalGameOfLifeState.EvolutionStatus.Paused
        }

    private var isRunning: Boolean by mutableStateOf(isRunning)

    private var averageGenerationsPerSecond: Double by mutableStateOf(0.0)

    private val completedGenerationTracker = ArrayDeque<CellComputationResult.NormalResult>()

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
            .onEach { cellComputationResult ->
                this.cellState = cellComputationResult.cellState

                when (cellComputationResult) {
                    is CellComputationResult.InstantResult -> {
                        completedGenerationTracker.clear()
                        averageGenerationsPerSecond = 0.0
                    }
                    is CellComputationResult.NormalResult -> {
                        completedGenerationTracker.addFirst(cellComputationResult)
                        while (completedGenerationTracker.size > 10) {
                            completedGenerationTracker.removeLast()
                        }
                        averageGenerationsPerSecond =
                            completedGenerationTracker.sumOf { it.computedGenerations }.toDouble() /
                                    (completedGenerationTracker.first().endTime -
                                            completedGenerationTracker.last().startTime).toDouble(DurationUnit.SECONDS)
                    }
                }
            }
            .launchIn(coroutineScope)
    }

    override fun setIsRunning(isRunning: Boolean) {
        this.isRunning = isRunning
    }

    private fun getCellUpdateAsync(
        cellState: CellState,
        isRunning: Boolean,
        @IntRange(from = 1)
        generationsPerStep: Int,
        @FloatRange(from = 0.0, fromInclusive = false)
        targetStepsPerSecond: Double
    ): suspend () -> CellComputationResult =
        if (isRunning) {
            {
                val startTime = Clock.System.now()
                val newCellState = coroutineScope {
                    delay(Duration.seconds(1) / targetStepsPerSecond)
                    withContext(Dispatchers.Default) {
                        gameOfLifeAlgorithm.computeGenerationWithStep(cellState, generationsPerStep)
                    }
                }
                val endTime = Clock.System.now()
                CellComputationResult.NormalResult(
                    cellState = newCellState,
                    computedGenerations = generationsPerStep,
                    startTime = startTime,
                    endTime = endTime
                )
            }
        } else {
            {
                CellComputationResult.InstantResult(
                    cellState = cellState
                )
            }
        }
}

private sealed interface CellComputationResult {

    val cellState: CellState

    data class NormalResult(
        override val cellState: CellState,
        val computedGenerations: Int,
        val startTime: Instant,
        val endTime: Instant
    ) : CellComputationResult

    data class InstantResult(
        override val cellState: CellState
    ) : CellComputationResult
}
