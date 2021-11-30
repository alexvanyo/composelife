package com.alexvanyo.composelife.data

import androidx.annotation.FloatRange
import androidx.annotation.IntRange
import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateListOf
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.runtime.saveable.Saver
import androidx.compose.runtime.saveable.listSaver
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.setValue
import androidx.compose.runtime.snapshotFlow
import androidx.compose.ui.unit.IntOffset
import com.alexvanyo.composelife.data.model.CellState
import com.alexvanyo.composelife.data.model.MutableGameOfLifeState
import com.alexvanyo.composelife.data.model.emptyCellState
import com.alexvanyo.composelife.data.model.toCellState
import com.alexvanyo.composelife.util.toPair
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.delay
import kotlinx.coroutines.flow.Flow
import kotlinx.coroutines.flow.MutableSharedFlow
import kotlinx.coroutines.flow.buffer
import kotlinx.coroutines.flow.collect
import kotlinx.coroutines.flow.collectLatest
import kotlinx.coroutines.flow.map
import kotlinx.coroutines.flow.zip
import kotlinx.coroutines.launch
import kotlinx.datetime.Clock
import kotlinx.datetime.Instant
import java.util.UUID
import kotlin.time.Duration.Companion.seconds
import kotlin.time.DurationUnit
import kotlin.time.ExperimentalTime

/**
 * A [MutableGameOfLifeState] that can change based on the passage of time, naturally evolving by generations.
 */
sealed interface TemporalGameOfLifeState : MutableGameOfLifeState {

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
    @setparam:FloatRange(from = 0.0, fromInclusive = false)
    var targetStepsPerSecond: Double

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

    companion object {
        val defaultCellState = emptyCellState()
        const val defaultIsRunning = true
        const val defaultGenerationsPerStep = 1
        const val defaultTargetStepsPerSecond = 60.0
    }
}

/**
 * A mutator for a [TemporalGameOfLifeState].
 *
 * If a [TemporalGameOfLifeStateMutator] is attached to a [TemporalGameOfLifeState], then the [TemporalGameOfLifeState]
 * will automatically advance (if running) with no user input.
 *
 * To accomplish this, the [TemporalGameOfLifeStateMutator] will need to exist in some [CoroutineScope] that performs
 * computation.
 */
interface TemporalGameOfLifeStateMutator {

    /**
     * Pauses or resumes execution of temporal evolution.
     */
    fun setIsRunning(isRunning: Boolean)
}

@Composable
fun rememberTemporalGameOfLifeState(
    cellState: CellState = TemporalGameOfLifeState.defaultCellState,
    isRunning: Boolean = TemporalGameOfLifeState.defaultIsRunning,
    @IntRange(from = 1)
    generationsPerStep: Int = TemporalGameOfLifeState.defaultGenerationsPerStep,
    @FloatRange(from = 0.0, fromInclusive = false)
    targetStepsPerSecond: Double = TemporalGameOfLifeState.defaultTargetStepsPerSecond
): TemporalGameOfLifeState =
    rememberSaveable(saver = TemporalGameOfLifeStateImpl.Saver) {
        TemporalGameOfLifeState(
            cellState = cellState,
            isRunning = isRunning,
            generationsPerStep = generationsPerStep,
            targetStepsPerSecond = targetStepsPerSecond
        )
    }

fun TemporalGameOfLifeState(
    cellState: CellState = TemporalGameOfLifeState.defaultCellState,
    isRunning: Boolean = TemporalGameOfLifeState.defaultIsRunning,
    @IntRange(from = 1)
    generationsPerStep: Int = TemporalGameOfLifeState.defaultGenerationsPerStep,
    @FloatRange(from = 0.0, fromInclusive = false)
    targetStepsPerSecond: Double = TemporalGameOfLifeState.defaultTargetStepsPerSecond
): TemporalGameOfLifeState = TemporalGameOfLifeStateImpl(
    seedCellState = cellState,
    isRunning = isRunning,
    generationsPerStep = generationsPerStep,
    targetStepsPerSecond = targetStepsPerSecond
)

@OptIn(ExperimentalCoroutinesApi::class, ExperimentalTime::class)
private class TemporalGameOfLifeStateImpl(
    seedCellState: CellState = TemporalGameOfLifeState.defaultCellState,
    isRunning: Boolean = TemporalGameOfLifeState.defaultIsRunning,
    @IntRange(from = 1)
    generationsPerStep: Int = TemporalGameOfLifeState.defaultGenerationsPerStep,
    @FloatRange(from = 0.0, fromInclusive = false)
    targetStepsPerSecond: Double = TemporalGameOfLifeState.defaultTargetStepsPerSecond
) : TemporalGameOfLifeState {

    override var cellState: CellState
        get() = computedCellState
        set(value) {
            seedCellState = value
            seedId = UUID.randomUUID()
            computedCellState = seedCellState
        }

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

    var seedId: UUID by mutableStateOf(UUID.randomUUID())

    var seedCellState by mutableStateOf(seedCellState)

    var computedCellState by mutableStateOf(seedCellState)

    var isRunning by mutableStateOf(isRunning)

    private val averageGenerationsPerSecond: Double
        get() =
            if (completedGenerationTracker.size == 0) {
                0.0
            } else {
                completedGenerationTracker.sumOf { it.computedGenerations }.toDouble() /
                    (
                        completedGenerationTracker.last().endTime -
                            completedGenerationTracker.first().startTime
                        ).toDouble(DurationUnit.SECONDS)
            }

    val completedGenerationTracker: MutableList<CellComputationResult> = mutableStateListOf()

    companion object {
        val Saver: Saver<TemporalGameOfLifeState, *> = listSaver(
            { temporalGameOfLifeState ->
                when (temporalGameOfLifeState) { is TemporalGameOfLifeStateImpl -> Unit }
                listOf(
                    temporalGameOfLifeState.computedCellState.map(IntOffset::toPair),
                    temporalGameOfLifeState.isRunning,
                    temporalGameOfLifeState.generationsPerStep,
                    temporalGameOfLifeState.targetStepsPerSecond
                )
            },
            { list ->
                @Suppress("UNCHECKED_CAST")
                TemporalGameOfLifeStateImpl(
                    seedCellState = (list[0] as List<Pair<Int, Int>>).toSet().toCellState(),
                    isRunning = list[1] as Boolean,
                    generationsPerStep = list[2] as Int,
                    targetStepsPerSecond = list[3] as Double
                )
            }
        )
    }
}

private data class CellComputationResult(
    val cellState: CellState,
    val computedGenerations: Int,
    val startTime: Instant,
    val endTime: Instant
)

@Composable
fun rememberTemporalGameOfLifeStateMutator(
    temporalGameOfLifeState: TemporalGameOfLifeState,
    gameOfLifeAlgorithm: GameOfLifeAlgorithm,
    coroutineScope: CoroutineScope = rememberCoroutineScope()
): TemporalGameOfLifeStateMutator {
    when (temporalGameOfLifeState) { is TemporalGameOfLifeStateImpl -> Unit }

    return remember(gameOfLifeAlgorithm, coroutineScope) {
        TemporalGameOfLifeStateMutatorImpl(
            coroutineScope = coroutineScope,
            gameOfLifeAlgorithm = gameOfLifeAlgorithm,
            temporalGameOfLifeState = temporalGameOfLifeState
        )
    }
}

@OptIn(ExperimentalCoroutinesApi::class)
private class TemporalGameOfLifeStateMutatorImpl(
    coroutineScope: CoroutineScope,
    private val gameOfLifeAlgorithm: GameOfLifeAlgorithm,
    private val temporalGameOfLifeState: TemporalGameOfLifeStateImpl
) : TemporalGameOfLifeStateMutator {

    private class UpdateCellStateDependencies(
        private val seedId: UUID,
        private val seedCellState: CellState,
        private val isRunning: Boolean,
        private val generationsPerStep: Int,
        private val targetStepsPerSecond: Double
    )

    init {
        coroutineScope.launch {
            snapshotFlow {
                // Read all dependencies that should invalidate our current getCellUpdates
                // We don't use these values directly, since we are about to race canceling previous updates
                UpdateCellStateDependencies(
                    seedId = temporalGameOfLifeState.seedId,
                    seedCellState = temporalGameOfLifeState.seedCellState,
                    isRunning = temporalGameOfLifeState.isRunning,
                    generationsPerStep = temporalGameOfLifeState.generationsPerStep,
                    targetStepsPerSecond = temporalGameOfLifeState.targetStepsPerSecond
                )
            }
                // Invalidate any previous cell updates, and crucially only one collectLatest block can run at a time.
                .collectLatest { updateCellState() }
        }
    }

    override fun setIsRunning(isRunning: Boolean) {
        temporalGameOfLifeState.isRunning = isRunning
    }

    private suspend fun updateCellState() {
        if (temporalGameOfLifeState.isRunning) {
            // At this point, computedCellState cannot be changed by a previous getCellUpdates
            getCellUpdates(
                seedCellState = temporalGameOfLifeState.computedCellState,
                generationsPerStep = temporalGameOfLifeState.generationsPerStep,
                targetStepsPerSecond = temporalGameOfLifeState.targetStepsPerSecond
            )
                .collect { cellComputationResult ->
                    // Update in a loopback manner with each cell computation result
                    temporalGameOfLifeState.computedCellState = cellComputationResult.cellState
                    temporalGameOfLifeState.completedGenerationTracker.add(cellComputationResult)
                    while (temporalGameOfLifeState.completedGenerationTracker.size > 10) {
                        temporalGameOfLifeState.completedGenerationTracker.removeFirst()
                    }
                }
        } else {
            temporalGameOfLifeState.completedGenerationTracker.clear()
        }
    }

    @OptIn(ExperimentalTime::class)
    private fun getCellUpdates(
        seedCellState: CellState,
        @IntRange(from = 1)
        generationsPerStep: Int,
        @FloatRange(from = 0.0, fromInclusive = false)
        targetStepsPerSecond: Double
    ): Flow<CellComputationResult> {
        val tickFlow = MutableSharedFlow<Unit>(replay = 1)
        tickFlow.tryEmit(Unit)

        return gameOfLifeAlgorithm
            .computeGenerationsWithStep(
                originalCellState = seedCellState,
                step = generationsPerStep
            )
            .buffer()
            .zip(
                tickFlow
                    .map {
                        val startTime = Clock.System.now()
                        delay(1.seconds / targetStepsPerSecond)
                        startTime
                    }
            ) { newCellState, startTime ->
                val endTime = Clock.System.now()
                tickFlow.tryEmit(Unit)

                CellComputationResult(
                    cellState = newCellState,
                    computedGenerations = generationsPerStep,
                    startTime = startTime,
                    endTime = endTime
                )
            }
    }
}
