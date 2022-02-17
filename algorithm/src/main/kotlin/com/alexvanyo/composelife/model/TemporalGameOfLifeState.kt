package com.alexvanyo.composelife.model

import androidx.annotation.FloatRange
import androidx.annotation.IntRange
import androidx.compose.runtime.Composable
import androidx.compose.runtime.derivedStateOf
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateListOf
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.referentialEqualityPolicy
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.runtime.saveable.Saver
import androidx.compose.runtime.saveable.listSaver
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.setValue
import androidx.compose.runtime.snapshotFlow
import androidx.compose.ui.unit.IntOffset
import com.alexvanyo.composelife.algorithm.GameOfLifeAlgorithm
import com.alexvanyo.composelife.util.toPair
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.channels.Channel
import kotlinx.coroutines.coroutineScope
import kotlinx.coroutines.delay
import kotlinx.coroutines.flow.Flow
import kotlinx.coroutines.flow.MutableSharedFlow
import kotlinx.coroutines.flow.buffer
import kotlinx.coroutines.flow.collectLatest
import kotlinx.coroutines.flow.emptyFlow
import kotlinx.coroutines.flow.flatMapLatest
import kotlinx.coroutines.flow.map
import kotlinx.coroutines.flow.merge
import kotlinx.coroutines.flow.receiveAsFlow
import kotlinx.coroutines.flow.zip
import kotlinx.coroutines.launch
import kotlinx.coroutines.sync.Mutex
import kotlinx.coroutines.sync.withLock
import kotlinx.datetime.Clock
import kotlinx.datetime.Instant
import java.util.UUID
import kotlin.time.Duration
import kotlin.time.Duration.Companion.seconds
import kotlin.time.DurationUnit

/**
 * A [MutableGameOfLifeState] that can change based on the passage of time, naturally evolving by generations.
 */
sealed interface TemporalGameOfLifeState : MutableGameOfLifeState {

    /**
     * The seed cell state that is starting the current genealogy.
     */
    val seedCellState: CellState

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
     * Pauses or resumes execution of temporal evolution.
     */
    fun setIsRunning(isRunning: Boolean)

    /**
     * Evolves the cell state a single step, and pauses execution if it is running.
     *
     * This function suspends until the step is complete.
     */
    suspend fun step()

    /**
     * Evolves the cell state using the given [GameOfLifeAlgorithm] automatically through time
     */
    suspend fun evolve(gameOfLifeAlgorithm: GameOfLifeAlgorithm, clock: Clock)

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
            val averageGenerationsPerSecond: Double,
        ) : EvolutionStatus
    }

    companion object {
        val defaultCellState = emptyCellState()
        const val defaultIsRunning = true
        const val defaultGenerationsPerStep = 1
        const val defaultTargetStepsPerSecond = 60.0
    }
}

private class GameOfLifeGenealogy(
    private val seedCellState: CellState,
    private val generationsPerStep: Int,
) {
    /**
     * The current, computed [CellState] to render.
     *
     * Use [referentialEqualityPolicy] here to avoid costly comparisons as the cell state changes.
     */
    var computedCellState by mutableStateOf(seedCellState, policy = referentialEqualityPolicy())
        private set

    suspend fun evolve(
        gameOfLifeAlgorithm: GameOfLifeAlgorithm,
        stepTicker: Flow<Unit>,
        onNewCellState: (generationsPerStep: Int) -> Unit,
    ) {
        gameOfLifeAlgorithm
            .computeGenerationsWithStep(
                originalCellState = seedCellState,
                step = generationsPerStep
            )
            .buffer()
            .zip(stepTicker) { newCellState, _ -> newCellState }
            .collect { cellState ->
                computedCellState = cellState
                onNewCellState(generationsPerStep)
            }
    }
}

@Composable
fun rememberTemporalGameOfLifeState(
    cellState: CellState = TemporalGameOfLifeState.defaultCellState,
    isRunning: Boolean = TemporalGameOfLifeState.defaultIsRunning,
    @IntRange(from = 1)
    generationsPerStep: Int = TemporalGameOfLifeState.defaultGenerationsPerStep,
    @FloatRange(from = 0.0, fromInclusive = false)
    targetStepsPerSecond: Double = TemporalGameOfLifeState.defaultTargetStepsPerSecond,
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
    targetStepsPerSecond: Double = TemporalGameOfLifeState.defaultTargetStepsPerSecond,
): TemporalGameOfLifeState = TemporalGameOfLifeStateImpl(
    seedCellState = cellState,
    isRunning = isRunning,
    generationsPerStep = generationsPerStep,
    targetStepsPerSecond = targetStepsPerSecond
)

private class TemporalGameOfLifeStateImpl(
    seedCellState: CellState,
    isRunning: Boolean,
    @IntRange(from = 1)
    generationsPerStep: Int,
    @FloatRange(from = 0.0, fromInclusive = false)
    targetStepsPerSecond: Double,
) : TemporalGameOfLifeState {

    override var cellState: CellState
        get() = cellStateGenealogy.computedCellState
        set(value) {
            seedCellState = value
        }

    private var _generationsPerStep: Int by mutableStateOf(generationsPerStep)

    override var generationsPerStep
        get() = _generationsPerStep
        set(value) {
            // Update the seed cell state to the current cell state, so the computation continues from where it
            // currently is. This has to come before updating generations per step, since retrieving the cell state
            // requires the old genealogy before it is updated.
            seedCellState = cellState
            _generationsPerStep = value
        }

    override var targetStepsPerSecond: Double by mutableStateOf(targetStepsPerSecond)

    override val status: TemporalGameOfLifeState.EvolutionStatus
        get() = if (isRunning) {
            TemporalGameOfLifeState.EvolutionStatus.Running(
                averageGenerationsPerSecond = averageGenerationsPerSecond
            )
        } else {
            TemporalGameOfLifeState.EvolutionStatus.Paused
        }

    private var seedId by mutableStateOf(UUID.randomUUID())

    private var _seedCellState by mutableStateOf(seedCellState)

    override var seedCellState
        get() = _seedCellState
        set(value) {
            _seedCellState = value
            seedId = UUID.randomUUID()
        }

    private val cellStateGenealogy by derivedStateOf {
        // Update the genealogy if the seed id changes
        // This ensures that setting the same seed state again will restart at that point, even if the current state
        // has evolved well beyond the seed state.
        this.seedId
        GameOfLifeGenealogy(
            seedCellState = this.seedCellState,
            generationsPerStep = this.generationsPerStep,
        )
    }

    private var isRunning by mutableStateOf(isRunning)

    private val stepManualTicker = Channel<Unit>(Channel.RENDEZVOUS)

    private val evolveMutex = Mutex()

    override fun setIsRunning(isRunning: Boolean) {
        this.isRunning = isRunning
    }

    override suspend fun step() {
        setIsRunning(false)
        stepManualTicker.send(Unit)
    }

    override suspend fun evolve(gameOfLifeAlgorithm: GameOfLifeAlgorithm, clock: Clock) {
        evolveMutex.withLock {
            try {
                // coroutineScope to ensure all child coroutines finish
                coroutineScope {
                    evolveImpl(gameOfLifeAlgorithm, clock)
                }
            } finally {
                // Update the seedCellState with the current cell state to ensure that the next evolve picks up at the
                // correct spot
                seedCellState = cellState
            }
        }
    }

    /**
     * The implementation of [evolve] guarded by [evolveMutex].
     */
    @OptIn(ExperimentalCoroutinesApi::class)
    suspend fun evolveImpl(gameOfLifeAlgorithm: GameOfLifeAlgorithm, clock: Clock) {
        val lastTickFlow = MutableSharedFlow<Instant>(replay = 1)

        val stepTimeTicker = snapshotFlow {
            isRunning to targetStepsPerSecond
        }
            .flatMapLatest { (isRunning, targetStepsPerSecond) ->
                if (isRunning) {
                    lastTickFlow.tryEmit(clock.now())
                    lastTickFlow.map { lastTick ->
                        val targetDelay = 1.seconds / targetStepsPerSecond
                        val remainingDelay = (targetDelay - (clock.now() - lastTick)).coerceAtLeast(Duration.ZERO)
                        delay(remainingDelay)
                    }
                } else {
                    emptyFlow()
                }
            }
            .buffer(0) // No buffer, so the ticks are only consumed upon a cell state being computed

        val stepTicker = merge(
            stepTimeTicker,
            stepManualTicker.receiveAsFlow()
        )
            .buffer(0) // No buffer, so the ticks are only consumed upon a cell state being computed

        snapshotFlow { cellStateGenealogy }
            .collectLatest { cellStateGenealogy ->
                completedGenerationTracker.add(
                    ComputationRecord(
                        computedGenerations = 0,
                        computedTime = clock.now()
                    )
                )
                cellStateGenealogy.evolve(gameOfLifeAlgorithm, stepTicker) { generationsPerStep ->
                    val lastTick = clock.now()
                    lastTickFlow.tryEmit(lastTick)
                    completedGenerationTracker.apply {
                        add(
                            ComputationRecord(
                                computedGenerations = generationsPerStep,
                                computedTime = lastTick
                            )
                        )
                        // Remove entries that are more than a second old to get a running average from the last second
                        while (last().computedTime - first().computedTime > 1.seconds) {
                            removeFirst()
                        }
                    }
                }
            }
    }

    /**
     * The backing value of [TemporalGameOfLifeState.EvolutionStatus.Running.averageGenerationsPerSecond] when running.
     * This is computed as a running average of the last second of computations, as kept track in
     * [completedGenerationTracker].
     */
    private val averageGenerationsPerSecond: Double
        get() =
            if (completedGenerationTracker.size < 2) {
                0.0
            } else {
                val totalComputedGenerations = completedGenerationTracker.drop(1).sumOf { it.computedGenerations }
                val duration = completedGenerationTracker.last().computedTime -
                    completedGenerationTracker.first().computedTime
                totalComputedGenerations / duration.toDouble(DurationUnit.SECONDS)
            }

    private val completedGenerationTracker: MutableList<ComputationRecord> = mutableStateListOf()

    companion object {
        val Saver: Saver<TemporalGameOfLifeState, *> = listSaver(
            { temporalGameOfLifeState ->
                when (temporalGameOfLifeState) {
                    is TemporalGameOfLifeStateImpl -> Unit
                }
                listOf(
                    temporalGameOfLifeState.cellState.aliveCells.map(IntOffset::toPair),
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

private data class ComputationRecord(
    val computedGenerations: Int,
    val computedTime: Instant,
)

@Composable
fun rememberTemporalGameOfLifeStateMutator(
    temporalGameOfLifeState: TemporalGameOfLifeState,
    gameOfLifeAlgorithm: GameOfLifeAlgorithm,
    coroutineScope: CoroutineScope = rememberCoroutineScope(),
    clock: Clock = Clock.System,
): TemporalGameOfLifeStateMutator =
    remember(gameOfLifeAlgorithm, coroutineScope) {
        TemporalGameOfLifeStateMutator(
            coroutineScope = coroutineScope,
            clock = clock,
            gameOfLifeAlgorithm = gameOfLifeAlgorithm,
            temporalGameOfLifeState = temporalGameOfLifeState
        )
    }

class TemporalGameOfLifeStateMutator(
    coroutineScope: CoroutineScope,
    private val clock: Clock,
    private val gameOfLifeAlgorithm: GameOfLifeAlgorithm,
    private val temporalGameOfLifeState: TemporalGameOfLifeState,
) {
    init {
        coroutineScope.launch {
            temporalGameOfLifeState.evolve(gameOfLifeAlgorithm, clock)
        }
    }
}
