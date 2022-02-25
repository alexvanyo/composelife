package com.alexvanyo.composelife.preferences

import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.setValue
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.preferences.CurrentShape.RoundRectangle
import com.alexvanyo.composelife.preferences.proto.AlgorithmProto
import com.alexvanyo.composelife.preferences.proto.CurrentShapeTypeProto
import com.alexvanyo.composelife.preferences.proto.RoundRectangleProto
import com.alexvanyo.composelife.preferences.proto.copy
import com.alexvanyo.composelife.preferences.proto.roundRectangleProto
import com.alexvanyo.composelife.resourcestate.ResourceState
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.SupervisorJob
import kotlinx.coroutines.flow.catch
import kotlinx.coroutines.flow.launchIn
import kotlinx.coroutines.flow.onEach
import javax.inject.Inject

class DefaultComposeLifePreferences @Inject constructor(
    private val dataStore: PreferencesDataStore,
    dispatchers: ComposeLifeDispatchers,
) : ComposeLifePreferences {

    private val lazyObserver by lazy {
        object {
            private val scope = CoroutineScope(dispatchers.Main + SupervisorJob())

            var algorithmChoiceState: ResourceState<AlgorithmType> by mutableStateOf(ResourceState.Loading)
                private set

            var currentShapeState: ResourceState<CurrentShape> by mutableStateOf(ResourceState.Loading)
                private set

            init {
                dataStore.data
                    .onEach { preferencesProto ->
                        algorithmChoiceState = ResourceState.Success(
                            when (preferencesProto.algorithm!!) {
                                AlgorithmProto.ALGORITHM_UNKNOWN,
                                AlgorithmProto.DEFAULT,
                                AlgorithmProto.HASHLIFE,
                                AlgorithmProto.UNRECOGNIZED
                                -> AlgorithmType.HashLifeAlgorithm
                                AlgorithmProto.NAIVE -> AlgorithmType.NaiveAlgorithm
                            }
                        )

                        currentShapeState = ResourceState.Success(
                            when (preferencesProto.currentShapeType!!) {
                                CurrentShapeTypeProto.CURRENT_SHAPE_TYPE_UNKNOWN,
                                CurrentShapeTypeProto.UNRECOGNIZED -> defaultRoundRectangle
                                CurrentShapeTypeProto.ROUND_RECTANGLE -> preferencesProto.roundRectangle.toResolved()
                            }
                        )
                    }
                    .catch {
                        algorithmChoiceState = ResourceState.Failure(it)
                        currentShapeState = ResourceState.Failure(it)
                    }
                    .launchIn(scope)
            }
        }
    }

    override val algorithmChoiceState: ResourceState<AlgorithmType> get() = lazyObserver.algorithmChoiceState

    override val currentShapeState: ResourceState<CurrentShape> get() = lazyObserver.currentShapeState

    override suspend fun setAlgorithmChoice(algorithm: AlgorithmType) {
        dataStore.updateData { preferencesProto ->
            preferencesProto.copy {
                this.algorithm = when (algorithm) {
                    AlgorithmType.HashLifeAlgorithm -> AlgorithmProto.HASHLIFE
                    AlgorithmType.NaiveAlgorithm -> AlgorithmProto.NAIVE
                }
            }
        }
    }

    override suspend fun setCurrentShapeType(currentShapeType: CurrentShapeType) {
        dataStore.updateData { preferencesProto ->
            preferencesProto.copy {
                this.currentShapeType = when (currentShapeType) {
                    CurrentShapeType.RoundRectangle -> CurrentShapeTypeProto.ROUND_RECTANGLE
                }
            }
        }
    }

    override suspend fun setRoundRectangleConfig(update: (RoundRectangle) -> RoundRectangle) {
        dataStore.updateData { preferencesProto ->
            preferencesProto.copy {
                when (currentShapeType) {
                    CurrentShapeTypeProto.CURRENT_SHAPE_TYPE_UNKNOWN,
                    CurrentShapeTypeProto.UNRECOGNIZED -> {
                        currentShapeType = CurrentShapeTypeProto.ROUND_RECTANGLE
                        roundRectangle = defaultRoundRectangle.toProto()
                    }
                    CurrentShapeTypeProto.ROUND_RECTANGLE -> Unit
                }
                roundRectangle = update(roundRectangle.toResolved()).toProto()
            }
        }
    }
}

private val defaultRoundRectangle
    get() = RoundRectangle(
        sizeFraction = 1f,
        cornerFraction = 0f
    )

private fun RoundRectangleProto.toResolved(): RoundRectangle =
    RoundRectangle(
        sizeFraction = sizeFraction,
        cornerFraction = cornerFraction,
    )

private fun RoundRectangle.toProto(): RoundRectangleProto =
    roundRectangleProto {
        sizeFraction = this@toProto.sizeFraction
        cornerFraction = this@toProto.cornerFraction
    }
