package com.alexvanyo.composelife.preferences

import com.alexvanyo.composelife.preferences.CurrentShape.RoundRectangle
import com.alexvanyo.composelife.resourcestate.ResourceState

interface ComposeLifePreferences {
    val algorithmChoiceState: ResourceState<AlgorithmType>

    val currentShapeState: ResourceState<CurrentShape>

    suspend fun setAlgorithmChoice(algorithm: AlgorithmType)

    suspend fun setCurrentShapeType(currentShapeType: CurrentShapeType)

    suspend fun setRoundRectangleConfig(update: (RoundRectangle) -> RoundRectangle)
}
