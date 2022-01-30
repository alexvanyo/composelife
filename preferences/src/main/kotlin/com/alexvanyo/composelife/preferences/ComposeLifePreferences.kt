package com.alexvanyo.composelife.preferences

import com.alexvanyo.composelife.preferences.proto.Algorithm
import kotlinx.coroutines.flow.Flow

interface ComposeLifePreferences {
    val algorithmChoice: Flow<Algorithm>

    suspend fun setAlgorithmChoice(algorithm: Algorithm)
}
