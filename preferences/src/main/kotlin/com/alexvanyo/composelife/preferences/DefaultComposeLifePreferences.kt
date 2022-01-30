package com.alexvanyo.composelife.preferences

import com.alexvanyo.composelife.preferences.proto.Algorithm
import com.alexvanyo.composelife.preferences.proto.Preferences
import com.alexvanyo.composelife.preferences.proto.copy
import kotlinx.coroutines.flow.Flow
import kotlinx.coroutines.flow.map
import kotlinx.coroutines.flow.retry
import javax.inject.Inject

class DefaultComposeLifePreferences @Inject constructor(
    private val dataStore: PreferencesDataStore
) : ComposeLifePreferences {
    override val algorithmChoice: Flow<Algorithm> =
        dataStore.data.map(Preferences::getAlgorithm).retry()

    override suspend fun setAlgorithmChoice(algorithm: Algorithm) {
        dataStore.updateData {
            it.copy {
                this.algorithm = algorithm
            }
        }
    }
}
