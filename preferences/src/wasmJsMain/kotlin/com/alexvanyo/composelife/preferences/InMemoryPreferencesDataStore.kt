/*
 * Copyright 2025 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.alexvanyo.composelife.preferences

import com.alexvanyo.composelife.preferences.proto.PreferencesProto
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.BindingContainer
import dev.zacsweers.metro.Binds
import dev.zacsweers.metro.ContributesBinding
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.Inject
import dev.zacsweers.metro.SingleIn
import kotlinx.coroutines.flow.Flow
import kotlinx.coroutines.flow.MutableStateFlow
import kotlinx.coroutines.flow.updateAndGet

@ContributesTo(AppScope::class)
@BindingContainer
interface InMemoryPreferencesDataStoreBindings {
    @Binds
    val InMemoryPreferencesDataStore.bind: PreferencesDataStore
}

/**
 * TODO: Replace with DiskPreferencesDataStore when DataStore supports wasmJs.
 */
@SingleIn(AppScope::class)
@Inject
class InMemoryPreferencesDataStore : PreferencesDataStore {
    private val actualDataStore = MutableStateFlow(
        PreferencesProto(
            round_rectangle_session_id = LoadedComposeLifePreferences
                .defaultRoundRectangleSessionId
                .toProto(),
            round_rectangle_value_id = LoadedComposeLifePreferences
                .defaultRoundRectangleValueId
                .toProto(),
            pattern_collections_synchronization_period_session_id = LoadedComposeLifePreferences
                .defaultPatternCollectionsSynchronizationPeriodSessionId
                .toProto(),
            pattern_collections_synchronization_period_value_id = LoadedComposeLifePreferences
                .defaultPatternCollectionsSynchronizationPeriodValueId
                .toProto(),
        ),
    )

    private val dataStore: KmpDataStore<PreferencesProto> =
        object : KmpDataStore<PreferencesProto> {
            override val data: Flow<PreferencesProto> = actualDataStore
            override suspend fun updateData(
                transform: suspend (PreferencesProto) -> PreferencesProto,
            ): PreferencesProto = actualDataStore.updateAndGet {
                transform(it)
            }
        }

    override suspend fun getDataStore(): KmpDataStore<PreferencesProto> = dataStore
}
