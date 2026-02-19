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

import androidx.datastore.core.CorruptionException
import androidx.datastore.core.DataMigration
import androidx.datastore.core.DataStore
import androidx.datastore.core.handlers.ReplaceFileCorruptionHandler
import androidx.datastore.core.okio.OkioSerializer
import com.alexvanyo.composelife.preferences.proto.PreferencesProto
import okio.BufferedSink
import okio.BufferedSource
import okio.IOException

interface PreferencesDataStore {
    suspend fun getDataStore(): DataStore<PreferencesProto>
}

internal val defaultPreferencesProto = PreferencesProto(
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
    cell_state_pruning_period_session_id = LoadedComposeLifePreferences
        .defaultCellStatePruningPeriodSessionId
        .toProto(),
    cell_state_pruning_period_value_id = LoadedComposeLifePreferences
        .defaultCellStatePruningPeriodValueId
        .toProto(),
)

internal val serializer = object : OkioSerializer<PreferencesProto> {
    override val defaultValue: PreferencesProto
        get() = PreferencesProto()

    override suspend fun readFrom(source: BufferedSource): PreferencesProto =
        try {
            PreferencesProto.ADAPTER.decode(source)
        } catch (exception: IOException) {
            throw CorruptionException("Cannot read proto.", exception)
        }

    override suspend fun writeTo(t: PreferencesProto, sink: BufferedSink) =
        PreferencesProto.ADAPTER.encode(sink, t)
}

internal val corruptionHandler = ReplaceFileCorruptionHandler { defaultPreferencesProto }

internal val migrations =
    listOf(
        object : DataMigration<PreferencesProto> {
            override suspend fun shouldMigrate(currentData: PreferencesProto): Boolean =
                currentData.round_rectangle_session_id == null

            override suspend fun migrate(currentData: PreferencesProto): PreferencesProto =
                currentData.copy(
                    round_rectangle_session_id = LoadedComposeLifePreferences
                        .defaultRoundRectangleSessionId
                        .toProto(),
                    round_rectangle_value_id = LoadedComposeLifePreferences
                        .defaultRoundRectangleValueId
                        .toProto(),
                )

            override suspend fun cleanUp() = Unit
        },
        object : DataMigration<PreferencesProto> {
            override suspend fun shouldMigrate(currentData: PreferencesProto): Boolean =
                currentData.pattern_collections_synchronization_period_session_id == null

            override suspend fun migrate(currentData: PreferencesProto): PreferencesProto =
                currentData.copy(
                    pattern_collections_synchronization_period_session_id = LoadedComposeLifePreferences
                        .defaultPatternCollectionsSynchronizationPeriodSessionId
                        .toProto(),
                    pattern_collections_synchronization_period_value_id = LoadedComposeLifePreferences
                        .defaultPatternCollectionsSynchronizationPeriodValueId
                        .toProto(),
                )

            override suspend fun cleanUp() = Unit
        },
        object : DataMigration<PreferencesProto> {
            override suspend fun shouldMigrate(currentData: PreferencesProto): Boolean =
                currentData.cell_state_pruning_period_session_id == null

            override suspend fun migrate(currentData: PreferencesProto): PreferencesProto =
                currentData.copy(
                    cell_state_pruning_period_session_id = LoadedComposeLifePreferences
                        .defaultCellStatePruningPeriodSessionId
                        .toProto(),
                    cell_state_pruning_period_value_id = LoadedComposeLifePreferences
                        .defaultCellStatePruningPeriodValueId
                        .toProto(),
                )

            override suspend fun cleanUp() = Unit
        },
    )
