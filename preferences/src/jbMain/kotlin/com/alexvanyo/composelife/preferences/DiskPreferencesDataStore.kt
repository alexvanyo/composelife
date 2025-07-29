/*
 * Copyright 2022 The Android Open Source Project
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
import androidx.datastore.core.DataStoreFactory
import androidx.datastore.core.okio.OkioSerializer
import androidx.datastore.core.okio.OkioStorage
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.preferences.proto.PreferencesProto
import com.alexvanyo.composelife.updatable.Updatable
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.ContributesBinding
import dev.zacsweers.metro.ContributesIntoSet
import dev.zacsweers.metro.Inject
import dev.zacsweers.metro.Qualifier
import dev.zacsweers.metro.SingleIn
import dev.zacsweers.metro.binding
import kotlinx.coroutines.CompletableDeferred
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.awaitCancellation
import kotlinx.coroutines.coroutineScope
import kotlinx.coroutines.sync.Mutex
import kotlinx.coroutines.sync.withLock
import kotlinx.coroutines.withContext
import okio.BufferedSink
import okio.BufferedSource
import okio.FileSystem
import okio.Path
import java.io.IOException

@Qualifier
annotation class PreferencesProtoPath

@SingleIn(AppScope::class)
@ContributesBinding(AppScope::class, binding = binding<PreferencesDataStore>())
@ContributesIntoSet(AppScope::class, binding = binding<Updatable>())
@Inject
class DiskPreferencesDataStore(
    private val fileSystem: FileSystem,
    @param:PreferencesProtoPath private val path: Lazy<Path>,
    private val dispatchers: ComposeLifeDispatchers,
) : PreferencesDataStore, Updatable {
    private val mutex = Mutex()

    private val dataStoreCompletable = CompletableDeferred<DataStore<PreferencesProto>>()

    override suspend fun getDataStore(): DataStore<PreferencesProto> = dataStoreCompletable.await()

    override suspend fun update(): Nothing = mutex.withLock {
        withContext(dispatchers.IO) {
            coroutineScope {
                dataStoreCompletable.complete(createDataStore(this))
                awaitCancellation()
            }
        }
    }

    private fun createDataStore(
        scope: CoroutineScope,
    ): DataStore<PreferencesProto> =
        DataStoreFactory.create(
            storage = OkioStorage(
                fileSystem = fileSystem,
                serializer =
                object : OkioSerializer<PreferencesProto> {
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
                },
                producePath = path::value,
            ),
            corruptionHandler = null,
            migrations = listOf(
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
            ),
            scope = scope,
        )
}
