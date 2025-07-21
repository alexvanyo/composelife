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

package com.alexvanyo.composelife.data

import androidx.compose.runtime.snapshotFlow
import androidx.work.Constraints
import androidx.work.ExistingPeriodicWorkPolicy
import androidx.work.NetworkType
import androidx.work.WorkManager
import androidx.work.await
import com.alexvanyo.composelife.preferences.ComposeLifePreferences
import com.alexvanyo.composelife.resourcestate.successes
import com.alexvanyo.composelife.updatable.Updatable
import kotlinx.coroutines.flow.collect
import kotlinx.coroutines.flow.distinctUntilChanged
import kotlinx.coroutines.flow.first
import kotlinx.coroutines.flow.map
import kotlinx.coroutines.flow.onEach
import kotlinx.coroutines.guava.await
import dev.zacsweers.metro.Inject
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.ContributesIntoSet
import dev.zacsweers.metro.SingleIn
import dev.zacsweers.metro.binding

@Inject
@ContributesIntoSet(AppScope::class, binding = binding<Updatable>())
@SingleIn(AppScope::class)
class PatternCollectionSync(
    private val composeLifePreferences: ComposeLifePreferences,
    workManager: Lazy<WorkManager>,
) : Updatable {
    private val workManager by workManager

    override suspend fun update(): Nothing {
        val workInfos = workManager
            .getWorkInfosForUniqueWorkFlow(PATTERN_COLLECTIONS_SYNC_NAME)
            .first()

        var id = if (workInfos.isEmpty()) {
            null
        } else {
            assert(workInfos.size == 1)
            workInfos.first().id
        }

        snapshotFlow {
            composeLifePreferences.loadedPreferencesState
        }
            .successes()
            .map { loadedPreferences ->
                loadedPreferences.value.synchronizePatternCollectionsOnMeteredNetwork to
                    loadedPreferences.value.patternCollectionsSynchronizationPeriodSessionValue.value
            }
            .distinctUntilChanged()
            .onEach { (synchronizePatternCollectionsOnMeteredNetwork, patternCollectionsSynchronizationPeriod) ->
                val requestBuilderWithoutId = PeriodicWorkRequestBuilder<PatternCollectionSyncWorker>(
                    repeatPeriod = patternCollectionsSynchronizationPeriod,
                )
                    .setConstraints(
                        Constraints.Builder()
                            .setRequiredNetworkType(
                                if (synchronizePatternCollectionsOnMeteredNetwork) {
                                    NetworkType.CONNECTED
                                } else {
                                    NetworkType.UNMETERED
                                }
                            )
                            .build()
                    )

                if (id == null) {
                    val request = requestBuilderWithoutId.build()
                    workManager.enqueueUniquePeriodicWork(
                        uniqueWorkName = PATTERN_COLLECTIONS_SYNC_NAME,
                        existingPeriodicWorkPolicy = ExistingPeriodicWorkPolicy.UPDATE,
                        request = request
                    )
                        .await()
                    id = request.id
                } else {
                    workManager.updateWork(
                        request = requestBuilderWithoutId.setId(id).build()
                    )
                        .await()
                }
            }
            .collect()

        error("snapshotFlow can not complete normally")
    }

    companion object {
        private const val PATTERN_COLLECTIONS_SYNC_NAME = "PatternCollectionSync"
    }
}
