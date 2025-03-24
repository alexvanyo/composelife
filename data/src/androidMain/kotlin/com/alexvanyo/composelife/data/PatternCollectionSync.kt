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
import androidx.work.ListenableWorker
import androidx.work.NetworkType
import androidx.work.PeriodicWorkRequest
import androidx.work.PeriodicWorkRequestBuilder
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
import kotlinx.datetime.DateTimePeriod
import me.tatarka.inject.annotations.Inject
import software.amazon.lastmile.kotlin.inject.anvil.AppScope
import software.amazon.lastmile.kotlin.inject.anvil.ContributesBinding
import software.amazon.lastmile.kotlin.inject.anvil.SingleIn
import java.util.concurrent.TimeUnit
import kotlin.time.Duration.Companion.days
import kotlin.time.Duration.Companion.hours
import kotlin.time.Duration.Companion.minutes
import kotlin.time.Duration.Companion.nanoseconds
import kotlin.time.Duration.Companion.seconds

@Inject
@ContributesBinding(AppScope::class, boundType = Updatable::class, multibinding = true)
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
                    loadedPreferences.value.patternCollectionsSynchronizationPeriod
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

inline fun <reified T : ListenableWorker> PeriodicWorkRequestBuilder(
    repeatPeriod: DateTimePeriod,
): PeriodicWorkRequest.Builder =
    PeriodicWorkRequestBuilder<T>(
        repeatInterval = (repeatPeriod.nanoseconds.nanoseconds +
                repeatPeriod.seconds.seconds +
                repeatPeriod.minutes.minutes +
                repeatPeriod.hours.hours +
                repeatPeriod.days.days +
                ((repeatPeriod.months / 12.0 + repeatPeriod.years) * 365.2422).days).inWholeMilliseconds,
        repeatIntervalTimeUnit = TimeUnit.MILLISECONDS,
    )
