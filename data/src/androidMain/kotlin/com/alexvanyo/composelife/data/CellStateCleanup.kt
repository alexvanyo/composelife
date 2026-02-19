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
import androidx.work.ExistingPeriodicWorkPolicy
import androidx.work.WorkManager
import androidx.work.await
import com.alexvanyo.composelife.preferences.ComposeLifePreferences
import com.alexvanyo.composelife.resourcestate.successes
import com.alexvanyo.composelife.updatable.Updatable
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.ContributesIntoSet
import dev.zacsweers.metro.ForScope
import dev.zacsweers.metro.Inject
import dev.zacsweers.metro.SingleIn
import dev.zacsweers.metro.binding
import kotlinx.coroutines.flow.collect
import kotlinx.coroutines.flow.distinctUntilChanged
import kotlinx.coroutines.flow.map
import kotlinx.coroutines.flow.onEach

@Inject
@SingleIn(AppScope::class)
@ContributesIntoSet(AppScope::class, binding = binding<
    @ForScope(AppScope::class)
    Updatable,
    >())
class CellStateCleanup(
    private val composeLifePreferences: ComposeLifePreferences,
    workManager: Lazy<WorkManager>,
) : Updatable {
    private val workManager by workManager

    override suspend fun update(): Nothing {
        snapshotFlow {
            composeLifePreferences.loadedPreferencesState
        }
            .successes()
            .map { loadedPreferences ->
                loadedPreferences.value.cellStatePruningPeriodSessionValue.value
            }
            .distinctUntilChanged()
            .onEach { cellStatePruningPeriod ->
                workManager.enqueueUniquePeriodicWork(
                    uniqueWorkName = CELL_STATE_CLEANUP_NAME,
                    existingPeriodicWorkPolicy = ExistingPeriodicWorkPolicy.UPDATE,
                    request = PeriodicWorkRequestBuilder<CellStateCleanupWorker>(
                        repeatPeriod = cellStatePruningPeriod,
                    ).build(),
                )
                    .await()
            }
            .collect()

        error("snapshotFlow can not complete normally")
    }

    companion object {
        private const val CELL_STATE_CLEANUP_NAME = "CellStateCleanup"
    }
}
