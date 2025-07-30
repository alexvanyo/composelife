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

import androidx.work.ExistingPeriodicWorkPolicy
import androidx.work.WorkManager
import androidx.work.await
import com.alexvanyo.composelife.updatable.AppUpdatable
import com.alexvanyo.composelife.updatable.Updatable
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.BindingContainer
import dev.zacsweers.metro.Binds
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.Inject
import dev.zacsweers.metro.IntoSet
import dev.zacsweers.metro.SingleIn
import kotlinx.coroutines.awaitCancellation
import kotlinx.coroutines.flow.first
import kotlinx.coroutines.guava.await
import kotlinx.datetime.DateTimePeriod

@ContributesTo(AppScope::class)
@BindingContainer
interface CellStateCleanupBindings {
    @Binds
    @IntoSet
    @AppUpdatable
    val CellStateCleanup.bindIntoUpdatable: Updatable
}

@Inject
@SingleIn(AppScope::class)
class CellStateCleanup(
    workManager: Lazy<WorkManager>,
) : Updatable {
    private val workManager by workManager

    override suspend fun update(): Nothing {
        val workInfos = workManager
            .getWorkInfosForUniqueWorkFlow(CELL_STATE_CLEANUP_NAME)
            .first()

        val id = if (workInfos.isEmpty()) {
            null
        } else {
            assert(workInfos.size == 1)
            workInfos.first().id
        }

        val requestBuilderWithoutId = PeriodicWorkRequestBuilder<CellStateCleanupWorker>(
            repeatPeriod = DateTimePeriod(days = 1),
        )

        if (id == null) {
            val request = requestBuilderWithoutId.build()
            workManager.enqueueUniquePeriodicWork(
                uniqueWorkName = CELL_STATE_CLEANUP_NAME,
                existingPeriodicWorkPolicy = ExistingPeriodicWorkPolicy.UPDATE,
                request = request,
            )
                .await()
        } else {
            workManager.updateWork(
                request = requestBuilderWithoutId.setId(id).build(),
            )
                .await()
        }

        awaitCancellation()
    }

    companion object {
        private const val CELL_STATE_CLEANUP_NAME = "CellStateCleanup"
    }
}
