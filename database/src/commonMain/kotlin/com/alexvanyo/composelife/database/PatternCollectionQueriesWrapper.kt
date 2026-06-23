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

package com.alexvanyo.composelife.database

import app.cash.sqldelight.async.coroutines.awaitAsList
import app.cash.sqldelight.async.coroutines.awaitAsOne
import app.cash.sqldelight.coroutines.asFlow
import app.cash.sqldelight.coroutines.mapToList
import dev.zacsweers.metro.Inject
import kotlinx.coroutines.flow.Flow
import kotlin.coroutines.EmptyCoroutineContext
import kotlin.time.Instant

@Inject
class PatternCollectionQueriesWrapper(val queries: PatternCollectionQueries) {
    fun observePatternCollections(): Flow<List<PatternCollection>> =
        queries.getPatternCollections().asFlow().mapToList(EmptyCoroutineContext)

    suspend fun getPatternCollections(): List<PatternCollection> = queries.getPatternCollections().awaitAsList()

    suspend fun insertPatternCollection(
        sourceUrl: String,
        lastSuccessfulSynchronizationTimestamp: Instant?,
        lastUnsuccessfulSynchronizationTimestamp: Instant?,
        synchronizationFailureMessage: String?,
    ): PatternCollectionId = queries.transactionWithResult {
        queries.insertPatternCollection(
            sourceUrl = sourceUrl,
            lastSuccessfulSynchronizationTimestamp = lastSuccessfulSynchronizationTimestamp,
            lastUnsuccessfulSynchronizationTimestamp = lastUnsuccessfulSynchronizationTimestamp,
            synchronizationFailureMessage = synchronizationFailureMessage,
        )
        PatternCollectionId(queries.lastInsertedRowId().awaitAsOne())
    }

    suspend fun updatePatternCollection(
        id: PatternCollectionId,
        sourceUrl: String,
        lastSuccessfulSynchronizationTimestamp: Instant?,
        lastUnsuccessfulSynchronizationTimestamp: Instant?,
        synchronizationFailureMessage: String?,
    ) = queries.updatePatternCollection(
        id = id,
        sourceUrl = sourceUrl,
        lastSuccessfulSynchronizationTimestamp = lastSuccessfulSynchronizationTimestamp,
        lastUnsuccessfulSynchronizationTimestamp = lastUnsuccessfulSynchronizationTimestamp,
        synchronizationFailureMessage = synchronizationFailureMessage,
    )

    suspend fun deletePatternCollection(id: PatternCollectionId) = queries.deletePatternCollection(
        id = id,
    )
}
