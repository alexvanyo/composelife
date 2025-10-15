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
import app.cash.sqldelight.async.coroutines.awaitAsOneOrNull
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import dev.zacsweers.metro.Inject
import kotlinx.coroutines.withContext

@Inject
class CellStateQueriesWrapper(
    val dispatchers: ComposeLifeDispatchers,
    val composeLifeDriver: ComposeLifeDriver,
    val queries: CellStateQueries,
) {
    suspend fun getCellStates() =
        withContext(dispatchers.IO) {
            composeLifeDriver.awaitDriverReady()
            queries.getCellStates().awaitAsList()
        }

    suspend fun getAutosavedCellStates() =
        withContext(dispatchers.IO) {
            composeLifeDriver.awaitDriverReady()
            queries.getAutosavedCellStates().awaitAsList()
        }

    suspend fun getMostRecentAutosavedCellState() =
        withContext(dispatchers.IO) {
            composeLifeDriver.awaitDriverReady()
            queries.getMostRecentAutosavedCellState().awaitAsOneOrNull()
        }

    suspend fun getCellStatesByPatternCollectionId(patternCollectionId: PatternCollectionId) =
        withContext(dispatchers.IO) {
            composeLifeDriver.awaitDriverReady()
            queries.getCellStatesByPatternCollectionId(patternCollectionId).awaitAsList()
        }

    @Suppress("LongParameterList")
    suspend fun upsertCellState(
        id: CellStateId?,
        name: String?,
        description: String?,
        formatExtension: String?,
        serializedCellState: String?,
        serializedCellStateFile: String?,
        generation: Long,
        wasAutosaved: Boolean,
        patternCollectionId: PatternCollectionId?,
    ): CellStateId = withContext(dispatchers.IO) {
        composeLifeDriver.awaitDriverReady()
        queries.transactionWithResult {
            if (id == null) {
                queries.insertCellState(
                    name = name,
                    description = description,
                    formatExtension = formatExtension,
                    serializedCellState = serializedCellState,
                    serializedCellStateFile = serializedCellStateFile,
                    generation = generation,
                    wasAutosaved = wasAutosaved,
                    patternCollectionId = patternCollectionId,
                )
                CellStateId(queries.lastInsertedRowId().awaitAsOne())
            } else {
                queries.updateCellState(
                    id = id,
                    name = name,
                    description = description,
                    formatExtension = formatExtension,
                    serializedCellState = serializedCellState,
                    serializedCellStateFile = serializedCellStateFile,
                    generation = generation,
                    wasAutosaved = wasAutosaved,
                    patternCollectionId = patternCollectionId,
                )
                id
            }
        }
    }

    suspend fun deleteCellState(
        id: CellStateId,
    ) =
        withContext(dispatchers.IO) {
            composeLifeDriver.awaitDriverReady()
            queries.deleteCellState(id)
        }
}
