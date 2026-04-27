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
import dev.zacsweers.metro.Inject

@Inject
class CellStateQueriesWrapper(
    val queries: CellStateQueries,
) {
    suspend fun getCellStates() =
        queries.getCellStates().awaitAsList()

    suspend fun getAutosavedCellStates() =
        queries.getAutosavedCellStates().awaitAsList()

    suspend fun getMostRecentAutosavedCellState() =
        queries.getMostRecentAutosavedCellState().awaitAsOneOrNull()

    suspend fun getCellStatesByPatternCollectionId(patternCollectionId: PatternCollectionId) =
        queries.getCellStatesByPatternCollectionId(patternCollectionId).awaitAsList()

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
    ): CellStateId =
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

    suspend fun deleteCellState(
        id: CellStateId,
    ) =
        queries.deleteCellState(id)
}
