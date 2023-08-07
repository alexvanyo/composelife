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

package com.alexvanyo.composelife.data

import com.alexvanyo.composelife.data.model.CellStateMetadata
import com.alexvanyo.composelife.data.model.SaveableCellState
import com.alexvanyo.composelife.database.CellStateId
import com.alexvanyo.composelife.database.CellStateQueries
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.model.CellStateFormat
import com.alexvanyo.composelife.model.DeserializationResult
import com.alexvanyo.composelife.model.FlexibleCellStateSerializer
import com.alexvanyo.composelife.model.fromFileExtension
import kotlinx.coroutines.withContext
import me.tatarka.inject.annotations.Inject

class CellStateRepositoryImpl @Inject constructor(
    private val flexibleCellStateSerializer: FlexibleCellStateSerializer,
    private val cellStateQueries: CellStateQueries,
    private val dispatchers: ComposeLifeDispatchers,
) : CellStateRepository {
    override suspend fun autosaveCellState(saveableCellState: SaveableCellState): CellStateId {
        val fileExtension = "rle"
        val serializedCellState =
            flexibleCellStateSerializer
                .serializeToString(
                    CellStateFormat.FixedFormat.RunLengthEncoding,
                    saveableCellState.cellState,
                )
                .joinToString("\n")

        @Suppress("InjectDispatcher")
        val insertedId = withContext(dispatchers.IO) {
            cellStateQueries.transactionWithResult {
                if (saveableCellState.cellStateMetadata.id == null) {
                    cellStateQueries.insertCellState(
                        name = saveableCellState.cellStateMetadata.name,
                        description = saveableCellState.cellStateMetadata.description,
                        formatExtension = fileExtension,
                        serializedCellState = serializedCellState,
                        generation = saveableCellState.cellStateMetadata.generation,
                        wasAutosaved = true,
                    )
                    CellStateId(cellStateQueries.lastInsertedRowId().executeAsOne())
                } else {
                    cellStateQueries.updateCellState(
                        id = saveableCellState.cellStateMetadata.id,
                        name = saveableCellState.cellStateMetadata.name,
                        description = saveableCellState.cellStateMetadata.description,
                        formatExtension = fileExtension,
                        serializedCellState = serializedCellState,
                        generation = saveableCellState.cellStateMetadata.generation,
                        wasAutosaved = true,
                    )
                    saveableCellState.cellStateMetadata.id
                }
            }
        }

        return insertedId
    }

    override suspend fun getAutosavedCellState(): SaveableCellState? {
        @Suppress("InjectDispatcher")
        val cellState = withContext(dispatchers.IO) {
            cellStateQueries.getMostRecentAutosavedCellState().executeAsOneOrNull()
        } ?: return null
        check(cellState.wasAutosaved)

        val deserializationResult = flexibleCellStateSerializer.deserializeToCellState(
            format = CellStateFormat.fromFileExtension(cellState.formatExtension),
            lines = cellState.serializedCellState.lineSequence(),
        )
        val cellStateMetadata = CellStateMetadata(
            id = cellState.id,
            name = cellState.name,
            description = cellState.description,
            generation = cellState.generation,
            wasAutosaved = cellState.wasAutosaved,
        )

        return when (deserializationResult) {
            is DeserializationResult.Successful -> SaveableCellState(
                cellState = deserializationResult.cellState,
                cellStateMetadata = cellStateMetadata,
            )
            is DeserializationResult.Unsuccessful -> null
        }
    }
}
