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
import com.alexvanyo.composelife.database.CellStateDao
import com.alexvanyo.composelife.database.CellStateEntity
import com.alexvanyo.composelife.database.upsertCellState
import com.alexvanyo.composelife.model.CellStateFormat
import com.alexvanyo.composelife.model.DeserializationResult
import com.alexvanyo.composelife.model.FlexibleCellStateSerializer
import com.alexvanyo.composelife.model.fromFileExtension
import kotlinx.coroutines.flow.first
import javax.inject.Inject
import javax.inject.Singleton

@Singleton
class CellStateRepositoryImpl @Inject constructor(
    private val flexibleCellStateSerializer: FlexibleCellStateSerializer,
    private val cellStateDao: CellStateDao,
) : CellStateRepository {
    override suspend fun saveAutosavePattern(saveableCellState: SaveableCellState): Long {
        val fileExtension = "cells"
        val serializedCellState =
            flexibleCellStateSerializer
                .serializeToString(
                    CellStateFormat.FixedFormat.Plaintext,
                    saveableCellState.cellState,
                )
                .joinToString("\n")

        return cellStateDao.upsertCellState(
            CellStateEntity(
                id = saveableCellState.cellStateMetadata.id ?: 0,
                name = saveableCellState.cellStateMetadata.name,
                description = saveableCellState.cellStateMetadata.name,
                formatExtension = fileExtension,
                serializedCellState = serializedCellState,
                generation = saveableCellState.cellStateMetadata.generation,
                wasAutosaved = true,
            ),
        )
    }

    override suspend fun getAutosavedPattern(): SaveableCellState? {
        val cellStateEntity = cellStateDao.getMostRecentAutosavedCellState().first() ?: return null
        check(cellStateEntity.wasAutosaved)

        val deserializationResult = flexibleCellStateSerializer.deserializeToCellState(
            format = CellStateFormat.fromFileExtension(cellStateEntity.formatExtension),
            lines = cellStateEntity.serializedCellState.lineSequence(),
        )
        val cellStateMetadata = CellStateMetadata(
            id = cellStateEntity.id,
            name = cellStateEntity.name,
            description = cellStateEntity.description,
            generation = cellStateEntity.generation,
            wasAutosaved = cellStateEntity.wasAutosaved,
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
