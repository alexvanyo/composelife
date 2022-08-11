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

package com.alexvanyo.composelife.database

import androidx.room.Dao
import androidx.room.Query
import androidx.room.Upsert
import kotlinx.coroutines.flow.Flow

@Dao
interface CellStateDao {

    @Query("SELECT * FROM CellStateEntity")
    fun getCellStates(): Flow<List<CellStateEntity>>

    @Query("SELECT * FROM CellStateEntity WHERE id = :id")
    fun getCellStateById(id: Long): Flow<CellStateEntity?>

    @Query("SELECT * FROM CellStateEntity WHERE wasAutosaved = 1")
    fun getMostRecentAutosavedCellState(): Flow<CellStateEntity?>

    @Upsert
    suspend fun upsertCellStates(cellStates: List<CellStateEntity>): List<Long>

    @Query("DELETE FROM CellStateEntity WHERE id = :id")
    suspend fun deleteCellState(id: Long)
}

suspend fun CellStateDao.upsertCellState(
    cellState: CellStateEntity,
): Long = upsertCellStates(listOf(cellState)).first()
