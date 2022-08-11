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
import androidx.room.Insert
import androidx.room.OnConflictStrategy
import androidx.room.Query
import androidx.room.Transaction
import androidx.room.Update
import kotlinx.coroutines.flow.Flow

@Dao
interface CellStateDao {

    @Query("SELECT * FROM CellStateEntity")
    fun getCellStates(): Flow<List<CellStateEntity>>

    @Query("SELECT * FROM CellStateEntity WHERE id = :id")
    fun getCellStateById(id: Int): Flow<CellStateEntity?>

    @Query("SELECT * FROM CellStateEntity WHERE wasAutosaved = 1")
    fun getMostRecentAutosavedCellState(): Flow<CellStateEntity?>

    @Insert(onConflict = OnConflictStrategy.IGNORE)
    suspend fun insertOrIgnoreCellStates(cellStates: List<CellStateEntity>): List<Long>

    @Update
    suspend fun updateCellStates(cellStates: List<CellStateEntity>)

    @Transaction
    suspend fun upsertCellStates(cellStates: List<CellStateEntity>): List<Long> =
        upsert(cellStates, CellStateEntity::id, ::insertOrIgnoreCellStates, ::updateCellStates)

    @Query("DELETE FROM CellStateEntity WHERE id = :id")
    suspend fun deleteCellState(id: Int)
}

suspend fun CellStateDao.upsertCellState(
    cellState: CellStateEntity,
): Long = upsertCellStates(listOf(cellState)).first()
