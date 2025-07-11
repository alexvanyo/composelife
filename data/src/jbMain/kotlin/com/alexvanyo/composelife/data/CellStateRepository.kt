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

import com.alexvanyo.composelife.data.model.SaveableCellState
import com.alexvanyo.composelife.database.CellStateId

interface CellStateRepository {
    /**
     * Returns the most recent autosaved cell state, if any.
     *
     * If there is none, or deserialization failed for an unknown reason, `null` will be returned instead.
     */
    suspend fun getAutosavedCellState(): SaveableCellState?

    /**
     * Returns all autosaved cell states.
     */
    suspend fun getAutosavedCellStates(): List<SaveableCellState>

    /**
     * Returns all cell states.
     */
    suspend fun getCellStates(): List<SaveableCellState>

    /**
     * Saves the given [saveableCellState] as an autosaved cell state.
     *
     * @return the id of the saved entry.
     */
    suspend fun autosaveCellState(saveableCellState: SaveableCellState): CellStateId

    /**
     * Cleans out any cell state files that aren't referenced by the database.
     *
     * @return true if all unused cell states were removed successfully.
     */
    suspend fun pruneUnusedCellStates(): Boolean
}
