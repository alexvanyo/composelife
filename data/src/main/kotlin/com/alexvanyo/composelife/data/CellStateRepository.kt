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

interface CellStateRepository {
    /**
     * Returns the most recent auto-saved pattern, if any.
     *
     * If there is none, or deserialization failed for an unknown reason, `null` will be returned instead.
     */
    suspend fun getAutosavedPattern(): SaveableCellState?

    /**
     * Saves the given [saveableCellState] as an autosaved pattern.
     */
    suspend fun saveAutosavePattern(saveableCellState: SaveableCellState): Long
}
