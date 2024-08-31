/*
 * Copyright 2024 The Android Open Source Project
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

package com.alexvanyo.composelife.ui.cells

import androidx.compose.ui.geometry.Offset
import com.alexvanyo.composelife.model.CellState

sealed interface CellStateDropState {

    /**
     * There is no active drop for the cell state
     */
    data object None : CellStateDropState

    /**
     * There is an active drop for the cell state in progress, but isn't previewable.
     */
    data object ApplicableDropAvailable : CellStateDropState

    /**
     * There is an active previewable drop for the cell state
     */
    data class DropPreview(
        val offset: Offset,
        val cellState: CellState,
    ) : CellStateDropState
}

interface CellStateDropStateHolder {
    val cellStateDropState: CellStateDropState
}

interface MutableCellStateDropStateHolder : CellStateDropStateHolder {
    override var cellStateDropState: CellStateDropState
}
