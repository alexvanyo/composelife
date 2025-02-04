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

import androidx.compose.foundation.draganddrop.dragAndDropTarget
import androidx.compose.runtime.Composable
import androidx.compose.ui.Modifier
import androidx.compose.ui.draganddrop.DragAndDropEvent
import androidx.compose.ui.layout.onGloballyPositioned
import androidx.compose.ui.layout.positionInRoot
import com.alexvanyo.composelife.model.CellState

/**
 * A [Modifier] for a drag-and-drop source for a [CellState].
 */
@Composable
expect fun Modifier.cellStateDragAndDropSource(getCellState: () -> CellState): Modifier

/**
 * A [Modifier] for a drag-and-drop target for a [CellState].
 */
@Composable
fun Modifier.cellStateDragAndDropTarget(
    mutableCellStateDropStateHolder: MutableCellStateDropStateHolder,
): Modifier {
    when (mutableCellStateDropStateHolder) {
        is MutableCellStateDropStateHolderImpl -> Unit
    }

    return onGloballyPositioned { coordinates ->
        mutableCellStateDropStateHolder.positionInRoot = coordinates.positionInRoot()
    }
        .dragAndDropTarget(
            shouldStartDragAndDrop = ::cellStateShouldStartDragAndDrop,
            target = mutableCellStateDropStateHolder,
        )
}

/**
 * Returns `true` if the drag-and-drop should start for the [cellStateDragAndDropTarget].
 */
internal expect fun cellStateShouldStartDragAndDrop(event: DragAndDropEvent): Boolean
