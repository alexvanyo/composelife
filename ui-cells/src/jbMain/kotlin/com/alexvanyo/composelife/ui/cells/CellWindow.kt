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

package com.alexvanyo.composelife.ui.cells

import androidx.compose.runtime.Composable
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.unit.Dp
import androidx.compose.ui.unit.IntRect
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.di.InjectContext
import com.alexvanyo.composelife.model.CellState
import com.alexvanyo.composelife.model.GameOfLifeState
import com.alexvanyo.composelife.model.MutableGameOfLifeState
import com.alexvanyo.composelife.sessionvalue.SessionValue
import dev.zacsweers.metro.Assisted
import dev.zacsweers.metro.Inject
import kotlin.uuid.Uuid

object CellWindow {
    val defaultIsEditable: (isGesturing: Boolean, scale: Float) -> Boolean =
        { isGesturing, scale ->
            !isGesturing && scale >= 1f
        }
    val defaultCellDpSize = 48.dp
    val defaultCenterOffset = Offset(0.5f, 0.5f)
    const val defaultInOverlay = false
}

@InjectContext
@Inject
@Suppress("LongParameterList")
@Composable
context(_: CellWindowImpl)
fun ThumbnailImmutableCellWindow(
    @Assisted gameOfLifeState: GameOfLifeState,
    @Assisted viewportInteractionConfig: ViewportInteractionConfig,
    @Assisted modifier: Modifier = Modifier,
    @Assisted cellDpSize: Dp = CellWindow.defaultCellDpSize,
    @Assisted centerOffset: Offset = CellWindow.defaultCenterOffset,
    @Assisted inOverlay: Boolean = CellWindow.defaultInOverlay,
) {
    CellWindowImpl(
        cellWindowUiState = CellWindowUiState.ImmutableCellWindowUiState.ThumbnailState(
            gameOfLifeState = gameOfLifeState,
            viewportInteractionConfig = viewportInteractionConfig,
        ),
        cellDpSize = cellDpSize,
        centerOffset = centerOffset,
        inOverlay = inOverlay,
        modifier = modifier,
    )
}

@InjectContext
@Inject
@Suppress("LongParameterList")
@Composable
context(_: CellWindowImpl)
fun ImmutableCellWindow(
    @Assisted gameOfLifeState: GameOfLifeState,
    @Assisted cellWindowInteractionState: CellWindowInteractionState,
    @Assisted modifier: Modifier = Modifier,
    @Assisted cellDpSize: Dp = CellWindow.defaultCellDpSize,
    @Assisted centerOffset: Offset = CellWindow.defaultCenterOffset,
    @Assisted inOverlay: Boolean = CellWindow.defaultInOverlay,
) {
    CellWindowImpl(
        cellWindowUiState = CellWindowUiState.ImmutableCellWindowUiState.InteractableState(
            gameOfLifeState = gameOfLifeState,
            cellWindowInteractionState = cellWindowInteractionState,
        ),
        cellDpSize = cellDpSize,
        centerOffset = centerOffset,
        inOverlay = inOverlay,
        modifier = modifier,
    )
}

@InjectContext
@Inject
@Suppress("LongParameterList")
@Composable
context(_: CellWindowImpl)
fun MutableCellWindow(
    @Assisted gameOfLifeState: MutableGameOfLifeState,
    @Assisted cellWindowInteractionState: MutableCellWindowInteractionState,
    @Assisted modifier: Modifier = Modifier,
    @Assisted isEditable: (isGesturing: Boolean, scale: Float) -> Boolean = CellWindow.defaultIsEditable,
    @Assisted cellDpSize: Dp = CellWindow.defaultCellDpSize,
    @Assisted centerOffset: Offset = CellWindow.defaultCenterOffset,
    @Assisted inOverlay: Boolean = CellWindow.defaultInOverlay,
) {
    CellWindowImpl(
        cellWindowUiState = CellWindowUiState.MutableState(
            gameOfLifeState = gameOfLifeState,
            isEditable = isEditable,
            cellWindowInteractionState = cellWindowInteractionState,
        ),
        cellDpSize = cellDpSize,
        centerOffset = centerOffset,
        inOverlay = inOverlay,
        modifier = modifier,
    )
}

internal sealed interface CellWindowUiState {

    val gameOfLifeState: GameOfLifeState

    val cellWindowInteractionState: CellWindowInteractionState

    sealed interface ImmutableCellWindowUiState : CellWindowUiState {
        class InteractableState(
            override val gameOfLifeState: GameOfLifeState,
            override val cellWindowInteractionState: CellWindowInteractionState,
        ) : ImmutableCellWindowUiState

        class ThumbnailState(
            override val gameOfLifeState: GameOfLifeState,
            viewportInteractionConfig: ViewportInteractionConfig,
        ) : ImmutableCellWindowUiState {
            override val cellWindowInteractionState = CellWindowInteractionState(
                viewportInteractionConfig = viewportInteractionConfig,
                selectionSessionState = SessionValue(Uuid.random(), Uuid.random(), SelectionState.NoSelection),
            )
        }
    }

    class MutableState(
        override val gameOfLifeState: MutableGameOfLifeState,
        override val cellWindowInteractionState: MutableCellWindowInteractionState,
        val isEditable: (isGesturing: Boolean, scale: Float) -> Boolean,
    ) : CellWindowUiState
}

/**
 * Returns the [CellState] that is selected by the given [selectionState] in this [CellState].
 */
fun CellState.getSelectedCellState(selectionState: SelectionState.SelectingBox.FixedSelectingBox): CellState {
    val left: Int
    val right: Int

    if (selectionState.width < 0) {
        left = selectionState.topLeft.x + selectionState.width + 1
        right = selectionState.topLeft.x + 1
    } else {
        left = selectionState.topLeft.x
        right = selectionState.topLeft.x + selectionState.width
    }

    val top: Int
    val bottom: Int

    if (selectionState.height < 0) {
        top = selectionState.topLeft.y + selectionState.height + 1
        bottom = selectionState.topLeft.y + 1
    } else {
        top = selectionState.topLeft.y
        bottom = selectionState.topLeft.y + selectionState.height
    }

    val cellWindow = com.alexvanyo.composelife.model.CellWindow(
        IntRect(
            left = left,
            top = top,
            right = right,
            bottom = bottom,
        ),
    )

    val aliveCells = getAliveCellsInWindow(cellWindow).toSet()

    return CellState(aliveCells)
}
