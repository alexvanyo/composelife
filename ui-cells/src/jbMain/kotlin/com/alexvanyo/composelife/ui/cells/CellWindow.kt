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
import androidx.compose.runtime.Immutable
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.unit.Dp
import androidx.compose.ui.unit.IntRect
import androidx.compose.ui.unit.dp
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

/**
 * A cell window that displays the given [gameOfLifeState] in an immutable fashion for a thumbnail.
 */
context(ctx: ThumbnailImmutableCellWindowCtxClass)
@Suppress("LongParameterList", "DEPRECATION")
@Composable
fun ThumbnailImmutableCellWindow(
    gameOfLifeState: GameOfLifeState,
    viewportInteractionConfig: ViewportInteractionConfig,
    modifier: Modifier = Modifier,
    cellDpSize: Dp = CellWindow.defaultCellDpSize,
    centerOffset: Offset = CellWindow.defaultCenterOffset,
    inOverlay: Boolean = CellWindow.defaultInOverlay,
) = ctx.invoke(gameOfLifeState, viewportInteractionConfig, modifier, cellDpSize, centerOffset, inOverlay)

context(_: CellWindowImplCtxClass)
@Suppress("LongParameterList")
@Composable
@Inject
internal fun ThumbnailImmutableCellWindowCtx(
    @Assisted gameOfLifeState: GameOfLifeState,
    @Assisted viewportInteractionConfig: ViewportInteractionConfig,
    @Assisted modifier: Modifier,
    @Assisted cellDpSize: Dp,
    @Assisted centerOffset: Offset,
    @Assisted inOverlay: Boolean,
) {
    ThumbnailImmutableCellWindowImpl(
        gameOfLifeState = gameOfLifeState,
        viewportInteractionConfig = viewportInteractionConfig,
        modifier = modifier,
        cellDpSize = cellDpSize,
        centerOffset = centerOffset,
        inOverlay = inOverlay,
    )
}

context(_: CellWindowImplCtxClass)
@Suppress("LongParameterList")
@Composable
internal fun ThumbnailImmutableCellWindowImpl(
    gameOfLifeState: GameOfLifeState,
    viewportInteractionConfig: ViewportInteractionConfig,
    modifier: Modifier = Modifier,
    cellDpSize: Dp = CellWindow.defaultCellDpSize,
    centerOffset: Offset = CellWindow.defaultCenterOffset,
    inOverlay: Boolean = CellWindow.defaultInOverlay,
) {
    CellWindowImpl(
        CellWindowUiState.ImmutableCellWindowUiState.ThumbnailState(
            gameOfLifeState = gameOfLifeState,
            viewportInteractionConfig = viewportInteractionConfig,
        ),
        cellDpSize,
        centerOffset,
        inOverlay,
        modifier,
    )
}

/**
 * A cell window that displays the given [gameOfLifeState] in an immutable fashion.
 */
context(ctx: ImmutableCellWindowCtxClass)
@Suppress("LongParameterList", "DEPRECATION")
@Composable
fun ImmutableCellWindow(
    gameOfLifeState: GameOfLifeState,
    cellWindowInteractionState: CellWindowInteractionState,
    modifier: Modifier = Modifier,
    cellDpSize: Dp = CellWindow.defaultCellDpSize,
    centerOffset: Offset = CellWindow.defaultCenterOffset,
    inOverlay: Boolean = CellWindow.defaultInOverlay,
) = ctx.invoke(gameOfLifeState, cellWindowInteractionState, modifier, cellDpSize, centerOffset, inOverlay)

context(_: CellWindowImplCtxClass)
@Suppress("LongParameterList")
@Composable
@Inject
internal fun ImmutableCellWindowCtx(
    @Assisted gameOfLifeState: GameOfLifeState,
    @Assisted cellWindowInteractionState: CellWindowInteractionState,
    @Assisted modifier: Modifier,
    @Assisted cellDpSize: Dp,
    @Assisted centerOffset: Offset,
    @Assisted inOverlay: Boolean,
) {
    CellWindowImpl(
        CellWindowUiState.ImmutableCellWindowUiState.InteractableState(
            gameOfLifeState = gameOfLifeState,
            cellWindowInteractionState = cellWindowInteractionState,
        ),
        cellDpSize,
        centerOffset,
        inOverlay,
        modifier,
    )
}

/**
 * A cell window that displays the given [gameOfLifeState] in an mutable fashion.
 *
 * The cells will be editable if and only if [isEditable] returns true.
 */
context(ctx: MutableCellWindowCtxClass)
@Suppress("LongParameterList", "DEPRECATION")
@Composable
fun MutableCellWindow(
    gameOfLifeState: MutableGameOfLifeState,
    cellWindowInteractionState: MutableCellWindowInteractionState,
    modifier: Modifier = Modifier,
    isEditable: (isGesturing: Boolean, scale: Float) -> Boolean = CellWindow.defaultIsEditable,
    cellDpSize: Dp = CellWindow.defaultCellDpSize,
    centerOffset: Offset = CellWindow.defaultCenterOffset,
    inOverlay: Boolean = CellWindow.defaultInOverlay,
) = ctx.invoke(
    gameOfLifeState,
    cellWindowInteractionState,
    modifier,
    isEditable,
    cellDpSize,
    centerOffset,
    inOverlay,
)

context(_: CellWindowImplCtxClass)
@Suppress("LongParameterList")
@Composable
@Inject
internal fun MutableCellWindowCtx(
    @Assisted gameOfLifeState: MutableGameOfLifeState,
    @Assisted cellWindowInteractionState: MutableCellWindowInteractionState,
    @Assisted modifier: Modifier,
    @Assisted isEditable: (isGesturing: Boolean, scale: Float) -> Boolean,
    @Assisted cellDpSize: Dp,
    @Assisted centerOffset: Offset,
    @Assisted inOverlay: Boolean,
) {
    CellWindowImpl(
        CellWindowUiState.MutableState(
            gameOfLifeState = gameOfLifeState,
            isEditable = isEditable,
            cellWindowInteractionState = cellWindowInteractionState,
        ),
        cellDpSize,
        centerOffset,
        inOverlay,
        modifier,
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
