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

import androidx.compose.animation.core.AnimationSpec
import androidx.compose.animation.core.AnimationVector
import androidx.compose.animation.core.SnapSpec
import androidx.compose.animation.core.TwoWayConverter
import androidx.compose.animation.core.animateValueAsState
import androidx.compose.animation.core.snap
import androidx.compose.animation.core.spring
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.BoxWithConstraints
import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.runtime.Composable
import androidx.compose.runtime.DisposableEffect
import androidx.compose.runtime.Immutable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberUpdatedState
import androidx.compose.runtime.setValue
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.input.pointer.PointerEventType
import androidx.compose.ui.input.pointer.PointerType
import androidx.compose.ui.input.pointer.pointerInput
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.semantics.ScrollAxisRange
import androidx.compose.ui.semantics.horizontalScrollAxisRange
import androidx.compose.ui.semantics.scrollBy
import androidx.compose.ui.semantics.scrollToIndex
import androidx.compose.ui.semantics.semantics
import androidx.compose.ui.semantics.verticalScrollAxisRange
import androidx.compose.ui.unit.Dp
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.IntRect
import androidx.compose.ui.unit.IntSize
import androidx.compose.ui.unit.dp
import androidx.compose.ui.unit.toOffset
import com.alexvanyo.composelife.geometry.floor
import com.alexvanyo.composelife.geometry.toRingOffset
import com.alexvanyo.composelife.model.CellState
import com.alexvanyo.composelife.model.CellStateParser
import com.alexvanyo.composelife.model.GameOfLifeState
import com.alexvanyo.composelife.model.MutableGameOfLifeState
import com.alexvanyo.composelife.model.emptyCellState
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferencesHolder
import com.alexvanyo.composelife.preferences.ToolConfig
import com.alexvanyo.composelife.sessionvalue.SessionValue
import com.alexvanyo.composelife.ui.util.detectTransformGestures
import dev.zacsweers.metro.Inject
import kotlinx.coroutines.currentCoroutineContext
import kotlinx.coroutines.isActive
import kotlin.contracts.ExperimentalContracts
import kotlin.contracts.contract
import kotlin.math.ceil
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

@Immutable
@Inject
class ThumbnailImmutableCellWindowEntryPoint internal constructor(
    private val cellWindowImplEntryPoint: CellWindowImplEntryPoint,
) {
    @Suppress("ComposableNaming", "LongParameterList")
    @Composable
    operator fun invoke(
        gameOfLifeState: GameOfLifeState,
        viewportInteractionConfig: ViewportInteractionConfig,
        modifier: Modifier = Modifier,
        cellDpSize: Dp = CellWindow.defaultCellDpSize,
        centerOffset: Offset = CellWindow.defaultCenterOffset,
        inOverlay: Boolean = CellWindow.defaultInOverlay,
    ) = lambda(
        cellWindowImplEntryPoint,
        gameOfLifeState,
        viewportInteractionConfig,
        modifier,
        cellDpSize,
        centerOffset,
        inOverlay,
    )

    companion object {
        private val lambda:
            @Composable
            context(
                CellWindowImplEntryPoint,
            ) (
                gameOfLifeState: GameOfLifeState,
                viewportInteractionConfig: ViewportInteractionConfig,
                modifier: Modifier,
                cellDpSize: Dp,
                centerOffset: Offset,
                inOverlay: Boolean,
            ) -> Unit =
            { gameOfLifeState, viewportInteractionConfig, modifier, cellDpSize, centerOffset, inOverlay ->
                ThumbnailImmutableCellWindow(
                    gameOfLifeState = gameOfLifeState,
                    viewportInteractionConfig = viewportInteractionConfig,
                    modifier = modifier,
                    cellDpSize = cellDpSize,
                    centerOffset = centerOffset,
                    inOverlay = inOverlay,
                )
            }
    }
}

/**
 * A cell window that displays the given [gameOfLifeState] in an immutable fashion for a thumbnail.
 */
context(entryPoint: ThumbnailImmutableCellWindowEntryPoint)
@Suppress("LongParameterList")
@Composable
fun ThumbnailImmutableCellWindow(
    gameOfLifeState: GameOfLifeState,
    viewportInteractionConfig: ViewportInteractionConfig,
    modifier: Modifier = Modifier,
    cellDpSize: Dp = CellWindow.defaultCellDpSize,
    centerOffset: Offset = CellWindow.defaultCenterOffset,
    inOverlay: Boolean = CellWindow.defaultInOverlay,
) = entryPoint.invoke(gameOfLifeState, viewportInteractionConfig, modifier, cellDpSize, centerOffset, inOverlay)

context(_: CellWindowImplEntryPoint)
@Suppress("LongParameterList")
@Composable
internal fun ThumbnailImmutableCellWindow(
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

@Immutable
@Inject
class ImmutableCellWindowEntryPoint internal constructor(
    private val cellWindowImplEntryPoint: CellWindowImplEntryPoint,
) {
    @Suppress("ComposableNaming", "LongParameterList")
    @Composable
    operator fun invoke(
        gameOfLifeState: GameOfLifeState,
        cellWindowInteractionState: CellWindowInteractionState,
        modifier: Modifier = Modifier,
        cellDpSize: Dp = CellWindow.defaultCellDpSize,
        centerOffset: Offset = CellWindow.defaultCenterOffset,
        inOverlay: Boolean = CellWindow.defaultInOverlay,
    ) = lambda(
        cellWindowImplEntryPoint,
        gameOfLifeState,
        cellWindowInteractionState,
        modifier,
        cellDpSize,
        centerOffset,
        inOverlay,
    )

    companion object {
        private val lambda:
            @Composable
            context(
                CellWindowImplEntryPoint,
            ) (
                gameOfLifeState: GameOfLifeState,
                cellWindowInteractionState: CellWindowInteractionState,
                modifier: Modifier,
                cellDpSize: Dp,
                centerOffset: Offset,
                inOverlay: Boolean,
            ) -> Unit =
            { gameOfLifeState, cellWindowInteractionState, modifier, cellDpSize, centerOffset, inOverlay ->
                ImmutableCellWindow(
                    gameOfLifeState = gameOfLifeState,
                    cellWindowInteractionState = cellWindowInteractionState,
                    modifier = modifier,
                    cellDpSize = cellDpSize,
                    centerOffset = centerOffset,
                    inOverlay = inOverlay,
                )
            }
    }
}

/**
 * A cell window that displays the given [gameOfLifeState] in an immutable fashion.
 */
context(entryPoint: ImmutableCellWindowEntryPoint)
@Suppress("LongParameterList")
@Composable
fun ImmutableCellWindow(
    gameOfLifeState: GameOfLifeState,
    cellWindowInteractionState: CellWindowInteractionState,
    modifier: Modifier = Modifier,
    cellDpSize: Dp = CellWindow.defaultCellDpSize,
    centerOffset: Offset = CellWindow.defaultCenterOffset,
    inOverlay: Boolean = CellWindow.defaultInOverlay,
) = entryPoint.invoke(gameOfLifeState, cellWindowInteractionState, modifier, cellDpSize, centerOffset, inOverlay)

context(_: CellWindowImplEntryPoint)
@Suppress("LongParameterList")
@Composable
private fun ImmutableCellWindow(
    gameOfLifeState: GameOfLifeState,
    cellWindowInteractionState: CellWindowInteractionState,
    modifier: Modifier = Modifier,
    cellDpSize: Dp = CellWindow.defaultCellDpSize,
    centerOffset: Offset = CellWindow.defaultCenterOffset,
    inOverlay: Boolean = CellWindow.defaultInOverlay,
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

@Immutable
@Inject
class MutableCellWindowEntryPoint internal constructor(
    private val cellWindowImplEntryPoint: CellWindowImplEntryPoint,
) {
    @Suppress("ComposableNaming", "LongParameterList")
    @Composable
    operator fun invoke(
        gameOfLifeState: MutableGameOfLifeState,
        cellWindowInteractionState: MutableCellWindowInteractionState,
        modifier: Modifier = Modifier,
        isEditable: (isGesturing: Boolean, scale: Float) -> Boolean = CellWindow.defaultIsEditable,
        cellDpSize: Dp = CellWindow.defaultCellDpSize,
        centerOffset: Offset = CellWindow.defaultCenterOffset,
        inOverlay: Boolean = CellWindow.defaultInOverlay,
    ) = lambda(
        cellWindowImplEntryPoint,
        gameOfLifeState,
        cellWindowInteractionState,
        modifier,
        isEditable,
        cellDpSize,
        centerOffset,
        inOverlay,
    )

    companion object {
        private val lambda:
            @Composable
            context(
                CellWindowImplEntryPoint,
            ) (
                gameOfLifeState: MutableGameOfLifeState,
                cellWindowInteractionState: MutableCellWindowInteractionState,
                modifier: Modifier,
                isEditable: (isGesturing: Boolean, scale: Float) -> Boolean,
                cellDpSize: Dp,
                centerOffset: Offset,
                inOverlay: Boolean,
            ) -> Unit =
            { gameOfLifeState, cellWindowInteractionState, modifier, isEditable, cellDpSize, centerOffset, inOverlay ->
                MutableCellWindow(
                    gameOfLifeState = gameOfLifeState,
                    cellWindowInteractionState = cellWindowInteractionState,
                    modifier = modifier,
                    cellDpSize = cellDpSize,
                    centerOffset = centerOffset,
                    inOverlay = inOverlay,
                )
            }
    }
}

/**
 * A cell window that displays the given [gameOfLifeState] in an mutable fashion.
 *
 * The cells will be editable if and only if [isEditable] returns true.
 */
context(entryPoint: MutableCellWindowEntryPoint)
@Suppress("LongParameterList")
@Composable
fun MutableCellWindow(
    gameOfLifeState: MutableGameOfLifeState,
    cellWindowInteractionState: MutableCellWindowInteractionState,
    modifier: Modifier = Modifier,
    isEditable: (isGesturing: Boolean, scale: Float) -> Boolean = CellWindow.defaultIsEditable,
    cellDpSize: Dp = CellWindow.defaultCellDpSize,
    centerOffset: Offset = CellWindow.defaultCenterOffset,
    inOverlay: Boolean = CellWindow.defaultInOverlay,
) = entryPoint.invoke(
    gameOfLifeState,
    cellWindowInteractionState,
    modifier,
    isEditable,
    cellDpSize,
    centerOffset,
    inOverlay,
)

context(_: CellWindowImplEntryPoint)
@Suppress("LongParameterList")
@Composable
private fun MutableCellWindow(
    gameOfLifeState: MutableGameOfLifeState,
    cellWindowInteractionState: MutableCellWindowInteractionState,
    modifier: Modifier = Modifier,
    isEditable: (isGesturing: Boolean, scale: Float) -> Boolean = CellWindow.defaultIsEditable,
    cellDpSize: Dp = CellWindow.defaultCellDpSize,
    centerOffset: Offset = CellWindow.defaultCenterOffset,
    inOverlay: Boolean = CellWindow.defaultInOverlay,
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
