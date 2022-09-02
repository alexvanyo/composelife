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

import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.BoxWithConstraints
import androidx.compose.foundation.layout.size
import androidx.compose.runtime.Composable
import androidx.compose.runtime.DisposableEffect
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberUpdatedState
import androidx.compose.runtime.setValue
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.Offset
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
import com.alexvanyo.composelife.model.GameOfLifeState
import com.alexvanyo.composelife.model.MutableGameOfLifeState
import com.alexvanyo.composelife.model.toCellState
import com.alexvanyo.composelife.ui.entrypoints.WithPreviewDependencies
import com.alexvanyo.composelife.ui.theme.ComposeLifeTheme
import com.alexvanyo.composelife.ui.util.ThemePreviews
import com.alexvanyo.composelife.ui.util.detectTransformGestures
import com.alexvanyo.composelife.util.floor
import com.alexvanyo.composelife.util.toRingOffset
import kotlin.contracts.ExperimentalContracts
import kotlin.contracts.contract
import kotlin.math.ceil

object CellWindow {
    val defaultIsEditable: (isGesturing: Boolean, scale: Float) -> Boolean =
        { isGesturing, scale ->
            !isGesturing && scale >= 1f
        }
    val defaultViewportInteractionConfig
        @Composable get() = ViewportInteractionConfig.Navigable(
            rememberMutableCellWindowState(),
        )
    val defaultCellDpSize = 48.dp
    val defaultCenterOffset = Offset(0.5f, 0.5f)
    const val defaultInOverlay = false
}

interface CellWindowLocalEntryPoint :
    InteractableCellsLocalEntryPoint,
    NonInteractableCellsLocalEntryPoint

/**
 * A cell window that displays the given [gameOfLifeState] in an immutable fashion.
 */
context(CellWindowLocalEntryPoint)
@Suppress("LongParameterList")
@Composable
fun ImmutableCellWindow(
    gameOfLifeState: GameOfLifeState,
    modifier: Modifier = Modifier,
    viewportInteractionConfig: ViewportInteractionConfig = CellWindow.defaultViewportInteractionConfig,
    cellDpSize: Dp = CellWindow.defaultCellDpSize,
    centerOffset: Offset = CellWindow.defaultCenterOffset,
    inOverlay: Boolean = CellWindow.defaultInOverlay,
) {
    CellWindowImpl(
        cellWindowUiState = CellWindowUiState.ImmutableState(
            gameOfLifeState = gameOfLifeState,
        ),
        cellDpSize = cellDpSize,
        centerOffset = centerOffset,
        viewportInteractionConfig = viewportInteractionConfig,
        inOverlay = inOverlay,
        modifier = modifier,
    )
}

/**
 * A cell window that displays the given [gameOfLifeState] in an mutable fashion.
 *
 * The cells will be editable if and only if [isEditable] returns true.
 */
context(CellWindowLocalEntryPoint)
@Suppress("LongParameterList")
@Composable
fun MutableCellWindow(
    gameOfLifeState: MutableGameOfLifeState,
    modifier: Modifier = Modifier,
    isEditable: (isGesturing: Boolean, scale: Float) -> Boolean = CellWindow.defaultIsEditable,
    viewportInteractionConfig: ViewportInteractionConfig = CellWindow.defaultViewportInteractionConfig,
    cellDpSize: Dp = CellWindow.defaultCellDpSize,
    centerOffset: Offset = CellWindow.defaultCenterOffset,
    inOverlay: Boolean = CellWindow.defaultInOverlay,
) {
    CellWindowImpl(
        cellWindowUiState = CellWindowUiState.MutableState(
            gameOfLifeState = gameOfLifeState,
            isEditable = isEditable,
        ),
        cellDpSize = cellDpSize,
        centerOffset = centerOffset,
        viewportInteractionConfig = viewportInteractionConfig,
        inOverlay = inOverlay,
        modifier = modifier,
    )
}

context(CellWindowLocalEntryPoint)
@Suppress("LongMethod", "LongParameterList")
@Composable
private fun CellWindowImpl(
    cellWindowUiState: CellWindowUiState,
    cellDpSize: Dp,
    centerOffset: Offset,
    viewportInteractionConfig: ViewportInteractionConfig,
    inOverlay: Boolean,
    modifier: Modifier,
) {
    require(centerOffset.x in 0f..1f)
    require(centerOffset.y in 0f..1f)

    var isGesturing by remember { mutableStateOf(false) }

    // If the viewport is non-navigable, ensure that gesturing is cancelled.
    when (viewportInteractionConfig) {
        is ViewportInteractionConfig.Navigable -> Unit
        is ViewportInteractionConfig.Fixed,
        is ViewportInteractionConfig.Tracking,
        -> {
            DisposableEffect(Unit) {
                isGesturing = false
                onDispose {}
            }
        }
    }

    BoxWithConstraints(
        modifier = modifier,
    ) {
        /**
         * The [CellWindowViewport] to use to display the cell universe.
         *
         * This will either be driven by the [viewportInteractionConfig].
         */
        val cellWindowViewport: CellWindowViewport

        when (viewportInteractionConfig) {
            is ViewportInteractionConfig.Fixed -> {
                cellWindowViewport = viewportInteractionConfig.cellWindowState.cellWindowViewport
            }
            is ViewportInteractionConfig.Navigable -> {
                cellWindowViewport = viewportInteractionConfig.mutableCellWindowState.cellWindowViewport
            }
            is ViewportInteractionConfig.Tracking -> {
                cellWindowViewport = viewportInteractionConfig.trackingCellWindowState.calculateCellWindowViewport(
                    baseCellWidth = maxWidth / cellDpSize,
                    baseCellHeight = maxHeight / cellDpSize,
                    centerOffset = centerOffset,
                )

                val mutableCellWindowState = viewportInteractionConfig.mutableCellWindowState

                // Sync the calculated tracking viewport back to the mutable cell window viewport to preserve
                // the viewport when disabling auto tracking
                DisposableEffect(cellWindowViewport, mutableCellWindowState) {
                    mutableCellWindowState?.offset = cellWindowViewport.offset
                    mutableCellWindowState?.scale = cellWindowViewport.scale

                    onDispose {}
                }
            }
        }

        val scaledCellDpSize = cellDpSize * cellWindowViewport.scale

        val cellPixelSize = with(LocalDensity.current) { cellDpSize.toPx() }
        val scaledCellPixelSize = cellPixelSize * cellWindowViewport.scale

        // Convert the window state offset into integer and fractional parts
        val intOffset = floor(cellWindowViewport.offset)
        val fracOffset = cellWindowViewport.offset - intOffset.toOffset()
        val fracOffsetFromCenter = fracOffset - Offset(0.5f, 0.5f)
        val fracPixelOffsetFromCenter = fracOffsetFromCenter * scaledCellPixelSize

        // Calculate the number of columns and rows necessary to cover the entire viewport.
        val columnsToLeft = ceil(constraints.maxWidth * centerOffset.x / scaledCellPixelSize).toInt()
        val columnsToRight = ceil(constraints.maxWidth * (1 - centerOffset.x) / scaledCellPixelSize).toInt()
        val rowsToTop = ceil(constraints.maxHeight * centerOffset.y / scaledCellPixelSize).toInt()
        val rowsToBottom = ceil(constraints.maxHeight * (1 - centerOffset.y) / scaledCellPixelSize).toInt()

        // Compute the offset from the main offset to the top left corner, in cell coordinates
        val topLeftOffset = IntOffset(-columnsToLeft, -rowsToTop)

        // Compute the cell window, describing all of the cells that will be drawn
        val cellWindow = IntRect(
            intOffset + topLeftOffset,
            IntSize(
                columnsToLeft + 1 + columnsToRight,
                rowsToTop + 1 + rowsToBottom,
            ),
        )

        val navigableModifier = when (viewportInteractionConfig) {
            is ViewportInteractionConfig.Fixed,
            is ViewportInteractionConfig.Tracking,
            -> Modifier
            is ViewportInteractionConfig.Navigable -> {
                val mutableCellWindowState = viewportInteractionConfig.mutableCellWindowState

                val currentOnGesture by rememberUpdatedState { centroid: Offset, pan: Offset, zoom: Float, _: Float ->
                    val oldScale = cellWindowViewport.scale

                    // Compute the offset from the centroid to the underlying offset, in cell coordinates
                    val centroidOffset = centroid / scaledCellPixelSize + topLeftOffset.toOffset()

                    // Compute the offset update due to panning
                    val panDiff = pan / scaledCellPixelSize

                    // Update the scale
                    mutableCellWindowState.scale = oldScale * zoom

                    // Compute offset update due to zooming. We adjust the offset by the distance it moved relative to
                    // the centroid, which allows the centroid to be the point that remains fixed while zooming.
                    val zoomDiff = centroidOffset * (mutableCellWindowState.scale / oldScale - 1)

                    // Update the offset
                    mutableCellWindowState.offset += zoomDiff - panDiff
                }

                Modifier
                    .semantics {
                        horizontalScrollAxisRange = ScrollAxisRange(
                            value = { cellWindowViewport.offset.x },
                            maxValue = { Float.POSITIVE_INFINITY },
                        )
                        verticalScrollAxisRange = ScrollAxisRange(
                            value = { cellWindowViewport.offset.y },
                            maxValue = { Float.POSITIVE_INFINITY },
                        )
                        scrollBy { x, y ->
                            mutableCellWindowState.offset += Offset(x, y)
                            true
                        }
                        scrollToIndex {
                            mutableCellWindowState.offset = it
                                .toRingOffset()
                                .toOffset()
                            true
                        }
                    }
                    .pointerInput(Unit) {
                        detectTransformGestures(
                            onGestureStart = { isGesturing = true },
                            onGestureEnd = { isGesturing = false },
                            onGesture = { centroid: Offset, pan: Offset, zoom: Float, rotation: Float ->
                                currentOnGesture(centroid, pan, zoom, rotation)
                            },
                        )
                    }
            }
        }

        Box(
            modifier = navigableModifier,
        ) {
            // Keep the non-interactable cells always visible, to easily be able to switch to it when moving
            NonInteractableCells(
                gameOfLifeState = cellWindowUiState.gameOfLifeState,
                scaledCellDpSize = scaledCellDpSize,
                cellWindow = cellWindow,
                pixelOffsetFromCenter = fracPixelOffsetFromCenter,
                modifier = Modifier.size(this@BoxWithConstraints.maxWidth, this@BoxWithConstraints.maxHeight),
                inOverlay = inOverlay,
            )

            // Only show the interactable cells if the conditions are met to be interactable.
            if (
                cellWindowUiState.isEditable(
                    isGesturing = when (viewportInteractionConfig) {
                        is ViewportInteractionConfig.Fixed,
                        is ViewportInteractionConfig.Tracking,
                        -> false
                        is ViewportInteractionConfig.Navigable -> true
                    } && isGesturing,
                    scale = cellWindowViewport.scale,
                )
            ) {
                InteractableCells(
                    gameOfLifeState = cellWindowUiState.gameOfLifeState,
                    scaledCellDpSize = scaledCellDpSize,
                    cellWindow = cellWindow,
                    pixelOffsetFromCenter = fracPixelOffsetFromCenter,
                )
            }
        }
    }
}

private sealed interface CellWindowUiState {

    val gameOfLifeState: GameOfLifeState

    class ImmutableState(
        override val gameOfLifeState: GameOfLifeState,
    ) : CellWindowUiState

    class MutableState(
        override val gameOfLifeState: MutableGameOfLifeState,
        val isEditable: (isGesturing: Boolean, scale: Float) -> Boolean,
    ) : CellWindowUiState
}

@OptIn(ExperimentalContracts::class)
private fun CellWindowUiState.isEditable(
    isGesturing: Boolean,
    scale: Float,
): Boolean {
    contract { returns(true) implies (this@isEditable is CellWindowUiState.MutableState) }
    return when (this) {
        is CellWindowUiState.ImmutableState -> false
        is CellWindowUiState.MutableState -> isEditable(isGesturing, scale)
    }
}

@ThemePreviews
@Composable
fun NavigableImmutableCellWindowPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            ImmutableCellWindow(
                gameOfLifeState = GameOfLifeState(
                    setOf(
                        0 to 0,
                        0 to 2,
                        0 to 4,
                        2 to 0,
                        2 to 2,
                        2 to 4,
                        4 to 0,
                        4 to 2,
                        4 to 4,
                    ).toCellState(),
                ),
            )
        }
    }
}

@ThemePreviews
@Composable
fun TrackingImmutableCellWindowPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            val gameOfLifeState = GameOfLifeState(
                setOf(
                    0 to 0,
                    0 to 2,
                    0 to 4,
                    2 to 0,
                    2 to 2,
                    2 to 4,
                    4 to 0,
                    4 to 2,
                    4 to 4,
                ).toCellState(),
            )
            val trackingCellWindowState = rememberTrackingCellWindowState(gameOfLifeState)

            ImmutableCellWindow(
                gameOfLifeState = gameOfLifeState,
                viewportInteractionConfig = ViewportInteractionConfig.Tracking(
                    trackingCellWindowState = trackingCellWindowState,
                ),
            )
        }
    }
}

@ThemePreviews
@Composable
fun NavigableMutableCellWindowPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            MutableCellWindow(
                gameOfLifeState = MutableGameOfLifeState(
                    setOf(
                        0 to 0,
                        0 to 2,
                        0 to 4,
                        2 to 0,
                        2 to 2,
                        2 to 4,
                        4 to 0,
                        4 to 2,
                        4 to 4,
                    ).toCellState(),
                ),
            )
        }
    }
}

@ThemePreviews
@Composable
fun TrackingMutableCellWindowPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            val gameOfLifeState = GameOfLifeState(
                setOf(
                    0 to 0,
                    0 to 2,
                    0 to 4,
                    2 to 0,
                    2 to 2,
                    2 to 4,
                    4 to 0,
                    4 to 2,
                    4 to 4,
                ).toCellState(),
            )
            val trackingCellWindowState = rememberTrackingCellWindowState(gameOfLifeState)

            MutableCellWindow(
                gameOfLifeState = MutableGameOfLifeState(
                    setOf(
                        0 to 0,
                        0 to 2,
                        0 to 4,
                        2 to 0,
                        2 to 2,
                        2 to 4,
                        4 to 0,
                        4 to 2,
                        4 to 4,
                    ).toCellState(),
                ),
                viewportInteractionConfig = ViewportInteractionConfig.Tracking(
                    trackingCellWindowState = trackingCellWindowState,
                ),
            )
        }
    }
}
