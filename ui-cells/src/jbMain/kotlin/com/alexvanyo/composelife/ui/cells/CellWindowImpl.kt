/*
 * Copyright 2025 The Android Open Source Project
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
@file:Suppress("MatchingDeclarationName")

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
import androidx.compose.ui.unit.toOffset
import com.alexvanyo.composelife.geometry.floor
import com.alexvanyo.composelife.geometry.toRingOffset
import com.alexvanyo.composelife.model.CellState
import com.alexvanyo.composelife.model.CellStateParser
import com.alexvanyo.composelife.model.emptyCellState
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferencesHolder
import com.alexvanyo.composelife.preferences.ToolConfig
import com.alexvanyo.composelife.ui.util.detectTransformGestures
import dev.zacsweers.metro.Inject
import kotlinx.coroutines.currentCoroutineContext
import kotlinx.coroutines.isActive
import kotlin.contracts.ExperimentalContracts
import kotlin.contracts.contract
import kotlin.math.ceil

@Immutable
@Inject
internal class CellWindowImplEntryPoint(
    internal val nonInteractableCellsEntryPoint: NonInteractableCellsEntryPoint,
    internal val interactableCellsEntryPoint: InteractableCellsEntryPoint,
    internal val preferencesHolder: LoadedComposeLifePreferencesHolder,
    internal val cellStateParser: CellStateParser,
)

context(entryPoint: CellWindowImplEntryPoint)
@Composable
internal fun CellWindowImpl(
    cellWindowUiState: CellWindowUiState,
    cellDpSize: Dp,
    centerOffset: Offset,
    inOverlay: Boolean,
    modifier: Modifier = Modifier,
) = CellWindowImpl(
    entryPoint.nonInteractableCellsEntryPoint,
    entryPoint.interactableCellsEntryPoint,
    entryPoint.preferencesHolder,
    entryPoint.cellStateParser,
    entryPoint,
    cellWindowUiState,
    cellDpSize,
    centerOffset,
    inOverlay,
    modifier,
)

@Suppress("LongMethod", "LongParameterList", "CyclomaticComplexMethod")
@Composable
private fun CellWindowImpl(
    nonInteractableCellsEntryPoint: NonInteractableCellsEntryPoint,
    interactableCellsEntryPoint: InteractableCellsEntryPoint,
    preferencesHolder: LoadedComposeLifePreferencesHolder,
    cellStateParser: CellStateParser,
    cellWindowImplEntryPoint: CellWindowImplEntryPoint,
    cellWindowUiState: CellWindowUiState,
    cellDpSize: Dp,
    centerOffset: Offset,
    inOverlay: Boolean,
    modifier: Modifier = Modifier,
) {
    require(centerOffset.x in 0f..1f)
    require(centerOffset.y in 0f..1f)

    var isGesturing by remember { mutableStateOf(false) }

    val viewportInteractionConfig = cellWindowUiState.cellWindowInteractionState.viewportInteractionConfig

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

    val preferences = preferencesHolder.preferences
    val panExcludedPointerTypes =
        setOfNotNull(
            PointerType.Touch.takeUnless { preferences.touchToolConfig == ToolConfig.Pan },
            PointerType.Stylus.takeUnless { preferences.stylusToolConfig == ToolConfig.Pan },
            PointerType.Mouse.takeUnless { preferences.mouseToolConfig == ToolConfig.Pan },
            PointerType.Eraser,
        )

    BoxWithConstraints(
        modifier = modifier,
    ) {
        /**
         * The target [CellWindowViewport] to use to display the cell universe.
         *
         * This will be driven by the [viewportInteractionConfig].
         */
        val targetCellWindowViewport: CellWindowViewport

        /**
         * The animation spec to animate to the [targetCellWindowViewport].
         *
         * This will be driven by the [viewportInteractionConfig].
         */
        val cellWindowViewportAnimationSpec: AnimationSpec<CellWindowViewport>

        // Determine the target viewport and animation spec based on the viewportInteractionConfig
        when (viewportInteractionConfig) {
            is ViewportInteractionConfig.Fixed -> {
                targetCellWindowViewport = viewportInteractionConfig.cellWindowViewportState.cellWindowViewport
                cellWindowViewportAnimationSpec = spring()
            }

            is ViewportInteractionConfig.Navigable -> {
                targetCellWindowViewport = viewportInteractionConfig.mutableCellWindowViewportState.cellWindowViewport
                cellWindowViewportAnimationSpec = snap()
            }

            is ViewportInteractionConfig.Tracking -> {
                targetCellWindowViewport =
                    viewportInteractionConfig.trackingCellWindowViewportState.calculateCellWindowViewport(
                        baseCellWidth = maxWidth / cellDpSize,
                        baseCellHeight = maxHeight / cellDpSize,
                        centerOffset = centerOffset,
                    )
                cellWindowViewportAnimationSpec = viewportInteractionConfig.trackingAnimationSpec
            }
        }

        /**
         * The animated [CellWindowViewport] to the [targetCellWindowViewport] using the
         * [cellWindowViewportAnimationSpec].
         */
        val animatingCellWindowViewport by animateValueAsState(
            targetValue = targetCellWindowViewport,
            typeConverter = TwoWayConverter(
                { AnimationVector(it.offset.x, it.offset.y, it.scale) },
                {
                    CellWindowViewport(
                        offset = Offset(it.v1, it.v2),
                        scale = it.v3,
                    )
                },
            ),
            animationSpec = cellWindowViewportAnimationSpec,
            visibilityThreshold = CellWindowViewport(Offset(0.01f, 0.01f), 0.01f),
            label = "CellWindowViewport Animation",
        )

        // If the animation spec is an immediate snap, use the targetCellWindowViewport immediately to avoid a single
        // frame delay
        val cellWindowViewport = if (
            cellWindowViewportAnimationSpec is SnapSpec<CellWindowViewport> &&
            cellWindowViewportAnimationSpec.delay == 0
        ) {
            targetCellWindowViewport
        } else {
            animatingCellWindowViewport
        }

        // Sync the currently displayed cell window viewport back to any syncable cell window states
        val syncableMutableCellWindowViewportStates =
            viewportInteractionConfig.syncableMutableCellWindowViewportStates
        DisposableEffect(cellWindowViewport, syncableMutableCellWindowViewportStates) {
            syncableMutableCellWindowViewportStates.forEach {
                it.cellWindowViewport = cellWindowViewport
            }

            onDispose {}
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

        // Compute the offset from the main offset to the top left displayed cell
        val topLeftCellOffset = IntOffset(-columnsToLeft, -rowsToTop)

        // Compute the cell window, describing all of the cells that will be drawn
        val cellWindow = com.alexvanyo.composelife.model.CellWindow(
            IntRect(
                intOffset + topLeftCellOffset,
                IntSize(
                    columnsToLeft + 1 + columnsToRight + 1,
                    rowsToTop + 1 + rowsToBottom + 1,
                ),
            ),
        )

        val navigableModifier = when (viewportInteractionConfig) {
            is ViewportInteractionConfig.Fixed,
            is ViewportInteractionConfig.Tracking,
            -> Modifier

            is ViewportInteractionConfig.Navigable -> {
                val mutableCellWindowViewportState = viewportInteractionConfig.mutableCellWindowViewportState

                val currentOnGesture by rememberOnGesture(
                    cellPixelSize = cellPixelSize,
                    topLeftOffset = Offset(
                        constraints.maxWidth * centerOffset.x,
                        constraints.maxHeight * centerOffset.y,
                    ),
                    mutableCellWindowViewportState = mutableCellWindowViewportState,
                )

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
                            mutableCellWindowViewportState.setOffset(
                                mutableCellWindowViewportState.offset + Offset(x, y),
                            )
                            true
                        }
                        scrollToIndex {
                            mutableCellWindowViewportState.setOffset(it.toRingOffset().toOffset())
                            true
                        }
                    }
                    .pointerInput(panExcludedPointerTypes) {
                        detectTransformGestures(
                            excludedPointerTypes = panExcludedPointerTypes,
                            onGestureStart = { isGesturing = true },
                            onGestureEnd = { isGesturing = false },
                            onGesture = { centroid: Offset, pan: Offset, zoom: Float, rotation: Float ->
                                currentOnGesture(centroid, pan, zoom, rotation)
                            },
                        )
                    }
                    .pointerInput(Unit) {
                        // Zoom in and out with vertical scroll wheel events
                        val coroutineContext = currentCoroutineContext()
                        awaitPointerEventScope {
                            while (coroutineContext.isActive) {
                                val event = awaitPointerEvent()
                                if (event.type == PointerEventType.Scroll && event.changes.isNotEmpty()) {
                                    currentOnGesture(
                                        event.changes.first().position,
                                        Offset.Zero,
                                        event.changes.fold(1f) { factor, change ->
                                            factor * if (change.scrollDelta.y > 0) 9f / 10f else 10f / 9f
                                        },
                                        0f,
                                    )
                                }
                            }
                        }
                    }
            }
        }

        Box {
            // Apply the navigable modifier around the cells, but not the selection overlay.
            // This ensures gestures for the selection overlay are given precedence over the cells.
            Box(
                modifier = navigableModifier,
            ) {
                with(nonInteractableCellsEntryPoint) {
                    // Keep the non-interactable cells always visible, to easily be able to switch to it when moving
                    NonInteractableCells(
                        gameOfLifeState = cellWindowUiState.gameOfLifeState,
                        scaledCellDpSize = scaledCellDpSize,
                        cellWindow = cellWindow,
                        pixelOffsetFromCenter = fracPixelOffsetFromCenter,
                        isThumbnail = when (cellWindowUiState) {
                            is CellWindowUiState.ImmutableCellWindowUiState.ThumbnailState -> true
                            is CellWindowUiState.ImmutableCellWindowUiState.InteractableState,
                            is CellWindowUiState.MutableState,
                            -> false
                        },
                        modifier = Modifier.fillMaxSize(),
                        inOverlay = inOverlay,
                    )
                }

                with(interactableCellsEntryPoint) {
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
                            setSelectionSessionState = {
                                cellWindowUiState.cellWindowInteractionState.selectionSessionState = it
                            },
                            scaledCellDpSize = scaledCellDpSize,
                            cellWindow = cellWindow,
                            pixelOffsetFromCenter = fracPixelOffsetFromCenter,
                        )
                    }
                }
            }

            when (cellWindowUiState) {
                is CellWindowUiState.ImmutableCellWindowUiState -> Unit
                is CellWindowUiState.MutableState -> {
                    with(cellWindowImplEntryPoint) {
                        with(cellStateParser) {
                            SelectionOverlay(
                                selectionSessionState =
                                cellWindowUiState.cellWindowInteractionState.selectionSessionState,
                                setSelectionSessionState = {
                                    cellWindowUiState.cellWindowInteractionState.selectionSessionState = it
                                },
                                getSelectionCellState = cellWindowUiState::getSelectionCellState,
                                scaledCellDpSize = scaledCellDpSize,
                                cellWindow = cellWindow,
                                pixelOffsetFromCenter = fracPixelOffsetFromCenter,
                            )
                        }
                    }
                }
            }
        }
    }
}

@Composable
private fun rememberOnGesture(
    cellPixelSize: Float,
    topLeftOffset: Offset,
    mutableCellWindowViewportState: MutableCellWindowViewportState,
) = rememberUpdatedState { centroid: Offset, pan: Offset, zoom: Float, _: Float ->
    // Note: it is possible for the currentOnGesture to run multiple times before recomposition
    // Therefore, these calculations should refer to the most up to date values available, and not
    // ones captured by the previous recomposition.
    // For example, we recalculate cellPixelSize * oldScale instead of using scaledCellPixelSize
    val oldScale = mutableCellWindowViewportState.scale

    // Compute the offset update due to panning
    val panDiff = pan / (cellPixelSize * oldScale)

    // Update the scale
    mutableCellWindowViewportState.setScale(oldScale * zoom)

    // Compute offset update due to zooming. We adjust the offset by the distance it moved relative to
    // the centroid, which allows the centroid to be the point that remains fixed while zooming.
    val zoomDiff = (centroid - topLeftOffset) / cellPixelSize *
        (1 / oldScale - 1 / mutableCellWindowViewportState.scale)

    // Update the offset
    mutableCellWindowViewportState.setOffset(mutableCellWindowViewportState.offset + zoomDiff - panDiff)
}

@OptIn(ExperimentalContracts::class)
private fun CellWindowUiState.isEditable(
    isGesturing: Boolean,
    scale: Float,
): Boolean {
    contract { returns(true) implies (this@isEditable is CellWindowUiState.MutableState) }
    return when (this) {
        is CellWindowUiState.ImmutableCellWindowUiState -> false
        is CellWindowUiState.MutableState -> isEditable(isGesturing, scale)
    }
}

private fun CellWindowUiState.getSelectionCellState(selectionState: SelectionState): CellState =
    when (selectionState) {
        SelectionState.NoSelection -> emptyCellState()
        is SelectionState.SelectingBox.FixedSelectingBox -> {
            gameOfLifeState.cellState.getSelectedCellState(selectionState)
        }
        is SelectionState.SelectingBox.TransientSelectingBox -> emptyCellState()
        is SelectionState.Selection -> selectionState.cellState
    }
