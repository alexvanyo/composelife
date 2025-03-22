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

import androidx.compose.animation.core.Animatable
import androidx.compose.animation.core.AnimationVector2D
import androidx.compose.animation.core.VectorConverter
import androidx.compose.animation.core.VisibilityThreshold
import androidx.compose.animation.core.spring
import androidx.compose.foundation.interaction.MutableInteractionSource
import androidx.compose.foundation.interaction.collectIsDraggedAsState
import androidx.compose.foundation.interaction.collectIsHoveredAsState
import androidx.compose.foundation.interaction.collectIsPressedAsState
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.foundation.layout.offset
import androidx.compose.runtime.Composable
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.Stable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.key
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.runtime.saveable.Saver
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.setValue
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.graphics.graphicsLayer
import androidx.compose.ui.semantics.contentDescription
import androidx.compose.ui.semantics.semantics
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.round
import androidx.compose.ui.unit.toOffset
import androidx.compose.ui.util.packInts
import androidx.compose.ui.util.unpackInt1
import androidx.compose.ui.util.unpackInt2
import com.alexvanyo.composelife.model.CellState
import com.alexvanyo.composelife.model.CellWindow
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResolver
import com.alexvanyo.composelife.sessionvalue.SessionValue
import com.alexvanyo.composelife.ui.cells.resources.SelectingBoxHandle
import com.alexvanyo.composelife.ui.cells.resources.Strings
import com.alexvanyo.composelife.ui.util.AnchoredDraggable2DState
import com.alexvanyo.composelife.ui.util.anchoredDraggable2D
import com.alexvanyo.composelife.ui.util.snapTo
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.launch
import kotlin.math.max
import kotlin.math.min

@Stable
private class HandleState(
    val state: AnchoredDraggable2DState<IntOffset>,
) {
    var reentrancyCount by mutableStateOf(0)
}

/**
 * Computes the initial handles for a [SelectionState.SelectingBox.FixedSelectingBox].
 *
 * If there is a [SelectionState.SelectingBox.FixedSelectingBox.previousTransientSelectingBox], then these handles
 * will follow those offsets (to be transiently adjusted back to the rounded values).
 *
 * Otherwise, it will just be the direct fixed values.
 */
private val SelectionState.SelectingBox.FixedSelectingBox.initialHandles get(): List<Offset> {
    val initialHandleAOffset: Offset
    val initialHandleBOffset: Offset
    val initialHandleCOffset: Offset
    val initialHandleDOffset: Offset

    if (previousTransientSelectingBox != null) {
        initialHandleAOffset = previousTransientSelectingBox.rect.topLeft
        initialHandleBOffset = previousTransientSelectingBox.rect.topRight
        initialHandleCOffset = previousTransientSelectingBox.rect.bottomRight
        initialHandleDOffset = previousTransientSelectingBox.rect.bottomLeft
    } else {
        initialHandleAOffset = topLeft.toOffset()
        initialHandleBOffset = (topLeft + IntOffset(width, 0)).toOffset()
        initialHandleCOffset = (topLeft + IntOffset(width, height)).toOffset()
        initialHandleDOffset = (topLeft + IntOffset(0, height)).toOffset()
    }

    return listOf(
        initialHandleAOffset,
        initialHandleBOffset,
        initialHandleCOffset,
        initialHandleDOffset,
    )
}

/**
 * The overlay for a [SelectionState.SelectingBox] [selectionState].
 *
 * This includes the selection box, along with 4 handles draggable in two dimensions to allow changing the selecting
 * box bounds.
 */
@Suppress("LongMethod", "CyclomaticComplexMethod", "LongParameterList")
@Composable
internal fun FixedSelectingBoxOverlay(
    selectionSessionState: SessionValue<SelectionState.SelectingBox.FixedSelectingBox>,
    setSelectionState: (SelectionState) -> Unit,
    getSelectionCellState: () -> CellState,
    scaledCellPixelSize: Float,
    cellWindow: CellWindow,
    modifier: Modifier = Modifier,
) {
    Box(modifier) {
        /**
         * The initial handles to initialize the handles with.
         */
        /**
         * The initial handles to initialize the handles with.
         */
        val initialHandles = selectionSessionState.value.initialHandles

        /**
         * The [DraggableAnchors2D] aligned to the current grid.
         */
        /**
         * The [DraggableAnchors2D] aligned to the current grid.
         */
        val handleAnchors = remember(scaledCellPixelSize, cellWindow) {
            GridDraggableAnchors2d(scaledCellPixelSize, cellWindow)
        }

        /**
         * State holders for the value change confirmation lambdas.
         *
         * These are initialized with a placeholder method, since this depends on the state of the other handles.
         */
        /**
         * State holders for the value change confirmation lambdas.
         *
         * These are initialized with a placeholder method, since this depends on the state of the other handles.
         */
        val confirmValueChangeStates = List(initialHandles.size) { index ->
            key(index) {
                remember { mutableStateOf({ _: IntOffset -> true }) }
            }
        }

        val coroutineScope = rememberCoroutineScope()

        /**
         * A list of [Animatable]s for each handle representing the fractional part of the initial handle value, in
         * cell coordinates.
         *
         * This will be initially added to the offset calculations, and animated to zero.
         */
        /**
         * A list of [Animatable]s for each handle representing the fractional part of the initial handle value, in
         * cell coordinates.
         *
         * This will be initially added to the offset calculations, and animated to zero.
         */
        val transientSelectingBoxAnimatables = initialHandles.mapIndexed { index, offset ->
            key(index) {
                remember {
                    Animatable(
                        initialValue = offset - offset.round().toOffset(),
                        typeConverter = Offset.VectorConverter,
                        visibilityThreshold = Offset.VisibilityThreshold / scaledCellPixelSize,
                    )
                }
            }
        }

        // Resolve the transient offsets to zero
        transientSelectingBoxAnimatables.forEachIndexed { index, animatable ->
            key(index) {
                LaunchedEffect(animatable) {
                    animatable.animateTo(Offset.Zero)
                }
            }
        }

        val handleAnchoredDraggable2DStates =
            initialHandles.mapIndexed { index, initialHandleOffset ->
                key(index, scaledCellPixelSize, cellWindow) {
                    rememberSaveable(
                        saver = Saver(
                            save = { packInts(it.currentValue.x, it.currentValue.y) },
                            restore = {
                                AnchoredDraggable2DState(
                                    initialValue = IntOffset(unpackInt1(it), unpackInt2(it)),
                                    animationSpec = spring(),
                                    confirmValueChange = { intOffset ->
                                        confirmValueChangeStates[index].value.invoke(intOffset)
                                    },
                                )
                            },
                        ),
                    ) {
                        AnchoredDraggable2DState(
                            initialValue = initialHandleOffset.round(),
                            animationSpec = spring(),
                            confirmValueChange = { intOffset ->
                                confirmValueChangeStates[index].value.invoke(intOffset)
                            },
                        )
                    }.apply {
                        updateAnchors(
                            newAnchors = handleAnchors,
                            newTarget = targetValue,
                        )
                    }
                }
            }

        val handleStates = handleAnchoredDraggable2DStates.mapIndexed { index, handleAnchoredDraggable2DState ->
            key(index) {
                remember(handleAnchoredDraggable2DState) {
                    HandleState(handleAnchoredDraggable2DState)
                }
            }
        }

        val handleAState = handleStates[0]
        val handleBState = handleStates[1]
        val handleCState = handleStates[2]
        val handleDState = handleStates[3]

        val selectionHandleStates = remember(
            handleStates,
            transientSelectingBoxAnimatables,
            setSelectionState,
            scaledCellPixelSize,
        ) {
            listOf(
                SelectionDraggableHandleState(
                    state = handleAState,
                    transientSelectingBoxAnimatable = transientSelectingBoxAnimatables[0],
                    horizontalPairState = handleBState,
                    verticalPairState = handleDState,
                    oppositeCornerState = handleCState,
                    setSelectionState = setSelectionState,
                    coroutineScope = coroutineScope,
                    scaledCellPixelSize = scaledCellPixelSize,
                ),
                SelectionDraggableHandleState(
                    state = handleBState,
                    transientSelectingBoxAnimatable = transientSelectingBoxAnimatables[1],
                    horizontalPairState = handleAState,
                    verticalPairState = handleCState,
                    oppositeCornerState = handleDState,
                    setSelectionState = setSelectionState,
                    coroutineScope = coroutineScope,
                    scaledCellPixelSize = scaledCellPixelSize,
                ),
                SelectionDraggableHandleState(
                    state = handleCState,
                    transientSelectingBoxAnimatable = transientSelectingBoxAnimatables[2],
                    horizontalPairState = handleDState,
                    verticalPairState = handleBState,
                    oppositeCornerState = handleAState,
                    setSelectionState = setSelectionState,
                    coroutineScope = coroutineScope,
                    scaledCellPixelSize = scaledCellPixelSize,
                ),
                SelectionDraggableHandleState(
                    state = handleDState,
                    transientSelectingBoxAnimatable = transientSelectingBoxAnimatables[3],
                    horizontalPairState = handleCState,
                    verticalPairState = handleAState,
                    oppositeCornerState = handleBState,
                    setSelectionState = setSelectionState,
                    coroutineScope = coroutineScope,
                    scaledCellPixelSize = scaledCellPixelSize,
                ),
            )
        }

        selectionHandleStates.forEachIndexed { index, selectionDraggableHandleState ->
            confirmValueChangeStates[index].value = selectionDraggableHandleState.confirmValueChange
        }

        SelectingBox(
            modifier = Modifier
                .fillMaxSize()
                .boxLayoutByHandles(
                    handleAOffsetCalculator = selectionHandleStates[0].offsetCalculator,
                    handleBOffsetCalculator = selectionHandleStates[1].offsetCalculator,
                    handleCOffsetCalculator = selectionHandleStates[2].offsetCalculator,
                    handleDOffsetCalculator = selectionHandleStates[3].offsetCalculator,
                )
                .cellStateDragAndDropSource(getSelectionCellState),
        )

        val parameterizedStringResolver = parameterizedStringResolver()

        selectionHandleStates
            .forEachIndexed { index, selectionDraggableHandleState ->
                key(index) {
                    val interactionSource = remember { MutableInteractionSource() }

                    val isDragged by interactionSource.collectIsDraggedAsState()
                    val isHovered by interactionSource.collectIsHoveredAsState()
                    val isPressed by interactionSource.collectIsPressedAsState()

                    val isActive = isDragged || isHovered || isPressed

                    SelectionHandle(
                        isActive = isActive,
                        modifier = Modifier
                            .offset {
                                selectionDraggableHandleState.offsetCalculator().round()
                            }
                            .graphicsLayer {
                                translationX = -size.width / 2f
                                translationY = -size.height / 2f
                            }
                            .anchoredDraggable2D(
                                state = selectionDraggableHandleState.state.state,
                                interactionSource = interactionSource,
                            )
                            .semantics {
                                val targetValue = selectionDraggableHandleState.state.state.targetValue
                                contentDescription = parameterizedStringResolver(
                                    Strings.SelectingBoxHandle(
                                        targetValue.x,
                                        targetValue.y,
                                    ),
                                )
                            },
                    )
                }
            }
    }
}

@Suppress("LongParameterList")
@Stable
private class SelectionDraggableHandleState(
    val state: HandleState,
    transientSelectingBoxAnimatable: Animatable<Offset, AnimationVector2D>,
    val horizontalPairState: HandleState,
    val verticalPairState: HandleState,
    val oppositeCornerState: HandleState,
    val setSelectionState: (SelectionState) -> Unit,
    val coroutineScope: CoroutineScope,
    val scaledCellPixelSize: Float,
) {
    val confirmValueChange: (IntOffset) -> Boolean = { intOffset ->
        if (state.reentrancyCount == 0) {
            val minX = min(intOffset.x, oppositeCornerState.state.targetValue.x)
            val maxX = max(intOffset.x, oppositeCornerState.state.targetValue.x)
            val minY = min(intOffset.y, oppositeCornerState.state.targetValue.y)
            val maxY = max(intOffset.y, oppositeCornerState.state.targetValue.y)

            setSelectionState(
                SelectionState.SelectingBox.FixedSelectingBox(
                    topLeft = IntOffset(minX, minY),
                    width = maxX - minX,
                    height = maxY - minY,
                    previousTransientSelectingBox = null,
                ),
            )

            coroutineScope.launch {
                try {
                    horizontalPairState.reentrancyCount++
                    horizontalPairState.state.snapTo(
                        IntOffset(
                            x = horizontalPairState.state.targetValue.x,
                            y = intOffset.y,
                        ),
                    )
                } finally {
                    horizontalPairState.reentrancyCount--
                }
            }
            coroutineScope.launch {
                try {
                    verticalPairState.reentrancyCount++
                    verticalPairState.state.snapTo(
                        IntOffset(
                            x = intOffset.x,
                            y = verticalPairState.state.targetValue.y,
                        ),
                    )
                } finally {
                    verticalPairState.reentrancyCount--
                }
            }
        }
        true
    }

    val offsetCalculator: () -> Offset = {
        val xReferenceState = when {
            state.state.isDraggingOrAnimating() -> state
            verticalPairState.state.isDraggingOrAnimating() -> verticalPairState
            else -> state
        }
        val yReferenceState = when {
            state.state.isDraggingOrAnimating() -> state
            horizontalPairState.state.isDraggingOrAnimating() -> horizontalPairState
            else -> state
        }

        Offset(
            xReferenceState.state.requireOffset().x,
            yReferenceState.state.requireOffset().y,
        ) + transientSelectingBoxAnimatable.value * scaledCellPixelSize
    }
}
