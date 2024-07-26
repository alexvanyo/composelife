/*
 * Copyright 2023 The Android Open Source Project
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

package com.alexvanyo.composelife.ui.app.cells

import androidx.compose.animation.core.Animatable
import androidx.compose.animation.core.AnimationVector2D
import androidx.compose.animation.core.VectorConverter
import androidx.compose.animation.core.VisibilityThreshold
import androidx.compose.animation.core.animateDpAsState
import androidx.compose.animation.core.spring
import androidx.compose.foundation.Canvas
import androidx.compose.foundation.interaction.MutableInteractionSource
import androidx.compose.foundation.interaction.collectIsDraggedAsState
import androidx.compose.foundation.interaction.collectIsHoveredAsState
import androidx.compose.foundation.interaction.collectIsPressedAsState
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.Spacer
import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.foundation.layout.offset
import androidx.compose.foundation.layout.requiredSize
import androidx.compose.foundation.layout.size
import androidx.compose.foundation.shape.CircleShape
import androidx.compose.material3.MaterialTheme
import androidx.compose.material3.Surface
import androidx.compose.runtime.Composable
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.Stable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.key
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.runtime.rememberUpdatedState
import androidx.compose.runtime.saveable.Saver
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.setValue
import androidx.compose.runtime.snapshotFlow
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.geometry.Rect
import androidx.compose.ui.geometry.Size
import androidx.compose.ui.geometry.toRect
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.graphics.PathEffect
import androidx.compose.ui.graphics.drawscope.DrawScope
import androidx.compose.ui.graphics.graphicsLayer
import androidx.compose.ui.layout.layout
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.semantics.contentDescription
import androidx.compose.ui.semantics.semantics
import androidx.compose.ui.unit.Constraints
import androidx.compose.ui.unit.Dp
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.dp
import androidx.compose.ui.unit.round
import androidx.compose.ui.unit.toOffset
import androidx.compose.ui.util.packInts
import androidx.compose.ui.util.unpackInt1
import androidx.compose.ui.util.unpackInt2
import com.alexvanyo.composelife.model.CellWindow
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResolver
import com.alexvanyo.composelife.sessionvalue.SessionValue
import com.alexvanyo.composelife.sessionvalue.preLocalSessionId
import com.alexvanyo.composelife.sessionvalue.rememberSessionValueHolder
import com.alexvanyo.composelife.ui.app.resources.SelectingBoxHandle
import com.alexvanyo.composelife.ui.app.resources.Strings
import com.alexvanyo.composelife.ui.util.AnchoredDraggable2DState
import com.alexvanyo.composelife.ui.util.AnimatedContent
import com.alexvanyo.composelife.ui.util.DraggableAnchors2D
import com.alexvanyo.composelife.ui.util.TargetState
import com.alexvanyo.composelife.ui.util.anchoredDraggable2D
import com.alexvanyo.composelife.ui.util.snapTo
import kotlinx.coroutines.flow.collect
import kotlinx.coroutines.flow.onEach
import kotlinx.coroutines.launch
import kotlin.math.max
import kotlin.math.min
import kotlin.math.roundToInt

/**
 * The overlay based on the [selectionState].
 */
@Suppress("LongMethod")
@Composable
fun SelectionOverlay(
    selectionSessionState: SessionValue<SelectionState>,
    setSelectionSessionState: (SessionValue<SelectionState>) -> Unit,
    scaledCellDpSize: Dp,
    cellWindow: CellWindow,
    modifier: Modifier = Modifier,
) {
    val selectionSessionStateValueHolder = rememberSessionValueHolder(
        upstreamSessionValue = selectionSessionState,
        setUpstreamSessionValue = { _, sessionValue ->
            setSelectionSessionState(sessionValue)
        },
        valueSaver = SelectionState.Saver,
    )
    val sessionValue = selectionSessionStateValueHolder.sessionValue

    AnimatedContent(
        targetState = TargetState.Single(
            sessionValue to selectionSessionStateValueHolder.info.preLocalSessionId,
        ),
        contentAlignment = Alignment.Center,
        contentKey = { (targetSelectionSessionState, preLocalSessionId) ->
            when (targetSelectionSessionState.value) {
                SelectionState.NoSelection -> 0
                is SelectionState.SelectingBox -> 1
                is SelectionState.Selection -> 2
            } to preLocalSessionId
        },
        modifier = modifier
            .requiredSize(
                scaledCellDpSize * cellWindow.width,
                scaledCellDpSize * cellWindow.height,
            ),
    ) { (targetSelectionSessionState, _) ->
        when (val targetSelectionState = targetSelectionSessionState.value) {
            SelectionState.NoSelection -> {
                Spacer(Modifier.fillMaxSize())
            }
            is SelectionState.SelectingBox.FixedSelectingBox -> {
                @Suppress("UNCHECKED_CAST")
                FixedSelectingBoxOverlay(
                    selectionSessionState = targetSelectionSessionState as
                        SessionValue<SelectionState.SelectingBox.FixedSelectingBox>,
                    setSelectionState = selectionSessionStateValueHolder::setValue,
                    scaledCellPixelSize = with(LocalDensity.current) { scaledCellDpSize.toPx() },
                    cellWindow = cellWindow,
                    modifier = Modifier.fillMaxSize(),
                )
            }
            is SelectionState.SelectingBox.TransientSelectingBox -> {
                TransientSelectingBoxOverlay(
                    selectionState = targetSelectionState,
                    scaledCellPixelSize = with(LocalDensity.current) { scaledCellDpSize.toPx() },
                    cellWindow = cellWindow,
                    modifier = Modifier.fillMaxSize(),
                )
            }
            is SelectionState.Selection -> {
                @Suppress("UNCHECKED_CAST")
                SelectionBoxOverlay(
                    selectionSessionState = targetSelectionSessionState as SessionValue<SelectionState.Selection>,
                    setSelectionState = selectionSessionStateValueHolder::setValue,
                    scaledCellPixelSize = with(LocalDensity.current) { scaledCellDpSize.toPx() },
                    cellWindow = cellWindow,
                    modifier = Modifier.fillMaxSize(),
                )
            }
        }
    }
}

val SelectionState.SelectingBox.FixedSelectingBox.initialHandles get(): List<Offset> {
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
private fun FixedSelectingBoxOverlay(
    selectionSessionState: SessionValue<SelectionState.SelectingBox.FixedSelectingBox>,
    setSelectionState: (SelectionState) -> Unit,
    scaledCellPixelSize: Float,
    cellWindow: CellWindow,
    modifier: Modifier = Modifier,
) {
    Box(modifier) {
        val initialHandles = selectionSessionState.value.initialHandles

        val handleAnchors = remember(scaledCellPixelSize, cellWindow) {
            GridDraggableAnchors2d(scaledCellPixelSize, cellWindow)
        }

        val confirmValueChangeStates = List(initialHandles.size) { index ->
            key(index) {
                remember { mutableStateOf({ _: IntOffset -> true }) }
            }
        }

        val coroutineScope = rememberCoroutineScope()

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

        transientSelectingBoxAnimatables.forEachIndexed { index, animatable ->
            key(index) {
                LaunchedEffect(animatable) {
                    animatable.animateTo(Offset.Zero)
                }
            }
        }

        @Stable
        class HandleState(
            val state: AnchoredDraggable2DState<IntOffset>,
        ) {
            var reentrancyCount by mutableStateOf(0)
        }

        @Stable
        class SelectionDraggableHandleState(
            val state: HandleState,
            transientSelectingBoxAnimatable: Animatable<Offset, AnimationVector2D>,
            val horizontalPairState: HandleState,
            val verticalPairState: HandleState,
            val oppositeCornerState: HandleState,
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

        val selectionHandleStates = remember(handleStates, transientSelectingBoxAnimatables) {
            listOf(
                SelectionDraggableHandleState(
                    state = handleAState,
                    transientSelectingBoxAnimatable = transientSelectingBoxAnimatables[0],
                    horizontalPairState = handleBState,
                    verticalPairState = handleDState,
                    oppositeCornerState = handleCState,
                ),
                SelectionDraggableHandleState(
                    state = handleBState,
                    transientSelectingBoxAnimatable = transientSelectingBoxAnimatables[1],
                    horizontalPairState = handleAState,
                    verticalPairState = handleCState,
                    oppositeCornerState = handleDState,
                ),
                SelectionDraggableHandleState(
                    state = handleCState,
                    transientSelectingBoxAnimatable = transientSelectingBoxAnimatables[2],
                    horizontalPairState = handleDState,
                    verticalPairState = handleBState,
                    oppositeCornerState = handleAState,
                ),
                SelectionDraggableHandleState(
                    state = handleDState,
                    transientSelectingBoxAnimatable = transientSelectingBoxAnimatables[3],
                    horizontalPairState = handleCState,
                    verticalPairState = handleAState,
                    oppositeCornerState = handleBState,
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
                ),
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

@Composable
private fun TransientSelectingBoxOverlay(
    selectionState: SelectionState.SelectingBox.TransientSelectingBox,
    scaledCellPixelSize: Float,
    cellWindow: CellWindow,
    modifier: Modifier = Modifier,
) {
    Box(modifier) {
        val selectionRect = selectionState.rect.translate(-cellWindow.topLeft.toOffset())

        val handleAOffsetCalculator = { selectionRect.topLeft * scaledCellPixelSize }
        val handleBOffsetCalculator = { selectionRect.topRight * scaledCellPixelSize }
        val handleCOffsetCalculator = { selectionRect.bottomRight * scaledCellPixelSize }
        val handleDOffsetCalculator = { selectionRect.bottomLeft * scaledCellPixelSize }

        val handleOffsetCalculators = listOf(
            handleAOffsetCalculator,
            handleBOffsetCalculator,
            handleCOffsetCalculator,
            handleDOffsetCalculator,
        )

        SelectingBox(
            modifier = Modifier
                .fillMaxSize()
                .boxLayoutByHandles(
                    handleAOffsetCalculator = {
                        selectionRect.topLeft * scaledCellPixelSize
                    },
                    handleBOffsetCalculator = {
                        selectionRect.topRight * scaledCellPixelSize
                    },
                    handleCOffsetCalculator = {
                        selectionRect.bottomRight * scaledCellPixelSize
                    },
                    handleDOffsetCalculator = {
                        selectionRect.bottomLeft * scaledCellPixelSize
                    },
                ),
        )

        handleOffsetCalculators.mapIndexed { index, offsetCalculator ->
            key(index) {
                SelectionHandle(
                    isActive = index == 2,
                    modifier = Modifier
                        .offset {
                            offsetCalculator().round()
                        }
                        .graphicsLayer {
                            translationX = -size.width / 2f
                            translationY = -size.height / 2f
                        },
                )
            }
        }
    }
}

@Composable
fun SelectionHandle(
    isActive: Boolean,
    modifier: Modifier = Modifier,
    selectionColor: Color = MaterialTheme.colorScheme.secondary,
) {
    Box(
        modifier = modifier.size(48.dp),
        contentAlignment = Alignment.Center,
    ) {
        val size by animateDpAsState(if (isActive) 24.dp else 16.dp)
        val elevation by animateDpAsState(if (isActive) 4.dp else 0.dp)
        Surface(
            modifier = Modifier.size(size),
            shape = CircleShape,
            shadowElevation = elevation,
            color = selectionColor,
        ) {}
    }
}

/**
 * A custom [layout] modifier that measures a box bounded by the given 4 offsets, such that the box doesn't extend
 * beyond the bounds of the parent.
 */
fun Modifier.boxLayoutByHandles(
    handleAOffsetCalculator: () -> Offset,
    handleBOffsetCalculator: () -> Offset,
    handleCOffsetCalculator: () -> Offset,
    handleDOffsetCalculator: () -> Offset,
): Modifier = layout { measurable, constraints ->
    // Calculate the offsets of the 4 handles
    val aOffset = handleAOffsetCalculator()
    val bOffset = handleBOffsetCalculator()
    val cOffset = handleCOffsetCalculator()
    val dOffset = handleDOffsetCalculator()

    // Determine the top left and bottom right points of the offset, coercing to the edges of this box
    // to avoid drawing the box outside of the bounds.
    val minX = min(min(aOffset.x, bOffset.x), min(cOffset.x, dOffset.x))
        .coerceIn(0f, constraints.maxWidth.toFloat())
    val maxX = max(max(aOffset.x, bOffset.x), max(cOffset.x, dOffset.x))
        .coerceIn(0f, constraints.maxWidth.toFloat())
    val minY = min(min(aOffset.y, bOffset.y), min(cOffset.y, dOffset.y))
        .coerceIn(0f, constraints.maxHeight.toFloat())
    val maxY = max(max(aOffset.y, bOffset.y), max(cOffset.y, dOffset.y))
        .coerceIn(0f, constraints.maxHeight.toFloat())

    val topLeft = Offset(minX, minY)
    val size = Size(maxX - minX, maxY - minY)

    val selectionBoxConstraints = Constraints(
        minWidth = size.width.roundToInt(),
        maxWidth = size.width.roundToInt(),
        minHeight = size.height.roundToInt(),
        maxHeight = size.height.roundToInt(),
    )

    // Measure the contents exactly to the constraints.
    val placeable = measurable.measure(selectionBoxConstraints)

    layout(constraints.maxWidth, constraints.maxHeight) {
        placeable.place(topLeft.round())
    }
}

/**
 * The selecting box itself.
 */
@Composable
fun SelectingBox(
    // noinspection ComposeModifierWithoutDefault
    modifier: Modifier,
    selectionColor: Color = MaterialTheme.colorScheme.secondary,
) {
    Canvas(
        modifier = modifier.fillMaxSize(),
    ) {
        drawRect(
            color = selectionColor,
            alpha = 0.2f,
        )
        drawSelectionRect(
            selectionColor = selectionColor,
            strokeWidth = 2.dp.toPx(),
            pathEffect = PathEffect.dashPathEffect(
                floatArrayOf(
                    24.dp.toPx(),
                    24.dp.toPx(),
                ),
                phase = 12.dp.toPx(),
            ),
        )
    }
}

/**
 * Draws a selection rectangle, with the given [PathEffect].
 *
 * This results in the [PathEffect] being applied symmetrically via 8 line segments: from the middle of each side,
 * to each corner.
 */
private fun DrawScope.drawSelectionRect(
    selectionColor: Color,
    strokeWidth: Float,
    pathEffect: PathEffect,
    rect: Rect = size.toRect(),
) {
    // Draw the selection outlines in a way that is symmetric, and hides the extra of the lines near the
    // corners with the selection handles
    drawLine(
        color = selectionColor,
        start = rect.topCenter,
        end = rect.topLeft,
        strokeWidth = strokeWidth,
        pathEffect = pathEffect,
    )
    drawLine(
        color = selectionColor,
        start = rect.topCenter,
        end = rect.topRight,
        strokeWidth = strokeWidth,
        pathEffect = pathEffect,
    )
    drawLine(
        color = selectionColor,
        start = rect.centerLeft,
        end = rect.topLeft,
        strokeWidth = strokeWidth,
        pathEffect = pathEffect,
    )
    drawLine(
        color = selectionColor,
        start = rect.centerLeft,
        end = rect.bottomLeft,
        strokeWidth = strokeWidth,
        pathEffect = pathEffect,
    )
    drawLine(
        color = selectionColor,
        start = rect.bottomCenter,
        end = rect.bottomLeft,
        strokeWidth = strokeWidth,
        pathEffect = pathEffect,
    )
    drawLine(
        color = selectionColor,
        start = rect.bottomCenter,
        end = rect.bottomRight,
        strokeWidth = strokeWidth,
        pathEffect = pathEffect,
    )
    drawLine(
        color = selectionColor,
        start = rect.centerRight,
        end = rect.topRight,
        strokeWidth = strokeWidth,
        pathEffect = pathEffect,
    )
    drawLine(
        color = selectionColor,
        start = rect.centerRight,
        end = rect.bottomRight,
        strokeWidth = strokeWidth,
        pathEffect = pathEffect,
    )
}

data class GridDraggableAnchors2d(
    private val scaledCellPixelSize: Float,
    private val cellWindow: CellWindow,
) : DraggableAnchors2D<IntOffset> {
    override fun positionOf(value: IntOffset): Offset =
        (value.toOffset() - cellWindow.topLeft.toOffset()) * scaledCellPixelSize

    override fun hasAnchorFor(value: IntOffset): Boolean = true
    override fun closestAnchor(position: Offset): IntOffset =
        (position / scaledCellPixelSize).round() + cellWindow.topLeft

    override val size: Int = Int.MAX_VALUE
}

@Suppress("LongParameterList", "LongMethod")
@Composable
private fun SelectionBoxOverlay(
    selectionSessionState: SessionValue<SelectionState.Selection>,
    setSelectionState: (SelectionState) -> Unit,
    scaledCellPixelSize: Float,
    cellWindow: CellWindow,
    modifier: Modifier = Modifier,
) {
    val handleAnchors = remember(scaledCellPixelSize, cellWindow) {
        GridDraggableAnchors2d(scaledCellPixelSize, cellWindow)
    }

    val initialOffset = selectionSessionState.value.offset

    val currentSelectionSessionState by rememberUpdatedState(selectionSessionState)
    val currentSetSelectionState by rememberUpdatedState(setSelectionState)

    val confirmValueChange = { intOffset: IntOffset ->
        setSelectionState(
            currentSelectionSessionState.value.copy(
                offset = intOffset,
            ),
        )
        true
    }

    val draggable2DState = rememberSaveable(
        saver = Saver(
            save = { packInts(it.currentValue.x, it.currentValue.y) },
            restore = {
                AnchoredDraggable2DState(
                    initialValue = IntOffset(unpackInt1(it), unpackInt2(it)),
                    animationSpec = spring(),
                    confirmValueChange = confirmValueChange,
                )
            },
        ),
    ) {
        AnchoredDraggable2DState(
            initialValue = initialOffset,
            animationSpec = spring(),
            confirmValueChange = confirmValueChange,
        )
    }.apply {
        updateAnchors(
            newAnchors = handleAnchors,
            // Ensure the target value remains the same due to updating the anchors.
            // This keeps the selection box stationary relative to the overall universe.
            newTarget = targetValue,
        )
    }

    // As a side-effect of dragging, update the underlying selection state to match the intermediate selection.
    LaunchedEffect(draggable2DState) {
        snapshotFlow { draggable2DState.currentValue }
            .onEach { intOffset ->
                currentSetSelectionState(
                    currentSelectionSessionState.value.copy(
                        offset = intOffset,
                    ),
                )
            }
            .collect()
    }

    val boundingBox = selectionSessionState.value.cellState.boundingBox

    SelectingBox(
        modifier = modifier
            .fillMaxSize()
            .boxLayoutByHandles(
                handleAOffsetCalculator = {
                    draggable2DState.requireOffset()
                },
                handleBOffsetCalculator = {
                    draggable2DState.requireOffset() + Offset(
                        boundingBox.width.toFloat(),
                        0f,
                    ) * scaledCellPixelSize
                },
                handleCOffsetCalculator = {
                    draggable2DState.requireOffset() + Offset(
                        boundingBox.width.toFloat(),
                        boundingBox.height.toFloat(),
                    ) * scaledCellPixelSize
                },
                handleDOffsetCalculator = {
                    draggable2DState.requireOffset() + Offset(
                        0f,
                        boundingBox.height.toFloat(),
                    ) * scaledCellPixelSize
                },
            )
            .anchoredDraggable2D(draggable2DState),
        selectionColor = MaterialTheme.colorScheme.tertiary,
    )
}

fun <T> AnchoredDraggable2DState<T>.isDraggingOrAnimating(): Boolean =
    anchors.positionOf(currentValue) != requireOffset()
