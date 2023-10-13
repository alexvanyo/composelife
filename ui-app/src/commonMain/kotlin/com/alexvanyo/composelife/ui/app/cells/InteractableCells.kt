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
@file:Suppress("MatchingDeclarationName")

package com.alexvanyo.composelife.ui.app.cells

import androidx.compose.animation.AnimatedContent
import androidx.compose.animation.core.animateDpAsState
import androidx.compose.animation.core.spring
import androidx.compose.foundation.Canvas
import androidx.compose.foundation.gestures.detectDragGestures
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
import androidx.compose.runtime.getValue
import androidx.compose.runtime.key
import androidx.compose.runtime.mutableStateMapOf
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.runtime.rememberUpdatedState
import androidx.compose.runtime.saveable.Saver
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.setValue
import androidx.compose.ui.Alignment
import androidx.compose.ui.ExperimentalComposeUiApi
import androidx.compose.ui.Modifier
import androidx.compose.ui.composed
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.geometry.Size
import androidx.compose.ui.geometry.isSpecified
import androidx.compose.ui.geometry.toRect
import androidx.compose.ui.graphics.PathEffect
import androidx.compose.ui.graphics.graphicsLayer
import androidx.compose.ui.input.pointer.HistoricalChange
import androidx.compose.ui.input.pointer.PointerType
import androidx.compose.ui.input.pointer.pointerInput
import androidx.compose.ui.layout.Layout
import androidx.compose.ui.layout.layout
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.platform.testTag
import androidx.compose.ui.unit.Constraints
import androidx.compose.ui.unit.Dp
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.IntRect
import androidx.compose.ui.unit.dp
import androidx.compose.ui.unit.round
import androidx.compose.ui.unit.toOffset
import androidx.compose.ui.util.packInts
import androidx.compose.ui.util.unpackInt1
import androidx.compose.ui.util.unpackInt2
import com.alexvanyo.composelife.geometry.LineSegmentPath
import com.alexvanyo.composelife.geometry.cellIntersections
import com.alexvanyo.composelife.geometry.containedPoints
import com.alexvanyo.composelife.model.GameOfLifeState
import com.alexvanyo.composelife.model.MutableGameOfLifeState
import com.alexvanyo.composelife.model.setCellState
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResource
import com.alexvanyo.composelife.preferences.ToolConfig
import com.alexvanyo.composelife.preferences.di.LoadedComposeLifePreferencesProvider
import com.alexvanyo.composelife.ui.app.resources.InteractableCellContentDescription
import com.alexvanyo.composelife.ui.app.resources.Strings
import com.alexvanyo.composelife.ui.util.AnchoredDraggable2DState
import com.alexvanyo.composelife.ui.util.DraggableAnchors2D
import com.alexvanyo.composelife.ui.util.anchoredDraggable2D
import com.alexvanyo.composelife.ui.util.snapTo
import com.alexvanyo.composelife.ui.util.uuidSaver
import kotlinx.coroutines.launch
import java.util.UUID
import kotlin.coroutines.cancellation.CancellationException
import kotlin.math.max
import kotlin.math.min
import kotlin.math.roundToInt

interface InteractableCellsLocalEntryPoint : LoadedComposeLifePreferencesProvider

/**
 * A fixed size composable that displays a specific [cellWindow] into the given [GameOfLifeState].
 *
 * The [GameOfLifeState] is interactable, so each cell is displayed by a unique [InteractableCell].
 */
context(InteractableCellsLocalEntryPoint)
@Suppress("LongParameterList", "LongMethod", "CyclomaticComplexMethod")
@Composable
fun InteractableCells(
    gameOfLifeState: MutableGameOfLifeState,
    selectionStateHolder: MutableSelectionStateHolder,
    scaledCellDpSize: Dp,
    cellWindow: IntRect,
    pixelOffsetFromCenter: Offset,
    modifier: Modifier = Modifier,
) {
    Surface(
        modifier = modifier
            .graphicsLayer {
                this.translationX = -pixelOffsetFromCenter.x
                this.translationY = -pixelOffsetFromCenter.y
            }
            .requiredSize(
                scaledCellDpSize * (cellWindow.width + 1),
                scaledCellDpSize * (cellWindow.height + 1),
            ),
    ) {
        val scaledCellPixelSize = with(LocalDensity.current) { scaledCellDpSize.toPx() }

        val numColumns = cellWindow.width + 1
        val numRows = cellWindow.height + 1

        val pendingCellChanges = remember { mutableStateMapOf<IntOffset, Boolean>() }

        val drawingPointerTypes =
            setOfNotNull(
                PointerType.Touch.takeIf { preferences.touchToolConfig == ToolConfig.Draw },
                PointerType.Stylus.takeIf { preferences.stylusToolConfig == ToolConfig.Draw },
                PointerType.Mouse.takeIf { preferences.mouseToolConfig == ToolConfig.Draw },
            )
        val erasingPointerTypes =
            setOfNotNull(
                PointerType.Touch.takeIf { preferences.touchToolConfig == ToolConfig.Erase },
                PointerType.Stylus.takeIf { preferences.stylusToolConfig == ToolConfig.Erase },
                PointerType.Mouse.takeIf { preferences.mouseToolConfig == ToolConfig.Erase },
            )

        var selectionState by selectionStateHolder::selectionState

        Box(
            Modifier
                .requiredSize(
                    scaledCellDpSize * numColumns,
                    scaledCellDpSize * numRows,
                )
                .testTag("CellCanvas")
                .drawingCellInput(
                    drawingPointerTypes = drawingPointerTypes,
                    erasingPointerTypes = erasingPointerTypes,
                    gameOfLifeState = gameOfLifeState,
                    pendingCellChanges = pendingCellChanges,
                    scaledCellPixelSize = scaledCellPixelSize,
                    cellWindow = cellWindow,
                ),
        ) {
            Layout(
                modifier = Modifier.fillMaxSize(),
                content = {
                    cellWindow.containedPoints().forEach { cell ->
                        key(cell) {
                            val isAliveInState = cell in gameOfLifeState.cellState.aliveCells
                            InteractableCell(
                                modifier = Modifier
                                    .size(scaledCellDpSize),
                                drawState = when (pendingCellChanges[cell]) {
                                    false -> if (isAliveInState) DrawState.PendingDead else DrawState.Dead
                                    true -> if (isAliveInState) DrawState.Alive else DrawState.PendingAlive
                                    null -> if (isAliveInState) DrawState.Alive else DrawState.Dead
                                },
                                shape = preferences.currentShape,
                                contentDescription = parameterizedStringResource(
                                    Strings.InteractableCellContentDescription(
                                        x = cell.x,
                                        y = cell.y,
                                    ),
                                ),
                                onValueChange = { isAlive ->
                                    gameOfLifeState.setCellState(
                                        cellCoordinate = cell,
                                        isAlive = isAlive,
                                    )
                                },
                                onLongClick = {
                                    selectionState = SelectionState.SelectingBox(
                                        topLeft = cell,
                                        width = 1,
                                        height = 1,
                                    )
                                },
                            )
                        }
                    }
                },
                measurePolicy = { measurables, _ ->
                    val placeables = measurables.map { it.measure(Constraints()) }

                    layout(
                        (numColumns * scaledCellPixelSize).roundToInt(),
                        (numRows * scaledCellPixelSize).roundToInt(),
                    ) {
                        placeables.forEachIndexed { index, placeable ->
                            val rowIndex = index / numColumns
                            val columnIndex = index % numColumns
                            placeable.place(
                                (columnIndex * scaledCellPixelSize).roundToInt(),
                                (rowIndex * scaledCellPixelSize).roundToInt(),
                            )
                        }
                    }
                },
            )

            AnimatedContent(
                targetState = selectionState,
                contentKey = {
                    when (it) {
                        SelectionState.NoSelection -> 0
                        is SelectionState.SelectingBox -> 1
                        is SelectionState.Selection -> 2
                    }
                },
                modifier = Modifier.fillMaxSize(),
            ) { targetSelectionState ->
                when (targetSelectionState) {
                    SelectionState.NoSelection -> {
                        Spacer(Modifier.fillMaxSize())
                    }
                    is SelectionState.SelectingBox -> {
                        Box(Modifier.fillMaxSize()) {
                            /**
                             * The key for the editing session, to allow wiping state on an external change.
                             */
                            var editingSessionKey by rememberSaveable(stateSaver = uuidSaver) {
                                mutableStateOf(UUID.randomUUID())
                            }

                            /**
                             * The known [SelectionState.SelectingBox] for valid values that we are setting.
                             */
                            var knownSelectionState: SelectionState.SelectingBox by remember {
                                mutableStateOf(targetSelectionState)
                            }

                            /**
                             * If `true`, the [targetSelectionState] was updated externally, and not via our own updates
                             * (which would have updated [knownSelectionState])
                             */
                            val didValueUpdateOutOfBand = knownSelectionState != targetSelectionState

                            // If a value update occurred out of band, then update our editing session
                            if (didValueUpdateOutOfBand) {
                                // Update the editing session key
                                editingSessionKey = UUID.randomUUID()
                                knownSelectionState = targetSelectionState
                            }

                            val initialHandleAOffset = targetSelectionState.topLeft
                            val initialHandleBOffset = targetSelectionState.topLeft +
                                IntOffset(targetSelectionState.width, 0)
                            val initialHandleCOffset = targetSelectionState.topLeft +
                                IntOffset(targetSelectionState.width, targetSelectionState.height)
                            val initialHandleDOffset = targetSelectionState.topLeft +
                                IntOffset(0, targetSelectionState.height)

                            val initialHandles = listOf(
                                initialHandleAOffset,
                                initialHandleBOffset,
                                initialHandleCOffset,
                                initialHandleDOffset,
                            )

                            val handleAnchors = remember(scaledCellPixelSize, cellWindow) {
                                object : DraggableAnchors2D<IntOffset> {
                                    override fun positionOf(value: IntOffset): Offset =
                                        (value.toOffset() - cellWindow.topLeft.toOffset()) * scaledCellPixelSize

                                    override fun hasAnchorFor(value: IntOffset): Boolean = true
                                    override fun closestAnchor(position: Offset): IntOffset =
                                        (position / scaledCellPixelSize).round() + cellWindow.topLeft

                                    override val size: Int = Int.MAX_VALUE
                                }
                            }

                            val confirmValueChangeStates = List(initialHandles.size) { index ->
                                key(index) {
                                    remember { mutableStateOf({ _: IntOffset -> true }) }
                                }
                            }

                            var newSelectionStateRequested: Boolean by remember { mutableStateOf(false) }

                            LaunchedEffect(newSelectionStateRequested) {
                                newSelectionStateRequested = false
                            }

                            val coroutineScope = rememberCoroutineScope()

                            val handleAnchoredDraggable2DStates =
                                initialHandles.mapIndexed { index, initialHandleOffset ->
                                    key(editingSessionKey, scaledCellPixelSize, cellWindow) {
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
                                                initialValue = initialHandleOffset,
                                                animationSpec = spring(),
                                                confirmValueChange = { intOffset ->
                                                    confirmValueChangeStates[index].value.invoke(intOffset)
                                                },
                                            )
                                        }.apply {
                                            updateAnchors(handleAnchors)
                                        }
                                    }
                                }

                            val handleAAnchoredDraggable2DState = handleAnchoredDraggable2DStates[0]
                            val handleBAnchoredDraggable2DState = handleAnchoredDraggable2DStates[1]
                            val handleCAnchoredDraggable2DState = handleAnchoredDraggable2DStates[2]
                            val handleDAnchoredDraggable2DState = handleAnchoredDraggable2DStates[3]

                            confirmValueChangeStates[0].value = { intOffset ->
                                if (!newSelectionStateRequested) {
                                    newSelectionStateRequested = true
                                    val minX = min(intOffset.x, handleCAnchoredDraggable2DState.targetValue.x)
                                    val maxX = max(intOffset.x, handleCAnchoredDraggable2DState.targetValue.x)
                                    val minY = min(intOffset.y, handleCAnchoredDraggable2DState.targetValue.y)
                                    val maxY = max(intOffset.y, handleCAnchoredDraggable2DState.targetValue.y)

                                    val newSelectionState = SelectionState.SelectingBox(
                                        IntOffset(minX, minY),
                                        width = maxX - minX,
                                        height = maxY - minY,
                                    )
                                    if (selectionStateHolder.selectionState != newSelectionState) {
                                        selectionStateHolder.selectionState = newSelectionState
                                        knownSelectionState = newSelectionState

                                        coroutineScope.launch {
                                            handleBAnchoredDraggable2DState.snapTo(
                                                IntOffset(
                                                    x = handleBAnchoredDraggable2DState.targetValue.x,
                                                    y = intOffset.y,
                                                ),
                                            )
                                            handleDAnchoredDraggable2DState.snapTo(
                                                IntOffset(
                                                    x = intOffset.x,
                                                    y = handleDAnchoredDraggable2DState.targetValue.y,
                                                ),
                                            )
                                        }
                                    }
                                }
                                true
                            }
                            confirmValueChangeStates[1].value = { intOffset ->
                                if (!newSelectionStateRequested) {
                                    newSelectionStateRequested = true
                                    val minX = min(intOffset.x, handleBAnchoredDraggable2DState.targetValue.x)
                                    val maxX = max(intOffset.x, handleBAnchoredDraggable2DState.targetValue.x)
                                    val minY = min(intOffset.y, handleBAnchoredDraggable2DState.targetValue.y)
                                    val maxY = max(intOffset.y, handleBAnchoredDraggable2DState.targetValue.y)

                                    val newSelectionState = SelectionState.SelectingBox(
                                        IntOffset(minX, minY),
                                        width = maxX - minX,
                                        height = maxY - minY,
                                    )

                                    if (selectionStateHolder.selectionState != newSelectionState) {
                                        selectionStateHolder.selectionState = newSelectionState
                                        knownSelectionState = newSelectionState

                                        coroutineScope.launch {
                                            handleAAnchoredDraggable2DState.snapTo(
                                                IntOffset(
                                                    x = handleAAnchoredDraggable2DState.targetValue.x,
                                                    y = intOffset.y,
                                                ),
                                            )
                                            handleCAnchoredDraggable2DState.snapTo(
                                                IntOffset(
                                                    x = intOffset.x,
                                                    y = handleCAnchoredDraggable2DState.targetValue.y,
                                                ),
                                            )
                                        }
                                    }
                                }
                                true
                            }
                            confirmValueChangeStates[2].value = { intOffset ->
                                if (!newSelectionStateRequested) {
                                    newSelectionStateRequested = true
                                    val minX = min(intOffset.x, handleAAnchoredDraggable2DState.targetValue.x)
                                    val maxX = max(intOffset.x, handleAAnchoredDraggable2DState.targetValue.x)
                                    val minY = min(intOffset.y, handleAAnchoredDraggable2DState.targetValue.y)
                                    val maxY = max(intOffset.y, handleAAnchoredDraggable2DState.targetValue.y)

                                    val newSelectionState = SelectionState.SelectingBox(
                                        IntOffset(minX, minY),
                                        width = maxX - minX,
                                        height = maxY - minY,
                                    )

                                    if (selectionStateHolder.selectionState != newSelectionState) {
                                        selectionStateHolder.selectionState = newSelectionState
                                        knownSelectionState = newSelectionState

                                        coroutineScope.launch {
                                            handleDAnchoredDraggable2DState.snapTo(
                                                IntOffset(
                                                    x = handleDAnchoredDraggable2DState.targetValue.x,
                                                    y = intOffset.y,
                                                ),
                                            )
                                            handleBAnchoredDraggable2DState.snapTo(
                                                IntOffset(
                                                    x = intOffset.x,
                                                    y = handleBAnchoredDraggable2DState.targetValue.y,
                                                ),
                                            )
                                        }
                                    }
                                }
                                true
                            }
                            confirmValueChangeStates[3].value = { intOffset ->
                                if (!newSelectionStateRequested) {
                                    newSelectionStateRequested = true
                                    val minX = min(intOffset.x, handleBAnchoredDraggable2DState.targetValue.x)
                                    val maxX = max(intOffset.x, handleBAnchoredDraggable2DState.targetValue.x)
                                    val minY = min(intOffset.y, handleBAnchoredDraggable2DState.targetValue.y)
                                    val maxY = max(intOffset.y, handleBAnchoredDraggable2DState.targetValue.y)

                                    val newSelectionState = SelectionState.SelectingBox(
                                        IntOffset(minX, minY),
                                        width = maxX - minX,
                                        height = maxY - minY,
                                    )

                                    if (selectionStateHolder.selectionState != newSelectionState) {
                                        selectionStateHolder.selectionState = newSelectionState
                                        knownSelectionState = newSelectionState

                                        coroutineScope.launch {
                                            handleCAnchoredDraggable2DState.snapTo(
                                                IntOffset(
                                                    x = handleCAnchoredDraggable2DState.targetValue.x,
                                                    y = intOffset.y,
                                                ),
                                            )
                                            handleAAnchoredDraggable2DState.snapTo(
                                                IntOffset(
                                                    x = intOffset.x,
                                                    y = handleAAnchoredDraggable2DState.targetValue.y,
                                                ),
                                            )
                                        }
                                    }
                                }
                                true
                            }

                            handleAnchoredDraggable2DStates.forEach {
                                it.updateAnchors(handleAnchors)
                            }

                            val handleAOffsetCalculator: () -> Offset = {
                                val xReferenceState =
                                    when {
                                        handleAAnchoredDraggable2DState.isDraggingOrAnimating() ->
                                            handleAAnchoredDraggable2DState

                                        handleDAnchoredDraggable2DState.isDraggingOrAnimating() ->
                                            handleDAnchoredDraggable2DState

                                        else ->
                                            handleAAnchoredDraggable2DState
                                    }
                                val yReferenceState =
                                    when {
                                        handleAAnchoredDraggable2DState.isDraggingOrAnimating() ->
                                            handleAAnchoredDraggable2DState

                                        handleBAnchoredDraggable2DState.isDraggingOrAnimating() ->
                                            handleBAnchoredDraggable2DState

                                        else ->
                                            handleAAnchoredDraggable2DState
                                    }

                                Offset(
                                    xReferenceState.requireOffset().x,
                                    yReferenceState.requireOffset().y,
                                )
                            }
                            val handleBOffsetCalculator: () -> Offset = {
                                val xReferenceState =
                                    when {
                                        handleBAnchoredDraggable2DState.isDraggingOrAnimating() ->
                                            handleBAnchoredDraggable2DState

                                        handleCAnchoredDraggable2DState.isDraggingOrAnimating() ->
                                            handleCAnchoredDraggable2DState

                                        else ->
                                            handleBAnchoredDraggable2DState
                                    }
                                val yReferenceState =
                                    when {
                                        handleBAnchoredDraggable2DState.isDraggingOrAnimating() ->
                                            handleBAnchoredDraggable2DState

                                        handleAAnchoredDraggable2DState.isDraggingOrAnimating() ->
                                            handleAAnchoredDraggable2DState

                                        else ->
                                            handleBAnchoredDraggable2DState
                                    }

                                Offset(
                                    xReferenceState.requireOffset().x,
                                    yReferenceState.requireOffset().y,
                                )
                            }
                            val handleCOffsetCalculator: () -> Offset = {
                                val xReferenceState =
                                    when {
                                        handleCAnchoredDraggable2DState.isDraggingOrAnimating() ->
                                            handleCAnchoredDraggable2DState

                                        handleBAnchoredDraggable2DState.isDraggingOrAnimating() ->
                                            handleBAnchoredDraggable2DState

                                        else ->
                                            handleCAnchoredDraggable2DState
                                    }
                                val yReferenceState =
                                    when {
                                        handleCAnchoredDraggable2DState.isDraggingOrAnimating() ->
                                            handleCAnchoredDraggable2DState

                                        handleDAnchoredDraggable2DState.isDraggingOrAnimating() ->
                                            handleDAnchoredDraggable2DState

                                        else ->
                                            handleCAnchoredDraggable2DState
                                    }

                                Offset(
                                    xReferenceState.requireOffset().x,
                                    yReferenceState.requireOffset().y,
                                )
                            }
                            val handleDOffsetCalculator: () -> Offset = {
                                val xReferenceState =
                                    when {
                                        handleDAnchoredDraggable2DState.isDraggingOrAnimating() ->
                                            handleDAnchoredDraggable2DState

                                        handleAAnchoredDraggable2DState.isDraggingOrAnimating() ->
                                            handleAAnchoredDraggable2DState

                                        else ->
                                            handleDAnchoredDraggable2DState
                                    }
                                val yReferenceState =
                                    when {
                                        handleDAnchoredDraggable2DState.isDraggingOrAnimating() ->
                                            handleDAnchoredDraggable2DState

                                        handleCAnchoredDraggable2DState.isDraggingOrAnimating() ->
                                            handleCAnchoredDraggable2DState

                                        else ->
                                            handleDAnchoredDraggable2DState
                                    }

                                Offset(
                                    xReferenceState.requireOffset().x,
                                    yReferenceState.requireOffset().y,
                                )
                            }

                            val offsetCalculators = listOf(
                                handleAOffsetCalculator,
                                handleBOffsetCalculator,
                                handleCOffsetCalculator,
                                handleDOffsetCalculator,
                            )

                            val selectionColor = MaterialTheme.colorScheme.secondary
                            Box(
                                modifier = Modifier
                                    .fillMaxSize()
                                    .layout { measurable, constraints ->
                                        val aOffset = handleAOffsetCalculator()
                                        val bOffset = handleBOffsetCalculator()
                                        val cOffset = handleCOffsetCalculator()
                                        val dOffset = handleDOffsetCalculator()

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

                                        val placeable = measurable.measure(selectionBoxConstraints)

                                        layout(constraints.maxWidth, constraints.maxHeight) {
                                            placeable.place(topLeft.round())
                                        }
                                    },
                            ) {
                                Canvas(
                                    modifier = Modifier.fillMaxSize(),
                                ) {
                                    val rect = size.toRect()
                                    drawRect(
                                        color = selectionColor,
                                        alpha = 0.2f,
                                    )
                                    val strokeWidth = 2.dp.toPx()
                                    val pathEffect = PathEffect.dashPathEffect(
                                        floatArrayOf(
                                            24.dp.toPx(),
                                            24.dp.toPx(),
                                        ),
                                    )

                                    drawLine(
                                        color = selectionColor,
                                        start = rect.topLeft,
                                        end = rect.topCenter,
                                        strokeWidth = strokeWidth,
                                        pathEffect = pathEffect,
                                    )
                                    drawLine(
                                        color = selectionColor,
                                        start = rect.topRight,
                                        end = rect.topCenter,
                                        strokeWidth = strokeWidth,
                                        pathEffect = pathEffect,
                                    )
                                    drawLine(
                                        color = selectionColor,
                                        start = rect.topLeft,
                                        end = rect.centerLeft,
                                        strokeWidth = strokeWidth,
                                        pathEffect = pathEffect,
                                    )
                                    drawLine(
                                        color = selectionColor,
                                        start = rect.bottomLeft,
                                        end = rect.centerLeft,
                                        strokeWidth = strokeWidth,
                                        pathEffect = pathEffect,
                                    )
                                    drawLine(
                                        color = selectionColor,
                                        start = rect.bottomLeft,
                                        end = rect.bottomCenter,
                                        strokeWidth = strokeWidth,
                                        pathEffect = pathEffect,
                                    )
                                    drawLine(
                                        color = selectionColor,
                                        start = rect.bottomRight,
                                        end = rect.bottomCenter,
                                        strokeWidth = strokeWidth,
                                        pathEffect = pathEffect,
                                    )
                                    drawLine(
                                        color = selectionColor,
                                        start = rect.topRight,
                                        end = rect.centerRight,
                                        strokeWidth = strokeWidth,
                                        pathEffect = pathEffect,
                                    )
                                    drawLine(
                                        color = selectionColor,
                                        start = rect.bottomRight,
                                        end = rect.centerRight,
                                        strokeWidth = strokeWidth,
                                        pathEffect = pathEffect,
                                    )
                                }
                            }

                            handleAnchoredDraggable2DStates
                                .zip(offsetCalculators)
                                .forEachIndexed { index, (anchoredDraggable2DState, offsetCalculator) ->
                                    key(index) {
                                        val interactionSource = remember { MutableInteractionSource() }
                                        Box(
                                            modifier = Modifier
                                                .offset {
                                                    offsetCalculator().round()
                                                }
                                                .offset((-24).dp, (-24).dp)
                                                .anchoredDraggable2D(
                                                    state = anchoredDraggable2DState,
                                                    interactionSource = interactionSource,
                                                )
                                                .size(48.dp),
                                            contentAlignment = Alignment.Center,
                                        ) {
                                            val isDragged by interactionSource.collectIsDraggedAsState()
                                            val isHovered by interactionSource.collectIsHoveredAsState()
                                            val isPressed by interactionSource.collectIsPressedAsState()

                                            val isActive = isDragged || isHovered || isPressed
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
                                }
                        }
                    }

                    is SelectionState.Selection -> {
                        Spacer(Modifier.fillMaxSize())
                    }
                }
            }
        }
    }
}

@Suppress("LongParameterList")
@OptIn(ExperimentalComposeUiApi::class)
private fun Modifier.drawingCellInput(
    drawingPointerTypes: Set<PointerType>,
    erasingPointerTypes: Set<PointerType>,
    gameOfLifeState: MutableGameOfLifeState,
    pendingCellChanges: MutableMap<IntOffset, Boolean>,
    scaledCellPixelSize: Float,
    cellWindow: IntRect,
): Modifier = composed {
    val currentScaledCellPixelSize by rememberUpdatedState(scaledCellPixelSize)
    val currentCellWindow by rememberUpdatedState(cellWindow)

    pointerInput(drawingPointerTypes, erasingPointerTypes, pendingCellChanges, gameOfLifeState) {
        detectDragGestures(
            onDragStart = {
                pendingCellChanges.clear()
            },
            onDragEnd = {
                if (pendingCellChanges.size == 1) {
                    // If the drawing change only hit one cell, treat it as a toggle
                    val cellCoordinate = pendingCellChanges.keys.first()
                    gameOfLifeState.setCellState(
                        cellCoordinate,
                        cellCoordinate !in gameOfLifeState.cellState.aliveCells,
                    )
                } else {
                    // Otherwise, add all of them
                    pendingCellChanges.forEach { (cellCoordinate, isAlive) ->
                        gameOfLifeState.setCellState(
                            cellCoordinate = cellCoordinate,
                            isAlive = isAlive,
                        )
                    }
                }
                pendingCellChanges.clear()
            },
            onDrag = { change, _ ->
                val path = LineSegmentPath(
                    (
                        listOf(change.previousPosition) +
                            change.historical.map(HistoricalChange::position) +
                            listOf(change.position)
                        )
                        .filter(Offset::isSpecified)
                        .map { it / currentScaledCellPixelSize },
                )
                val isAlive = when (change.type) {
                    in drawingPointerTypes -> true
                    in erasingPointerTypes -> false
                    else -> throw CancellationException("Non-stylus type!")
                }
                path.cellIntersections().forEach { localCoordinate ->
                    pendingCellChanges[localCoordinate + currentCellWindow.topLeft] = isAlive
                }
            },
        )
    }
}

fun <T> AnchoredDraggable2DState<T>.isDraggingOrAnimating(): Boolean =
    anchors.positionOf(currentValue) != requireOffset()
