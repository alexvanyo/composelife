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

package com.alexvanyo.composelife.ui.cells

import androidx.compose.foundation.layout.Spacer
import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.foundation.layout.requiredSize
import androidx.compose.material3.MaterialTheme
import androidx.compose.runtime.Composable
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.draw.drawWithContent
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.geometry.Size
import androidx.compose.ui.geometry.center
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.graphics.drawscope.ContentDrawScope
import androidx.compose.ui.graphics.graphicsLayer
import androidx.compose.ui.layout.layout
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.unit.Constraints
import androidx.compose.ui.unit.Dp
import androidx.compose.ui.unit.dp
import androidx.compose.ui.unit.round
import androidx.compose.ui.unit.toIntRect
import androidx.compose.ui.unit.toOffset
import androidx.compose.ui.unit.toRect
import androidx.compose.ui.unit.toSize
import com.alexvanyo.composelife.geometry.times
import com.alexvanyo.composelife.model.CellState
import com.alexvanyo.composelife.model.CellWindow
import com.alexvanyo.composelife.model.di.CellStateParserProvider
import com.alexvanyo.composelife.sessionvalue.SessionValue
import com.alexvanyo.composelife.sessionvalue.preLocalSessionId
import com.alexvanyo.composelife.sessionvalue.rememberSessionValueHolder
import com.alexvanyo.composelife.ui.util.AnchoredDraggable2DState
import com.alexvanyo.composelife.ui.util.AnimatedContent
import com.alexvanyo.composelife.ui.util.TargetState
import kotlin.math.max
import kotlin.math.min
import kotlin.math.roundToInt
import kotlin.uuid.Uuid

/**
 * The overlay based on the [selectionSessionState].
 */
context(CellStateParserProvider)
@Suppress("LongMethod", "LongParameterList", "CyclomaticComplexMethod")
@Composable
fun SelectionOverlay(
    selectionSessionState: SessionValue<SelectionState>,
    setSelectionSessionState: (SessionValue<SelectionState>) -> Unit,
    getSelectionCellState: (SelectionState) -> CellState,
    scaledCellDpSize: Dp,
    cellWindow: CellWindow,
    pixelOffsetFromCenter: Offset,
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

    val scaledCellPixelSize = with(LocalDensity.current) { scaledCellDpSize.toPx() }
    val cellStateDropStateHolder = rememberMutableCellStateDropStateHolder { dropOffset, cellState ->
        setSelectionSessionState(
            SessionValue(
                sessionId = Uuid.random(),
                valueId = Uuid.random(),
                value = SelectionState.Selection(
                    cellState = cellState,
                    offset = (
                        cellWindow.topLeft.toOffset() + (dropOffset / scaledCellPixelSize) -
                            cellState.boundingBox.size.toSize().center
                        ).round(),
                ),
            ),
        )
    }

    val dropAvailableBorderColor = MaterialTheme.colorScheme.tertiary
    val dropPreviewCellStateBorderColor = MaterialTheme.colorScheme.secondary

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
            .drawWithContent {
                drawContent()

                when (cellStateDropStateHolder.cellStateDropState) {
                    CellStateDropState.ApplicableDropAvailable,
                    is CellStateDropState.DropPreview,
                    -> {
                        drawDashedRect(
                            selectionColor = dropAvailableBorderColor,
                            strokeWidth = 4.dp.toPx(),
                            intervals = floatArrayOf(
                                24.dp.toPx(),
                                24.dp.toPx(),
                            ),
                            phase = 12.dp.toPx(),
                        )
                    }
                    CellStateDropState.None -> Unit
                }
            }
            .graphicsLayer {
                this.translationX = -pixelOffsetFromCenter.x
                this.translationY = -pixelOffsetFromCenter.y
            }
            .requiredSize(
                scaledCellDpSize * cellWindow.width,
                scaledCellDpSize * cellWindow.height,
            )
            .cellStateDragAndDropTarget(
                mutableCellStateDropStateHolder = cellStateDropStateHolder,
            )
            .drawWithContent {
                drawContent()

                when (val cellStateDropState = cellStateDropStateHolder.cellStateDropState) {
                    CellStateDropState.ApplicableDropAvailable -> Unit
                    is CellStateDropState.DropPreview -> {
                        drawDropPreview(
                            dropPreview = cellStateDropState,
                            scaledCellDpSize = scaledCellDpSize,
                            cellStateOutlineColor = dropPreviewCellStateBorderColor,
                        )
                    }

                    CellStateDropState.None -> Unit
                }
            },
    ) { (targetSelectionSessionState, _) ->
        when (val targetSelectionState = targetSelectionSessionState.value) {
            SelectionState.NoSelection -> {
                Spacer(Modifier.fillMaxSize())
            }

            is SelectionState.SelectingBox.FixedSelectingBox -> {
                @Suppress("UNCHECKED_CAST")
                (
                    FixedSelectingBoxOverlay(
                        selectionSessionState = targetSelectionSessionState as
                            SessionValue<SelectionState.SelectingBox.FixedSelectingBox>,
                        setSelectionState = selectionSessionStateValueHolder::setValue,
                        getSelectionCellState = {
                            getSelectionCellState(targetSelectionState)
                        },
                        scaledCellPixelSize = with(LocalDensity.current) { scaledCellDpSize.toPx() },
                        cellWindow = cellWindow,
                        modifier = Modifier.fillMaxSize(),
                    )
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
                    getSelectionCellState = {
                        getSelectionCellState(targetSelectionState)
                    },
                    scaledCellPixelSize = with(LocalDensity.current) { scaledCellDpSize.toPx() },
                    cellWindow = cellWindow,
                    modifier = Modifier.fillMaxSize(),
                )
            }
        }
    }
}

private fun ContentDrawScope.drawDropPreview(
    dropPreview: CellStateDropState.DropPreview,
    scaledCellDpSize: Dp,
    cellStateOutlineColor: Color,
) {
    drawDashedRect(
        selectionColor = cellStateOutlineColor,
        strokeWidth = 2.dp.toPx(),
        intervals = floatArrayOf(
            24.dp.toPx(),
            12.dp.toPx(),
        ),
        phase = 12.dp.toPx(),
        rect = (
            (
                dropPreview.cellState.boundingBox.size.toIntRect().toRect()
                    .translate(-dropPreview.cellState.boundingBox.size.toSize().center)
                ) * scaledCellDpSize.toPx()
            ).translate(dropPreview.offset),
    )
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

fun <T> AnchoredDraggable2DState<T>.isDraggingOrAnimating(): Boolean =
    anchors.positionOf(currentValue) != requireOffset()
