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

import android.content.ClipData
import android.content.ClipDescription
import android.os.Build
import android.view.View
import androidx.compose.foundation.draganddrop.dragAndDropSource
import androidx.compose.foundation.draganddrop.dragAndDropTarget
import androidx.compose.runtime.Composable
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.ui.Modifier
import androidx.compose.ui.draganddrop.DragAndDropEvent
import androidx.compose.ui.draganddrop.DragAndDropTarget
import androidx.compose.ui.draganddrop.DragAndDropTransferData
import androidx.compose.ui.draganddrop.mimeTypes
import androidx.compose.ui.draganddrop.toAndroidDragEvent
import androidx.compose.ui.geometry.Offset
import com.alexvanyo.composelife.model.CellState
import com.alexvanyo.composelife.model.DeserializationResult
import com.alexvanyo.composelife.model.RunLengthEncodedCellStateSerializer
import com.alexvanyo.composelife.model.di.CellStateParserProvider
import kotlinx.coroutines.async
import kotlinx.coroutines.channels.Channel
import kotlinx.coroutines.flow.collect
import kotlinx.coroutines.flow.receiveAsFlow
import kotlinx.coroutines.launch
import kotlinx.coroutines.selects.select

actual fun Modifier.cellStateDragAndDropSource(
    getCellState: () -> CellState,
): Modifier =
    dragAndDropSource(
        transferData = {
            DragAndDropTransferData(
                clipData = ClipData.newPlainText(
                    "cellState",
                    RunLengthEncodedCellStateSerializer.serializeToString(getCellState())
                        .joinToString("\n"),
                ),
                flags = if (Build.VERSION.SDK_INT >= 24) {
                    View.DRAG_FLAG_GLOBAL
                } else {
                    0
                },
            )
        },
    )

context(CellStateParserProvider)
@Composable
@Suppress("ComposeComposableModifier")
actual fun Modifier.cellStateDragAndDropTarget(
    setSelectionToCellState: (CellState) -> Unit,
): Modifier {
    val coroutineScope = rememberCoroutineScope()
    val target = remember(cellStateParser, coroutineScope) {
        object : DragAndDropTarget {
            override fun onDrop(event: DragAndDropEvent): Boolean {
                val clipData = event.toAndroidDragEvent().clipData
                coroutineScope.launch {
                    when (
                        val deserializationResult = cellStateParser.parseCellState(clipData)
                    ) {
                        is DeserializationResult.Successful -> {
                            setSelectionToCellState(deserializationResult.cellState)
                        }
                        is DeserializationResult.Unsuccessful -> {
                            // TODO: Show error for unsuccessful drag and drop
                        }
                    }
                }
                return true
            }
        }
    }

    return dragAndDropTarget(
        shouldStartDragAndDrop = { event ->
            event.mimeTypes().contains(ClipDescription.MIMETYPE_TEXT_PLAIN)
        },
        target = target,
    )
}


context(CellStateParserProvider)
@OptIn(ExperimentalFoundationApi::class)
@Composable
@Suppress("ComposeComposableModifier")
fun Modifier.cellStateDragAndDropTarget(
    mutableCellStateDropStateHolder: MutableCellStateDropStateHolder,
    setSelectionToCellState: (CellState) -> Unit,
): Modifier {
    val coroutineScope = rememberCoroutineScope()
    val dragAndDropEvents = remember { Channel<CellStateDragAndDropEvent>(Channel.UNLIMITED) }

    LaunchedEffect(dragAndDropEvents) {
        while (true) {
            mutableCellStateDropStateHolder.cellStateDropState = CellStateDropState.None
            var event: CellStateDragAndDropEvent
            do {
                event = dragAndDropEvents.receive()
            } while (event !is CellStateDragAndDropEvent.Started)
            val startedEvent: CellStateDragAndDropEvent.Started = event

            val deserializationResultDeferred = async {
                cellStateParser.parseCellState(startedEvent.clipData)
            }

            var isEntered = false
            var offset: Offset = Offset.Zero

            while (event != CellStateDragAndDropEvent.Ended) {
                select {
                    deserializationResultDeferred.onAwait {}
                    dragAndDropEvents.onReceive {
                        event = it
                        when (it) {
                            CellStateDragAndDropEvent.Dropped -> {
                                val deserializationResult = deserializationResultDeferred.await()
                                when (deserializationResult) {
                                    is DeserializationResult.Successful -> {
                                        setSelectionToCellState(deserializationResult.cellState)
                                    }
                                    is DeserializationResult.Unsuccessful -> {
                                        // TODO: Show error for unsuccessful drag and drop
                                    }
                                }
                            }
                            CellStateDragAndDropEvent.Ended -> Unit
                            is CellStateDragAndDropEvent.Entered -> {
                                isEntered = true
                                offset = it.offset
                            }
                            CellStateDragAndDropEvent.Exited -> {
                                isEntered = false
                            }
                            is CellStateDragAndDropEvent.Moved -> {
                                check(isEntered)
                                offset = it.offset
                            }
                            is CellStateDragAndDropEvent.Started ->
                                throw IllegalStateException("")
                        }
                    }
                }

                mutableCellStateDropStateHolder.cellStateDropState =
                    if (isEntered && deserializationResultDeferred.isCompleted) {
                        val deserializationResult = deserializationResultDeferred.getCompleted()
                        when (deserializationResult) {
                            is DeserializationResult.Successful -> {
                                CellStateDropState.DropPreview(
                                    offset = offset,
                                    cellState = deserializationResult.cellState,
                                )
                            }
                            is DeserializationResult.Unsuccessful -> {
                                // TODO: Show error for what will be an unsuccessful drag and drop
                                CellStateDropState.ApplicableDropAvailable
                            }
                        }
                    } else {
                        CellStateDropState.ApplicableDropAvailable
                    }
            }

            deserializationResultDeferred.cancel()
        }
    }

    val target = remember(cellStateParser, coroutineScope) {
        object : DragAndDropTarget {
            override fun onStarted(event: DragAndDropEvent) {
                dragAndDropEvents.trySend(
                    CellStateDragAndDropEvent.Started(
                        event.toAndroidDragEvent().clipData
                    )
                )
            }

            override fun onEntered(event: DragAndDropEvent) {
                val androidDragEvent = event.toAndroidDragEvent()
                dragAndDropEvents.trySend(
                    CellStateDragAndDropEvent.Entered(
                        Offset(
                            androidDragEvent.x,
                            androidDragEvent.y,
                        )
                    )
                )
            }

            override fun onMoved(event: DragAndDropEvent) {
                val androidDragEvent = event.toAndroidDragEvent()
                dragAndDropEvents.trySend(
                    CellStateDragAndDropEvent.Moved(
                        Offset(
                            androidDragEvent.x,
                            androidDragEvent.y,
                        )
                    )
                )
            }

            override fun onExited(event: DragAndDropEvent) {
                dragAndDropEvents.trySend(
                    CellStateDragAndDropEvent.Exited
                )
            }

            override fun onEnded(event: DragAndDropEvent) {
                dragAndDropEvents.trySend(
                    CellStateDragAndDropEvent.Ended
                )
            }

            override fun onDrop(event: DragAndDropEvent): Boolean {
                dragAndDropEvents.trySend(
                    CellStateDragAndDropEvent.Dropped
                )
                return true
            }
        }
    }

    return dragAndDropTarget(
        shouldStartDragAndDrop = { event ->
            event.mimeTypes().contains(ClipDescription.MIMETYPE_TEXT_PLAIN)
        },
        target = target,
    )
}

private sealed interface CellStateDragAndDropEvent {
    data class Started(
        val clipData: ClipData
    ) : CellStateDragAndDropEvent
    data class Entered(
        val offset: Offset
    ) : CellStateDragAndDropEvent
    data class Moved(
        val offset: Offset
    ) : CellStateDragAndDropEvent
    data object Exited : CellStateDragAndDropEvent
    data object Ended : CellStateDragAndDropEvent
    data object Dropped : CellStateDragAndDropEvent
}
