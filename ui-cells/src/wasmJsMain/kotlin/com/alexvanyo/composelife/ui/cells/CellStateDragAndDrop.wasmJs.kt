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

import androidx.compose.foundation.draganddrop.dragAndDropSource
import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.setValue
import androidx.compose.runtime.snapshotFlow
import androidx.compose.ui.ExperimentalComposeUiApi
import androidx.compose.ui.Modifier
import androidx.compose.ui.draganddrop.DragAndDropEvent
import androidx.compose.ui.draganddrop.DragAndDropTransferData
import androidx.compose.ui.draganddrop.domDataTransferOrNull
import androidx.compose.ui.geometry.Offset
import com.alexvanyo.composelife.model.CellState
import com.alexvanyo.composelife.model.CellStateParser
import com.alexvanyo.composelife.model.DeserializationResult
import com.alexvanyo.composelife.model.RunLengthEncodedCellStateSerializer
import com.alexvanyo.composelife.model.parseCellState
import kotlinx.coroutines.flow.filterNotNull
import kotlinx.coroutines.flow.first
import org.w3c.dom.DataTransfer

@OptIn(ExperimentalComposeUiApi::class)
@Composable
actual fun Modifier.cellStateDragAndDropSource(getCellState: () -> CellState): Modifier =
    dragAndDropSource { offset ->
        DragAndDropTransferData(
            nativeTransferData = createDataTransfer().apply {
                setData(
                    "text/plain",
                    RunLengthEncodedCellStateSerializer.serializeToString(getCellState())
                        .joinToString("\n"),
                )
            },
        )
    }

@OptIn(ExperimentalComposeUiApi::class, ExperimentalWasmJsInterop::class)
internal actual fun cellStateShouldStartDragAndDrop(event: DragAndDropEvent): Boolean =
    "text/plain" in event.transferData?.domDataTransferOrNull?.types?.toList().orEmpty().map { it.toString() }

@OptIn(ExperimentalComposeUiApi::class)
internal actual class DragAndDropSession {
    private var _isEntered by mutableStateOf(false)
    private var _isEnded by mutableStateOf(false)
    private var _isDropped by mutableStateOf(false)
    private var _rootOffset by mutableStateOf(Offset.Zero)

    actual val isEntered get() = _isEntered
    actual val isEnded get() = _isEnded
    actual val isDropped get() = _isDropped
    actual val rootOffset get() = _rootOffset
    var dragData by mutableStateOf<DragAndDropTransferData?>(null)
    actual var deserializationResult by mutableStateOf<DeserializationResult?>(null)

    actual fun updateWithOnStarted(event: DragAndDropEvent) {
        dragData = event.transferData
    }

    actual fun updateWithOnEntered(event: DragAndDropEvent) {
        _isEntered = true
        _rootOffset = event.positionInRoot
    }

    actual fun updateWithOnMoved(event: DragAndDropEvent) {
        _rootOffset = event.positionInRoot
    }

    actual fun updateWithOnExited(event: DragAndDropEvent) {
        _isEntered = false
        _rootOffset = event.positionInRoot
    }

    actual fun updateWithOnEnded(event: DragAndDropEvent) {
        _isEnded = true
    }

    actual fun updateWithOnDrop(event: DragAndDropEvent) {
        _isDropped = true
        _rootOffset = event.positionInRoot
    }
}

@OptIn(ExperimentalComposeUiApi::class)
private val DragAndDropEvent.positionInRoot get() =
    Offset.Zero

@OptIn(ExperimentalComposeUiApi::class)
internal actual suspend fun awaitAndParseCellState(
    session: DragAndDropSession,
    cellStateParser: CellStateParser,
): DeserializationResult =
    cellStateParser.parseCellState(
        snapshotFlow { session.dragData?.domDataTransferOrNull }.filterNotNull().first().getData("text/plain"),
    )

@OptIn(ExperimentalWasmJsInterop::class)
private fun createDataTransfer(): DataTransfer = js("new DataTransfer()")
