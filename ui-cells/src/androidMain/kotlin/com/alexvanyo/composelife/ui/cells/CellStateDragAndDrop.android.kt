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
import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.setValue
import androidx.compose.runtime.snapshotFlow
import androidx.compose.ui.Modifier
import androidx.compose.ui.draganddrop.DragAndDropEvent
import androidx.compose.ui.draganddrop.DragAndDropTransferData
import androidx.compose.ui.draganddrop.mimeTypes
import androidx.compose.ui.draganddrop.toAndroidDragEvent
import androidx.compose.ui.draw.drawWithCache
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.graphics.layer.drawLayer
import androidx.compose.ui.graphics.rememberGraphicsLayer
import com.alexvanyo.composelife.model.CellState
import com.alexvanyo.composelife.model.CellStateParser
import com.alexvanyo.composelife.model.DeserializationResult
import com.alexvanyo.composelife.model.RunLengthEncodedCellStateSerializer
import kotlinx.coroutines.flow.filterNotNull
import kotlinx.coroutines.flow.first

@Composable
actual fun Modifier.cellStateDragAndDropSource(
    getCellState: () -> CellState,
): Modifier {
    // TODO: Remove graphics layer workaround once default drag decoration works with Coil.
    //       https://github.com/coil-kt/coil/issues/2150
    val graphicsLayer = rememberGraphicsLayer()
    return drawWithCache {
        graphicsLayer.record { drawContent() }
        onDrawWithContent { drawLayer(graphicsLayer) }
    }
        .dragAndDropSource(
            drawDragDecoration = {
                drawLayer(graphicsLayer)
            },
            transferData = {
                val clipData = ClipData.newPlainText(
                    "cellState",
                    RunLengthEncodedCellStateSerializer.serializeToString(getCellState())
                        .joinToString("\n"),
                )

                DragAndDropTransferData(
                    clipData = clipData,
                    localState = clipData,
                    flags = if (Build.VERSION.SDK_INT >= 24) {
                        View.DRAG_FLAG_GLOBAL
                    } else {
                        0
                    },
                )
            },
        )
}

internal actual fun cellStateShouldStartDragAndDrop(event: DragAndDropEvent): Boolean =
    event.mimeTypes().contains(ClipDescription.MIMETYPE_TEXT_PLAIN)

internal actual class DragAndDropSession {
    private var _isEntered by mutableStateOf(false)
    private var _isEnded by mutableStateOf(false)
    private var _isDropped by mutableStateOf(false)
    private var _rootOffset by mutableStateOf(Offset.Zero)

    actual val isEntered get() = _isEntered
    actual val isEnded get() = _isEnded
    actual val isDropped get() = _isDropped
    actual val rootOffset get() = _rootOffset
    var clipData by mutableStateOf<ClipData?>(null)
    actual var deserializationResult by mutableStateOf<DeserializationResult?>(null)

    actual fun updateWithOnStarted(event: DragAndDropEvent) {
        val androidDragEvent = event.toAndroidDragEvent()
        clipData = androidDragEvent.clipData ?: androidDragEvent.localState as? ClipData
    }

    actual fun updateWithOnEntered(event: DragAndDropEvent) {
        val androidDragEvent = event.toAndroidDragEvent()
        clipData = androidDragEvent.clipData ?: androidDragEvent.localState as? ClipData
        _isEntered = true
        _rootOffset = Offset(androidDragEvent.x, androidDragEvent.y)
    }

    actual fun updateWithOnMoved(event: DragAndDropEvent) {
        val androidDragEvent = event.toAndroidDragEvent()
        clipData = androidDragEvent.clipData ?: androidDragEvent.localState as? ClipData
        _rootOffset = Offset(androidDragEvent.x, androidDragEvent.y)
    }

    actual fun updateWithOnExited(event: DragAndDropEvent) {
        val androidDragEvent = event.toAndroidDragEvent()
        clipData = androidDragEvent.clipData ?: androidDragEvent.localState as? ClipData
        _isEntered = false
        _rootOffset = Offset(androidDragEvent.x, androidDragEvent.y)
    }

    actual fun updateWithOnEnded(event: DragAndDropEvent) {
        val androidDragEvent = event.toAndroidDragEvent()
        clipData = androidDragEvent.clipData ?: androidDragEvent.localState as? ClipData
        _isEnded = true
    }

    actual fun updateWithOnDrop(event: DragAndDropEvent) {
        val androidDragEvent = event.toAndroidDragEvent()
        clipData = androidDragEvent.clipData
        _rootOffset = Offset(androidDragEvent.x, androidDragEvent.y)
        _isDropped = true
    }
}

internal actual suspend fun awaitAndParseCellState(
    session: DragAndDropSession,
    cellStateParser: CellStateParser,
): DeserializationResult =
    cellStateParser.parseCellState(
        snapshotFlow { session.clipData }.filterNotNull().first(),
    )
