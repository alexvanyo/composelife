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

package com.alexvanyo.composelife.ui.app.cells

import androidx.compose.foundation.ExperimentalFoundationApi
import androidx.compose.foundation.draganddrop.DragAndDropSourceScope
import androidx.compose.foundation.draganddrop.dragAndDropSource
import androidx.compose.foundation.draganddrop.dragAndDropTarget
import androidx.compose.foundation.gestures.detectTapGestures
import androidx.compose.runtime.Composable
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.ui.DragData
import androidx.compose.ui.ExperimentalComposeUiApi
import androidx.compose.ui.Modifier
import androidx.compose.ui.draganddrop.DragAndDropEvent
import androidx.compose.ui.draganddrop.DragAndDropModifierNode
import androidx.compose.ui.draganddrop.DragAndDropTarget
import androidx.compose.ui.draganddrop.DragAndDropTransferAction
import androidx.compose.ui.draganddrop.DragAndDropTransferData
import androidx.compose.ui.draganddrop.DragAndDropTransferable
import androidx.compose.ui.draganddrop.dragData
import androidx.compose.ui.draw.CacheDrawModifierNode
import androidx.compose.ui.draw.CacheDrawScope
import androidx.compose.ui.draw.DrawResult
import androidx.compose.ui.graphics.asComposeCanvas
import androidx.compose.ui.graphics.drawscope.DrawScope
import androidx.compose.ui.graphics.drawscope.draw
import androidx.compose.ui.graphics.drawscope.drawIntoCanvas
import androidx.compose.ui.graphics.nativeCanvas
import androidx.compose.ui.input.pointer.PointerInputScope
import androidx.compose.ui.input.pointer.SuspendingPointerInputModifierNode
import androidx.compose.ui.node.DelegatingNode
import androidx.compose.ui.node.LayoutAwareModifierNode
import androidx.compose.ui.node.ModifierNodeElement
import androidx.compose.ui.platform.InspectorInfo
import androidx.compose.ui.unit.IntSize
import androidx.compose.ui.unit.toSize
import com.alexvanyo.composelife.model.CellState
import com.alexvanyo.composelife.model.DeserializationResult
import com.alexvanyo.composelife.model.RunLengthEncodedCellStateSerializer
import com.alexvanyo.composelife.ui.app.ClipboardCellStateParserProvider
import kotlinx.coroutines.launch
import org.jetbrains.skia.Picture
import org.jetbrains.skia.PictureRecorder
import org.jetbrains.skia.Rect
import java.awt.datatransfer.StringSelection

@OptIn(ExperimentalFoundationApi::class, ExperimentalComposeUiApi::class)
actual fun Modifier.cellStateDragAndDropSource(getCellState: () -> CellState): Modifier =
    dragAndDropSource {
        detectTapGestures(
            onLongPress = {
                startTransfer(
                    DragAndDropTransferData(
                        transferable = DragAndDropTransferable(
                            transferable = StringSelection(
                                RunLengthEncodedCellStateSerializer.serializeToString(getCellState())
                                    .joinToString("\n"),
                            ),
                        ),
                        supportedActions = listOf(DragAndDropTransferAction.Copy),
                    ),
                )
            },
        )
    }

@ExperimentalFoundationApi
fun Modifier.dragAndDropSource(
    block: suspend DragAndDropSourceScope.() -> Unit,
): Modifier = this then DragAndDropSourceWithDefaultShadowElement(
    dragAndDropSourceHandler = block,
)

@ExperimentalFoundationApi
private class DragAndDropSourceWithDefaultShadowElement(
    /**
     * @see Modifier.dragAndDropSource
     */
    val dragAndDropSourceHandler: suspend DragAndDropSourceScope.() -> Unit,
) : ModifierNodeElement<DragSourceNodeWithDefaultPainter>() {
    override fun create() = DragSourceNodeWithDefaultPainter(
        dragAndDropSourceHandler = dragAndDropSourceHandler,
    )

    override fun update(node: DragSourceNodeWithDefaultPainter) = with(node) {
        dragAndDropSourceHandler =
            this@DragAndDropSourceWithDefaultShadowElement.dragAndDropSourceHandler
    }

    override fun InspectorInfo.inspectableProperties() {
        name = "dragSourceWithDefaultPainter"
        properties["dragAndDropSourceHandler"] = dragAndDropSourceHandler
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is DragAndDropSourceWithDefaultShadowElement) return false

        return dragAndDropSourceHandler == other.dragAndDropSourceHandler
    }

    override fun hashCode(): Int {
        return dragAndDropSourceHandler.hashCode()
    }
}

@ExperimentalFoundationApi
private class DragSourceNodeWithDefaultPainter(
    var dragAndDropSourceHandler: suspend DragAndDropSourceScope.() -> Unit,
) : DelegatingNode() {

    init {
        val cacheDrawScopeDragShadowCallback = CacheDrawScopeDragShadowCallback().also {
            delegate(CacheDrawModifierNode(it::cachePicture))
        }
        delegate(
            DragAndDropSourceNode(
                drawDragDecoration = {
                    cacheDrawScopeDragShadowCallback.drawDragShadow(this)
                },
                dragAndDropSourceHandler = {
                    dragAndDropSourceHandler.invoke(this)
                },
            ),
        )
    }
}

@ExperimentalFoundationApi
internal class DragAndDropSourceNode(
    var drawDragDecoration: DrawScope.() -> Unit,
    var dragAndDropSourceHandler: suspend DragAndDropSourceScope.() -> Unit,
) : DelegatingNode(),
    LayoutAwareModifierNode {

    private var size: IntSize = IntSize.Zero

    init {
        val dragAndDropModifierNode = delegate(
            DragAndDropModifierNode(),
        )

        delegate(
            SuspendingPointerInputModifierNode {
                dragAndDropSourceHandler(
                    object : DragAndDropSourceScope, PointerInputScope by this {
                        override fun startTransfer(transferData: DragAndDropTransferData) =
                            dragAndDropModifierNode.drag(
                                transferData = transferData,
                                decorationSize = size.toSize(),
                                drawDragDecoration = drawDragDecoration,
                            )
                    },
                )
            },
        )
    }

    override fun onRemeasured(size: IntSize) {
        this.size = size
    }
}

@ExperimentalFoundationApi
private class CacheDrawScopeDragShadowCallback {
    private var cachedPicture: Picture? = null

    fun drawDragShadow(drawScope: DrawScope) = with(drawScope) {
        when (val picture = cachedPicture) {
            null -> throw IllegalArgumentException(
                "No cached drag shadow. Check if Modifier.cacheDragShadow(painter) was called.",
            )

            else -> drawIntoCanvas { canvas ->
                canvas.nativeCanvas.drawPicture(picture)
            }
        }
    }

    fun cachePicture(scope: CacheDrawScope): DrawResult = with(scope) {
        val pictureRecorder = PictureRecorder()
        val width = this.size.width
        val height = this.size.height
        onDrawWithContent {
            val pictureCanvas = pictureRecorder.beginRecording(Rect.makeWH(width, height)).asComposeCanvas()
            draw(
                density = this,
                layoutDirection = this.layoutDirection,
                canvas = pictureCanvas,
                size = this.size,
            ) {
                this@onDrawWithContent.drawContent()
            }
            val picture = pictureRecorder.finishRecordingAsPicture()
            cachedPicture = picture

            drawIntoCanvas { canvas -> canvas.nativeCanvas.drawPicture(picture) }
        }
    }
}

context(ClipboardCellStateParserProvider)
@OptIn(ExperimentalComposeUiApi::class, ExperimentalFoundationApi::class)
@Composable
@Suppress("ComposeComposableModifier")
actual fun Modifier.cellStateDragAndDropTarget(
    setSelectionToCellState: (CellState) -> Unit,
): Modifier {
    val coroutineScope = rememberCoroutineScope()
    val target = remember(clipboardCellStateParser, coroutineScope) {
        object : DragAndDropTarget {
            override fun onDrop(event: DragAndDropEvent): Boolean {
                coroutineScope.launch {
                    when (
                        val deserializationResult = clipboardCellStateParser.parseCellState(event)
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
            event.dragData() is DragData.Text
        },
        target = target,
    )
}
