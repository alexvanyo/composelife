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

import androidx.compose.runtime.Composable
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.Stable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateListOf
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberUpdatedState
import androidx.compose.runtime.setValue
import androidx.compose.runtime.snapshotFlow
import androidx.compose.ui.draganddrop.DragAndDropEvent
import androidx.compose.ui.draganddrop.DragAndDropTarget
import androidx.compose.ui.geometry.Offset
import com.alexvanyo.composelife.logging.Logger
import com.alexvanyo.composelife.logging.d
import com.alexvanyo.composelife.model.CellState
import com.alexvanyo.composelife.model.CellStateParser
import com.alexvanyo.composelife.model.DeserializationResult
import com.alexvanyo.composelife.model.di.CellStateParserProvider
import com.alexvanyo.composelife.updatable.Updatable
import kotlinx.coroutines.flow.channelFlow
import kotlinx.coroutines.flow.filter
import kotlinx.coroutines.flow.first
import kotlinx.coroutines.launch

/**
 * The state of drag and drop for a cell state.
 */
sealed interface CellStateDropState {

    /**
     * There is no active drop for the cell state
     */
    data object None : CellStateDropState

    /**
     * There is an active drop for the cell state in progress, but isn't previewable yet.
     */
    data object ApplicableDropAvailable : CellStateDropState

    /**
     * There is an active previewable drop for the cell state
     */
    data class DropPreview(
        val offset: Offset,
        val cellState: CellState,
    ) : CellStateDropState
}

/**
 * A state holder for a [CellStateDropState].
 */
@Stable
interface CellStateDropStateHolder {
    val cellStateDropState: CellStateDropState
}

/**
 * A mutable state holder for a [CellStateDropState].
 *
 * This is also a [DragAndDropTarget] to be passed to a drag and drop target to update the current drop state.
 */
@Stable
sealed interface MutableCellStateDropStateHolder : CellStateDropStateHolder, DragAndDropTarget

internal expect class DragAndDropSession() {
    val isEntered: Boolean
    val isEnded: Boolean
    val isDropped: Boolean
    val rootOffset: Offset
    var deserializationResult: DeserializationResult?

    fun updateWithOnStarted(event: DragAndDropEvent)
    fun updateWithOnEntered(event: DragAndDropEvent)
    fun updateWithOnMoved(event: DragAndDropEvent)
    fun updateWithOnExited(event: DragAndDropEvent)
    fun updateWithOnEnded(event: DragAndDropEvent)
    fun updateWithOnDrop(event: DragAndDropEvent)
}

/**
 * Given a [session] and [cellStateParser], awaits for a [DeserializationResult] from the data available in the
 * session and parsing it.
 */
internal expect suspend fun awaitAndParseCellState(
    session: DragAndDropSession,
    cellStateParser: CellStateParser,
): DeserializationResult

@Stable
internal class MutableCellStateDropStateHolderImpl(
    private val cellStateParser: CellStateParser,
    private val setSelectionToCellState: (dropOffset: Offset, cellState: CellState) -> Unit,
) : MutableCellStateDropStateHolder, Updatable {

    var positionInRoot: Offset by mutableStateOf(Offset.Zero)

    private val dragAndDropSessions: MutableList<DragAndDropSession> = mutableStateListOf()

    override val cellStateDropState: CellStateDropState
        get() = if (dragAndDropSessions.isEmpty()) {
            CellStateDropState.None
        } else {
            val activeSession = dragAndDropSessions.first()
            val deserializationResult = activeSession.deserializationResult
            if (activeSession.isEntered && deserializationResult != null) {
                when (deserializationResult) {
                    is DeserializationResult.Successful -> {
                        CellStateDropState.DropPreview(
                            offset = activeSession.rootOffset - positionInRoot,
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

    override fun onStarted(event: DragAndDropEvent) {
        Logger.d { "onStarted: $event" }
        val activeSession = DragAndDropSession()
        activeSession.updateWithOnStarted(event)
        dragAndDropSessions.add(activeSession)
    }

    override fun onEntered(event: DragAndDropEvent) {
        Logger.d { "onEntered: $event" }
        dragAndDropSessions.last().updateWithOnEntered(event)
    }

    override fun onMoved(event: DragAndDropEvent) {
        Logger.d { "onMoved: $event" }
        dragAndDropSessions.last().updateWithOnMoved(event)
    }

    override fun onExited(event: DragAndDropEvent) {
        Logger.d { "onExited: $event" }
        dragAndDropSessions.last().updateWithOnExited(event)
    }

    override fun onEnded(event: DragAndDropEvent) {
        Logger.d { "onEnded: $event" }
        dragAndDropSessions.last().updateWithOnEnded(event)
    }

    override fun onDrop(event: DragAndDropEvent): Boolean {
        Logger.d { "onDrop: $event" }
        dragAndDropSessions.last().updateWithOnDrop(event)
        return true
    }

    override suspend fun update(): Nothing {
        snapshotFlow { dragAndDropSessions.firstOrNull() }
            .collect { session ->
                if (session != null) {
                    // If the session isn't null, race the following two events, of which only one should complete:
                    // - the session ends without dropping
                    // - the session acquires data, is dropped, and then ends
                    channelFlow {
                        launch {
                            snapshotFlow { session.isEnded && !session.isDropped }.filter { it }.first()
                            Logger.d { "Session ended without dropping" }
                            send(Unit)
                        }
                        launch {
                            val deserializationResult = awaitAndParseCellState(session, cellStateParser)
                            session.deserializationResult = deserializationResult
                            snapshotFlow { session.isDropped }.filter { it }.first()
                            when (deserializationResult) {
                                is DeserializationResult.Successful -> {
                                    setSelectionToCellState(
                                        session.rootOffset - positionInRoot,
                                        deserializationResult.cellState,
                                    )
                                }
                                is DeserializationResult.Unsuccessful -> {
                                    // TODO: Show error for unsuccessful drag and drop
                                }
                            }
                            snapshotFlow { session.isEnded }.filter { it }.first()
                            Logger.d { "Session dropped and ended" }
                            send(Unit)
                        }
                    }.first()
                    // Remove the active session
                    dragAndDropSessions.removeAt(0)
                }
            }

        error("snapshotFlow cannot complete normally")
    }
}

/**
 * Remember a [MutableCellStateDropStateHolder] with the given [setSelectionToCellState] callback upon dropping.
 *
 * The passed [dropOffset] will be in the local coordinates of the [cellStateDragAndDropTarget].
 */
context(cellStateParserProvider: CellStateParserProvider)
@Composable
fun rememberMutableCellStateDropStateHolder(
    setSelectionToCellState: (dropOffset: Offset, cellState: CellState) -> Unit,
): MutableCellStateDropStateHolder {
    val currentSetSelectionToCellState by rememberUpdatedState(setSelectionToCellState)
    val mutableCellStateDropStateHolderImpl = remember(cellStateParserProvider.cellStateParser) {
        MutableCellStateDropStateHolderImpl(cellStateParserProvider.cellStateParser) { dropOffset, cellState ->
            currentSetSelectionToCellState(dropOffset, cellState)
        }
    }
    LaunchedEffect(mutableCellStateDropStateHolderImpl) {
        mutableCellStateDropStateHolderImpl.update()
    }
    return mutableCellStateDropStateHolderImpl
}
