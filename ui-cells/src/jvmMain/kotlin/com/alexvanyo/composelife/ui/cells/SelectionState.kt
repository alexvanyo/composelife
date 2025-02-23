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

import androidx.compose.runtime.Composable
import androidx.compose.runtime.Stable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.saveable.Saver
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.setValue
import androidx.compose.ui.geometry.Rect
import androidx.compose.ui.unit.IntOffset
import com.alexvanyo.composelife.model.CellState
import com.alexvanyo.composelife.serialization.IntOffsetSerializer
import com.alexvanyo.composelife.serialization.RectSerializer
import com.alexvanyo.composelife.serialization.saver
import com.alexvanyo.composelife.sessionvalue.SessionValue
import kotlinx.serialization.Serializable

/**
 * A hierarchy of possible states for a selection of cells.
 */
@Serializable
sealed interface SelectionState {

    /**
     * No selection.
     */
    @Serializable
    data object NoSelection : SelectionState

    /**
     * A selecting box that describes a rectangle of some size and location in the cell universe.
     */
    @Serializable
    sealed interface SelectingBox : SelectionState {

        /**
         * A cell-grid-aligned selecting box.
         */
        @Serializable
        data class FixedSelectingBox(
            /**
             * The top left coordinate of the box.
             */
            @Serializable(with = IntOffsetSerializer::class) val topLeft: IntOffset,
            /**
             * The width of the box, which may be negative.
             */
            val width: Int,
            /**
             * The height of the box, which may be negative.
             */
            val height: Int,
            /**
             * The previous [TransientSelectingBox] that was used to create the current [FixedSelectingBox], if any.
             */
            val previousTransientSelectingBox: TransientSelectingBox?,
        ) : SelectingBox

        /**
         * An intermediate selecting box that is being driven by an external input and may not be aligned to
         * the cell grid.
         */
        @Serializable
        data class TransientSelectingBox(
            /**
             * The [Rect] describing the transient box. This [Rect] may not be normalized, and have either a negative
             * width or a negative height.
             */
            @Serializable(with = RectSerializer::class) val rect: Rect,
        ) : SelectingBox
    }

    /**
     * A selection that includes a specific [CellState]
     */
    @Serializable
    data class Selection(
        val cellState: CellState,
        @Serializable(with = IntOffsetSerializer::class) val offset: IntOffset,
    ) : SelectionState

    companion object {
        val Saver get() = serializer().saver
    }
}

@Stable
interface SelectionStateHolder {
    val selectionSessionState: SessionValue<SelectionState>
}

fun SelectionStateHolder(
    selectionSessionState: SessionValue<SelectionState>,
) = object : SelectionStateHolder {
    override val selectionSessionState = selectionSessionState
}

@Stable
interface MutableSelectionStateHolder : SelectionStateHolder {
    override var selectionSessionState: SessionValue<SelectionState>
}

fun MutableSelectionStateHolder(
    initialSelectionState: SessionValue<SelectionState>,
): MutableSelectionStateHolder = MutableSelectionStateHolderImpl(initialSelectionState)

@Composable
fun rememberMutableSelectionStateHolder(
    initialSelectionState: SessionValue<SelectionState>,
): MutableSelectionStateHolder =
    rememberSaveable(saver = MutableSelectionStateHolderImpl.Saver) {
        MutableSelectionStateHolder(initialSelectionState)
    }

private class MutableSelectionStateHolderImpl(
    initialSelectionSessionState: SessionValue<SelectionState>,
) : MutableSelectionStateHolder {
    override var selectionSessionState by mutableStateOf(initialSelectionSessionState)

    companion object {
        private val sessionValueSaver = SessionValue.Saver(SelectionState.Saver)

        val Saver: Saver<MutableSelectionStateHolder, Any> = Saver(
            save = {
                with(sessionValueSaver) {
                    save(it.selectionSessionState)
                }
            },
            restore = {
                MutableSelectionStateHolderImpl(
                    sessionValueSaver.restore(it)!!,
                )
            },
        )
    }
}
