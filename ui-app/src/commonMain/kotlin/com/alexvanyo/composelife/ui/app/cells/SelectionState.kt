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
import com.alexvanyo.composelife.sessionvaluekey.SessionValue
import com.alexvanyo.composelife.ui.util.IntOffsetSerializer
import com.alexvanyo.composelife.ui.util.RectSerializer
import com.alexvanyo.composelife.ui.util.saver
import kotlinx.serialization.Serializable

@Serializable
sealed interface SelectionState {

    @Serializable
    data object NoSelection : SelectionState

    @Serializable
    sealed interface SelectingBox : SelectionState {

        @Serializable
        data class FixedSelectingBox(
            @Serializable(with = IntOffsetSerializer::class) val topLeft: IntOffset,
            val width: Int,
            val height: Int,
            val previousTransientSelectingBox: TransientSelectingBox?,
        ) : SelectingBox

        @Serializable
        data class TransientSelectingBox(
            @Serializable(with = RectSerializer::class) val rect: Rect,
        ) : SelectingBox
    }

    @Serializable
    data class Selection(
        val cellState: CellState,
        @Serializable(with = IntOffsetSerializer::class) val offset: IntOffset,
    ) : SelectionState

    companion object {
        val Saver: Saver<SelectionState, String> = serializer().saver
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
