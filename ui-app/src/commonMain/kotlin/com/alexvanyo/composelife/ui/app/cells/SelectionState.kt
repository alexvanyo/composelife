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
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.util.packInts
import androidx.compose.ui.util.unpackInt1
import androidx.compose.ui.util.unpackInt2
import com.alexvanyo.composelife.model.CellState
import kotlinx.serialization.KSerializer
import kotlinx.serialization.Serializable
import kotlinx.serialization.descriptors.PrimitiveKind
import kotlinx.serialization.descriptors.PrimitiveSerialDescriptor
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.encoding.Decoder
import kotlinx.serialization.encoding.Encoder
import kotlinx.serialization.json.Json

@Serializable
sealed interface SelectionState {

    @Serializable
    data object NoSelection : SelectionState

    @Serializable
    data class SelectingBox(
        @Serializable(with = IntOffsetSerializer::class) val topLeft: IntOffset,
        val width: Int,
        val height: Int,
    ) : SelectionState

    @Serializable
    data class Selection(
        val cellState: CellState,
    ) : SelectionState

    companion object {
        val Saver: Saver<SelectionState, String> = JsonSaver(serializer())
    }
}

class JsonSaver<T>(serializer: KSerializer<T>) : Saver<T, String> by Saver(
    { Json.encodeToString(serializer, it) },
    { Json.decodeFromString(serializer, it) },
)

object IntOffsetSerializer : KSerializer<IntOffset> {
    override val descriptor: SerialDescriptor = PrimitiveSerialDescriptor(
        "androidx.compose.ui.unit.IntOffset",
        PrimitiveKind.LONG,
    )

    override fun deserialize(decoder: Decoder): IntOffset {
        val longValue = decoder.decodeLong()
        return IntOffset(unpackInt1(longValue), unpackInt2(longValue))
    }

    override fun serialize(encoder: Encoder, value: IntOffset) {
        encoder.encodeLong(packInts(value.x, value.y))
    }
}

@Stable
interface SelectionStateHolder {
    val selectionState: SelectionState
}

fun SelectionStateHolder(
    selectionState: SelectionState,
) = object : SelectionStateHolder {
    override val selectionState: SelectionState = selectionState
}

@Stable
interface MutableSelectionStateHolder {
    var selectionState: SelectionState
}

fun MutableSelectionStateHolder(
    initialSelectionState: SelectionState,
): MutableSelectionStateHolder = MutableSelectionStateHolderImpl(initialSelectionState)

@Composable
fun rememberMutableSelectionStateHolder(
    initialSelectionState: SelectionState,
): MutableSelectionStateHolder =
    rememberSaveable(saver = MutableSelectionStateHolderImpl.Saver) {
        MutableSelectionStateHolder(initialSelectionState)
    }

private class MutableSelectionStateHolderImpl(
    initialSelectionState: SelectionState,
) : MutableSelectionStateHolder {
    override var selectionState: SelectionState by mutableStateOf(initialSelectionState)

    companion object {
        val Saver: Saver<MutableSelectionStateHolder, String> = Saver(
            save = {
                with(SelectionState.Saver) {
                    save(it.selectionState)
                }
            },
            restore = {
                MutableSelectionStateHolderImpl(
                    SelectionState.Saver.restore(it)!!,
                )
            },
        )
    }
}
