/*
 * Copyright 2025 The Android Open Source Project
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

package com.alexvanyo.composelife.ui.app.info

import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.saveable.Saver
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.setValue
import androidx.savedstate.SavedState
import com.alexvanyo.composelife.serialization.SurrogatingSerializer
import com.alexvanyo.composelife.serialization.saver
import kotlinx.serialization.KSerializer
import kotlinx.serialization.Serializable

@Serializable(with = CellUniverseInfoItemState.Serializer::class)
class CellUniverseInfoItemState(
    isChecked: Boolean = defaultIsChecked,
) {
    var isChecked by mutableStateOf(isChecked)

    private object Serializer : KSerializer<CellUniverseInfoItemState> by SurrogatingSerializer(
        CellUniverseInfoItemState::isChecked,
        ::CellUniverseInfoItemState,
    )

    companion object {
        const val defaultIsChecked: Boolean = true

        val Saver: Saver<CellUniverseInfoItemState, SavedState> = serializer().saver()
    }
}

@Composable
fun rememberCellUniverseInfoItemState(
    isChecked: Boolean = CellUniverseInfoItemState.defaultIsChecked,
): CellUniverseInfoItemState =
    rememberSaveable(saver = CellUniverseInfoItemState.Saver) {
        CellUniverseInfoItemState(isChecked = isChecked)
    }

class CellUniverseInfoItemContent(
    private val cellUniverseInfoCardState: CellUniverseInfoItemState,
    val text: @Composable (isEditing: Boolean) -> String,
) {
    var isChecked by cellUniverseInfoCardState::isChecked
}
