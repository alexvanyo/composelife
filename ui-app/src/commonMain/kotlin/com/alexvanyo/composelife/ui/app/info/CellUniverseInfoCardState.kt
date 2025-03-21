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
import com.alexvanyo.composelife.ui.util.TargetState
import com.alexvanyo.composelife.ui.util.or

/**
 * The persistable state describing the [CellUniverseInfoCard].
 */
interface CellUniverseInfoCardState {

    /**
     * Sets if the card is expanded.
     */
    fun setIsExpanded(isExpanded: Boolean)

    /**
     * The target state for whether the card is expanded.
     */
    val expandedTargetState: TargetState<Boolean, *>
}

/**
 * Remembers the a default implementation of [CellUniverseInfoCardState].
 */
@Composable
fun rememberCellUniverseInfoCardState(
    setIsExpanded: (Boolean) -> Unit,
    expandedTargetState: TargetState<Boolean, *>,
): CellUniverseInfoCardState =
    object : CellUniverseInfoCardState {
        override fun setIsExpanded(isExpanded: Boolean) {
            setIsExpanded(isExpanded)
        }

        override val expandedTargetState: TargetState<Boolean, *>
            get() = expandedTargetState
    }

class CellUniverseInfoCardContent(
    private val cellUniverseInfoCardState: CellUniverseInfoCardState,
    val cellUniverseInfoItemContents: List<CellUniverseInfoItemContent>,
) {
    fun setIsExpanded(isExpanded: Boolean) {
        cellUniverseInfoCardState.setIsExpanded(isExpanded)
    }

    val expandedTargetState: TargetState<Boolean, *> get() =
        cellUniverseInfoCardState.expandedTargetState

    val editingTargetState: TargetState<Boolean, *> get() =
        expandedTargetState or cellUniverseInfoItemContents.none { it.isChecked }

    val showColumnTargetState: TargetState<Boolean, *> get() =
        expandedTargetState or cellUniverseInfoItemContents.any { it.isChecked }
}
