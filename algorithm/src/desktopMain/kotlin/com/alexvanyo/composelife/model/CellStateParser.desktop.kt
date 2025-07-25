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

@file:Suppress("MatchingDeclarationName")

package com.alexvanyo.composelife.model

import androidx.compose.ui.ExperimentalComposeUiApi
import androidx.compose.ui.draganddrop.DragData
import dev.zacsweers.metro.Inject

@Inject
actual class CellStateParser(
    internal actual val flexibleCellStateSerializer: FlexibleCellStateSerializer,
) {
    @OptIn(ExperimentalComposeUiApi::class)
    suspend fun parseCellState(dragData: DragData): DeserializationResult =
        when (dragData) {
            is DragData.Text -> parseCellState(dragData.readText())
            else -> DeserializationResult.Unsuccessful(
                warnings = emptyList(),
                errors = emptyList(),
            )
        }
}
