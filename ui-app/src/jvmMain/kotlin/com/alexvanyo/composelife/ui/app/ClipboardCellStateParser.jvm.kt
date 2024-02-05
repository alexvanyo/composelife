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

package com.alexvanyo.composelife.ui.app

import com.alexvanyo.composelife.model.CellStateFormat
import com.alexvanyo.composelife.model.DeserializationResult
import com.alexvanyo.composelife.model.FlexibleCellStateSerializer
import com.alexvanyo.composelife.ui.util.ClipboardReader
import me.tatarka.inject.annotations.Inject

@Inject
actual class ClipboardCellStateParser actual constructor(
    private val flexibleCellStateSerializer: FlexibleCellStateSerializer,
) {
    actual suspend fun parseCellState(clipboardStateReader: ClipboardReader): DeserializationResult =
        flexibleCellStateSerializer.deserializeToCellState(
            format = CellStateFormat.Unknown,
            lines = clipboardStateReader.getText()?.text.orEmpty().lineSequence(),
        )
}
