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

import android.content.ClipData
import android.content.Context
import androidx.compose.ui.draganddrop.DragAndDropEvent
import androidx.compose.ui.draganddrop.toAndroidDragEvent
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.model.CellStateFormat
import com.alexvanyo.composelife.model.DeserializationResult
import com.alexvanyo.composelife.model.FlexibleCellStateSerializer
import com.alexvanyo.composelife.scopes.ApplicationContext
import com.alexvanyo.composelife.ui.app.resources.EmptyClipboard
import com.alexvanyo.composelife.ui.app.resources.Strings
import com.alexvanyo.composelife.ui.util.ClipboardReader
import kotlinx.coroutines.async
import kotlinx.coroutines.awaitAll
import kotlinx.coroutines.coroutineScope
import kotlinx.coroutines.withContext
import me.tatarka.inject.annotations.Inject

@Inject
actual class ClipboardCellStateParser(
    private val flexibleCellStateSerializer: FlexibleCellStateSerializer,
    private val dispatchers: ComposeLifeDispatchers,
    private val context: @ApplicationContext Context,
) {
    actual suspend fun parseCellState(clipboardStateReader: ClipboardReader): DeserializationResult =
        parseCellState(clipboardStateReader.getClipData())

    actual suspend fun parseCellState(dragAndDropEvent: DragAndDropEvent): DeserializationResult =
        parseCellState(dragAndDropEvent.toAndroidDragEvent().clipData)

    suspend fun parseCellState(clipData: ClipData?): DeserializationResult {
        val items = clipData?.items.orEmpty()
        if (items.isEmpty()) {
            return DeserializationResult.Unsuccessful(
                warnings = emptyList(),
                errors = listOf(Strings.EmptyClipboard),
            )
        }

        return coroutineScope {
            items
                .map { clipDataItem ->
                    async {
                        flexibleCellStateSerializer.deserializeToCellState(
                            format = CellStateFormat.Unknown,
                            lines = clipDataItem.resolveToText().lineSequence(),
                        )
                    }
                }
                .awaitAll()
                .reduce { a, b ->
                    when (a) {
                        is DeserializationResult.Unsuccessful -> b
                        is DeserializationResult.Successful -> {
                            when (b) {
                                is DeserializationResult.Successful -> if (a.warnings.isEmpty()) {
                                    a
                                } else {
                                    b
                                }

                                is DeserializationResult.Unsuccessful -> a
                            }
                        }
                    }
                }
        }
    }

    @Suppress("InjectDispatcher")
    private suspend fun ClipData.Item.resolveToText(): CharSequence =
        withContext(dispatchers.IO) {
            coerceToText(context)
        }
}

private val ClipData.items: List<ClipData.Item> get() = List(itemCount, ::getItemAt)
