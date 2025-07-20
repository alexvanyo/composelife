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

package com.alexvanyo.composelife.model

import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import kotlinx.coroutines.CompletableDeferred
import kotlinx.coroutines.async
import kotlinx.coroutines.awaitAll
import kotlinx.coroutines.coroutineScope
import kotlinx.coroutines.withContext
import dev.zacsweers.metro.Inject

@Inject
class FlexibleCellStateSerializer(
    private val dispatchers: ComposeLifeDispatchers,
) : CellStateSerializer {
    override suspend fun deserializeToCellState(
        format: CellStateFormat,
        lines: Sequence<String>,
    ): DeserializationResult =
        withContext(dispatchers.Default) {
            val targetedSerializer = when (format) {
                CellStateFormat.FixedFormat.Plaintext -> PlaintextCellStateSerializer
                CellStateFormat.FixedFormat.Life105 -> Life105CellStateSerializer
                CellStateFormat.FixedFormat.RunLengthEncoding -> RunLengthEncodedCellStateSerializer
                CellStateFormat.FixedFormat.Life106 -> Life106CellStateSerializer
                CellStateFormat.FixedFormat.Macrocell -> MacrocellCellStateSerializer
                CellStateFormat.Life,
                CellStateFormat.Unknown,
                -> null
            }

            val targetedResult = targetedSerializer?.deserializeToCellState(lines)
            when (targetedResult) {
                is DeserializationResult.Successful -> return@withContext targetedResult
                is DeserializationResult.Unsuccessful,
                null,
                -> Unit
            }

            val allSerializers = listOf(
                PlaintextCellStateSerializer,
                Life105CellStateSerializer,
                Life106CellStateSerializer,
                RunLengthEncodedCellStateSerializer,
            )

            coroutineScope {
                allSerializers
                    .map {
                        if (it == targetedSerializer) {
                            CompletableDeferred(checkNotNull(targetedResult))
                        } else {
                            async {
                                it.deserializeToCellState(lines)
                            }
                        }
                    }
                    .awaitAll()
                    .reduceToSuccessful()
            }
        }

    override suspend fun serializeToString(
        format: CellStateFormat.FixedFormat,
        cellState: CellState,
    ): Sequence<String> =
        when (format) {
            CellStateFormat.FixedFormat.Plaintext -> PlaintextCellStateSerializer
            CellStateFormat.FixedFormat.Life105 -> Life105CellStateSerializer
            CellStateFormat.FixedFormat.RunLengthEncoding -> RunLengthEncodedCellStateSerializer
            CellStateFormat.FixedFormat.Life106 -> Life106CellStateSerializer
            CellStateFormat.FixedFormat.Macrocell -> MacrocellCellStateSerializer
        }.serializeToString(cellState)
}
