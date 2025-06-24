/*
 * Copyright 2022 The Android Open Source Project
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

import kotlinx.serialization.ExperimentalSerializationApi
import kotlinx.serialization.KSerializer
import kotlinx.serialization.SerializationException
import kotlinx.serialization.builtins.ListSerializer
import kotlinx.serialization.builtins.serializer
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.encoding.Decoder
import kotlinx.serialization.encoding.Encoder

object JsonCellStateSerialization : KSerializer<CellState> by
FixedFormatKSerializer(RunLengthEncodedCellStateSerializer)

class FixedFormatKSerializer(
    private val fixedFormatCellStateSerializer: FixedFormatCellStateSerializer,
) : KSerializer<CellState> {
    private val delegateSerializer = ListSerializer(String.serializer())

    @OptIn(ExperimentalSerializationApi::class)
    override val descriptor: SerialDescriptor = SerialDescriptor(
        "com.alexvanyo.composelife.model.CellState.${fixedFormatCellStateSerializer.format._name}",
        delegateSerializer.descriptor,
    )

    override fun deserialize(decoder: Decoder): CellState {
        val lines = delegateSerializer.deserialize(decoder)
        val deserializationResult = fixedFormatCellStateSerializer.deserializeToCellState(
            lines.asSequence(),
        )
        return when (deserializationResult) {
            is DeserializationResult.Successful -> {
                if (deserializationResult.warnings.isNotEmpty()) {
                    throw SerializationException(
                        "Warnings when parsing cell state!\n" + deserializationResult.warnings.joinToString("\n"),
                    )
                }
                deserializationResult.cellState
            }

            is DeserializationResult.Unsuccessful -> {
                throw SerializationException(
                    "Warnings when parsing cell state!\n" + deserializationResult.warnings.joinToString("\n"),
                )
            }
        }
    }

    override fun serialize(encoder: Encoder, value: CellState) {
        val lines = fixedFormatCellStateSerializer.serializeToString(value).toList()
        delegateSerializer.serialize(encoder, lines)
    }
}
