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

/**
 * A general [CellStateSerializer] that can asynchronously serialize and deserialize with a given format.
 */
interface CellStateSerializer {

    /**
     * Attempts to deserialize the sequence of lines into a [DeserializationResult] for the given [CellStateFormat].
     *
     * If format is not a [CellStateFormat.FixedFormat], or if deserialization with the given
     * [CellStateFormat.FixedFormat] fails, then an attempt will be made to deserialize lines with
     * multiple formats.
     */
    suspend fun deserializeToCellState(
        format: CellStateFormat,
        lines: Sequence<String>,
    ): DeserializationResult

    /**
     * Serializes the [CellState] into a sequence of lines with the given [CellStateFormat.FixedFormat].
     *
     * Note that format
     */
    suspend fun serializeToString(
        format: CellStateFormat.FixedFormat,
        cellState: CellState,
    ): Sequence<String>
}
