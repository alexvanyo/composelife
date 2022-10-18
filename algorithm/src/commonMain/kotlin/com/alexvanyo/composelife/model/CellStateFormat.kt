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

import com.livefront.sealedenum.GenSealedEnum

sealed interface CellStateFormat {

    object Unknown : CellStateFormat
    object Life : CellStateFormat

    /**
     * A "fixed" format for a cell state. Any serialization or deserialization of a cell state should eventually
     * be done with one of these formats, and other [CellStateFormat]s might delegate to here.
     */
    sealed interface FixedFormat : CellStateFormat {
        object Plaintext : FixedFormat
        object Life105 : FixedFormat
        object Life106 : FixedFormat
        object RunLengthEncoding : FixedFormat

        @GenSealedEnum(generateEnum = true)
        companion object
    }

    @GenSealedEnum(generateEnum = true)
    companion object
}

fun CellStateFormat.Companion.fromFileExtension(fileExtension: String?): CellStateFormat =
    when (fileExtension) {
        "cells" -> CellStateFormat.FixedFormat.Plaintext
        "lif", "life" -> CellStateFormat.Life
        "rle" -> CellStateFormat.FixedFormat.RunLengthEncoding
        else -> CellStateFormat.Unknown
    }
