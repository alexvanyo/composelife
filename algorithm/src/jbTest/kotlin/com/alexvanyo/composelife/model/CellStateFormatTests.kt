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

import kotlin.test.Test
import kotlin.test.assertEquals

@Suppress("TooManyFunctions")
class CellStateFormatTests {

    @Test
    fun from_file_extension_null_is_unknown() {
        assertEquals(
            CellStateFormat.Unknown,
            CellStateFormat.fromFileExtension(null),
        )
    }

    @Test
    fun from_file_extension_cells_is_plaintext() {
        assertEquals(
            CellStateFormat.FixedFormat.Plaintext,
            CellStateFormat.fromFileExtension("cells"),
        )
    }

    @Test
    fun from_file_extension_rle_is_run_length_encoding() {
        assertEquals(
            CellStateFormat.FixedFormat.RunLengthEncoding,
            CellStateFormat.fromFileExtension("rle"),
        )
    }

    @Test
    fun from_file_extension_lif_is_life() {
        assertEquals(
            CellStateFormat.Life,
            CellStateFormat.fromFileExtension("lif"),
        )
    }

    @Test
    fun from_file_extension_life_is_life() {
        assertEquals(
            CellStateFormat.Life,
            CellStateFormat.fromFileExtension("life"),
        )
    }

    @Test
    fun from_file_extension_txt_is_unknown() {
        assertEquals(
            CellStateFormat.Unknown,
            CellStateFormat.fromFileExtension("txt"),
        )
    }

    @Test
    fun from_file_extension_empty_is_unknown() {
        assertEquals(
            CellStateFormat.Unknown,
            CellStateFormat.fromFileExtension(""),
        )
    }

    @Test
    fun from_file_extension_mc_is_macrocell() {
        assertEquals(
            CellStateFormat.FixedFormat.Macrocell,
            CellStateFormat.fromFileExtension("mc"),
        )
    }

    @Test
    fun sealed_enum_values_are_correct() {
        assertEquals(
            listOf(
                CellStateFormat.Unknown,
                CellStateFormat.Life,
                CellStateFormat.FixedFormat.Plaintext,
                CellStateFormat.FixedFormat.Life105,
                CellStateFormat.FixedFormat.Life106,
                CellStateFormat.FixedFormat.RunLengthEncoding,
                CellStateFormat.FixedFormat.Macrocell,
            ),
            CellStateFormat.sealedEnum.values,
        )
    }

    @Test
    fun fixed_format_sealed_enum_values_are_correct() {
        assertEquals(
            listOf(
                CellStateFormat.FixedFormat.Plaintext,
                CellStateFormat.FixedFormat.Life105,
                CellStateFormat.FixedFormat.Life106,
                CellStateFormat.FixedFormat.RunLengthEncoding,
                CellStateFormat.FixedFormat.Macrocell,
            ),
            CellStateFormat.FixedFormat.sealedEnum.values,
        )
    }

    @Test
    fun fixed_format_name_is_correct() {
        assertEquals("CellStateFormat_FixedFormat_Plaintext", CellStateFormat.FixedFormat.Plaintext._name)
        assertEquals("CellStateFormat_FixedFormat_Life105", CellStateFormat.FixedFormat.Life105._name)
        assertEquals("CellStateFormat_FixedFormat_Life106", CellStateFormat.FixedFormat.Life106._name)
        val rleName = CellStateFormat.FixedFormat.RunLengthEncoding._name
        assertEquals("CellStateFormat_FixedFormat_RunLengthEncoding", rleName)
        assertEquals("CellStateFormat_FixedFormat_Macrocell", CellStateFormat.FixedFormat.Macrocell._name)
    }
}
