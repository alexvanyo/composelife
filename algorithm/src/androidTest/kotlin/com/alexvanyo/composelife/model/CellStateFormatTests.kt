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

import org.junit.jupiter.api.Test
import kotlin.test.assertEquals

class CellStateFormatTests {

    @Test
    fun `from file extension null is unknown`() {
        assertEquals(
            CellStateFormat.Unknown,
            CellStateFormat.fromFileExtension(null),
        )
    }

    @Test
    fun `from file extension cells is plaintext`() {
        assertEquals(
            CellStateFormat.FixedFormat.Plaintext,
            CellStateFormat.fromFileExtension("cells"),
        )
    }

    @Test
    fun `from file extension rle is run length encoding`() {
        assertEquals(
            CellStateFormat.FixedFormat.RunLengthEncoding,
            CellStateFormat.fromFileExtension("rle"),
        )
    }

    @Test
    fun `from file extension lif is life`() {
        assertEquals(
            CellStateFormat.Life,
            CellStateFormat.fromFileExtension("lif"),
        )
    }

    @Test
    fun `from file extension life is life`() {
        assertEquals(
            CellStateFormat.Life,
            CellStateFormat.fromFileExtension("life"),
        )
    }

    @Test
    fun `from file extension txt is unknown`() {
        assertEquals(
            CellStateFormat.Unknown,
            CellStateFormat.fromFileExtension("txt"),
        )
    }

    @Test
    fun `from file extension empty is unknown`() {
        assertEquals(
            CellStateFormat.Unknown,
            CellStateFormat.fromFileExtension(""),
        )
    }
}
