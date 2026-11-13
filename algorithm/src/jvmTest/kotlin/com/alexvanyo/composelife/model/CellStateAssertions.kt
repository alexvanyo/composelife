/*
 * Copyright 2026 The Android Open Source Project
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

import kotlin.test.assertEquals
import kotlin.test.fail

/**
 * Asserts that [actual] equals [expected] (or equals it up to an offset, if [equalsModuleOffset]). The failure message
 * shows both as RLE, which is only formatted on failure.
 */
fun assertCellStateEquals(expected: CellState, actual: CellState, equalsModuleOffset: Boolean = false) {
    val matches = if (equalsModuleOffset) expected.equalsModuloOffset(actual) else expected == actual
    if (matches) return
    val qualifier = if (equalsModuleOffset) "modulo offset " else ""
    val message = "Expected $qualifier${expected.toRle()} but was ${actual.toRle()}"
    if (equalsModuleOffset) {
        fail(message)
    } else {
        assertEquals(expected = expected, actual = actual, message = message)
    }
}

private fun CellState.toRle(): String = RunLengthEncodedCellStateSerializer.serializeToString(this).joinToString("\n")
