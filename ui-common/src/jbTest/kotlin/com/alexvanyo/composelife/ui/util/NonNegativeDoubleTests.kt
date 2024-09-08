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

package com.alexvanyo.composelife.ui.util

import androidx.compose.foundation.text.KeyboardOptions
import androidx.compose.foundation.text.input.InputTransformation
import androidx.compose.foundation.text.input.TextFieldState
import androidx.compose.foundation.text.input.insert
import androidx.compose.foundation.text.input.placeCursorAtEnd
import androidx.compose.ui.text.TextRange
import androidx.compose.ui.text.input.KeyboardType
import kotlin.test.Test
import kotlin.test.assertEquals

class NonNegativeDoubleTests {

    private val textFieldState = TextFieldState()
    private val inputTransformation = InputTransformation.nonNegativeDouble()

    @Test
    fun keyboard_options() {
        assertEquals(
            KeyboardOptions(
                keyboardType = KeyboardType.Decimal,
            ),
            inputTransformation.keyboardOptions,
        )
    }

    @Test
    fun empty_string_with_no_changes() {
        textFieldState.edit {
            with(inputTransformation) {
                transformInput()
            }
        }

        assertEquals("", textFieldState.text)
    }

    @Test
    fun empty_string_with_adding_space() {
        textFieldState.edit {
            append(" ")

            with(inputTransformation) {
                transformInput()
            }
        }

        assertEquals("", textFieldState.text)
    }

    @Test
    fun empty_string_with_adding_tab() {
        textFieldState.edit {
            append("\t")

            with(inputTransformation) {
                transformInput()
            }
        }

        assertEquals("", textFieldState.text)
    }

    @Test
    fun empty_string_with_adding_letter() {
        textFieldState.edit {
            append("a")

            with(inputTransformation) {
                transformInput()
            }
        }

        assertEquals("", textFieldState.text)
    }

    @Test
    fun empty_string_with_adding_digits() {
        textFieldState.edit {
            append("123")

            with(inputTransformation) {
                transformInput()
            }
        }

        assertEquals("123", textFieldState.text)
    }

    @Test
    fun empty_string_with_adding_digits_and_whitespace_after() {
        textFieldState.edit {
            append("12")
            append(" ")
            append("3")

            with(inputTransformation) {
                transformInput()
            }
        }

        assertEquals("123", textFieldState.text)
    }

    @Test
    fun empty_string_with_prepending_non_whitespace_and_whitespace_after() {
        textFieldState.edit {
            placeCursorAtEnd()
            insert(0, "1")
            insert(0, " ")
            insert(0, "2")

            with(inputTransformation) {
                transformInput()
            }
        }

        assertEquals("21", textFieldState.text)
        assertEquals(TextRange(2), textFieldState.selection)
    }

    @Test
    fun empty_string_with_prepending_number_and_negative() {
        textFieldState.edit {
            placeCursorAtEnd()
            insert(0, "34")
            insert(0, "-")

            with(inputTransformation) {
                transformInput()
            }
        }

        assertEquals("", textFieldState.text)
        assertEquals(TextRange(0), textFieldState.selection)
    }


    @Test
    fun empty_string_with_prepending_number_and_positive() {
        textFieldState.edit {
            placeCursorAtEnd()
            insert(0, "34")
            insert(0, "+")

            with(inputTransformation) {
                transformInput()
            }
        }

        assertEquals("+34", textFieldState.text)
        assertEquals(TextRange(3), textFieldState.selection)
    }

    @Test
    fun number_with_prepending_negative() {
        textFieldState.edit {
            append("34")
        }

        textFieldState.edit {
            placeCursorAtEnd()
            insert(0, "-")

            with(inputTransformation) {
                transformInput()
            }
        }

        assertEquals("34", textFieldState.text)
        assertEquals(TextRange(2), textFieldState.selection)
    }

    @Test
    fun number_with_prepending_positive() {
        textFieldState.edit {
            append("34")
        }

        textFieldState.edit {
            placeCursorAtEnd()
            insert(0, "+")

            with(inputTransformation) {
                transformInput()
            }
        }

        assertEquals("+34", textFieldState.text)
        assertEquals(TextRange(3), textFieldState.selection)
    }

    @Test
    fun empty_string_with_appending_decimal_point() {
        textFieldState.edit {
            append("34")
            append(".")

            with(inputTransformation) {
                transformInput()
            }
        }

        assertEquals("34.", textFieldState.text)
    }

    @Test
    fun empty_string_with_appending_second_decimal_point() {
        textFieldState.edit {
            append("34")
            append(".")
            append(".")

            with(inputTransformation) {
                transformInput()
            }
        }

        assertEquals("", textFieldState.text)
    }

    @Test
    fun number_with_decimal_point_appending_second_decimal_point() {
        textFieldState.edit {
            append("34.")
        }

        textFieldState.edit {
            append(".")

            with(inputTransformation) {
                transformInput()
            }
        }

        assertEquals("34.", textFieldState.text)
    }
}
