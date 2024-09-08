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

import androidx.compose.foundation.text.input.InputTransformation
import androidx.compose.foundation.text.input.TextFieldState
import androidx.compose.foundation.text.input.insert
import androidx.compose.foundation.text.input.placeCursorAtEnd
import androidx.compose.ui.text.TextRange
import kotlin.test.Test
import kotlin.test.assertEquals

class TrimWhitespaceTests {

    private val textFieldState = TextFieldState()
    private val inputTransformation = InputTransformation.trimWhitespace()

    @Test
    fun keyboard_options() {
        assertEquals(
            null,
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
    fun empty_string_with_adding_non_whitespace() {
        textFieldState.edit {
            append("a")

            with(inputTransformation) {
                transformInput()
            }
        }

        assertEquals("a", textFieldState.text)
    }

    @Test
    fun empty_string_with_adding_non_whitespace_and_whitespace_together() {
        textFieldState.edit {
            append("a b")

            with(inputTransformation) {
                transformInput()
            }
        }

        assertEquals("ab", textFieldState.text)
    }

    @Test
    fun empty_string_with_adding_non_whitespace_and_whitespace_after() {
        textFieldState.edit {
            append("a")
            append(" ")
            append("b")

            with(inputTransformation) {
                transformInput()
            }
        }

        assertEquals("ab", textFieldState.text)
    }

    @Test
    fun empty_string_with_prepending_non_whitespace_and_whitespace_after() {
        textFieldState.edit {
            placeCursorAtEnd()
            insert(0, "a")
            insert(0, " ")
            insert(0, "b")

            with(inputTransformation) {
                transformInput()
            }
        }

        assertEquals("ba", textFieldState.text)
        assertEquals(TextRange(2), textFieldState.selection)
    }
}
