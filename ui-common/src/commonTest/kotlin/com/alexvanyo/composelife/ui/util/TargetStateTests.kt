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

import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith

class TargetStateTests {

    @Test
    fun creating_in_progress_with_same_state_throws_exception() {
        assertFailsWith<IllegalArgumentException> {
            TargetState.InProgress(
                current = 0,
                provisional = 0,
                progress = 0.5f,
            )
        }
    }

    @Test
    fun progress_to_true_is_0_when_false() {
        assertEquals(
            0f,
            TargetState.Single(false).progressToTrue,
        )
    }

    @Test
    fun progress_to_true_is_1_when_true() {
        assertEquals(
            1f,
            TargetState.Single(true).progressToTrue,
        )
    }

    @Test
    fun progress_to_true_is_correct_when_to_is_true() {
        assertEquals(
            0.25f,
            TargetState.InProgress(current = false, provisional = true, progress = 0.25f).progressToTrue,
        )
    }

    @Test
    fun progress_to_true_is_correct_when_to_is_false() {
        assertEquals(
            0.25f,
            TargetState.InProgress(current = true, provisional = false, progress = 0.75f).progressToTrue,
        )
    }

    @Test
    fun single_false_not_is_correct() {
        assertEquals(
            TargetState.Single(true),
            TargetState.Single(false).not(),
        )
    }

    @Test
    fun single_true_not_is_correct() {
        assertEquals(
            TargetState.Single(false),
            TargetState.Single(true).not(),
        )
    }

    @Test
    fun in_progress_not_is_correct() {
        assertEquals(
            TargetState.InProgress(current = true, provisional = false, progress = 0.25f),
            TargetState.InProgress(current = false, provisional = true, progress = 0.25f).not(),
        )
    }

    @Test
    fun single_false_and_false_is_correct() {
        assertEquals(
            TargetState.Single(false),
            TargetState.Single(false) and false,
        )
    }

    @Test
    fun single_false_and_true_is_correct() {
        assertEquals(
            TargetState.Single(false),
            TargetState.Single(false) and true,
        )
    }

    @Test
    fun single_true_and_false_is_correct() {
        assertEquals(
            TargetState.Single(false),
            TargetState.Single(true) and false,
        )
    }

    @Test
    fun single_true_and_true_is_correct() {
        assertEquals(
            TargetState.Single(true),
            TargetState.Single(true) and true,
        )
    }

    @Test
    fun in_progress_and_false_is_correct() {
        assertEquals(
            TargetState.Single(false),
            TargetState.InProgress(current = false, provisional = true, progress = 0.25f) and false,
        )
    }

    @Test
    fun in_progress_and_true_is_correct() {
        assertEquals(
            TargetState.InProgress(current = false, provisional = true, progress = 0.25f),
            TargetState.InProgress(current = false, provisional = true, progress = 0.25f) and true,
        )
    }

    @Test
    fun single_false_or_false_is_correct() {
        assertEquals(
            TargetState.Single(false),
            TargetState.Single(false) or false,
        )
    }

    @Test
    fun single_false_or_true_is_correct() {
        assertEquals(
            TargetState.Single(true),
            TargetState.Single(false) or true,
        )
    }

    @Test
    fun single_true_or_false_is_correct() {
        assertEquals(
            TargetState.Single(true),
            TargetState.Single(true) or false,
        )
    }

    @Test
    fun single_true_or_true_is_correct() {
        assertEquals(
            TargetState.Single(true),
            TargetState.Single(true) or true,
        )
    }

    @Test
    fun in_progress_or_false_is_correct() {
        assertEquals(
            TargetState.InProgress(current = false, provisional = true, progress = 0.25f),
            TargetState.InProgress(current = false, provisional = true, progress = 0.25f) or false,
        )
    }

    @Test
    fun in_progress_or_true_is_correct() {
        assertEquals(
            TargetState.Single(true),
            TargetState.InProgress(current = false, provisional = true, progress = 0.25f) or true,
        )
    }
}
