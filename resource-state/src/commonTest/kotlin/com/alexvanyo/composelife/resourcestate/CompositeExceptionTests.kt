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

package com.alexvanyo.composelife.resourcestate

import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith

class CompositeExceptionTests {

    @Test
    fun empty_constructor_throws_exception() {
        assertFailsWith<IllegalArgumentException> {
            CompositeException()
        }
    }

    @Test
    fun single_exception_constructor_throws_exception() {
        assertFailsWith<IllegalArgumentException> {
            CompositeException(Exception())
        }
    }

    @Test
    fun vararg_constructor_creates_expected_exception() {
        val exception1 = Exception()
        val exception2 = Exception()

        val compositeException = CompositeException(exception1, exception2)

        assertEquals("2 exceptions occurred.", compositeException.message)
        assertEquals(exception1, compositeException.cause)
        assertEquals(listOf(exception1, exception2), compositeException.exceptions)
    }
}
