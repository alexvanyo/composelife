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

package com.alexvanyo.composelife.navigation

import java.util.UUID
import kotlin.test.Test
import kotlin.test.assertEquals

class BackstackEntryTests {

    private val id1 = UUID.randomUUID()
    private val id2 = UUID.randomUUID()
    private val id3 = UUID.randomUUID()
    private val id4 = UUID.randomUUID()
    private val entry1 = BackstackEntry("a", null, id1)
    private val entry2 = BackstackEntry("b", entry1, id2)
    private val entry3 = BackstackEntry("c", entry2, id3)
    private val entry4 = BackstackEntry("d", entry3, id4)

    @Test
    fun entry_1_iterable_is_correct() {
        assertEquals(
            listOf(entry1),
            entry1.iterator().asSequence().toList(),
        )
    }

    @Test
    fun entry_2_iterable_is_correct() {
        assertEquals(
            listOf(entry2, entry1),
            entry2.iterator().asSequence().toList(),
        )
    }

    @Test
    fun entry_3_iterable_is_correct() {
        assertEquals(
            listOf(entry3, entry2, entry1),
            entry3.iterator().asSequence().toList(),
        )
    }

    @Test
    fun entry_4_iterable_is_correct() {
        assertEquals(
            listOf(entry4, entry3, entry2, entry1),
            entry4.iterator().asSequence().toList(),
        )
    }
}
