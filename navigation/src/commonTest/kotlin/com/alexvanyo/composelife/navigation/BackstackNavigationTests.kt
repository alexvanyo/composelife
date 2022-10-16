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

import androidx.compose.runtime.mutableStateMapOf
import java.util.UUID
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith
import kotlin.test.assertNotNull

class BackstackNavigationTests {

    private val id1 = UUID.randomUUID()
    private val id2 = UUID.randomUUID()
    private val id3 = UUID.randomUUID()
    private val id4 = UUID.randomUUID()
    private val entry1 = BackstackEntry("a", null, id1)
    private val entry2 = BackstackEntry("b", entry1, id2)
    private val entry3 = BackstackEntry("c", entry2, id3)
    private val entry4 = BackstackEntry("d", entry3, id4)

    private val mutableBackstackMap: MutableBackstackMap<String> = mutableStateMapOf(
        id1 to entry1,
        id2 to entry2,
        id3 to entry3,
        id4 to entry4,
    )

    @Test
    fun pop_backstack_is_correct() {
        val newId = mutableBackstackMap.popBackstack(id4)

        assertEquals(
            mapOf(
                id1 to entry1,
                id2 to entry2,
                id3 to entry3,
            ),
            mutableBackstackMap.toMap(),
        )
        assertEquals(id3, newId)
    }

    @Test
    fun pop_backstack_with_one_entry_throws_exception() {
        mutableBackstackMap.popBackstack(id4)
        mutableBackstackMap.popBackstack(id3)
        mutableBackstackMap.popBackstack(id2)

        assertFailsWith<IllegalStateException> {
            mutableBackstackMap.popBackstack(id1)
        }
    }

    @Test
    fun pop_up_to_with_id_non_inclusive_is_correct() {
        val newId = mutableBackstackMap.popUpTo(
            currentEntryId = id4,
            id = id2,
        )

        assertEquals(
            mapOf(
                id1 to entry1,
                id2 to entry2,
            ),
            mutableBackstackMap.toMap(),
        )
        assertEquals(id2, newId)
    }

    @Test
    fun pop_up_to_with_id_inclusive_is_correct() {
        val newId = mutableBackstackMap.popUpTo(
            currentEntryId = id4,
            id = id2,
            inclusive = true,
        )

        assertEquals(
            mapOf(
                id1 to entry1,
            ),
            mutableBackstackMap.toMap(),
        )
        assertEquals(id1, newId)
    }

    @Test
    fun pop_up_to_with_no_matching_id_throws_exception() {
        assertFailsWith<IllegalStateException> {
            mutableBackstackMap.popUpTo(
                currentEntryId = id4,
                id = UUID.randomUUID(),
            )
        }
    }

    @Test
    fun pop_up_to_inclusive_on_last_entry_throws_exception() {
        assertFailsWith<IllegalStateException> {
            mutableBackstackMap.popUpTo(
                currentEntryId = id4,
                id = id1,
                inclusive = true,
            )
        }
    }

    @Test
    fun pop_up_to_with_value_predicate_non_inclusive_is_correct() {
        val newId = mutableBackstackMap.popUpTo(
            currentEntryId = id4,
            predicate = { it == "b" },
        )

        assertEquals(
            mapOf(
                id1 to entry1,
                id2 to entry2,
            ),
            mutableBackstackMap.toMap(),
        )
        assertEquals(id2, newId)
    }

    @Test
    fun pop_up_to_with_value_inclusive_is_correct() {
        val newId = mutableBackstackMap.popUpTo(
            currentEntryId = id4,
            predicate = { it == "b" },
            inclusive = true,
        )

        assertEquals(
            mapOf(
                id1 to entry1,
            ),
            mutableBackstackMap.toMap(),
        )
        assertEquals(id1, newId)
    }

    @Test
    fun pop_up_to_with_entry_predicate_non_inclusive_is_correct() {
        val newId = mutableBackstackMap.popUpTo(
            currentEntryId = id4,
            entryPredicate = { it.value == "b" },
        )

        assertEquals(
            mapOf(
                id1 to entry1,
                id2 to entry2,
            ),
            mutableBackstackMap.toMap(),
        )
        assertEquals(id2, newId)
    }

    @Test
    fun pop_up_to_with_entry_predicate_inclusive_is_correct() {
        val newId = mutableBackstackMap.popUpTo(
            currentEntryId = id4,
            entryPredicate = { it.value == "b" },
            inclusive = true,
        )

        assertEquals(
            mapOf(
                id1 to entry1,
            ),
            mutableBackstackMap.toMap(),
        )
        assertEquals(id1, newId)
    }

    @Test
    fun navigate_with_raw_value_is_correct() {
        val id5 = UUID.randomUUID()
        val newId = mutableBackstackMap.navigate(
            currentEntryId = id4,
            value = "e",
            id = id5,
        )

        val entry5 = mutableBackstackMap[newId]

        assertNotNull(entry5)
        assertEquals("e", entry5.value)
        assertEquals(id5, entry5.id)
        assertEquals(entry4, entry5.previous)
        assertEquals(
            mapOf(
                id1 to entry1,
                id2 to entry2,
                id3 to entry3,
                id4 to entry4,
                id5 to entry5,
            ),
            mutableBackstackMap.toMap(),
        )
        assertEquals(id5, newId)
    }

    @Test
    fun navigate_with_value_factory_is_correct() {
        val id5 = UUID.randomUUID()
        val newId = mutableBackstackMap.navigate(
            currentEntryId = id4,
            valueFactory = { it.value + "2" },
            id = id5,
        )

        val entry5 = mutableBackstackMap[newId]

        assertNotNull(entry5)
        assertEquals("d2", entry5.value)
        assertEquals(id5, entry5.id)
        assertEquals(entry4, entry5.previous)
        assertEquals(
            mapOf(
                id1 to entry1,
                id2 to entry2,
                id3 to entry3,
                id4 to entry4,
                id5 to entry5,
            ),
            mutableBackstackMap.toMap(),
        )
        assertEquals(id5, newId)
    }
}
