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

import androidx.compose.runtime.remember
import androidx.compose.ui.test.ExperimentalTestApi
import com.alexvanyo.composelife.kmpandroidrunner.BaseKmpTest
import com.alexvanyo.composelife.kmpstaterestorationtester.KmpStateRestorationTester
import com.alexvanyo.composelife.test.runComposeUiTest
import kotlinx.serialization.Serializable
import kotlinx.serialization.builtins.serializer
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotNull
import kotlin.uuid.Uuid

@OptIn(ExperimentalTestApi::class)
class BackstackStateTests : BaseKmpTest() {

    private val id1 = Uuid.random()
    private val id2 = Uuid.random()
    private val id3 = Uuid.random()
    private val id4 = Uuid.random()

    @Test
    fun backstack_state_with_basic_value_is_saved_correctly() = runComposeUiTest {
        val stateRestorationTester = KmpStateRestorationTester(this)

        @Suppress("DoubleMutabilityForCollection")
        var backstackMap: MutableBackstackMap<String>? = null

        stateRestorationTester.setContent {
            val initialBackstackEntries = remember {
                val entry1 = BackstackEntry(
                    value = "a",
                    previous = null,
                    id = id1,
                )
                val entry2 = BackstackEntry(
                    value = "b",
                    previous = entry1,
                    id = id2,
                )
                val entry3 = BackstackEntry(
                    value = "c",
                    previous = entry2,
                    id = id3,
                )
                val entry4 = BackstackEntry(
                    value = "d",
                    previous = entry3,
                    id = id4,
                )

                listOf(entry1, entry2, entry3, entry4)
            }

            backstackMap = rememberBackstackMap(
                initialBackstackEntries = initialBackstackEntries,
            )
        }

        assertNotNull(backstackMap)
        backstackMap = null

        stateRestorationTester.emulateStateRestore()

        val restoredBackstackMap = assertNotNull(backstackMap)
        assertEquals(4, restoredBackstackMap.size)
        assertEquals("a", restoredBackstackMap[id1]?.value)
        assertEquals("b", restoredBackstackMap[id2]?.value)
        assertEquals("c", restoredBackstackMap[id3]?.value)
        assertEquals("d", restoredBackstackMap[id4]?.value)
    }

    @Suppress("LongMethod")
    @Test
    fun backstack_state_with_saver_factory_is_saved_correctly() = runComposeUiTest {
        val stateRestorationTester = KmpStateRestorationTester(this)

        @Suppress("DoubleMutabilityForCollection")
        var backstackMap: MutableBackstackMap<TestEntryType>? = null

        stateRestorationTester.setContent {
            val initialBackstackEntries = remember {
                val entry1 = BackstackEntry(
                    value = TestEntryType(
                        value = "a",
                        previous = null,
                    ),
                    previous = null,
                    id = id1,
                )
                val entry2 = BackstackEntry(
                    value = TestEntryType(
                        value = "b",
                        previous = entry1.value,
                    ),
                    previous = entry1,
                    id = id2,
                )
                val entry3 = BackstackEntry(
                    value = TestEntryType(
                        value = "c",
                        previous = entry2.value,
                    ),
                    previous = entry2,
                    id = id3,
                )
                val entry4 = BackstackEntry(
                    value = TestEntryType(
                        value = "d",
                        previous = entry3.value,
                    ),
                    previous = entry3,
                    id = id4,
                )

                listOf(entry1, entry2, entry3, entry4)
            }

            backstackMap = rememberBackstackMap(
                initialBackstackEntries = initialBackstackEntries,
                backstackMapSerializer = BackstackMapSerializer(
                    convertToSurrogate = TestEntryType::surrogate,
                ),
            )
        }

        assertNotNull(backstackMap)
        backstackMap = null

        stateRestorationTester.emulateStateRestore()

        val restoredBackstackMap = assertNotNull(backstackMap)
        assertEquals(4, restoredBackstackMap.size)
        assertEquals("a", restoredBackstackMap[id1]?.value?.fullValue)
        assertEquals("ab", restoredBackstackMap[id2]?.value?.fullValue)
        assertEquals("abc", restoredBackstackMap[id3]?.value?.fullValue)
        assertEquals("abcd", restoredBackstackMap[id4]?.value?.fullValue)
    }

    @Test
    fun backstack_state_extension_properties_are_correct() {
        val entry1 = BackstackEntry(
            value = "a",
            previous = null,
            id = id1,
        )
        val entry2 = BackstackEntry(
            value = "b",
            previous = entry1,
            id = id2,
        )

        val backstackState = object : BackstackState<String> {
            override val entryMap = mapOf(
                id1 to entry1,
                id2 to entry2,
            )
            override val currentEntryId = id2
        }

        assertEquals(id1, backstackState.previousEntryId)
        assertEquals(entry1, backstackState.previousEntry)

        val backstackStateNoPrevious = object : BackstackState<String> {
            override val entryMap = mapOf(
                id1 to entry1,
            )
            override val currentEntryId = id1
        }

        assertEquals(null, backstackStateNoPrevious.previousEntryId)
        assertEquals(null, backstackStateNoPrevious.previousEntry)
    }

    @Test
    fun backstack_state_previous_entry_missing_from_map() {
        val missingEntry = BackstackEntry(
            value = "missing",
            previous = null,
            id = id1,
        )
        val entry = BackstackEntry(
            value = "current",
            previous = missingEntry,
            id = id2,
        )
        val backstackState = object : BackstackState<String> {
            override val entryMap = mapOf(id2 to entry)
            override val currentEntryId = id2
        }
        assertEquals(id1, backstackState.previousEntryId)
        assertEquals(null, backstackState.previousEntry)
    }

    @Test
    fun value_as_surrogate_is_correct() {
        val surrogate = ValueAsSurrogate("value")
        assertEquals("value", surrogate.value)
        assertEquals("value", surrogate.createFromSurrogate(null))
        assertEquals("value", surrogate.component1())
        val copy = surrogate.copy(value = "other")
        assertEquals("other", copy.value)
        assertEquals(surrogate, ValueAsSurrogate("value"))
    }

    @Test
    fun branching_backstack_state_is_saved_correctly() = runComposeUiTest {
        val stateRestorationTester = KmpStateRestorationTester(this)

        @Suppress("DoubleMutabilityForCollection")
        var backstackMap: MutableBackstackMap<String>? = null

        stateRestorationTester.setContent {
            val initialBackstackEntries = remember {
                val entry1 = BackstackEntry(
                    value = "root",
                    previous = null,
                    id = id1,
                )
                val entry2a = BackstackEntry(
                    value = "branchA",
                    previous = entry1,
                    id = id2,
                )
                val entry2b = BackstackEntry(
                    value = "branchB",
                    previous = entry1,
                    id = id3,
                )
                val entry3 = BackstackEntry(
                    value = "leaf",
                    previous = entry2a,
                    id = id4,
                )

                listOf(entry1, entry2a, entry2b, entry3)
            }

            backstackMap = rememberBackstackMap(
                initialBackstackEntries = initialBackstackEntries,
            )
        }

        assertNotNull(backstackMap)
        backstackMap = null

        stateRestorationTester.emulateStateRestore()

        val restoredBackstackMap = assertNotNull(backstackMap)
        assertEquals(4, restoredBackstackMap.size)
        assertEquals("root", restoredBackstackMap[id1]?.value)
        assertEquals("branchA", restoredBackstackMap[id2]?.value)
        assertEquals("branchB", restoredBackstackMap[id3]?.value)
        assertEquals("leaf", restoredBackstackMap[id4]?.value)
        assertEquals(id1, restoredBackstackMap[id2]?.previous?.id)
        assertEquals(id1, restoredBackstackMap[id3]?.previous?.id)
        assertEquals(id2, restoredBackstackMap[id4]?.previous?.id)
    }

    @Test
    fun backstack_state_with_explicit_serializer_is_saved_correctly() = runComposeUiTest {
        val stateRestorationTester = KmpStateRestorationTester(this)

        @Suppress("DoubleMutabilityForCollection")
        var backstackMap: MutableBackstackMap<String>? = null

        stateRestorationTester.setContent {
            val initialBackstackEntries = remember {
                listOf(
                    BackstackEntry(
                        value = "a",
                        previous = null,
                        id = id1,
                    ),
                )
            }

            backstackMap = rememberBackstackMap(
                initialBackstackEntries = initialBackstackEntries,
                serializer = String.serializer(),
            )
        }

        assertNotNull(backstackMap)
        backstackMap = null

        stateRestorationTester.emulateStateRestore()

        val restoredBackstackMap = assertNotNull(backstackMap)
        assertEquals(1, restoredBackstackMap.size)
        assertEquals("a", restoredBackstackMap[id1]?.value)
    }
}

class TestEntryType(val value: String, val previous: TestEntryType?) {
    val fullValue: String get() = previous?.fullValue.orEmpty() + value

    val surrogate get() = Surrogate(value)

    @Serializable
    data class Surrogate(val value: String) : BackstackValueSurrogate<TestEntryType> {
        override fun createFromSurrogate(previous: BackstackEntry<TestEntryType>?): TestEntryType = TestEntryType(
            value = value,
            previous = previous?.value,
        )
    }
}
