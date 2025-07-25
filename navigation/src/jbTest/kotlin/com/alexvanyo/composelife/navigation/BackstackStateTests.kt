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
import androidx.compose.runtime.saveable.Saver
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.runComposeUiTest
import com.alexvanyo.composelife.kmpandroidrunner.KmpAndroidJUnit4
import com.alexvanyo.composelife.kmpstaterestorationtester.KmpStateRestorationTester
import org.junit.runner.RunWith
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotNull
import kotlin.uuid.Uuid

@OptIn(ExperimentalTestApi::class)
@RunWith(KmpAndroidJUnit4::class)
class BackstackStateTests {

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
                backstackValueSaverFactory = { entry ->
                    Saver(
                        save = { it.value },
                        restore = {
                            TestEntryType(
                                value = it as String,
                                previous = entry?.value,
                            )
                        },
                    )
                },
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
}

class TestEntryType(
    val value: String,
    val previous: TestEntryType?,
) {
    val fullValue: String get() = previous?.fullValue.orEmpty() + value
}
