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

import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.runComposeUiTest
import com.alexvanyo.composelife.kmpandroidrunner.KmpAndroidJUnit4
import org.junit.runner.RunWith
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith
import kotlin.test.assertFalse
import kotlin.test.assertTrue
import kotlin.uuid.Uuid

@OptIn(ExperimentalTestApi::class)
@Suppress("TooManyFunctions")
@RunWith(KmpAndroidJUnit4::class)
class MutableBackstackNavigationControllerTests {

    private val id1 = Uuid.random()
    private val id2 = Uuid.random()
    private val id3 = Uuid.random()
    private val id4 = Uuid.random()

    @Test
    fun empty_initial_backstack_entries_throws_exception() = runComposeUiTest {
        assertFailsWith<IllegalArgumentException> {
            setContent {
                rememberMutableBackstackNavigationController<String>(
                    initialBackstackEntries = emptyList(),
                )
            }
        }
    }

    @Test
    fun initial_navigation_state_is_correct() = runComposeUiTest {
        lateinit var navController: MutableBackstackNavigationController<String>

        setContent {
            navController = rememberMutableBackstackNavigationController(
                initialBackstackEntries = listOf(
                    BackstackEntry(
                        value = "a",
                        previous = null,
                        id = id1,
                    ),
                ),
            )
        }

        assertEquals(id1, navController.currentEntryId)
        assertEquals("a", navController.currentEntry.value)
        assertFalse(navController.canNavigateBack)
        assertEquals(1, navController.entryMap.size)
    }

    @Test
    fun navigation_state_is_correct_after_navigating() = runComposeUiTest {
        lateinit var navController: MutableBackstackNavigationController<String>

        setContent {
            navController = rememberMutableBackstackNavigationController(
                initialBackstackEntries = listOf(
                    BackstackEntry(
                        value = "a",
                        previous = null,
                        id = id1,
                    ),
                ),
            )
        }

        navController.navigate(
            value = "b",
            id = id2,
        )

        assertEquals(id2, navController.currentEntryId)
        assertEquals("b", navController.currentEntry.value)
        assertTrue(navController.canNavigateBack)
        assertEquals(2, navController.entryMap.size)
    }

    @Test
    fun navigation_state_is_correct_after_navigating_with_random_id() = runComposeUiTest {
        lateinit var navController: MutableBackstackNavigationController<String>

        setContent {
            navController = rememberMutableBackstackNavigationController(
                initialBackstackEntries = listOf(
                    BackstackEntry(
                        value = "a",
                        previous = null,
                        id = id1,
                    ),
                ),
            )
        }

        navController.navigate(
            value = "b",
        )

        val newId = navController.entryMap.filterKeys { it != id1 }.keys.first()

        assertEquals(newId, navController.currentEntryId)
        assertEquals("b", navController.currentEntry.value)
        assertTrue(navController.canNavigateBack)
        assertEquals(2, navController.entryMap.size)
    }

    @Test
    fun navigation_state_is_correct_after_navigating_with_value_factory() = runComposeUiTest {
        lateinit var navController: MutableBackstackNavigationController<String>

        setContent {
            navController = rememberMutableBackstackNavigationController(
                initialBackstackEntries = listOf(
                    BackstackEntry(
                        value = "a",
                        previous = null,
                        id = id1,
                    ),
                ),
            )
        }

        navController.navigate(
            valueFactory = { it.value + "2" },
            id = id2,
        )

        assertEquals(id2, navController.currentEntryId)
        assertEquals("a2", navController.currentEntry.value)
        assertTrue(navController.canNavigateBack)
        assertEquals(2, navController.entryMap.size)
    }

    @Test
    fun navigation_state_is_correct_after_navigating_with_value_factory_and_random_id() = runComposeUiTest {
        lateinit var navController: MutableBackstackNavigationController<String>

        setContent {
            navController = rememberMutableBackstackNavigationController(
                initialBackstackEntries = listOf(
                    BackstackEntry(
                        value = "a",
                        previous = null,
                        id = id1,
                    ),
                ),
            )
        }

        navController.navigate(
            valueFactory = { it.value + "2" },
        )

        val newId = navController.entryMap.filterKeys { it != id1 }.keys.first()

        assertEquals(newId, navController.currentEntryId)
        assertEquals("a2", navController.currentEntry.value)
        assertTrue(navController.canNavigateBack)
        assertEquals(2, navController.entryMap.size)
    }

    @Test
    fun navigation_state_is_correct_after_navigating_and_popping_backstack() = runComposeUiTest {
        lateinit var navController: MutableBackstackNavigationController<String>

        setContent {
            navController = rememberMutableBackstackNavigationController(
                initialBackstackEntries = listOf(
                    BackstackEntry(
                        value = "a",
                        previous = null,
                        id = id1,
                    ),
                ),
            )
        }

        navController.navigate(
            value = "b",
            id = id2,
        )
        navController.popBackstack()

        assertEquals(id1, navController.currentEntryId)
        assertEquals("a", navController.currentEntry.value)
        assertFalse(navController.canNavigateBack)
        assertEquals(1, navController.entryMap.size)
    }

    @Test
    fun navigation_state_is_correct_after_navigating_repeatedly() = runComposeUiTest {
        lateinit var navController: MutableBackstackNavigationController<String>

        setContent {
            navController = rememberMutableBackstackNavigationController(
                initialBackstackEntries = listOf(
                    BackstackEntry(
                        value = "a",
                        previous = null,
                        id = id1,
                    ),
                ),
            )
        }

        navController.navigate(
            value = "b",
            id = id2,
        )
        navController.navigate(
            value = "c",
            id = id3,
        )
        navController.navigate(
            value = "d",
            id = id4,
        )

        assertEquals(id4, navController.currentEntryId)
        assertEquals("d", navController.currentEntry.value)
        assertTrue(navController.canNavigateBack)
        assertEquals(4, navController.entryMap.size)
    }

    @Test
    fun navigation_state_is_correct_after_navigating_repeatedly_and_popping_up_to_id() = runComposeUiTest {
        lateinit var navController: MutableBackstackNavigationController<String>

        setContent {
            navController = rememberMutableBackstackNavigationController(
                initialBackstackEntries = listOf(
                    BackstackEntry(
                        value = "a",
                        previous = null,
                        id = id1,
                    ),
                ),
            )
        }

        navController.navigate(
            value = "b",
            id = id2,
        )
        navController.navigate(
            value = "c",
            id = id3,
        )
        navController.navigate(
            value = "d",
            id = id4,
        )
        navController.popUpTo(id2)

        assertEquals(id2, navController.currentEntryId)
        assertEquals("b", navController.currentEntry.value)
        assertTrue(navController.canNavigateBack)
        assertEquals(2, navController.entryMap.size)
    }

    @Test
    fun navigation_state_is_correct_after_navigating_repeatedly_and_popping_up_to_value() = runComposeUiTest {
        lateinit var navController: MutableBackstackNavigationController<String>

        setContent {
            navController = rememberMutableBackstackNavigationController(
                initialBackstackEntries = listOf(
                    BackstackEntry(
                        value = "a",
                        previous = null,
                        id = id1,
                    ),
                ),
            )
        }

        navController.navigate(
            value = "b",
            id = id2,
        )
        navController.navigate(
            value = "c",
            id = id3,
        )
        navController.navigate(
            value = "d",
            id = id4,
        )
        navController.popUpTo(predicate = { it == "b" })

        assertEquals(id2, navController.currentEntryId)
        assertEquals("b", navController.currentEntry.value)
        assertTrue(navController.canNavigateBack)
        assertEquals(2, navController.entryMap.size)
    }

    @Test
    fun navigation_state_is_correct_after_navigating_repeatedly_and_popping_up_to_entry() = runComposeUiTest {
        lateinit var navController: MutableBackstackNavigationController<String>

        setContent {
            navController = rememberMutableBackstackNavigationController(
                initialBackstackEntries = listOf(
                    BackstackEntry(
                        value = "a",
                        previous = null,
                        id = id1,
                    ),
                ),
            )
        }

        navController.navigate(
            value = "b",
            id = id2,
        )
        navController.navigate(
            value = "c",
            id = id3,
        )
        navController.navigate(
            value = "d",
            id = id4,
        )
        navController.popUpTo(entryPredicate = { it.value == "b" })

        assertEquals(id2, navController.currentEntryId)
        assertEquals("b", navController.currentEntry.value)
        assertTrue(navController.canNavigateBack)
        assertEquals(2, navController.entryMap.size)
    }

    @Test
    fun navigation_state_is_correct_after_with_expected_actor_fails() = runComposeUiTest {
        lateinit var navController: MutableBackstackNavigationController<String>

        setContent {
            navController = rememberMutableBackstackNavigationController(
                initialBackstackEntries = listOf(
                    BackstackEntry(
                        value = "a",
                        previous = null,
                        id = id1,
                    ),
                ),
            )
        }

        navController.navigate(
            value = "b",
            id = id2,
        )
        navController.navigate(
            value = "c",
            id = id3,
        )
        navController.navigate(
            value = "d",
            id = id4,
        )

        assertTrue {
            navController.withExpectedActor(id4) {
                popBackstack()
            }
        }
        assertFalse {
            navController.withExpectedActor(id4) {
                popBackstack()
            }
        }

        assertEquals(id3, navController.currentEntryId)
        assertEquals("c", navController.currentEntry.value)
        assertTrue(navController.canNavigateBack)
        assertEquals(3, navController.entryMap.size)
    }

    @Test
    fun navigation_state_is_correct_after_with_expected_actor_succeeds() = runComposeUiTest {
        lateinit var navController: MutableBackstackNavigationController<String>

        setContent {
            navController = rememberMutableBackstackNavigationController(
                initialBackstackEntries = listOf(
                    BackstackEntry(
                        value = "a",
                        previous = null,
                        id = id1,
                    ),
                ),
            )
        }

        navController.navigate(
            value = "b",
            id = id2,
        )
        navController.navigate(
            value = "c",
            id = id3,
        )
        navController.navigate(
            value = "d",
            id = id4,
        )

        assertTrue {
            navController.withExpectedActor(id4) {
                popBackstack()
            }
        }

        assertEquals(id3, navController.currentEntryId)
        assertEquals("c", navController.currentEntry.value)
        assertTrue(navController.canNavigateBack)
        assertEquals(3, navController.entryMap.size)
    }

    @Test
    fun navigation_state_is_correct_after_with_expected_actor_succeeds_by_null() = runComposeUiTest {
        lateinit var navController: MutableBackstackNavigationController<String>

        setContent {
            navController = rememberMutableBackstackNavigationController(
                initialBackstackEntries = listOf(
                    BackstackEntry(
                        value = "a",
                        previous = null,
                        id = id1,
                    ),
                ),
            )
        }

        navController.navigate(
            value = "b",
            id = id2,
        )
        navController.navigate(
            value = "c",
            id = id3,
        )
        navController.navigate(
            value = "d",
            id = id4,
        )

        assertTrue {
            navController.withExpectedActor(null) {
                popBackstack()
            }
        }

        assertEquals(id3, navController.currentEntryId)
        assertEquals("c", navController.currentEntry.value)
        assertTrue(navController.canNavigateBack)
        assertEquals(3, navController.entryMap.size)
    }
}
