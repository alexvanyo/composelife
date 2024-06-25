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

import androidx.compose.foundation.clickable
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.text.BasicText
import androidx.compose.runtime.CompositionLocalProvider
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateMapOf
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.setValue
import androidx.compose.ui.Modifier
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.onNodeWithText
import androidx.compose.ui.test.performClick
import androidx.compose.ui.test.runComposeUiTest
import com.alexvanyo.composelife.kmpandroidrunner.KmpAndroidJUnit4
import com.alexvanyo.composelife.kmpstaterestorationtester.KmpStateRestorationTester
import com.benasher44.uuid.Uuid
import com.benasher44.uuid.uuid4
import com.benasher44.uuid.uuidFrom
import com.slack.circuit.retained.LocalRetainedStateRegistry
import com.slack.circuit.retained.RetainedStateRegistry
import com.slack.circuit.retained.rememberRetained
import org.junit.runner.RunWith
import kotlin.test.Test

@OptIn(ExperimentalTestApi::class)
@RunWith(KmpAndroidJUnit4::class)
class NavigationHostTests {

    @Test
    fun navigation_host_displays_current_entry() = runComposeUiTest {
        val id = uuidFrom("00000000-0000-0000-0000-000000000000")
        val entry = BackstackEntry(
            value = "a",
            previous = null,
            id = id,
        )

        val navigationState = object : NavigationState<BackstackEntry<String>> {
            override val entryMap get() = mapOf(id to entry)
            override val currentEntryId get() = id
        }

        setContent {
            NavigationHost(
                navigationState = navigationState,
            ) { entry ->
                BasicText("value: ${entry.value}, id: ${entry.id}")
            }
        }

        onNodeWithText("value: a, id: $id").assertExists()
    }

    @Test
    fun navigation_host_displays_current_entry_with_multiple_entries() = runComposeUiTest {
        val id1 = uuidFrom("00000000-0000-0000-0000-000000000000")
        val id2 = uuidFrom("11111111-1111-1111-1111-111111111111")
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

        val navigationState = object : BackstackState<String> {
            override val entryMap: Map<Uuid, BackstackEntry<String>> = mapOf(
                id1 to entry1,
                id2 to entry2,
            )
            override val currentEntryId: Uuid = id2
        }

        setContent {
            NavigationHost(
                navigationState = navigationState,
            ) { entry ->
                BasicText("value: ${entry.value}, id: ${entry.id}")
            }
        }

        onNodeWithText("value: b, id: $id2").assertExists()
    }

    @Test
    fun navigation_host_keeps_state_for_entries_in_map() = runComposeUiTest {
        val id1 = uuidFrom("00000000-0000-0000-0000-000000000000")
        val id2 = uuidFrom("11111111-1111-1111-1111-111111111111")
        val entry1 = BackstackEntry(
            value = "a",
            previous = null,
            id = id1,
        )
        val entry2 = BackstackEntry(
            value = "b",
            previous = null,
            id = id2,
        )

        val backstackMap = mutableStateMapOf<Uuid, BackstackEntry<String>>(
            id1 to entry1,
            id2 to entry2,
        )

        var currentEntryId by mutableStateOf(id1)

        val navigationState = object : BackstackState<String> {
            override val entryMap get() = backstackMap
            override val currentEntryId get() = currentEntryId
        }

        val retainedStateRegistry = RetainedStateRegistry()

        setContent {
            CompositionLocalProvider(LocalRetainedStateRegistry provides retainedStateRegistry) {
                NavigationHost(
                    navigationState = navigationState,
                ) { entry ->
                    var rememberSaveableCount by rememberSaveable { mutableStateOf(0) }
                    var rememberRetainedCount by rememberRetained { mutableStateOf(0) }

                    Column {
                        BasicText(
                            "value: ${entry.value}, id: ${entry.id}, " +
                                "rememberSaveableCount: $rememberSaveableCount, " +
                                "rememberRetainedCount: $rememberRetainedCount",
                        )
                        BasicText(
                            "+",
                            modifier = Modifier.clickable {
                                rememberSaveableCount++
                                rememberRetainedCount++
                            },
                        )
                    }
                }
            }
        }

        onNodeWithText("value: a, id: $id1, rememberSaveableCount: 0, rememberRetainedCount: 0").assertExists()

        onNodeWithText("+").performClick()

        onNodeWithText("value: a, id: $id1, rememberSaveableCount: 1, rememberRetainedCount: 1").assertExists()

        currentEntryId = id2

        onNodeWithText("value: b, id: $id2, rememberSaveableCount: 0, rememberRetainedCount: 0").assertExists()

        currentEntryId = id1

        onNodeWithText("value: a, id: $id1, rememberSaveableCount: 1, rememberRetainedCount: 1").assertExists()
    }

    @Test
    fun navigation_host_does_not_keep_state_for_entries_not_in_map() = runComposeUiTest {
        val id1 = uuidFrom("00000000-0000-0000-0000-000000000000")
        val id2 = uuidFrom("11111111-1111-1111-1111-111111111111")
        val entry1 = BackstackEntry(
            value = "a",
            previous = null,
            id = id1,
        )
        val entry2 = BackstackEntry(
            value = "b",
            previous = null,
            id = id2,
        )

        val backstackMap = mutableStateMapOf<Uuid, BackstackEntry<String>>(
            id1 to entry1,
            id2 to entry2,
        )

        var currentEntryId by mutableStateOf(id1)

        val navigationState = object : BackstackState<String> {
            override val entryMap get() = backstackMap
            override val currentEntryId get() = currentEntryId
        }

        val retainedStateRegistry = RetainedStateRegistry()

        setContent {
            CompositionLocalProvider(LocalRetainedStateRegistry provides retainedStateRegistry) {
                NavigationHost(
                    navigationState = navigationState,
                ) { entry ->
                    var rememberSaveableCount by rememberSaveable { mutableStateOf(0) }
                    var rememberRetainedCount by rememberRetained(key = "rememberRetainedCount") {
                        mutableStateOf(0)
                    }

                    Column {
                        BasicText(
                            "value: ${entry.value}, id: ${entry.id}, " +
                                "rememberSaveableCount: $rememberSaveableCount, " +
                                "rememberRetainedCount: $rememberRetainedCount",
                        )
                        BasicText(
                            "+",
                            modifier = Modifier.clickable {
                                rememberSaveableCount++
                                rememberRetainedCount++
                            },
                        )
                    }
                }
            }
        }

        onNodeWithText("value: a, id: $id1, rememberSaveableCount: 0, rememberRetainedCount: 0").assertExists()

        onNodeWithText("+").performClick()

        onNodeWithText("value: a, id: $id1, rememberSaveableCount: 1, rememberRetainedCount: 1").assertExists()

        currentEntryId = id2
        backstackMap.remove(id1)

        onNodeWithText("value: b, id: $id2, rememberSaveableCount: 0, rememberRetainedCount: 0").assertExists()

        currentEntryId = id1
        backstackMap[id1] = entry1

        onNodeWithText("value: a, id: $id1, rememberSaveableCount: 0, rememberRetainedCount: 0").assertExists()
    }

    @Test
    fun navigation_host_does_not_keep_state_for_entries_not_in_map_and_not_rendered() = runComposeUiTest {
        val id1 = uuidFrom("00000000-0000-0000-0000-000000000000")
        val id2 = uuidFrom("11111111-1111-1111-1111-111111111111")
        val id3 = uuidFrom("22222222-2222-2222-2222-222222222222")
        val entry1 = BackstackEntry(
            value = "a",
            previous = null,
            id = id1,
        )
        val entry2 = BackstackEntry(
            value = "b",
            previous = null,
            id = id2,
        )
        val entry3 = BackstackEntry(
            value = "c",
            previous = null,
            id = id3,
        )

        val backstackMap = mutableStateMapOf<Uuid, BackstackEntry<String>>(
            id1 to entry1,
            id2 to entry2,
            id3 to entry3,
        )

        var currentEntryId by mutableStateOf(id1)

        val navigationState = object : BackstackState<String> {
            override val entryMap get() = backstackMap
            override val currentEntryId get() = currentEntryId
        }

        val retainedStateRegistry = RetainedStateRegistry()

        setContent {
            CompositionLocalProvider(LocalRetainedStateRegistry provides retainedStateRegistry) {
                NavigationHost(
                    navigationState = navigationState,
                ) { entry ->
                    var rememberSaveableCount by rememberSaveable { mutableStateOf(0) }
                    var rememberRetainedCount by rememberRetained(key = "rememberRetainedCount") {
                        mutableStateOf(0)
                    }

                    Column {
                        BasicText(
                            "value: ${entry.value}, id: ${entry.id}, " +
                                "rememberSaveableCount: $rememberSaveableCount, " +
                                "rememberRetainedCount: $rememberRetainedCount",
                        )
                        BasicText(
                            "+",
                            modifier = Modifier.clickable {
                                rememberSaveableCount++
                                rememberRetainedCount++
                            },
                        )
                    }
                }
            }
        }

        onNodeWithText("value: a, id: $id1, rememberSaveableCount: 0, rememberRetainedCount: 0").assertExists()

        onNodeWithText("+").performClick()

        onNodeWithText("value: a, id: $id1, rememberSaveableCount: 1, rememberRetainedCount: 1").assertExists()

        currentEntryId = id2

        onNodeWithText("value: b, id: $id2, rememberSaveableCount: 0, rememberRetainedCount: 0").assertExists()

        currentEntryId = id3

        onNodeWithText("value: c, id: $id3, rememberSaveableCount: 0, rememberRetainedCount: 0").assertExists()

        backstackMap.remove(id1)

        onNodeWithText("value: c, id: $id3, rememberSaveableCount: 0, rememberRetainedCount: 0").assertExists()

        backstackMap[id1] = entry1
        currentEntryId = id1

        onNodeWithText("value: a, id: $id1, rememberSaveableCount: 0, rememberRetainedCount: 0").assertExists()
    }

    @Test
    fun navigation_host_state_is_preserved_through_recreation() = runComposeUiTest {
        val stateRestorationTester = KmpStateRestorationTester(this)

        val id1 = uuid4()
        val id2 = uuid4()
        val entry1 = BackstackEntry(
            value = "a",
            previous = null,
            id = id1,
        )
        val entry2 = BackstackEntry(
            value = "b",
            previous = null,
            id = id2,
        )

        val backstackMap = mutableStateMapOf<Uuid, BackstackEntry<String>>(
            id1 to entry1,
            id2 to entry2,
        )

        var currentEntryId by mutableStateOf(id1)

        val navigationState = object : BackstackState<String> {
            override val entryMap get() = backstackMap
            override val currentEntryId get() = currentEntryId
        }

        val retainedStateRegistry = RetainedStateRegistry()

        stateRestorationTester.setContent {
            CompositionLocalProvider(LocalRetainedStateRegistry provides retainedStateRegistry) {
                NavigationHost(
                    navigationState = navigationState,
                ) { entry ->
                    var rememberSaveableCount by rememberSaveable { mutableStateOf(0) }
                    var rememberRetainedCount by rememberRetained { mutableStateOf(0) }

                    Column {
                        BasicText(
                            "value: ${entry.value}, id: ${entry.id}, " +
                                "rememberSaveableCount: $rememberSaveableCount, " +
                                "rememberRetainedCount: $rememberRetainedCount",
                        )
                        BasicText(
                            "+",
                            modifier = Modifier.clickable {
                                rememberSaveableCount++
                                rememberRetainedCount++
                            },
                        )
                    }
                }
            }
        }

        onNodeWithText("value: a, id: $id1, rememberSaveableCount: 0, rememberRetainedCount: 0").assertExists()

        onNodeWithText("+").performClick()

        onNodeWithText("value: a, id: $id1, rememberSaveableCount: 1, rememberRetainedCount: 1").assertExists()

        currentEntryId = id2

        onNodeWithText("value: b, id: $id2, rememberSaveableCount: 0, rememberRetainedCount: 0").assertExists()

        stateRestorationTester.emulateSavedInstanceStateRestore()

        currentEntryId = id1

        onNodeWithText("value: a, id: $id1, rememberSaveableCount: 1, rememberRetainedCount: 1").assertExists()
    }
}
