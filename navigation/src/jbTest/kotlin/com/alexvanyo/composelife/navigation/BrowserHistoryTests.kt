/*
 * Copyright 2026 The Android Open Source Project
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

import androidx.compose.runtime.LaunchedEffect
import androidx.compose.ui.test.ExperimentalTestApi
import com.alexvanyo.composelife.kmpandroidrunner.BaseKmpTest
import com.alexvanyo.composelife.test.runComposeUiTest
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue
import kotlin.uuid.Uuid

@OptIn(ExperimentalTestApi::class)
class BrowserHistoryTests : BaseKmpTest() {

    private val id1 = Uuid.random()
    private val id2 = Uuid.random()
    private val id3 = Uuid.random()
    private val id4 = Uuid.random()

    @Test
    fun in_app_navigation_pushes_browser_history_and_updates_fragment() = runComposeUiTest {
        val browserHistory = FakeBrowserHistory()
        lateinit var navController: MutableBackstackNavigationController<String>

        setContent {
            navController = rememberMutableBackstackNavigationController(
                initialBackstackEntries = listOf(
                    BackstackEntry(value = "home", previous = null, id = id1),
                ),
            )
            LaunchedEffect(navController) {
                navController.bindToBrowserHistory(
                    browserHistory = browserHistory,
                    getBackstackFragment = { if (it.value == "home") "" else it.value },
                )
            }
        }

        waitForIdle()
        assertEquals(1, browserHistory.entries.size)
        assertEquals(0, browserHistory.currentIndex)
        assertEquals("", browserHistory.currentFragment)

        navController.navigate(value = "settings", id = id2)
        waitForIdle()

        assertEquals(2, browserHistory.entries.size)
        assertEquals(1, browserHistory.currentIndex)
        assertEquals("settings", browserHistory.currentFragment)

        navController.navigate(value = "settings/visual", id = id3)
        waitForIdle()

        assertEquals(3, browserHistory.entries.size)
        assertEquals(2, browserHistory.currentIndex)
        assertEquals("settings/visual", browserHistory.currentFragment)
    }

    @Test
    fun browser_back_and_forward_synchronizes_navigation_controller() = runComposeUiTest {
        val browserHistory = FakeBrowserHistory()
        lateinit var navController: MutableBackstackNavigationController<String>

        setContent {
            navController = rememberMutableBackstackNavigationController(
                initialBackstackEntries = listOf(
                    BackstackEntry(value = "home", previous = null, id = id1),
                ),
            )
            LaunchedEffect(navController) {
                navController.bindToBrowserHistory(
                    browserHistory = browserHistory,
                    getBackstackFragment = { if (it.value == "home") "" else it.value },
                )
            }
        }

        waitForIdle()
        navController.navigate(value = "settings", id = id2)
        waitForIdle()
        navController.navigate(value = "detail", id = id3)
        waitForIdle()

        // Browser Back to "settings"
        browserHistory.back()
        waitForIdle()

        assertEquals(id2, navController.currentEntryId)
        assertEquals("settings", navController.currentEntry.value)
        assertEquals(2, navController.entryMap.size)
        assertEquals(1, browserHistory.currentIndex)

        // Browser Back to "home"
        browserHistory.back()
        waitForIdle()

        assertEquals(id1, navController.currentEntryId)
        assertEquals("home", navController.currentEntry.value)
        assertFalse(navController.canNavigateBack)
        assertEquals(1, navController.entryMap.size)
        assertEquals(0, browserHistory.currentIndex)

        // Browser Forward to "settings"
        browserHistory.forward()
        waitForIdle()

        assertEquals(id2, navController.currentEntryId)
        assertEquals("settings", navController.currentEntry.value)
        assertTrue(navController.canNavigateBack)
        assertEquals(2, navController.entryMap.size)
        assertEquals(1, browserHistory.currentIndex)

        // Browser Forward to "detail"
        browserHistory.forward()
        waitForIdle()

        assertEquals(id3, navController.currentEntryId)
        assertEquals("detail", navController.currentEntry.value)
        assertEquals(3, navController.entryMap.size)
        assertEquals(2, browserHistory.currentIndex)
    }

    @Test
    fun in_app_back_moves_browser_history_back_and_allows_browser_forward() = runComposeUiTest {
        val browserHistory = FakeBrowserHistory()
        lateinit var navController: MutableBackstackNavigationController<String>

        setContent {
            navController = rememberMutableBackstackNavigationController(
                initialBackstackEntries = listOf(
                    BackstackEntry(value = "home", previous = null, id = id1),
                ),
            )
            LaunchedEffect(navController) {
                navController.bindToBrowserHistory(
                    browserHistory = browserHistory,
                    getBackstackFragment = { if (it.value == "home") "" else it.value },
                )
            }
        }

        waitForIdle()
        navController.navigate(value = "settings", id = id2)
        waitForIdle()
        navController.navigate(value = "detail", id = id3)
        waitForIdle()

        // In-app Back pops "detail"
        navController.popBackstack()
        waitForIdle()

        assertEquals(id2, navController.currentEntryId)
        assertEquals(1, browserHistory.currentIndex)
        assertEquals("settings", browserHistory.currentFragment)
        assertEquals(3, browserHistory.entries.size)

        // Browser Forward restores "detail"
        browserHistory.forward()
        waitForIdle()

        assertEquals(id3, navController.currentEntryId)
        assertEquals("detail", navController.currentEntry.value)
        assertEquals(2, browserHistory.currentIndex)
        assertEquals("detail", browserHistory.currentFragment)
    }

    @Test
    fun in_app_navigation_after_browser_back_truncates_forward_history() = runComposeUiTest {
        val browserHistory = FakeBrowserHistory()
        lateinit var navController: MutableBackstackNavigationController<String>

        setContent {
            navController = rememberMutableBackstackNavigationController(
                initialBackstackEntries = listOf(
                    BackstackEntry(value = "home", previous = null, id = id1),
                ),
            )
            LaunchedEffect(navController) {
                navController.bindToBrowserHistory(
                    browserHistory = browserHistory,
                    getBackstackFragment = { if (it.value == "home") "" else it.value },
                )
            }
        }

        waitForIdle()
        navController.navigate(value = "settings", id = id2)
        waitForIdle()
        navController.navigate(value = "detail", id = id3)
        waitForIdle()

        browserHistory.back()
        waitForIdle()
        assertEquals(id2, navController.currentEntryId)

        // Navigate to a new branch "other"
        navController.navigate(value = "other", id = id4)
        waitForIdle()

        assertEquals(3, browserHistory.entries.size)
        assertEquals(2, browserHistory.currentIndex)
        assertEquals("other", browserHistory.currentFragment)

        // Back goes to "settings", forward goes to "other" (not "detail")
        browserHistory.back()
        waitForIdle()
        assertEquals(id2, navController.currentEntryId)

        browserHistory.forward()
        waitForIdle()
        assertEquals(id4, navController.currentEntryId)
        assertEquals("other", navController.currentEntry.value)
    }

    @Test
    fun initial_fragment_deep_links_on_bind() = runComposeUiTest {
        val browserHistory = FakeBrowserHistory(initialFragment = "settings")
        lateinit var navController: MutableBackstackNavigationController<String>

        setContent {
            navController = rememberMutableBackstackNavigationController(
                initialBackstackEntries = listOf(
                    BackstackEntry(value = "home", previous = null, id = id1),
                ),
            )
            LaunchedEffect(navController) {
                navController.bindToBrowserHistory(
                    browserHistory = browserHistory,
                    getBackstackFragment = { if (it.value == "home") "" else it.value },
                    parseFragment = { fragment ->
                        if (fragment == "settings") {
                            val home = BackstackEntry(value = "home", previous = null, id = id1)
                            val settings = BackstackEntry(value = "settings", previous = home, id = id2)
                            listOf(home, settings)
                        } else {
                            null
                        }
                    },
                )
            }
        }

        waitForIdle()

        assertEquals(id2, navController.currentEntryId)
        assertEquals("settings", navController.currentEntry.value)
        assertEquals(2, navController.entryMap.size)
        assertEquals("settings", browserHistory.currentFragment)
    }

    @Test
    fun manual_hash_change_updates_navigation_state() = runComposeUiTest {
        val browserHistory = FakeBrowserHistory()
        lateinit var navController: MutableBackstackNavigationController<String>

        setContent {
            navController = rememberMutableBackstackNavigationController(
                initialBackstackEntries = listOf(
                    BackstackEntry(value = "home", previous = null, id = id1),
                ),
            )
            LaunchedEffect(navController) {
                navController.bindToBrowserHistory(
                    browserHistory = browserHistory,
                    getBackstackFragment = { if (it.value == "home") "" else it.value },
                    parseFragment = { fragment ->
                        if (fragment == "settings") {
                            val home = BackstackEntry(value = "home", previous = null, id = id1)
                            val settings = BackstackEntry(value = "settings", previous = home, id = id2)
                            listOf(home, settings)
                        } else {
                            null
                        }
                    },
                )
            }
        }

        waitForIdle()
        assertEquals(id1, navController.currentEntryId)

        // Simulate user editing URL hash in address bar
        browserHistory.navigateToHash("settings")
        waitForIdle()

        assertEquals(id2, navController.currentEntryId)
        assertEquals("settings", navController.currentEntry.value)
        assertEquals(2, browserHistory.entries.size)

        // Browser back returns to "home"
        browserHistory.back()
        waitForIdle()
        assertEquals(id1, navController.currentEntryId)
        assertEquals("home", navController.currentEntry.value)
    }

    @Test
    fun state_restores_across_page_reload_and_supports_back() = runComposeUiTest {
        val browserHistory = FakeBrowserHistory()
        lateinit var navController1: MutableBackstackNavigationController<String>

        setContent {
            navController1 = rememberMutableBackstackNavigationController(
                initialBackstackEntries = listOf(
                    BackstackEntry(value = "home", previous = null, id = id1),
                ),
            )
            LaunchedEffect(navController1) {
                navController1.bindToBrowserHistory(
                    browserHistory = browserHistory,
                    getBackstackFragment = { if (it.value == "home") "" else it.value },
                )
            }
        }

        waitForIdle()
        navController1.navigate(value = "settings", id = id2)
        waitForIdle()
        assertEquals(1, browserHistory.currentIndex)

        // Simulate page reload with a fresh navController bound to the same browserHistory
        lateinit var navController2: MutableBackstackNavigationController<String>
        setContent {
            navController2 = rememberMutableBackstackNavigationController(
                initialBackstackEntries = listOf(
                    BackstackEntry(value = "home", previous = null, id = Uuid.random()),
                ),
            )
            LaunchedEffect(navController2) {
                navController2.bindToBrowserHistory(
                    browserHistory = browserHistory,
                    getBackstackFragment = { if (it.value == "home") "" else it.value },
                )
            }
        }

        waitForIdle()
        assertEquals(id2, navController2.currentEntryId)
        assertEquals("settings", navController2.currentEntry.value)

        // Browser back still returns to the pre-reload "home" entry
        browserHistory.back()
        waitForIdle()
        assertEquals(id1, navController2.currentEntryId)
        assertEquals("home", navController2.currentEntry.value)
    }
}

private class FakeBrowserHistory(initialState: String? = null, initialFragment: String = "") : BrowserHistory {
    data class Entry(val state: String?, val fragment: String)

    val entries = mutableListOf(Entry(state = initialState, fragment = initialFragment))
    var currentIndex = 0
        private set

    private val listeners = mutableListOf<(String?, String) -> Unit>()

    override val currentState: String?
        get() = entries[currentIndex].state

    override val currentFragment: String
        get() = entries[currentIndex].fragment

    override fun pushState(state: String?, fragment: String?) {
        while (entries.size > currentIndex + 1) {
            entries.removeAt(entries.lastIndex)
        }
        entries.add(Entry(state = state, fragment = fragment?.removePrefix("#").orEmpty()))
        currentIndex = entries.lastIndex
    }

    override fun replaceState(state: String?, fragment: String?) {
        entries[currentIndex] = Entry(state = state, fragment = fragment?.removePrefix("#").orEmpty())
    }

    override fun go(delta: Int) {
        val targetIndex = (currentIndex + delta).coerceIn(0, entries.lastIndex)
        if (targetIndex != currentIndex) {
            currentIndex = targetIndex
            val entry = entries[currentIndex]
            listeners.toList().forEach { it(entry.state, entry.fragment) }
        }
    }

    fun back() = go(-1)

    fun forward() = go(1)

    fun navigateToHash(fragment: String) {
        pushState(state = null, fragment = fragment)
        val entry = entries[currentIndex]
        listeners.toList().forEach { it(entry.state, entry.fragment) }
    }

    override fun addPopStateListener(listener: (state: String?, fragment: String) -> Unit): () -> Unit {
        listeners.add(listener)
        return {
            listeners.remove(listener)
        }
    }
}
