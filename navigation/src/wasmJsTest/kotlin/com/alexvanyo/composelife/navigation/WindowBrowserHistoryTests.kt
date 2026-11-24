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
import com.alexvanyo.composelife.test.runComposeUiTest
import kotlinx.browser.window
import kotlinx.coroutines.suspendCancellableCoroutine
import org.w3c.dom.events.Event
import kotlin.coroutines.resume
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.uuid.Uuid

@OptIn(ExperimentalTestApi::class, ExperimentalWasmJsInterop::class)
class WindowBrowserHistoryTests {

    @Test
    fun bind_to_browser_navigation_updates_window_hash_and_syncs_back_and_forward() = runComposeUiTest {
        val id1 = Uuid.random()
        val id2 = Uuid.random()
        lateinit var navController: MutableBackstackNavigationController<String>

        // Reset hash and state before test
        window.history.replaceState(null, "", window.location.pathname + window.location.search)

        setContent {
            navController = rememberMutableBackstackNavigationController(
                initialBackstackEntries = listOf(
                    BackstackEntry(value = "home", previous = null, id = id1),
                ),
            )
            LaunchedEffect(navController) {
                navController.bindToBrowserNavigation(
                    window = window,
                    getBackstackFragment = { if (it.value == "home") "" else it.value },
                )
            }
        }

        waitForIdle()
        assertEquals("", window.location.hash)

        navController.navigate(value = "settings", id = id2)
        waitForIdle()
        assertEquals("#settings", window.location.hash)

        awaitPopState {
            window.history.back()
        }
        waitForIdle()
        assertEquals(id1, navController.currentEntryId)
        assertEquals("home", navController.currentEntry.value)
        assertEquals("", window.location.hash)

        awaitPopState {
            window.history.forward()
        }
        waitForIdle()
        assertEquals(id2, navController.currentEntryId)
        assertEquals("settings", navController.currentEntry.value)
        assertEquals("#settings", window.location.hash)
    }

    private suspend fun awaitPopState(action: () -> Unit) = suspendCancellableCoroutine { continuation ->
        lateinit var listener: (Event) -> Unit
        listener = {
            window.removeEventListener("popstate", listener)
            if (continuation.isActive) {
                continuation.resume(Unit)
            }
        }
        window.addEventListener("popstate", listener)
        continuation.invokeOnCancellation {
            window.removeEventListener("popstate", listener)
        }
        action()
    }
}
