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

@file:OptIn(ExperimentalWasmJsInterop::class)
@file:Suppress("MatchingDeclarationName")

package com.alexvanyo.composelife.navigation

import androidx.compose.runtime.Composable
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.getValue
import androidx.compose.runtime.rememberUpdatedState
import kotlinx.browser.window
import kotlinx.serialization.KSerializer
import kotlinx.serialization.serializer
import org.w3c.dom.PopStateEvent
import org.w3c.dom.Window
import org.w3c.dom.events.Event

/**
 * A [BrowserHistory] implementation backed by the browser's [Window.history] and [Window.location].
 */
class WindowBrowserHistory(private val window: Window = kotlinx.browser.window) : BrowserHistory {
    override val currentState: String?
        get() = (window.history.state as? JsString)?.toString()

    override val currentFragment: String
        get() = window.location.hash.removePrefix("#")

    override fun pushState(state: String?, fragment: String?) {
        val url = buildUrl(fragment)
        runCatching {
            window.history.pushState(state?.toJsString(), "", url)
        }.getOrElse {
            if (state != null) {
                runCatching {
                    window.history.pushState(null, "", url)
                }.getOrDefault(Unit)
            }
        }
    }

    override fun replaceState(state: String?, fragment: String?) {
        val url = buildUrl(fragment)
        runCatching {
            window.history.replaceState(state?.toJsString(), "", url)
        }.getOrElse {
            if (state != null) {
                runCatching {
                    window.history.replaceState(null, "", url)
                }.getOrDefault(Unit)
            }
        }
    }

    override fun go(delta: Int) {
        window.history.go(delta)
    }

    override fun addPopStateListener(listener: (state: String?, fragment: String) -> Unit): () -> Unit {
        val eventListener: (Event) -> Unit = { event ->
            val popStateEvent = event as? PopStateEvent
            val state = (popStateEvent?.state as? JsString)?.toString()
            listener(state, currentFragment)
        }
        window.addEventListener("popstate", eventListener)
        return {
            window.removeEventListener("popstate", eventListener)
        }
    }

    private fun buildUrl(fragment: String?): String {
        val baseUrl = window.location.pathname + window.location.search
        val normalizedFragment = fragment?.removePrefix("#").orEmpty()
        return if (normalizedFragment.isEmpty()) baseUrl else "$baseUrl#$normalizedFragment"
    }
}

/**
 * Synchronizes this [MutableBackstackNavigationController] with the browser's [window] history.
 */
suspend inline fun <reified T> MutableBackstackNavigationController<T>.bindToBrowserNavigation(
    window: Window = kotlinx.browser.window,
    serializer: KSerializer<T> = serializer(),
    noinline getBackstackFragment: (BackstackEntry<T>) -> String? = { null },
    noinline parseFragment: (String) -> List<BackstackEntry<T>>? = { null },
) = bindToBrowserHistory(
    browserHistory = WindowBrowserHistory(window),
    serializer = serializer,
    getBackstackFragment = getBackstackFragment,
    parseFragment = parseFragment,
)

/**
 * Synchronizes this [MutableBackstackNavigationController] with the browser's [window] history.
 */
suspend fun <T> MutableBackstackNavigationController<T>.bindToBrowserNavigation(
    backstackMapSerializer: KSerializer<MutableBackstackMap<T>>,
    window: Window = kotlinx.browser.window,
    getBackstackFragment: (BackstackEntry<T>) -> String? = { null },
    parseFragment: (String) -> List<BackstackEntry<T>>? = { null },
) = bindToBrowserHistory(
    browserHistory = WindowBrowserHistory(window),
    backstackMapSerializer = backstackMapSerializer,
    getBackstackFragment = getBackstackFragment,
    parseFragment = parseFragment,
)

@Composable
actual fun <T> MutableBackstackNavigationController<T>.BindToBrowserNavigation(
    backstackMapSerializer: KSerializer<MutableBackstackMap<T>>,
    getBackstackFragment: (BackstackEntry<T>) -> String?,
    parseFragment: (String) -> List<BackstackEntry<T>>?,
) {
    val currentGetBackstackFragment by rememberUpdatedState(getBackstackFragment)
    val currentParseFragment by rememberUpdatedState(parseFragment)

    LaunchedEffect(this, backstackMapSerializer) {
        bindToBrowserNavigation(
            backstackMapSerializer = backstackMapSerializer,
            window = window,
            getBackstackFragment = { currentGetBackstackFragment(it) },
            parseFragment = { currentParseFragment(it) },
        )
    }
}
