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

import androidx.compose.runtime.Composable
import androidx.compose.runtime.snapshotFlow
import androidx.compose.runtime.snapshots.Snapshot
import kotlinx.coroutines.CompletableDeferred
import kotlinx.coroutines.withTimeoutOrNull
import kotlinx.serialization.KSerializer
import kotlinx.serialization.Serializable
import kotlinx.serialization.json.Json
import kotlinx.serialization.json.JsonElement
import kotlinx.serialization.serializer
import kotlin.jvm.JvmName
import kotlin.uuid.Uuid

/**
 * An abstraction over the browser history and location APIs for synchronizing navigation state with browser
 * back and forward navigation.
 */
interface BrowserHistory {
    /**
     * The serialized state string of the current browser history entry, if any.
     */
    val currentState: String?

    /**
     * The current URL fragment (without the leading `#`), or empty string if none.
     */
    val currentFragment: String

    /**
     * Pushes a new entry onto the browser's session history stack with the given [state] and optional [fragment]
     * (without a leading `#`).
     */
    fun pushState(state: String?, fragment: String?)

    /**
     * Replaces the current entry in the browser's session history stack with the given [state] and optional
     * [fragment] (without a leading `#`).
     */
    fun replaceState(state: String?, fragment: String?)

    /**
     * Moves the browser's session history by [delta] entries (negative for back, positive for forward).
     */
    fun go(delta: Int)

    /**
     * Registers a [listener] to be invoked when a browser `popstate` event occurs, returning a handle that
     * removes the listener when invoked.
     */
    fun addPopStateListener(listener: (state: String?, fragment: String) -> Unit): () -> Unit
}

/**
 * Synchronizes this [MutableBackstackNavigationController] with the platform's browser navigation history
 * (back and forward buttons and URL fragments).
 *
 * On non-web platforms, this is a no-op.
 */
@Composable
expect fun <T> MutableBackstackNavigationController<T>.BindToBrowserNavigation(
    backstackMapSerializer: KSerializer<MutableBackstackMap<T>>,
    getBackstackFragment: (BackstackEntry<T>) -> String? = { null },
    parseFragment: (String) -> List<BackstackEntry<T>>? = { null },
)

/**
 * Synchronizes this [MutableBackstackNavigationController] with the given [browserHistory].
 */
suspend inline fun <reified T> MutableBackstackNavigationController<T>.bindToBrowserHistory(
    browserHistory: BrowserHistory,
    serializer: KSerializer<T> = serializer(),
    noinline getBackstackFragment: (BackstackEntry<T>) -> String? = { null },
    noinline parseFragment: (String) -> List<BackstackEntry<T>>? = { null },
) = bindToBrowserHistory(
    browserHistory = browserHistory,
    backstackMapSerializer = BackstackMapSerializer(
        convertToSurrogate = ::ValueAsSurrogate,
        backstackValueSurrogateSerializer = ValueAsSurrogate.serializer(serializer),
    ),
    getBackstackFragment = getBackstackFragment,
    parseFragment = parseFragment,
)

/**
 * Synchronizes this [MutableBackstackNavigationController] with the given [browserHistory].
 */
@JvmName("bindToBrowserHistoryWithBackstackMapSerializer")
@Suppress("LongMethod", "CyclomaticComplexMethod")
suspend fun <T> MutableBackstackNavigationController<T>.bindToBrowserHistory(
    browserHistory: BrowserHistory,
    backstackMapSerializer: KSerializer<MutableBackstackMap<T>>,
    getBackstackFragment: (BackstackEntry<T>) -> String? = { null },
    parseFragment: (String) -> List<BackstackEntry<T>>? = { null },
) {
    var sessionId = Uuid.random()
    val sessionHistory = mutableMapOf<Int, List<Uuid>>()
    var currentHistoryIndex: Int
    var lastSyncedSnapshot: BackstackSnapshot
    var pendingGoTargetIndex: Int? = null
    var pendingGoDeferred: CompletableDeferred<Boolean>? = null

    fun createSnapshot(current: BackstackEntry<T>): BackstackSnapshot {
        val chain = current.toList().reversed()
        val activeMap = mutableMapOf<Uuid, BackstackEntry<T>>().apply {
            chain.forEach { put(it.id, it) }
        }
        return BackstackSnapshot(
            entryIds = chain.map(BackstackEntry<T>::id),
            currentEntryId = current.id,
            backstackMapElement = BrowserHistoryJson.encodeToJsonElement(backstackMapSerializer, activeMap),
            fragment = getBackstackFragment(current),
        )
    }

    fun captureSnapshot(): BackstackSnapshot = createSnapshot(currentEntry)

    fun encodeHistoryState(index: Int, snapshot: BackstackSnapshot): String? = runCatching {
        BrowserHistoryJson.encodeToString(
            SerializedBrowserHistoryState.serializer(),
            SerializedBrowserHistoryState(
                sessionId = sessionId,
                index = index,
                currentEntryId = snapshot.currentEntryId,
                backstackMap = snapshot.backstackMapElement,
                sessionHistory = sessionHistory.filterKeys { it <= index },
            ),
        )
    }.getOrNull()

    fun decodeHistoryState(rawState: String?): Pair<SerializedBrowserHistoryState, MutableBackstackMap<T>>? =
        rawState?.let { raw ->
            runCatching {
                BrowserHistoryJson.decodeFromString(SerializedBrowserHistoryState.serializer(), raw)
            }.getOrNull()
        }?.let { decodedState ->
            runCatching {
                BrowserHistoryJson.decodeFromJsonElement(backstackMapSerializer, decodedState.backstackMap)
            }.getOrNull()?.takeIf { decodedState.currentEntryId in it }?.let { restoredMap ->
                decodedState to restoredMap
            }
        }

    fun applyBackstack(newEntries: Map<Uuid, BackstackEntry<T>>, newCurrentEntryId: Uuid) {
        Snapshot.withMutableSnapshot {
            entryMap.clear()
            entryMap.putAll(newEntries)
            currentEntryId = newCurrentEntryId
        }
    }

    // Initialize from existing browser state (e.g. page refresh) or URL fragment (deep link).
    val initialRestored = decodeHistoryState(browserHistory.currentState)
    if (initialRestored != null) {
        val (decodedState, restoredMap) = initialRestored
        sessionId = decodedState.sessionId
        sessionHistory.putAll(decodedState.sessionHistory)
        applyBackstack(restoredMap, decodedState.currentEntryId)
        currentHistoryIndex = decodedState.index
    } else {
        val initialFragment = browserHistory.currentFragment
        if (initialFragment.isNotEmpty()) {
            val parsedEntries = parseFragment(initialFragment)
            if (!parsedEntries.isNullOrEmpty()) {
                val parsedCurrent = parsedEntries.last()
                val activeParsedMap = parsedCurrent.toList().reversed().associateBy(BackstackEntry<T>::id)
                applyBackstack(
                    newEntries = activeParsedMap,
                    newCurrentEntryId = parsedCurrent.id,
                )
            }
        }
        currentHistoryIndex = 0
    }

    lastSyncedSnapshot = captureSnapshot()
    sessionHistory[currentHistoryIndex] = lastSyncedSnapshot.entryIds
    browserHistory.replaceState(
        state = encodeHistoryState(currentHistoryIndex, lastSyncedSnapshot),
        fragment = lastSyncedSnapshot.fragment,
    )

    val removeListener = browserHistory.addPopStateListener { rawState, fragment ->
        val decoded = decodeHistoryState(rawState)
        if (decoded != null) {
            val (decodedState, restoredMap) = decoded
            if (decodedState.sessionId == sessionId && decodedState.index == pendingGoTargetIndex) {
                pendingGoTargetIndex = null
                pendingGoDeferred?.complete(true)
                pendingGoDeferred = null
                return@addPopStateListener
            }

            pendingGoTargetIndex = null
            pendingGoDeferred?.complete(false)
            pendingGoDeferred = null

            val restoredCurrent = restoredMap.getValue(decodedState.currentEntryId)
            val restoredChain = restoredCurrent.toList().reversed()
            val restoredSnapshot = BackstackSnapshot(
                entryIds = restoredChain.map(BackstackEntry<T>::id),
                currentEntryId = decodedState.currentEntryId,
                backstackMapElement = decodedState.backstackMap,
                fragment = getBackstackFragment(restoredCurrent),
            )
            currentHistoryIndex = decodedState.index
            lastSyncedSnapshot = restoredSnapshot
            sessionHistory.putAll(decodedState.sessionHistory)
            sessionHistory[currentHistoryIndex] = restoredSnapshot.entryIds
            applyBackstack(restoredMap, decodedState.currentEntryId)
        } else {
            pendingGoTargetIndex = null
            pendingGoDeferred?.complete(false)
            pendingGoDeferred = null

            val parsedEntries = parseFragment(fragment)
            if (!parsedEntries.isNullOrEmpty()) {
                val parsedCurrent = parsedEntries.last()
                val activeParsedMap = parsedCurrent.toList().reversed().associateBy(BackstackEntry<T>::id)
                val newSnapshot = createSnapshot(parsedCurrent)
                currentHistoryIndex += 1
                sessionHistory.keys.removeAll { it >= currentHistoryIndex }
                lastSyncedSnapshot = newSnapshot
                sessionHistory[currentHistoryIndex] = newSnapshot.entryIds
                browserHistory.replaceState(
                    state = encodeHistoryState(currentHistoryIndex, newSnapshot),
                    fragment = newSnapshot.fragment,
                )
                applyBackstack(
                    newEntries = activeParsedMap,
                    newCurrentEntryId = parsedCurrent.id,
                )
            } else {
                // Unknown or external history entry: reset relative history tracking so subsequent
                // in-app navigation does not compute an invalid delta.
                currentHistoryIndex += 1
                sessionHistory.clear()
                sessionHistory[currentHistoryIndex] = lastSyncedSnapshot.entryIds
                browserHistory.replaceState(
                    state = encodeHistoryState(currentHistoryIndex, lastSyncedSnapshot),
                    fragment = lastSyncedSnapshot.fragment,
                )
            }
        }
    }

    try {
        snapshotFlow { captureSnapshot() }.collect { newSnapshot ->
            if (newSnapshot == lastSyncedSnapshot) return@collect

            if (newSnapshot.entryIds == lastSyncedSnapshot.entryIds) {
                lastSyncedSnapshot = newSnapshot
                browserHistory.replaceState(
                    state = encodeHistoryState(currentHistoryIndex, newSnapshot),
                    fragment = newSnapshot.fragment,
                )
                return@collect
            }

            val previousMatchIndex = sessionHistory
                .filterKeys { it < currentHistoryIndex }
                .entries
                .filter { it.value == newSnapshot.entryIds }
                .maxOfOrNull { it.key }

            if (previousMatchIndex != null) {
                val delta = previousMatchIndex - currentHistoryIndex
                currentHistoryIndex = previousMatchIndex
                lastSyncedSnapshot = newSnapshot
                val deferred = CompletableDeferred<Boolean>()
                pendingGoTargetIndex = previousMatchIndex
                pendingGoDeferred = deferred
                browserHistory.go(delta)
                val completedExpectedPopState = withTimeoutOrNull(POPSTATE_TIMEOUT_MS) {
                    deferred.await()
                } == true
                pendingGoTargetIndex = null
                pendingGoDeferred = null
                if (completedExpectedPopState && lastSyncedSnapshot == newSnapshot) {
                    browserHistory.replaceState(
                        state = encodeHistoryState(currentHistoryIndex, newSnapshot),
                        fragment = newSnapshot.fragment,
                    )
                }
            } else if (
                newSnapshot.entryIds.size < lastSyncedSnapshot.entryIds.size &&
                lastSyncedSnapshot.entryIds.subList(0, newSnapshot.entryIds.size) == newSnapshot.entryIds
            ) {
                lastSyncedSnapshot = newSnapshot
                sessionHistory[currentHistoryIndex] = newSnapshot.entryIds
                browserHistory.replaceState(
                    state = encodeHistoryState(currentHistoryIndex, newSnapshot),
                    fragment = newSnapshot.fragment,
                )
            } else {
                currentHistoryIndex += 1
                sessionHistory.keys.removeAll { it >= currentHistoryIndex }
                sessionHistory[currentHistoryIndex] = newSnapshot.entryIds
                lastSyncedSnapshot = newSnapshot
                browserHistory.pushState(
                    state = encodeHistoryState(currentHistoryIndex, newSnapshot),
                    fragment = newSnapshot.fragment,
                )
            }
        }
    } finally {
        removeListener()
    }
}

private data class BackstackSnapshot(
    val entryIds: List<Uuid>,
    val currentEntryId: Uuid,
    val backstackMapElement: JsonElement,
    val fragment: String?,
)

@Serializable
private data class SerializedBrowserHistoryState(
    val sessionId: Uuid,
    val index: Int,
    val currentEntryId: Uuid,
    val backstackMap: JsonElement,
    val sessionHistory: Map<Int, List<Uuid>> = emptyMap(),
)

private val BrowserHistoryJson = Json {
    ignoreUnknownKeys = true
}

private const val POPSTATE_TIMEOUT_MS = 500L
