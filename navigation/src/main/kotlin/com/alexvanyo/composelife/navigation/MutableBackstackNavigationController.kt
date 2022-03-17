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

import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.saveable.Saver
import androidx.compose.runtime.saveable.autoSaver
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.setValue
import java.util.UUID

/**
 * A mutable [BackstackState] that can be modified by changing the [entryMap] and the [currentEntryId].
 *
 * A canonical [MutableBackstackNavigationController] representing a simple backstack can be created with
 * [rememberMutableBackstackNavigationController].
 */
interface MutableBackstackNavigationController<T> : BackstackState<T> {
    override val entryMap: MutableBackstackMap<T>

    override var currentEntryId: UUID
}

/**
 * `true` if [popBackstack] is possible.
 */
val <T> MutableBackstackNavigationController<T>.canNavigateBack
    get() = currentEntry.previous != null

@Composable
fun <T> rememberMutableBackstackNavigationController(
    initialBackstackEntries: List<BackstackEntry<T>>,
    saver: Saver<T, Any> = autoSaver(),
): MutableBackstackNavigationController<T> =
    rememberMutableBackstackNavigationController(
        initialBackstackEntries = initialBackstackEntries,
        backstackValueSaverFactory = { saver }
    )

@Composable
fun <T> rememberMutableBackstackNavigationController(
    initialBackstackEntries: List<BackstackEntry<T>>,
    backstackValueSaverFactory: BackstackValueSaverFactory<T>,
): MutableBackstackNavigationController<T> {
    require(initialBackstackEntries.isNotEmpty())

    val backstackMap = rememberBackstackMap(
        initialBackstackEntries = initialBackstackEntries,
        backstackValueSaverFactory = backstackValueSaverFactory
    )

    var currentBackstackEntryId by rememberSaveable(
        saver = Saver(
            save = { it.value.toString() },
            restore = { mutableStateOf(UUID.fromString(it)) }
        )
    ) {
        mutableStateOf(initialBackstackEntries.last().id)
    }

    return remember {
        object : MutableBackstackNavigationController<T> {
            override val entryMap: MutableBackstackMap<T> get() = backstackMap
            override var currentEntryId: UUID
                get() = currentBackstackEntryId
                set(value) {
                    currentBackstackEntryId = value
                }
        }
    }
}

/**
 * Guards running the block against whether the actor (that is, the one running this function) is expected.
 *
 * If [actorEntryId] is not `null,` then [block] will only be run if the
 * [MutableBackstackNavigationController.currentEntryId] at the time of invocation matches the
 * [actorEntryId].
 * If [actorEntryId] is `null`, then [block] will always be run.
 *
 * This function returns `true` if and only if the [block] was run.
 */
fun <T> MutableBackstackNavigationController<T>.withExpectedActor(
    actorEntryId: UUID?,
    block: MutableBackstackNavigationController<T>.(currentEntry: BackstackEntry<T>) -> Unit
): Boolean =
    if (actorEntryId == null || actorEntryId == currentEntry.id) {
        block(currentEntry)
        true
    } else {
        false
    }

/**
 * A navigation action that pops the backstack until the [entryPredicate] is `true` for some  entry, starting at the
 * current entry.
 *
 * If [inclusive] is true, then the entry that satisfies the [entryPredicate] will also be popped.
 *
 * Note that the action must be valid. If there is no entry that matches the [entryPredicate] an exception will be
 * thrown.
 */
fun <T> MutableBackstackNavigationController<T>.popUpTo(
    entryPredicate: (BackstackEntry<T>) -> Boolean,
    inclusive: Boolean = false,
) {
    currentEntryId = entryMap.popUpTo(
        currentEntryId = currentEntryId,
        entryPredicate = entryPredicate,
        inclusive = inclusive
    )
}

/**
 * A navigation action that pops the backstack to the entry with the given [id], starting at the current entry.
 *
 * If [inclusive] is true, then the entry with the given [id] will also be popped.
 */
fun <T> MutableBackstackNavigationController<T>.popUpTo(
    id: UUID,
    inclusive: Boolean = false,
) {
    val predicate: (BackstackEntry<T>) -> Boolean = { it.id == id }
    popUpTo(
        entryPredicate = predicate,
        inclusive = inclusive,
    )
}

/**
 * A navigation action that pops the backstack until the [predicate] is `true` for some entry's value, starting at the
 * current entry.
 *
 * If [inclusive] is true, then the entry that satisfies the [predicate] will also be popped.
 */
@JvmName("popUpToValue")
fun <T> MutableBackstackNavigationController<T>.popUpTo(
    predicate: (T) -> Boolean,
    inclusive: Boolean = false,
) {
    val entryPredicate: (BackstackEntry<T>) -> Boolean = { predicate(it.value) }
    popUpTo(
        entryPredicate = entryPredicate,
        inclusive = inclusive,
    )
}

/**
 * A navigation action which adds the destination.
 */
fun <T> MutableBackstackNavigationController<T>.navigate(
    valueFactory: (previous: BackstackEntry<T>) -> T,
    id: UUID = UUID.randomUUID(),
) {
    currentEntryId = entryMap.navigate(
        currentEntryId = currentEntryId,
        valueFactory = valueFactory,
        id = id
    )
}

/**
 * A navigation action which adds the destination.
 */
fun <T> MutableBackstackNavigationController<T>.navigate(
    value: T,
    id: UUID = UUID.randomUUID(),
) = navigate(
    valueFactory = { value },
    id = id,
)

/**
 * A navigation action which removes the last destination.
 */
fun <T> MutableBackstackNavigationController<T>.popBackstack() {
    currentEntryId = entryMap.popBackstack(
        currentEntryId = currentEntryId,
    )
}
