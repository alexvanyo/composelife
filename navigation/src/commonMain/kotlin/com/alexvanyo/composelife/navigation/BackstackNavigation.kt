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

import com.benasher44.uuid.Uuid
import com.benasher44.uuid.uuid4
import kotlin.jvm.JvmName

/**
 * A navigation action on [MutableBackstackMap] that pops the backstack until the [entryPredicate] is `true` for some
 * entry, starting at the given [currentEntryId].
 *
 * If [inclusive] is true, then the entry that satisfies the [entryPredicate] will also be popped.
 *
 * Note that the action must be valid. If there is no entry that matches the [entryPredicate] an exception will be
 * thrown.
 *
 * This new [currentEntryId] is returned.
 */
fun <T> MutableBackstackMap<T>.popUpTo(
    currentEntryId: Uuid,
    entryPredicate: (BackstackEntry<T>) -> Boolean,
    inclusive: Boolean = false,
): Uuid {
    var current = getValue(currentEntryId)
    while (!entryPredicate(current)) {
        remove(current.id)
        current = checkNotNull(current.previous) { "Predicate did not correspond to any entry in the backstack!" }
    }
    if (inclusive) {
        remove(current.id)
        current = checkNotNull(current.previous) { "Tried to pop last entry in the backstack!" }
    }
    return current.id
}

/**
 * A navigation action on [MutableBackstackMap] that pops the backstack to the entry with the given [id], starting at
 * the given [currentEntryId].
 *
 * If [inclusive] is true, then the entry with the given [id] will also be popped.
 *
 * This new [currentEntryId] is returned.
 */
fun <T> MutableBackstackMap<T>.popUpTo(
    currentEntryId: Uuid,
    id: Uuid,
    inclusive: Boolean = false,
): Uuid {
    val predicate: (BackstackEntry<T>) -> Boolean = { it.id == id }
    return popUpTo(
        currentEntryId = currentEntryId,
        entryPredicate = predicate,
        inclusive = inclusive,
    )
}

/**
 * A navigation action on [MutableBackstackMap] that pops the backstack until the [predicate] is `true` for some
 * entry's value, starting at the given [currentEntryId].
 *
 * If [inclusive] is true, then the entry that satisfies the [predicate] will also be popped.
 *
 * This new [currentEntryId] is returned.
 */
@JvmName("popUpToValue")
fun <T> MutableBackstackMap<T>.popUpTo(
    currentEntryId: Uuid,
    predicate: (T) -> Boolean,
    inclusive: Boolean = false,
): Uuid {
    val entryPredicate: (BackstackEntry<T>) -> Boolean = { predicate(it.value) }
    return popUpTo(
        currentEntryId = currentEntryId,
        entryPredicate = entryPredicate,
        inclusive = inclusive,
    )
}

/**
 * A navigation action which adds the destination.
 */
fun <T> MutableBackstackMap<T>.navigate(
    currentEntryId: Uuid,
    valueFactory: (previous: BackstackEntry<T>) -> T,
    id: Uuid = uuid4(),
): Uuid {
    val previous = getValue(currentEntryId)
    val current = BackstackEntry(
        value = valueFactory(previous),
        id = id,
        previous = previous,
    )
    put(current.id, current)
    return current.id
}

/**
 * A navigation action which adds the destination.
 */
fun <T> MutableBackstackMap<T>.navigate(
    currentEntryId: Uuid,
    value: T,
    id: Uuid = uuid4(),
): Uuid = navigate(
    currentEntryId = currentEntryId,
    valueFactory = { value },
    id = id,
)

/**
 * A navigation action which removes the last destination.
 */
fun <T> MutableBackstackMap<T>.popBackstack(
    currentEntryId: Uuid,
): Uuid {
    val current = getValue(currentEntryId)
    val previous = checkNotNull(current.previous) { "Tried to pop last entry in the backstack!" }
    remove(current.id)
    return previous.id
}
