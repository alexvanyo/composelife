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

import kotlin.jvm.JvmName
import kotlin.uuid.Uuid

private fun <T> MutableBackstackMap<T>.toBackstackModel(currentEntryId: Uuid): BackstackModel<T> = BackstackModel(
    entries = values.map { it as Any? }.toTypedArray(),
    currentEntryId = currentEntryId,
)

@Suppress("UNCHECKED_CAST")
private fun <T> MutableBackstackMap<T>.applyBackstackModel(model: BackstackModel<T>): Uuid {
    val newEntries = model.entries.associate {
        val entry = it as BackstackEntry<T>
        entry.id to entry
    }
    keys.retainAll(newEntries.keys)
    for ((id, entry) in newEntries) {
        if (this[id] !== entry) {
            this[id] = entry
        }
    }
    return model.currentEntryId
}

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
@Suppress("UNCHECKED_CAST")
fun <T> MutableBackstackMap<T>.popUpTo(
    currentEntryId: Uuid,
    entryPredicate: (BackstackEntry<T>) -> Boolean,
    inclusive: Boolean = false,
): Uuid = applyBackstackModel(
    checkNotNull(
        f_Navigation_popUpTo(
            toBackstackModel(currentEntryId),
            { entryPredicate(it as BackstackEntry<T>) },
            inclusive,
        ),
    ) {
        "Predicate did not correspond to any entry in the backstack, or tried to pop last entry in the backstack!"
    },
)

/**
 * A navigation action on [MutableBackstackMap] that pops the backstack to the entry with the given [id], starting at
 * the given [currentEntryId].
 *
 * If [inclusive] is true, then the entry with the given [id] will also be popped.
 *
 * This new [currentEntryId] is returned.
 */
fun <T> MutableBackstackMap<T>.popUpTo(currentEntryId: Uuid, id: Uuid, inclusive: Boolean = false): Uuid =
    applyBackstackModel(
        checkNotNull(
            f_Navigation_popUpToId(
                toBackstackModel(currentEntryId),
                id,
                inclusive,
            ),
        ) {
            "Id did not correspond to any entry in the backstack, or tried to pop last entry in the backstack!"
        },
    )

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
): Uuid = applyBackstackModel(
    checkNotNull(
        f_Navigation_popUpToValue(
            toBackstackModel(currentEntryId),
            predicate,
            inclusive,
        ),
    ) {
        "Predicate did not correspond to any entry in the backstack, or tried to pop last entry in the backstack!"
    },
)

/**
 * A navigation action which adds the destination.
 */
@Suppress("UNCHECKED_CAST")
fun <T> MutableBackstackMap<T>.navigate(
    currentEntryId: Uuid,
    valueFactory: (previous: BackstackEntry<T>) -> T,
    id: Uuid = Uuid.random(),
): Uuid = applyBackstackModel(
    checkNotNull(
        f_Navigation_navigateWithFactory(
            toBackstackModel(currentEntryId),
            { valueFactory(it as BackstackEntry<T>) },
            id,
        ),
    ) {
        "Current entry id did not correspond to any entry in the backstack!"
    },
)

/**
 * A navigation action which adds the destination.
 */
fun <T> MutableBackstackMap<T>.navigate(currentEntryId: Uuid, value: T, id: Uuid = Uuid.random()): Uuid =
    applyBackstackModel(
        checkNotNull(
            f_Navigation_navigate(
                toBackstackModel(currentEntryId),
                value,
                id,
            ),
        ) {
            "Current entry id did not correspond to any entry in the backstack!"
        },
    )

/**
 * A navigation action which removes the last destination.
 */
fun <T> MutableBackstackMap<T>.popBackstack(currentEntryId: Uuid): Uuid = applyBackstackModel(
    checkNotNull(
        f_Navigation_popBackstack(
            toBackstackModel(currentEntryId),
        ),
    ) {
        "Tried to pop last entry in the backstack!"
    },
)
