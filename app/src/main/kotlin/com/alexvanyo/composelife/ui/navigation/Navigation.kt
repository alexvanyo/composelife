package com.alexvanyo.composelife.ui.navigation

import java.util.UUID

/**
 * A navigation action on [MutableBackstack] that pops the backstack until the [entryPredicate] is `true` for some
 * entry.
 *
 * If [inclusive] is true, then the entry that satisfies the [entryPredicate] will also be popped.
 *
 * Note that the action must be valid. If there is no entry that matches the [entryPredicate] an exception will be
 * thrown.
 */
fun <T> MutableBackstack<T>.popUpTo(
    entryPredicate: (BackstackEntry<T>) -> Boolean,
    inclusive: Boolean = false,
) {
    while (isNotEmpty() && !entryPredicate(last())) {
        removeLast()
    }
    check(isNotEmpty()) { "Predicate did not correspond to any entry in the backstack!" }
    if (inclusive) {
        removeLast()
    }
}

/**
 * A navigation action on [MutableBackstack] that pops the backstack to the entry with the given [id].
 *
 * If [inclusive] is true, then the entry with the given [id] will also be popped.
 */
fun <T> MutableBackstack<T>.popUpTo(
    id: UUID,
    inclusive: Boolean = false,
) {
    val predicate: (BackstackEntry<T>) -> Boolean = { it.id == id }
    popUpTo(
        entryPredicate = predicate,
        inclusive = inclusive
    )
}

/**
 * A navigation action on [MutableBackstack] that pops the backstack until the [predicate] is `true` for some
 * entry's value.
 *
 * If [inclusive] is true, then the entry that satisfies the [predicate] will also be popped.
 */
@JvmName("popUpToValue")
fun <T> MutableBackstack<T>.popUpTo(
    predicate: (T) -> Boolean,
    inclusive: Boolean = false,
) {
    val entryPredicate: (BackstackEntry<T>) -> Boolean = { predicate(it.value) }
    popUpTo(
        entryPredicate = entryPredicate,
        inclusive = inclusive
    )
}

/**
 * A navigation action which adds the destination.
 */
fun <T> MutableBackstack<T>.navigate(
    value: T,
    id: UUID = UUID.randomUUID(),
) {
    add(BackstackEntry(value, id))
}

/**
 * A navigation action which removes the last destination.
 */
fun <T> MutableBackstack<T>.popBackstack() {
    removeLast()
}
