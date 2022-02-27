package com.alexvanyo.composelife.navigation

import java.util.UUID

/**
 * A navigation action on [MutableBackstackMap] that pops the backstack until the [entryPredicate] is `true` for some
 * entry, starting at the given [topOfBackstackId].
 *
 * If [inclusive] is true, then the entry that satisfies the [entryPredicate] will also be popped.
 *
 * Note that the action must be valid. If there is no entry that matches the [entryPredicate] an exception will be
 * thrown.
 *
 * This new [topOfBackstackId] is returned.
 */
fun <T> MutableBackstackMap<T>.popUpTo(
    topOfBackstackId: UUID,
    entryPredicate: (BackstackEntry<T>) -> Boolean,
    inclusive: Boolean = false,
): UUID {
    var current = getValue(topOfBackstackId)
    while (isNotEmpty() && !entryPredicate(current)) {
        remove(current.id)
        current = checkNotNull(current.previous) { "Predicate did not correspond to any entry in the backstack!" }
    }
    if (inclusive) {
        current = checkNotNull(current.previous) { "Tried to pop last entry in the backstack!" }
    }
    return current.id
}

/**
 * A navigation action on [MutableBackstackMap] that pops the backstack to the entry with the given [id], starting at
 * the given [topOfBackstackId].
 *
 * If [inclusive] is true, then the entry with the given [id] will also be popped.
 *
 * This new [topOfBackstackId] is returned.
 */
fun <T> MutableBackstackMap<T>.popUpTo(
    topOfBackstackId: UUID,
    id: UUID,
    inclusive: Boolean = false,
): UUID {
    val predicate: (BackstackEntry<T>) -> Boolean = { it.id == id }
    return popUpTo(
        topOfBackstackId = topOfBackstackId,
        entryPredicate = predicate,
        inclusive = inclusive
    )
}

/**
 * A navigation action on [MutableBackstackMap] that pops the backstack until the [predicate] is `true` for some
 * entry's value, starting at the given [topOfBackstackId].
 *
 * If [inclusive] is true, then the entry that satisfies the [predicate] will also be popped.
 *
 * This new [topOfBackstackId] is returned.
 */
@JvmName("popUpToValue")
fun <T> MutableBackstackMap<T>.popUpTo(
    topOfBackstackId: UUID,
    predicate: (T) -> Boolean,
    inclusive: Boolean = false,
): UUID {
    val entryPredicate: (BackstackEntry<T>) -> Boolean = { predicate(it.value) }
    return popUpTo(
        topOfBackstackId = topOfBackstackId,
        entryPredicate = entryPredicate,
        inclusive = inclusive
    )
}

/**
 * A navigation action which adds the destination.
 */
fun <T> MutableBackstackMap<T>.navigate(
    topOfBackstackId: UUID,
    valueFactory: (previous: BackstackEntry<T>) -> T,
    id: UUID = UUID.randomUUID(),
): UUID {
    val previous = getValue(topOfBackstackId)
    val current = BackstackEntry(
        value = valueFactory(previous),
        id = id,
        previous = previous
    )
    put(current.id, current)
    return current.id
}

/**
 * A navigation action which adds the destination.
 */
fun <T> MutableBackstackMap<T>.navigate(
    topOfBackstackId: UUID,
    value: T,
    id: UUID = UUID.randomUUID(),
): UUID = navigate(
    topOfBackstackId = topOfBackstackId,
    valueFactory = { value },
    id = id,
)

/**
 * A navigation action which removes the last destination.
 */
fun <T> MutableBackstackMap<T>.popBackstack(
    topOfBackstackId: UUID,
): UUID {
    val current = getValue(topOfBackstackId)
    val previous = checkNotNull(current.previous) { "Tried to pop last entry in the backstack!" }
    remove(current.id)
    return previous.id
}
