package com.livefront.sealedenum.internal.common

/**
 * Returns true if and only if all elements of the [Array] are unique based on the key computed by the [selector].
 *
 * This is logically equivalent to checking if [Array.distinctBy] made the array smaller, but is more efficient
 * due to short-circuiting.
 */
public fun <T, K> Array<T>.areUniqueBy(selector: (T) -> K): Boolean {
    val set = mutableSetOf<K>()
    for (e in this) {
        if (!set.add(selector(e))) {
            return false
        }
    }
    return true
}

/**
 * Returns true if and only if all elements of the [Iterable] are unique based on the key computed by the [selector].
 *
 * This is logically equivalent to checking if [Iterable.distinctBy] made the array smaller, but is more efficient
 * due to short-circuiting.
 */
public fun <T, K> Iterable<T>.areUniqueBy(selector: (T) -> K): Boolean {
    val set = mutableSetOf<K>()
    for (e in this) {
        if (!set.add(selector(e))) {
            return false
        }
    }
    return true
}
