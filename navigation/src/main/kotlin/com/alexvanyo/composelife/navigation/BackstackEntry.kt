package com.alexvanyo.composelife.navigation

import androidx.compose.runtime.Stable
import java.util.UUID

/**
 * An entry in the backstack.
 *
 * This is a stable pair between an unique [id], and an arbitrary [value] of type [T].
 *
 * [BackstackEntry] is [Stable], meaning that [value] must also be [Stable] as anything observing backstack entries
 * will want to observe if any relevant state changes.
 */
@Stable
class BackstackEntry<T>(
    val value: T,
    val previous: BackstackEntry<T>?,
    override val id: UUID = UUID.randomUUID(),
) : NavigationEntry, Iterable<BackstackEntry<T>> {
    override fun iterator(): Iterator<BackstackEntry<T>> = iterator {
        var current: BackstackEntry<T>? = this@BackstackEntry
        while (current != null) {
            yield(current)
            current = current.previous
        }
    }
}
