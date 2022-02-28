package com.alexvanyo.composelife.navigation

import java.util.UUID

/**
 * A navigation state for destinations of type [T].
 *
 * A navigation state consists of [entryMap], which contains a directed acyclic graph of backstack entries.
 *
 * The [currentEntryId] acts as a pointer to the backstack entry to currently display.
 */
interface NavigationState<T : NavigationEntry> {
    val entryMap: Map<UUID, T>

    val currentEntryId: UUID
}

val <T : NavigationEntry> NavigationState<T>.currentEntry: T
    get() = entryMap.getValue(currentEntryId)
