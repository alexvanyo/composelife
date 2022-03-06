package com.alexvanyo.composelife.navigation

import androidx.compose.runtime.Stable
import java.util.UUID

/**
 * A navigation state for destinations of type [T].
 *
 * A navigation state consists of [entryMap], which represents all known entries that may be returned to at some point.
 *
 * The [currentEntryId] acts as a pointer to the navigation entry to currently display.
 */
@Stable
interface NavigationState<T : NavigationEntry> {

    /**
     * A map of all entries, keyed by their [NavigationEntry.id]. This should contain all previous entries that may
     * be returned to at some point.
     */
    val entryMap: Map<UUID, T>

    /**
     * The id of the current entry. This acts a pointer into [entryMap].
     */
    val currentEntryId: UUID
}

/**
 * The current entry of this [NavigationState], based on the [NavigationState.currentEntryId].
 */
val <T : NavigationEntry> NavigationState<T>.currentEntry: T
    get() = entryMap.getValue(currentEntryId)
