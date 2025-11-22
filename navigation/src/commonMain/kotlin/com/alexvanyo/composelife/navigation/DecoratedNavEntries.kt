package com.alexvanyo.composelife.navigation

import androidx.compose.runtime.Composable
import androidx.compose.runtime.remember
import androidx.navigation3.runtime.NavEntry
import androidx.navigation3.runtime.NavEntryDecorator
import androidx.navigation3.runtime.rememberDecoratedNavEntries
import androidx.navigation3.runtime.rememberSaveableStateHolderNavEntryDecorator
import kotlin.uuid.Uuid

@Composable
fun <T, S : NavigationState<BackstackEntry<T>>> rememberDecoratedNavEntries(
    navigationState: S,
    entryDecorators: List<NavEntryDecorator<BackstackEntry<T>>> =
        listOf(
            rememberSaveableStateHolderNavEntryDecorator(),
            rememberRetainedValuesStoreNavEntryDecorator(),
        ),
    pane: @Composable (BackstackEntry<T>) -> Unit,
): List<NavEntry<BackstackEntry<T>>> {
    // Remember decorated nav entries for all navigation entries in the navigation state
    val entryList = rememberDecoratedNavEntries(
        entries = navigationState.entryMap.values.map { navigationEntry ->
            NavEntry(
                key = navigationEntry,
                contentKey = navigationEntry.id,
                content = { pane(navigationEntry) },
            )
        },
        entryDecorators = entryDecorators,
    )

    // Return only the entries that are in the previous chain
    return remember(entryList) {
        val entryMap = entryList.associateBy { it.contentKey as Uuid }
        navigationState.currentEntry.toList().reversed().map {
            entryMap.getValue(it.id)
        }
    }
}
