/*
 * Copyright 2025 The Android Open Source Project
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
                metadata = mapOf(NavKeyMetadataKey to navigationEntry),
                content = { pane(it) },
            )
        },
        entryDecorators = entryDecorators,
    )

    // Return only the entries that are in the previous chain
    val history = navigationState.currentEntry.toList().reversed()
    return remember(entryList, history) {
        val entryMap = entryList.associateBy { it.contentKey as Uuid }
        history.map { entryMap.getValue(it.id) }
    }
}

@Suppress("UNCHECKED_CAST")
val <T> NavEntry<BackstackEntry<T>>.navigationEntry : BackstackEntry<T>
    get() = metadata[NavKeyMetadataKey] as BackstackEntry<T>

private const val NavKeyMetadataKey = "com.alexvanyo.composelife.navigation.NavKeyMetadataKey"
