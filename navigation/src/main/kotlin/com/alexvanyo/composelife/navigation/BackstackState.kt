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

import androidx.compose.runtime.Composable
import androidx.compose.runtime.mutableStateMapOf
import androidx.compose.runtime.saveable.Saver
import androidx.compose.runtime.saveable.autoSaver
import androidx.compose.runtime.saveable.listSaver
import androidx.compose.runtime.saveable.rememberSaveable
import java.util.UUID

/**
 * A [NavigationState] representing a backstack of [BackstackEntry]s.
 */
interface BackstackState<T> : NavigationState<BackstackEntry<T>> {
    override val entryMap: BackstackMap<T>
}

/**
 * A mutable entry map of [BackstackEntry] of type [T].
 */
typealias MutableBackstackMap<T> = MutableMap<UUID, BackstackEntry<T>>

/**
 * An entry map of [BackstackEntry] of type [T].
 */
typealias BackstackMap<T> = Map<UUID, BackstackEntry<T>>

/**
 * Remembers a [MutableBackstackMap] of type [T], with the given [initialBackstackEntries], and saving for each entry
 * value done by [saver].
 */
@Composable
fun <T> rememberBackstackMap(
    initialBackstackEntries: List<BackstackEntry<T>>,
    saver: Saver<T, Any> = autoSaver(),
) = rememberBackstackMap(
    initialBackstackEntries = initialBackstackEntries,
    backstackValueSaverFactory = { saver },
)

/**
 * A more advanced version of [rememberBackstackMap] that allows saving and restoring state with knowledge of the
 * previous entry in the backstack.
 */
@Composable
fun <T> rememberBackstackMap(
    initialBackstackEntries: List<BackstackEntry<T>>,
    backstackValueSaverFactory: BackstackValueSaverFactory<T>,
): MutableBackstackMap<T> =
    rememberSaveable(
        saver = listSaver<MutableBackstackMap<T>, List<Any?>>(
            save = { backstack ->
                backstack.values.map { entry ->
                    val saver = backstackValueSaverFactory.create(entry.previous)

                    listOf(
                        with(saver) { save(entry.value) },
                        entry.id.toString(),
                        entry.previous?.id?.toString()
                    )
                }
            },
            restore = { list ->
                // Create a map from the restored entry ids to their restored values
                val savedEntries = list.associateBy { entryList -> UUID.fromString(entryList[1] as String) }

                val map = mutableStateMapOf<UUID, BackstackEntry<T>>()

                /**
                 * Recursively restore the entry with the given [id] and store it in [map].
                 *
                 * If the entry for the given [id] hasn't been restored yet, start restoring it, by first restoring
                 * its previous entry, if any.
                 */
                fun restoreEntry(id: UUID): BackstackEntry<T> =
                    map.getOrPut(id) {
                        val entryList = savedEntries.getValue(id)
                        val previousId = (entryList[2] as String?)?.let(UUID::fromString)
                        val previous = previousId?.let { restoreEntry(previousId) }
                        val saver = backstackValueSaverFactory.create(previous)
                        BackstackEntry(
                            id = id,
                            previous = previous,
                            value = saver.restore(entryList[0]!!)!!
                        )
                    }

                savedEntries.keys.forEach(::restoreEntry)

                map
            }
        )
    ) {
        mutableStateMapOf<UUID, BackstackEntry<T>>().apply {
            putAll(initialBackstackEntries.associateBy { it.id })
        }
    }

/**
 * A factory for creating a [Saver] that has knowledge of the previous entry in the backstack.
 *
 * Note that [previous] can be null, if saving or restoring the first entry.
 */
fun interface BackstackValueSaverFactory<T> {
    fun create(previous: BackstackEntry<T>?): Saver<T, Any>
}
