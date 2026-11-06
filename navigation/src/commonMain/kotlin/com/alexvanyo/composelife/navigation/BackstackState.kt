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
import androidx.compose.runtime.saveable.rememberSerializable
import com.alexvanyo.composelife.serialization.SurrogatingSerializer
import kotlinx.serialization.KSerializer
import kotlinx.serialization.Serializable
import kotlinx.serialization.builtins.ListSerializer
import kotlinx.serialization.serializer
import kotlin.uuid.Uuid

/**
 * A [NavigationState] representing a backstack of [BackstackEntry]s.
 */
interface BackstackState<T> : NavigationState<BackstackEntry<T>> {
    override val entryMap: BackstackMap<T>
}

/**
 * The id of the previous entry if any. This acts a pointer into [BackstackState.entryMap].
 */
val <T> BackstackState<T>.previousEntryId: Uuid?
    get() = f_Navigation_previousEntryId<T>(currentEntry)

/**
 * The previous entry of this [BackstackState], based on the [BackstackState.previousEntryId].
 */
val <T> BackstackState<T>.previousEntry: BackstackEntry<T>?
    get() = entryMap[previousEntryId]

/**
 * A mutable entry map of [BackstackEntry] of type [T].
 */
typealias MutableBackstackMap<T> = MutableMap<Uuid, BackstackEntry<T>>

/**
 * An entry map of [BackstackEntry] of type [T].
 */
typealias BackstackMap<T> = Map<Uuid, BackstackEntry<T>>

/**
 * Remembers a [MutableBackstackMap] of type [T], with the given [initialBackstackEntries], and saving for each entry
 * value done by [saver].
 */
@Composable
inline fun <reified T> rememberBackstackMap(
    initialBackstackEntries: List<BackstackEntry<T>>,
    serializer: KSerializer<T> = serializer(),
): MutableBackstackMap<T> = rememberBackstackMap(
    initialBackstackEntries = initialBackstackEntries,
    backstackMapSerializer = BackstackMapSerializer(
        convertToSurrogate = ::ValueAsSurrogate,
        backstackValueSurrogateSerializer = ValueAsSurrogate.serializer(serializer),
    ),
)

/**
 * A more advanced version of [rememberBackstackMap] that allows saving and restoring state with knowledge of the
 * previous entry in the backstack.
 */
@Composable
fun <T> rememberBackstackMap(
    initialBackstackEntries: List<BackstackEntry<T>>,
    backstackMapSerializer: KSerializer<MutableBackstackMap<T>>,
): MutableBackstackMap<T> = rememberSerializable(
    serializer = backstackMapSerializer,
) {
    mutableStateMapOf<Uuid, BackstackEntry<T>>().apply {
        putAll(initialBackstackEntries.associateBy { it.id })
    }
}

@Serializable
@PublishedApi
internal data class ValueAsSurrogate<T>(val value: T) : BackstackValueSurrogate<T> {
    override fun createFromSurrogate(previous: BackstackEntry<T>?): T = value
}

interface BackstackValueSurrogate<T> {
    fun createFromSurrogate(previous: BackstackEntry<T>?): T
}

inline fun <T, reified S : BackstackValueSurrogate<T>> BackstackMapSerializer(
    noinline convertToSurrogate: (T) -> S,
): KSerializer<MutableBackstackMap<T>> = BackstackMapSerializer(
    convertToSurrogate = convertToSurrogate,
    backstackValueSurrogateSerializer = serializer(),
)

@Suppress("UNCHECKED_CAST")
fun <T, S : BackstackValueSurrogate<T>> BackstackMapSerializer(
    convertToSurrogate: (T) -> S,
    backstackValueSurrogateSerializer: KSerializer<S>,
): KSerializer<MutableBackstackMap<T>> = SurrogatingSerializer(
    serialName = "com.alexvanyo.composelife.navigation.BackstackMap",
    convertFromSurrogate = { entrySurrogateList ->
        val entries = checkNotNull(
            f_Navigation_deserializeBackstackEntries<S, T>(
                entrySurrogateList.map { it as Any? }.toTypedArray(),
            ) { surrogate, previous ->
                surrogate.createFromSurrogate(previous as BackstackEntry<T>?)
            },
        ) {
            "Failed to deserialize backstack entries!"
        }
        mutableStateMapOf<Uuid, BackstackEntry<T>>().apply {
            for (entry in entries) {
                val typedEntry = entry as BackstackEntry<T>
                put(typedEntry.id, typedEntry)
            }
        }
    },
    convertToSurrogate = { backstackMap ->
        val surrogates = f_Navigation_serializeBackstackEntries<T, S>(
            backstackMap.values.map { it as Any? }.toTypedArray(),
            convertToSurrogate,
        )
        surrogates.map { it as BackstackEntrySurrogate<S> }
    },
    surrogateSerializer = ListSerializer(
        BackstackEntrySurrogate.serializer(backstackValueSurrogateSerializer),
    ),
)
