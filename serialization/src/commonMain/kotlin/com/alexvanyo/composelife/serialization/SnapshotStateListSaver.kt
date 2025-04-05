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

package com.alexvanyo.composelife.serialization

import androidx.compose.runtime.mutableStateListOf
import androidx.compose.runtime.saveable.Saver
import androidx.compose.runtime.snapshots.SnapshotStateList
import kotlinx.serialization.KSerializer

/**
 * A [Saver] for a [T] to encode and decode with the given [KSerializer].
 */
fun <T, R : Any> SnapshotStateListSaver(
    listSaver: Saver<List<T>, R>,
): Saver<SnapshotStateList<T>, R> = Saver(
    save = { with(listSaver) { save(it) } },
    restore = {
        mutableStateListOf<T>().apply {
            listSaver.restore(it)?.let(::addAll)
        }
    },
)
