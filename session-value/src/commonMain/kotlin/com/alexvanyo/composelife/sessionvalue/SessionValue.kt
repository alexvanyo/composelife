/*
 * Copyright 2024 The Android Open Source Project
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

package com.alexvanyo.composelife.sessionvalue

import androidx.compose.runtime.saveable.Saver
import androidx.compose.runtime.saveable.listSaver
import java.util.UUID

data class SessionValue<out T>(
    val sessionId: UUID,
    val valueId: UUID,
    val value: T,
) {
    companion object {
        fun <T, R : Any> Saver(
            valueSaver: Saver<T, R>,
        ): Saver<SessionValue<T>, Any> = listSaver(
            save = {
                listOf(
                    with(uuidSaver) { save(it.sessionId) },
                    with(uuidSaver) { save(it.valueId) },
                    with(valueSaver) { save(it.value) },
                )
            },
            restore = {
                @Suppress("UNCHECKED_CAST")
                SessionValue(
                    sessionId = uuidSaver.restore(it[0]!! as String)!!,
                    valueId = uuidSaver.restore(it[1]!! as String)!!,
                    value = valueSaver.restore(it[2]!! as R)!!,
                )
            },
        )
    }
}

/**
 * A [Saver] for a [UUID].
 */
internal val uuidSaver: Saver<UUID, String> = Saver(
    save = { it.toString() },
    restore = UUID::fromString,
)
