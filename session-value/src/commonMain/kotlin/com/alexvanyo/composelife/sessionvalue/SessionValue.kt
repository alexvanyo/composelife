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
import androidx.savedstate.SavedState
import com.alexvanyo.composelife.serialization.saver
import kotlinx.serialization.KSerializer
import kotlinx.serialization.Serializable
import kotlin.uuid.Uuid

/**
 * An object representing a specific session for [value].
 *
 * This [value] is from the given [sessionId], and has the associated [valueId].
 *
 * Session values can be managed with a [SessionValueHolder] created with [rememberSessionValueHolder].
 */
@Serializable
data class SessionValue<out T>(
    val sessionId: Uuid,
    val valueId: Uuid,
    val value: T,
) {
    companion object {
        inline fun <reified T> Saver(): Saver<SessionValue<T>, SavedState> =
            Saver(kotlinx.serialization.serializer())

        fun <T> Saver(
            valueSerializer: KSerializer<T>,
        ): Saver<SessionValue<T>, SavedState> = serializer(valueSerializer).saver()
    }
}
