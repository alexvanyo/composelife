/*
 * Copyright 2026 The Android Open Source Project
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
import kotlinx.serialization.serializer

inline fun <reified T : Any> SessionValue.Companion.Saver(): Saver<SessionValue<T>, SavedState> = Saver(serializer<T>())

fun <T : Any> SessionValue.Companion.Saver(valueSerializer: KSerializer<T>): Saver<SessionValue<T>, SavedState> =
    SessionValue.serializer(valueSerializer).saver()
