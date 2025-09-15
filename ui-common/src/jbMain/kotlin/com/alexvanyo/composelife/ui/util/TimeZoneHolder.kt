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

package com.alexvanyo.composelife.ui.util

import androidx.compose.runtime.Composable
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.Stable
import androidx.lifecycle.Lifecycle
import androidx.lifecycle.repeatOnLifecycle
import com.alexvanyo.composelife.updatable.Updatable
import kotlinx.datetime.TimeZone

/**
 * A [Stable] state holder of the current [TimeZone].
 *
 * [timeZone] will give the current [timeZone] backed by snapshot state. Reading this value directly will return the
 * most up-to-date value, which is populated by its [Updatable.update].
 *
 * Therefore, callers interested in receiving any updates to the [TimeZone] should also call [Updatable.update] while
 * they are interested in the most up-to-date values.
 *
 * A helper for doing this in composition is [currentTimeZone].
 */
@Stable
interface TimeZoneHolder : Updatable {
    val timeZone: TimeZone
}

/**
 * Returns the current [TimeZone] as an observable value.
 *
 * @param lifecycleState the minimum [Lifecycle.State] to watch for updates to the [TimeZone] in. If the [TimeZone] is
 * just being used to drive UI such as for formatting, then the default [Lifecycle.State.STARTED] is appropriate to
 * only listen while the UI is visible.
 */
@Composable
context(timeZoneHolder: TimeZoneHolder)
fun currentTimeZone(lifecycleState: Lifecycle.State = Lifecycle.State.STARTED): TimeZone {
    val lifecycleOwner = androidx.lifecycle.compose.LocalLifecycleOwner.current
    LaunchedEffect(lifecycleOwner) {
        lifecycleOwner.repeatOnLifecycle(lifecycleState) {
            timeZoneHolder.update()
        }
    }
    return timeZoneHolder.timeZone
}
