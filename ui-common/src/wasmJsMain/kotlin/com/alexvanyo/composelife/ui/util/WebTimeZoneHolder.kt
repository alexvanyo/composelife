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

import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.BindingContainer
import dev.zacsweers.metro.Binds
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.Inject
import kotlinx.coroutines.awaitCancellation
import kotlinx.datetime.TimeZone

@ContributesTo(AppScope::class)
@BindingContainer
interface WebTimeZoneHolderBindings {
    @Binds
    val WebTimeZoneHolder.bind: TimeZoneHolder
}

@Inject
class WebTimeZoneHolder : TimeZoneHolder {
    override val timeZone: TimeZone
        get() = TimeZone.currentSystemDefault()

    /**
     * TODO: Figure out how to listen for time zone updates on web.
     */
    override suspend fun update(): Nothing = awaitCancellation()
}
