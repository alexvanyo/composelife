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

package com.alexvanyo.composelife.tracing.di

import android.content.Context
import androidx.tracing.wire.TraceDriver
import androidx.tracing.wire.TraceSink
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.scopes.ApplicationContext
import com.alexvanyo.composelife.tracing.AbstractTraceDriver
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.BindingContainer
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.Provides
import dev.zacsweers.metro.SingleIn

@ContributesTo(AppScope::class)
@BindingContainer
interface AndroidTracingBindings {
    companion object {
        @SingleIn(AppScope::class)
        @Provides
        internal fun providesTraceDriver(
            @ApplicationContext context: Context,
            dispatchers: ComposeLifeDispatchers,
        ): AbstractTraceDriver = TraceDriver(
            context = context,
            sink = TraceSink(
                context = context,
                sequenceId = 1,
                coroutineContext = dispatchers.IO,
            ),
        )
    }
}
