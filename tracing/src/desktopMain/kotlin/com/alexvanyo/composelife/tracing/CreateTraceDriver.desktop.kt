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

package com.alexvanyo.composelife.tracing

import androidx.tracing.wire.TraceDriver
import androidx.tracing.wire.TraceSink
import kotlinx.coroutines.Dispatchers
import java.io.File
import kotlin.coroutines.CoroutineContext

public fun createTraceDriver(
    directory: File = File(System.getProperty("java.io.tmpdir")),
    coroutineContext: CoroutineContext = Dispatchers.IO,
): AbstractTraceDriver = TraceDriver(
    sink = TraceSink(
        directory = directory,
        sequenceId = 1,
        coroutineContext = coroutineContext,
    ),
)
