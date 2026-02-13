/*
 * Copyright 2023 The Android Open Source Project
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

import androidx.compose.runtime.Stable
import com.alexvanyo.composelife.scopes.UiScope
import dev.zacsweers.metro.ContributesBinding
import dev.zacsweers.metro.Inject
import dev.zacsweers.metro.binding

/**
 * A reader for the system clipboard.
 */
@Stable
expect interface ClipboardReader

/**
 * Retrieves a snapshot-state aware indicator that the clipboard state may have changed.
 *
 * If this [clipboardStateKey] object doesn't change (the previous value is equal to the current value) then the
 * clipboard state has not changed.
 *
 * The type of this object may be platform-specific, and not be the text represented by the clipboard itself.
 */
expect val ClipboardReader.clipboardStateKey: Any?

/**
 * A reader for the system clipboard.
 */
@Stable
expect interface ClipboardWriter

/**
 * Sets the clipboard to the given text.
 */
expect suspend fun ClipboardWriter.setText(value: String)

@Stable
interface ClipboardReaderWriter : ClipboardReader, ClipboardWriter

@Inject
@ContributesBinding(UiScope::class, binding<ClipboardReaderWriter>())
class ClipboardReaderWriterImpl(
    clipboardReader: ClipboardReader,
    clipboardWriter: ClipboardWriter,
): ClipboardReaderWriter, ClipboardReader by clipboardReader, ClipboardWriter by clipboardWriter
