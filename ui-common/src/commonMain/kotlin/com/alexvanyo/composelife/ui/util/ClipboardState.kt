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

import androidx.compose.runtime.Composable
import androidx.compose.runtime.Stable
import androidx.compose.runtime.remember
import com.alexvanyo.composelife.dispatchers.di.ComposeLifeDispatchersProvider

/**
 * A reader for the system clipboard.
 */
@Stable
expect interface ClipboardReader

/**
 * A reader for the system clipboard.
 */
@Stable
expect interface ClipboardWriter {

    fun setText(value: String)
}

@Stable
interface ClipboardReaderWriter : ClipboardReader, ClipboardWriter

/**
 * Creates a [ClipboardReader] for reading from the system clipboard.
 *
 * Note: This will read from and listen to clipboard changes, which the user may be notified of.
 */
context(ComposeLifeDispatchersProvider)
@Composable
expect fun rememberClipboardReader(): ClipboardReader

/**
 * Creates a [ClipboardWriter] for writing to the system clipboard.
 */
@Composable
expect fun rememberClipboardWriter(): ClipboardWriter

/**
 * Creates a [ClipboardReaderWriter] for writing to the system clipboard.
 *
 * Note: This will read from and listen to clipboard changes, which the user may be notified of.
 * If you are just writing to the clipboard, use [rememberClipboardWriter] instead.
 */
context(ComposeLifeDispatchersProvider)
@Composable
fun rememberClipboardReaderWriter(): ClipboardReaderWriter {
    val clipboardReader = rememberClipboardReader()
    val clipboardWriter = rememberClipboardWriter()

    return remember(clipboardReader, clipboardWriter) {
        object :
            ClipboardReaderWriter,
            ClipboardReader by clipboardReader,
            ClipboardWriter by clipboardWriter {}
    }
}
