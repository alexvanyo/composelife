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
import androidx.compose.ui.platform.LocalClipboardManager
import androidx.compose.ui.text.AnnotatedString

@Stable
actual interface ClipboardReader {

    fun getText(): AnnotatedString?
}

/**
 * TODO: getText is not snapshot-state aware, so we may not get updates if the clipboard changes
 */
actual val ClipboardReader.clipboardStateKey: Any? get() = getText()

@Stable
actual interface ClipboardWriter {

    fun setText(annotatedString: AnnotatedString)
}

actual fun ClipboardWriter.setText(value: String): Unit = setText(AnnotatedString(value))

@Composable
actual fun rememberClipboardReader(): ClipboardReader {
    val clipboardManager = LocalClipboardManager.current
    return remember(clipboardManager) {
        object : ClipboardReader {
            override fun getText(): AnnotatedString? = clipboardManager.getText()
        }
    }
}

@Composable
actual fun rememberClipboardWriter(): ClipboardWriter {
    val clipboardManager = LocalClipboardManager.current
    return remember(clipboardManager) {
        object : ClipboardWriter {
            override fun setText(annotatedString: AnnotatedString) = clipboardManager.setText(annotatedString)
        }
    }
}

@Composable
actual fun rememberClipboardReaderWriter(): ClipboardReaderWriter {
    val clipboardReader = rememberClipboardReader()
    val clipboardWriter = rememberClipboardWriter()

    return remember(clipboardReader, clipboardWriter) {
        object :
            ClipboardReaderWriter,
            ClipboardReader by clipboardReader,
            ClipboardWriter by clipboardWriter {}
    }
}
