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
import androidx.compose.ui.platform.ClipEntry
import androidx.compose.ui.platform.LocalClipboard
import androidx.compose.ui.platform.LocalClipboardManager
import androidx.compose.ui.text.AnnotatedString

@Stable
actual interface ClipboardReader {

    suspend fun getText(): String?
}

/**
 * TODO: getText is not snapshot-state aware, so we may not get updates if the clipboard changes
 */
actual val ClipboardReader.clipboardStateKey: Any? get() = Unit

@Stable
actual interface ClipboardWriter {

    suspend fun setText(value: String)
}

actual suspend fun ClipboardWriter.setText(value: String): Unit = setText(value)
