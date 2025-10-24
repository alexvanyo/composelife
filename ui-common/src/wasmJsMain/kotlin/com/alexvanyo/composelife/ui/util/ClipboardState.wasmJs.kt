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
import androidx.compose.runtime.remember
import androidx.compose.ui.ExperimentalComposeUiApi
import androidx.compose.ui.platform.ClipEntry
import androidx.compose.ui.platform.ClipboardItem
import androidx.compose.ui.platform.LocalClipboard
import kotlinx.coroutines.await
import org.w3c.files.Blob
import kotlin.js.Promise

@OptIn(ExperimentalWasmJsInterop::class, ExperimentalComposeUiApi::class)
@Composable
actual fun rememberClipboardReader(): ClipboardReader {
    val clipboard = LocalClipboard.current
    return remember(clipboard) {
        object : ClipboardReader {
            override suspend fun getText(): String? {
                val clipboardItem =
                    clipboard.nativeClipboard
                        .read()
                        .await<JsArray<ClipboardItem>>()
                        .toList()
                        .firstOrNull {
                            "text/plain" in it.types.toList().map(JsString::toString)
                        } ?: return null

                val blob = clipboardItem.getType("text/plain".toJsString()).await<Blob>()
                return readTextFromBlob(blob).await<JsString>().toString()
            }
        }
    }
}

@Composable
actual fun rememberClipboardWriter(): ClipboardWriter {
    val clipboard = LocalClipboard.current
    return remember(clipboard) {
        object : ClipboardWriter {
            override suspend fun setText(value: String) = clipboard.setClipEntry(
                ClipEntry.withPlainText(value),
            )
        }
    }
}

@Suppress("UNUSED_PARAMETER")
@OptIn(ExperimentalWasmJsInterop::class)
private fun readTextFromBlob(blob: Blob): Promise<JsString> =
    js("blob.text()")
