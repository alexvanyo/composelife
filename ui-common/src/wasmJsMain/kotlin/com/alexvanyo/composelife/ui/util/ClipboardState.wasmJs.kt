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

import androidx.compose.ui.ExperimentalComposeUiApi
import androidx.compose.ui.platform.ClipEntry
import androidx.compose.ui.platform.Clipboard
import androidx.compose.ui.platform.ClipboardItem
import com.alexvanyo.composelife.scopes.UiScope
import dev.zacsweers.metro.ContributesBinding
import dev.zacsweers.metro.Inject
import dev.zacsweers.metro.binding
import kotlinx.coroutines.await
import org.w3c.files.Blob
import kotlin.js.Promise

@Inject
@ContributesBinding(UiScope::class, binding<ClipboardReader>())
class WebClipboardReader(
    private val clipboard: Clipboard,
) : ClipboardReader {
    @OptIn(ExperimentalComposeUiApi::class, ExperimentalWasmJsInterop::class)
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

@Inject
@ContributesBinding(UiScope::class, binding<ClipboardWriter>())
class WebClipboardWriter(
    private val clipboard: Clipboard,
) : ClipboardWriter {
    @OptIn(ExperimentalComposeUiApi::class)
    override suspend fun setText(value: String) = clipboard.setClipEntry(
        ClipEntry.withPlainText(value),
    )
}

@Suppress("UNUSED_PARAMETER")
@OptIn(ExperimentalWasmJsInterop::class)
private fun readTextFromBlob(blob: Blob): Promise<JsString> =
    js("blob.text()")
