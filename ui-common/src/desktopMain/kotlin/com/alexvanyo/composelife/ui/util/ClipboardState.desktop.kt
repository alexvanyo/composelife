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
import androidx.compose.ui.platform.awtClipboard
import com.alexvanyo.composelife.scopes.UiScope
import dev.zacsweers.metro.ContributesBinding
import dev.zacsweers.metro.Inject
import dev.zacsweers.metro.binding
import java.awt.datatransfer.DataFlavor
import java.awt.datatransfer.StringSelection
import java.awt.datatransfer.UnsupportedFlavorException
import java.io.IOException

@Inject
@ContributesBinding(UiScope::class, binding<ClipboardReader>())
class DesktopClipboardReader(
    private val clipboard: Clipboard,
) : ClipboardReader {
    @OptIn(ExperimentalComposeUiApi::class)
    override suspend fun getText(): String? =
        clipboard.awtClipboard?.getContents(this)?.let {
            try {
                DataFlavor.stringFlavor.getReaderForText(it).use { reader ->
                    reader.readText()
                }
            } catch (_: UnsupportedFlavorException) {
                null
            } catch (_: IOException) {
                null
            }
        }
}

@Inject
@ContributesBinding(UiScope::class, binding<ClipboardWriter>())
class DesktopClipboardWriter(
    private val clipboard: Clipboard,
) : ClipboardWriter {
    @OptIn(ExperimentalComposeUiApi::class)
    override suspend fun setText(value: String) = clipboard.setClipEntry(
        ClipEntry(StringSelection(value)),
    )
}
