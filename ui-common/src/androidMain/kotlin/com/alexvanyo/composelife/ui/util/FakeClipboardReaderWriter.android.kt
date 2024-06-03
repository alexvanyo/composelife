/*
 * Copyright 2024 The Android Open Source Project
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

import android.content.ClipData
import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.setValue
import androidx.compose.ui.platform.LocalContext

@Composable
actual fun rememberFakeClipboardReaderWriter(): ClipboardReaderWriter {
    var state: ClipData? by rememberSaveable {
        mutableStateOf(null)
    }

    val context = LocalContext.current

    return object : ClipboardReaderWriter {
        override val androidClipboardStateKey: ClipboardStateKey
            get() {
                val currentClipData = state
                return when {
                    currentClipData == null -> ClipboardStateKey.Empty
                    currentClipData.itemCount == 1 -> {
                        currentClipData.getItemAt(0)
                            .text
                            ?.toString()
                            ?.let(ClipboardStateKey::PlaintextClipboard) ?: ClipboardStateKey.Unknown()
                    }
                    else -> ClipboardStateKey.Unknown()
                }
            }

        override fun getClipData(): ClipData? = state

        override suspend fun resolveToText(clipDataItem: ClipData.Item): CharSequence =
            clipDataItem.coerceToText(context)

        override fun setClipData(clipData: ClipData?) {
            state = clipData
        }
    }
}
