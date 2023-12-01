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

import android.content.ClipData
import android.content.ClipboardManager
import android.os.Build
import android.widget.Toast
import androidx.compose.runtime.Composable
import androidx.compose.runtime.Stable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.produceState
import androidx.compose.runtime.remember
import androidx.compose.ui.platform.LocalContext
import androidx.core.content.getSystemService
import com.alexvanyo.composelife.dispatchers.di.ComposeLifeDispatchersProvider
import com.alexvanyo.composelife.ui.common.R
import kotlinx.coroutines.withContext

@Stable
actual interface ClipboardReader {
    fun getClipData(): ClipData?

    suspend fun resolveToText(clipDataItem: ClipData.Item): CharSequence
}

@Stable
actual interface ClipboardWriter {
    fun setClipData(clipData: ClipData?)

    actual fun setText(value: String)
}

context(ComposeLifeDispatchersProvider)
@Composable
actual fun rememberClipboardReader(): ClipboardReader {
    val context = LocalContext.current
    val clipboardManager = remember(context) { requireNotNull(context.getSystemService<ClipboardManager>()) }

    val clipData by produceState(clipboardManager.primaryClip) {
        val listener = ClipboardManager.OnPrimaryClipChangedListener {
            value = clipboardManager.primaryClip
        }
        clipboardManager.addPrimaryClipChangedListener(listener)
        awaitDispose {
            clipboardManager.removePrimaryClipChangedListener(listener)
        }
    }
    return remember(dispatchers) {
        object : ClipboardReader {
            override fun getClipData(): ClipData? = clipData

            override suspend fun resolveToText(clipDataItem: ClipData.Item): CharSequence =
                withContext(dispatchers.IO) {
                    clipDataItem.coerceToText(context)
                }
        }
    }
}

@Composable
actual fun rememberClipboardWriter(): ClipboardWriter {
    val context = LocalContext.current
    val clipboardManager = remember(context) { requireNotNull(context.getSystemService<ClipboardManager>()) }

    return remember {
        object : ClipboardWriter {
            override fun setClipData(clipData: ClipData?) {
                if (clipData == null) {
                    if (Build.VERSION.SDK_INT >= 28) {
                        clipboardManager.clearPrimaryClip()
                    } else {
                        // TODO: Is there an alternate way to clear clipboard on older API levels?
                    }
                } else {
                    clipboardManager.setPrimaryClip(clipData)
                    // Provide feedback on older API versions as recommended by
                    // https://developer.android.com/develop/ui/views/touch-and-input/copy-paste
                    if (Build.VERSION.SDK_INT <= 32) {
                        Toast.makeText(context, R.string.copied, Toast.LENGTH_SHORT).show()
                    }
                }
            }

            override fun setText(value: String) {
                setClipData(ClipData.newPlainText(null, value))
            }
        }
    }
}
