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
import androidx.compose.runtime.DisposableEffect
import androidx.compose.runtime.Stable
import androidx.compose.runtime.derivedStateOf
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.setValue
import androidx.compose.ui.platform.LocalContext
import androidx.compose.ui.platform.LocalWindowInfo
import androidx.core.content.getSystemService
import androidx.lifecycle.compose.LifecycleStartEffect
import com.alexvanyo.composelife.ui.common.R
import com.benasher44.uuid.Uuid
import com.benasher44.uuid.uuid4

@Stable
actual interface ClipboardReader {
    val androidClipboardStateKey: ClipboardStateKey

    fun getClipData(): ClipData?
}

actual val ClipboardReader.clipboardStateKey: Any? get() = androidClipboardStateKey

@Stable
actual interface ClipboardWriter {
    fun setClipData(clipData: ClipData?)
}

actual fun ClipboardWriter.setText(value: String) {
    setClipData(ClipData.newPlainText(null, value))
}

sealed interface ClipboardStateKey {
    data object Empty : ClipboardStateKey
    data class PlaintextClipboard(
        val value: String,
    ) : ClipboardStateKey
    data class Unknown(
        val id: Uuid = uuid4(),
    ) : ClipboardStateKey
}

@Composable
actual fun rememberClipboardReader(): ClipboardReader {
    var windowFocusKey by remember { mutableStateOf(uuid4()) }
    val isWindowFocused = LocalWindowInfo.current.isWindowFocused
    DisposableEffect(isWindowFocused) {
        if (isWindowFocused) {
            windowFocusKey = uuid4()
        }
        onDispose {}
    }

    val context = LocalContext.current
    val clipboardManager = remember(context) { requireNotNull(context.getSystemService<ClipboardManager>()) }

    var keyToReadClipData by remember(clipboardManager) { mutableStateOf(uuid4()) }

    LifecycleStartEffect(
        clipboardManager,
        windowFocusKey,
    ) {
        // The clipboard could have changed while in the background or while the window wasn't focused, so we need
        // to read it again
        keyToReadClipData = uuid4()
        val listener = ClipboardManager.OnPrimaryClipChangedListener {
            // The clipboard changed, so we need to read it again
            keyToReadClipData = uuid4()
        }
        clipboardManager.addPrimaryClipChangedListener(listener)
        onStopOrDispose {
            clipboardManager.removePrimaryClipChangedListener(listener)
        }
    }

    val clipData by remember {
        // Avoid reading clipboard immediately, and instead read it lazily via derivedStateOf
        // This avoids reading from clipboard until the clip data is used
        derivedStateOf {
            keyToReadClipData
            clipboardManager.primaryClip
        }
    }

    return remember {
        object : ClipboardReader {
            override val androidClipboardStateKey: ClipboardStateKey
                get() {
                    val currentClipData = clipData
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

            override fun getClipData(): ClipData? = clipData
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
