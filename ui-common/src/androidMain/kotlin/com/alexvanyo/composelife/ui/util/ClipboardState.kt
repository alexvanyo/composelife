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
import androidx.compose.runtime.Composable
import androidx.compose.runtime.Stable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.produceState
import androidx.compose.runtime.remember
import androidx.compose.ui.platform.LocalContext
import androidx.core.content.getSystemService

@Stable
interface ClipboardState {
    var clipData: ClipData?
}

@Composable
fun rememberClipboardState(): ClipboardState {
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
    return remember {
        object : ClipboardState {
            override var clipData: ClipData?
                get() = clipData
                set(value) {
                    if (value == null) {
                        if (Build.VERSION.SDK_INT >= 28) {
                            clipboardManager.clearPrimaryClip()
                        } else {
                            // TODO: Is there an alternate way to clear clipboard on older API levels?
                        }
                    } else {
                        clipboardManager.setPrimaryClip(value)
                    }
                }
        }
    }
}
