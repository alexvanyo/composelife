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
import android.content.Context
import android.os.Build
import android.widget.Toast
import androidx.compose.runtime.Stable
import androidx.compose.runtime.derivedStateOf
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.setValue
import androidx.compose.runtime.snapshotFlow
import androidx.compose.ui.platform.WindowInfo
import androidx.core.content.getSystemService
import androidx.lifecycle.Lifecycle
import androidx.lifecycle.repeatOnLifecycle
import com.alexvanyo.composelife.scopes.ActivityContext
import com.alexvanyo.composelife.scopes.UiScope
import com.alexvanyo.composelife.ui.common.R
import com.alexvanyo.composelife.updatable.Updatable
import dev.zacsweers.metro.ContributesBinding
import dev.zacsweers.metro.ContributesIntoSet
import dev.zacsweers.metro.ForScope
import dev.zacsweers.metro.Inject
import dev.zacsweers.metro.SingleIn
import dev.zacsweers.metro.binding
import kotlinx.coroutines.awaitCancellation
import kotlin.uuid.Uuid

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

actual suspend fun ClipboardWriter.setText(value: String) {
    setClipData(ClipData.newPlainText(null, value))
}

sealed interface ClipboardStateKey {
    data object Empty : ClipboardStateKey
    data class PlaintextClipboard(
        val value: String,
    ) : ClipboardStateKey
    data class Unknown(
        val id: Uuid = Uuid.random(),
    ) : ClipboardStateKey
}

@Inject
@SingleIn(UiScope::class)
@ContributesBinding(UiScope::class, binding<ClipboardReader>())
@ContributesIntoSet(UiScope::class, binding = binding<
    @ForScope(UiScope::class)
    Updatable,
    >())
class AndroidClipboardReader(
    @param:ActivityContext private val context: Context,
    private val windowInfo: WindowInfo,
    @param:ForScope(UiScope::class) private val lifecycle: Lifecycle,
) : ClipboardReader, Updatable {

    val clipboardManager = requireNotNull(context.getSystemService<ClipboardManager>())

    var keyToReadClipData by mutableStateOf(Uuid.random())

    // Avoid reading clipboard immediately, and instead read it lazily via derivedStateOf
    // This avoids reading from clipboard until the clip data is used
    private val _clipData by
        derivedStateOf {
            keyToReadClipData
            clipboardManager.primaryClip
        }

    override val androidClipboardStateKey: ClipboardStateKey
        get() {
            val currentClipData = _clipData
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

    override fun getClipData(): ClipData? = _clipData

    override suspend fun update(): Nothing {
        lifecycle.repeatOnLifecycle(Lifecycle.State.STARTED) {
            // The clipboard could have changed while in the background or while the window wasn't focused, so we need
            // to read it again
            keyToReadClipData = Uuid.random()
            val listener = ClipboardManager.OnPrimaryClipChangedListener {
                // The clipboard changed, so we need to read it again
                keyToReadClipData = Uuid.random()
            }
            try {
                clipboardManager.addPrimaryClipChangedListener(listener)
                snapshotFlow { windowInfo.isWindowFocused }
                    .collect { keyToReadClipData = Uuid.random() }
            } finally {
                clipboardManager.removePrimaryClipChangedListener(listener)
            }
        }
        awaitCancellation()
    }
}

@Inject
@ContributesBinding(UiScope::class, binding<ClipboardWriter>())
class AndroidClipboardWriter(
    @param:ActivityContext private val context: Context,
) : ClipboardWriter {
    private val clipboardManager: ClipboardManager =
        requireNotNull(context.getSystemService<ClipboardManager>())

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
