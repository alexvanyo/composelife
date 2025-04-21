/*
 * Copyright 2025 The Android Open Source Project
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

import android.util.Log
import android.view.View
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.size
import androidx.compose.runtime.Composable
import androidx.compose.runtime.CompositionLocalProvider
import androidx.compose.runtime.ProvidableCompositionLocal
import androidx.compose.runtime.compositionLocalWithComputedDefaultOf
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.setValue
import androidx.compose.ui.Modifier
import androidx.compose.ui.platform.LocalView
import androidx.compose.ui.unit.dp
import androidx.compose.ui.viewinterop.AndroidView
import androidx.core.view.ViewCompat
import androidx.core.view.WindowInsetsCompat

/**
 * Provides [LocalWindowInsetsHolder] with the updated value given by the insets dispatched to this point in the
 * composition hierarchy.
 */
@Composable
actual fun ProvideLocalWindowInsetsHolder(
    modifier: Modifier,
    content: @Composable () -> Unit,
) {
    Box(
        propagateMinConstraints = true,
        modifier = modifier,
    ) {
        var windowInsets: WindowInsetsCompat? by remember { mutableStateOf(null) }

        AndroidView(
            factory = { context ->
                View(context).also { view ->
                    ViewCompat.setOnApplyWindowInsetsListener(
                        view,
                    ) { v, insets ->
                        windowInsets = insets
                        insets
                    }
                }
            },
            modifier = Modifier.size(0.dp)
        ) {
            it.requestApplyInsets()
        }

        val windowInsetsHolder = remember {
            object : WindowInsetsHolder {
                override val windowInsets: WindowInsetsCompat?
                    get() = windowInsets
            }
        }

        CompositionLocalProvider(LocalWindowInsetsHolder provides windowInsetsHolder) {
            content()
        }
    }
}

actual interface WindowInsetsHolder {
    val windowInsets: WindowInsetsCompat?
}

/*
 * A [ProvidableCompositionLocal] for the [WindowInsetsCompat].
 *
 * Use [ProvideLocalWindowInsets] to update the [WindowInsetsCompat] appropriately.
 * If not used, the default [WindowShape] will be a simple rectangle path that matches the size of the window.
 */
actual val LocalWindowInsetsHolder: ProvidableCompositionLocal<WindowInsetsHolder> =
    compositionLocalWithComputedDefaultOf {
        object : WindowInsetsHolder {
            override val windowInsets: WindowInsetsCompat? =
                ViewCompat.getRootWindowInsets(LocalView.currentValue)
        }
    }
