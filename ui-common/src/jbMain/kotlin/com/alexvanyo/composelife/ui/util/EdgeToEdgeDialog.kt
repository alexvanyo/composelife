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

import androidx.compose.runtime.Composable
import androidx.compose.ui.window.Dialog
import androidx.compose.ui.window.DialogProperties

/**
 * A [Dialog] based on [EdgeToEdgeDialog] that provides a more opinionated dialog that is closer to the default
 * [Dialog].
 *
 * The [scrim] is rendered behind the content. The default scrim will request to dismiss the dialog if
 * [DialogProperties.dismissOnClickOutside] is true.
 *
 * The [content] of the dialog can be arbitrarily sized, and can fill the entire window if desired.
 *
 * If [DialogProperties.dismissOnBackPress] is true, the [content] will automatically start to animate out with a
 * predictive back gestures from the dialog.
 */
@Composable
expect fun PlatformEdgeToEdgeDialog(
    onDismissRequest: () -> Unit,
    properties: DialogProperties = DialogProperties(),
    content: @Composable () -> Unit,
)
