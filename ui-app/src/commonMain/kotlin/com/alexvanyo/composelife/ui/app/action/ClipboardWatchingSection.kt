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

package com.alexvanyo.composelife.ui.app.action

import androidx.compose.animation.AnimatedContent
import androidx.compose.animation.core.tween
import androidx.compose.animation.fadeIn
import androidx.compose.animation.fadeOut
import androidx.compose.animation.togetherWith
import androidx.compose.foundation.layout.Arrangement
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.ExperimentalLayoutApi
import androidx.compose.foundation.layout.FlowRow
import androidx.compose.foundation.layout.Spacer
import androidx.compose.foundation.layout.fillMaxWidth
import androidx.compose.foundation.layout.height
import androidx.compose.foundation.layout.padding
import androidx.compose.material3.Button
import androidx.compose.material3.OutlinedButton
import androidx.compose.material3.Text
import androidx.compose.runtime.Composable
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.text.style.TextAlign
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResource
import com.alexvanyo.composelife.ui.app.resources.Allow
import com.alexvanyo.composelife.ui.app.resources.ClipboardWatchingOnboarding
import com.alexvanyo.composelife.ui.app.resources.Disallow
import com.alexvanyo.composelife.ui.app.resources.Strings

context(ClipboardCellStatePreviewInjectEntryPoint, ClipboardCellStatePreviewLocalEntryPoint)
@OptIn(ExperimentalLayoutApi::class)
@Composable
fun ClipboardWatchingSection(
    clipboardWatchingState: ClipboardWatchingState,
    modifier: Modifier = Modifier,
) {
    AnimatedContent(
        targetState = clipboardWatchingState,
        contentKey = {
            when (clipboardWatchingState) {
                ClipboardWatchingState.ClipboardWatchingDisabled -> 0
                is ClipboardWatchingState.ClipboardWatchingEnabled -> 1
                is ClipboardWatchingState.Onboarding -> 2
            }
        },
        transitionSpec = {
            fadeIn(animationSpec = tween(220, delayMillis = 90))
                .togetherWith(fadeOut(animationSpec = tween(90)))
        },
        modifier = modifier,
    ) { targetState ->
        when (targetState) {
            ClipboardWatchingState.ClipboardWatchingDisabled -> Unit
            is ClipboardWatchingState.ClipboardWatchingEnabled -> {
                ClipboardCellStatePreview(
                    clipboardCellStateResourceState = targetState.clipboardCellStateResourceState,
                    onPaste = targetState::onPasteClipboard,
                    onPin = targetState::onPinClipboard,
                    modifier = Modifier.padding(horizontal = 24.dp),
                )
            }
            is ClipboardWatchingState.Onboarding -> {
                Column {
                    Text(
                        text = parameterizedStringResource(Strings.ClipboardWatchingOnboarding),
                        textAlign = TextAlign.Center,
                        modifier = Modifier.padding(horizontal = 16.dp),
                    )

                    Spacer(modifier = Modifier.height(8.dp))

                    FlowRow(
                        modifier = Modifier.fillMaxWidth(),
                        horizontalArrangement = Arrangement.spacedBy(24.dp, Alignment.CenterHorizontally),
                    ) {
                        OutlinedButton(
                            onClick = targetState::onDisallowClipboardWatching,
                        ) {
                            Text(parameterizedStringResource(Strings.Disallow))
                        }
                        Button(
                            onClick = targetState::onAllowClipboardWatching,
                        ) {
                            Text(parameterizedStringResource(Strings.Allow))
                        }
                    }
                }
            }
        }
    }
}
