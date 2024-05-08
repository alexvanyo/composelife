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
import androidx.compose.animation.AnimatedVisibility
import androidx.compose.animation.core.tween
import androidx.compose.animation.fadeIn
import androidx.compose.animation.fadeOut
import androidx.compose.animation.togetherWith
import androidx.compose.foundation.layout.Arrangement
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.ExperimentalLayoutApi
import androidx.compose.foundation.layout.FlowRow
import androidx.compose.foundation.layout.Row
import androidx.compose.foundation.layout.Spacer
import androidx.compose.foundation.layout.fillMaxWidth
import androidx.compose.foundation.layout.height
import androidx.compose.foundation.layout.padding
import androidx.compose.material3.Button
import androidx.compose.material3.HorizontalDivider
import androidx.compose.material3.LinearProgressIndicator
import androidx.compose.material3.MaterialTheme
import androidx.compose.material3.OutlinedButton
import androidx.compose.material3.Text
import androidx.compose.runtime.Composable
import androidx.compose.runtime.key
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.text.style.TextAlign
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResource
import com.alexvanyo.composelife.ui.app.resources.Allow
import com.alexvanyo.composelife.ui.app.resources.Clipboard
import com.alexvanyo.composelife.ui.app.resources.ClipboardWatchingOnboarding
import com.alexvanyo.composelife.ui.app.resources.Disallow
import com.alexvanyo.composelife.ui.app.resources.Pinned
import com.alexvanyo.composelife.ui.app.resources.Strings
import com.alexvanyo.composelife.ui.util.SharedTransitionLayout

context(ClipboardCellStatePreviewInjectEntryPoint, ClipboardCellStatePreviewLocalEntryPoint)
@Composable
fun ClipboardWatchingSection(
    clipboardWatchingState: ClipboardWatchingState,
    modifier: Modifier = Modifier,
) {
    AnimatedContent(
        targetState = clipboardWatchingState,
        contentKey = { targetState ->
            when (targetState) {
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
            is ClipboardWatchingState.ClipboardWatchingEnabled -> { ClipboardWatchingEnabled(targetState) }
            is ClipboardWatchingState.Onboarding -> { ClipboardWatchingOnboarding(targetState) }
        }
    }
}

context(ClipboardCellStatePreviewInjectEntryPoint, ClipboardCellStatePreviewLocalEntryPoint)
@Composable
fun ClipboardWatchingEnabled(
    clipboardWatchingState: ClipboardWatchingState.ClipboardWatchingEnabled,
    modifier: Modifier = Modifier,
) {
    Column(modifier = modifier) {
        Box(contentAlignment = Alignment.BottomCenter) {
            Text(
                text = parameterizedStringResource(Strings.Clipboard),
                style = MaterialTheme.typography.titleMedium,
                modifier = Modifier.fillMaxWidth().padding(16.dp),
            )

            androidx.compose.animation.AnimatedVisibility(
                clipboardWatchingState.isLoading,
                enter = fadeIn(),
                exit = fadeOut(),
            ) {
                LinearProgressIndicator(Modifier.fillMaxWidth())
            }
        }

        ClipboardPreviewHistory(clipboardWatchingState.clipboardPreviewStates)

        HorizontalDivider(modifier = Modifier.fillMaxWidth().padding(16.dp))

        AnimatedVisibility(clipboardWatchingState.pinnedClipboardPreviewStates.isNotEmpty()) {
            Text(
                text = parameterizedStringResource(Strings.Pinned),
                style = MaterialTheme.typography.titleMedium,
                modifier = Modifier.fillMaxWidth().padding(16.dp),
            )
        }

        PinnedClipboardPreviews(clipboardWatchingState.pinnedClipboardPreviewStates)

        AnimatedVisibility(clipboardWatchingState.pinnedClipboardPreviewStates.isNotEmpty()) {
            HorizontalDivider(modifier = Modifier.fillMaxWidth().padding(16.dp))
        }
    }
}

context(ClipboardCellStatePreviewInjectEntryPoint, ClipboardCellStatePreviewLocalEntryPoint)
@Composable
private fun PinnedClipboardPreviews(
    pinnedClipboardPreviewStates: List<PinnedClipboardPreviewState>,
    modifier: Modifier = Modifier,
) {
    SharedTransitionLayout(modifier = modifier) {
        AnimatedContent(
            pinnedClipboardPreviewStates,
            transitionSpec = {
                fadeIn(animationSpec = tween(220, delayMillis = 90))
                    .togetherWith(fadeOut(animationSpec = tween(90)))
            },
            contentKey = { it.map(PinnedClipboardPreviewState::id) },
        ) { targetState ->
            val chunks: List<List<PinnedClipboardPreviewState?>> =
                targetState
                    .chunked(2) { partialChunk ->
                        List(2) { partialChunk.getOrNull(it) }
                    }

            Column(Modifier.fillMaxWidth().padding(horizontal = 16.dp)) {
                chunks.forEach { chunk ->
                    Row {
                        chunk.forEach { pinnedClipboardPreviewState ->
                            if (pinnedClipboardPreviewState == null) {
                                Spacer(Modifier.weight(1f))
                            } else {
                                key(pinnedClipboardPreviewState.id) {
                                    ClipboardCellStatePreview(
                                        deserializationResult = pinnedClipboardPreviewState.deserializationResult,
                                        isPinned = true,
                                        onPaste = pinnedClipboardPreviewState::onPaste,
                                        onPinChanged = pinnedClipboardPreviewState::onUnpin,
                                        modifier = Modifier
                                            .weight(1f)
                                            .padding(8.dp)
                                            .sharedElement(
                                                rememberSharedContentState(
                                                    pinnedClipboardPreviewState.id,
                                                ),
                                                this@AnimatedContent,
                                            ),
                                    )
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

context(ClipboardCellStatePreviewInjectEntryPoint, ClipboardCellStatePreviewLocalEntryPoint)
@Composable
private fun ClipboardPreviewHistory(
    clipboardPreviewStates: List<ClipboardPreviewState>,
    modifier: Modifier = Modifier,
) {
    SharedTransitionLayout(modifier = modifier) {
        AnimatedContent(
            clipboardPreviewStates,
            transitionSpec = {
                fadeIn(animationSpec = tween(220, delayMillis = 90))
                    .togetherWith(fadeOut(animationSpec = tween(90)))
            },
            contentKey = { it.map(ClipboardPreviewState::id) },
        ) { targetState ->
            key(targetState.map(ClipboardPreviewState::id)) {
                val chunks: List<List<ClipboardPreviewState?>> =
                    listOf(listOf(targetState.firstOrNull())) + targetState
                        .drop(1)
                        .chunked(2) { partialChunk ->
                            List(2) { partialChunk.getOrNull(it) }
                        }

                Column(Modifier.fillMaxWidth().padding(horizontal = 16.dp)) {
                    chunks.forEach { chunk ->
                        Row {
                            chunk.forEach { clipboardPreviewState ->
                                if (clipboardPreviewState == null) {
                                    Spacer(
                                        Modifier
                                            .weight(1f)
                                            .padding(8.dp)
                                            .height(160.dp),
                                    )
                                } else {
                                    key(clipboardPreviewState.id) {
                                        ClipboardCellStatePreview(
                                            deserializationResult = clipboardPreviewState.deserializationResult,
                                            isPinned = clipboardPreviewState.isPinned,
                                            onPaste = clipboardPreviewState::onPaste,
                                            onPinChanged = clipboardPreviewState::onPinChanged,
                                            modifier = Modifier
                                                .weight(1f)
                                                .padding(8.dp)
                                                .sharedElement(
                                                    rememberSharedContentState(clipboardPreviewState.id),
                                                    this@AnimatedContent,
                                                ),
                                        )
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

@OptIn(ExperimentalLayoutApi::class)
@Composable
fun ClipboardWatchingOnboarding(
    clipboardWatchingState: ClipboardWatchingState.Onboarding,
    modifier: Modifier = Modifier,
) {
    Column(modifier = modifier) {
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
                onClick = clipboardWatchingState::onDisallowClipboardWatching,
            ) {
                Text(parameterizedStringResource(Strings.Disallow))
            }
            Button(
                onClick = clipboardWatchingState::onAllowClipboardWatching,
            ) {
                Text(parameterizedStringResource(Strings.Allow))
            }
        }
    }
}
