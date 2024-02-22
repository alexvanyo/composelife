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

package com.alexvanyo.composelife.ui.app.action

import androidx.compose.material3.Surface
import androidx.compose.runtime.Composable
import androidx.compose.ui.Modifier
import com.alexvanyo.composelife.model.CellStateFormat
import com.alexvanyo.composelife.model.DeserializationResult
import com.alexvanyo.composelife.patterns.GliderPattern
import com.alexvanyo.composelife.resourcestate.ResourceState
import com.alexvanyo.composelife.ui.app.entrypoints.WithPreviewDependencies
import com.alexvanyo.composelife.ui.app.theme.ComposeLifeTheme
import com.alexvanyo.composelife.ui.util.ThemePreviews

@ThemePreviews
@Composable
fun ClipboardWatchingSectionOnboardingPreview(modifier: Modifier = Modifier) {
    WithPreviewDependencies {
        ComposeLifeTheme {
            Surface(modifier) {
                ClipboardWatchingSection(
                    clipboardWatchingState = object : ClipboardWatchingState.Onboarding {
                        override fun onAllowClipboardWatching() = Unit
                        override fun onDisallowClipboardWatching() = Unit
                    },
                )
            }
        }
    }
}

@ThemePreviews
@Composable
fun ClipboardWatchingSectionDisabledPreview(modifier: Modifier = Modifier) {
    WithPreviewDependencies {
        ComposeLifeTheme {
            Surface(modifier) {
                ClipboardWatchingSection(
                    clipboardWatchingState = ClipboardWatchingState.ClipboardWatchingDisabled,
                )
            }
        }
    }
}

@ThemePreviews
@Composable
fun ClipboardWatchingSectionEnabledLoadingPreview(modifier: Modifier = Modifier) {
    WithPreviewDependencies {
        ComposeLifeTheme {
            Surface(modifier) {
                ClipboardWatchingSection(
                    clipboardWatchingState = object : ClipboardWatchingState.ClipboardWatchingEnabled {
                        override val clipboardCellStateResourceState get() = ResourceState.Loading

                        override fun onPasteClipboard() = Unit

                        override fun onPinClipboard() = Unit
                    },
                )
            }
        }
    }
}

@ThemePreviews
@Composable
fun ClipboardWatchingSectionEnabledFailurePreview(modifier: Modifier = Modifier) {
    WithPreviewDependencies {
        ComposeLifeTheme {
            Surface(modifier) {
                ClipboardWatchingSection(
                    clipboardWatchingState = object : ClipboardWatchingState.ClipboardWatchingEnabled {
                        override val clipboardCellStateResourceState: ResourceState<DeserializationResult>
                            get() = ResourceState.Failure(Exception("Test exception"))

                        override fun onPasteClipboard() = Unit

                        override fun onPinClipboard() = Unit
                    },
                )
            }
        }
    }
}

@ThemePreviews
@Composable
fun ClipboardWatchingSectionEnabledSuccessSuccessfulPreview(modifier: Modifier = Modifier) {
    WithPreviewDependencies {
        ComposeLifeTheme {
            Surface(modifier) {
                ClipboardWatchingSection(
                    clipboardWatchingState = object : ClipboardWatchingState.ClipboardWatchingEnabled {
                        override val clipboardCellStateResourceState: ResourceState<DeserializationResult>
                            get() = ResourceState.Success(
                                DeserializationResult.Successful(
                                    cellState = GliderPattern.seedCellState,
                                    warnings = emptyList(),
                                    format = CellStateFormat.FixedFormat.RunLengthEncoding,
                                ),
                            )

                        override fun onPasteClipboard() = Unit

                        override fun onPinClipboard() = Unit
                    },
                )
            }
        }
    }
}
