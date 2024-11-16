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
import com.airbnb.android.showkase.annotation.ShowkaseComposable
import com.alexvanyo.composelife.model.CellStateFormat
import com.alexvanyo.composelife.model.DeserializationResult
import com.alexvanyo.composelife.patterns.GliderPattern
import com.alexvanyo.composelife.ui.app.entrypoints.WithPreviewDependencies
import com.alexvanyo.composelife.ui.mobile.ComposeLifeTheme
import com.alexvanyo.composelife.ui.util.ThemePreviews
import kotlin.uuid.Uuid

@ShowkaseComposable
@ThemePreviews
@Composable
internal fun ClipboardWatchingSectionOnboardingPreview(modifier: Modifier = Modifier) {
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
private fun ClipboardWatchingSectionDisabledPreview(modifier: Modifier = Modifier) {
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

@ShowkaseComposable
@ThemePreviews
@Composable
internal fun ClipboardWatchingSectionEnabledLoadingPreview(modifier: Modifier = Modifier) {
    WithPreviewDependencies {
        ComposeLifeTheme {
            Surface(modifier) {
                ClipboardWatchingSection(
                    clipboardWatchingState = object : ClipboardWatchingState.ClipboardWatchingEnabled {
                        override val useSharedElementForCellStatePreviews: Boolean = false
                        override val isLoading = true
                        override val clipboardPreviewStates: List<ClipboardPreviewState> = emptyList()
                        override val pinnedClipboardPreviewStates: List<PinnedClipboardPreviewState> = emptyList()
                    },
                )
            }
        }
    }
}

@ShowkaseComposable
@ThemePreviews
@Composable
internal fun ClipboardWatchingSectionEnabledUnsuccessfulPreview(modifier: Modifier = Modifier) {
    WithPreviewDependencies {
        ComposeLifeTheme {
            Surface(modifier) {
                ClipboardWatchingSection(
                    clipboardWatchingState = object : ClipboardWatchingState.ClipboardWatchingEnabled {
                        override val useSharedElementForCellStatePreviews: Boolean = false
                        override val isLoading: Boolean = true
                        override val clipboardPreviewStates: List<ClipboardPreviewState> = listOf(
                            object : ClipboardPreviewState {
                                override val id = Uuid.random()
                                override val deserializationResult: DeserializationResult =
                                    DeserializationResult.Unsuccessful(
                                        warnings = emptyList(),
                                        errors = emptyList(),
                                    )
                                override val isPinned: Boolean = false

                                override fun onPaste() = Unit
                                override fun onPinChanged() = Unit
                                override fun onViewDeserializationInfo() = Unit
                            },
                        )
                        override val pinnedClipboardPreviewStates: List<PinnedClipboardPreviewState> = emptyList()
                    },
                )
            }
        }
    }
}

@ShowkaseComposable
@ThemePreviews
@Composable
internal fun ClipboardWatchingSectionEnabledSuccessfulPreview(modifier: Modifier = Modifier) {
    WithPreviewDependencies {
        ComposeLifeTheme {
            Surface(modifier) {
                ClipboardWatchingSection(
                    clipboardWatchingState = object : ClipboardWatchingState.ClipboardWatchingEnabled {
                        override val useSharedElementForCellStatePreviews: Boolean = false
                        override val isLoading: Boolean = true
                        override val clipboardPreviewStates: List<ClipboardPreviewState> = listOf(
                            object : ClipboardPreviewState {
                                override val id = Uuid.random()
                                override val deserializationResult: DeserializationResult =
                                    DeserializationResult.Successful(
                                        cellState = GliderPattern.seedCellState,
                                        warnings = emptyList(),
                                        format = CellStateFormat.FixedFormat.RunLengthEncoding,
                                    )
                                override val isPinned: Boolean = false

                                override fun onPaste() = Unit
                                override fun onPinChanged() = Unit
                                override fun onViewDeserializationInfo() = Unit
                            },
                        )
                        override val pinnedClipboardPreviewStates: List<PinnedClipboardPreviewState> = emptyList()
                    },
                )
            }
        }
    }
}
