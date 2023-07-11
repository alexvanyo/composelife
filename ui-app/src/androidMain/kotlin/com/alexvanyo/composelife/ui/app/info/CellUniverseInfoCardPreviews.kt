/*
 * Copyright 2022 The Android Open Source Project
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

package com.alexvanyo.composelife.ui.app.info

import androidx.compose.runtime.Composable
import com.alexvanyo.composelife.ui.app.entrypoints.WithPreviewDependencies
import com.alexvanyo.composelife.ui.app.theme.ComposeLifeTheme
import com.alexvanyo.composelife.ui.util.TargetState
import com.alexvanyo.composelife.ui.util.ThemePreviews

@ThemePreviews
@Composable
fun CellUniverseInfoCardCollapsedPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            CellUniverseInfoCard(
                cellUniverseInfoCardContent = CellUniverseInfoCardContent(
                    cellUniverseInfoCardState = rememberCellUniverseInfoCardState(
                        setIsExpanded = {},
                        expandedTargetState = TargetState.Single(false),
                    ),
                    cellUniverseInfoItemContents = listOf(
                        CellUniverseInfoItemContent(
                            rememberCellUniverseInfoItemState(isChecked = true),
                        ) { "First" },
                        CellUniverseInfoItemContent(
                            rememberCellUniverseInfoItemState(isChecked = true),
                        ) { "Second" },
                        CellUniverseInfoItemContent(
                            rememberCellUniverseInfoItemState(isChecked = true),
                        ) { "Third" },
                    ),
                ),
            )
        }
    }
}

@ThemePreviews
@Composable
fun CellUniverseInfoCardCollapsedSingleSelectionPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            CellUniverseInfoCard(
                cellUniverseInfoCardContent = CellUniverseInfoCardContent(
                    cellUniverseInfoCardState = rememberCellUniverseInfoCardState(
                        setIsExpanded = {},
                        expandedTargetState = TargetState.Single(false),
                    ),
                    cellUniverseInfoItemContents = listOf(
                        CellUniverseInfoItemContent(
                            rememberCellUniverseInfoItemState(isChecked = false),
                        ) { "First" },
                        CellUniverseInfoItemContent(
                            rememberCellUniverseInfoItemState(isChecked = false),
                        ) { "Second" },
                        CellUniverseInfoItemContent(
                            rememberCellUniverseInfoItemState(isChecked = true),
                        ) { "Third" },
                    ),
                ),
            )
        }
    }
}

@ThemePreviews
@Composable
fun CellUniverseInfoCardFullyCollapsedPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            CellUniverseInfoCard(
                cellUniverseInfoCardContent = CellUniverseInfoCardContent(
                    cellUniverseInfoCardState = rememberCellUniverseInfoCardState(
                        setIsExpanded = {},
                        expandedTargetState = TargetState.Single(false),
                    ),
                    cellUniverseInfoItemContents = listOf(
                        CellUniverseInfoItemContent(
                            rememberCellUniverseInfoItemState(isChecked = false),
                        ) { "First" },
                        CellUniverseInfoItemContent(
                            rememberCellUniverseInfoItemState(isChecked = false),
                        ) { "Second" },
                        CellUniverseInfoItemContent(
                            rememberCellUniverseInfoItemState(isChecked = false),
                        ) { "Third" },
                    ),
                ),
            )
        }
    }
}

@ThemePreviews
@Composable
fun CellUniverseInfoCardExpandedPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            CellUniverseInfoCard(
                cellUniverseInfoCardContent = CellUniverseInfoCardContent(
                    cellUniverseInfoCardState = rememberCellUniverseInfoCardState(
                        setIsExpanded = {},
                        expandedTargetState = TargetState.Single(true),
                    ),
                    cellUniverseInfoItemContents = listOf(
                        CellUniverseInfoItemContent(
                            rememberCellUniverseInfoItemState(),
                        ) { "First" },
                        CellUniverseInfoItemContent(
                            rememberCellUniverseInfoItemState(),
                        ) { "Second" },
                        CellUniverseInfoItemContent(
                            rememberCellUniverseInfoItemState(),
                        ) { "Third" },
                    ),
                ),
            )
        }
    }
}
