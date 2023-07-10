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

package com.alexvanyo.composelife.ui.app.cells

import androidx.compose.runtime.Composable
import com.alexvanyo.composelife.model.GameOfLifeState
import com.alexvanyo.composelife.model.MutableGameOfLifeState
import com.alexvanyo.composelife.model.toCellState
import com.alexvanyo.composelife.ui.app.entrypoints.WithPreviewDependencies
import com.alexvanyo.composelife.ui.app.theme.ComposeLifeTheme
import com.alexvanyo.composelife.ui.util.ThemePreviews

@ThemePreviews
@Composable
fun NavigableImmutableCellWindowPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            ImmutableCellWindow(
                gameOfLifeState = GameOfLifeState(
                    setOf(
                        0 to 0,
                        0 to 2,
                        0 to 4,
                        2 to 0,
                        2 to 2,
                        2 to 4,
                        4 to 0,
                        4 to 2,
                        4 to 4,
                    ).toCellState(),
                ),
            )
        }
    }
}

@ThemePreviews
@Composable
fun TrackingImmutableCellWindowPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            val gameOfLifeState = GameOfLifeState(
                setOf(
                    0 to 0,
                    0 to 2,
                    0 to 4,
                    2 to 0,
                    2 to 2,
                    2 to 4,
                    4 to 0,
                    4 to 2,
                    4 to 4,
                ).toCellState(),
            )
            val trackingCellWindowState = rememberTrackingCellWindowState(gameOfLifeState)

            ImmutableCellWindow(
                gameOfLifeState = gameOfLifeState,
                viewportInteractionConfig = ViewportInteractionConfig.Tracking(
                    trackingCellWindowState = trackingCellWindowState,
                ),
            )
        }
    }
}

@ThemePreviews
@Composable
fun NavigableMutableCellWindowPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            MutableCellWindow(
                gameOfLifeState = MutableGameOfLifeState(
                    setOf(
                        0 to 0,
                        0 to 2,
                        0 to 4,
                        2 to 0,
                        2 to 2,
                        2 to 4,
                        4 to 0,
                        4 to 2,
                        4 to 4,
                    ).toCellState(),
                ),
            )
        }
    }
}

@ThemePreviews
@Composable
fun TrackingMutableCellWindowPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            val gameOfLifeState = GameOfLifeState(
                setOf(
                    0 to 0,
                    0 to 2,
                    0 to 4,
                    2 to 0,
                    2 to 2,
                    2 to 4,
                    4 to 0,
                    4 to 2,
                    4 to 4,
                ).toCellState(),
            )
            val trackingCellWindowState = rememberTrackingCellWindowState(gameOfLifeState)

            MutableCellWindow(
                gameOfLifeState = MutableGameOfLifeState(
                    setOf(
                        0 to 0,
                        0 to 2,
                        0 to 4,
                        2 to 0,
                        2 to 2,
                        2 to 4,
                        4 to 0,
                        4 to 2,
                        4 to 4,
                    ).toCellState(),
                ),
                viewportInteractionConfig = ViewportInteractionConfig.Tracking(
                    trackingCellWindowState = trackingCellWindowState,
                ),
            )
        }
    }
}
