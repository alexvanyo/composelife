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
import com.alexvanyo.composelife.sessionvalue.SessionValue
import com.alexvanyo.composelife.ui.cells.entrypoints.WithPreviewDependencies
import com.alexvanyo.composelife.ui.mobile.ComposeLifeTheme
import com.alexvanyo.composelife.ui.util.ThemePreviews
import com.benasher44.uuid.uuid4

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
                cellWindowInteractionState = CellWindowInteractionState(
                    viewportInteractionConfig = ViewportInteractionConfig.Navigable(
                        mutableCellWindowViewportState = rememberMutableCellWindowViewportState(),
                    ),
                    selectionSessionState = SessionValue(
                        sessionId = uuid4(),
                        valueId = uuid4(),
                        value = SelectionState.NoSelection,
                    ),
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
            val trackingCellWindowViewportState = rememberTrackingCellWindowViewportState(gameOfLifeState)

            ImmutableCellWindow(
                gameOfLifeState = gameOfLifeState,
                cellWindowInteractionState = CellWindowInteractionState(
                    viewportInteractionConfig = ViewportInteractionConfig.Tracking(
                        trackingCellWindowViewportState = trackingCellWindowViewportState,
                    ),
                    selectionSessionState = SessionValue(
                        sessionId = uuid4(),
                        valueId = uuid4(),
                        value = SelectionState.NoSelection,
                    ),
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
            val mutableCellWindowViewportState = rememberMutableCellWindowViewportState()

            val selectionStateHolder = rememberMutableSelectionStateHolder(
                SessionValue(
                    sessionId = uuid4(),
                    valueId = uuid4(),
                    value = SelectionState.NoSelection,
                ),
            )

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
                cellWindowInteractionState = object :
                    MutableCellWindowInteractionState,
                    MutableSelectionStateHolder by selectionStateHolder {
                    override val viewportInteractionConfig = ViewportInteractionConfig.Navigable(
                        mutableCellWindowViewportState = mutableCellWindowViewportState,
                    )
                },
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
            val trackingCellWindowViewportState = rememberTrackingCellWindowViewportState(gameOfLifeState)

            val selectionStateHolder = rememberMutableSelectionStateHolder(
                SessionValue(
                    sessionId = uuid4(),
                    valueId = uuid4(),
                    value = SelectionState.NoSelection,
                ),
            )

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
                cellWindowInteractionState = object :
                    MutableCellWindowInteractionState,
                    MutableSelectionStateHolder by selectionStateHolder {
                    override val viewportInteractionConfig = ViewportInteractionConfig.Tracking(
                        trackingCellWindowViewportState = trackingCellWindowViewportState,
                    )
                },
            )
        }
    }
}
