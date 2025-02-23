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

package com.alexvanyo.composelife.ui.cells

import androidx.compose.runtime.Composable
import androidx.compose.runtime.remember
import com.airbnb.android.showkase.annotation.ShowkaseComposable
import com.alexvanyo.composelife.model.GameOfLifeState
import com.alexvanyo.composelife.model.MutableGameOfLifeState
import com.alexvanyo.composelife.model.toCellState
import com.alexvanyo.composelife.sessionvalue.SessionValue
import com.alexvanyo.composelife.ui.cells.entrypoints.WithPreviewDependencies
import com.alexvanyo.composelife.ui.mobile.ComposeLifeTheme
import com.alexvanyo.composelife.ui.util.ThemePreviews
import kotlin.uuid.Uuid

@ShowkaseComposable
@ThemePreviews
@Composable
internal fun NavigableImmutableCellWindowPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            ImmutableCellWindow(
                gameOfLifeState = remember {
                    GameOfLifeState(
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
                },
                cellWindowInteractionState = CellWindowInteractionState(
                    viewportInteractionConfig = ViewportInteractionConfig.Navigable(
                        mutableCellWindowViewportState = rememberMutableCellWindowViewportState(),
                    ),
                    selectionSessionState = SessionValue(
                        sessionId = Uuid.random(),
                        valueId = Uuid.random(),
                        value = SelectionState.NoSelection,
                    ),
                ),
            )
        }
    }
}

@ShowkaseComposable
@ThemePreviews
@Composable
internal fun TrackingImmutableCellWindowPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            val gameOfLifeState = remember {
                GameOfLifeState(
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
            }
            val trackingCellWindowViewportState = rememberTrackingCellWindowViewportState(gameOfLifeState)

            ImmutableCellWindow(
                gameOfLifeState = gameOfLifeState,
                cellWindowInteractionState = CellWindowInteractionState(
                    viewportInteractionConfig = ViewportInteractionConfig.Tracking(
                        trackingCellWindowViewportState = trackingCellWindowViewportState,
                    ),
                    selectionSessionState = SessionValue(
                        sessionId = Uuid.random(),
                        valueId = Uuid.random(),
                        value = SelectionState.NoSelection,
                    ),
                ),
            )
        }
    }
}

@ShowkaseComposable
@ThemePreviews
@Composable
internal fun NavigableMutableCellWindowPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            val mutableCellWindowViewportState = rememberMutableCellWindowViewportState()

            val selectionStateHolder = rememberMutableSelectionStateHolder(
                SessionValue(
                    sessionId = Uuid.random(),
                    valueId = Uuid.random(),
                    value = SelectionState.NoSelection,
                ),
            )

            MutableCellWindow(
                gameOfLifeState = remember {
                    MutableGameOfLifeState(
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
                },
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

@ShowkaseComposable
@ThemePreviews
@Composable
internal fun TrackingMutableCellWindowPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            val gameOfLifeState = remember {
                MutableGameOfLifeState(
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
            }
            val trackingCellWindowViewportState = rememberTrackingCellWindowViewportState(gameOfLifeState)

            val selectionStateHolder = rememberMutableSelectionStateHolder(
                SessionValue(
                    sessionId = Uuid.random(),
                    valueId = Uuid.random(),
                    value = SelectionState.NoSelection,
                ),
            )

            MutableCellWindow(
                gameOfLifeState = gameOfLifeState,
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
