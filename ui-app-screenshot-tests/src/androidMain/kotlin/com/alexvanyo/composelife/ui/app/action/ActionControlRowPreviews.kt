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

import androidx.compose.runtime.Composable
import androidx.compose.ui.unit.IntOffset
import com.airbnb.android.showkase.annotation.ShowkaseComposable
import com.alexvanyo.composelife.model.CellState
import com.alexvanyo.composelife.model.emptyCellState
import com.alexvanyo.composelife.ui.app.ctxs.WithPreviewDependencies
import com.alexvanyo.composelife.ui.cells.SelectionState
import com.alexvanyo.composelife.ui.mobile.ComposeLifeTheme
import com.alexvanyo.composelife.ui.util.ThemePreviews

@ShowkaseComposable
@ThemePreviews
@Composable
internal fun CollapsedRunningActionControlRowPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            ActionControlRow(
                actionControlRowState = object : ActionControlRowState {
                    override val isElevated = false
                    override var isRunning = true
                    override var isExpanded = false
                    override var isViewportTracking = false
                    override val showImmersiveModeControl = true
                    override var isImmersiveMode = false
                    override val showFullSpaceModeControl = false
                    override var isFullSpaceMode = false
                    override val selectionState = SelectionState.NoSelection
                    override fun onStep() = Unit
                    override fun onClearSelection() = Unit
                    override fun onCopy() = Unit
                    override fun onCut() = Unit
                    override fun onPaste() = Unit
                    override fun onApplyPaste() = Unit
                },
            )
        }
    }
}

@ShowkaseComposable
@ThemePreviews
@Composable
internal fun CollapsedPausedActionControlRowPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            ActionControlRow(
                actionControlRowState = object : ActionControlRowState {
                    override val isElevated = false
                    override var isRunning = false
                    override var isExpanded = false
                    override var isViewportTracking = false
                    override val showImmersiveModeControl = true
                    override var isImmersiveMode = false
                    override val showFullSpaceModeControl = false
                    override var isFullSpaceMode = false
                    override val selectionState = SelectionState.NoSelection
                    override fun onStep() = Unit
                    override fun onClearSelection() = Unit
                    override fun onCopy() = Unit
                    override fun onCut() = Unit
                    override fun onPaste() = Unit
                    override fun onApplyPaste() = Unit
                },
            )
        }
    }
}

@ShowkaseComposable
@ThemePreviews
@Composable
internal fun ExpandedActionControlRowPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            ActionControlRow(
                actionControlRowState = object : ActionControlRowState {
                    override val isElevated = false
                    override var isRunning = true
                    override var isExpanded = true
                    override var isViewportTracking = false
                    override val showImmersiveModeControl = true
                    override var isImmersiveMode = false
                    override val showFullSpaceModeControl = false
                    override var isFullSpaceMode = false
                    override val selectionState = SelectionState.NoSelection
                    override fun onStep() = Unit
                    override fun onClearSelection() = Unit
                    override fun onCopy() = Unit
                    override fun onCut() = Unit
                    override fun onPaste() = Unit
                    override fun onApplyPaste() = Unit
                },
            )
        }
    }
}

@ShowkaseComposable
@ThemePreviews
@Composable
internal fun ViewportTrackingActionControlRowPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            ActionControlRow(
                actionControlRowState = object : ActionControlRowState {
                    override val isElevated = false
                    override var isRunning = false
                    override var isExpanded = false
                    override var isViewportTracking = true
                    override val showImmersiveModeControl = true
                    override var isImmersiveMode = false
                    override val showFullSpaceModeControl = false
                    override var isFullSpaceMode = false
                    override val selectionState = SelectionState.NoSelection
                    override fun onStep() = Unit
                    override fun onClearSelection() = Unit
                    override fun onCopy() = Unit
                    override fun onCut() = Unit
                    override fun onPaste() = Unit
                    override fun onApplyPaste() = Unit
                },
            )
        }
    }
}

@ShowkaseComposable
@ThemePreviews
@Composable
internal fun ImmersiveModeActionControlRowPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            ActionControlRow(
                actionControlRowState = object : ActionControlRowState {
                    override val isElevated = false
                    override var isRunning = false
                    override var isExpanded = false
                    override var isViewportTracking = true
                    override val showImmersiveModeControl = true
                    override var isImmersiveMode = true
                    override val showFullSpaceModeControl = false
                    override var isFullSpaceMode = false
                    override val selectionState = SelectionState.NoSelection
                    override fun onStep() = Unit
                    override fun onClearSelection() = Unit
                    override fun onCopy() = Unit
                    override fun onCut() = Unit
                    override fun onPaste() = Unit
                    override fun onApplyPaste() = Unit
                },
            )
        }
    }
}

@ShowkaseComposable
@ThemePreviews
@Composable
internal fun InFullSpaceModeActionControlRowPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            ActionControlRow(
                actionControlRowState = object : ActionControlRowState {
                    override val isElevated = false
                    override var isRunning = false
                    override var isExpanded = false
                    override var isViewportTracking = true
                    override val showImmersiveModeControl = false
                    override var isImmersiveMode = false
                    override val showFullSpaceModeControl = true
                    override var isFullSpaceMode = true
                    override val selectionState = SelectionState.NoSelection
                    override fun onStep() = Unit
                    override fun onClearSelection() = Unit
                    override fun onCopy() = Unit
                    override fun onCut() = Unit
                    override fun onPaste() = Unit
                    override fun onApplyPaste() = Unit
                },
            )
        }
    }
}

@ShowkaseComposable
@ThemePreviews
@Composable
internal fun InHomeSpaceModeActionControlRowPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            ActionControlRow(
                actionControlRowState = object : ActionControlRowState {
                    override val isElevated = false
                    override var isRunning = false
                    override var isExpanded = false
                    override var isViewportTracking = true
                    override val showImmersiveModeControl = false
                    override var isImmersiveMode = false
                    override val showFullSpaceModeControl = true
                    override var isFullSpaceMode = false
                    override val selectionState = SelectionState.NoSelection
                    override fun onStep() = Unit
                    override fun onClearSelection() = Unit
                    override fun onCopy() = Unit
                    override fun onCut() = Unit
                    override fun onPaste() = Unit
                    override fun onApplyPaste() = Unit
                },
            )
        }
    }
}

@ShowkaseComposable
@ThemePreviews
@Composable
internal fun SelectingBoxActionControlRowPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            ActionControlRow(
                actionControlRowState = object : ActionControlRowState {
                    override val isElevated = false
                    override var isRunning = false
                    override var isExpanded = false
                    override var isViewportTracking = false
                    override val showImmersiveModeControl = true
                    override var isImmersiveMode = false
                    override val showFullSpaceModeControl = false
                    override var isFullSpaceMode = false
                    override val selectionState = SelectionState.SelectingBox.FixedSelectingBox(
                        topLeft = IntOffset.Zero,
                        width = 1,
                        height = 1,
                        previousTransientSelectingBox = null,
                    )
                    override fun onStep() = Unit
                    override fun onClearSelection() = Unit
                    override fun onCopy() = Unit
                    override fun onCut() = Unit
                    override fun onPaste() = Unit
                    override fun onApplyPaste() = Unit
                },
            )
        }
    }
}

@ShowkaseComposable
@ThemePreviews
@Composable
internal fun SelectionActionControlRowPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            ActionControlRow(
                actionControlRowState = object : ActionControlRowState {
                    override val isElevated = false
                    override var isRunning = false
                    override var isExpanded = false
                    override var isViewportTracking = false
                    override val showImmersiveModeControl = true
                    override var isImmersiveMode = false
                    override val showFullSpaceModeControl = false
                    override var isFullSpaceMode = false
                    override val selectionState = SelectionState.Selection(
                        cellState = emptyCellState(),
                        offset = IntOffset.Zero,
                    )
                    override fun onStep() = Unit
                    override fun onClearSelection() = Unit
                    override fun onCopy() = Unit
                    override fun onCut() = Unit
                    override fun onPaste() = Unit
                    override fun onApplyPaste() = Unit
                },
            )
        }
    }
}

@ShowkaseComposable
@ThemePreviews
@Composable
internal fun ElevatedExpandedActionControlRowPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            ActionControlRow(
                actionControlRowState = object : ActionControlRowState {
                    override val isElevated = true
                    override var isRunning = true
                    override var isExpanded = true
                    override var isViewportTracking = false
                    override val showImmersiveModeControl = true
                    override var isImmersiveMode = false
                    override val showFullSpaceModeControl = false
                    override var isFullSpaceMode = false
                    override val selectionState = SelectionState.Selection(
                        cellState = emptyCellState(),
                        offset = IntOffset.Zero,
                    )
                    override fun onStep() = Unit
                    override fun onClearSelection() = Unit
                    override fun onCopy() = Unit
                    override fun onCut() = Unit
                    override fun onPaste() = Unit
                    override fun onApplyPaste() = Unit
                },
            )
        }
    }
}
