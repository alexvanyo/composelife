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
import com.alexvanyo.composelife.model.emptyCellState
import com.alexvanyo.composelife.ui.app.entrypoints.WithPreviewDependencies
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
                isElevated = false,
                isRunning = true,
                setIsRunning = {},
                onStep = {},
                isExpanded = false,
                setIsExpanded = {},
                isViewportTracking = false,
                setIsViewportTracking = {},
                isImmersiveMode = false,
                setIsImmersiveMode = {},
                selectionState = SelectionState.NoSelection,
                onClearSelection = {},
                onCopy = {},
                onCut = {},
                onPaste = {},
                onApplyPaste = {},
            )
        }
    }
}

@ThemePreviews
@Composable
internal fun CollapsedPausedActionControlRowPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            ActionControlRow(
                isElevated = false,
                isRunning = false,
                setIsRunning = {},
                onStep = {},
                isExpanded = false,
                setIsExpanded = {},
                isViewportTracking = false,
                setIsViewportTracking = {},
                isImmersiveMode = false,
                setIsImmersiveMode = {},
                selectionState = SelectionState.NoSelection,
                onClearSelection = {},
                onCopy = {},
                onCut = {},
                onPaste = {},
                onApplyPaste = {},
            )
        }
    }
}

@ThemePreviews
@Composable
internal fun ExpandedActionControlRowPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            ActionControlRow(
                isElevated = false,
                isRunning = true,
                setIsRunning = {},
                onStep = {},
                isExpanded = true,
                setIsExpanded = {},
                isViewportTracking = false,
                setIsViewportTracking = {},
                isImmersiveMode = false,
                setIsImmersiveMode = {},
                selectionState = SelectionState.NoSelection,
                onClearSelection = {},
                onCopy = {},
                onCut = {},
                onPaste = {},
                onApplyPaste = {},
            )
        }
    }
}

@ThemePreviews
@Composable
internal fun ViewportTrackingActionControlRowPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            ActionControlRow(
                isElevated = false,
                isRunning = false,
                setIsRunning = {},
                onStep = {},
                isExpanded = false,
                setIsExpanded = {},
                isViewportTracking = true,
                setIsViewportTracking = {},
                isImmersiveMode = false,
                setIsImmersiveMode = {},
                selectionState = SelectionState.NoSelection,
                onClearSelection = {},
                onCopy = {},
                onCut = {},
                onPaste = {},
                onApplyPaste = {},
            )
        }
    }
}

@ThemePreviews
@Composable
internal fun ImmersiveModeActionControlRowPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            ActionControlRow(
                isElevated = false,
                isRunning = false,
                setIsRunning = {},
                onStep = {},
                isExpanded = false,
                setIsExpanded = {},
                isViewportTracking = true,
                setIsViewportTracking = {},
                isImmersiveMode = true,
                setIsImmersiveMode = {},
                selectionState = SelectionState.NoSelection,
                onClearSelection = {},
                onCopy = {},
                onCut = {},
                onPaste = {},
                onApplyPaste = {},
            )
        }
    }
}

@ThemePreviews
@Composable
internal fun SelectingBoxActionControlRowPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            ActionControlRow(
                isElevated = false,
                isRunning = false,
                setIsRunning = {},
                onStep = {},
                isExpanded = false,
                setIsExpanded = {},
                isViewportTracking = false,
                setIsViewportTracking = {},
                isImmersiveMode = false,
                setIsImmersiveMode = {},
                selectionState = SelectionState.SelectingBox.FixedSelectingBox(
                    topLeft = IntOffset.Zero,
                    width = 1,
                    height = 1,
                    previousTransientSelectingBox = null,
                ),
                onClearSelection = {},
                onCopy = {},
                onCut = {},
                onPaste = {},
                onApplyPaste = {},
            )
        }
    }
}

@ThemePreviews
@Composable
internal fun SelectionActionControlRowPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            ActionControlRow(
                isElevated = false,
                isRunning = false,
                setIsRunning = {},
                onStep = {},
                isExpanded = false,
                setIsExpanded = {},
                isViewportTracking = false,
                setIsViewportTracking = {},
                isImmersiveMode = false,
                setIsImmersiveMode = {},
                selectionState = SelectionState.Selection(
                    cellState = emptyCellState(),
                    offset = IntOffset.Zero,
                ),
                onClearSelection = {},
                onCopy = {},
                onCut = {},
                onPaste = {},
                onApplyPaste = {},
            )
        }
    }
}

@ThemePreviews
@Composable
internal fun ElevatedExpandedActionControlRowPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            ActionControlRow(
                isElevated = true,
                isRunning = true,
                setIsRunning = {},
                onStep = {},
                isExpanded = true,
                setIsExpanded = {},
                isViewportTracking = false,
                setIsViewportTracking = {},
                isImmersiveMode = false,
                setIsImmersiveMode = {},
                selectionState = SelectionState.NoSelection,
                onClearSelection = {},
                onCopy = {},
                onCut = {},
                onPaste = {},
                onApplyPaste = {},
            )
        }
    }
}
