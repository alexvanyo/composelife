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

package com.alexvanyo.composelife.ui.app.action

import androidx.compose.animation.AnimatedVisibility
import androidx.compose.animation.animateColorAsState
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.ExperimentalLayoutApi
import androidx.compose.foundation.layout.FlowRow
import androidx.compose.material.icons.Icons
import androidx.compose.material.icons.filled.AutoMode
import androidx.compose.material.icons.filled.Cancel
import androidx.compose.material.icons.filled.CloseFullscreen
import androidx.compose.material.icons.filled.ContentCopy
import androidx.compose.material.icons.filled.ContentCut
import androidx.compose.material.icons.filled.ContentPaste
import androidx.compose.material.icons.filled.Done
import androidx.compose.material.icons.filled.ExpandLess
import androidx.compose.material.icons.filled.ExpandMore
import androidx.compose.material.icons.filled.Fullscreen
import androidx.compose.material.icons.filled.FullscreenExit
import androidx.compose.material.icons.filled.OpenInFull
import androidx.compose.material.icons.filled.Pause
import androidx.compose.material.icons.filled.PlayArrow
import androidx.compose.material.icons.filled.SkipNext
import androidx.compose.material3.ExperimentalMaterial3Api
import androidx.compose.material3.Icon
import androidx.compose.material3.IconButton
import androidx.compose.material3.IconButtonDefaults
import androidx.compose.material3.IconToggleButton
import androidx.compose.material3.LocalContentColor
import androidx.compose.material3.MaterialTheme
import androidx.compose.material3.PlainTooltip
import androidx.compose.material3.Surface
import androidx.compose.material3.Text
import androidx.compose.material3.TooltipAnchorPosition
import androidx.compose.material3.TooltipBox
import androidx.compose.material3.TooltipDefaults
import androidx.compose.material3.rememberTooltipState
import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResource
import com.alexvanyo.composelife.ui.app.resources.ApplyPaste
import com.alexvanyo.composelife.ui.app.resources.CancelPaste
import com.alexvanyo.composelife.ui.app.resources.ClearSelection
import com.alexvanyo.composelife.ui.app.resources.Collapse
import com.alexvanyo.composelife.ui.app.resources.Copy
import com.alexvanyo.composelife.ui.app.resources.Cut
import com.alexvanyo.composelife.ui.app.resources.DisableAutofit
import com.alexvanyo.composelife.ui.app.resources.DisableImmersiveMode
import com.alexvanyo.composelife.ui.app.resources.EnableAutofit
import com.alexvanyo.composelife.ui.app.resources.EnableImmersiveMode
import com.alexvanyo.composelife.ui.app.resources.EnterFullSpaceMode
import com.alexvanyo.composelife.ui.app.resources.EnterHomeSpaceMode
import com.alexvanyo.composelife.ui.app.resources.Expand
import com.alexvanyo.composelife.ui.app.resources.Paste
import com.alexvanyo.composelife.ui.app.resources.Pause
import com.alexvanyo.composelife.ui.app.resources.Play
import com.alexvanyo.composelife.ui.app.resources.Step
import com.alexvanyo.composelife.ui.app.resources.Strings
import com.alexvanyo.composelife.ui.cells.SelectionState

@OptIn(ExperimentalMaterial3Api::class, ExperimentalLayoutApi::class)
@Suppress("LongParameterList", "LongMethod", "CyclomaticComplexMethod")
@Composable
fun ActionControlRow(
    actionControlRowState: ActionControlRowState,
    modifier: Modifier = Modifier,
) {
    val color by animateColorAsState(
        targetValue = if (actionControlRowState.isElevated) {
            MaterialTheme.colorScheme.surfaceContainerHigh
        } else {
            MaterialTheme.colorScheme.surfaceContainerLow
        },
    )

    Surface(
        color = color,
        modifier = modifier,
    ) {
        Box(
            contentAlignment = Alignment.Center,
        ) {
            FlowRow {
                val showTimeControls: Boolean
                val showSelectingControls: Boolean
                val showSelectionControls: Boolean

                when (actionControlRowState.selectionState) {
                    SelectionState.NoSelection -> {
                        showTimeControls = true
                        showSelectingControls = false
                        showSelectionControls = false
                    }
                    is SelectionState.SelectingBox -> {
                        showTimeControls = false
                        showSelectingControls = true
                        showSelectionControls = false
                    }
                    is SelectionState.Selection -> {
                        showTimeControls = false
                        showSelectingControls = false
                        showSelectionControls = true
                    }
                }

                AnimatedVisibility(showTimeControls) {
                    TooltipBox(
                        positionProvider = TooltipDefaults.rememberTooltipPositionProvider(TooltipAnchorPosition.Above),
                        tooltip = {
                            PlainTooltip {
                                Text(
                                    parameterizedStringResource(
                                        if (actionControlRowState.isRunning) {
                                            Strings.Pause
                                        } else {
                                            Strings.Play
                                        },
                                    ),
                                )
                            }
                        },
                        state = rememberTooltipState(),
                    ) {
                        IconToggleButton(
                            checked = actionControlRowState.isRunning,
                            onCheckedChange = { actionControlRowState.isRunning = it },
                            colors = IconButtonDefaults.iconToggleButtonColors(
                                checkedContentColor = LocalContentColor.current,
                            ),
                        ) {
                            Icon(
                                imageVector = if (actionControlRowState.isRunning) {
                                    Icons.Filled.Pause
                                } else {
                                    Icons.Filled.PlayArrow
                                },
                                contentDescription = parameterizedStringResource(
                                    if (actionControlRowState.isRunning) {
                                        Strings.Pause
                                    } else {
                                        Strings.Play
                                    },
                                ),
                            )
                        }
                    }
                }

                AnimatedVisibility(showTimeControls) {
                    TooltipBox(
                        positionProvider = TooltipDefaults.rememberTooltipPositionProvider(TooltipAnchorPosition.Above),
                        tooltip = {
                            PlainTooltip {
                                Text(parameterizedStringResource(Strings.Step))
                            }
                        },
                        state = rememberTooltipState(),
                    ) {
                        IconButton(
                            onClick = actionControlRowState::onStep,
                        ) {
                            Icon(
                                imageVector = Icons.Filled.SkipNext,
                                contentDescription = parameterizedStringResource(Strings.Step),
                            )
                        }
                    }
                }

                AnimatedVisibility(showSelectingControls) {
                    TooltipBox(
                        positionProvider = TooltipDefaults.rememberTooltipPositionProvider(TooltipAnchorPosition.Above),
                        tooltip = {
                            PlainTooltip {
                                Text(parameterizedStringResource(Strings.ClearSelection))
                            }
                        },
                        state = rememberTooltipState(),
                    ) {
                        IconButton(
                            onClick = actionControlRowState::onClearSelection,
                        ) {
                            Icon(
                                imageVector = Icons.Filled.Cancel,
                                contentDescription = parameterizedStringResource(Strings.ClearSelection),
                            )
                        }
                    }
                }

                AnimatedVisibility(showSelectingControls) {
                    TooltipBox(
                        positionProvider = TooltipDefaults.rememberTooltipPositionProvider(TooltipAnchorPosition.Above),
                        tooltip = {
                            PlainTooltip {
                                Text(parameterizedStringResource(Strings.Copy))
                            }
                        },
                        state = rememberTooltipState(),
                    ) {
                        IconButton(
                            onClick = actionControlRowState::onCopy,
                        ) {
                            Icon(
                                imageVector = Icons.Filled.ContentCopy,
                                contentDescription = parameterizedStringResource(Strings.Copy),
                            )
                        }
                    }
                }

                AnimatedVisibility(showSelectingControls) {
                    TooltipBox(
                        positionProvider = TooltipDefaults.rememberTooltipPositionProvider(TooltipAnchorPosition.Above),
                        tooltip = {
                            PlainTooltip {
                                Text(parameterizedStringResource(Strings.Cut))
                            }
                        },
                        state = rememberTooltipState(),
                    ) {
                        IconButton(
                            onClick = actionControlRowState::onCut,
                        ) {
                            Icon(
                                imageVector = Icons.Filled.ContentCut,
                                contentDescription = parameterizedStringResource(Strings.Cut),
                            )
                        }
                    }
                }

                AnimatedVisibility(showTimeControls || showSelectingControls) {
                    TooltipBox(
                        positionProvider = TooltipDefaults.rememberTooltipPositionProvider(TooltipAnchorPosition.Above),
                        tooltip = {
                            PlainTooltip {
                                Text(parameterizedStringResource(Strings.Paste))
                            }
                        },
                        state = rememberTooltipState(),
                    ) {
                        IconButton(
                            onClick = actionControlRowState::onPaste,
                        ) {
                            Icon(
                                imageVector = Icons.Filled.ContentPaste,
                                contentDescription = parameterizedStringResource(Strings.Paste),
                            )
                        }
                    }
                }

                AnimatedVisibility(showSelectionControls) {
                    TooltipBox(
                        positionProvider = TooltipDefaults.rememberTooltipPositionProvider(TooltipAnchorPosition.Above),
                        tooltip = {
                            PlainTooltip {
                                Text(parameterizedStringResource(Strings.CancelPaste))
                            }
                        },
                        state = rememberTooltipState(),
                    ) {
                        IconButton(
                            onClick = actionControlRowState::onClearSelection,
                        ) {
                            Icon(
                                imageVector = Icons.Filled.Cancel,
                                contentDescription = parameterizedStringResource(Strings.CancelPaste),
                            )
                        }
                    }
                }

                AnimatedVisibility(showSelectionControls) {
                    TooltipBox(
                        positionProvider = TooltipDefaults.rememberTooltipPositionProvider(TooltipAnchorPosition.Above),
                        tooltip = {
                            PlainTooltip {
                                Text(parameterizedStringResource(Strings.ApplyPaste))
                            }
                        },
                        state = rememberTooltipState(),
                    ) {
                        IconButton(
                            onClick = actionControlRowState::onApplyPaste,
                        ) {
                            Icon(
                                imageVector = Icons.Filled.Done,
                                contentDescription = parameterizedStringResource(Strings.ApplyPaste),
                            )
                        }
                    }
                }

                TooltipBox(
                    positionProvider = TooltipDefaults.rememberTooltipPositionProvider(TooltipAnchorPosition.Above),
                    tooltip = {
                        PlainTooltip {
                            Text(
                                parameterizedStringResource(
                                    if (actionControlRowState.isViewportTracking) {
                                        Strings.DisableAutofit
                                    } else {
                                        Strings.EnableAutofit
                                    },
                                ),
                            )
                        }
                    },
                    state = rememberTooltipState(),
                ) {
                    IconToggleButton(
                        checked = actionControlRowState.isViewportTracking,
                        onCheckedChange = { actionControlRowState.isViewportTracking = it },
                    ) {
                        Icon(
                            imageVector = Icons.Filled.AutoMode,
                            contentDescription = parameterizedStringResource(
                                if (actionControlRowState.isViewportTracking) {
                                    Strings.DisableAutofit
                                } else {
                                    Strings.EnableAutofit
                                },
                            ),
                        )
                    }
                }

                AnimatedVisibility(actionControlRowState.showImmersiveModeControl) {
                    TooltipBox(
                        positionProvider = TooltipDefaults.rememberTooltipPositionProvider(TooltipAnchorPosition.Above),
                        tooltip = {
                            PlainTooltip {
                                Text(
                                    parameterizedStringResource(
                                        if (actionControlRowState.isImmersiveMode) {
                                            Strings.DisableImmersiveMode
                                        } else {
                                            Strings.EnableImmersiveMode
                                        },
                                    ),
                                )
                            }
                        },
                        state = rememberTooltipState(),
                    ) {
                        IconToggleButton(
                            checked = actionControlRowState.isImmersiveMode,
                            onCheckedChange = { actionControlRowState.isImmersiveMode = it },
                        ) {
                            Icon(
                                imageVector = if (actionControlRowState.isImmersiveMode) {
                                    Icons.Default.FullscreenExit
                                } else {
                                    Icons.Default.Fullscreen
                                },
                                contentDescription = parameterizedStringResource(
                                    if (actionControlRowState.isImmersiveMode) {
                                        Strings.DisableImmersiveMode
                                    } else {
                                        Strings.EnableImmersiveMode
                                    },
                                ),
                            )
                        }
                    }
                }

                AnimatedVisibility(actionControlRowState.showFullSpaceModeControl) {
                    TooltipBox(
                        positionProvider = TooltipDefaults.rememberTooltipPositionProvider(TooltipAnchorPosition.Above),
                        tooltip = {
                            PlainTooltip {
                                Text(
                                    parameterizedStringResource(
                                        if (actionControlRowState.isFullSpaceMode) {
                                            Strings.EnterHomeSpaceMode
                                        } else {
                                            Strings.EnterFullSpaceMode
                                        },
                                    ),
                                )
                            }
                        },
                        state = rememberTooltipState(),
                    ) {
                        IconButton(
                            onClick = {
                                actionControlRowState.isFullSpaceMode = !actionControlRowState.isFullSpaceMode
                            },
                        ) {
                            Icon(
                                imageVector = if (actionControlRowState.isFullSpaceMode) {
                                    Icons.Default.CloseFullscreen
                                } else {
                                    Icons.Default.OpenInFull
                                },
                                contentDescription = parameterizedStringResource(
                                    if (actionControlRowState.isFullSpaceMode) {
                                        Strings.EnterHomeSpaceMode
                                    } else {
                                        Strings.EnterFullSpaceMode
                                    },
                                ),
                            )
                        }
                    }
                }

                TooltipBox(
                    positionProvider = TooltipDefaults.rememberTooltipPositionProvider(TooltipAnchorPosition.Above),
                    tooltip = {
                        PlainTooltip {
                            Text(
                                parameterizedStringResource(
                                    if (actionControlRowState.isExpanded) {
                                        Strings.Collapse
                                    } else {
                                        Strings.Expand
                                    },
                                ),
                            )
                        }
                    },
                    state = rememberTooltipState(),
                ) {
                    IconToggleButton(
                        checked = actionControlRowState.isExpanded,
                        onCheckedChange = { actionControlRowState.isExpanded = it },
                        colors = IconButtonDefaults.iconToggleButtonColors(
                            checkedContentColor = LocalContentColor.current,
                        ),
                    ) {
                        Icon(
                            imageVector = if (actionControlRowState.isExpanded) {
                                Icons.Filled.ExpandMore
                            } else {
                                Icons.Filled.ExpandLess
                            },
                            contentDescription = parameterizedStringResource(
                                if (actionControlRowState.isExpanded) {
                                    Strings.Collapse
                                } else {
                                    Strings.Expand
                                },
                            ),
                        )
                    }
                }
            }
        }
    }
}
