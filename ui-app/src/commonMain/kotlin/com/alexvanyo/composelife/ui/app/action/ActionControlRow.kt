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
import androidx.compose.animation.animateContentSize
import androidx.compose.animation.core.animateDpAsState
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.Row
import androidx.compose.material.icons.Icons
import androidx.compose.material.icons.filled.AutoMode
import androidx.compose.material.icons.filled.Cancel
import androidx.compose.material.icons.filled.ContentCopy
import androidx.compose.material.icons.filled.ContentCut
import androidx.compose.material.icons.filled.ContentPaste
import androidx.compose.material.icons.filled.Done
import androidx.compose.material.icons.filled.ExpandLess
import androidx.compose.material.icons.filled.ExpandMore
import androidx.compose.material.icons.filled.Pause
import androidx.compose.material.icons.filled.PlayArrow
import androidx.compose.material.icons.filled.SkipNext
import androidx.compose.material3.ExperimentalMaterial3Api
import androidx.compose.material3.Icon
import androidx.compose.material3.IconButton
import androidx.compose.material3.IconButtonDefaults
import androidx.compose.material3.IconToggleButton
import androidx.compose.material3.LocalContentColor
import androidx.compose.material3.Surface
import androidx.compose.material3.Text
import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.ui.Alignment
import androidx.compose.ui.ExperimentalComposeUiApi
import androidx.compose.ui.Modifier
import androidx.compose.ui.layout.LookaheadScope
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResource
import com.alexvanyo.composelife.ui.app.cells.SelectionState
import com.alexvanyo.composelife.ui.app.component.PlainTooltipBox
import com.alexvanyo.composelife.ui.app.resources.ApplyPaste
import com.alexvanyo.composelife.ui.app.resources.CancelPaste
import com.alexvanyo.composelife.ui.app.resources.ClearSelection
import com.alexvanyo.composelife.ui.app.resources.Collapse
import com.alexvanyo.composelife.ui.app.resources.Copy
import com.alexvanyo.composelife.ui.app.resources.Cut
import com.alexvanyo.composelife.ui.app.resources.DisableAutofit
import com.alexvanyo.composelife.ui.app.resources.EnableAutofit
import com.alexvanyo.composelife.ui.app.resources.Expand
import com.alexvanyo.composelife.ui.app.resources.Paste
import com.alexvanyo.composelife.ui.app.resources.Pause
import com.alexvanyo.composelife.ui.app.resources.Play
import com.alexvanyo.composelife.ui.app.resources.Step
import com.alexvanyo.composelife.ui.app.resources.Strings

@OptIn(ExperimentalMaterial3Api::class, ExperimentalComposeUiApi::class)
@Suppress("LongParameterList", "LongMethod")
@Composable
fun ActionControlRow(
    isElevated: Boolean,
    isRunning: Boolean,
    setIsRunning: (Boolean) -> Unit,
    onStep: () -> Unit,
    isExpanded: Boolean,
    setIsExpanded: (Boolean) -> Unit,
    isViewportTracking: Boolean,
    setIsViewportTracking: (Boolean) -> Unit,
    selectionState: SelectionState,
    onClearSelection: () -> Unit,
    onCopy: () -> Unit,
    onCut: () -> Unit,
    modifier: Modifier = Modifier,
) {
    val elevation by animateDpAsState(targetValue = if (isElevated) 3.dp else 0.dp)

    Surface(
        tonalElevation = elevation,
        modifier = modifier,
    ) {
        Box(
            contentAlignment = Alignment.Center,
        ) {
            LookaheadScope {
                Row(
                    modifier = Modifier.animateContentSize(),
                ) {
                    val showTimeControls: Boolean
                    val showSelectingControls: Boolean
                    val showSelectionControls: Boolean

                    when (selectionState) {
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
                        PlainTooltipBox(
                            tooltip = {
                                Text(
                                    parameterizedStringResource(
                                        if (isRunning) {
                                            Strings.Pause
                                        } else {
                                            Strings.Play
                                        },
                                    ),
                                )
                            },
                        ) {
                            IconToggleButton(
                                checked = isRunning,
                                onCheckedChange = setIsRunning,
                                colors = IconButtonDefaults.iconToggleButtonColors(
                                    checkedContentColor = LocalContentColor.current,
                                ),
                                modifier = Modifier.tooltipTrigger(),
                            ) {
                                Icon(
                                    imageVector = if (isRunning) {
                                        Icons.Filled.Pause
                                    } else {
                                        Icons.Filled.PlayArrow
                                    },
                                    contentDescription = parameterizedStringResource(
                                        if (isRunning) {
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
                        PlainTooltipBox(
                            tooltip = {
                                Text(parameterizedStringResource(Strings.Step))
                            },
                        ) {
                            IconButton(
                                onClick = onStep,
                                modifier = Modifier.tooltipTrigger(),
                            ) {
                                Icon(
                                    imageVector = Icons.Filled.SkipNext,
                                    contentDescription = parameterizedStringResource(Strings.Step),
                                )
                            }
                        }
                    }

                    AnimatedVisibility(showSelectingControls) {
                        PlainTooltipBox(
                            tooltip = {
                                Text(parameterizedStringResource(Strings.ClearSelection))
                            },
                        ) {
                            IconButton(
                                onClick = onClearSelection,
                                modifier = Modifier.tooltipTrigger(),
                            ) {
                                Icon(
                                    imageVector = Icons.Filled.Cancel,
                                    contentDescription = parameterizedStringResource(Strings.ClearSelection),
                                )
                            }
                        }
                    }

                    AnimatedVisibility(showSelectingControls) {
                        PlainTooltipBox(
                            tooltip = {
                                Text(parameterizedStringResource(Strings.Copy))
                            },
                        ) {
                            IconButton(
                                onClick = onCopy,
                                modifier = Modifier.tooltipTrigger(),
                            ) {
                                Icon(
                                    imageVector = Icons.Filled.ContentCopy,
                                    contentDescription = parameterizedStringResource(Strings.Copy),
                                )
                            }
                        }
                    }

                    AnimatedVisibility(showSelectingControls) {
                        PlainTooltipBox(
                            tooltip = {
                                Text(parameterizedStringResource(Strings.Cut))
                            },
                        ) {
                            IconButton(
                                onClick = onCut,
                                modifier = Modifier.tooltipTrigger(),
                            ) {
                                Icon(
                                    imageVector = Icons.Filled.ContentCut,
                                    contentDescription = parameterizedStringResource(Strings.Cut),
                                )
                            }
                        }
                    }

                    AnimatedVisibility(showTimeControls || showSelectingControls) {
                        PlainTooltipBox(
                            tooltip = {
                                Text(parameterizedStringResource(Strings.Paste))
                            },
                        ) {
                            IconButton(
                                onClick = {},
                                modifier = Modifier.tooltipTrigger(),
                            ) {
                                Icon(
                                    imageVector = Icons.Filled.ContentPaste,
                                    contentDescription = parameterizedStringResource(Strings.Paste),
                                )
                            }
                        }
                    }

                    AnimatedVisibility(showSelectionControls) {
                        PlainTooltipBox(
                            tooltip = {
                                Text(parameterizedStringResource(Strings.CancelPaste))
                            },
                        ) {
                            IconButton(
                                onClick = {},
                                modifier = Modifier.tooltipTrigger(),
                            ) {
                                Icon(
                                    imageVector = Icons.Filled.Cancel,
                                    contentDescription = parameterizedStringResource(Strings.CancelPaste),
                                )
                            }
                        }
                    }

                    AnimatedVisibility(showSelectionControls) {
                        PlainTooltipBox(
                            tooltip = {
                                Text(parameterizedStringResource(Strings.ApplyPaste))
                            },
                        ) {
                            IconButton(
                                onClick = {},
                                modifier = Modifier.tooltipTrigger(),
                            ) {
                                Icon(
                                    imageVector = Icons.Filled.Done,
                                    contentDescription = parameterizedStringResource(Strings.ApplyPaste),
                                )
                            }
                        }
                    }

                    PlainTooltipBox(
                        tooltip = {
                            Text(
                                parameterizedStringResource(
                                    if (isViewportTracking) {
                                        Strings.DisableAutofit
                                    } else {
                                        Strings.EnableAutofit
                                    },
                                ),
                            )
                        },
                    ) {
                        IconToggleButton(
                            checked = isViewportTracking,
                            onCheckedChange = setIsViewportTracking,
                            modifier = Modifier.tooltipTrigger(),
                        ) {
                            Icon(
                                imageVector = Icons.Filled.AutoMode,
                                contentDescription = parameterizedStringResource(
                                    if (isViewportTracking) {
                                        Strings.DisableAutofit
                                    } else {
                                        Strings.EnableAutofit
                                    },
                                ),
                            )
                        }
                    }

                    PlainTooltipBox(
                        tooltip = {
                            Text(
                                parameterizedStringResource(
                                    if (isExpanded) {
                                        Strings.Collapse
                                    } else {
                                        Strings.Expand
                                    },
                                ),
                            )
                        },
                    ) {
                        IconToggleButton(
                            checked = isExpanded,
                            onCheckedChange = setIsExpanded,
                            colors = IconButtonDefaults.iconToggleButtonColors(
                                checkedContentColor = LocalContentColor.current,
                            ),
                            modifier = Modifier.tooltipTrigger(),
                        ) {
                            Icon(
                                imageVector = if (isExpanded) {
                                    Icons.Filled.ExpandMore
                                } else {
                                    Icons.Filled.ExpandLess
                                },
                                contentDescription = parameterizedStringResource(
                                    if (isExpanded) {
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
}
