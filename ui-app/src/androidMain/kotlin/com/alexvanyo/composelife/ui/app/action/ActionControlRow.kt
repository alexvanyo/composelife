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

import androidx.compose.animation.core.animateDpAsState
import androidx.compose.foundation.layout.Arrangement
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.Row
import androidx.compose.material.icons.Icons
import androidx.compose.material.icons.filled.AutoMode
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
import androidx.compose.material3.PlainTooltipBox
import androidx.compose.material3.Surface
import androidx.compose.material3.Text
import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.res.stringResource
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.ui.app.R
import com.alexvanyo.composelife.ui.app.entrypoints.WithPreviewDependencies
import com.alexvanyo.composelife.ui.app.theme.ComposeLifeTheme
import com.alexvanyo.composelife.ui.util.ThemePreviews

@OptIn(ExperimentalMaterial3Api::class)
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
            Row(
                horizontalArrangement = Arrangement.spacedBy(8.dp),
            ) {
                PlainTooltipBox(
                    tooltip = {
                        Text(
                            if (isRunning) {
                                stringResource(id = R.string.pause)
                            } else {
                                stringResource(id = R.string.play)
                            },
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
                            contentDescription = if (isRunning) {
                                stringResource(id = R.string.pause)
                            } else {
                                stringResource(id = R.string.play)
                            },
                        )
                    }
                }

                PlainTooltipBox(
                    tooltip = {
                        Text(stringResource(id = R.string.step))
                    },
                ) {
                    IconButton(
                        onClick = onStep,
                        modifier = Modifier.tooltipTrigger(),
                    ) {
                        Icon(
                            imageVector = Icons.Filled.SkipNext,
                            contentDescription = stringResource(id = R.string.step),
                        )
                    }
                }

                PlainTooltipBox(
                    tooltip = {
                        Text(
                            if (isViewportTracking) {
                                stringResource(id = R.string.disable_autofit)
                            } else {
                                stringResource(id = R.string.enable_autofit)
                            },
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
                            contentDescription = if (isViewportTracking) {
                                stringResource(id = R.string.disable_autofit)
                            } else {
                                stringResource(id = R.string.enable_autofit)
                            },
                        )
                    }
                }

                PlainTooltipBox(
                    tooltip = {
                        Text(
                            if (isExpanded) {
                                stringResource(id = R.string.collapse)
                            } else {
                                stringResource(id = R.string.expand)
                            },
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
                            contentDescription = if (isExpanded) {
                                stringResource(id = R.string.collapse)
                            } else {
                                stringResource(id = R.string.expand)
                            },
                        )
                    }
                }
            }
        }
    }
}

@ThemePreviews
@Composable
fun CollapsedRunningActionControlRowPreview() {
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
            )
        }
    }
}

@ThemePreviews
@Composable
fun CollapsedPausedActionControlRowPreview() {
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
            )
        }
    }
}

@ThemePreviews
@Composable
fun ExpandedActionControlRowPreview() {
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
            )
        }
    }
}

@ThemePreviews
@Composable
fun ViewportTrackingActionControlRowPreview() {
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
            )
        }
    }
}

@ThemePreviews
@Composable
fun ElevatedExpandedActionControlRowPreview() {
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
            )
        }
    }
}
