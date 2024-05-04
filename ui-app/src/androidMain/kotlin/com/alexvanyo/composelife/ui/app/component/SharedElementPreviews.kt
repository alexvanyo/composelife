/*
 * Copyright 2024 The Android Open Source Project
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

package com.alexvanyo.composelife.ui.app.component

import androidx.compose.animation.AnimatedContent
import androidx.compose.animation.ExperimentalSharedTransitionApi
import androidx.compose.animation.SharedTransitionScope
import androidx.compose.foundation.background
import androidx.compose.foundation.clickable
import androidx.compose.foundation.layout.Arrangement
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.ExperimentalLayoutApi
import androidx.compose.foundation.layout.FlowRow
import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.foundation.layout.size
import androidx.compose.material3.Surface
import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.setValue
import androidx.compose.ui.Modifier
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.tooling.preview.Preview
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.ui.app.action.settings.Setting
import com.alexvanyo.composelife.ui.app.action.settings.SettingUi
import com.alexvanyo.composelife.ui.app.entrypoints.WithPreviewDependencies
import com.alexvanyo.composelife.ui.util.TargetState

@OptIn(ExperimentalSharedTransitionApi::class, ExperimentalLayoutApi::class)
@Preview
@Composable
internal fun AnimatedContentSharedElement() {
    var isExpanded by remember { mutableStateOf(false) }

    Box(modifier = Modifier.size(256.dp)) {
        SharedTransitionScope { modifier ->
            AnimatedContent(isExpanded, modifier = modifier) { targetState ->
                if (targetState) {
                    Box(
                        modifier = Modifier
                            .sharedElement(
                                rememberSharedContentState(key = "a"),
                                this,
                            )
                            .fillMaxSize()
                            .background(Color.Red)
                            .clickable {
                                isExpanded = !isExpanded
                            },
                    )
                } else {
                    FlowRow {
                        Box(
                            modifier = Modifier
                                .sharedElement(
                                    rememberSharedContentState(key = "a"),
                                    this@AnimatedContent,
                                )
                                .size(64.dp)
                                .background(Color.Magenta)
                                .clickable {
                                    isExpanded = !isExpanded
                                },
                        )
                        Box(
                            modifier = Modifier
                                .size(64.dp)
                                .background(Color.Blue),
                        )
                        Box(
                            modifier = Modifier
                                .size(64.dp)
                                .background(Color.Green),
                        )
                        Box(
                            modifier = Modifier
                                .size(64.dp)
                                .background(Color.Yellow),
                        )
                    }
                }
            }
        }
    }
}

@OptIn(ExperimentalSharedTransitionApi::class, ExperimentalLayoutApi::class)
@Preview
@Composable
internal fun AnimatedContentSharedElementWithCallerManagedVisibility() {
    var isExpanded by remember { mutableStateOf(false) }

    Box(modifier = Modifier.size(256.dp)) {
        SharedTransitionScope { modifier ->
            AnimatedContent(isExpanded, modifier = modifier) { targetState ->
                if (targetState) {
                    Box(
                        modifier = Modifier
                            .sharedElementWithCallerManagedVisibility(
                                rememberSharedContentState(key = "a"),
                                isExpanded,
                            )
                            .fillMaxSize()
                            .background(Color.Red)
                            .clickable {
                                isExpanded = !isExpanded
                            },
                    )
                } else {
                    FlowRow {
                        Box(
                            modifier = Modifier
                                .sharedElementWithCallerManagedVisibility(
                                    rememberSharedContentState(key = "a"),
                                    !isExpanded,
                                )
                                .size(64.dp)
                                .background(Color.Magenta)
                                .clickable {
                                    isExpanded = !isExpanded
                                },
                        )
                        Box(
                            modifier = Modifier
                                .size(64.dp)
                                .background(Color.Blue),
                        )
                        Box(
                            modifier = Modifier
                                .size(64.dp)
                                .background(Color.Green),
                        )
                        Box(
                            modifier = Modifier
                                .size(64.dp)
                                .background(Color.Yellow),
                        )
                    }
                }
            }
        }
    }
}

@OptIn(ExperimentalSharedTransitionApi::class, ExperimentalLayoutApi::class)
@Preview
@Composable
internal fun CustomAnimatedContentSharedElementWithCallerManagedVisibility() {
    var isExpanded by remember { mutableStateOf(false) }

    Box(modifier = Modifier.size(256.dp)) {
        SharedTransitionScope { modifier ->
            com.alexvanyo.composelife.ui.util.AnimatedContent(
                TargetState.Single(isExpanded),
                modifier = modifier,
            ) { targetState ->
                if (targetState) {
                    Box(
                        modifier = Modifier
                            .sharedElementWithCallerManagedVisibility(
                                rememberSharedContentState(key = "a"),
                                isExpanded,
                            )
                            .fillMaxSize()
                            .background(Color.Red)
                            .clickable {
                                isExpanded = !isExpanded
                            },
                    )
                } else {
                    FlowRow {
                        Box(
                            modifier = Modifier
                                .sharedElementWithCallerManagedVisibility(
                                    rememberSharedContentState(key = "a"),
                                    !isExpanded,
                                )
                                .size(64.dp)
                                .background(Color.Magenta)
                                .clickable {
                                    isExpanded = !isExpanded
                                },
                        )
                        Box(
                            modifier = Modifier
                                .size(64.dp)
                                .background(Color.Blue),
                        )
                        Box(
                            modifier = Modifier
                                .size(64.dp)
                                .background(Color.Green),
                        )
                        Box(
                            modifier = Modifier
                                .size(64.dp)
                                .background(Color.Yellow),
                        )
                    }
                }
            }
        }
    }
}

@OptIn(ExperimentalSharedTransitionApi::class, ExperimentalLayoutApi::class)
@Preview
@Composable
internal fun CustomAnimatedContentSettingUiSharedElementWithCallerManagedVisibility() {
    var isExpanded by remember { mutableStateOf(false) }

    WithPreviewDependencies {
        Surface {
            SharedTransitionScope { modifier ->
                com.alexvanyo.composelife.ui.util.AnimatedContent(
                    TargetState.Single(isExpanded),
                    modifier = modifier
                        .fillMaxSize()
                        .clickable { isExpanded = !isExpanded },
                ) { targetState ->
                    if (targetState) {
                        Column(verticalArrangement = Arrangement.Top, modifier = Modifier.fillMaxSize()) {
                            SettingUi(
                                setting = Setting.CellShapeConfig,
                                onOpenInSettingsClicked = null,
                                modifier = Modifier.sharedElementWithCallerManagedVisibility(
                                    rememberSharedContentState(key = "a"),
                                    isExpanded,
                                ),
                            )
                        }
                    } else {
                        Column(verticalArrangement = Arrangement.Bottom, modifier = Modifier.fillMaxSize()) {
                            SettingUi(
                                setting = Setting.CellShapeConfig,
                                onOpenInSettingsClicked = {},
                                modifier = Modifier.sharedElementWithCallerManagedVisibility(
                                    rememberSharedContentState(key = "a"),
                                    !isExpanded,
                                ),
                            )
                        }
                    }
                }
            }
        }
    }
}
