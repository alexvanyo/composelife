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

package com.alexvanyo.composelife.ui.info

import android.content.res.Configuration
import androidx.compose.animation.AnimatedContent
import androidx.compose.animation.AnimatedVisibility
import androidx.compose.animation.EnterTransition
import androidx.compose.animation.ExitTransition
import androidx.compose.animation.ExperimentalAnimationApi
import androidx.compose.animation.SizeTransform
import androidx.compose.animation.core.AnimationConstants
import androidx.compose.animation.core.FastOutLinearInEasing
import androidx.compose.animation.core.keyframes
import androidx.compose.animation.expandIn
import androidx.compose.animation.expandVertically
import androidx.compose.animation.fadeIn
import androidx.compose.animation.fadeOut
import androidx.compose.animation.shrinkOut
import androidx.compose.animation.shrinkVertically
import androidx.compose.animation.with
import androidx.compose.foundation.interaction.MutableInteractionSource
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.ColumnScope
import androidx.compose.foundation.layout.Row
import androidx.compose.foundation.layout.Spacer
import androidx.compose.foundation.layout.padding
import androidx.compose.foundation.layout.size
import androidx.compose.foundation.layout.width
import androidx.compose.foundation.selection.triStateToggleable
import androidx.compose.material.ripple.rememberRipple
import androidx.compose.material3.Checkbox
import androidx.compose.material3.ExperimentalMaterial3Api
import androidx.compose.material3.Text
import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.saveable.Saver
import androidx.compose.runtime.saveable.listSaver
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.setValue
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.semantics.Role
import androidx.compose.ui.semantics.semantics
import androidx.compose.ui.state.ToggleableState
import androidx.compose.ui.tooling.preview.Preview
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.ui.theme.ComposeLifeTheme

class CellUniverseInfoItemState(
    isChecked: Boolean = defaultIsChecked,
) {
    var isChecked by mutableStateOf(isChecked)

    companion object {
        const val defaultIsChecked: Boolean = true

        val Saver: Saver<CellUniverseInfoItemState, *> = listSaver(
            { cellUniverseInfoItemState ->
                listOf(cellUniverseInfoItemState.isChecked)
            },
            { list ->
                CellUniverseInfoItemState(list[0])
            },
        )
    }
}

@Composable
fun rememberCellUniverseInfoItemState(
    isChecked: Boolean = CellUniverseInfoItemState.defaultIsChecked,
): CellUniverseInfoItemState =
    rememberSaveable(saver = CellUniverseInfoItemState.Saver) {
        CellUniverseInfoItemState(isChecked = isChecked)
    }

class CellUniverseInfoItemContent(
    private val cellUniverseInfoCardState: CellUniverseInfoItemState,
    val text: @Composable (isEditing: Boolean) -> String,
) {
    var isChecked by cellUniverseInfoCardState::isChecked
}

@Suppress("LongMethod")
@OptIn(ExperimentalAnimationApi::class, ExperimentalMaterial3Api::class)
@Composable
fun ColumnScope.InfoItem(
    cellUniverseInfoItemContent: CellUniverseInfoItemContent,
    isEditing: Boolean,
    modifier: Modifier = Modifier,
) {
    // Animate the appearance and disappearance of this item.
    AnimatedVisibility(
        visible = cellUniverseInfoItemContent.isChecked || isEditing,
        enter = fadeIn() + expandVertically(expandFrom = Alignment.CenterVertically),
        exit = fadeOut() + shrinkVertically(shrinkTowards = Alignment.CenterVertically),
        modifier = modifier,
    ) {
        Box(
            modifier = if (isEditing) {
                Modifier.triStateToggleable(
                    state = ToggleableState(cellUniverseInfoItemContent.isChecked),
                    onClick = {
                        cellUniverseInfoItemContent.isChecked = !cellUniverseInfoItemContent.isChecked
                    },
                    enabled = true,
                    role = Role.Checkbox,
                    interactionSource = remember { MutableInteractionSource() },
                    indication = rememberRipple(),
                )
            } else {
                Modifier
            }
                .semantics(mergeDescendants = true) {}
                .padding(horizontal = 8.dp),
        ) {
            Row(
                verticalAlignment = Alignment.CenterVertically,
            ) {
                Text(
                    text = cellUniverseInfoItemContent.text(isEditing),
                    modifier = Modifier.weight(1f),
                )

                // The AnimatedContent allowing the text to grow.
                // The spacer represents the room needed for the checkbox, and its presence will ensure the text does
                // not overlap the checkbox.
                // The animated spacer's absence will allow the text to expand as needed within the row.
                AnimatedContent(
                    targetState = isEditing,
                    transitionSpec = {
                        (EnterTransition.None with ExitTransition.None)
                            .using(
                                SizeTransform { initialSize, targetSize ->
                                    keyframes {
                                        if (false isTransitioningTo true) {
                                            targetSize
                                        } else {
                                            initialSize
                                        } at AnimationConstants.DefaultDurationMillis / 2 with FastOutLinearInEasing
                                    }
                                },
                            )
                    },
                    contentAlignment = Alignment.Center,
                ) { targetIsEditing ->
                    if (targetIsEditing) {
                        Spacer(modifier = Modifier.size(48.dp))
                    }
                }
            }

            // The AnimatedContent for the checkbox.
            // This content remains a constant width, allowing for more graceful animations without horizontal
            // movement
            AnimatedContent(
                targetState = isEditing,
                transitionSpec = {
                    fadeIn() + expandIn(expandFrom = Alignment.Center) with
                        fadeOut() + shrinkOut(shrinkTowards = Alignment.Center)
                },
                contentAlignment = Alignment.Center,
                modifier = Modifier.align(Alignment.CenterEnd),
            ) { targetIsEditing ->
                if (targetIsEditing) {
                    Checkbox(
                        checked = cellUniverseInfoItemContent.isChecked,
                        onCheckedChange = null,
                        modifier = Modifier.size(48.dp),
                    )
                } else {
                    Spacer(modifier = Modifier.width(48.dp))
                }
            }
        }
    }
}

@Preview(
    name = "Not editing light mode",
    uiMode = Configuration.UI_MODE_NIGHT_NO,
)
@Preview(
    name = "Not editing dark mode",
    uiMode = Configuration.UI_MODE_NIGHT_YES,
)
@Composable
fun CellUniverseInfoItemNotEditingPreview() {
    ComposeLifeTheme {
        Column {
            InfoItem(
                cellUniverseInfoItemContent = CellUniverseInfoItemContent(
                    cellUniverseInfoCardState = rememberCellUniverseInfoItemState(),
                ) { "isEditing: $it" },
                isEditing = false,
            )
        }
    }
}

@Preview(
    name = "Editing light mode",
    uiMode = Configuration.UI_MODE_NIGHT_NO,
)
@Preview(
    name = "Editing dark mode",
    uiMode = Configuration.UI_MODE_NIGHT_YES,
)
@Composable
fun CellUniverseInfoItemEditingPreview() {
    ComposeLifeTheme {
        Column {
            InfoItem(
                cellUniverseInfoItemContent = CellUniverseInfoItemContent(
                    cellUniverseInfoCardState = rememberCellUniverseInfoItemState(),
                ) { "isEditing: $it" },
                isEditing = true,
            )
        }
    }
}
