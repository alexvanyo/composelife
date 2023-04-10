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

import androidx.compose.foundation.Canvas
import androidx.compose.foundation.interaction.MutableInteractionSource
import androidx.compose.foundation.layout.size
import androidx.compose.foundation.selection.toggleable
import androidx.compose.material.ripple.rememberRipple
import androidx.compose.runtime.Composable
import androidx.compose.runtime.remember
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.CornerRadius
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.graphics.isSpecified
import androidx.compose.ui.semantics.Role
import androidx.compose.ui.semantics.contentDescription
import androidx.compose.ui.semantics.semantics
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.preferences.CurrentShape
import com.alexvanyo.composelife.ui.app.entrypoints.WithPreviewDependencies
import com.alexvanyo.composelife.ui.app.theme.ComposeLifeTheme
import com.alexvanyo.composelife.ui.util.ThemePreviews

/**
 * An individual cell that is interactable.
 *
 * This cell has no inherent size, which must be specified via [modifier].
 *
 * The cell is alive if [isAlive] is true, and [onValueChange] will be called when the living state should be toggled.
 */
@Composable
fun InteractableCell(
    // noinspection ComposeModifierWithoutDefault
    modifier: Modifier,
    drawState: DrawState,
    shape: CurrentShape,
    contentDescription: String,
    onValueChange: (isAlive: Boolean) -> Unit,
) {
    val aliveColor = ComposeLifeTheme.aliveCellColor
    val pendingAliveColor = ComposeLifeTheme.pendingAliveCellColor
    val deadColor = ComposeLifeTheme.deadCellColor
    val pendingDeadColor = ComposeLifeTheme.pendingAliveCellColor

    val rippleColor = when (drawState) {
        DrawState.Alive, DrawState.PendingAlive -> deadColor
        DrawState.Dead, DrawState.PendingDead -> aliveColor
    }

    Canvas(
        modifier = modifier
            .semantics {
                this.contentDescription = contentDescription
            }
            .toggleable(
                value = when (drawState) {
                    DrawState.Alive, DrawState.PendingAlive -> true
                    DrawState.Dead, DrawState.PendingDead -> false
                },
                interactionSource = remember { MutableInteractionSource() },
                indication = rememberRipple(color = rippleColor),
                role = Role.Switch,
                onValueChange = onValueChange,
            ),
    ) {
        val drawColor = when (drawState) {
            DrawState.Alive -> aliveColor
            DrawState.PendingAlive -> pendingAliveColor
            DrawState.Dead -> Color.Unspecified
            DrawState.PendingDead -> pendingDeadColor
        }
        if (drawColor.isSpecified) {
            when (shape) {
                is CurrentShape.RoundRectangle -> {
                    drawRoundRect(
                        color = drawColor,
                        topLeft = Offset(
                            size.width * (1f - shape.sizeFraction) / 2f,
                            size.height * (1f - shape.sizeFraction) / 2f,
                        ),
                        size = size * shape.sizeFraction,
                        cornerRadius = CornerRadius(
                            size.width * shape.sizeFraction * shape.cornerFraction,
                        ),
                    )
                }
            }
        }
    }
}

sealed interface DrawState {
    object Alive : DrawState
    object Dead : DrawState
    object PendingAlive : DrawState
    object PendingDead : DrawState
}

@ThemePreviews
@Composable
fun AliveCellPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            InteractableCell(
                modifier = Modifier.size(50.dp),
                drawState = DrawState.Alive,
                shape = CurrentShape.RoundRectangle(
                    sizeFraction = 1f,
                    cornerFraction = 0f,
                ),
                contentDescription = "test cell",
                onValueChange = {},
            )
        }
    }
}

@ThemePreviews
@Composable
fun PendingAliveCellPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            InteractableCell(
                modifier = Modifier.size(50.dp),
                drawState = DrawState.PendingAlive,
                shape = CurrentShape.RoundRectangle(
                    sizeFraction = 1f,
                    cornerFraction = 0f,
                ),
                contentDescription = "test cell",
                onValueChange = {},
            )
        }
    }
}

@ThemePreviews
@Composable
fun DeadCellPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            InteractableCell(
                modifier = Modifier.size(50.dp),
                drawState = DrawState.Dead,
                shape = CurrentShape.RoundRectangle(
                    sizeFraction = 1f,
                    cornerFraction = 0f,
                ),
                contentDescription = "test cell",
                onValueChange = {},
            )
        }
    }
}

@ThemePreviews
@Composable
fun PendingDeadCellPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            InteractableCell(
                modifier = Modifier.size(50.dp),
                drawState = DrawState.PendingDead,
                shape = CurrentShape.RoundRectangle(
                    sizeFraction = 1f,
                    cornerFraction = 0f,
                ),
                contentDescription = "test cell",
                onValueChange = {},
            )
        }
    }
}
