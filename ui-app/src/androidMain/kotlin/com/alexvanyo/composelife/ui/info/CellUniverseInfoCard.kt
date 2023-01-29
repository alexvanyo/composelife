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

import androidx.compose.animation.AnimatedContent
import androidx.compose.animation.ExperimentalAnimationApi
import androidx.compose.animation.core.tween
import androidx.compose.animation.fadeIn
import androidx.compose.animation.fadeOut
import androidx.compose.animation.with
import androidx.compose.foundation.layout.Arrangement
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.Row
import androidx.compose.foundation.layout.heightIn
import androidx.compose.foundation.layout.padding
import androidx.compose.foundation.rememberScrollState
import androidx.compose.foundation.verticalScroll
import androidx.compose.material.icons.Icons
import androidx.compose.material.icons.filled.ExpandLess
import androidx.compose.material.icons.filled.ExpandMore
import androidx.compose.material3.Card
import androidx.compose.material3.CardDefaults
import androidx.compose.material3.Icon
import androidx.compose.material3.IconButtonDefaults
import androidx.compose.material3.IconToggleButton
import androidx.compose.material3.LocalContentColor
import androidx.compose.material3.MaterialTheme
import androidx.compose.runtime.Composable
import androidx.compose.runtime.derivedStateOf
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberUpdatedState
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.setValue
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.res.stringResource
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.model.TemporalGameOfLifeState
import com.alexvanyo.composelife.ui.R
import com.alexvanyo.composelife.ui.cells.CellWindowState
import com.alexvanyo.composelife.ui.entrypoints.WithPreviewDependencies
import com.alexvanyo.composelife.ui.theme.ComposeLifeTheme
import com.alexvanyo.composelife.ui.util.ThemePreviews

/**
 * The persistable state describing the [CellUniverseInfoCard].
 */
interface CellUniverseInfoCardState {

    /**
     * `true` if the card is expanded.
     */
    var isExpanded: Boolean

    companion object {
        const val defaultIsExpanded: Boolean = false
    }
}

/**
 * Remembers the a default implementation of [CellUniverseInfoCardState].
 */
@Composable
fun rememberCellUniverseInfoCardState(
    initialIsExpanded: Boolean = CellUniverseInfoCardState.defaultIsExpanded,
): CellUniverseInfoCardState {
    var isExpanded by rememberSaveable { mutableStateOf(initialIsExpanded) }

    return remember {
        object : CellUniverseInfoCardState {
            override var isExpanded: Boolean
                get() = isExpanded
                set(value) {
                    isExpanded = value
                }
        }
    }
}

class CellUniverseInfoCardContent(
    private val cellUniverseInfoCardState: CellUniverseInfoCardState,
    val cellUniverseInfoItemContents: List<CellUniverseInfoItemContent>,
) {
    var isExpanded by cellUniverseInfoCardState::isExpanded

    val isEditing by derivedStateOf {
        cellUniverseInfoCardState.isExpanded ||
            cellUniverseInfoItemContents.none { it.isChecked }
    }

    val showColumn by derivedStateOf {
        cellUniverseInfoCardState.isExpanded ||
            cellUniverseInfoItemContents.any { it.isChecked }
    }
}

@Composable
fun CellUniverseInfoCard(
    cellWindowState: CellWindowState,
    evolutionStatus: TemporalGameOfLifeState.EvolutionStatus,
    modifier: Modifier = Modifier,
    infoCardState: CellUniverseInfoCardState = rememberCellUniverseInfoCardState(),
) {
    val currentEvolutionStatus by rememberUpdatedState(newValue = evolutionStatus)

    CellUniverseInfoCard(
        infoItemTexts = listOf(
            {
                stringResource(
                    id = R.string.offset,
                    cellWindowState.offset.x,
                    cellWindowState.offset.y,
                )
            },
            {
                stringResource(
                    id = R.string.scale,
                    cellWindowState.scale,
                )
            },
            { isEditing ->
                when (val newEvolutionStatus = currentEvolutionStatus) {
                    TemporalGameOfLifeState.EvolutionStatus.Paused ->
                        stringResource(id = R.string.paused)
                    is TemporalGameOfLifeState.EvolutionStatus.Running ->
                        stringResource(
                            id = if (isEditing) {
                                R.string.generations_per_second_long
                            } else {
                                R.string.generations_per_second_short
                            },
                            newEvolutionStatus.averageGenerationsPerSecond,
                        )
                }
            },
        ),
        infoCardState = infoCardState,
        modifier = modifier,
    )
}

@Composable
fun CellUniverseInfoCard(
    infoItemTexts: List<@Composable (isEditing: Boolean) -> String>,
    modifier: Modifier = Modifier,
    infoCardState: CellUniverseInfoCardState = rememberCellUniverseInfoCardState(),
) {
    val infoItemContents = infoItemTexts.map { text ->
        val infoItemState = rememberCellUniverseInfoItemState()
        remember {
            CellUniverseInfoItemContent(
                cellUniverseInfoCardState = infoItemState,
                text = text,
            )
        }
    }

    val infoCardContent = remember(infoItemContents, infoCardState) {
        CellUniverseInfoCardContent(
            cellUniverseInfoCardState = infoCardState,
            cellUniverseInfoItemContents = infoItemContents,
        )
    }

    CellUniverseInfoCard(
        cellUniverseInfoCardContent = infoCardContent,
        modifier = modifier,
    )
}

@OptIn(ExperimentalAnimationApi::class)
@Composable
fun CellUniverseInfoCard(
    cellUniverseInfoCardContent: CellUniverseInfoCardContent,
    modifier: Modifier = Modifier,
) {
    Card(
        modifier = modifier,
        colors = CardDefaults.cardColors(
            containerColor = MaterialTheme.colorScheme.surface,
        ),
        elevation = CardDefaults.cardElevation(
            defaultElevation = 1.dp,
        ),
    ) {
        AnimatedContent(
            targetState = cellUniverseInfoCardContent.showColumn,
            transitionSpec = {
                fadeIn(animationSpec = tween(220, delayMillis = 90)) with
                    fadeOut(animationSpec = tween(90))
            },
            contentAlignment = Alignment.TopEnd,
            modifier = Modifier.padding(8.dp),
        ) { showColumn ->
            Row(
                horizontalArrangement = Arrangement.spacedBy(8.dp),
                verticalAlignment = Alignment.Top,
            ) {
                if (showColumn) {
                    Column(
                        verticalArrangement = Arrangement.Center,
                        modifier = Modifier
                            .weight(1f)
                            .heightIn(min = 48.dp)
                            .verticalScroll(rememberScrollState())
                            .padding(vertical = 8.dp),
                    ) {
                        cellUniverseInfoCardContent.cellUniverseInfoItemContents
                            .forEach { cellUniverseInfoItemContent ->
                                InfoItem(
                                    cellUniverseInfoItemContent = cellUniverseInfoItemContent,
                                    isEditing = cellUniverseInfoCardContent.isEditing,
                                )
                            }
                    }
                }

                CellUniverseInfoExpandButton(
                    isExpanded = cellUniverseInfoCardContent.isExpanded,
                    setIsExpanded = { cellUniverseInfoCardContent.isExpanded = it },
                )
            }
        }
    }
}

@Composable
private fun CellUniverseInfoExpandButton(
    isExpanded: Boolean,
    setIsExpanded: (Boolean) -> Unit,
    modifier: Modifier = Modifier,
) {
    IconToggleButton(
        checked = isExpanded,
        onCheckedChange = setIsExpanded,
        colors = IconButtonDefaults.iconToggleButtonColors(
            checkedContentColor = LocalContentColor.current,
        ),
        modifier = modifier,
    ) {
        Icon(
            imageVector = if (isExpanded) {
                Icons.Filled.ExpandLess
            } else {
                Icons.Filled.ExpandMore
            },
            contentDescription = if (isExpanded) {
                stringResource(id = R.string.collapse)
            } else {
                stringResource(id = R.string.expand)
            },
        )
    }
}

@ThemePreviews
@Composable
fun CellUniverseInfoCardCollapsedPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            CellUniverseInfoCard(
                cellUniverseInfoCardContent = CellUniverseInfoCardContent(
                    rememberCellUniverseInfoCardState(initialIsExpanded = false),
                    cellUniverseInfoItemContents = listOf(
                        CellUniverseInfoItemContent(
                            rememberCellUniverseInfoItemState(isChecked = true),
                        ) { "First" },
                        CellUniverseInfoItemContent(
                            rememberCellUniverseInfoItemState(isChecked = true),
                        ) { "Second" },
                        CellUniverseInfoItemContent(
                            rememberCellUniverseInfoItemState(isChecked = true),
                        ) { "Third" },
                    ),
                ),
            )
        }
    }
}

@ThemePreviews
@Composable
fun CellUniverseInfoCardCollapsedSingleSelectionPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            CellUniverseInfoCard(
                cellUniverseInfoCardContent = CellUniverseInfoCardContent(
                    rememberCellUniverseInfoCardState(initialIsExpanded = false),
                    cellUniverseInfoItemContents = listOf(
                        CellUniverseInfoItemContent(
                            rememberCellUniverseInfoItemState(isChecked = false),
                        ) { "First" },
                        CellUniverseInfoItemContent(
                            rememberCellUniverseInfoItemState(isChecked = false),
                        ) { "Second" },
                        CellUniverseInfoItemContent(
                            rememberCellUniverseInfoItemState(isChecked = true),
                        ) { "Third" },
                    ),
                ),
            )
        }
    }
}

@ThemePreviews
@Composable
fun CellUniverseInfoCardFullyCollapsedPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            CellUniverseInfoCard(
                cellUniverseInfoCardContent = CellUniverseInfoCardContent(
                    rememberCellUniverseInfoCardState(initialIsExpanded = false),
                    cellUniverseInfoItemContents = listOf(
                        CellUniverseInfoItemContent(
                            rememberCellUniverseInfoItemState(isChecked = false),
                        ) { "First" },
                        CellUniverseInfoItemContent(
                            rememberCellUniverseInfoItemState(isChecked = false),
                        ) { "Second" },
                        CellUniverseInfoItemContent(
                            rememberCellUniverseInfoItemState(isChecked = false),
                        ) { "Third" },
                    ),
                ),
            )
        }
    }
}

@ThemePreviews
@Composable
fun CellUniverseInfoCardExpandedPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            CellUniverseInfoCard(
                cellUniverseInfoCardContent = CellUniverseInfoCardContent(
                    rememberCellUniverseInfoCardState(initialIsExpanded = true),
                    cellUniverseInfoItemContents = listOf(
                        CellUniverseInfoItemContent(
                            rememberCellUniverseInfoItemState(),
                        ) { "First" },
                        CellUniverseInfoItemContent(
                            rememberCellUniverseInfoItemState(),
                        ) { "Second" },
                        CellUniverseInfoItemContent(
                            rememberCellUniverseInfoItemState(),
                        ) { "Third" },
                    ),
                ),
            )
        }
    }
}
