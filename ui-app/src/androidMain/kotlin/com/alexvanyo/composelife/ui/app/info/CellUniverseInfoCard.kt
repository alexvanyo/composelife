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

package com.alexvanyo.composelife.ui.app.info

import androidx.compose.animation.core.Spring
import androidx.compose.animation.core.spring
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
import androidx.compose.runtime.getValue
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberUpdatedState
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.res.stringResource
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.model.TemporalGameOfLifeState
import com.alexvanyo.composelife.ui.app.R
import com.alexvanyo.composelife.ui.app.cells.CellWindowState
import com.alexvanyo.composelife.ui.app.entrypoints.WithPreviewDependencies
import com.alexvanyo.composelife.ui.app.theme.ComposeLifeTheme
import com.alexvanyo.composelife.ui.util.AnimatedContent
import com.alexvanyo.composelife.ui.util.TargetState
import com.alexvanyo.composelife.ui.util.ThemePreviews
import com.alexvanyo.composelife.ui.util.or
import kotlinx.collections.immutable.ImmutableList
import kotlinx.collections.immutable.persistentListOf

/**
 * The persistable state describing the [CellUniverseInfoCard].
 */
interface CellUniverseInfoCardState {

    /**
     * Sets if the card is expanded.
     */
    fun setIsExpanded(isExpanded: Boolean)

    /**
     * The target state for whether the card is expanded.
     */
    val expandedTargetState: TargetState<Boolean>
}

/**
 * Remembers the a default implementation of [CellUniverseInfoCardState].
 */
@Composable
fun rememberCellUniverseInfoCardState(
    setIsExpanded: (Boolean) -> Unit,
    expandedTargetState: TargetState<Boolean>,
): CellUniverseInfoCardState =
    object : CellUniverseInfoCardState {
        override fun setIsExpanded(isExpanded: Boolean) {
            setIsExpanded(isExpanded)
        }

        override val expandedTargetState: TargetState<Boolean>
            get() = expandedTargetState
    }

class CellUniverseInfoCardContent(
    private val cellUniverseInfoCardState: CellUniverseInfoCardState,
    val cellUniverseInfoItemContents: List<CellUniverseInfoItemContent>,
) {
    fun setIsExpanded(isExpanded: Boolean) {
        cellUniverseInfoCardState.setIsExpanded(isExpanded)
    }

    val expandedTargetState: TargetState<Boolean> get() =
        cellUniverseInfoCardState.expandedTargetState

    val editingTargetState: TargetState<Boolean> get() =
        expandedTargetState or cellUniverseInfoItemContents.none { it.isChecked }

    val showColumnTargetState: TargetState<Boolean> get() =
        expandedTargetState or cellUniverseInfoItemContents.any { it.isChecked }
}

@Composable
fun CellUniverseInfoCard(
    cellWindowState: CellWindowState,
    evolutionStatus: TemporalGameOfLifeState.EvolutionStatus,
    infoCardState: CellUniverseInfoCardState,
    modifier: Modifier = Modifier,
) {
    val currentEvolutionStatus by rememberUpdatedState(newValue = evolutionStatus)

    CellUniverseInfoCard(
        infoItemTexts = persistentListOf(
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
    infoItemTexts: ImmutableList<@Composable (isEditing: Boolean) -> String>,
    infoCardState: CellUniverseInfoCardState,
    modifier: Modifier = Modifier,
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
            targetState = cellUniverseInfoCardContent.showColumnTargetState,
            contentAlignment = Alignment.TopEnd,
            contentSizeAnimationSpec = spring(
                stiffness = Spring.StiffnessMedium,
            ),
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
                                    editingTargetState = cellUniverseInfoCardContent.editingTargetState,
                                )
                            }
                    }
                }

                CellUniverseInfoExpandButton(
                    isExpanded = cellUniverseInfoCardContent.expandedTargetState.current,
                    setIsExpanded = cellUniverseInfoCardContent::setIsExpanded,
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
                    cellUniverseInfoCardState = rememberCellUniverseInfoCardState(
                        setIsExpanded = {},
                        expandedTargetState = TargetState.Single(false),
                    ),
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
                    cellUniverseInfoCardState = rememberCellUniverseInfoCardState(
                        setIsExpanded = {},
                        expandedTargetState = TargetState.Single(false),
                    ),
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
                    cellUniverseInfoCardState = rememberCellUniverseInfoCardState(
                        setIsExpanded = {},
                        expandedTargetState = TargetState.Single(false),
                    ),
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
                    cellUniverseInfoCardState = rememberCellUniverseInfoCardState(
                        setIsExpanded = {},
                        expandedTargetState = TargetState.Single(true),
                    ),
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
