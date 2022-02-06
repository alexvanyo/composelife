package com.alexvanyo.composelife.ui

import android.content.res.Configuration
import androidx.compose.animation.AnimatedContent
import androidx.compose.animation.ExperimentalAnimationApi
import androidx.compose.animation.core.tween
import androidx.compose.animation.fadeIn
import androidx.compose.animation.fadeOut
import androidx.compose.animation.with
import androidx.compose.foundation.layout.Arrangement
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.Row
import androidx.compose.foundation.layout.padding
import androidx.compose.material.Card
import androidx.compose.material.Icon
import androidx.compose.material.IconToggleButton
import androidx.compose.material.icons.Icons
import androidx.compose.material.icons.filled.ArrowDropDown
import androidx.compose.material.icons.filled.ArrowDropUp
import androidx.compose.runtime.Composable
import androidx.compose.runtime.derivedStateOf
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberUpdatedState
import androidx.compose.runtime.saveable.Saver
import androidx.compose.runtime.saveable.listSaver
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.setValue
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.res.stringResource
import androidx.compose.ui.tooling.preview.Preview
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.R
import com.alexvanyo.composelife.model.TemporalGameOfLifeState
import com.alexvanyo.composelife.ui.theme.ComposeLifeTheme

class CellUniverseInfoCardState(
    isExpanded: Boolean = defaultIsExpanded,
) {
    var isExpanded by mutableStateOf(isExpanded)

    companion object {
        const val defaultIsExpanded: Boolean = false

        val Saver: Saver<CellUniverseInfoCardState, *> = listSaver(
            { cellUniverseInfoCardState ->
                listOf(cellUniverseInfoCardState.isExpanded)
            },
            { list ->
                CellUniverseInfoCardState(list[0])
            }
        )
    }
}

@Composable
fun rememberCellUniverseInfoCardState(
    isExpanded: Boolean = CellUniverseInfoCardState.defaultIsExpanded,
): CellUniverseInfoCardState =
    rememberSaveable(saver = CellUniverseInfoCardState.Saver) {
        CellUniverseInfoCardState(isExpanded = isExpanded)
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
) {
    val currentEvolutionStatus by rememberUpdatedState(newValue = evolutionStatus)

    CellUniverseInfoCard(
        infoItemTexts = listOf(
            {
                stringResource(
                    id = R.string.offset,
                    cellWindowState.offset.x,
                    cellWindowState.offset.y
                )
            },
            {
                stringResource(
                    id = R.string.scale,
                    cellWindowState.scale
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
                            newEvolutionStatus.averageGenerationsPerSecond
                        )
                }
            }
        ),
        modifier = modifier
    )
}

@OptIn(ExperimentalAnimationApi::class)
@Composable
fun CellUniverseInfoCard(
    infoItemTexts: List<@Composable (isEditing: Boolean) -> String>,
    modifier: Modifier = Modifier,
) {
    val infoItemContents = infoItemTexts.map { text ->
        val infoItemState = rememberCellUniverseInfoItemState()
        remember {
            CellUniverseInfoItemContent(
                cellUniverseInfoCardState = infoItemState,
                text = text
            )
        }
    }

    val infoCardState = rememberCellUniverseInfoCardState()
    val infoCardContent = remember(infoItemContents, infoCardState) {
        CellUniverseInfoCardContent(
            cellUniverseInfoCardState = infoCardState,
            cellUniverseInfoItemContents = infoItemContents
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
    Card(modifier = modifier) {
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
            ) {
                if (showColumn) {
                    Column(
                        modifier = Modifier
                            .weight(1f)
                            .padding(vertical = 8.dp),
                    ) {
                        cellUniverseInfoCardContent.cellUniverseInfoItemContents
                            .forEach { cellUniverseInfoItemContent ->
                                InfoItem(
                                    cellUniverseInfoItemContent = cellUniverseInfoItemContent,
                                    isEditing = cellUniverseInfoCardContent.isEditing
                                )
                            }
                    }
                }

                IconToggleButton(
                    checked = cellUniverseInfoCardContent.isExpanded,
                    onCheckedChange = { cellUniverseInfoCardContent.isExpanded = it },
                ) {
                    Icon(
                        imageVector = if (cellUniverseInfoCardContent.isExpanded) {
                            Icons.Filled.ArrowDropUp
                        } else {
                            Icons.Filled.ArrowDropDown
                        },
                        contentDescription = if (cellUniverseInfoCardContent.isExpanded) {
                            stringResource(id = R.string.collapse)
                        } else {
                            stringResource(id = R.string.expand)
                        }
                    )
                }
            }
        }
    }
}

@Preview(
    name = "Collapsed light mode",
    uiMode = Configuration.UI_MODE_NIGHT_NO
)
@Preview(
    name = "Collapsed dark mode",
    uiMode = Configuration.UI_MODE_NIGHT_YES
)
@Composable
fun CellUniverseInfoCardCollapsedPreview() {
    ComposeLifeTheme {
        CellUniverseInfoCard(
            cellUniverseInfoCardContent = CellUniverseInfoCardContent(
                rememberCellUniverseInfoCardState(isExpanded = false),
                cellUniverseInfoItemContents = listOf(
                    CellUniverseInfoItemContent(
                        rememberCellUniverseInfoItemState(isChecked = true)
                    ) { "First" },
                    CellUniverseInfoItemContent(
                        rememberCellUniverseInfoItemState(isChecked = true)
                    ) { "Second" },
                    CellUniverseInfoItemContent(
                        rememberCellUniverseInfoItemState(isChecked = true)
                    ) { "Third" }
                )
            )
        )
    }
}

@Preview(
    name = "Fully collapsed light mode",
    uiMode = Configuration.UI_MODE_NIGHT_NO
)
@Preview(
    name = "Fully collapsed dark mode",
    uiMode = Configuration.UI_MODE_NIGHT_YES
)
@Composable
fun CellUniverseInfoCardFullyCollapsedPreview() {
    ComposeLifeTheme {
        CellUniverseInfoCard(
            cellUniverseInfoCardContent = CellUniverseInfoCardContent(
                rememberCellUniverseInfoCardState(isExpanded = false),
                cellUniverseInfoItemContents = listOf(
                    CellUniverseInfoItemContent(
                        rememberCellUniverseInfoItemState(isChecked = false)
                    ) { "First" },
                    CellUniverseInfoItemContent(
                        rememberCellUniverseInfoItemState(isChecked = false)
                    ) { "Second" },
                    CellUniverseInfoItemContent(
                        rememberCellUniverseInfoItemState(isChecked = false)
                    ) { "Third" }
                )
            )
        )
    }
}

@Preview(
    name = "Expanded light mode",
    uiMode = Configuration.UI_MODE_NIGHT_NO
)
@Preview(
    name = "Expanded dark mode",
    uiMode = Configuration.UI_MODE_NIGHT_YES
)
@Composable
fun CellUniverseInfoCardExpandedPreview() {
    ComposeLifeTheme {
        CellUniverseInfoCard(
            cellUniverseInfoCardContent = CellUniverseInfoCardContent(
                rememberCellUniverseInfoCardState(isExpanded = true),
                cellUniverseInfoItemContents = listOf(
                    CellUniverseInfoItemContent(
                        rememberCellUniverseInfoItemState()
                    ) { "First" },
                    CellUniverseInfoItemContent(
                        rememberCellUniverseInfoItemState()
                    ) { "Second" },
                    CellUniverseInfoItemContent(
                        rememberCellUniverseInfoItemState()
                    ) { "Third" }
                )
            )
        )
    }
}
