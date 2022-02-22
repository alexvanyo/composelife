package com.alexvanyo.composelife.ui

import androidx.activity.compose.BackHandler
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.Spacer
import androidx.compose.foundation.layout.WindowInsets
import androidx.compose.foundation.layout.WindowInsetsSides
import androidx.compose.foundation.layout.fillMaxWidth
import androidx.compose.foundation.layout.only
import androidx.compose.foundation.layout.padding
import androidx.compose.foundation.layout.safeDrawing
import androidx.compose.foundation.layout.windowInsetsBottomHeight
import androidx.compose.foundation.layout.windowInsetsPadding
import androidx.compose.foundation.layout.windowInsetsTopHeight
import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.setValue
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.layout.Layout
import androidx.compose.ui.layout.Placeable
import androidx.compose.ui.layout.layoutId
import androidx.compose.ui.platform.testTag
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.model.TemporalGameOfLifeState
import com.alexvanyo.composelife.ui.InteractiveCellUniverseOverlayLayoutTypes.CardTypes
import com.alexvanyo.composelife.ui.InteractiveCellUniverseOverlayLayoutTypes.CardTypes.CellUniverseActionCard
import com.alexvanyo.composelife.ui.InteractiveCellUniverseOverlayLayoutTypes.CardTypes.CellUniverseInfoCard
import com.alexvanyo.composelife.ui.InteractiveCellUniverseOverlayLayoutTypes.InsetsTypes
import com.alexvanyo.composelife.ui.InteractiveCellUniverseOverlayLayoutTypes.InsetsTypes.BottomInsets
import com.alexvanyo.composelife.ui.InteractiveCellUniverseOverlayLayoutTypes.InsetsTypes.TopInsets
import com.alexvanyo.composelife.ui.util.animatePlacement

@Suppress("LongMethod", "ComplexMethod")
@Composable
fun InteractiveCellUniverseOverlay(
    temporalGameOfLifeState: TemporalGameOfLifeState,
    cellWindowState: CellWindowState,
    modifier: Modifier = Modifier,
) {
    var isActionCardTopCard by rememberSaveable { mutableStateOf(true) }

    val delegateInfoCardState = rememberCellUniverseInfoCardState()
    val delegateActionCardState = rememberCellUniverseActionCardState()

    val infoCardState = remember(delegateInfoCardState) {
        object : CellUniverseInfoCardState by delegateInfoCardState {
            override var isExpanded: Boolean
                get() = delegateInfoCardState.isExpanded
                set(value) {
                    delegateInfoCardState.isExpanded = value
                    if (value) {
                        isActionCardTopCard = false
                    } else if (delegateActionCardState.isExpanded) {
                        isActionCardTopCard = true
                    }
                }
        }
    }
    val actionCardState = remember(delegateActionCardState) {
        object : CellUniverseActionCardState by delegateActionCardState {
            override var isExpanded: Boolean
                get() = delegateActionCardState.isExpanded
                set(value) {
                    delegateActionCardState.isExpanded = value
                    isActionCardTopCard = value || !infoCardState.isExpanded
                    if (value) {
                        isActionCardTopCard = true
                    } else if (delegateInfoCardState.isExpanded) {
                        isActionCardTopCard = false
                    }
                }
        }
    }

    if (infoCardState.isExpanded || actionCardState.isExpanded) {
        BackHandler {
            if (isActionCardTopCard && actionCardState.isExpanded) {
                actionCardState.isExpanded = false
            } else {
                check(infoCardState.isExpanded)
                infoCardState.isExpanded = false
            }
        }
    }

    Layout(
        content = {
            Spacer(
                modifier = Modifier
                    .windowInsetsTopHeight(WindowInsets.safeDrawing)
                    .layoutId(TopInsets)
            )
            Spacer(
                modifier = Modifier
                    .windowInsetsBottomHeight(WindowInsets.safeDrawing)
                    .layoutId(BottomInsets)
            )

            Box(
                modifier = Modifier
                    .fillMaxWidth()
                    .windowInsetsPadding(WindowInsets.safeDrawing.only(WindowInsetsSides.Horizontal))
                    .animatePlacement(
                        alignment = Alignment.TopCenter
                    )
                    .layoutId(CellUniverseInfoCard)
            ) {
                CellUniverseInfoCard(
                    cellWindowState = cellWindowState,
                    evolutionStatus = temporalGameOfLifeState.status,
                    infoCardState = infoCardState,
                    modifier = Modifier
                        .align(Alignment.CenterEnd)
                        .padding(8.dp)
                        .testTag("CellUniverseInfoCard")
                )
            }

            Box(
                modifier = Modifier
                    .fillMaxWidth()
                    .windowInsetsPadding(WindowInsets.safeDrawing.only(WindowInsetsSides.Horizontal))
                    .animatePlacement(
                        alignment = Alignment.BottomCenter
                    )
                    .layoutId(CellUniverseActionCard)
            ) {
                CellUniverseActionCard(
                    isTopCard = isActionCardTopCard,
                    temporalGameOfLifeState = temporalGameOfLifeState,
                    actionCardState = actionCardState,
                    modifier = Modifier
                        .align(Alignment.Center)
                        .padding(8.dp)
                        .testTag("CellUniverseActionCard")
                )
            }
        },
        measurePolicy = { measurables, constraints ->
            lateinit var topInsetsPlaceable: Placeable
            lateinit var bottomInsetsPlaceable: Placeable
            lateinit var infoCardPlaceable: Placeable
            lateinit var actionCardPlaceable: Placeable

            measurables.forEach { measurable ->
                when (measurable.layoutId as InteractiveCellUniverseOverlayLayoutTypes) {
                    is InsetsTypes -> {
                        val placeable = measurable.measure(constraints)
                        when (measurable.layoutId) {
                            TopInsets -> topInsetsPlaceable = placeable
                            BottomInsets -> bottomInsetsPlaceable = placeable
                        }
                    }
                    is CardTypes -> {
                        val placeable = measurable.measure(
                            constraints.copy(
                                maxHeight = constraints.maxHeight -
                                    topInsetsPlaceable.measuredHeight - bottomInsetsPlaceable.measuredHeight
                            )
                        )
                        when (measurable.layoutId) {
                            CellUniverseInfoCard -> infoCardPlaceable = placeable
                            CellUniverseActionCard -> actionCardPlaceable = placeable
                        }
                    }
                }
            }

            layout(constraints.maxWidth, constraints.maxHeight) {
                topInsetsPlaceable.place(0, 0)
                bottomInsetsPlaceable.place(0, constraints.maxHeight - bottomInsetsPlaceable.measuredHeight)

                // If we can fit both cards, place them both on screen.
                // Otherwise, place the top-card (as determined by
                if (topInsetsPlaceable.height + infoCardPlaceable.measuredHeight +
                    actionCardPlaceable.measuredHeight + bottomInsetsPlaceable.height <= constraints.maxHeight
                ) {
                    infoCardPlaceable.place(0, topInsetsPlaceable.measuredHeight)
                    actionCardPlaceable.place(
                        0,
                        constraints.maxHeight -
                            bottomInsetsPlaceable.measuredHeight - actionCardPlaceable.measuredHeight
                    )
                } else if (isActionCardTopCard) {
                    infoCardPlaceable.place(0, -infoCardPlaceable.measuredHeight)
                    actionCardPlaceable.place(
                        0,
                        constraints.maxHeight -
                            actionCardPlaceable.measuredHeight - bottomInsetsPlaceable.measuredHeight
                    )
                } else {
                    infoCardPlaceable.place(0, topInsetsPlaceable.measuredHeight)
                    actionCardPlaceable.place(0, constraints.maxHeight)
                }
            }
        },
        modifier = modifier
    )
}

private sealed interface InteractiveCellUniverseOverlayLayoutTypes {
    sealed interface InsetsTypes : InteractiveCellUniverseOverlayLayoutTypes {
        object TopInsets : InsetsTypes
        object BottomInsets : InsetsTypes
    }
    sealed interface CardTypes : InteractiveCellUniverseOverlayLayoutTypes {
        object CellUniverseInfoCard : CardTypes
        object CellUniverseActionCard : CardTypes
    }
}
