package com.alexvanyo.composelife.ui

import androidx.activity.compose.BackHandler
import androidx.compose.animation.core.animateDpAsState
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.ExperimentalLayoutApi
import androidx.compose.foundation.layout.PaddingValues
import androidx.compose.foundation.layout.Spacer
import androidx.compose.foundation.layout.WindowInsets
import androidx.compose.foundation.layout.asPaddingValues
import androidx.compose.foundation.layout.calculateEndPadding
import androidx.compose.foundation.layout.calculateStartPadding
import androidx.compose.foundation.layout.consumedWindowInsets
import androidx.compose.foundation.layout.fillMaxWidth
import androidx.compose.foundation.layout.padding
import androidx.compose.foundation.layout.safeDrawing
import androidx.compose.foundation.layout.windowInsetsBottomHeight
import androidx.compose.foundation.layout.windowInsetsPadding
import androidx.compose.foundation.layout.windowInsetsTopHeight
import androidx.compose.foundation.shape.RoundedCornerShape
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
import androidx.compose.ui.platform.LocalLayoutDirection
import androidx.compose.ui.platform.testTag
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.model.TemporalGameOfLifeState
import com.alexvanyo.composelife.ui.InteractiveCellUniverseOverlayLayoutTypes.BottomInsets
import com.alexvanyo.composelife.ui.InteractiveCellUniverseOverlayLayoutTypes.CellUniverseActionCard
import com.alexvanyo.composelife.ui.InteractiveCellUniverseOverlayLayoutTypes.CellUniverseInfoCard
import com.alexvanyo.composelife.ui.InteractiveCellUniverseOverlayLayoutTypes.TopInsets
import com.alexvanyo.composelife.ui.action.CellUniverseActionCard
import com.alexvanyo.composelife.ui.action.CellUniverseActionCardState
import com.alexvanyo.composelife.ui.action.rememberCellUniverseActionCardState
import com.alexvanyo.composelife.ui.cells.CellWindowState
import com.alexvanyo.composelife.ui.info.CellUniverseInfoCard
import com.alexvanyo.composelife.ui.info.CellUniverseInfoCardState
import com.alexvanyo.composelife.ui.info.rememberCellUniverseInfoCardState
import com.alexvanyo.composelife.ui.util.animatePlacement

@OptIn(ExperimentalLayoutApi::class)
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
                        delegateActionCardState.isExpanded = false
                        isActionCardTopCard = false
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
                    if (value) {
                        delegateInfoCardState.isExpanded = false
                        isActionCardTopCard = true
                    }
                }
        }
    }

    if (infoCardState.isExpanded || actionCardState.isExpanded) {
        check(!(infoCardState.isExpanded && actionCardState.isExpanded))

        BackHandler {
            if (actionCardState.isExpanded) {
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
                    .windowInsetsPadding(WindowInsets.safeDrawing)
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

            val windowInsets = WindowInsets.safeDrawing
            val windowInsetsPaddingValues = windowInsets.asPaddingValues()

            val outerPaddingStart by animateDpAsState(
                targetValue = if (actionCardState.isFullscreen) {
                    0.dp
                } else {
                    8.dp + windowInsetsPaddingValues.calculateStartPadding(LocalLayoutDirection.current)
                }
            )
            val outerPaddingTop by animateDpAsState(
                targetValue = if (actionCardState.isFullscreen) {
                    0.dp
                } else {
                    8.dp + windowInsetsPaddingValues.calculateTopPadding()
                }
            )
            val outerPaddingEnd by animateDpAsState(
                targetValue = if (actionCardState.isFullscreen) {
                    0.dp
                } else {
                    8.dp + windowInsetsPaddingValues.calculateEndPadding(LocalLayoutDirection.current)
                }
            )
            val outerPaddingBottom by animateDpAsState(
                targetValue = if (actionCardState.isFullscreen) {
                    0.dp
                } else {
                    8.dp + windowInsetsPaddingValues.calculateBottomPadding()
                }
            )

            val outerPadding = PaddingValues(
                start = outerPaddingStart,
                top = outerPaddingTop,
                end = outerPaddingEnd,
                bottom = outerPaddingBottom
            )

            val contentPaddingStart by animateDpAsState(
                targetValue = if (actionCardState.isFullscreen) {
                    windowInsetsPaddingValues.calculateStartPadding(LocalLayoutDirection.current)
                } else {
                    0.dp
                }
            )
            val contentPaddingTop by animateDpAsState(
                targetValue = if (actionCardState.isFullscreen) {
                    windowInsetsPaddingValues.calculateTopPadding()
                } else {
                    0.dp
                }
            )
            val contentPaddingEnd by animateDpAsState(
                targetValue = if (actionCardState.isFullscreen) {
                    windowInsetsPaddingValues.calculateEndPadding(LocalLayoutDirection.current)
                } else {
                    0.dp
                }
            )
            val contentPaddingBottom by animateDpAsState(
                targetValue = if (actionCardState.isFullscreen) {
                    windowInsetsPaddingValues.calculateBottomPadding()
                } else {
                    0.dp
                }
            )

            val contentPadding = PaddingValues(
                start = contentPaddingStart,
                top = contentPaddingTop,
                end = contentPaddingEnd,
                bottom = contentPaddingBottom
            )

            val cornerSize by animateDpAsState(
                targetValue = if (actionCardState.isFullscreen) {
                    0.dp
                } else {
                    12.dp
                }
            )

            Box(
                modifier = Modifier
                    .fillMaxWidth()
                    .consumedWindowInsets(windowInsets)
                    .animatePlacement(
                        alignment = Alignment.BottomCenter
                    )
                    .layoutId(CellUniverseActionCard)
            ) {
                CellUniverseActionCard(
                    isTopCard = isActionCardTopCard,
                    temporalGameOfLifeState = temporalGameOfLifeState,
                    actionCardState = actionCardState,
                    contentPadding = contentPadding,
                    shape = RoundedCornerShape(cornerSize),
                    modifier = Modifier
                        .align(Alignment.Center)
                        .padding(outerPadding)
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
                val placeable = measurable.measure(constraints)

                when (measurable.layoutId as InteractiveCellUniverseOverlayLayoutTypes) {
                    TopInsets -> topInsetsPlaceable = placeable
                    BottomInsets -> bottomInsetsPlaceable = placeable
                    CellUniverseInfoCard -> infoCardPlaceable = placeable
                    CellUniverseActionCard -> actionCardPlaceable = placeable
                }
            }

            layout(constraints.maxWidth, constraints.maxHeight) {
                topInsetsPlaceable.place(0, 0)
                bottomInsetsPlaceable.place(0, constraints.maxHeight - bottomInsetsPlaceable.measuredHeight)

                // If we can fit both cards, place them both on screen.
                // Otherwise, place the top-card (as determined by
                if (infoCardPlaceable.measuredHeight + actionCardPlaceable.measuredHeight -
                    topInsetsPlaceable.height - bottomInsetsPlaceable.height <= constraints.maxHeight
                ) {
                    infoCardPlaceable.place(0, 0)
                    actionCardPlaceable.place(
                        0,
                        constraints.maxHeight - actionCardPlaceable.measuredHeight
                    )
                } else if (isActionCardTopCard) {
                    infoCardPlaceable.place(0, bottomInsetsPlaceable.height - infoCardPlaceable.measuredHeight)
                    actionCardPlaceable.place(
                        0,
                        constraints.maxHeight - actionCardPlaceable.measuredHeight
                    )
                } else {
                    infoCardPlaceable.place(0, 0)
                    actionCardPlaceable.place(0, constraints.maxHeight - topInsetsPlaceable.height)
                }
            }
        },
        modifier = modifier
    )
}

private sealed interface InteractiveCellUniverseOverlayLayoutTypes {
    object TopInsets : InteractiveCellUniverseOverlayLayoutTypes
    object BottomInsets : InteractiveCellUniverseOverlayLayoutTypes
    object CellUniverseInfoCard : InteractiveCellUniverseOverlayLayoutTypes
    object CellUniverseActionCard : InteractiveCellUniverseOverlayLayoutTypes
}
