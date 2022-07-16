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

package com.alexvanyo.composelife.ui

import androidx.activity.compose.BackHandler
import androidx.compose.animation.core.Spring
import androidx.compose.animation.core.animateDpAsState
import androidx.compose.animation.core.snap
import androidx.compose.animation.core.spring
import androidx.compose.foundation.background
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.BoxWithConstraints
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
import androidx.compose.foundation.layout.sizeIn
import androidx.compose.foundation.layout.windowInsetsBottomHeight
import androidx.compose.foundation.layout.windowInsetsPadding
import androidx.compose.foundation.layout.windowInsetsTopHeight
import androidx.compose.foundation.shape.RoundedCornerShape
import androidx.compose.material3.MaterialTheme
import androidx.compose.material3.windowsizeclass.WindowSizeClass
import androidx.compose.material3.windowsizeclass.WindowWidthSizeClass
import androidx.compose.runtime.Composable
import androidx.compose.runtime.derivedStateOf
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.setValue
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.layout.layoutId
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.platform.LocalLayoutDirection
import androidx.compose.ui.platform.testTag
import androidx.compose.ui.unit.Dp
import androidx.compose.ui.unit.LayoutDirection
import androidx.compose.ui.unit.dp
import androidx.compose.ui.unit.sp
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
import com.alexvanyo.composelife.ui.util.Layout
import com.alexvanyo.composelife.ui.util.animatePlacement
import com.livefront.sealedenum.GenSealedEnum

@OptIn(ExperimentalLayoutApi::class)
@Suppress("LongMethod", "ComplexMethod")
@Composable
fun InteractiveCellUniverseOverlay(
    temporalGameOfLifeState: TemporalGameOfLifeState,
    cellWindowState: CellWindowState,
    windowSizeClass: WindowSizeClass,
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
            if (!infoCardState.isExpanded || isActionCardTopCard) {
                actionCardState.isExpanded = false
            } else {
                check(infoCardState.isExpanded)
                infoCardState.isExpanded = false
            }
        }
    }

    val windowInsets = WindowInsets.safeDrawing
    val windowInsetsPaddingValues = windowInsets.asPaddingValues()

    val outerPaddingStart by animateDpAsState(
        targetValue = if (actionCardState.isFullscreen) {
            0.dp
        } else {
            8.dp + windowInsetsPaddingValues.calculateStartPadding(LocalLayoutDirection.current)
        },
    )
    val outerPaddingTop by animateDpAsState(
        targetValue = if (actionCardState.isFullscreen) {
            0.dp
        } else {
            8.dp + windowInsetsPaddingValues.calculateTopPadding()
        },
    )
    val outerPaddingEnd by animateDpAsState(
        targetValue = if (actionCardState.isFullscreen) {
            0.dp
        } else {
            8.dp + windowInsetsPaddingValues.calculateEndPadding(LocalLayoutDirection.current)
        },
    )
    val outerPaddingBottom by animateDpAsState(
        targetValue = if (actionCardState.isFullscreen) {
            0.dp
        } else {
            8.dp + windowInsetsPaddingValues.calculateBottomPadding()
        },
    )
    val outerPaddingLeft: Dp
    val outerPaddingRight: Dp
    if (LocalLayoutDirection.current == LayoutDirection.Ltr) {
        outerPaddingLeft = outerPaddingStart
        outerPaddingRight = outerPaddingEnd
    } else {
        outerPaddingLeft = outerPaddingEnd
        outerPaddingRight = outerPaddingStart
    }

    val outerPadding = PaddingValues(
        start = outerPaddingStart,
        top = outerPaddingTop,
        end = outerPaddingEnd,
        bottom = outerPaddingBottom,
    )
    val consumedWindowInsets = WindowInsets(
        left = outerPaddingLeft,
        top = outerPaddingTop,
        right = outerPaddingRight,
        bottom = outerPaddingBottom,
    )

    val cornerSize by animateDpAsState(
        targetValue = if (actionCardState.isFullscreen) {
            0.dp
        } else {
            12.dp
        },
    )

    /**
     * `true` if we are currently showing a full-screen card, which is inferred to be the case if the outer padding
     * is 0 and we are still wanting to show the card as full-screen.
     */
    val isShowingFullscreen by remember {
        derivedStateOf {
            outerPaddingStart == 0.dp &&
                outerPaddingTop == 0.dp &&
                outerPaddingEnd == 0.dp &&
                outerPaddingBottom == 0.dp &&
                actionCardState.isFullscreen
        }
    }

    Layout(
        layoutIdTypes = InteractiveCellUniverseOverlayLayoutTypes.sealedEnum,
        content = {
            Spacer(
                modifier = Modifier
                    .windowInsetsTopHeight(WindowInsets.safeDrawing)
                    .layoutId(TopInsets),
            )
            Spacer(
                modifier = Modifier
                    .windowInsetsBottomHeight(WindowInsets.safeDrawing)
                    .layoutId(BottomInsets),
            )

            Box(
                modifier = Modifier
                    .fillMaxWidth()
                    .windowInsetsPadding(WindowInsets.safeDrawing)
                    .animatePlacement(
                        alignment = Alignment.TopCenter,
                    )
                    .layoutId(CellUniverseInfoCard),
            ) {
                CellUniverseInfoCard(
                    cellWindowState = cellWindowState,
                    evolutionStatus = temporalGameOfLifeState.status,
                    infoCardState = infoCardState,
                    modifier = Modifier
                        .align(Alignment.CenterEnd)
                        .padding(8.dp)
                        .sizeIn(maxWidth = with(LocalDensity.current) { 400.sp.toDp() })
                        .testTag("CellUniverseInfoCard"),
                )
            }

            BoxWithConstraints(
                modifier = Modifier
                    .fillMaxWidth()
                    .consumedWindowInsets(consumedWindowInsets)
                    .animatePlacement(
                        // If we are showing fullscreen, avoid animating placement at this level, since the card
                        // should effectively be fixed to be full screen
                        animationSpec = if (isShowingFullscreen) {
                            snap()
                        } else {
                            spring(stiffness = Spring.StiffnessMedium)
                        },
                        alignment = Alignment.BottomCenter,
                    )
                    .layoutId(CellUniverseActionCard),
            ) {
                val confinedWidth by animateDpAsState(if (actionCardState.isFullscreen) maxWidth else 480.dp)

                CellUniverseActionCard(
                    windowSizeClass = windowSizeClass,
                    isTopCard = isActionCardTopCard,
                    temporalGameOfLifeState = temporalGameOfLifeState,
                    actionCardState = actionCardState,
                    shape = RoundedCornerShape(cornerSize),
                    modifier = Modifier
                        .align(
                            if (windowSizeClass.widthSizeClass == WindowWidthSizeClass.Compact) {
                                Alignment.Center
                            } else {
                                Alignment.CenterEnd
                            },
                        )
                        .padding(outerPadding)
                        .sizeIn(maxWidth = confinedWidth)
                        .testTag("CellUniverseActionCard"),
                )
            }
        },
        measurePolicy = { measurables, constraints ->
            val placeables = measurables.mapValues { (_, measurable) -> measurable.measure(constraints) }
            val topInsetsPlaceable = placeables.getValue(TopInsets)
            val bottomInsetsPlaceable = placeables.getValue(BottomInsets)
            val infoCardPlaceable = placeables.getValue(CellUniverseInfoCard)
            val actionCardPlaceable = placeables.getValue(CellUniverseActionCard)

            layout(constraints.maxWidth, constraints.maxHeight) {
                topInsetsPlaceable.place(0, 0)
                bottomInsetsPlaceable.place(0, constraints.maxHeight - bottomInsetsPlaceable.measuredHeight)

                // If we can fit both cards, place them both on screen.
                // Otherwise, place the top-card (as determined by isActionCardTopCard) only aligned to the correct
                // side of the screen, and align the hidden card just off-screen.
                if (infoCardPlaceable.measuredHeight + actionCardPlaceable.measuredHeight -
                    topInsetsPlaceable.height - bottomInsetsPlaceable.height <= constraints.maxHeight
                ) {
                    infoCardPlaceable.place(0, 0)
                    actionCardPlaceable.place(
                        0,
                        constraints.maxHeight - actionCardPlaceable.measuredHeight,
                    )
                } else if (isActionCardTopCard) {
                    infoCardPlaceable.place(0, bottomInsetsPlaceable.height - infoCardPlaceable.measuredHeight)
                    actionCardPlaceable.place(
                        0,
                        constraints.maxHeight - actionCardPlaceable.measuredHeight,
                    )
                } else {
                    infoCardPlaceable.place(0, 0)
                    actionCardPlaceable.place(0, constraints.maxHeight - topInsetsPlaceable.height)
                }
            }
        },
        modifier = modifier
            .then(
                // If we are showing a card fullscreen, put an opaque background on the overlay (between the cards
                // and the content underneath) to ensure content underneath is masked completely during animations
                // while remaining fullscreen.
                if (isShowingFullscreen) {
                    Modifier.background(MaterialTheme.colorScheme.surface)
                } else {
                    Modifier
                },
            ),
    )
}

internal sealed interface InteractiveCellUniverseOverlayLayoutTypes {
    object TopInsets : InteractiveCellUniverseOverlayLayoutTypes
    object BottomInsets : InteractiveCellUniverseOverlayLayoutTypes
    object CellUniverseInfoCard : InteractiveCellUniverseOverlayLayoutTypes
    object CellUniverseActionCard : InteractiveCellUniverseOverlayLayoutTypes

    @GenSealedEnum
    companion object
}
