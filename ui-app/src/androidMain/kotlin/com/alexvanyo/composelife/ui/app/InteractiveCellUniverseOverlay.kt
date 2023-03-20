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

package com.alexvanyo.composelife.ui.app

import androidx.compose.animation.core.animateDpAsState
import androidx.compose.animation.core.animateFloatAsState
import androidx.compose.foundation.background
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.Spacer
import androidx.compose.foundation.layout.WindowInsets
import androidx.compose.foundation.layout.WindowInsetsSides
import androidx.compose.foundation.layout.add
import androidx.compose.foundation.layout.fillMaxWidth
import androidx.compose.foundation.layout.only
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
import androidx.compose.ui.layout.boundsInParent
import androidx.compose.ui.layout.layoutId
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.platform.testTag
import androidx.compose.ui.unit.dp
import androidx.compose.ui.unit.lerp
import androidx.compose.ui.unit.round
import androidx.compose.ui.unit.sp
import androidx.compose.ui.unit.toIntRect
import com.alexvanyo.composelife.model.TemporalGameOfLifeState
import com.alexvanyo.composelife.ui.app.InteractiveCellUniverseOverlayLayoutTypes.BottomInsets
import com.alexvanyo.composelife.ui.app.InteractiveCellUniverseOverlayLayoutTypes.CellUniverseActionCard
import com.alexvanyo.composelife.ui.app.InteractiveCellUniverseOverlayLayoutTypes.CellUniverseInfoCard
import com.alexvanyo.composelife.ui.app.InteractiveCellUniverseOverlayLayoutTypes.TopInsets
import com.alexvanyo.composelife.ui.app.action.CellUniverseActionCard
import com.alexvanyo.composelife.ui.app.action.CellUniverseActionCardHiltEntryPoint
import com.alexvanyo.composelife.ui.app.action.CellUniverseActionCardLocalEntryPoint
import com.alexvanyo.composelife.ui.app.action.rememberCellUniverseActionCardState
import com.alexvanyo.composelife.ui.app.cells.CellWindowState
import com.alexvanyo.composelife.ui.app.info.CellUniverseInfoCard
import com.alexvanyo.composelife.ui.app.info.rememberCellUniverseInfoCardState
import com.alexvanyo.composelife.ui.util.Layout
import com.alexvanyo.composelife.ui.util.PredictiveBackState
import com.alexvanyo.composelife.ui.util.TargetState
import com.alexvanyo.composelife.ui.util.WindowInsets
import com.alexvanyo.composelife.ui.util.Zero
import com.alexvanyo.composelife.ui.util.animatePlacement
import com.alexvanyo.composelife.ui.util.bottomEnd
import com.alexvanyo.composelife.ui.util.lerp
import com.alexvanyo.composelife.ui.util.predictiveBackHandler
import com.alexvanyo.composelife.ui.util.progressToTrue
import com.alexvanyo.composelife.ui.util.realBoundsInParent
import com.livefront.sealedenum.GenSealedEnum
import dagger.hilt.EntryPoint
import dagger.hilt.InstallIn
import dagger.hilt.android.components.ActivityComponent

@EntryPoint
@InstallIn(ActivityComponent::class)
interface InteractiveCellUniverseOverlayHiltEntryPoint :
    CellUniverseActionCardHiltEntryPoint

interface InteractiveCellUniverseOverlayLocalEntryPoint :
    CellUniverseActionCardLocalEntryPoint

context(InteractiveCellUniverseOverlayHiltEntryPoint, InteractiveCellUniverseOverlayLocalEntryPoint)
@Suppress("LongMethod", "ComplexMethod", "LongParameterList")
@Composable
fun InteractiveCellUniverseOverlay(
    temporalGameOfLifeState: TemporalGameOfLifeState,
    cellWindowState: CellWindowState,
    isViewportTracking: Boolean,
    setIsViewportTracking: (Boolean) -> Unit,
    windowSizeClass: WindowSizeClass,
    modifier: Modifier = Modifier,
) {
    var isActionCardTopCard by rememberSaveable { mutableStateOf(true) }

    val isInfoCardExpandedState = rememberSaveable { mutableStateOf(false) }
    val isActionCardExpandedState = rememberSaveable { mutableStateOf(false) }

    val isInfoCardExpanded = isInfoCardExpandedState.value
    fun setIsInfoCardExpanded(value: Boolean) {
        isInfoCardExpandedState.value = value
        if (value) {
            isActionCardExpandedState.value = false
            isActionCardTopCard = false
        }
    }

    val isActionCardExpanded = isActionCardExpandedState.value
    fun setIsActionCardExpanded(value: Boolean) {
        isActionCardExpandedState.value = value
        if (value) {
            isInfoCardExpandedState.value = false
            isActionCardTopCard = true
        }
    }

    val infoCardExpandedPredictiveBackState = if (isInfoCardExpanded && !isActionCardTopCard) {
        predictiveBackHandler {
            setIsInfoCardExpanded(false)
        }
    } else {
        PredictiveBackState.NotRunning
    }
    val actionCardExpandedPredictiveBackState = if (isActionCardExpanded) {
        predictiveBackHandler {
            setIsActionCardExpanded(false)
        }
    } else {
        PredictiveBackState.NotRunning
    }

    val infoCardState = rememberCellUniverseInfoCardState(
        setIsExpanded = ::setIsInfoCardExpanded,
        expandedTargetState = when (infoCardExpandedPredictiveBackState) {
            PredictiveBackState.NotRunning -> TargetState.Single(isInfoCardExpanded)
            is PredictiveBackState.Running -> {
                check(isInfoCardExpanded)
                TargetState.InProgress(
                    current = true,
                    provisional = false,
                    progress = infoCardExpandedPredictiveBackState.progress,
                )
            }
        },
    )
    val actionCardState = rememberCellUniverseActionCardState(
        setIsExpanded = ::setIsActionCardExpanded,
        enableBackHandler = isActionCardTopCard,
        expandedTargetState = when (actionCardExpandedPredictiveBackState) {
            PredictiveBackState.NotRunning -> TargetState.Single(isActionCardExpanded)
            is PredictiveBackState.Running -> {
                check(isActionCardExpanded)
                TargetState.InProgress(
                    current = true,
                    provisional = false,
                    progress = actionCardExpandedPredictiveBackState.progress,
                )
            }
        },
    )

    val progressToFullscreen = actionCardState.fullscreenTargetState.progressToTrue

    val targetWindowInsetsProgressToFullscreen by animateFloatAsState(progressToFullscreen)

    val targetWindowInsets = lerp(
        WindowInsets.safeDrawing.add(WindowInsets(all = 8.dp)),
        WindowInsets.Zero,
        targetWindowInsetsProgressToFullscreen
    )

    val cornerSize by animateDpAsState(
        targetValue = lerp(
            12.dp,
            0.dp,
            progressToFullscreen,
        ),
    )

    /**
     * `true` if we are currently showing a full-screen card, which is inferred to be the case if the corner size is 0
     * and we are still wanting to show the card as full-screen.
     */
    val isShowingFullscreen by remember {
        derivedStateOf {
            cornerSize == 0.dp &&
                when (val fullscreenTargetState = actionCardState.fullscreenTargetState) {
                    is TargetState.InProgress -> false
                    is TargetState.Single -> fullscreenTargetState.current
                }
        }
    }

    Layout(
        layoutIdTypes = InteractiveCellUniverseOverlayLayoutTypes.sealedEnum,
        content = {
            Spacer(
                modifier = Modifier
                    .windowInsetsTopHeight(WindowInsets.safeDrawing.only(WindowInsetsSides.Top))
                    .layoutId(TopInsets)
            )
            Spacer(
                modifier = Modifier
                    .windowInsetsBottomHeight(WindowInsets.safeDrawing.only(WindowInsetsSides.Bottom))
                    .layoutId(BottomInsets)
            )

            Box(
                modifier = Modifier
                    .fillMaxWidth()
                    .windowInsetsPadding(WindowInsets.safeDrawing)
                    .animatePlacement(
                        fixedPoint = { layoutCoordinates ->
                            layoutCoordinates.boundsInParent().topCenter.round()
                        },
                        parentFixedPoint = { parentLayoutCoordinates ->
                            parentLayoutCoordinates.size.toIntRect().topCenter
                        }
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

            Box(
                modifier = Modifier
                    .fillMaxWidth()
                    .then(
                        // If we are showing fullscreen, avoid animating placement at this level, since the card
                        // should effectively be fixed to be full screen
                        if (isShowingFullscreen) {
                            Modifier
                        } else {
                            Modifier.animatePlacement(
                                fixedPoint = { layoutCoordinates ->
                                    if (windowSizeClass.widthSizeClass == WindowWidthSizeClass.Compact) {
                                        layoutCoordinates.realBoundsInParent().bottomCenter.round()
                                    } else {
                                        layoutCoordinates.realBoundsInParent().bottomEnd.round()
                                    }
                                },
                                parentFixedPoint = { parentLayoutCoordinates ->
                                    if (windowSizeClass.widthSizeClass == WindowWidthSizeClass.Compact) {
                                        parentLayoutCoordinates.size.toIntRect().bottomCenter
                                    } else {
                                        parentLayoutCoordinates.size.toIntRect().bottomEnd
                                    }
                                }
                            )
                        }
                    )
                    .windowInsetsPadding(targetWindowInsets)
                    .layoutId(CellUniverseActionCard),
            ) {
                // TODO: Calling order is weird here, but required due to https://youtrack.jetbrains.com/issue/KT-51863
                CellUniverseActionCard(
                    temporalGameOfLifeState = temporalGameOfLifeState,
                    windowSizeClass = windowSizeClass,
                    isViewportTracking = isViewportTracking,
                    setIsViewportTracking = setIsViewportTracking,
                    actionCardState = actionCardState,
                    modifier = Modifier
                        .align(
                            if (windowSizeClass.widthSizeClass == WindowWidthSizeClass.Compact) {
                                Alignment.Center
                            } else {
                                Alignment.CenterEnd
                            },
                        )
                        .testTag("CellUniverseActionCard"),
                    shape = RoundedCornerShape(cornerSize),
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
                bottomInsetsPlaceable.place(0, constraints.maxHeight - bottomInsetsPlaceable.height)

                // If we can fit both cards, place them both on screen.
                // Otherwise, place the top-card (as determined by isActionCardTopCard) only aligned to the correct
                // side of the screen, and align the hidden card just off-screen.
                if (
                    infoCardPlaceable.height + actionCardPlaceable.height -
                    topInsetsPlaceable.height - bottomInsetsPlaceable.height <= constraints.maxHeight
                ) {
                    infoCardPlaceable.place(0, 0)
                    actionCardPlaceable.place(
                        0,
                        constraints.maxHeight - actionCardPlaceable.height
                    )
                } else if (isActionCardTopCard) {
                    infoCardPlaceable.place(0, -infoCardPlaceable.height + bottomInsetsPlaceable.height)
                    actionCardPlaceable.place(
                        0,
                        constraints.maxHeight - actionCardPlaceable.height,
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
