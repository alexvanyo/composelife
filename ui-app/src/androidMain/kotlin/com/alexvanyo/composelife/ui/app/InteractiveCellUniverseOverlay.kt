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

import androidx.compose.animation.core.Animatable
import androidx.compose.animation.core.AnimationVector1D
import androidx.compose.animation.core.VectorConverter
import androidx.compose.animation.core.spring
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.Spacer
import androidx.compose.foundation.layout.WindowInsets
import androidx.compose.foundation.layout.fillMaxWidth
import androidx.compose.foundation.layout.padding
import androidx.compose.foundation.layout.safeDrawing
import androidx.compose.foundation.layout.sizeIn
import androidx.compose.foundation.layout.windowInsetsBottomHeight
import androidx.compose.foundation.layout.windowInsetsPadding
import androidx.compose.foundation.layout.windowInsetsTopHeight
import androidx.compose.material3.windowsizeclass.WindowSizeClass
import androidx.compose.material3.windowsizeclass.WindowWidthSizeClass
import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.runtime.setValue
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.layout.layoutId
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.platform.testTag
import androidx.compose.ui.unit.dp
import androidx.compose.ui.unit.sp
import androidx.compose.ui.util.lerp
import com.alexvanyo.composelife.model.TemporalGameOfLifeState
import com.alexvanyo.composelife.ui.app.InteractiveCellUniverseOverlayLayoutTypes.BottomInsets
import com.alexvanyo.composelife.ui.app.InteractiveCellUniverseOverlayLayoutTypes.CellUniverseActionCard
import com.alexvanyo.composelife.ui.app.InteractiveCellUniverseOverlayLayoutTypes.CellUniverseInfoCard
import com.alexvanyo.composelife.ui.app.InteractiveCellUniverseOverlayLayoutTypes.TopInsets
import com.alexvanyo.composelife.ui.app.action.CellUniverseActionCard
import com.alexvanyo.composelife.ui.app.action.CellUniverseActionCardHiltEntryPoint
import com.alexvanyo.composelife.ui.app.action.CellUniverseActionCardLocalEntryPoint
import com.alexvanyo.composelife.ui.app.cells.CellWindowState
import com.alexvanyo.composelife.ui.app.info.CellUniverseInfoCard
import com.alexvanyo.composelife.ui.util.Layout
import com.alexvanyo.composelife.ui.util.isInProgress
import com.livefront.sealedenum.GenSealedEnum
import dagger.hilt.EntryPoint
import dagger.hilt.InstallIn
import dagger.hilt.android.components.ActivityComponent
import kotlinx.coroutines.launch

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
    interactiveCellUniverseState: InteractiveCellUniverseState,
    cellWindowState: CellWindowState,
    windowSizeClass: WindowSizeClass,
    modifier: Modifier = Modifier,
) {
    val scope = rememberCoroutineScope()
    var infoCardAnimatable by remember {
        mutableStateOf<Animatable<Float, AnimationVector1D>?>(null)
    }
    var actionCardAnimatable by remember {
        mutableStateOf<Animatable<Float, AnimationVector1D>?>(null)
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
                    .layoutId(CellUniverseInfoCard),
            ) {
                CellUniverseInfoCard(
                    cellWindowState = cellWindowState,
                    evolutionStatus = temporalGameOfLifeState.status,
                    infoCardState = interactiveCellUniverseState.infoCardState,
                    modifier = Modifier
                        .align(Alignment.CenterEnd)
                        .padding(8.dp)
                        .sizeIn(maxWidth = with(LocalDensity.current) { 400.sp.toDp() })
                        .testTag("CellUniverseInfoCard"),
                )
            }

            // TODO: Calling order is weird here, but required due to https://youtrack.jetbrains.com/issue/KT-51863
            CellUniverseActionCard(
                temporalGameOfLifeState = temporalGameOfLifeState,
                windowSizeClass = windowSizeClass,
                isViewportTracking = interactiveCellUniverseState.isViewportTracking,
                setIsViewportTracking = { interactiveCellUniverseState.isViewportTracking = it },
                actionCardState = interactiveCellUniverseState.actionCardState,
                modifier = Modifier
                    .layoutId(CellUniverseActionCard)
                    .testTag("CellUniverseActionCard"),
            )
        },
        measurePolicy = { measurables, constraints ->
            val topInsetsPlaceable = measurables.getValue(TopInsets).measure(constraints)
            val bottomInsetsPlaceable = measurables.getValue(BottomInsets).measure(constraints)
            val infoCardPlaceable = measurables.getValue(CellUniverseInfoCard).measure(constraints)
            val actionCardPlaceable = measurables.getValue(CellUniverseActionCard).measure(constraints)

            layout(constraints.maxWidth, constraints.maxHeight) {
                topInsetsPlaceable.place(0, 0)
                bottomInsetsPlaceable.place(0, constraints.maxHeight - bottomInsetsPlaceable.height)

                val displayInfoCardOffscreen: Boolean
                val displayActionCardOffscreen: Boolean

                // If we aren't trying to show fullscreen and we can fit both cards, place them both on screen.
                // Otherwise, place the top-card (as determined by isActionCardTopCard) only aligned to the correct
                // side of the screen, and align the hidden card just off-screen.
                val fullscreenTargetState =
                    interactiveCellUniverseState.actionCardState.fullscreenTargetState
                if (
                    (fullscreenTargetState.isInProgress() || !fullscreenTargetState.current) &&
                    infoCardPlaceable.height + actionCardPlaceable.height -
                    topInsetsPlaceable.height - bottomInsetsPlaceable.height <= constraints.maxHeight
                ) {
                    displayInfoCardOffscreen = false
                    displayActionCardOffscreen = false
                } else if (interactiveCellUniverseState.isActionCardTopCard) {
                    displayInfoCardOffscreen = true
                    displayActionCardOffscreen = false
                } else {
                    displayInfoCardOffscreen = false
                    displayActionCardOffscreen = true
                }

                val infoCardYOffscreen = -infoCardPlaceable.height + bottomInsetsPlaceable.height
                val infoCardYOnscreen = 0

                val targetInfoCardFractionOffscreen = if (displayInfoCardOffscreen) 1f else 0f

                val infoAnim = infoCardAnimatable ?: Animatable(
                    initialValue = targetInfoCardFractionOffscreen,
                    typeConverter = Float.VectorConverter,
                ).also { infoCardAnimatable = it }
                if (infoAnim.targetValue != targetInfoCardFractionOffscreen) {
                    scope.launch {
                        infoAnim.animateTo(targetInfoCardFractionOffscreen, spring())
                    }
                }

                infoCardPlaceable.place(0, lerp(infoCardYOnscreen, infoCardYOffscreen, infoAnim.value))

                val actionCardX = if (windowSizeClass.widthSizeClass == WindowWidthSizeClass.Compact) {
                    (constraints.maxWidth - actionCardPlaceable.width) / 2
                } else {
                    constraints.maxWidth - actionCardPlaceable.width
                }

                val actionCardYOffscreen = constraints.maxHeight - topInsetsPlaceable.height
                val actionCardYOnscreen = constraints.maxHeight - actionCardPlaceable.height

                val targetActionCardFractionOffscreen = if (displayActionCardOffscreen) 1f else 0f

                val actionAnim = actionCardAnimatable ?: Animatable(
                    initialValue = targetActionCardFractionOffscreen,
                    typeConverter = Float.VectorConverter,
                ).also { actionCardAnimatable = it }
                if (actionAnim.targetValue != targetActionCardFractionOffscreen) {
                    scope.launch {
                        actionAnim.animateTo(targetActionCardFractionOffscreen, spring())
                    }
                }

                actionCardPlaceable.place(
                    actionCardX,
                    lerp(actionCardYOnscreen, actionCardYOffscreen, actionAnim.value),
                )
            }
        },
        modifier = modifier,
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
