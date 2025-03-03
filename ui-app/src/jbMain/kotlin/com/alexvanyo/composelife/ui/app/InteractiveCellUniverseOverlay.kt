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
import androidx.window.core.layout.WindowSizeClass
import com.alexvanyo.composelife.model.DeserializationResult
import com.alexvanyo.composelife.model.TemporalGameOfLifeState
import com.alexvanyo.composelife.sessionvalue.SessionValue
import com.alexvanyo.composelife.ui.app.InteractiveCellUniverseOverlayLayoutTypes.BottomInsets
import com.alexvanyo.composelife.ui.app.InteractiveCellUniverseOverlayLayoutTypes.CellUniverseActionCard
import com.alexvanyo.composelife.ui.app.InteractiveCellUniverseOverlayLayoutTypes.CellUniverseInfoCard
import com.alexvanyo.composelife.ui.app.InteractiveCellUniverseOverlayLayoutTypes.TopInsets
import com.alexvanyo.composelife.ui.app.action.CellUniverseActionCard
import com.alexvanyo.composelife.ui.app.info.CellUniverseInfoCard
import com.alexvanyo.composelife.ui.cells.CellWindowViewportState
import com.alexvanyo.composelife.ui.cells.SelectionState
import com.alexvanyo.composelife.ui.settings.Setting
import com.alexvanyo.composelife.ui.util.Layout
import com.livefront.sealedenum.GenSealedEnum
import com.livefront.sealedenum.SealedEnum
import kotlinx.coroutines.launch
import kotlin.uuid.Uuid

context(InteractiveCellUniverseOverlayInjectEntryPoint, InteractiveCellUniverseOverlayLocalEntryPoint)
@Suppress("LongMethod", "ComplexMethod", "LongParameterList")
@Composable
fun InteractiveCellUniverseOverlay(
    temporalGameOfLifeState: TemporalGameOfLifeState,
    interactiveCellUniverseState: InteractiveCellUniverseState,
    cellWindowViewportState: CellWindowViewportState,
    windowSizeClass: WindowSizeClass,
    onSeeMoreSettingsClicked: () -> Unit,
    onOpenInSettingsClicked: (setting: Setting) -> Unit,
    onViewDeserializationInfo: (DeserializationResult) -> Unit,
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
        layoutIdTypes = InteractiveCellUniverseOverlayLayoutTypes._sealedEnum,
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
                    cellWindowViewportState = cellWindowViewportState,
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
                isViewportTracking = interactiveCellUniverseState.isViewportTracking,
                setIsViewportTracking = { interactiveCellUniverseState.isViewportTracking = it },
                isImmersiveMode = interactiveCellUniverseState.isImmersiveMode,
                setIsImmersiveMode = { interactiveCellUniverseState.isImmersiveMode = it },
                selectionState = interactiveCellUniverseState.cellWindowInteractionState.selectionSessionState.value,
                setSelectionToCellState = interactiveCellUniverseState::setSelectionToCellState,
                onClearSelection = {
                    interactiveCellUniverseState.cellWindowInteractionState.selectionSessionState =
                        SessionValue(Uuid.random(), Uuid.random(), SelectionState.NoSelection)
                },
                onCopy = interactiveCellUniverseState::onCopy,
                onCut = interactiveCellUniverseState::onCut,
                onPaste = interactiveCellUniverseState::onPaste,
                onApplyPaste = interactiveCellUniverseState::onApplyPaste,
                onSeeMoreSettingsClicked = onSeeMoreSettingsClicked,
                onOpenInSettingsClicked = onOpenInSettingsClicked,
                onViewDeserializationInfo = onViewDeserializationInfo,
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

                // If we can fit both cards, place them both on screen.
                // Otherwise, place the top-card (as determined by isActionCardTopCard) only aligned to the correct
                // side of the screen, and align the hidden card just off-screen.
                if (
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

                val actionCardX = if (
                    windowSizeClass.isWidthAtLeastBreakpoint(WindowSizeClass.WIDTH_DP_MEDIUM_LOWER_BOUND)
                ) {
                    constraints.maxWidth - actionCardPlaceable.width
                } else {
                    (constraints.maxWidth - actionCardPlaceable.width) / 2
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
    data object TopInsets : InteractiveCellUniverseOverlayLayoutTypes
    data object BottomInsets : InteractiveCellUniverseOverlayLayoutTypes
    data object CellUniverseInfoCard : InteractiveCellUniverseOverlayLayoutTypes
    data object CellUniverseActionCard : InteractiveCellUniverseOverlayLayoutTypes

    @GenSealedEnum
    companion object
}

internal expect val InteractiveCellUniverseOverlayLayoutTypes.Companion._sealedEnum:
    SealedEnum<InteractiveCellUniverseOverlayLayoutTypes>
