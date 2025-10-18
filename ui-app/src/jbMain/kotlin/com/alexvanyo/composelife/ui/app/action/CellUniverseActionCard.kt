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

package com.alexvanyo.composelife.ui.app.action

import androidx.compose.animation.core.Spring
import androidx.compose.animation.core.spring
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.WindowInsets
import androidx.compose.foundation.layout.add
import androidx.compose.foundation.layout.fillMaxWidth
import androidx.compose.foundation.layout.safeDrawing
import androidx.compose.foundation.layout.widthIn
import androidx.compose.foundation.layout.windowInsetsPadding
import androidx.compose.material3.CardDefaults
import androidx.compose.material3.ElevatedCard
import androidx.compose.runtime.Composable
import androidx.compose.runtime.CompositionLocalProvider
import androidx.compose.runtime.remember
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.layout.layoutId
import androidx.compose.ui.unit.dp
import androidx.compose.ui.unit.offset
import com.alexvanyo.composelife.model.DeserializationResult
import com.alexvanyo.composelife.model.TemporalGameOfLifeState
import com.alexvanyo.composelife.navigation.associateWithRenderablePanes
import com.alexvanyo.composelife.ui.app.action.CellUniverseActionCardLayoutTypes.ActionControlRow
import com.alexvanyo.composelife.ui.app.action.CellUniverseActionCardLayoutTypes.NavContainer
import com.alexvanyo.composelife.ui.mobile.component.LocalBackgroundColor
import com.alexvanyo.composelife.ui.settings.InlineSettingsPane
import com.alexvanyo.composelife.ui.settings.InlineSettingsPaneCtx
import com.alexvanyo.composelife.ui.settings.Setting
import com.alexvanyo.composelife.ui.util.AnimatedContent
import com.alexvanyo.composelife.ui.util.CrossfadePredictiveNavigationFrame
import com.alexvanyo.composelife.ui.util.Layout
import com.alexvanyo.composelife.ui.util.WindowInsets
import com.alexvanyo.composelife.ui.util.isImeAnimating
import com.livefront.sealedenum.GenSealedEnum
import com.livefront.sealedenum.SealedEnum
import kotlin.math.max

// region templated-ctx
@Suppress("ComposableNaming", "LongParameterList")
@Composable
private operator fun CellUniverseActionCardCtx.invoke(
    temporalGameOfLifeState: TemporalGameOfLifeState,
    onViewDeserializationInfo: (DeserializationResult) -> Unit,
    onSeeMoreSettingsClicked: () -> Unit,
    onOpenInSettingsClicked: (setting: Setting) -> Unit,
    actionCardState: CellUniverseActionCardState,
    modifier: Modifier = Modifier,
) = CellUniverseActionCardCtx.lambda(
    inlineEditPaneCtx,
    inlineSettingsPaneCtx,
    temporalGameOfLifeState,
    onViewDeserializationInfo,
    onSeeMoreSettingsClicked,
    onOpenInSettingsClicked,
    actionCardState,
    modifier,
)

private val CellUniverseActionCardCtx.Companion.lambda:
    @Composable (context(InlineEditPaneCtx, InlineSettingsPaneCtx) (
        temporalGameOfLifeState: TemporalGameOfLifeState,
        onViewDeserializationInfo: (DeserializationResult) -> Unit,
        onSeeMoreSettingsClicked: () -> Unit,
        onOpenInSettingsClicked: (setting: Setting) -> Unit,
        actionCardState: CellUniverseActionCardState,
        modifier: Modifier,
    ) -> Unit)
    get() = {
            temporalGameOfLifeState,
            onViewDeserializationInfo,
            onSeeMoreSettingsClicked,
            onOpenInSettingsClicked,
            actionCardState,
            modifier,
        ->
        CellUniverseActionCard(
            temporalGameOfLifeState = temporalGameOfLifeState,
            onViewDeserializationInfo = onViewDeserializationInfo,
            onSeeMoreSettingsClicked = onSeeMoreSettingsClicked,
            onOpenInSettingsClicked = onOpenInSettingsClicked,
            actionCardState = actionCardState,
            modifier = modifier,
        )
    }

context(ctx: CellUniverseActionCardCtx)
@Suppress("LongParameterList")
@Composable
fun CellUniverseActionCard(
    temporalGameOfLifeState: TemporalGameOfLifeState,
    onViewDeserializationInfo: (DeserializationResult) -> Unit,
    onSeeMoreSettingsClicked: () -> Unit,
    onOpenInSettingsClicked: (setting: Setting) -> Unit,
    actionCardState: CellUniverseActionCardState,
    modifier: Modifier = Modifier,
) = ctx(
    temporalGameOfLifeState = temporalGameOfLifeState,
    onViewDeserializationInfo = onViewDeserializationInfo,
    onSeeMoreSettingsClicked = onSeeMoreSettingsClicked,
    onOpenInSettingsClicked = onOpenInSettingsClicked,
    actionCardState = actionCardState,
    modifier = modifier,
)
// endregion templated-ctx

context(
    _: InlineEditPaneCtx,
_: InlineSettingsPaneCtx
)
@Suppress("LongParameterList", "LongMethod")
@Composable
private fun CellUniverseActionCard(
    temporalGameOfLifeState: TemporalGameOfLifeState,
    onViewDeserializationInfo: (DeserializationResult) -> Unit,
    onSeeMoreSettingsClicked: () -> Unit,
    onOpenInSettingsClicked: (setting: Setting) -> Unit,
    actionCardState: CellUniverseActionCardState,
    modifier: Modifier = Modifier,
) {
    CellUniverseActionCard(
        targetStepsPerSecond = temporalGameOfLifeState.targetStepsPerSecond,
        setTargetStepsPerSecond = { temporalGameOfLifeState.targetStepsPerSecond = it },
        generationsPerStep = temporalGameOfLifeState.generationsPerStep,
        setGenerationsPerStep = { temporalGameOfLifeState.generationsPerStep = it },
        onViewDeserializationInfo = onViewDeserializationInfo,
        onSeeMoreSettingsClicked = onSeeMoreSettingsClicked,
        onOpenInSettingsClicked = onOpenInSettingsClicked,
        actionCardState = actionCardState,
        modifier = modifier,
    )
}

context(
    _: InlineEditPaneCtx,
_: InlineSettingsPaneCtx
)
@Suppress("LongParameterList", "LongMethod", "ComplexMethod")
@Composable
fun CellUniverseActionCard(
    targetStepsPerSecond: Double,
    setTargetStepsPerSecond: (Double) -> Unit,
    generationsPerStep: Int,
    setGenerationsPerStep: (Int) -> Unit,
    onViewDeserializationInfo: (DeserializationResult) -> Unit,
    onSeeMoreSettingsClicked: () -> Unit,
    onOpenInSettingsClicked: (setting: Setting) -> Unit,
    actionCardState: CellUniverseActionCardState,
    modifier: Modifier = Modifier,
) {
    val contentScrollStateMap = actionCardState.contentScrollStateMap
    val currentScrollState = contentScrollStateMap.getValue(
        actionCardState.inlineNavigationState.currentEntryId,
    )

    val colors = CardDefaults.elevatedCardColors()
    ElevatedCard(
        modifier = modifier.windowInsetsPadding(
            WindowInsets.safeDrawing.add(WindowInsets(all = 8.dp)),
        ),
        colors = colors,
    ) {
        CompositionLocalProvider(
            LocalBackgroundColor provides colors.containerColor,
        ) {
            Layout(
                layoutIdTypes = CellUniverseActionCardLayoutTypes._sealedEnum,
                content = {
                    Box(
                        modifier = Modifier
                            .layoutId(ActionControlRow)
                            .widthIn(max = 480.dp),
                        propagateMinConstraints = true,
                    ) {
                        ActionControlRow(
                            actionControlRowState = actionCardState.actionControlRowState,
                        )
                    }

                    val renderableNavigationState = associateWithRenderablePanes(
                        actionCardState.inlineNavigationState,
                    ) { entry ->
                        // Cache the scroll state based for the target entry id.
                        // This value won't change normally, but it will ensure we keep using
                        // the old state while being removed from the backstack
                        val scrollState =
                            remember { contentScrollStateMap.getValue(entry.id) }

                        Box(
                            Modifier.widthIn(max = 480.dp),
                        ) {
                            when (entry.value) {
                                is InlineActionCardNavigation.Speed -> {
                                    InlineSpeedPane(
                                        targetStepsPerSecond = targetStepsPerSecond,
                                        setTargetStepsPerSecond = setTargetStepsPerSecond,
                                        generationsPerStep = generationsPerStep,
                                        setGenerationsPerStep = setGenerationsPerStep,
                                        scrollState = scrollState,
                                        modifier = Modifier.fillMaxWidth(),
                                    )
                                }

                                is InlineActionCardNavigation.Edit -> {
                                    InlineEditPane(
                                        setSelectionToCellState = actionCardState.editingState::setSelectionToCellState,
                                        onViewDeserializationInfo = onViewDeserializationInfo,
                                        modifier = Modifier.fillMaxWidth(),
                                        scrollState = scrollState,
                                    )
                                }

                                is InlineActionCardNavigation.Settings -> {
                                    InlineSettingsPane(
                                        onSeeMoreClicked = onSeeMoreSettingsClicked,
                                        onOpenInSettingsClicked = onOpenInSettingsClicked,
                                        modifier = Modifier.fillMaxWidth(),
                                        scrollState = scrollState,
                                    )
                                }
                            }
                        }
                    }

                    AnimatedContent(
                        targetState = actionCardState.expandedTargetState,
                        contentAlignment = Alignment.BottomCenter,
                        contentSizeAnimationSpec = spring(
                            stiffness = Spring.StiffnessMedium,
                        ),
                        animateInternalContentSizeChanges = !WindowInsets.isImeAnimating,
                        modifier = Modifier.layoutId(NavContainer),
                    ) { isExpanded ->
                        if (isExpanded) {
                            Column(
                                horizontalAlignment = Alignment.CenterHorizontally,
                            ) {
                                CrossfadePredictiveNavigationFrame(
                                    renderableNavigationState = renderableNavigationState,
                                    navigationEventTransitionState =
                                    actionCardState.inlineNavigationEventTransitionState,
                                    contentAlignment = Alignment.BottomCenter,
                                    animateInternalContentSizeChanges = false,
                                    modifier = Modifier.weight(1f, fill = false),
                                )

                                Box(
                                    modifier = Modifier.widthIn(max = 480.dp),
                                ) {
                                    ActionCardNavigationBar(
                                        actionCardState = actionCardState,
                                        isElevated = currentScrollState.canScrollBackward,
                                    )
                                }
                            }
                        }
                    }
                },
                measurePolicy = { measurables, constraints ->
                    val actionControlRowMeasurable = measurables.getValue(ActionControlRow)
                    val navContainerMeasurable = measurables.getValue(NavContainer)

                    // Measure the nav container after removing the height that the action control row will
                    // take up
                    val navContainerPlaceable = navContainerMeasurable.measure(
                        constraints.offset(
                            vertical = -actionControlRowMeasurable.minIntrinsicHeight(constraints.maxWidth),
                        ),
                    )
                    // Measure the action control row to at least as big as the nav container
                    val actionControlRowPlaceable = actionControlRowMeasurable.measure(
                        constraints.copy(minWidth = navContainerPlaceable.width),
                    )

                    val width = max(actionControlRowPlaceable.width, navContainerPlaceable.width)

                    layout(
                        width = width,
                        height = actionControlRowPlaceable.height + navContainerPlaceable.height,
                    ) {
                        actionControlRowPlaceable.placeRelative(0, 0)
                        navContainerPlaceable.placeRelative(
                            (width - navContainerPlaceable.width) / 2,
                            actionControlRowPlaceable.height,
                        )
                    }
                },
            )
        }
    }
}

internal sealed interface CellUniverseActionCardLayoutTypes {
    data object ActionControlRow : CellUniverseActionCardLayoutTypes
    data object NavContainer : CellUniverseActionCardLayoutTypes

    @GenSealedEnum
    companion object
}

internal expect val CellUniverseActionCardLayoutTypes.Companion._sealedEnum:
    SealedEnum<CellUniverseActionCardLayoutTypes>
