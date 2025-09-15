/*
 * Copyright 2023 The Android Open Source Project
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

import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.runtime.Composable
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.window.core.layout.WindowSizeClass
import com.alexvanyo.composelife.algorithm.GameOfLifeAlgorithm
import com.alexvanyo.composelife.data.CellStateRepository
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.model.DeserializationResult
import com.alexvanyo.composelife.ui.app.component.GameOfLifeProgressIndicator
import com.alexvanyo.composelife.ui.app.component.GameOfLifeProgressIndicatorCtx
import com.alexvanyo.composelife.ui.settings.Setting
import kotlin.time.Clock

// region templated-ctx
@Suppress("ComposableNaming", "LongParameterList")
@Composable
private operator fun CellUniversePaneCtx.invoke(
    windowSizeClass: WindowSizeClass,
    onSeeMoreSettingsClicked: () -> Unit,
    onOpenInSettingsClicked: (setting: Setting) -> Unit,
    onViewDeserializationInfo: (DeserializationResult) -> Unit,
    modifier: Modifier = Modifier,
    cellUniversePaneState: CellUniversePaneState = rememberCellUniversePaneState(),
) = CellUniversePaneCtx.lambda(
    cellStateRepository,
    gameOfLifeAlgorithm,
    dispatchers,
    clock,
    gameOfLifeProgressIndicatorCtx,
    interactiveCellUniverseCtx,
    windowSizeClass,
    onSeeMoreSettingsClicked,
    onOpenInSettingsClicked,
    onViewDeserializationInfo,
    modifier,
    cellUniversePaneState,
)

private val CellUniversePaneCtx.Companion.lambda:
    @Composable context(
        CellStateRepository,
        GameOfLifeAlgorithm,
        ComposeLifeDispatchers,
        Clock,
        GameOfLifeProgressIndicatorCtx,
        InteractiveCellUniverseCtx,
    )
    (
        windowSizeClass: WindowSizeClass,
        onSeeMoreSettingsClicked: () -> Unit,
        onOpenInSettingsClicked: (setting: Setting) -> Unit,
        onViewDeserializationInfo: (DeserializationResult) -> Unit,
        modifier: Modifier,
        cellUniversePaneState: CellUniversePaneState,
    ) -> Unit
    get() = {
            windowSizeClass,
            onSeeMoreSettingsClicked,
            onOpenInSettingsClicked,
            onViewDeserializationInfo,
            modifier,
            cellUniversePaneState,
        ->
        CellUniversePane(
            windowSizeClass = windowSizeClass,
            onSeeMoreSettingsClicked = onSeeMoreSettingsClicked,
            onOpenInSettingsClicked = onOpenInSettingsClicked,
            onViewDeserializationInfo = onViewDeserializationInfo,
            modifier = modifier,
            cellUniversePaneState = cellUniversePaneState,
        )
    }

@Suppress("LongParameterList")
@Composable
context(ctx: CellUniversePaneCtx)
fun CellUniversePane(
    windowSizeClass: WindowSizeClass,
    onSeeMoreSettingsClicked: () -> Unit,
    onOpenInSettingsClicked: (setting: Setting) -> Unit,
    onViewDeserializationInfo: (DeserializationResult) -> Unit,
    modifier: Modifier = Modifier,
    cellUniversePaneState: CellUniversePaneState = rememberCellUniversePaneState(),
) = ctx(
    windowSizeClass = windowSizeClass,
    onSeeMoreSettingsClicked = onSeeMoreSettingsClicked,
    onOpenInSettingsClicked = onOpenInSettingsClicked,
    onViewDeserializationInfo = onViewDeserializationInfo,
    modifier = modifier,
    cellUniversePaneState = cellUniversePaneState,
)
// endregion templated-ctx

@Suppress("LongParameterList")
@Composable
context(
    cellStateRepository: CellStateRepository,
    gameOfLifeAlgorithm: GameOfLifeAlgorithm,
    dispatchers: ComposeLifeDispatchers,
    clock: Clock,
    _: GameOfLifeProgressIndicatorCtx,
    _: InteractiveCellUniverseCtx,
)
private fun CellUniversePane(
    windowSizeClass: WindowSizeClass,
    onSeeMoreSettingsClicked: () -> Unit,
    onOpenInSettingsClicked: (setting: Setting) -> Unit,
    onViewDeserializationInfo: (DeserializationResult) -> Unit,
    modifier: Modifier = Modifier,
    cellUniversePaneState: CellUniversePaneState =
        rememberCellUniversePaneState(
            cellStateRepository = cellStateRepository,
            gameOfLifeAlgorithm = gameOfLifeAlgorithm,
            dispatchers = dispatchers,
            clock = clock,
        ),
) {
    Box(modifier = modifier) {
        when (cellUniversePaneState) {
            is CellUniversePaneState.LoadingCellState -> {
                Box(
                    contentAlignment = Alignment.Center,
                    modifier = Modifier.fillMaxSize(),
                ) {
                    GameOfLifeProgressIndicator()
                }
            }

            is CellUniversePaneState.LoadedCellState -> {
                InteractiveCellUniverse(
                    temporalGameOfLifeState = cellUniversePaneState.temporalGameOfLifeState,
                    windowSizeClass = windowSizeClass,
                    onSeeMoreSettingsClicked = onSeeMoreSettingsClicked,
                    onOpenInSettingsClicked = onOpenInSettingsClicked,
                    onViewDeserializationInfo = onViewDeserializationInfo,
                )
            }
        }
    }
}
