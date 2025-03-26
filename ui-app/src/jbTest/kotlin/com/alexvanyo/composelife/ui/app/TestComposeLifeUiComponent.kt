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

import coil3.ImageLoader
import com.alexvanyo.composelife.algorithm.GameOfLifeAlgorithm
import com.alexvanyo.composelife.data.CellStateRepository
import com.alexvanyo.composelife.data.PatternCollectionRepository
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.model.CellStateParser
import com.alexvanyo.composelife.preferences.ComposeLifePreferences
import com.alexvanyo.composelife.scopes.UiComponent
import com.alexvanyo.composelife.scopes.UiComponentArguments
import com.alexvanyo.composelife.scopes.UiScope
import com.alexvanyo.composelife.ui.app.action.CellUniverseActionCardInjectEntryPoint
import com.alexvanyo.composelife.ui.settings.AlgorithmImplementationUiInjectEntryPoint
import com.alexvanyo.composelife.ui.settings.CellShapeConfigUiInjectEntryPoint
import com.alexvanyo.composelife.ui.settings.DarkThemeConfigUiInjectEntryPoint
import com.alexvanyo.composelife.ui.settings.DisableAGSLUiInjectEntryPoint
import com.alexvanyo.composelife.ui.settings.DisableOpenGLUiInjectEntryPoint
import com.alexvanyo.composelife.ui.settings.FullscreenSettingsDetailPaneInjectEntryPoint
import com.alexvanyo.composelife.ui.settings.InlineSettingsPaneInjectEntryPoint
import com.alexvanyo.composelife.ui.settings.SettingUiInjectEntryPoint
import com.alexvanyo.composelife.ui.cells.CellWindowInjectEntryPoint
import com.alexvanyo.composelife.ui.app.component.GameOfLifeProgressIndicatorInjectEntryPoint
import kotlinx.datetime.Clock
import me.tatarka.inject.annotations.Inject
import software.amazon.lastmile.kotlin.inject.anvil.SingleIn
import kotlin.random.Random

expect interface TestComposeLifeUiComponent : UiComponent<TestComposeLifeUiEntryPoint> {

    override val entryPoint: TestComposeLifeUiEntryPoint

    interface Factory

    companion object
}

@SingleIn(UiScope::class)
@Inject
class TestComposeLifeUiEntryPoint(
    override val cellStateParser: CellStateParser,
    override val composeLifePreferences: ComposeLifePreferences,
    override val imageLoader: ImageLoader,
    override val gameOfLifeAlgorithm: GameOfLifeAlgorithm,
    override val dispatchers: ComposeLifeDispatchers,
    override val random: Random,
    override val clock: Clock,
    override val cellStateRepository: CellStateRepository,
    override val patternCollectionRepository: PatternCollectionRepository,
) : AlgorithmImplementationUiInjectEntryPoint,
    CellShapeConfigUiInjectEntryPoint,
    CellUniverseActionCardInjectEntryPoint,
    CellWindowInjectEntryPoint,
    ComposeLifeAppInjectEntryPoint,
    DarkThemeConfigUiInjectEntryPoint,
    DisableAGSLUiInjectEntryPoint,
    DisableOpenGLUiInjectEntryPoint,
    FullscreenSettingsDetailPaneInjectEntryPoint,
    GameOfLifeProgressIndicatorInjectEntryPoint,
    InlineSettingsPaneInjectEntryPoint,
    InteractiveCellUniverseInjectEntryPoint,
    InteractiveCellUniverseOverlayInjectEntryPoint,
    SettingUiInjectEntryPoint

expect fun TestComposeLifeUiComponent.Companion.createComponent(
    applicationComponent: TestComposeLifeApplicationComponent,
    uiComponentArguments: UiComponentArguments,
): TestComposeLifeUiComponent
