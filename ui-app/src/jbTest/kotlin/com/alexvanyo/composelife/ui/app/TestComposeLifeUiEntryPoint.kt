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

import com.alexvanyo.composelife.scopes.UiGraph
import com.alexvanyo.composelife.scopes.UiScope
import com.alexvanyo.composelife.ui.app.action.CellUniverseActionCardInjectEntryPoint
import com.alexvanyo.composelife.ui.app.component.GameOfLifeProgressIndicatorInjectEntryPoint
import com.alexvanyo.composelife.ui.cells.CellWindowInjectEntryPoint
import com.alexvanyo.composelife.ui.settings.AlgorithmImplementationUiInjectEntryPoint
import com.alexvanyo.composelife.ui.settings.CellShapeConfigUiInjectEntryPoint
import com.alexvanyo.composelife.ui.settings.DarkThemeConfigUiInjectEntryPoint
import com.alexvanyo.composelife.ui.settings.DisableAGSLUiInjectEntryPoint
import com.alexvanyo.composelife.ui.settings.DisableOpenGLUiInjectEntryPoint
import com.alexvanyo.composelife.ui.settings.FullscreenSettingsDetailPaneInjectEntryPoint
import com.alexvanyo.composelife.ui.settings.InlineSettingsPaneInjectEntryPoint
import com.alexvanyo.composelife.ui.settings.SettingUiInjectEntryPoint
import dev.zacsweers.metro.ContributesTo

@ContributesTo(UiScope::class)
interface TestComposeLifeUiEntryPoint :
    AlgorithmImplementationUiInjectEntryPoint,
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

// TODO: Replace with asContribution()
internal val UiGraph.testComposeLifeUiEntryPoint: TestComposeLifeUiEntryPoint get() =
    this as TestComposeLifeUiEntryPoint
