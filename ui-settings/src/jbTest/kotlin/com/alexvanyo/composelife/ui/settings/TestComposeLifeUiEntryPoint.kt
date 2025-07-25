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

package com.alexvanyo.composelife.ui.settings

import com.alexvanyo.composelife.scopes.UiGraph
import com.alexvanyo.composelife.scopes.UiScope
import com.alexvanyo.composelife.ui.cells.CellWindowInjectEntryPoint
import dev.zacsweers.metro.ContributesTo

@ContributesTo(UiScope::class)
interface TestComposeLifeUiEntryPoint :
    AlgorithmImplementationUiInjectEntryPoint,
    CellShapeConfigUiInjectEntryPoint,
    CellWindowInjectEntryPoint,
    DarkThemeConfigUiInjectEntryPoint,
    DisableAGSLUiInjectEntryPoint,
    DisableOpenGLUiInjectEntryPoint,
    FullscreenSettingsDetailPaneInjectEntryPoint,
    InlineSettingsPaneInjectEntryPoint,
    PatternCollectionsUiInjectEntryPoint,
    SettingUiInjectEntryPoint

// TODO: Replace with asContribution()
internal val UiGraph.testComposeLifeUiEntryPoint: TestComposeLifeUiEntryPoint get() =
    this as TestComposeLifeUiEntryPoint
