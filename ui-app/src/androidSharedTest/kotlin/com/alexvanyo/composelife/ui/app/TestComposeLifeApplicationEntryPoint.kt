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

import com.alexvanyo.composelife.algorithm.di.AlgorithmModule
import com.alexvanyo.composelife.clock.di.ClockModule
import com.alexvanyo.composelife.data.di.RepositoryModule
import com.alexvanyo.composelife.dispatchers.di.DispatchersModule
import com.alexvanyo.composelife.preferences.di.PreferencesModule
import com.alexvanyo.composelife.random.di.RandomModule
import com.alexvanyo.composelife.ui.app.action.CellUniverseActionCardHiltEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.AlgorithmImplementationUiHiltEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.CellShapeConfigUiHiltEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.DarkThemeConfigUiHiltEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.DisableAGSLUiHiltEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.DisableOpenGLUiHiltEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.FullscreenSettingsScreenHiltEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.InlineSettingsScreenHiltEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.SettingUiHiltEntryPoint
import com.alexvanyo.composelife.ui.app.component.GameOfLifeProgressIndicatorHiltEntryPoint
import com.alexvanyo.composelife.updatable.di.UpdatableModule

class TestComposeLifeApplicationEntryPoint(
    applicationComponent: TestComposeLifeApplicationComponent,
) : ClockModule by applicationComponent,
    RandomModule by applicationComponent,
    RepositoryModule by applicationComponent,
    AlgorithmModule by applicationComponent,
    DispatchersModule by applicationComponent,
    PreferencesModule by applicationComponent,
    UpdatableModule by applicationComponent,
    AlgorithmImplementationUiHiltEntryPoint,
    CellShapeConfigUiHiltEntryPoint,
    CellUniverseActionCardHiltEntryPoint,
    ComposeLifeAppHiltEntryPoint,
    DarkThemeConfigUiHiltEntryPoint,
    DisableAGSLUiHiltEntryPoint,
    DisableOpenGLUiHiltEntryPoint,
    FullscreenSettingsScreenHiltEntryPoint,
    GameOfLifeProgressIndicatorHiltEntryPoint,
    InlineSettingsScreenHiltEntryPoint,
    InteractiveCellUniverseHiltEntryPoint,
    InteractiveCellUniverseOverlayHiltEntryPoint,
    SettingUiHiltEntryPoint
