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

package com.alexvanyo.composelife.ui.app.entrypoints

import android.content.Context
import androidx.compose.runtime.Composable
import androidx.compose.ui.platform.LocalContext
import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.random.TestRandom
import com.alexvanyo.composelife.scopes.ApplicationGraph
import com.alexvanyo.composelife.scopes.ApplicationGraphArguments
import com.alexvanyo.composelife.scopes.GlobalScope
import com.alexvanyo.composelife.scopes.UiGraph
import com.alexvanyo.composelife.scopes.UiGraphArguments
import com.alexvanyo.composelife.scopes.UiScope
import com.alexvanyo.composelife.ui.app.CellUniversePaneEntryPoint
import com.alexvanyo.composelife.ui.app.ComposeLifeAppUiEntryPoint
import com.alexvanyo.composelife.ui.app.UiWithLoadedPreferencesScope
import com.alexvanyo.composelife.ui.app.UiWithLoadedPreferencesScopeBindings
import com.alexvanyo.composelife.ui.app.action.ClipboardCellStatePreviewEntryPoint
import com.alexvanyo.composelife.ui.app.action.InlineEditPaneEntryPoint
import com.alexvanyo.composelife.ui.app.component.GameOfLifeProgressIndicatorEntryPoint
import com.alexvanyo.composelife.ui.settings.SettingUiEntryPoint
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.DependencyGraph
import dev.zacsweers.metro.Provides
import dev.zacsweers.metro.createGraph

/**
 * The full super-interface implementing all entry points for rendering
 * previews in this module.
 */
@ContributesTo(UiScope::class)
internal interface PreviewEntryPoint : ComposeLifePreferencesProvider {
    val cellUniversePaneEntryPoint: CellUniversePaneEntryPoint
    val composeLifeAppUiEntryPoint: ComposeLifeAppUiEntryPoint
    val clipboardCellStatePreviewEntryPoint: ClipboardCellStatePreviewEntryPoint
    val gameOfLifeProgressIndicatorEntryPoint: GameOfLifeProgressIndicatorEntryPoint
    val inlineEditPaneEntryPoint: InlineEditPaneEntryPoint
    val settingUiEntryPoint: SettingUiEntryPoint
    val testRandom: TestRandom
}

@DependencyGraph(GlobalScope::class, isExtendable = true)
interface PreviewGlobalGraph

@ContributesTo(UiWithLoadedPreferencesScope::class, replaces = [UiWithLoadedPreferencesScopeBindings::class])
interface TestLoadedComposeLifePreferencesHolderBindings {

    companion object {
        @Provides
        internal fun emptyProvides(): EmptyProvides = EmptyProvides()
    }
}

internal class EmptyProvides

/**
 * Provides preview-appropriate bindings for the dependency graph.
 */
@Suppress("LongParameterList")
@Composable
internal fun WithPreviewDependencies(
    content: @Composable context(PreviewEntryPoint) () -> Unit,
) {
    val previewGraph = createGraph<PreviewGlobalGraph>()
    val applicationGraph = (previewGraph as ApplicationGraph.Factory).create(
        object : ApplicationGraphArguments {
            override val applicationContext: Context = LocalContext.current.applicationContext
        },
    )
    val uiGraph = (applicationGraph as UiGraph.Factory).create(
        object : UiGraphArguments {
            override val uiContext: Context = LocalContext.current
        },
    )
    val entryPoint = uiGraph as PreviewEntryPoint

    content(entryPoint)
}
