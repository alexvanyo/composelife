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

package com.alexvanyo.composelife.ui.app.ctxs

import android.app.Activity
import android.content.Context
import androidx.activity.compose.LocalActivity
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
import com.alexvanyo.composelife.ui.app.CellUniversePaneCtx
import com.alexvanyo.composelife.ui.app.ComposeLifeAppUiCtx
import com.alexvanyo.composelife.ui.app.UiWithLoadedPreferencesScope
import com.alexvanyo.composelife.ui.app.UiWithLoadedPreferencesScopeBindings
import com.alexvanyo.composelife.ui.app.action.ClipboardCellStatePreviewCtx
import com.alexvanyo.composelife.ui.app.action.InlineEditPaneCtx
import com.alexvanyo.composelife.ui.app.component.GameOfLifeProgressIndicatorCtx
import com.alexvanyo.composelife.ui.settings.SettingUiCtx
import dev.zacsweers.metro.BindingContainer
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.DependencyGraph
import dev.zacsweers.metro.createGraph

/**
 * The full super-interface implementing all entry points for rendering
 * previews in this module.
 */
@ContributesTo(UiScope::class)
internal interface PreviewCtx : ComposeLifePreferencesProvider {
    val cellUniversePaneCtx: CellUniversePaneCtx
    val composeLifeAppUiCtx: ComposeLifeAppUiCtx
    val clipboardCellStatePreviewCtx: ClipboardCellStatePreviewCtx
    val gameOfLifeProgressIndicatorCtx: GameOfLifeProgressIndicatorCtx
    val inlineEditPaneCtx: InlineEditPaneCtx
    val settingUiCtx: SettingUiCtx
    val testRandom: TestRandom
}

@DependencyGraph(GlobalScope::class)
interface PreviewGlobalGraph

@ContributesTo(UiWithLoadedPreferencesScope::class, replaces = [UiWithLoadedPreferencesScopeBindings::class])
@BindingContainer
interface TestLoadedComposeLifePreferencesHolderBindings

/**
 * Provides preview-appropriate bindings for the dependency graph.
 */
@Suppress("LongParameterList")
@Composable
internal fun WithPreviewDependencies(content: @Composable context(PreviewCtx) () -> Unit) {
    val previewGraph = createGraph<PreviewGlobalGraph>()
    val applicationGraph =
        (previewGraph as ApplicationGraph.Factory).create(
            object : ApplicationGraphArguments {
                override val applicationContext: Context = LocalContext.current.applicationContext
            },
        )
    val uiGraph =
        (applicationGraph as UiGraph.Factory).create(
            object : UiGraphArguments {
                override val uiContext: Context = LocalContext.current
                override val activity: Activity? = LocalActivity.current
            },
        )
    val ctx = uiGraph as PreviewCtx

    content(ctx)
}
