/*
 * Copyright 2024 The Android Open Source Project
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

package com.alexvanyo.composelife.ui.settings.entrypoints

import android.app.Activity
import android.content.Context
import androidx.activity.compose.LocalActivity
import androidx.compose.runtime.Composable
import androidx.compose.ui.platform.LocalContext
import com.alexvanyo.composelife.preferences.TestComposeLifePreferences
import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.scopes.ApplicationGraph
import com.alexvanyo.composelife.scopes.ApplicationGraphArguments
import com.alexvanyo.composelife.scopes.GlobalScope
import com.alexvanyo.composelife.scopes.UiGraph
import com.alexvanyo.composelife.scopes.UiGraphArguments
import com.alexvanyo.composelife.scopes.UiScope
import com.alexvanyo.composelife.ui.settings.CellStatePreviewUiEntryPoint
import com.alexvanyo.composelife.ui.settings.FullscreenSettingsDetailPaneEntryPoint
import com.alexvanyo.composelife.ui.settings.InlineSettingsPaneEntryPoint
import com.alexvanyo.composelife.ui.util.TimeZoneHolder
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.DependencyGraph
import dev.zacsweers.metro.createGraph

/**
 * The full super-interface implementing all entry points for rendering
 * previews in this module.
 */
@ContributesTo(UiScope::class)
internal interface PreviewEntryPoint : ComposeLifePreferencesProvider {
    val cellStatePreviewUiEntryPoint: CellStatePreviewUiEntryPoint
    val fullscreenSettingsDetailPaneEntryPoint: FullscreenSettingsDetailPaneEntryPoint
    val inlineSettingsPaneEntryPoint: InlineSettingsPaneEntryPoint
    val testComposeLifePreferences: TestComposeLifePreferences
    val timeZoneHolder: TimeZoneHolder
}

@DependencyGraph(GlobalScope::class)
interface PreviewGlobalGraph

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
            override val activity: Activity? = LocalActivity.current
        },
    )
    val entryPoint = uiGraph as PreviewEntryPoint

    content(entryPoint)
}
