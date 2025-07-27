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

package com.alexvanyo.composelife.ui.cells.entrypoints

import android.content.Context
import androidx.compose.runtime.Composable
import androidx.compose.ui.platform.LocalContext
import coil3.ImageLoader
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferencesHolder
import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.scopes.ApplicationGraph
import com.alexvanyo.composelife.scopes.ApplicationGraphArguments
import com.alexvanyo.composelife.scopes.GlobalScope
import com.alexvanyo.composelife.scopes.UiGraph
import com.alexvanyo.composelife.scopes.UiGraphArguments
import com.alexvanyo.composelife.scopes.UiScope
import com.alexvanyo.composelife.ui.cells.ImmutableCellWindowEntryPoint
import com.alexvanyo.composelife.ui.cells.InteractableCellsEntryPoint
import com.alexvanyo.composelife.ui.cells.MutableCellWindowEntryPoint
import com.alexvanyo.composelife.ui.cells.NonInteractableCellsEntryPoint
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.DependencyGraph
import dev.zacsweers.metro.createGraph

/**
 * The full super-interface implementing all entry points for rendering
 * previews in this module.
 */
@ContributesTo(UiScope::class)
internal interface PreviewEntryPoint : ComposeLifePreferencesProvider {
    val mutableCellWindowEntryPoint: MutableCellWindowEntryPoint
    val immutableCellWindowEntryPoint: ImmutableCellWindowEntryPoint
    val interactableCellsEntryPoint: InteractableCellsEntryPoint
    val nonInteractableCellsEntryPoint: NonInteractableCellsEntryPoint
    val imageLoader: ImageLoader
    val loadedComposeLifePreferencesHolder: LoadedComposeLifePreferencesHolder
}

@DependencyGraph(GlobalScope::class, isExtendable = true)
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
        },
    )
    val entryPoint = uiGraph as PreviewEntryPoint

    content(entryPoint)
}
