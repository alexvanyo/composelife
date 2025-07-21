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

package com.alexvanyo.composelife

import androidx.compose.material3.adaptive.currentWindowAdaptiveInfo
import androidx.compose.runtime.CompositionLocalProvider
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.remember
import androidx.compose.ui.window.Window
import androidx.compose.ui.window.application
import androidx.compose.ui.window.rememberWindowState
import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.scopes.ApplicationGraph
import com.alexvanyo.composelife.scopes.ApplicationGraphArguments
import com.alexvanyo.composelife.scopes.GlobalScope
import com.alexvanyo.composelife.scopes.UiGraph
import com.alexvanyo.composelife.scopes.UiGraphArguments
import com.alexvanyo.composelife.scopes.UiScope
import com.alexvanyo.composelife.ui.app.ComposeLifeApp
import com.alexvanyo.composelife.ui.app.ComposeLifeAppInjectEntryPoint
import com.alexvanyo.composelife.ui.mobile.ComposeLifeTheme
import com.alexvanyo.composelife.ui.mobile.shouldUseDarkTheme
import com.alexvanyo.composelife.ui.util.rememberImmersiveModeManager
import com.alexvanyo.composelife.updatable.Updatable
import com.slack.circuit.retained.LocalRetainedStateRegistry
import com.slack.circuit.retained.continuityRetainedStateRegistry
import kotlinx.coroutines.launch
import kotlinx.coroutines.supervisorScope
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.DependencyGraph
import dev.zacsweers.metro.asContribution
import dev.zacsweers.metro.createGraph

fun main() = application {
    val globalGraph = createGraph<GlobalGraph>()
    val applicationGraph = globalGraph.asContribution<ApplicationGraph.Factory>().create(
        object : ApplicationGraphArguments {}
    )

    val entryPoint = applicationGraph.composeLifeApplicationEntryPoint
    val updatables = entryPoint.updatables

    LaunchedEffect(Unit) {
        supervisorScope {
            updatables.forEach { updatable ->
                launch {
                    updatable.update()
                }
            }
        }
    }

    val windowState = rememberWindowState()
    val immersiveModeManager = rememberImmersiveModeManager(windowState)

    Window(
        onCloseRequest = ::exitApplication,
        title = "ComposeLife",
        state = windowState,
    ) {
        CompositionLocalProvider(LocalRetainedStateRegistry provides continuityRetainedStateRegistry()) {
            val uiGraph = remember(applicationGraph) {
                (applicationGraph as UiGraph.Factory).create(
                    object : UiGraphArguments {},
                )
            }
            val mainInjectEntryPoint = uiGraph.mainInjectEntryPoint
            with(mainInjectEntryPoint) {
                ComposeLifeTheme(shouldUseDarkTheme()) {
                    ComposeLifeApp(
                        windowSizeClass = currentWindowAdaptiveInfo().windowSizeClass,
                        windowSize = windowState.size,
                        immersiveModeManager = immersiveModeManager,
                    )
                }
            }
        }
    }
}

@ContributesTo(AppScope::class)
interface ComposeLifeApplicationEntryPoint {
    val updatables: Set<Updatable>
}

// TODO: Replace with asContribution()
internal val ApplicationGraph.composeLifeApplicationEntryPoint: ComposeLifeApplicationEntryPoint get() =
    this as ComposeLifeApplicationEntryPoint

@ContributesTo(UiScope::class)
interface MainInjectEntryPoint :
    ComposeLifePreferencesProvider,
    ComposeLifeAppInjectEntryPoint

// TODO: Replace with asContribution()
internal val UiGraph.mainInjectEntryPoint: MainInjectEntryPoint get() =
    this as MainInjectEntryPoint

@DependencyGraph(GlobalScope::class, isExtendable = true)
interface GlobalGraph
