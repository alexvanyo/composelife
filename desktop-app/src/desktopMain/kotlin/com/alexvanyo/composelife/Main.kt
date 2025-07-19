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
import com.alexvanyo.composelife.scopes.ApplicationComponent
import com.alexvanyo.composelife.scopes.ApplicationComponentArguments
import com.alexvanyo.composelife.scopes.GlobalScope
import com.alexvanyo.composelife.scopes.UiComponent
import com.alexvanyo.composelife.scopes.UiComponentArguments
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
    val applicationComponent = globalGraph.asContribution<ApplicationComponent.Factory>().create(
        object : ApplicationComponentArguments {}
    )

    val entryPoint = applicationComponent as ComposeLifeApplicationEntryPoint
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
            val uiComponent = remember(applicationComponent) {
                applicationComponent.asContribution<UiComponent.Factory>().create(
                    object : UiComponentArguments {},
                )
            }
            val mainInjectEntryPoint = uiComponent as MainInjectEntryPoint
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

@ContributesTo(UiScope::class)
interface MainInjectEntryPoint :
    ComposeLifePreferencesProvider,
    ComposeLifeAppInjectEntryPoint

@DependencyGraph(GlobalScope::class, isExtendable = true)
interface GlobalGraph
