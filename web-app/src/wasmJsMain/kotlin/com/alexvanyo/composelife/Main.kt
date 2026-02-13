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
import androidx.compose.runtime.retain.LocalRetainedValuesStoreProvider
import androidx.compose.runtime.retain.retainManagedRetainedValuesStore
import androidx.compose.ui.ExperimentalComposeUiApi
import androidx.compose.ui.platform.LocalClipboard
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.platform.LocalWindowInfo
import androidx.compose.ui.unit.toSize
import androidx.compose.ui.window.ComposeViewport
import androidx.navigationevent.NavigationEventDispatcher
import androidx.navigationevent.NavigationEventDispatcherOwner
import androidx.navigationevent.compose.LocalNavigationEventDispatcherOwner
import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.scopes.ApplicationGraph
import com.alexvanyo.composelife.scopes.ApplicationGraphArguments
import com.alexvanyo.composelife.scopes.GlobalScope
import com.alexvanyo.composelife.scopes.UiGraph
import com.alexvanyo.composelife.scopes.UiGraphArguments
import com.alexvanyo.composelife.scopes.UiScope
import com.alexvanyo.composelife.ui.app.ComposeLifeApp
import com.alexvanyo.composelife.ui.app.ComposeLifeAppUiCtx
import com.alexvanyo.composelife.ui.mobile.ComposeLifeTheme
import com.alexvanyo.composelife.ui.mobile.shouldUseDarkTheme
import com.alexvanyo.composelife.updatable.Updatable
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.DependencyGraph
import dev.zacsweers.metro.ForScope
import dev.zacsweers.metro.asContribution
import dev.zacsweers.metro.createGraph
import kotlinx.browser.document
import kotlinx.coroutines.launch
import kotlinx.coroutines.supervisorScope
import org.w3c.dom.HTMLElement

@OptIn(ExperimentalComposeUiApi::class)
@Suppress("LongMethod")
fun main() {
    val globalGraph = createGraph<GlobalGraph>()
    val applicationGraph = globalGraph.asContribution<ApplicationGraph.Factory>().create(
        object : ApplicationGraphArguments {},
    )

    val element = document.getElementById("composeApp") as HTMLElement
    element.title = "ComposeLife"
    element.focus() // Focus is required for keyboard navigation.
    ComposeViewport(
        viewportContainer = element,
    ) {
        val ctx = applicationGraph.composeLifeApplicationCtx
        val appUpdatables = ctx.appUpdatables
        LaunchedEffect(Unit) {
            supervisorScope {
                appUpdatables.forEach { updatable ->
                    launch {
                        updatable.update()
                    }
                }
            }
        }

        val navigationEventDispatcherOwner = remember {
            object : NavigationEventDispatcherOwner {
                override val navigationEventDispatcher = NavigationEventDispatcher(
                    onBackCompletedFallback = {},
                )
            }
        }
        val retainedValuesStore = retainManagedRetainedValuesStore()

        CompositionLocalProvider(
            LocalNavigationEventDispatcherOwner provides navigationEventDispatcherOwner,
        ) {
            LocalRetainedValuesStoreProvider(retainedValuesStore) {
                val clipboard = LocalClipboard.current
                val uiGraph = remember(applicationGraph, clipboard) {
                    (applicationGraph as UiGraph.Factory).create(
                        object : UiGraphArguments {
                            override val element = element
                            override val clipboard = clipboard
                        },
                    )
                }
                val mainInjectCtx = uiGraph.mainInjectCtx
                val uiUpdatables = mainInjectCtx.uiUpdatables

                LaunchedEffect(uiUpdatables) {
                    supervisorScope {
                        uiUpdatables.forEach { updatable ->
                            launch {
                                updatable.update()
                            }
                        }
                    }
                }

                with(mainInjectCtx) {
                    ComposeLifeTheme(shouldUseDarkTheme()) {
                        with(mainInjectCtx.composeLifeAppUiCtx) {
                            ComposeLifeApp(
                                windowSizeClass = currentWindowAdaptiveInfo().windowSizeClass,
                                windowSize = with(LocalDensity.current) {
                                    LocalWindowInfo.current.containerSize.toSize().toDpSize()
                                },
                            )
                        }
                    }
                }
            }
        }
    }
}

@ContributesTo(AppScope::class)
interface ComposeLifeApplicationCtx {
    @ForScope(AppScope::class)
    val appUpdatables: Set<Updatable>
}

// TODO: Replace with asContribution()
internal val ApplicationGraph.composeLifeApplicationCtx: ComposeLifeApplicationCtx get() =
    this as ComposeLifeApplicationCtx

@ContributesTo(UiScope::class)
interface MainInjectCtx : ComposeLifePreferencesProvider {
    val composeLifeAppUiCtx: ComposeLifeAppUiCtx

    @ForScope(UiScope::class)
    val uiUpdatables: Set<Updatable>
}

// TODO: Replace with asContribution()
internal val UiGraph.mainInjectCtx: MainInjectCtx get() =
    this as MainInjectCtx

@DependencyGraph(GlobalScope::class)
interface GlobalGraph : ApplicationGraph.Factory
