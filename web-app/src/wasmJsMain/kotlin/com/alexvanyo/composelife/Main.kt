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
import androidx.compose.runtime.retain.ControlledRetainScope
import androidx.compose.runtime.retain.LocalRetainScope
import androidx.compose.ui.ExperimentalComposeUiApi
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.platform.LocalWindowInfo
import androidx.compose.ui.unit.toSize
import androidx.compose.ui.window.ComposeViewport
import androidx.navigationevent.NavigationEventDispatcher
import androidx.navigationevent.NavigationEventDispatcherOwner
import androidx.navigationevent.compose.LocalNavigationEventDispatcherOwner
import com.alexvanyo.composelife.algorithm.ConfigurableGameOfLifeAlgorithmBindings
import com.alexvanyo.composelife.clock.di.ClockBindings
import com.alexvanyo.composelife.data.CellStateRepositoryImplBindings
import com.alexvanyo.composelife.data.PatternCollectionRepositoryImplBindings
import com.alexvanyo.composelife.database.WebComposeLifeDriverBindings
import com.alexvanyo.composelife.database.di.AdapterBindings
import com.alexvanyo.composelife.database.di.DatabaseBindings
import com.alexvanyo.composelife.database.di.DriverBindings
import com.alexvanyo.composelife.database.di.QueriesBindings
import com.alexvanyo.composelife.dispatchers.DefaultComposeLifeDispatchersBindings
import com.alexvanyo.composelife.filesystem.di.FileSystemBindings
import com.alexvanyo.composelife.filesystem.di.PersistedDataPathBindings
import com.alexvanyo.composelife.imageloader.di.ImageLoaderBindings
import com.alexvanyo.composelife.imageloader.di.ImageLoaderDiskCacheBindings
import com.alexvanyo.composelife.imageloader.di.ImageLoaderFetcherFactoryBindings
import com.alexvanyo.composelife.imageloader.di.ImageLoaderKeyerBindings
import com.alexvanyo.composelife.imageloader.di.PlatformContextBindings
import com.alexvanyo.composelife.logging.di.LoggerBindings
import com.alexvanyo.composelife.network.di.EngineFactoryBindings
import com.alexvanyo.composelife.network.di.NetworkBindings
import com.alexvanyo.composelife.preferences.DefaultComposeLifePreferencesBindings
import com.alexvanyo.composelife.preferences.InMemoryPreferencesDataStoreBindings
import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.random.di.RandomBindings
import com.alexvanyo.composelife.scopes.ApplicationGraph
import com.alexvanyo.composelife.scopes.ApplicationGraphArguments
import com.alexvanyo.composelife.scopes.GlobalScope
import com.alexvanyo.composelife.scopes.UiGraph
import com.alexvanyo.composelife.scopes.UiGraphArguments
import com.alexvanyo.composelife.scopes.UiScope
import com.alexvanyo.composelife.ui.app.ComposeLifeApp
import com.alexvanyo.composelife.ui.app.ComposeLifeAppUiCtx
import com.alexvanyo.composelife.ui.app.UiWithLoadedPreferencesGraph
import com.alexvanyo.composelife.ui.app.UiWithLoadedPreferencesScope
import com.alexvanyo.composelife.ui.app.UiWithLoadedPreferencesScopeBindings
import com.alexvanyo.composelife.ui.mobile.ComposeLifeTheme
import com.alexvanyo.composelife.ui.mobile.shouldUseDarkTheme
import com.alexvanyo.composelife.ui.util.WebImmersiveModeManagerBindings
import com.alexvanyo.composelife.ui.util.WebTimeZoneHolderBindings
import com.alexvanyo.composelife.updatable.Updatable
import com.alexvanyo.composelife.updatable.di.AppUpdatableBindings
import com.alexvanyo.composelife.updatable.di.UiUpdatableBindings
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
        val retainScope = ControlledRetainScope()

        CompositionLocalProvider(
            LocalRetainScope provides retainScope,
            LocalNavigationEventDispatcherOwner provides navigationEventDispatcherOwner,
        ) {
            val uiGraph = remember(applicationGraph) {
                (applicationGraph as UiGraph.Factory).create(
                    object : UiGraphArguments {},
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

// TODO: This should all be removable once metadata support improves in metro.

@ContributesTo(AppScope::class)
interface ManualApplicationBindings :
    AppUpdatableBindings,
    DefaultComposeLifePreferencesBindings,
    InMemoryPreferencesDataStoreBindings,
    LoggerBindings,
    CellStateRepositoryImplBindings,
    ConfigurableGameOfLifeAlgorithmBindings,
    ClockBindings,
    DefaultComposeLifeDispatchersBindings,
    PatternCollectionRepositoryImplBindings,
    RandomBindings,
    QueriesBindings,
    FileSystemBindings,
    PersistedDataPathBindings,
    WebTimeZoneHolderBindings,
    ImageLoaderBindings,
    NetworkBindings,
    DatabaseBindings,
    PlatformContextBindings,
    ImageLoaderDiskCacheBindings,
    ImageLoaderFetcherFactoryBindings,
    ImageLoaderKeyerBindings,
    EngineFactoryBindings,
    DriverBindings,
    WebComposeLifeDriverBindings,
    AdapterBindings,
    UiGraph.Factory

@ContributesTo(UiScope::class)
interface ManualUiBindings :
    UiUpdatableBindings,
    WebImmersiveModeManagerBindings,
    UiWithLoadedPreferencesGraph.Factory

@ContributesTo(UiWithLoadedPreferencesScope::class)
interface ManualUiWithLoadedPreferencesBindings :
    UiWithLoadedPreferencesScopeBindings
