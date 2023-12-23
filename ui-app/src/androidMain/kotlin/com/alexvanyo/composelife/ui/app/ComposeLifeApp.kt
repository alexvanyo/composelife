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
@file:Suppress("MatchingDeclarationName")

package com.alexvanyo.composelife.ui.app

import androidx.activity.compose.ReportDrawn
import androidx.compose.animation.Crossfade
import androidx.compose.animation.ExperimentalAnimationApi
import androidx.compose.animation.core.updateTransition
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.BoxWithConstraints
import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.material3.CircularProgressIndicator
import androidx.compose.material3.Surface
import androidx.compose.material3.windowsizeclass.ExperimentalMaterial3WindowSizeClassApi
import androidx.compose.material3.windowsizeclass.WindowSizeClass
import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberUpdatedState
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.layout.LookaheadScope
import androidx.compose.ui.layout.layout
import androidx.compose.ui.platform.LocalConfiguration
import androidx.compose.ui.unit.DpSize
import com.alexvanyo.composelife.algorithm.di.GameOfLifeAlgorithmProvider
import com.alexvanyo.composelife.clock.di.ClockProvider
import com.alexvanyo.composelife.data.di.CellStateRepositoryProvider
import com.alexvanyo.composelife.dispatchers.di.ComposeLifeDispatchersProvider
import com.alexvanyo.composelife.navigation.BackstackEntry
import com.alexvanyo.composelife.navigation.BackstackState
import com.alexvanyo.composelife.navigation.canNavigateBack
import com.alexvanyo.composelife.navigation.navigate
import com.alexvanyo.composelife.navigation.popBackstack
import com.alexvanyo.composelife.navigation.rememberMutableBackstackNavigationController
import com.alexvanyo.composelife.navigation.withExpectedActor
import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.preferences.di.LoadedComposeLifePreferencesProvider
import com.alexvanyo.composelife.resourcestate.ResourceState
import com.alexvanyo.composelife.ui.app.action.settings.FullscreenSettingsScreen
import com.alexvanyo.composelife.ui.app.action.settings.FullscreenSettingsScreenInjectEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.FullscreenSettingsScreenLocalEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.Setting
import com.alexvanyo.composelife.ui.app.action.settings.SettingsCategory
import com.alexvanyo.composelife.ui.app.component.GameOfLifeProgressIndicatorInjectEntryPoint
import com.alexvanyo.composelife.ui.app.entrypoints.WithPreviewDependencies
import com.alexvanyo.composelife.ui.app.theme.ComposeLifeTheme
import com.alexvanyo.composelife.ui.util.MobileDevicePreviews
import com.alexvanyo.composelife.ui.util.PredictiveBackHandler
import com.alexvanyo.composelife.ui.util.PredictiveNavigationHost
import com.alexvanyo.composelife.ui.util.rememberPredictiveBackStateHolder
import java.util.UUID

interface ComposeLifeAppInjectEntryPoint :
    ComposeLifePreferencesProvider,
    CellStateRepositoryProvider,
    ClockProvider,
    GameOfLifeProgressIndicatorInjectEntryPoint,
    CellUniverseScreenInjectEntryPoint,
    FullscreenSettingsScreenInjectEntryPoint

context(ComposeLifeAppInjectEntryPoint)
@Suppress("LongMethod")
@OptIn(ExperimentalAnimationApi::class)
@Composable
fun ComposeLifeApp(
    windowSizeClass: WindowSizeClass,
    modifier: Modifier = Modifier,
    composeLifeAppState: ComposeLifeAppState = rememberComposeLifeAppState(),
) {
    Surface(modifier = modifier.fillMaxSize()) {
        LookaheadScope {
            val transition = updateTransition(composeLifeAppState, "ComposeLifeAppState Crossfade")
            val configuration = LocalConfiguration.current

            @Suppress("UNUSED_EXPRESSION")
            transition.Crossfade(
                contentKey = {
                    when (it) {
                        ComposeLifeAppState.ErrorLoadingPreferences -> 0
                        is ComposeLifeAppState.LoadedPreferences -> 1
                        ComposeLifeAppState.LoadingPreferences -> 2
                    }
                },
                modifier = Modifier.layout { measurable, constraints ->
                    // TODO: This force remeasuring and placing should not be necessary
                    configuration
                    val placeable = measurable.measure(constraints)
                    layout(placeable.width, placeable.height) {
                        placeable.place(0, 0)
                    }
                },
            ) { targetComposeLifeAppState ->
                when (targetComposeLifeAppState) {
                    ComposeLifeAppState.ErrorLoadingPreferences -> Unit
                    ComposeLifeAppState.LoadingPreferences -> {
                        Box(
                            contentAlignment = Alignment.Center,
                            modifier = Modifier.fillMaxSize(),
                        ) {
                            CircularProgressIndicator()
                        }
                    }
                    is ComposeLifeAppState.LoadedPreferences -> {
                        ReportDrawn()

                        val localEntryPoint = remember {
                            object :
                                CellUniverseScreenLocalEntryPoint,
                                FullscreenSettingsScreenLocalEntryPoint,
                                LoadedComposeLifePreferencesProvider by targetComposeLifeAppState {}
                        }

                        val predictiveBackStateHolder = rememberPredictiveBackStateHolder()

                        PredictiveBackHandler(
                            predictiveBackStateHolder = predictiveBackStateHolder,
                            enabled = targetComposeLifeAppState.canNavigateBack,
                        ) {
                            targetComposeLifeAppState.onBackPressed(null)
                        }

                        with(localEntryPoint) {
                            PredictiveNavigationHost(
                                predictiveBackState = predictiveBackStateHolder.value,
                                backstackState = targetComposeLifeAppState.navigationState,
                            ) { entry ->
                                when (val value = entry.value) {
                                    is ComposeLifeNavigation.CellUniverse -> {
                                        CellUniverseScreen(
                                            windowSizeClass = windowSizeClass,
                                            navEntryValue = value,
                                            onSeeMoreSettingsClicked = {
                                                targetComposeLifeAppState.onSeeMoreSettingsClicked(entry.id)
                                            },
                                            onOpenInSettingsClicked = { setting ->
                                                targetComposeLifeAppState.onOpenInSettingsClicked(setting, entry.id)
                                            },
                                        )
                                    }
                                    is ComposeLifeNavigation.FullscreenSettings -> {
                                        FullscreenSettingsScreen(
                                            windowSizeClass = windowSizeClass,
                                            navEntryValue = value,
                                            onBackButtonPressed = {
                                                targetComposeLifeAppState.onBackPressed(entry.id)
                                            },
                                        )
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

context(
    ComposeLifePreferencesProvider, CellStateRepositoryProvider, GameOfLifeAlgorithmProvider,
    ComposeLifeDispatchersProvider, ClockProvider
)
@Suppress("LongMethod")
@Composable
fun rememberComposeLifeAppState(): ComposeLifeAppState {
    return when (val loadedPreferencesState = composeLifePreferences.loadedPreferencesState) {
        is ResourceState.Failure -> ComposeLifeAppState.ErrorLoadingPreferences
        ResourceState.Loading -> ComposeLifeAppState.LoadingPreferences
        is ResourceState.Success -> {
            val currentLoadedPreferences by rememberUpdatedState(loadedPreferencesState.value)

            val navController = rememberMutableBackstackNavigationController(
                initialBackstackEntries = listOf(
                    BackstackEntry(
                        value = ComposeLifeNavigation.CellUniverse(),
                        previous = null,
                    ),
                ),
                backstackValueSaverFactory = ComposeLifeNavigation.SaverFactory,
            )

            remember(navController) {
                object : ComposeLifeAppState.LoadedPreferences {
                    override val preferences get() = currentLoadedPreferences

                    override val navigationState: BackstackState<out ComposeLifeNavigation>
                        get() = navController

                    override val canNavigateBack
                        get() = navController.canNavigateBack

                    override fun onBackPressed(actorBackstackEntryId: UUID?) {
                        navController.withExpectedActor(actorBackstackEntryId) {
                            if (navController.canNavigateBack) {
                                navController.popBackstack()
                            }
                        }
                    }

                    override fun onSeeMoreSettingsClicked(actorBackstackEntryId: UUID?) {
                        navController.withExpectedActor(actorBackstackEntryId) {
                            navController.navigate(
                                ComposeLifeNavigation.FullscreenSettings(
                                    initialSettingsCategory = SettingsCategory.Algorithm,
                                    initialShowDetails = false,
                                    initialSettingToScrollTo = null,
                                ),
                            )
                        }
                    }

                    override fun onOpenInSettingsClicked(setting: Setting, actorBackstackEntryId: UUID?) {
                        navController.withExpectedActor(actorBackstackEntryId) {
                            navController.navigate(
                                ComposeLifeNavigation.FullscreenSettings(
                                    initialSettingsCategory = setting.category,
                                    initialShowDetails = true,
                                    initialSettingToScrollTo = setting,
                                ),
                            )
                        }
                    }
                }
            }
        }
    }
}

sealed interface ComposeLifeAppState {
    /**
     * The user's preferences are loading.
     */
    data object LoadingPreferences : ComposeLifeAppState

    /**
     * There was an error loading the user's preferences.
     */
    data object ErrorLoadingPreferences : ComposeLifeAppState

    /**
     * The user's preferences are loaded, so the state can be a [LoadedComposeLifePreferencesProvider].
     */
    interface LoadedPreferences : ComposeLifeAppState, LoadedComposeLifePreferencesProvider {

        val navigationState: BackstackState<out ComposeLifeNavigation>

        val canNavigateBack: Boolean

        fun onBackPressed(actorBackstackEntryId: UUID?)

        fun onSeeMoreSettingsClicked(actorBackstackEntryId: UUID?)

        fun onOpenInSettingsClicked(setting: Setting, actorBackstackEntryId: UUID?)
    }
}

@OptIn(ExperimentalMaterial3WindowSizeClassApi::class)
@MobileDevicePreviews
@Composable
fun LoadingPreferencesComposeLifeAppPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            BoxWithConstraints {
                val size = DpSize(maxWidth, maxHeight)
                ComposeLifeApp(
                    windowSizeClass = WindowSizeClass.calculateFromSize(size),
                    composeLifeAppState = ComposeLifeAppState.LoadingPreferences,
                )
            }
        }
    }
}
