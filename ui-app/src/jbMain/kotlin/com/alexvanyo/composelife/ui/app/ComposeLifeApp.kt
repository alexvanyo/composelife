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

import androidx.compose.animation.Crossfade
import androidx.compose.animation.ExperimentalAnimationApi
import androidx.compose.animation.ExperimentalSharedTransitionApi
import androidx.compose.animation.SharedTransitionLayout
import androidx.compose.animation.core.updateTransition
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.material3.CircularProgressIndicator
import androidx.compose.material3.Surface
import androidx.compose.runtime.Composable
import androidx.compose.runtime.CompositionLocalProvider
import androidx.compose.runtime.getValue
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberUpdatedState
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.layout.LookaheadScope
import androidx.compose.ui.unit.DpSize
import androidx.window.core.layout.WindowSizeClass
import com.alexvanyo.composelife.algorithm.di.GameOfLifeAlgorithmProvider
import com.alexvanyo.composelife.clock.di.ClockProvider
import com.alexvanyo.composelife.data.di.CellStateRepositoryProvider
import com.alexvanyo.composelife.dispatchers.di.ComposeLifeDispatchersProvider
import com.alexvanyo.composelife.model.DeserializationResult
import com.alexvanyo.composelife.navigation.BackstackEntry
import com.alexvanyo.composelife.navigation.BackstackState
import com.alexvanyo.composelife.navigation.associateWithRenderablePanes
import com.alexvanyo.composelife.navigation.canNavigateBack
import com.alexvanyo.composelife.navigation.currentEntry
import com.alexvanyo.composelife.navigation.navigate
import com.alexvanyo.composelife.navigation.popBackstack
import com.alexvanyo.composelife.navigation.popUpTo
import com.alexvanyo.composelife.navigation.rememberMutableBackstackNavigationController
import com.alexvanyo.composelife.navigation.segmentingNavigationTransform
import com.alexvanyo.composelife.navigation.withExpectedActor
import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.preferences.di.LoadedComposeLifePreferencesProvider
import com.alexvanyo.composelife.resourcestate.ResourceState
import com.alexvanyo.composelife.ui.app.component.GameOfLifeProgressIndicatorInjectEntryPoint
import com.alexvanyo.composelife.ui.mobile.component.ListDetailInfo
import com.alexvanyo.composelife.ui.mobile.component.dialogNavigationTransform
import com.alexvanyo.composelife.ui.mobile.component.listDetailNavigationTransform
import com.alexvanyo.composelife.ui.settings.FullscreenSettingsDetailPane
import com.alexvanyo.composelife.ui.settings.FullscreenSettingsDetailPaneInjectEntryPoint
import com.alexvanyo.composelife.ui.settings.FullscreenSettingsDetailPaneLocalEntryPoint
import com.alexvanyo.composelife.ui.settings.FullscreenSettingsListPane
import com.alexvanyo.composelife.ui.settings.Setting
import com.alexvanyo.composelife.ui.settings.SettingsCategory
import com.alexvanyo.composelife.ui.util.LocalNavigationSharedTransitionScope
import com.alexvanyo.composelife.ui.util.MaterialPredictiveNavigationFrame
import com.alexvanyo.composelife.ui.util.RepeatablePredictiveBackHandler
import com.alexvanyo.composelife.ui.util.ReportDrawn
import com.alexvanyo.composelife.ui.util.rememberImmersiveModeManager
import com.alexvanyo.composelife.ui.util.rememberRepeatablePredictiveBackStateHolder

interface ComposeLifeAppInjectEntryPoint :
    ComposeLifePreferencesProvider,
    CellStateRepositoryProvider,
    ClockProvider,
    GameOfLifeProgressIndicatorInjectEntryPoint,
    CellUniversePaneInjectEntryPoint,
    FullscreenSettingsDetailPaneInjectEntryPoint

context(ComposeLifeAppInjectEntryPoint)
@Suppress("LongMethod")
@OptIn(ExperimentalAnimationApi::class, ExperimentalSharedTransitionApi::class)
@Composable
fun ComposeLifeApp(
    windowSizeClass: WindowSizeClass,
    windowSize: DpSize,
    modifier: Modifier = Modifier,
    composeLifeAppState: ComposeLifeAppState = rememberComposeLifeAppState(windowSizeClass, windowSize),
) {
    val immersiveModeManager = rememberImmersiveModeManager()

    Surface(modifier = modifier.fillMaxSize()) {
        LookaheadScope {
            val transition = updateTransition(composeLifeAppState, "ComposeLifeAppState Crossfade")
            transition.Crossfade(
                contentKey = {
                    when (it) {
                        ComposeLifeAppState.ErrorLoadingPreferences -> 0
                        is ComposeLifeAppState.LoadedPreferences -> 1
                        ComposeLifeAppState.LoadingPreferences -> 2
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
                                CellUniversePaneLocalEntryPoint,
                                FullscreenSettingsDetailPaneLocalEntryPoint,
                                LoadedComposeLifePreferencesProvider by targetComposeLifeAppState {}
                        }

                        val predictiveBackStateHolder = rememberRepeatablePredictiveBackStateHolder()

                        RepeatablePredictiveBackHandler(
                            repeatablePredictiveBackStateHolder = predictiveBackStateHolder,
                            enabled = targetComposeLifeAppState.canNavigateBack,
                            onBack = targetComposeLifeAppState::onBackPressed,
                        )

                        with(localEntryPoint) {
                            SharedTransitionLayout {
                                CompositionLocalProvider(LocalNavigationSharedTransitionScope provides this) {
                                    val renderableNavigationState = associateWithRenderablePanes(
                                        targetComposeLifeAppState.navigationState,
                                    ) { entry ->
                                        when (val value = entry.value) {
                                            is ComposeLifeUiNavigation.CellUniverse -> {
                                                Surface {
                                                    CellUniversePane(
                                                        windowSizeClass = windowSizeClass,
                                                        immersiveModeManager = immersiveModeManager,
                                                        onSeeMoreSettingsClicked =
                                                        targetComposeLifeAppState::onSeeMoreSettingsClicked,
                                                        onOpenInSettingsClicked =
                                                        targetComposeLifeAppState::onOpenInSettingsClicked,
                                                        onViewDeserializationInfo =
                                                        targetComposeLifeAppState::onViewDeserializationInfo,
                                                    )
                                                }
                                            }

                                            is ComposeLifeUiNavigation.FullscreenSettingsList -> {
                                                FullscreenSettingsListPane(
                                                    fullscreenSettingsListPaneState = value,
                                                    setSettingsCategory =
                                                    targetComposeLifeAppState::onSettingsCategoryClicked,
                                                    onBackButtonPressed = targetComposeLifeAppState::onBackPressed,
                                                )
                                            }

                                            is ComposeLifeUiNavigation.FullscreenSettingsDetail -> {
                                                FullscreenSettingsDetailPane(
                                                    fullscreenSettingsDetailPaneState = value,
                                                    onBackButtonPressed = targetComposeLifeAppState::onBackPressed,
                                                )
                                            }

                                            is ComposeLifeUiNavigation.DeserializationInfo -> {
                                                DeserializationInfoPane(
                                                    navEntryValue = value,
                                                    onBackButtonPressed = targetComposeLifeAppState::onBackPressed,
                                                )
                                            }
                                        }
                                    }

                                    MaterialPredictiveNavigationFrame(
                                        renderableNavigationState =
                                        dialogNavigationTransform<ComposeLifeUiNavigation>(
                                            onBackButtonPressed = targetComposeLifeAppState::onBackPressed,
                                        ).invoke(
                                            listDetailNavigationTransform<ComposeLifeUiNavigation>(
                                                onBackButtonPressed = targetComposeLifeAppState::onBackPressed,
                                            ).invoke(
                                                segmentingNavigationTransform<ComposeLifeUiNavigation>()
                                                    .invoke(renderableNavigationState),
                                            ),
                                        ),
                                        repeatablePredictiveBackState = predictiveBackStateHolder.value,
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

context(
    ComposeLifePreferencesProvider, CellStateRepositoryProvider, GameOfLifeAlgorithmProvider,
    ComposeLifeDispatchersProvider, ClockProvider
)
@Suppress("LongMethod")
@Composable
fun rememberComposeLifeAppState(
    windowSizeClass: WindowSizeClass,
    windowSize: DpSize,
): ComposeLifeAppState {
    return when (val loadedPreferencesState = composeLifePreferences.loadedPreferencesState) {
        is ResourceState.Failure -> ComposeLifeAppState.ErrorLoadingPreferences
        ResourceState.Loading -> ComposeLifeAppState.LoadingPreferences
        is ResourceState.Success -> {
            val currentLoadedPreferences by rememberUpdatedState(loadedPreferencesState.value)

            val navController = rememberMutableBackstackNavigationController(
                initialBackstackEntries = listOf(
                    BackstackEntry(
                        value = ComposeLifeNavigation.CellUniverse,
                        previous = null,
                    ),
                ),
                backstackValueSaverFactory = ComposeLifeNavigation.SaverFactory,
            )

            val currentEntryId = navController.currentEntryId

            val navigationUiState = navController.toComposeLifeUiNavigation(windowSizeClass, windowSize)

            remember(navController, navigationUiState) {
                object : ComposeLifeAppState.LoadedPreferences {
                    override val preferences get() = currentLoadedPreferences

                    override val navigationState: BackstackState<ComposeLifeUiNavigation>
                        get() = navigationUiState

                    override val canNavigateBack
                        get() = navController.canNavigateBack

                    override fun onBackPressed() {
                        navController.withExpectedActor(currentEntryId) {
                            val currentEntryValue = navController.currentEntry.value
                            if (navController.canNavigateBack) {
                                when (val value = navigationUiState.currentEntry.value) {
                                    is ListDetailInfo -> {
                                        navController.popBackstack()
                                        if (value.isListVisible && value.isDetailVisible &&
                                            currentEntryValue is ComposeLifeNavigation.FullscreenSettingsDetail
                                        ) {
                                            navController.popBackstack()
                                        }
                                    }
                                    else -> {
                                        navController.popBackstack()
                                    }
                                }
                            }
                        }
                    }

                    override fun onSeeMoreSettingsClicked() {
                        navController.withExpectedActor(currentEntryId) {
                            navController.navigate(
                                ComposeLifeNavigation.FullscreenSettingsList(
                                    initialSettingsCategory = SettingsCategory.Algorithm,
                                ),
                            )
                        }
                    }

                    override fun onOpenInSettingsClicked(setting: Setting) {
                        navController.withExpectedActor(currentEntryId) {
                            navController.navigate(
                                ComposeLifeNavigation.FullscreenSettingsList(
                                    initialSettingsCategory = setting.category,
                                ),
                            )
                            navController.navigate(
                                ComposeLifeNavigation.FullscreenSettingsDetail(
                                    settingsCategory = setting.category,
                                    initialSettingToScrollTo = setting,
                                ),
                            )
                        }
                    }

                    override fun onSettingsCategoryClicked(settingsCategory: SettingsCategory) {
                        navController.withExpectedActor(currentEntryId) {
                            navController.popUpTo(
                                predicate = { it is ComposeLifeNavigation.FullscreenSettingsList },
                            )
                            val currentEntryValue =
                                navController.currentEntry.value as ComposeLifeNavigation.FullscreenSettingsList
                            currentEntryValue.settingsCategory = settingsCategory
                            navController.navigate(
                                currentEntryValue.transientFullscreenSettingsDetail,
                                id = currentEntryValue.transientDetailId,
                            )
                        }
                    }

                    override fun onViewDeserializationInfo(deserializationResult: DeserializationResult) {
                        navController.withExpectedActor(currentEntryId) {
                            navController.navigate(
                                ComposeLifeNavigation.DeserializationInfo(
                                    deserializationResult = deserializationResult,
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

        val navigationState: BackstackState<ComposeLifeUiNavigation>

        val canNavigateBack: Boolean

        fun onBackPressed()

        fun onSeeMoreSettingsClicked()

        fun onOpenInSettingsClicked(setting: Setting)

        fun onSettingsCategoryClicked(settingsCategory: SettingsCategory)

        fun onViewDeserializationInfo(deserializationResult: DeserializationResult)
    }
}
