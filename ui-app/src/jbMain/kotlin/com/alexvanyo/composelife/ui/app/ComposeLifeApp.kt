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
import androidx.compose.foundation.background
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.material3.CircularProgressIndicator
import androidx.compose.material3.MaterialTheme
import androidx.compose.runtime.Composable
import androidx.compose.runtime.CompositionLocalProvider
import androidx.compose.runtime.Immutable
import androidx.compose.runtime.collectAsState
import androidx.compose.runtime.getValue
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberUpdatedState
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.unit.DpSize
import androidx.navigation3.scene.Scene
import androidx.navigationevent.NavigationEventInfo
import androidx.navigationevent.NavigationEventTransitionState
import androidx.navigationevent.compose.LocalNavigationEventDispatcherOwner
import androidx.navigationevent.compose.NavigationBackHandler
import androidx.navigationevent.compose.rememberNavigationEventState
import androidx.window.core.layout.WindowSizeClass
import com.alexvanyo.composelife.model.DeserializationResult
import com.alexvanyo.composelife.navigation.BackstackEntry
import com.alexvanyo.composelife.navigation.BackstackMapSerializer
import com.alexvanyo.composelife.navigation.BackstackState
import com.alexvanyo.composelife.navigation.MaterialPredictiveNavDisplay
import com.alexvanyo.composelife.navigation.canNavigateBack
import com.alexvanyo.composelife.navigation.currentEntry
import com.alexvanyo.composelife.navigation.navigate
import com.alexvanyo.composelife.navigation.popBackstack
import com.alexvanyo.composelife.navigation.popUpTo
import com.alexvanyo.composelife.navigation.rememberDecoratedNavEntries
import com.alexvanyo.composelife.navigation.rememberMutableBackstackNavigationController
import com.alexvanyo.composelife.navigation.withExpectedActor
import com.alexvanyo.composelife.navigation3.scene.SinglePaneSceneStrategy
import com.alexvanyo.composelife.navigation3.scene.rememberSceneState
import com.alexvanyo.composelife.preferences.ComposeLifePreferences
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferences
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferencesHolder
import com.alexvanyo.composelife.resourcestate.ResourceState
import com.alexvanyo.composelife.scopes.UiGraph
import com.alexvanyo.composelife.scopes.UiScope
import com.alexvanyo.composelife.ui.mobile.component.DialogSceneStrategy
import com.alexvanyo.composelife.ui.mobile.component.ListDetailInfo
import com.alexvanyo.composelife.ui.mobile.component.ListDetailSceneStrategy
import com.alexvanyo.composelife.ui.settings.FullscreenSettingsDetailPane
import com.alexvanyo.composelife.ui.settings.FullscreenSettingsDetailPaneCtx
import com.alexvanyo.composelife.ui.settings.FullscreenSettingsListPane
import com.alexvanyo.composelife.ui.settings.Setting
import com.alexvanyo.composelife.ui.settings.SettingsCategory
import com.alexvanyo.composelife.ui.util.LocalSharedTransitionScope
import com.alexvanyo.composelife.ui.util.ReportDrawn
import dev.zacsweers.metro.BindingContainer
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.GraphExtension
import dev.zacsweers.metro.Inject
import dev.zacsweers.metro.Provides
import dev.zacsweers.metro.SingleIn
import kotlin.reflect.KClass

@Immutable
@Inject
class ComposeLifeAppUiCtx(
    internal val composeLifePreferences: ComposeLifePreferences,
    internal val uiGraph: UiGraph,
) {
    companion object
}

@Immutable
@Inject
class ComposeLifeAppUiWithLoadedPreferencesCtx(
    internal val preferencesHolder: LoadedComposeLifePreferencesHolder,
    internal val cellUniversePaneCtx: CellUniversePaneCtx,
    internal val fullscreenSettingsDetailPaneCtx: FullscreenSettingsDetailPaneCtx,
) {
    companion object
}

context(uiCtx: ComposeLifeAppUiCtx)
@Suppress("LongMethod", "CyclomaticComplexMethod")
@OptIn(ExperimentalSharedTransitionApi::class, ExperimentalAnimationApi::class)
@Composable
fun ComposeLifeApp(
    windowSizeClass: WindowSizeClass,
    windowSize: DpSize,
    modifier: Modifier = Modifier,
    composeLifeAppState: ComposeLifeAppState = rememberComposeLifeAppState(
        uiCtx.composeLifePreferences,
        uiCtx.uiGraph,
        windowSizeClass,
        windowSize,
    ),
) {
    val transition = updateTransition(composeLifeAppState, "ComposeLifeAppState Crossfade")
    transition.Crossfade(
        contentKey = {
            when (it) {
                ComposeLifeAppState.ErrorLoadingPreferences -> 0
                is ComposeLifeAppState.LoadedPreferences -> 1
                ComposeLifeAppState.LoadingPreferences -> 2
            }
        },
        modifier = modifier
            .fillMaxSize()
            .background(MaterialTheme.colorScheme.surface),
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

                val dispatcher = requireNotNull(
                    LocalNavigationEventDispatcherOwner.current,
                ).navigationEventDispatcher
                val navigationEventHistory by dispatcher.history.collectAsState()
                val currentInfo = navigationEventHistory.mergedHistory.getOrNull(
                    navigationEventHistory.currentIndex,
                )

                with(targetComposeLifeAppState.composeLifeAppUiWithLoadedPreferencesCtx) {
                    SharedTransitionLayout {
                        CompositionLocalProvider(LocalSharedTransitionScope provides this) {
                            val navEntries = rememberDecoratedNavEntries(
                                targetComposeLifeAppState.navigationState,
                            ) { entry ->
                                when (val value = entry.value) {
                                    is ComposeLifeUiNavigation.CellUniverse -> {
                                        with(cellUniversePaneCtx) {
                                            CellUniversePane(
                                                windowSizeClass = windowSizeClass,
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
                                        with(fullscreenSettingsDetailPaneCtx) {
                                            FullscreenSettingsDetailPane(
                                                fullscreenSettingsDetailPaneState = value,
                                                onBackButtonPressed = targetComposeLifeAppState::onBackPressed,
                                            )
                                        }
                                    }

                                    is ComposeLifeUiNavigation.DeserializationInfo -> {
                                        DeserializationInfoPane(
                                            navEntryValue = value,
                                            onBackButtonPressed = targetComposeLifeAppState::onBackPressed,
                                        )
                                    }
                                }
                            }

                            val sceneState = rememberSceneState(
                                entries = navEntries,
                                sceneStrategy = DialogSceneStrategy(
                                    ListDetailSceneStrategy<ComposeLifeUiNavigation>() then
                                        SinglePaneSceneStrategy(),
                                ),
                                onBack = targetComposeLifeAppState::onBackPressed,
                            )

                            val navigationEventTransitionState =
                                if (currentInfo is ComposeLifeAppNavigationEventInfo &&
                                    currentInfo.sceneKey ==
                                    sceneState.currentScene::class to sceneState.currentScene.key
                                ) {
                                    dispatcher.transitionState.collectAsState().value
                                } else {
                                    NavigationEventTransitionState.Idle
                                }

                            NavigationBackHandler(
                                state = rememberNavigationEventState(
                                    currentInfo = ComposeLifeAppNavigationEventInfo(
                                        sceneState.currentScene::class to sceneState.currentScene.key,
                                    ),
                                    backInfo = sceneState.previousScenes.map {
                                        ComposeLifeAppNavigationEventInfo(it::class to it.key)
                                    },
                                ),
                                isBackEnabled = targetComposeLifeAppState.canNavigateBack,
                                onBackCompleted = targetComposeLifeAppState::onBackPressed,
                            )

                            MaterialPredictiveNavDisplay(
                                sceneState = sceneState,
                                navigationEventTransitionState = navigationEventTransitionState,
                                clipUsingWindowShape = preferencesHolder.preferences.enableWindowShapeClipping,
                            )
                        }
                    }
                }
            }
        }
    }
}

@Suppress("LongMethod", "LongParameterList")
@Composable
fun rememberComposeLifeAppState(
    composeLifePreferences: ComposeLifePreferences,
    uiGraph: UiGraph,
    windowSizeClass: WindowSizeClass,
    windowSize: DpSize,
): ComposeLifeAppState {
    return when (val loadedPreferencesState = composeLifePreferences.loadedPreferencesState) {
        is ResourceState.Failure -> ComposeLifeAppState.ErrorLoadingPreferences
        ResourceState.Loading -> ComposeLifeAppState.LoadingPreferences
        is ResourceState.Success -> {
            val currentLoadedPreferences by rememberUpdatedState(loadedPreferencesState.value)

            val preferencesHolder = remember {
                object : LoadedComposeLifePreferencesHolder {
                    override val preferences: LoadedComposeLifePreferences
                        get() = currentLoadedPreferences
                }
            }

            val uiWithLoadedPreferencesGraph = remember(currentLoadedPreferences) {
                (uiGraph as UiWithLoadedPreferencesGraph.Factory).create(
                    UiWithLoadedPreferencesGraphArguments(
                        loadedComposeLifePreferencesHolder = preferencesHolder,
                    ),
                )
            }

            val navController = rememberMutableBackstackNavigationController(
                initialBackstackEntries = listOf(
                    BackstackEntry(
                        value = ComposeLifeNavigation.CellUniverse,
                        previous = null,
                    ),
                ),
                backstackMapSerializer = BackstackMapSerializer(ComposeLifeNavigation::surrogate),
            )

            val currentEntryId = navController.currentEntryId

            val navigationUiState = navController.toComposeLifeUiNavigation(windowSizeClass, windowSize)

            remember(navController, navigationUiState) {
                object : ComposeLifeAppState.LoadedPreferences {
                    override val composeLifeAppUiWithLoadedPreferencesCtx:
                        ComposeLifeAppUiWithLoadedPreferencesCtx
                        get() = uiWithLoadedPreferencesGraph.composeLifeAppUiWithLoadedPreferencesCtx

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

private data class ComposeLifeAppNavigationEventInfo(
    val sceneKey: Pair<KClass<out Scene<*>>, Any>,
) : NavigationEventInfo()

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
     * The user's preferences are loaded,.
     */
    interface LoadedPreferences : ComposeLifeAppState {

        val composeLifeAppUiWithLoadedPreferencesCtx: ComposeLifeAppUiWithLoadedPreferencesCtx

        val navigationState: BackstackState<ComposeLifeUiNavigation>

        val canNavigateBack: Boolean

        fun onBackPressed()

        fun onSeeMoreSettingsClicked()

        fun onOpenInSettingsClicked(setting: Setting)

        fun onSettingsCategoryClicked(settingsCategory: SettingsCategory)

        fun onViewDeserializationInfo(deserializationResult: DeserializationResult)
    }
}

abstract class UiWithLoadedPreferencesScope private constructor()

@GraphExtension(UiWithLoadedPreferencesScope::class)
interface UiWithLoadedPreferencesGraph {
    val composeLifeAppUiWithLoadedPreferencesCtx: ComposeLifeAppUiWithLoadedPreferencesCtx

    @ContributesTo(UiScope::class)
    @GraphExtension.Factory
    fun interface Factory {
        fun create(
            @Provides uiWithLoadedPreferencesGraphArguments: UiWithLoadedPreferencesGraphArguments,
        ): UiWithLoadedPreferencesGraph
    }
}

class UiWithLoadedPreferencesGraphArguments(
    val loadedComposeLifePreferencesHolder: LoadedComposeLifePreferencesHolder,
)

@ContributesTo(UiWithLoadedPreferencesScope::class)
@BindingContainer
interface UiWithLoadedPreferencesScopeBindings {

    companion object {
        @Provides
        @SingleIn(UiWithLoadedPreferencesScope::class)
        internal fun providesLoadedComposeLifePreferencesHolder(
            uiWithLoadedPreferencesGraphArguments: UiWithLoadedPreferencesGraphArguments,
        ): LoadedComposeLifePreferencesHolder =
            uiWithLoadedPreferencesGraphArguments.loadedComposeLifePreferencesHolder
    }
}
