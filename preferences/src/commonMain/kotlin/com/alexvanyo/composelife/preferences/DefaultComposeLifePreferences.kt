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

package com.alexvanyo.composelife.preferences

import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.setValue
import androidx.compose.runtime.snapshots.Snapshot
import com.alexvanyo.composelife.preferences.CurrentShape.RoundRectangle
import com.alexvanyo.composelife.preferences.CurrentShape.Superellipse
import com.alexvanyo.composelife.preferences.proto.AlgorithmProto
import com.alexvanyo.composelife.preferences.proto.CurrentShapeTypeProto
import com.alexvanyo.composelife.preferences.proto.DarkThemeConfigProto
import com.alexvanyo.composelife.preferences.proto.QuickAccessSettingProto
import com.alexvanyo.composelife.preferences.proto.RoundRectangleProto
import com.alexvanyo.composelife.preferences.proto.SuperellipseProto
import com.alexvanyo.composelife.resourcestate.ResourceState
import com.alexvanyo.composelife.resourcestate.map
import kotlinx.coroutines.flow.catch
import kotlinx.coroutines.flow.collect
import kotlinx.coroutines.flow.onEach
import kotlinx.coroutines.flow.retry
import javax.inject.Inject
import javax.inject.Singleton

@Suppress("TooManyFunctions")
@Singleton
class DefaultComposeLifePreferences @Inject constructor(
    private val dataStore: PreferencesDataStore,
) : ComposeLifePreferences {

    override val quickAccessSettingsState: ResourceState<Set<QuickAccessSetting>>
        get() = loadedPreferencesState.map(LoadedComposeLifePreferences::quickAccessSettings)

    override val algorithmChoiceState: ResourceState<AlgorithmType>
        get() = loadedPreferencesState.map(LoadedComposeLifePreferences::algorithmChoice)

    override val currentShapeState: ResourceState<CurrentShape>
        get() = loadedPreferencesState.map(LoadedComposeLifePreferences::currentShape)

    override val darkThemeConfigState: ResourceState<DarkThemeConfig>
        get() = loadedPreferencesState.map(LoadedComposeLifePreferences::darkThemeConfig)

    override val disableAGSLState: ResourceState<Boolean>
        get() = loadedPreferencesState.map(LoadedComposeLifePreferences::disableAGSL)

    override val disableOpenGLState: ResourceState<Boolean>
        get() = loadedPreferencesState.map(LoadedComposeLifePreferences::disableOpenGL)

    override val doNotKeepProcessState: ResourceState<Boolean>
        get() = loadedPreferencesState.map(LoadedComposeLifePreferences::doNotKeepProcess)

    override var loadedPreferencesState:
        ResourceState<LoadedComposeLifePreferences> by mutableStateOf(ResourceState.Loading)
            private set

    @Suppress("LongMethod", "ComplexMethod")
    override suspend fun update(): Nothing {
        dataStore.data
            .retry()
            .onEach { preferencesProto ->
                val quickAccessSettings =
                    preferencesProto.quick_access_settings.mapNotNull { quickAccessSettingProto ->
                        when (quickAccessSettingProto) {
                            QuickAccessSettingProto.ALGORITHM_IMPLEMENTATION ->
                                QuickAccessSetting.AlgorithmImplementation
                            QuickAccessSettingProto.DARK_THEME_CONFIG ->
                                QuickAccessSetting.DarkThemeConfig
                            QuickAccessSettingProto.CELL_SHAPE_CONFIG ->
                                QuickAccessSetting.CellShapeConfig
                            QuickAccessSettingProto.DISABLE_AGSL ->
                                QuickAccessSetting.DisableAGSL
                            QuickAccessSettingProto.DISABLE_OPENGL ->
                                QuickAccessSetting.DisableOpenGL
                            QuickAccessSettingProto.DO_NOT_KEEP_PROCESS ->
                                QuickAccessSetting.DoNotKeepProcess
                            QuickAccessSettingProto.SETTINGS_UNKNOWN,
                            -> null
                        }
                    }.toSet()

                val algorithmChoice =
                    when (preferencesProto.algorithm) {
                        AlgorithmProto.ALGORITHM_UNKNOWN,
                        AlgorithmProto.DEFAULT,
                        AlgorithmProto.HASHLIFE,
                        -> AlgorithmType.HashLifeAlgorithm
                        AlgorithmProto.NAIVE -> AlgorithmType.NaiveAlgorithm
                    }

                val currentShape =
                    when (preferencesProto.current_shape_type) {
                        CurrentShapeTypeProto.CURRENT_SHAPE_TYPE_UNKNOWN,
                        CurrentShapeTypeProto.ROUND_RECTANGLE,
                        -> preferencesProto.round_rectangle.toResolved()
                        CurrentShapeTypeProto.SUPERELLIPSE -> preferencesProto.superellipse.toResolved()
                    }

                val darkThemeConfig =
                    when (preferencesProto.dark_theme_config) {
                        DarkThemeConfigProto.DARK_THEME_UNKNOWN,
                        DarkThemeConfigProto.SYSTEM, -> DarkThemeConfig.FollowSystem
                        DarkThemeConfigProto.DARK -> DarkThemeConfig.Dark
                        DarkThemeConfigProto.LIGHT -> DarkThemeConfig.Light
                    }
                val disableAGSL = preferencesProto.disable_agsl
                val disableOpenGL = preferencesProto.disable_opengl
                val doNotKeepProcess = preferencesProto.do_not_keep_process

                Snapshot.withMutableSnapshot {
                    loadedPreferencesState = ResourceState.Success(
                        LoadedComposeLifePreferences(
                            quickAccessSettings = quickAccessSettings,
                            algorithmChoice = algorithmChoice,
                            currentShape = currentShape,
                            darkThemeConfig = darkThemeConfig,
                            disableAGSL = disableAGSL,
                            disableOpenGL = disableOpenGL,
                            doNotKeepProcess = doNotKeepProcess,
                        ),
                    )
                }
            }
            .catch {
                Snapshot.withMutableSnapshot {
                    loadedPreferencesState = ResourceState.Failure(it)
                }
            }
            .collect()

        error("data can not complete normally")
    }

    override suspend fun setAlgorithmChoice(algorithm: AlgorithmType) {
        dataStore.updateData { preferencesProto ->
            preferencesProto.copy(
                algorithm = when (algorithm) {
                    AlgorithmType.HashLifeAlgorithm -> AlgorithmProto.HASHLIFE
                    AlgorithmType.NaiveAlgorithm -> AlgorithmProto.NAIVE
                },
            )
        }
    }

    override suspend fun setCurrentShapeType(currentShapeType: CurrentShapeType) {
        dataStore.updateData { preferencesProto ->
            preferencesProto.copy(
                current_shape_type = when (currentShapeType) {
                    CurrentShapeType.RoundRectangle -> CurrentShapeTypeProto.ROUND_RECTANGLE
                    CurrentShapeType.Superellipse -> CurrentShapeTypeProto.SUPERELLIPSE
                },
            )
        }
    }

    override suspend fun setDarkThemeConfig(darkThemeConfig: DarkThemeConfig) {
        dataStore.updateData { preferencesProto ->
            preferencesProto.copy(
                dark_theme_config = when (darkThemeConfig) {
                    DarkThemeConfig.FollowSystem -> DarkThemeConfigProto.SYSTEM
                    DarkThemeConfig.Dark -> DarkThemeConfigProto.DARK
                    DarkThemeConfig.Light -> DarkThemeConfigProto.LIGHT
                },
            )
        }
    }

    override suspend fun setRoundRectangleConfig(update: (RoundRectangle) -> RoundRectangle) {
        dataStore.updateData { preferencesProto ->
            preferencesProto.copy(
                round_rectangle = update(preferencesProto.round_rectangle.toResolved()).toProto(),
            )
        }
    }

    override suspend fun setSuperellipseConfig(update: (Superellipse) -> Superellipse) {
        dataStore.updateData { preferencesProto ->
            preferencesProto.copy(
                superellipse = update(preferencesProto.superellipse.toResolved()).toProto(),
            )
        }
    }

    override suspend fun addQuickAccessSetting(quickAccessSetting: QuickAccessSetting) =
        updateQuickAccessSetting(true, quickAccessSetting)

    override suspend fun removeQuickAccessSetting(quickAccessSetting: QuickAccessSetting) =
        updateQuickAccessSetting(false, quickAccessSetting)

    private suspend fun updateQuickAccessSetting(include: Boolean, quickAccessSetting: QuickAccessSetting) {
        dataStore.updateData { preferencesProto ->
            val quickAccessSettingProto = when (quickAccessSetting) {
                QuickAccessSetting.AlgorithmImplementation -> QuickAccessSettingProto.ALGORITHM_IMPLEMENTATION
                QuickAccessSetting.CellShapeConfig -> QuickAccessSettingProto.CELL_SHAPE_CONFIG
                QuickAccessSetting.DarkThemeConfig -> QuickAccessSettingProto.DARK_THEME_CONFIG
                QuickAccessSetting.DisableAGSL -> QuickAccessSettingProto.DISABLE_AGSL
                QuickAccessSetting.DisableOpenGL -> QuickAccessSettingProto.DISABLE_OPENGL
                QuickAccessSetting.DoNotKeepProcess -> QuickAccessSettingProto.DO_NOT_KEEP_PROCESS
            }

            val oldQuickAccessSettings = preferencesProto.quick_access_settings.toSet()
            val newQuickAccessSetting = if (include) {
                oldQuickAccessSettings + quickAccessSettingProto
            } else {
                oldQuickAccessSettings - quickAccessSettingProto
            }

            preferencesProto.copy(
                quick_access_settings = newQuickAccessSetting.toList(),
            )
        }
    }

    override suspend fun setDisabledAGSL(disabled: Boolean) {
        dataStore.updateData { preferencesProto ->
            preferencesProto.copy(
                disable_agsl = disabled,
            )
        }
    }

    override suspend fun setDisableOpenGL(disabled: Boolean) {
        dataStore.updateData { preferencesProto ->
            preferencesProto.copy(
                disable_opengl = disabled,
            )
        }
    }

    override suspend fun setDoNotKeepProcess(doNotKeepProcess: Boolean) {
        dataStore.updateData { preferencesProto ->
            preferencesProto.copy(
                do_not_keep_process = doNotKeepProcess,
            )
        }
    }
}

private fun RoundRectangleProto?.toResolved(): RoundRectangle =
    if (this == null) {
        RoundRectangle(
            sizeFraction = 1f,
            cornerFraction = 0f,
        )
    } else {
        RoundRectangle(
            sizeFraction = size_fraction,
            cornerFraction = corner_fraction,
        )
    }

private fun RoundRectangle.toProto(): RoundRectangleProto =
    RoundRectangleProto(
        size_fraction = sizeFraction,
        corner_fraction = cornerFraction,
    )

private fun SuperellipseProto?.toResolved(): Superellipse =
    if (this == null) {
        Superellipse(
            sizeFraction = 1f,
            p = 4f,
        )
    } else {
        Superellipse(
            sizeFraction = size_fraction,
            p = p,
        )
    }

private fun Superellipse.toProto(): SuperellipseProto =
    SuperellipseProto(
        size_fraction = sizeFraction,
        p = p,
    )
