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
import com.alexvanyo.composelife.preferences.proto.AlgorithmProto
import com.alexvanyo.composelife.preferences.proto.CurrentShapeTypeProto
import com.alexvanyo.composelife.preferences.proto.DarkThemeConfigProto
import com.alexvanyo.composelife.preferences.proto.QuickAccessSettingProto
import com.alexvanyo.composelife.preferences.proto.RoundRectangleProto
import com.alexvanyo.composelife.preferences.proto.copy
import com.alexvanyo.composelife.preferences.proto.roundRectangleProto
import com.alexvanyo.composelife.resourcestate.ResourceState
import kotlinx.coroutines.flow.catch
import kotlinx.coroutines.flow.collect
import kotlinx.coroutines.flow.onEach
import javax.inject.Inject
import javax.inject.Singleton

@Singleton
class DefaultComposeLifePreferences @Inject constructor(
    private val dataStore: PreferencesDataStore,
) : ComposeLifePreferences {

    override var quickAccessSettings: ResourceState<Set<QuickAccessSetting>> by mutableStateOf(ResourceState.Loading)
        private set

    override var algorithmChoiceState: ResourceState<AlgorithmType> by mutableStateOf(ResourceState.Loading)
        private set

    override var currentShapeState: ResourceState<CurrentShape> by mutableStateOf(ResourceState.Loading)
        private set

    override var darkThemeConfigState: ResourceState<DarkThemeConfig> by mutableStateOf(ResourceState.Loading)
        private set

    override suspend fun update() {
        dataStore.data
            .onEach { preferencesProto ->
                Snapshot.withMutableSnapshot {
                    quickAccessSettings = ResourceState.Success(
                        preferencesProto.quickAccessSettingsList.mapNotNull { quickAccessSettingProto ->
                            when (quickAccessSettingProto!!) {
                                QuickAccessSettingProto.ALGORITHM_IMPLEMENTATION ->
                                    QuickAccessSetting.AlgorithmImplementation
                                QuickAccessSettingProto.DARK_THEME_CONFIG ->
                                    QuickAccessSetting.DarkThemeConfig
                                QuickAccessSettingProto.CELL_SHAPE_CONFIG ->
                                    QuickAccessSetting.CellShapeConfig
                                QuickAccessSettingProto.SETTINGS_UNKNOWN,
                                QuickAccessSettingProto.UNRECOGNIZED,
                                -> null
                            }
                        }.toSet(),
                    )

                    algorithmChoiceState = ResourceState.Success(
                        when (preferencesProto.algorithm!!) {
                            AlgorithmProto.ALGORITHM_UNKNOWN,
                            AlgorithmProto.DEFAULT,
                            AlgorithmProto.HASHLIFE,
                            AlgorithmProto.UNRECOGNIZED,
                            -> AlgorithmType.HashLifeAlgorithm
                            AlgorithmProto.NAIVE -> AlgorithmType.NaiveAlgorithm
                        },
                    )

                    currentShapeState = ResourceState.Success(
                        when (preferencesProto.currentShapeType!!) {
                            CurrentShapeTypeProto.CURRENT_SHAPE_TYPE_UNKNOWN,
                            CurrentShapeTypeProto.UNRECOGNIZED, -> defaultRoundRectangle
                            CurrentShapeTypeProto.ROUND_RECTANGLE -> preferencesProto.roundRectangle.toResolved()
                        },
                    )

                    darkThemeConfigState = ResourceState.Success(
                        when (preferencesProto.darkThemeConfig!!) {
                            DarkThemeConfigProto.DARK_THEME_UNKNOWN,
                            DarkThemeConfigProto.UNRECOGNIZED,
                            DarkThemeConfigProto.SYSTEM, -> DarkThemeConfig.FollowSystem
                            DarkThemeConfigProto.DARK -> DarkThemeConfig.Dark
                            DarkThemeConfigProto.LIGHT -> DarkThemeConfig.Light
                        },
                    )
                }
            }
            .catch {
                Snapshot.withMutableSnapshot {
                    quickAccessSettings = ResourceState.Failure(it)
                    algorithmChoiceState = ResourceState.Failure(it)
                    currentShapeState = ResourceState.Failure(it)
                    darkThemeConfigState = ResourceState.Failure(it)
                }
            }
            .collect()
    }

    override suspend fun setAlgorithmChoice(algorithm: AlgorithmType) {
        dataStore.updateData { preferencesProto ->
            preferencesProto.copy {
                this.algorithm = when (algorithm) {
                    AlgorithmType.HashLifeAlgorithm -> AlgorithmProto.HASHLIFE
                    AlgorithmType.NaiveAlgorithm -> AlgorithmProto.NAIVE
                }
            }
        }
    }

    override suspend fun setCurrentShapeType(currentShapeType: CurrentShapeType) {
        dataStore.updateData { preferencesProto ->
            preferencesProto.copy {
                this.currentShapeType = when (currentShapeType) {
                    CurrentShapeType.RoundRectangle -> CurrentShapeTypeProto.ROUND_RECTANGLE
                }
            }
        }
    }

    override suspend fun setDarkThemeConfig(darkThemeConfig: DarkThemeConfig) {
        dataStore.updateData { preferencesProto ->
            preferencesProto.copy {
                this.darkThemeConfig = when (darkThemeConfig) {
                    DarkThemeConfig.FollowSystem -> DarkThemeConfigProto.SYSTEM
                    DarkThemeConfig.Dark -> DarkThemeConfigProto.DARK
                    DarkThemeConfig.Light -> DarkThemeConfigProto.LIGHT
                }
            }
        }
    }

    override suspend fun setRoundRectangleConfig(update: (RoundRectangle) -> RoundRectangle) {
        dataStore.updateData { preferencesProto ->
            preferencesProto.copy {
                when (currentShapeType) {
                    CurrentShapeTypeProto.CURRENT_SHAPE_TYPE_UNKNOWN,
                    CurrentShapeTypeProto.UNRECOGNIZED, -> {
                        currentShapeType = CurrentShapeTypeProto.ROUND_RECTANGLE
                        roundRectangle = defaultRoundRectangle.toProto()
                    }
                    CurrentShapeTypeProto.ROUND_RECTANGLE -> Unit
                }
                roundRectangle = update(roundRectangle.toResolved()).toProto()
            }
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
            }

            preferencesProto.copy {
                val oldQuickAccessSettings = quickAccessSettings.toSet()
                quickAccessSettings.clear()
                val newQuickAccessSetting = if (include) {
                    oldQuickAccessSettings + quickAccessSettingProto
                } else {
                    oldQuickAccessSettings - quickAccessSettingProto
                }
                quickAccessSettings.addAll(newQuickAccessSetting)
            }
        }
    }
}

private val defaultRoundRectangle
    get() = RoundRectangle(
        sizeFraction = 1f,
        cornerFraction = 0f,
    )

private fun RoundRectangleProto.toResolved(): RoundRectangle =
    RoundRectangle(
        sizeFraction = sizeFraction,
        cornerFraction = cornerFraction,
    )

private fun RoundRectangle.toProto(): RoundRectangleProto =
    roundRectangleProto {
        sizeFraction = this@toProto.sizeFraction
        cornerFraction = this@toProto.cornerFraction
    }
