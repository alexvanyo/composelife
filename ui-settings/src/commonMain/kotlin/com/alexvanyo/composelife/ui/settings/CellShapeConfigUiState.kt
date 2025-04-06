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

package com.alexvanyo.composelife.ui.settings

import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.key
import androidx.compose.runtime.mutableFloatStateOf
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.setValue
import com.alexvanyo.composelife.preferences.ComposeLifePreferences
import com.alexvanyo.composelife.preferences.CurrentShape
import com.alexvanyo.composelife.preferences.CurrentShapeType
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferences
import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.preferences.di.LoadedComposeLifePreferencesProvider
import com.alexvanyo.composelife.preferences.setCurrentShapeType
import com.alexvanyo.composelife.preferences.setRoundRectangleConfig
import com.alexvanyo.composelife.serialization.uuidSaver
import com.alexvanyo.composelife.sessionvalue.SessionValue
import com.alexvanyo.composelife.sessionvalue.localSessionId
import com.alexvanyo.composelife.sessionvalue.rememberAsyncSessionValueHolder
import kotlinx.coroutines.launch
import kotlin.uuid.Uuid

interface CellShapeConfigUiInjectEntryPoint :
    ComposeLifePreferencesProvider

interface CellShapeConfigUiLocalEntryPoint :
    LoadedComposeLifePreferencesProvider

interface CellShapeConfigUiState {
    val currentShapeDropdownOption: ShapeDropdownOption

    val currentShapeConfigUiState: CurrentShapeConfigUiState

    fun setCurrentShapeType(option: ShapeDropdownOption)
}

sealed interface CurrentShapeConfigUiState {

    interface RoundRectangleConfigUi : CurrentShapeConfigUiState {
        val sizeFractionSessionValue: SessionValue<Float>

        val cornerFractionSessionValue: SessionValue<Float>

        fun onSizeFractionSessionValueChange(expected: SessionValue<Float>, newValue: SessionValue<Float>)

        fun onCornerFractionSessionValueChange(expected: SessionValue<Float>, newValue: SessionValue<Float>)
    }
}

context(injectEntryPoint: CellShapeConfigUiInjectEntryPoint, localEntryPoint: CellShapeConfigUiLocalEntryPoint)
@Composable
fun rememberCellShapeConfigUiState(): CellShapeConfigUiState =
    rememberCellShapeConfigUiState(
        composeLifePreferences = injectEntryPoint.composeLifePreferences,
        preferences = localEntryPoint.preferences,
    )

@Suppress("LongMethod")
@Composable
fun rememberCellShapeConfigUiState(
    composeLifePreferences: ComposeLifePreferences,
    preferences: LoadedComposeLifePreferences,
): CellShapeConfigUiState {
    val currentShapeType: CurrentShapeType = preferences.currentShapeType
    val coroutineScope = rememberCoroutineScope()
    val roundRectangleSessionValueHolder = rememberAsyncSessionValueHolder(
        upstreamSessionValue = preferences.roundRectangleSessionValue,
        setUpstreamSessionValue = composeLifePreferences::setRoundRectangleConfig,
    )

    val currentShapeConfigUiState = when (currentShapeType) {
        is CurrentShapeType.RoundRectangle -> {
            val localSessionId = roundRectangleSessionValueHolder.info.localSessionId

            val initialSizeFraction = remember(localSessionId) {
                roundRectangleSessionValueHolder.sessionValue.value.sizeFraction
            }
            val initialCornerFraction = remember(localSessionId) {
                roundRectangleSessionValueHolder.sessionValue.value.cornerFraction
            }
            var sizeFraction by remember(localSessionId) {
                mutableFloatStateOf(initialSizeFraction)
            }
            var cornerFraction by remember(localSessionId) {
                mutableFloatStateOf(initialCornerFraction)
            }

            var sizeFractionSessionId by key(localSessionId) {
                rememberSaveable(stateSaver = uuidSaver) {
                    mutableStateOf(Uuid.random())
                }
            }
            var sizeFractionValueId by key(localSessionId) {
                rememberSaveable(stateSaver = uuidSaver) {
                    mutableStateOf(Uuid.random())
                }
            }
            var cornerFractionSessionId by key(localSessionId) {
                rememberSaveable(stateSaver = uuidSaver) {
                    mutableStateOf(Uuid.random())
                }
            }
            var cornerFractionValueId by key(localSessionId) {
                rememberSaveable(stateSaver = uuidSaver) {
                    mutableStateOf(Uuid.random())
                }
            }

            object : CurrentShapeConfigUiState.RoundRectangleConfigUi {
                override val sizeFractionSessionValue: SessionValue<Float>
                    get() =
                        SessionValue(
                            sessionId = sizeFractionSessionId,
                            valueId = sizeFractionValueId,
                            value = sizeFraction,
                        )

                override val cornerFractionSessionValue: SessionValue<Float>
                    get() =
                        SessionValue(
                            sessionId = cornerFractionSessionId,
                            valueId = cornerFractionValueId,
                            value = cornerFraction,
                        )

                override fun onSizeFractionSessionValueChange(
                    expected: SessionValue<Float>,
                    newValue: SessionValue<Float>,
                ) {
                    if (expected.sessionId == sizeFractionSessionId && expected.valueId == sizeFractionValueId) {
                        sizeFractionSessionId = newValue.sessionId
                        sizeFractionValueId = newValue.valueId
                        sizeFraction = newValue.value
                        updateRoundRectangleConfig()
                    }
                }

                override fun onCornerFractionSessionValueChange(
                    expected: SessionValue<Float>,
                    newValue: SessionValue<Float>,
                ) {
                    if (expected.sessionId == cornerFractionSessionId && expected.valueId == cornerFractionValueId) {
                        cornerFractionSessionId = newValue.sessionId
                        cornerFractionValueId = newValue.valueId
                        cornerFraction = newValue.value
                        updateRoundRectangleConfig()
                    }
                }

                private fun updateRoundRectangleConfig() {
                    roundRectangleSessionValueHolder.setValue(
                        CurrentShape.RoundRectangle(
                            sizeFraction,
                            cornerFraction,
                        ),
                    )
                }
            }
        }
    }

    return object : CellShapeConfigUiState {
        override val currentShapeDropdownOption: ShapeDropdownOption
            get() = when (currentShapeType as CurrentShapeType) {
                is CurrentShapeType.RoundRectangle -> ShapeDropdownOption.RoundRectangle
            }

        override val currentShapeConfigUiState: CurrentShapeConfigUiState
            get() = currentShapeConfigUiState

        override fun setCurrentShapeType(option: ShapeDropdownOption) {
            coroutineScope.launch {
                composeLifePreferences.setCurrentShapeType(
                    when (option) {
                        ShapeDropdownOption.RoundRectangle -> CurrentShapeType.RoundRectangle
                    },
                )
            }
        }
    }
}
