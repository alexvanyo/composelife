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

package com.alexvanyo.composelife.ui.app.action.settings

import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.key
import androidx.compose.runtime.mutableFloatStateOf
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.runtime.saveable.listSaver
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.setValue
import com.alexvanyo.composelife.preferences.CurrentShape
import com.alexvanyo.composelife.preferences.CurrentShapeType
import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.preferences.di.LoadedComposeLifePreferencesProvider
import com.alexvanyo.composelife.preferences.setCurrentShapeType
import com.alexvanyo.composelife.preferences.setRoundRectangleConfig
import com.alexvanyo.composelife.sessionvalue.SessionValue
import com.alexvanyo.composelife.sessionvalue.localSessionId
import com.alexvanyo.composelife.sessionvalue.rememberSessionValueHolder
import com.alexvanyo.composelife.ui.util.uuidSaver
import com.benasher44.uuid.uuid4
import kotlinx.coroutines.launch

interface CellShapeConfigUiState {
    val currentShapeDropdownOption: ShapeDropdownOption

    val currentShapeConfigUiState: CurrentShapeConfigUiState

    fun setCurrentShapeType(option: ShapeDropdownOption)
}

sealed interface CurrentShapeConfigUiState {

    interface RoundRectangleConfigUi : CurrentShapeConfigUiState {
        val sizeFractionSessionValue: SessionValue<Float>

        val cornerFractionSessionValue: SessionValue<Float>

        fun onSizeFractionSessionValueChange(value: SessionValue<Float>)

        fun onCornerFractionSessionValueChange(value: SessionValue<Float>)
    }
}

context(ComposeLifePreferencesProvider, LoadedComposeLifePreferencesProvider)
@Suppress("LongMethod")
@Composable
fun rememberCellShapeConfigUiState(): CellShapeConfigUiState {
    val currentShapeType: CurrentShapeType = preferences.currentShapeType
    val coroutineScope = rememberCoroutineScope()

    val currentShapeConfigUiState = when (currentShapeType) {
        is CurrentShapeType.RoundRectangle -> {
            val roundRectangleSessionValueHolder = rememberSessionValueHolder<CurrentShape.RoundRectangle>(
                upstreamSessionValue = preferences.roundRectangleSessionValue,
                setUpstreamSessionValue = { expected, newValue ->
                    coroutineScope.launch {
                        composeLifePreferences.setRoundRectangleConfig(expected, newValue)
                    }
                },
                valueSaver = listSaver(
                    save = {
                        listOf(it.sizeFraction, it.cornerFraction)
                    },
                    restore = {
                        CurrentShape.RoundRectangle(
                            it[0],
                            it[1],
                        )
                    },
                ),
            )

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
                    mutableStateOf(uuid4())
                }
            }
            var sizeFractionValueId by key(localSessionId) {
                rememberSaveable(stateSaver = uuidSaver) {
                    mutableStateOf(uuid4())
                }
            }
            var cornerFractionSessionId by key(localSessionId) {
                rememberSaveable(stateSaver = uuidSaver) {
                    mutableStateOf(uuid4())
                }
            }
            var cornerFractionValueId by key(localSessionId) {
                rememberSaveable(stateSaver = uuidSaver) {
                    mutableStateOf(uuid4())
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

                override fun onSizeFractionSessionValueChange(value: SessionValue<Float>) {
                    sizeFractionSessionId = value.sessionId
                    sizeFractionValueId = value.valueId
                    sizeFraction = value.value
                    launchRoundRectangleConfigUpdate()
                }

                override fun onCornerFractionSessionValueChange(value: SessionValue<Float>) {
                    cornerFractionSessionId = value.sessionId
                    cornerFractionValueId = value.valueId
                    cornerFraction = value.value
                    launchRoundRectangleConfigUpdate()
                }

                private fun launchRoundRectangleConfigUpdate() {
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
