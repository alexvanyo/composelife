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

package com.alexvanyo.composelife.ui.app.action.settings

import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.Spacer
import androidx.compose.foundation.layout.height
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
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResolver
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResource
import com.alexvanyo.composelife.preferences.CurrentShape
import com.alexvanyo.composelife.preferences.CurrentShapeType
import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.preferences.di.LoadedComposeLifePreferencesProvider
import com.alexvanyo.composelife.preferences.setCurrentShapeType
import com.alexvanyo.composelife.preferences.setRoundRectangleConfig
import com.alexvanyo.composelife.sessionvalue.SessionValue
import com.alexvanyo.composelife.sessionvalue.localSessionId
import com.alexvanyo.composelife.sessionvalue.rememberSessionValueHolder
import com.alexvanyo.composelife.ui.app.component.DropdownOption
import com.alexvanyo.composelife.ui.app.component.EditableSlider
import com.alexvanyo.composelife.ui.app.component.IdentitySliderBijection
import com.alexvanyo.composelife.ui.app.component.TextFieldDropdown
import com.alexvanyo.composelife.ui.app.resources.CornerFractionLabel
import com.alexvanyo.composelife.ui.app.resources.CornerFractionLabelAndValue
import com.alexvanyo.composelife.ui.app.resources.CornerFractionValue
import com.alexvanyo.composelife.ui.app.resources.RoundRectangle
import com.alexvanyo.composelife.ui.app.resources.Shape
import com.alexvanyo.composelife.ui.app.resources.SizeFractionLabel
import com.alexvanyo.composelife.ui.app.resources.SizeFractionLabelAndValue
import com.alexvanyo.composelife.ui.app.resources.SizeFractionValue
import com.alexvanyo.composelife.ui.app.resources.Strings
import com.alexvanyo.composelife.ui.util.uuidSaver
import com.livefront.sealedenum.GenSealedEnum
import kotlinx.collections.immutable.toImmutableList
import kotlinx.coroutines.launch
import java.util.UUID

interface CellShapeConfigUiInjectEntryPoint :
    ComposeLifePreferencesProvider

interface CellShapeConfigUiLocalEntryPoint :
    LoadedComposeLifePreferencesProvider

context(CellShapeConfigUiInjectEntryPoint, CellShapeConfigUiLocalEntryPoint)
@Composable
fun CellShapeConfigUi(
    modifier: Modifier = Modifier,
) {
    CellShapeConfigUi(
        cellShapeConfigUiState = rememberCellShapeConfigUiState(),
        modifier = modifier,
    )
}

@Suppress("LongMethod")
@Composable
fun CellShapeConfigUi(
    cellShapeConfigUiState: CellShapeConfigUiState,
    modifier: Modifier = Modifier,
) {
    Column(
        modifier = modifier,
        horizontalAlignment = Alignment.CenterHorizontally,
    ) {
        TextFieldDropdown(
            label = parameterizedStringResource(Strings.Shape),
            currentValue = cellShapeConfigUiState.currentShapeDropdownOption,
            allValues = ShapeDropdownOption.values.toImmutableList(),
            setValue = cellShapeConfigUiState::setCurrentShapeType,
        )

        Spacer(modifier = Modifier.height(16.dp))

        @Suppress("USELESS_IS_CHECK")
        when (val currentShapeConfigUiState = cellShapeConfigUiState.currentShapeConfigUiState) {
            is CurrentShapeConfigUiState.RoundRectangleConfigUi -> {
                val resolver = parameterizedStringResolver()

                EditableSlider(
                    labelAndValueText = { parameterizedStringResource(Strings.SizeFractionLabelAndValue(it)) },
                    valueText = { resolver(Strings.SizeFractionValue(it)) },
                    labelText = parameterizedStringResource(Strings.SizeFractionLabel),
                    textToValue = { it.toFloatOrNull() },
                    sessionValue = currentShapeConfigUiState.sizeFractionSessionValue,
                    onSessionValueChange = currentShapeConfigUiState::onSizeFractionSessionValueChange,
                    valueRange = 0.1f..1f,
                    sliderBijection = Float.IdentitySliderBijection,
                )

                EditableSlider(
                    labelAndValueText = { parameterizedStringResource(Strings.CornerFractionLabelAndValue(it)) },
                    valueText = { resolver(Strings.CornerFractionValue(it)) },
                    labelText = parameterizedStringResource(Strings.CornerFractionLabel),
                    textToValue = { it.toFloatOrNull() },
                    sessionValue = currentShapeConfigUiState.cornerFractionSessionValue,
                    onSessionValueChange = currentShapeConfigUiState::onCornerFractionSessionValueChange,
                    valueRange = 0f..0.5f,
                    sliderBijection = Float.IdentitySliderBijection,
                )
            }
        }
    }
}

sealed interface ShapeDropdownOption : DropdownOption {
    data object RoundRectangle : ShapeDropdownOption {
        override val displayText: ParameterizedString = Strings.RoundRectangle
    }

    @GenSealedEnum
    companion object
}

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
    val currentShapeType = preferences.currentShapeType
    val coroutineScope = rememberCoroutineScope()

    val currentShapeConfigUiState = when (currentShapeType) {
        is CurrentShapeType.RoundRectangle -> {
            val roundRectangleSessionValueHolder = rememberSessionValueHolder<CurrentShape.RoundRectangle>(
                upstreamSessionValue = preferences.roundRectangleSessionValue,
                setUpstreamSessionValue = { upstreamSessionId, sessionValue ->
                    coroutineScope.launch {
                        composeLifePreferences.setRoundRectangleConfig(
                            oldSessionId = upstreamSessionId,
                            newSessionId = sessionValue.sessionId,
                            valueId = sessionValue.valueId,
                        ) { roundRectangle ->
                            roundRectangle.copy(
                                sizeFraction = sessionValue.value.sizeFraction,
                                cornerFraction = sessionValue.value.cornerFraction,
                            )
                        }
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
                    mutableStateOf(UUID.randomUUID())
                }
            }
            var sizeFractionValueId by key(localSessionId) {
                rememberSaveable(stateSaver = uuidSaver) {
                    mutableStateOf(UUID.randomUUID())
                }
            }
            var cornerFractionSessionId by key(localSessionId) {
                rememberSaveable(stateSaver = uuidSaver) {
                    mutableStateOf(UUID.randomUUID())
                }
            }
            var cornerFractionValueId by key(localSessionId) {
                rememberSaveable(stateSaver = uuidSaver) {
                    mutableStateOf(UUID.randomUUID())
                }
            }

            object : CurrentShapeConfigUiState.RoundRectangleConfigUi {
                override val sizeFractionSessionValue: SessionValue<Float> get() =
                    SessionValue(
                        sessionId = sizeFractionSessionId,
                        valueId = sizeFractionValueId,
                        value = sizeFraction,
                    )

                override val cornerFractionSessionValue: SessionValue<Float> get() =
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
            get() = when (currentShapeType) {
                CurrentShapeType.RoundRectangle -> ShapeDropdownOption.RoundRectangle
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
