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
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResolver
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResource
import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.preferences.di.LoadedComposeLifePreferencesProvider
import com.alexvanyo.composelife.ui.app.component.EditableSlider
import com.alexvanyo.composelife.ui.app.component.IdentitySliderBijection
import com.alexvanyo.composelife.ui.app.component.TextFieldDropdown
import com.alexvanyo.composelife.ui.app.resources.CornerFractionLabel
import com.alexvanyo.composelife.ui.app.resources.CornerFractionLabelAndValue
import com.alexvanyo.composelife.ui.app.resources.CornerFractionValue
import com.alexvanyo.composelife.ui.app.resources.Shape
import com.alexvanyo.composelife.ui.app.resources.SizeFractionLabel
import com.alexvanyo.composelife.ui.app.resources.SizeFractionLabelAndValue
import com.alexvanyo.composelife.ui.app.resources.SizeFractionValue
import com.alexvanyo.composelife.ui.app.resources.Strings
import kotlinx.collections.immutable.toImmutableList

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
            allValues = ShapeDropdownOption._values.toImmutableList(),
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
