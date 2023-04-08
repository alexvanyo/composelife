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
import androidx.compose.material3.Surface
import androidx.compose.runtime.Composable
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.runtime.setValue
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.res.stringResource
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResolver
import com.alexvanyo.composelife.preferences.CurrentShape
import com.alexvanyo.composelife.preferences.CurrentShapeType
import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.preferences.di.LoadedComposeLifePreferencesProvider
import com.alexvanyo.composelife.ui.app.R
import com.alexvanyo.composelife.ui.app.component.DropdownOption
import com.alexvanyo.composelife.ui.app.component.EditableSlider
import com.alexvanyo.composelife.ui.app.component.IdentitySliderBijection
import com.alexvanyo.composelife.ui.app.component.TextFieldDropdown
import com.alexvanyo.composelife.ui.app.entrypoints.WithPreviewDependencies
import com.alexvanyo.composelife.ui.app.theme.ComposeLifeTheme
import com.alexvanyo.composelife.ui.util.ThemePreviews
import com.livefront.sealedenum.GenSealedEnum
import dagger.hilt.EntryPoint
import dagger.hilt.InstallIn
import dagger.hilt.android.components.ActivityComponent
import kotlinx.collections.immutable.toImmutableList
import kotlinx.coroutines.launch

@EntryPoint
@InstallIn(ActivityComponent::class)
interface CellShapeConfigUiHiltEntryPoint :
    ComposeLifePreferencesProvider

interface CellShapeConfigUiLocalEntryPoint :
    LoadedComposeLifePreferencesProvider

context(CellShapeConfigUiHiltEntryPoint, CellShapeConfigUiLocalEntryPoint)
@Composable
fun CellShapeConfigUi(
    modifier: Modifier = Modifier,
) {
    CellShapeConfigUi(
        currentShape = preferences.currentShape,
        setCurrentShapeType = composeLifePreferences::setCurrentShapeType,
        setRoundRectangleConfig = composeLifePreferences::setRoundRectangleConfig,
        modifier = modifier,
    )
}

@Suppress("LongMethod")
@Composable
fun CellShapeConfigUi(
    currentShape: CurrentShape,
    setCurrentShapeType: suspend (CurrentShapeType) -> Unit,
    setRoundRectangleConfig: suspend ((CurrentShape.RoundRectangle) -> CurrentShape.RoundRectangle) -> Unit,
    modifier: Modifier = Modifier,
) {
    Column(
        modifier = modifier,
        horizontalAlignment = Alignment.CenterHorizontally,
    ) {
        val coroutineScope = rememberCoroutineScope()

        TextFieldDropdown(
            label = stringResource(R.string.shape),
            currentValue = when (currentShape) {
                is CurrentShape.RoundRectangle -> ShapeDropdownOption.RoundRectangle
            },
            allValues = ShapeDropdownOption.values.toImmutableList(),
            setValue = { option ->
                coroutineScope.launch {
                    setCurrentShapeType(
                        when (option) {
                            ShapeDropdownOption.RoundRectangle -> CurrentShapeType.RoundRectangle
                        },
                    )
                }
            },
        )

        Spacer(modifier = Modifier.height(16.dp))

        @Suppress("USELESS_IS_CHECK")
        when (currentShape) {
            is CurrentShape.RoundRectangle -> {
                var sizeFraction by remember { mutableStateOf(currentShape.sizeFraction) }
                var cornerFraction by remember { mutableStateOf(currentShape.cornerFraction) }

                LaunchedEffect(sizeFraction, cornerFraction) {
                    setRoundRectangleConfig { roundRectangle ->
                        roundRectangle.copy(
                            sizeFraction = sizeFraction,
                            cornerFraction = cornerFraction,
                        )
                    }
                }

                val resolver = parameterizedStringResolver()

                EditableSlider(
                    labelAndValueText = { stringResource(id = R.string.size_fraction_label_and_value, it) },
                    valueText = { resolver(ParameterizedString(R.string.size_fraction_value, it)) },
                    labelText = stringResource(id = R.string.size_fraction_label),
                    textToValue = { it.toFloatOrNull() },
                    value = sizeFraction,
                    onValueChange = { sizeFraction = it },
                    valueRange = 0.1f..1f,
                    sliderBijection = Float.IdentitySliderBijection,
                )

                EditableSlider(
                    labelAndValueText = { stringResource(id = R.string.corner_fraction_label_and_value, it) },
                    valueText = { resolver(ParameterizedString(R.string.corner_fraction_value, it)) },
                    labelText = stringResource(id = R.string.corner_fraction_label),
                    textToValue = { it.toFloatOrNull() },
                    value = cornerFraction,
                    onValueChange = { cornerFraction = it },
                    valueRange = 0f..0.5f,
                    sliderBijection = Float.IdentitySliderBijection,
                )
            }
        }
    }
}

sealed interface ShapeDropdownOption : DropdownOption {
    object RoundRectangle : ShapeDropdownOption {
        override val displayText: ParameterizedString = ParameterizedString(R.string.round_rectangle)
    }

    @GenSealedEnum
    companion object
}

@ThemePreviews
@Composable
fun CellShapeConfigUiRoundRectanglePreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            Surface {
                CellShapeConfigUi(
                    currentShape = CurrentShape.RoundRectangle(
                        sizeFraction = 0.8f,
                        cornerFraction = 0.4f,
                    ),
                    setCurrentShapeType = {},
                    setRoundRectangleConfig = {},
                )
            }
        }
    }
}
