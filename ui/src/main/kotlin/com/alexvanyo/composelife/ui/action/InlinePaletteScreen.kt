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

package com.alexvanyo.composelife.ui.action

import androidx.compose.foundation.ScrollState
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.Spacer
import androidx.compose.foundation.layout.height
import androidx.compose.foundation.layout.padding
import androidx.compose.foundation.rememberScrollState
import androidx.compose.foundation.verticalScroll
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
import com.alexvanyo.composelife.preferences.CurrentShape
import com.alexvanyo.composelife.preferences.CurrentShapeType
import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.resourcestate.ResourceState
import com.alexvanyo.composelife.ui.R
import com.alexvanyo.composelife.ui.component.DropdownOption
import com.alexvanyo.composelife.ui.component.GameOfLifeProgressIndicator
import com.alexvanyo.composelife.ui.component.GameOfLifeProgressIndicatorEntryPoint
import com.alexvanyo.composelife.ui.component.LabeledSlider
import com.alexvanyo.composelife.ui.component.TextFieldDropdown
import com.alexvanyo.composelife.ui.entrypoints.WithPreviewDependencies
import com.alexvanyo.composelife.ui.theme.ComposeLifeTheme
import com.alexvanyo.composelife.ui.util.ThemePreviews
import com.livefront.sealedenum.GenSealedEnum
import dagger.hilt.EntryPoint
import dagger.hilt.InstallIn
import dagger.hilt.android.components.ActivityComponent
import kotlinx.coroutines.launch

@EntryPoint
@InstallIn(ActivityComponent::class)
interface InlinePaletteScreenEntryPoint :
    GameOfLifeProgressIndicatorEntryPoint,
    ComposeLifePreferencesProvider

context(InlinePaletteScreenEntryPoint)
@Composable
fun InlinePaletteScreen(
    modifier: Modifier = Modifier,
    scrollState: ScrollState = rememberScrollState(),
) {
    InlinePaletteScreen(
        currentShapeState = composeLifePreferences.currentShapeState,
        setCurrentShapeType = composeLifePreferences::setCurrentShapeType,
        setRoundRectangleConfig = composeLifePreferences::setRoundRectangleConfig,
        modifier = modifier,
        scrollState = scrollState,
    )
}

context(InlinePaletteScreenEntryPoint)
@Suppress("LongMethod")
@Composable
fun InlinePaletteScreen(
    currentShapeState: ResourceState<CurrentShape>,
    setCurrentShapeType: suspend (CurrentShapeType) -> Unit,
    setRoundRectangleConfig: suspend ((CurrentShape.RoundRectangle) -> CurrentShape.RoundRectangle) -> Unit,
    modifier: Modifier = Modifier,
    scrollState: ScrollState = rememberScrollState(),
) {
    Column(
        modifier = modifier
            .verticalScroll(scrollState)
            .padding(horizontal = 16.dp),
        horizontalAlignment = Alignment.CenterHorizontally,
    ) {
        when (currentShapeState) {
            ResourceState.Loading, is ResourceState.Failure -> {
                GameOfLifeProgressIndicator()
            }
            is ResourceState.Success -> {
                val currentShape = currentShapeState.value
                val coroutineScope = rememberCoroutineScope()

                TextFieldDropdown(
                    label = stringResource(R.string.shape),
                    currentValue = when (currentShape) {
                        is CurrentShape.RoundRectangle -> ShapeDropdownOption.RoundRectangle
                    },
                    allValues = ShapeDropdownOption.values,
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

                        LabeledSlider(
                            label = stringResource(id = R.string.size_fraction, sizeFraction),
                            value = sizeFraction,
                            onValueChange = { sizeFraction = it },
                            valueRange = 0.1f..1f,
                        )

                        LabeledSlider(
                            label = stringResource(id = R.string.corner_fraction, cornerFraction),
                            value = cornerFraction,
                            onValueChange = { cornerFraction = it },
                            valueRange = 0f..0.5f,
                        )
                    }
                }
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
fun LoadingInlinePaletteScreenPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            Surface {
                InlinePaletteScreen(
                    currentShapeState = ResourceState.Loading,
                    setCurrentShapeType = {},
                    setRoundRectangleConfig = {},
                )
            }
        }
    }
}

@ThemePreviews
@Composable
fun RoundRectangleInlinePaletteScreenPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            Surface {
                InlinePaletteScreen(
                    currentShapeState = ResourceState.Success(
                        CurrentShape.RoundRectangle(
                            sizeFraction = 0.8f,
                            cornerFraction = 0.4f,
                        ),
                    ),
                    setCurrentShapeType = {},
                    setRoundRectangleConfig = {},
                )
            }
        }
    }
}
