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

package com.alexvanyo.composelife.ui.action

import androidx.compose.foundation.ScrollState
import androidx.compose.foundation.clickable
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.Spacer
import androidx.compose.foundation.layout.fillMaxWidth
import androidx.compose.foundation.layout.height
import androidx.compose.foundation.layout.padding
import androidx.compose.foundation.rememberScrollState
import androidx.compose.foundation.verticalScroll
import androidx.compose.material.icons.Icons
import androidx.compose.material.icons.filled.ArrowDropDown
import androidx.compose.material.icons.filled.ArrowDropUp
import androidx.compose.material3.DropdownMenu
import androidx.compose.material3.DropdownMenuItem
import androidx.compose.material3.Icon
import androidx.compose.material3.MaterialTheme
import androidx.compose.material3.OutlinedTextField
import androidx.compose.material3.Surface
import androidx.compose.material3.Text
import androidx.compose.material3.TextFieldDefaults
import androidx.compose.runtime.Composable
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.runtime.setValue
import androidx.compose.ui.Modifier
import androidx.compose.ui.res.stringResource
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.preferences.ComposeLifePreferences
import com.alexvanyo.composelife.preferences.CurrentShape
import com.alexvanyo.composelife.preferences.CurrentShapeType
import com.alexvanyo.composelife.resourcestate.ResourceState
import com.alexvanyo.composelife.ui.R
import com.alexvanyo.composelife.ui.component.GameOfLifeProgressIndicator
import com.alexvanyo.composelife.ui.component.LabeledSlider
import com.alexvanyo.composelife.ui.entrypoints.preferences.inject
import com.alexvanyo.composelife.ui.theme.ComposeLifeTheme
import com.alexvanyo.composelife.ui.util.ThemePreviews
import kotlinx.coroutines.launch

@Composable
fun InlinePaletteScreen(
    modifier: Modifier = Modifier,
    preferences: ComposeLifePreferences = inject(),
    scrollState: ScrollState = rememberScrollState(),
) {
    InlinePaletteScreen(
        currentShapeState = preferences.currentShapeState,
        setCurrentShapeType = preferences::setCurrentShapeType,
        setRoundRectangleConfig = preferences::setRoundRectangleConfig,
        modifier = modifier,
        scrollState = scrollState,
    )
}

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
    ) {
        when (currentShapeState) {
            ResourceState.Loading, is ResourceState.Failure -> {
                GameOfLifeProgressIndicator()
            }
            is ResourceState.Success -> {
                val currentShape = currentShapeState.value
                val coroutineScope = rememberCoroutineScope()

                var isShowingDropdownMenu by remember { mutableStateOf(false) }

                Box {
                    OutlinedTextField(
                        value = stringResource(
                            id = when (currentShape) {
                                is CurrentShape.RoundRectangle -> R.string.round_rectangle
                            },
                        ),
                        onValueChange = {},
                        enabled = false,
                        readOnly = true,
                        label = {
                            Text(text = stringResource(R.string.shape))
                        },
                        trailingIcon = {
                            Icon(
                                if (isShowingDropdownMenu) {
                                    Icons.Default.ArrowDropUp
                                } else {
                                    Icons.Default.ArrowDropDown
                                },
                                contentDescription = null,
                            )
                        },
                        colors = TextFieldDefaults.outlinedTextFieldColors(
                            containerColor = MaterialTheme.colorScheme.surfaceVariant,
                            disabledBorderColor = MaterialTheme.colorScheme.outline,
                            disabledTextColor = MaterialTheme.colorScheme.onSurfaceVariant,
                            disabledTrailingIconColor = MaterialTheme.colorScheme.onSurfaceVariant,
                            disabledLabelColor = MaterialTheme.colorScheme.onSurfaceVariant,
                        ),
                        modifier = Modifier
                            .fillMaxWidth()
                            .clickable {
                                isShowingDropdownMenu = true
                            },
                    )

                    DropdownMenu(
                        expanded = isShowingDropdownMenu,
                        onDismissRequest = { isShowingDropdownMenu = false },
                    ) {
                        DropdownMenuItem(
                            text = { Text(stringResource(id = R.string.round_rectangle)) },
                            onClick = {
                                coroutineScope.launch {
                                    setCurrentShapeType(CurrentShapeType.RoundRectangle)
                                    isShowingDropdownMenu = false
                                }
                            },
                        )
                    }
                }

                Spacer(modifier = Modifier.height(16.dp))

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

@ThemePreviews
@Composable
fun LoadingInlinePaletteScreenPreview() {
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

@ThemePreviews
@Composable
fun RoundRectangleInlinePaletteScreenPreview() {
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
