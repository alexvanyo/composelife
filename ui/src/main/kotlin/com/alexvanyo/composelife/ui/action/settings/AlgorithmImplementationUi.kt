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

package com.alexvanyo.composelife.ui.action.settings

import androidx.compose.foundation.clickable
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.fillMaxWidth
import androidx.compose.material.icons.Icons
import androidx.compose.material.icons.filled.ArrowDropDown
import androidx.compose.material.icons.filled.ArrowDropUp
import androidx.compose.material3.CircularProgressIndicator
import androidx.compose.material3.DropdownMenu
import androidx.compose.material3.DropdownMenuItem
import androidx.compose.material3.Icon
import androidx.compose.material3.MaterialTheme
import androidx.compose.material3.OutlinedTextField
import androidx.compose.material3.Text
import androidx.compose.material3.TextFieldDefaults
import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.runtime.setValue
import androidx.compose.ui.Modifier
import androidx.compose.ui.res.stringResource
import androidx.compose.ui.tooling.preview.Preview
import com.alexvanyo.composelife.preferences.AlgorithmType
import com.alexvanyo.composelife.preferences.ComposeLifePreferences
import com.alexvanyo.composelife.resourcestate.ResourceState
import com.alexvanyo.composelife.ui.R
import com.alexvanyo.composelife.ui.entrypoints.preferences.inject
import com.alexvanyo.composelife.ui.theme.ComposeLifeTheme
import kotlinx.coroutines.launch

@Composable
fun AlgorithmImplementationUi(
    modifier: Modifier = Modifier,
    composeLifePreferences: ComposeLifePreferences = inject(),
) {
    AlgorithmImplementationUi(
        algorithmChoiceState = composeLifePreferences.algorithmChoiceState,
        setAlgorithmChoice = composeLifePreferences::setAlgorithmChoice,
        modifier = modifier,
    )
}

@Suppress("LongMethod")
@Composable
fun AlgorithmImplementationUi(
    algorithmChoiceState: ResourceState<AlgorithmType>,
    setAlgorithmChoice: suspend (AlgorithmType) -> Unit,
    modifier: Modifier = Modifier,
) {
    Box(modifier = modifier) {
        when (algorithmChoiceState) {
            ResourceState.Loading, is ResourceState.Failure -> {
                CircularProgressIndicator()
            }

            is ResourceState.Success -> {
                val currentAlgorithm = algorithmChoiceState.value
                val coroutineScope = rememberCoroutineScope()

                var isShowingDropdownMenu by remember { mutableStateOf(false) }

                Box {
                    OutlinedTextField(
                        value = stringResource(
                            id = when (currentAlgorithm) {
                                AlgorithmType.HashLifeAlgorithm -> R.string.hash_life_algorithm
                                AlgorithmType.NaiveAlgorithm -> R.string.naive_algorithm
                            },
                        ),
                        onValueChange = {},
                        enabled = false,
                        readOnly = true,
                        label = {
                            Text(text = stringResource(R.string.algorithm_implementation))
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

                    fun chooseAlgorithmImplementation(
                        algorithmType: AlgorithmType,
                    ) {
                        coroutineScope.launch {
                            setAlgorithmChoice(algorithmType)
                            isShowingDropdownMenu = false
                        }
                    }

                    DropdownMenu(
                        expanded = isShowingDropdownMenu,
                        onDismissRequest = { isShowingDropdownMenu = false },
                    ) {
                        DropdownMenuItem(
                            text = { Text(stringResource(id = R.string.hash_life_algorithm)) },
                            onClick = {
                                chooseAlgorithmImplementation(AlgorithmType.HashLifeAlgorithm)
                            },
                        )
                        DropdownMenuItem(
                            text = { Text(stringResource(id = R.string.naive_algorithm)) },
                            onClick = {
                                chooseAlgorithmImplementation(AlgorithmType.NaiveAlgorithm)
                            },
                        )
                    }
                }
            }
        }
    }
}

@Preview
@Composable
fun AlgorithmImplementationUiLoadingPreview() {
    ComposeLifeTheme {
        AlgorithmImplementationUi(
            algorithmChoiceState = ResourceState.Loading,
            setAlgorithmChoice = {},
        )
    }
}

@Preview
@Composable
fun AlgorithmImplementationUiLoadedPreview() {
    ComposeLifeTheme {
        AlgorithmImplementationUi(
            algorithmChoiceState = ResourceState.Success(AlgorithmType.HashLifeAlgorithm),
            setAlgorithmChoice = {},
        )
    }
}
