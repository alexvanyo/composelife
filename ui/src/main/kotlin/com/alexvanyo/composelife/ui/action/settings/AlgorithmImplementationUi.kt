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

import androidx.compose.foundation.layout.Box
import androidx.compose.runtime.Composable
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.ui.Modifier
import androidx.compose.ui.res.stringResource
import androidx.compose.ui.tooling.preview.Preview
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import com.alexvanyo.composelife.preferences.AlgorithmType
import com.alexvanyo.composelife.resourcestate.ResourceState
import com.alexvanyo.composelife.ui.R
import com.alexvanyo.composelife.ui.component.DropdownOption
import com.alexvanyo.composelife.ui.component.GameOfLifeProgressIndicator
import com.alexvanyo.composelife.ui.component.TextFieldDropdown
import com.alexvanyo.composelife.ui.entrypoints.WithPreviewDependencies
import com.alexvanyo.composelife.ui.entrypoints.algorithm.GameOfLifeAlgorithmEntryPoint
import com.alexvanyo.composelife.ui.entrypoints.dispatchers.ComposeLifeDispatchersEntryPoint
import com.alexvanyo.composelife.ui.entrypoints.preferences.ComposeLifePreferencesEntryPoint
import com.alexvanyo.composelife.ui.theme.ComposeLifeTheme
import com.livefront.sealedenum.GenSealedEnum
import kotlinx.coroutines.launch

context(GameOfLifeAlgorithmEntryPoint, ComposeLifePreferencesEntryPoint, ComposeLifeDispatchersEntryPoint)
@Composable
fun AlgorithmImplementationUi(
    modifier: Modifier = Modifier,
) {
    AlgorithmImplementationUi(
        algorithmChoiceState = composeLifePreferences.algorithmChoiceState,
        setAlgorithmChoice = composeLifePreferences::setAlgorithmChoice,
        modifier = modifier,
    )
}

context(GameOfLifeAlgorithmEntryPoint, ComposeLifePreferencesEntryPoint, ComposeLifeDispatchersEntryPoint)
@Composable
fun AlgorithmImplementationUi(
    algorithmChoiceState: ResourceState<AlgorithmType>,
    setAlgorithmChoice: suspend (AlgorithmType) -> Unit,
    modifier: Modifier = Modifier,
) {
    Box(modifier = modifier) {
        when (algorithmChoiceState) {
            ResourceState.Loading, is ResourceState.Failure -> {
                GameOfLifeProgressIndicator()
            }

            is ResourceState.Success -> {
                val currentAlgorithm = algorithmChoiceState.value
                val coroutineScope = rememberCoroutineScope()

                TextFieldDropdown(
                    label = stringResource(R.string.algorithm_implementation),
                    currentValue = when (currentAlgorithm) {
                        AlgorithmType.HashLifeAlgorithm -> AlgorithmImplementationDropdownOption.HashLifeAlgorithm
                        AlgorithmType.NaiveAlgorithm -> AlgorithmImplementationDropdownOption.NaiveAlgorithm
                    },
                    allValues = AlgorithmImplementationDropdownOption.values,
                    setValue = { option ->
                        coroutineScope.launch {
                            setAlgorithmChoice(
                                when (option) {
                                    AlgorithmImplementationDropdownOption.HashLifeAlgorithm ->
                                        AlgorithmType.HashLifeAlgorithm
                                    AlgorithmImplementationDropdownOption.NaiveAlgorithm ->
                                        AlgorithmType.NaiveAlgorithm
                                },
                            )
                        }
                    },
                )
            }
        }
    }
}

sealed interface AlgorithmImplementationDropdownOption : DropdownOption {
    object HashLifeAlgorithm : AlgorithmImplementationDropdownOption {
        override val displayText: ParameterizedString = ParameterizedString(R.string.hash_life_algorithm)
    }
    object NaiveAlgorithm : AlgorithmImplementationDropdownOption {
        override val displayText: ParameterizedString = ParameterizedString(R.string.naive_algorithm)
    }

    @GenSealedEnum
    companion object
}

@Preview
@Composable
fun AlgorithmImplementationUiLoadingPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            AlgorithmImplementationUi(
                algorithmChoiceState = ResourceState.Loading,
                setAlgorithmChoice = {},
            )
        }
    }
}

@Preview
@Composable
fun AlgorithmImplementationUiLoadedPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            AlgorithmImplementationUi(
                algorithmChoiceState = ResourceState.Success(AlgorithmType.HashLifeAlgorithm),
                setAlgorithmChoice = {},
            )
        }
    }
}
