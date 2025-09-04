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

package com.alexvanyo.composelife.ui.settings

import androidx.compose.runtime.Composable
import androidx.compose.runtime.Immutable
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.ui.Modifier
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResource
import com.alexvanyo.composelife.preferences.AlgorithmType
import com.alexvanyo.composelife.preferences.ComposeLifePreferences
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferencesHolder
import com.alexvanyo.composelife.preferences.setAlgorithmChoice
import com.alexvanyo.composelife.ui.mobile.component.DropdownOption
import com.alexvanyo.composelife.ui.mobile.component.TextFieldDropdown
import com.alexvanyo.composelife.ui.settings.resources.AlgorithmImplementation
import com.alexvanyo.composelife.ui.settings.resources.HashLifeAlgorithm
import com.alexvanyo.composelife.ui.settings.resources.NaiveAlgorithm
import com.alexvanyo.composelife.ui.settings.resources.Strings
import com.livefront.sealedenum.GenSealedEnum
import dev.zacsweers.metro.Inject
import kotlinx.collections.immutable.toImmutableList
import kotlinx.coroutines.launch

// region templated-ctx
@Immutable
@Inject
class AlgorithmImplementationUiCtx(
    private val preferencesHolder: LoadedComposeLifePreferencesHolder,
    private val composeLifePreferences: ComposeLifePreferences,
) {
    @Suppress("ComposableNaming")
    @Composable
    operator fun invoke(
        modifier: Modifier = Modifier,
    ) = lambda(preferencesHolder, composeLifePreferences, modifier)

    companion object {
        private val lambda:
            @Composable context(LoadedComposeLifePreferencesHolder, ComposeLifePreferences) (
                modifier: Modifier,
            ) -> Unit =
            { modifier ->
                AlgorithmImplementationUi(modifier)
            }
    }
}

context(ctx: AlgorithmImplementationUiCtx)
@Composable
fun AlgorithmImplementationUi(
    modifier: Modifier = Modifier,
) = ctx(modifier)
// endregion templated-ctx

context(
    preferencesHolder: LoadedComposeLifePreferencesHolder,
composeLifePreferences: ComposeLifePreferences,
)
@Composable
private fun AlgorithmImplementationUi(
    modifier: Modifier = Modifier,
) {
    AlgorithmImplementationUi(
        algorithmChoice = preferencesHolder.preferences.algorithmChoice,
        setAlgorithmChoice = composeLifePreferences::setAlgorithmChoice,
        modifier = modifier,
    )
}

@Composable
fun AlgorithmImplementationUi(
    algorithmChoice: AlgorithmType,
    setAlgorithmChoice: suspend (AlgorithmType) -> Unit,
    modifier: Modifier = Modifier,
) {
    val coroutineScope = rememberCoroutineScope()

    TextFieldDropdown(
        label = parameterizedStringResource(Strings.AlgorithmImplementation),
        currentValue = when (algorithmChoice) {
            AlgorithmType.HashLifeAlgorithm -> AlgorithmImplementationDropdownOption.HashLifeAlgorithm
            AlgorithmType.NaiveAlgorithm -> AlgorithmImplementationDropdownOption.NaiveAlgorithm
        },
        allValues = AlgorithmImplementationDropdownOption._values.toImmutableList(),
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
        modifier = modifier,
    )
}

sealed interface AlgorithmImplementationDropdownOption : DropdownOption {
    data object HashLifeAlgorithm : AlgorithmImplementationDropdownOption {
        override val displayText: ParameterizedString = Strings.HashLifeAlgorithm
    }
    data object NaiveAlgorithm : AlgorithmImplementationDropdownOption {
        override val displayText: ParameterizedString = Strings.NaiveAlgorithm
    }

    @GenSealedEnum
    companion object
}

expect val AlgorithmImplementationDropdownOption.Companion._values: List<AlgorithmImplementationDropdownOption>
