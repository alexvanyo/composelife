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
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResource
import com.alexvanyo.composelife.preferences.ComposeLifePreferences
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferencesHolder
import com.alexvanyo.composelife.preferences.setDisabledAGSL
import com.alexvanyo.composelife.ui.mobile.component.LabeledSwitch
import com.alexvanyo.composelife.ui.settings.resources.DisableAGSL
import com.alexvanyo.composelife.ui.settings.resources.Strings
import dev.zacsweers.metro.Inject
import kotlinx.coroutines.launch

@Immutable
@Inject
class DisableAGSLUiEntryPoint(
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
                DisableAGSLUi(modifier)
            }
    }
}

context(entryPoint: DisableAGSLUiEntryPoint)
@Composable
fun DisableAGSLUi(
    modifier: Modifier = Modifier,
) = entryPoint(modifier)

context(
    preferencesHolder: LoadedComposeLifePreferencesHolder,
composeLifePreferences: ComposeLifePreferences,
)
@Composable
private fun DisableAGSLUi(
    modifier: Modifier = Modifier,
) {
    DisableAGSLUi(
        disableAGSL = preferencesHolder.preferences.disableAGSL,
        setDisableAGSL = composeLifePreferences::setDisabledAGSL,
        modifier = modifier,
    )
}

@Composable
fun DisableAGSLUi(
    disableAGSL: Boolean,
    setDisableAGSL: suspend (Boolean) -> Unit,
    modifier: Modifier = Modifier,
) {
    val coroutineScope = rememberCoroutineScope()
    LabeledSwitch(
        label = parameterizedStringResource(Strings.DisableAGSL),
        checked = disableAGSL,
        onCheckedChange = { disabled ->
            coroutineScope.launch {
                setDisableAGSL(disabled)
            }
        },
        modifier = modifier,
    )
}
