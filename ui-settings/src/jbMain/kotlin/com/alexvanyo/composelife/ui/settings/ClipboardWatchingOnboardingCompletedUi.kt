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
@file:Suppress("MatchingDeclarationName")

package com.alexvanyo.composelife.ui.settings

import androidx.compose.runtime.Composable
import androidx.compose.runtime.Immutable
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.ui.Modifier
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResource
import com.alexvanyo.composelife.preferences.ComposeLifePreferences
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferences
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferencesHolder
import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.preferences.di.LoadedComposeLifePreferencesProvider
import com.alexvanyo.composelife.preferences.setCompletedClipboardWatchingOnboarding
import com.alexvanyo.composelife.ui.mobile.component.LabeledSwitch
import com.alexvanyo.composelife.ui.settings.resources.ClipboardWatchingOnboardingCompleted
import com.alexvanyo.composelife.ui.settings.resources.Strings
import dev.zacsweers.metro.Inject
import kotlinx.coroutines.launch

@Immutable
@Inject
class ClipboardWatchingOnboardingCompletedUiEntryPoint(
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
                ClipboardWatchingOnboardingCompletedUi(modifier)
            }
    }
}

context(entryPoint: ClipboardWatchingOnboardingCompletedUiEntryPoint)
@Composable
fun ClipboardWatchingOnboardingCompletedUi(
    modifier: Modifier = Modifier,
) = entryPoint(modifier)

context(
    preferencesHolder: LoadedComposeLifePreferencesHolder,
composeLifePreferences: ComposeLifePreferences,
)
@Composable
private fun ClipboardWatchingOnboardingCompletedUi(
    modifier: Modifier = Modifier,
) {
    ClipboardWatchingOnboardingCompletedUi(
        completedClipboardWatchingOnboarding = preferencesHolder.preferences.completedClipboardWatchingOnboarding,
        setCompletedClipboardWatchingOnboarding =
        composeLifePreferences::setCompletedClipboardWatchingOnboarding,
        modifier = modifier,
    )
}

@Composable
fun ClipboardWatchingOnboardingCompletedUi(
    completedClipboardWatchingOnboarding: Boolean,
    setCompletedClipboardWatchingOnboarding: suspend (Boolean) -> Unit,
    modifier: Modifier = Modifier,
) {
    val coroutineScope = rememberCoroutineScope()
    LabeledSwitch(
        label = parameterizedStringResource(Strings.ClipboardWatchingOnboardingCompleted),
        checked = completedClipboardWatchingOnboarding,
        onCheckedChange = { disabled ->
            coroutineScope.launch {
                setCompletedClipboardWatchingOnboarding(disabled)
            }
        },
        modifier = modifier,
    )
}
