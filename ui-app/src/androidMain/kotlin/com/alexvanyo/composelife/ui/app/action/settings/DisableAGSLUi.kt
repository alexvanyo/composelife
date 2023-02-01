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

import androidx.compose.runtime.Composable
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.ui.Modifier
import androidx.compose.ui.res.stringResource
import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.preferences.di.LoadedComposeLifePreferencesProvider
import com.alexvanyo.composelife.ui.app.R
import com.alexvanyo.composelife.ui.app.component.LabeledSwitch
import com.alexvanyo.composelife.ui.app.entrypoints.WithPreviewDependencies
import com.alexvanyo.composelife.ui.app.theme.ComposeLifeTheme
import com.alexvanyo.composelife.ui.util.ThemePreviews
import dagger.hilt.EntryPoint
import dagger.hilt.InstallIn
import dagger.hilt.android.components.ActivityComponent
import kotlinx.coroutines.launch

@EntryPoint
@InstallIn(ActivityComponent::class)
interface DisableAGSLUiHiltEntryPoint :
    ComposeLifePreferencesProvider

interface DisableAGSLUiLocalEntryPoint :
    LoadedComposeLifePreferencesProvider

context(DisableAGSLUiHiltEntryPoint, DisableAGSLUiLocalEntryPoint)
@Composable
fun DisableAGSLUi(
    modifier: Modifier = Modifier,
) {
    DisableAGSLUi(
        disableAGSL = preferences.disableAGSL,
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
        label = stringResource(R.string.disable_agsl),
        checked = disableAGSL,
        onCheckedChange = { disabled ->
            coroutineScope.launch {
                setDisableAGSL(disabled)
            }
        },
        modifier = modifier,
    )
}

@ThemePreviews
@Composable
fun DisableAGSLUiDisabledPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            DisableAGSLUi(
                disableAGSL = true,
                setDisableAGSL = {},
            )
        }
    }
}

@ThemePreviews
@Composable
fun DisableAGSLUiEnabledPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            DisableAGSLUi(
                disableAGSL = false,
                setDisableAGSL = {},
            )
        }
    }
}
