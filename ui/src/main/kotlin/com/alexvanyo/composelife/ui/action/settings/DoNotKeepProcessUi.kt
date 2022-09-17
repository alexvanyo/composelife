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

package com.alexvanyo.composelife.ui.action.settings

import androidx.compose.foundation.layout.Arrangement
import androidx.compose.foundation.layout.Row
import androidx.compose.material3.Switch
import androidx.compose.material3.Text
import androidx.compose.runtime.Composable
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.res.stringResource
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.preferences.di.LoadedComposeLifePreferencesProvider
import com.alexvanyo.composelife.ui.R
import com.alexvanyo.composelife.ui.entrypoints.WithPreviewDependencies
import com.alexvanyo.composelife.ui.theme.ComposeLifeTheme
import com.alexvanyo.composelife.ui.util.ThemePreviews
import dagger.hilt.EntryPoint
import dagger.hilt.InstallIn
import dagger.hilt.android.components.ActivityComponent
import kotlinx.coroutines.launch

@EntryPoint
@InstallIn(ActivityComponent::class)
interface DoNotKeepProcessUiHiltEntryPoint :
    ComposeLifePreferencesProvider

interface DoNotKeepProcessUiLocalEntryPoint :
    LoadedComposeLifePreferencesProvider

context(DoNotKeepProcessUiHiltEntryPoint, DoNotKeepProcessUiLocalEntryPoint)
@Composable
fun DoNotKeepProcessUi(
    modifier: Modifier = Modifier,
) {
    DoNotKeepProcessUi(
        doNotKeepProcess = preferences.doNotKeepProcess,
        setDoNotKeepProcess = composeLifePreferences::setDoNotKeepProcess,
        modifier = modifier,
    )
}

@Composable
fun DoNotKeepProcessUi(
    doNotKeepProcess: Boolean,
    setDoNotKeepProcess: suspend (Boolean) -> Unit,
    modifier: Modifier = Modifier,
) {
    val coroutineScope = rememberCoroutineScope()
    Row(
        horizontalArrangement = Arrangement.spacedBy(16.dp),
        verticalAlignment = Alignment.CenterVertically,
        modifier = modifier,
    ) {
        Text(
            stringResource(R.string.do_not_keep_process),
            modifier = Modifier.weight(1f),
        )

        Switch(
            checked = doNotKeepProcess,
            onCheckedChange = { disabled ->
                coroutineScope.launch {
                    setDoNotKeepProcess(disabled)
                }
            },
        )
    }
}

@ThemePreviews
@Composable
fun DoNotKeepProcessUiDisabledPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            DoNotKeepProcessUi(
                doNotKeepProcess = true,
                setDoNotKeepProcess = {},
            )
        }
    }
}

@ThemePreviews
@Composable
fun DoNotKeepProcessUiEnabledPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            DoNotKeepProcessUi(
                doNotKeepProcess = false,
                setDoNotKeepProcess = {},
            )
        }
    }
}
