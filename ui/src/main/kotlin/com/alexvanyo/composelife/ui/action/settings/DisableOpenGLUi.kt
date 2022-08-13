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
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.Row
import androidx.compose.material3.Switch
import androidx.compose.material3.Text
import androidx.compose.runtime.Composable
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.res.stringResource
import androidx.compose.ui.tooling.preview.Preview
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.resourcestate.ResourceState
import com.alexvanyo.composelife.ui.R
import com.alexvanyo.composelife.ui.component.GameOfLifeProgressIndicator
import com.alexvanyo.composelife.ui.component.GameOfLifeProgressIndicatorEntryPoint
import com.alexvanyo.composelife.ui.entrypoints.WithPreviewDependencies
import com.alexvanyo.composelife.ui.theme.ComposeLifeTheme
import dagger.hilt.EntryPoint
import dagger.hilt.InstallIn
import dagger.hilt.android.components.ActivityComponent
import kotlinx.coroutines.launch

@EntryPoint
@InstallIn(ActivityComponent::class)
interface DisableOpenGLUiEntryPoint :
    ComposeLifePreferencesProvider,
    GameOfLifeProgressIndicatorEntryPoint

context(DisableOpenGLUiEntryPoint)
@Composable
fun DisableOpenGLUi(
    modifier: Modifier = Modifier,
) {
    DisableOpenGLUi(
        disableOpenGLState = composeLifePreferences.disableOpenGLState,
        setDisableOpenGL = composeLifePreferences::setDisableOpenGL,
        modifier = modifier,
    )
}

context(GameOfLifeProgressIndicatorEntryPoint)
@Composable
fun DisableOpenGLUi(
    disableOpenGLState: ResourceState<Boolean>,
    setDisableOpenGL: suspend (Boolean) -> Unit,
    modifier: Modifier = Modifier,
) {
    Box(modifier = modifier) {
        when (disableOpenGLState) {
            ResourceState.Loading, is ResourceState.Failure -> {
                GameOfLifeProgressIndicator()
            }

            is ResourceState.Success -> {
                val coroutineScope = rememberCoroutineScope()
                Row(
                    horizontalArrangement = Arrangement.spacedBy(16.dp),
                    verticalAlignment = Alignment.CenterVertically,
                ) {
                    Text(
                        stringResource(R.string.disable_opengl),
                        modifier = Modifier.weight(1f),
                    )

                    Switch(
                        checked = disableOpenGLState.value,
                        onCheckedChange = { disabled ->
                            coroutineScope.launch {
                                setDisableOpenGL(disabled)
                            }
                        },
                    )
                }
            }
        }
    }
}

@Preview
@Composable
fun DisableOpenGLUiLoadingPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            DisableOpenGLUi(
                disableOpenGLState = ResourceState.Loading,
                setDisableOpenGL = {},
            )
        }
    }
}

@Preview
@Composable
fun DisableOpenGLUiDisabledPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            DisableOpenGLUi(
                disableOpenGLState = ResourceState.Success(true),
                setDisableOpenGL = {},
            )
        }
    }
}

@Preview
@Composable
fun DisableOpenGLUiEnabledPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            DisableOpenGLUi(
                disableOpenGLState = ResourceState.Success(false),
                setDisableOpenGL = {},
            )
        }
    }
}
