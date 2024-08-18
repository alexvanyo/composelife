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

package com.alexvanyo.composelife

import androidx.compose.material3.windowsizeclass.ExperimentalMaterial3WindowSizeClassApi
import androidx.compose.material3.windowsizeclass.calculateWindowSizeClass
import androidx.compose.runtime.CompositionLocalProvider
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.ui.window.Window
import androidx.compose.ui.window.application
import androidx.compose.ui.window.rememberWindowState
import com.alexvanyo.composelife.ui.app.ComposeLifeApp
import com.alexvanyo.composelife.ui.mobile.ComposeLifeTheme
import com.alexvanyo.composelife.ui.mobile.shouldUseDarkTheme
import com.slack.circuit.retained.LocalRetainedStateRegistry
import com.slack.circuit.retained.continuityRetainedStateRegistry
import kotlinx.coroutines.launch
import kotlinx.coroutines.supervisorScope

fun main() = application {
    val applicationComponent = ComposeLifeApplicationComponent::class.create()

    val updatables = applicationComponent.updatables

    LaunchedEffect(Unit) {
        supervisorScope {
            updatables.forEach { updatable ->
                launch {
                    updatable.update()
                }
            }
        }
    }

    val windowState = rememberWindowState()

    Window(
        onCloseRequest = ::exitApplication,
        title = "ComposeLife",
        state = windowState,
    ) {
        CompositionLocalProvider(LocalRetainedStateRegistry provides continuityRetainedStateRegistry()) {
            val uiComponent = ComposeLifeUiComponent::class.create(applicationComponent)
            val mainInjectEntryPoint = uiComponent.entryPoint as MainInjectEntryPoint

            with(mainInjectEntryPoint) {
                ComposeLifeTheme(shouldUseDarkTheme()) {
                    @OptIn(ExperimentalMaterial3WindowSizeClassApi::class)
                    ComposeLifeApp(calculateWindowSizeClass())
                }
            }
        }
    }
}
