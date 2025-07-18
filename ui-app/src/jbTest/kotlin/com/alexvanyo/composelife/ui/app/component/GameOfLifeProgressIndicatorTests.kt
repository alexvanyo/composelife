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

package com.alexvanyo.composelife.ui.app.component

import androidx.compose.runtime.CompositionLocalProvider
import androidx.compose.ui.semantics.ProgressBarRangeInfo
import androidx.compose.ui.semantics.SemanticsProperties
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.SemanticsMatcher
import androidx.compose.ui.test.assert
import androidx.compose.ui.test.hasProgressBarRangeInfo
import androidx.lifecycle.Lifecycle
import androidx.lifecycle.LifecycleOwner
import androidx.lifecycle.LifecycleRegistry
import androidx.lifecycle.compose.LocalLifecycleOwner
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferences
import com.alexvanyo.composelife.scopes.UiComponent
import com.alexvanyo.composelife.test.BaseUiInjectTest
import com.alexvanyo.composelife.test.runUiTest
import com.alexvanyo.composelife.ui.app.TestComposeLifeApplicationComponent
import com.alexvanyo.composelife.ui.app.TestComposeLifeUiEntryPoint
import dev.zacsweers.metro.asContribution
import dev.zacsweers.metro.createGraphFactory
import kotlin.test.Test

@OptIn(ExperimentalTestApi::class)
class GameOfLifeProgressIndicatorTests : BaseUiInjectTest<TestComposeLifeApplicationComponent, UiComponent>(
    createGraphFactory<TestComposeLifeApplicationComponent.Factory>()::create,
    {  applicationComponent, uiComponentArguments ->
        applicationComponent.asContribution<UiComponent.Factory>().create(uiComponentArguments)
    },
) {
    private val gameOfLifeProgressIndicatorLocalEntryPoint = object : GameOfLifeProgressIndicatorLocalEntryPoint {
        override val preferences = LoadedComposeLifePreferences.Defaults
    }

    @Test
    fun progress_indicator_is_displayed_correctly() = runUiTest { uiComponent ->
        val gameOfLifeProgressIndicatorInjectEntryPoint: GameOfLifeProgressIndicatorInjectEntryPoint =
            uiComponent as TestComposeLifeUiEntryPoint

        setContent {
            CompositionLocalProvider(
                LocalLifecycleOwner provides object : LifecycleOwner {
                    override val lifecycle = LifecycleRegistry(this).apply {
                        currentState = Lifecycle.State.RESUMED
                    }
                }
            ) {
                with(gameOfLifeProgressIndicatorInjectEntryPoint) {
                    with(gameOfLifeProgressIndicatorLocalEntryPoint) {
                        GameOfLifeProgressIndicator()
                    }
                }
            }
        }

        onNode(SemanticsMatcher.keyIsDefined(SemanticsProperties.ProgressBarRangeInfo))
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo.Indeterminate))
    }
}
