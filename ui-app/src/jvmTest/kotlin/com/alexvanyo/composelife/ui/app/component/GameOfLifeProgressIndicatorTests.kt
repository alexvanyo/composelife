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

import androidx.compose.ui.semantics.ProgressBarRangeInfo
import androidx.compose.ui.semantics.SemanticsProperties
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.SemanticsMatcher
import androidx.compose.ui.test.assert
import androidx.compose.ui.test.hasProgressBarRangeInfo
import com.alexvanyo.composelife.scopes.UiGraph
import com.alexvanyo.composelife.scopes.UiGraphArguments
import com.alexvanyo.composelife.scopes.UiScope
import com.alexvanyo.composelife.test.BaseUiInjectTest
import com.alexvanyo.composelife.test.BaseUiInjectTestCtx
import com.alexvanyo.composelife.test.runUiTest
import com.alexvanyo.composelife.ui.app.TestApplicationGraph
import com.alexvanyo.composelife.ui.app.createTestApplicationGraph
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.GraphExtension
import dev.zacsweers.metro.Provides
import dev.zacsweers.metro.asContribution
import kotlin.test.Test

@GraphExtension(UiScope::class)
interface GameOfLifeProgressIndicatorTestsUiGraph :
    UiGraph,
    BaseUiInjectTestCtx {
    val gameOfLifeProgressIndicatorCtx: GameOfLifeProgressIndicator

    @ContributesTo(AppScope::class)
    @GraphExtension.Factory
    fun interface Factory {
        fun createGameOfLifeProgressIndicatorTestsUiGraph(
            @Provides uiGraphArguments: UiGraphArguments,
        ): GameOfLifeProgressIndicatorTestsUiGraph
    }
}

@OptIn(ExperimentalTestApi::class)
class GameOfLifeProgressIndicatorTests :
    BaseUiInjectTest<TestApplicationGraph, GameOfLifeProgressIndicatorTestsUiGraph>(
        applicationGraphCreator = ::createTestApplicationGraph,
        uiGraphCreator = {
            asContribution<GameOfLifeProgressIndicatorTestsUiGraph.Factory>()
                .createGameOfLifeProgressIndicatorTestsUiGraph(it)
        },
    ) {

    @Test
    fun progress_indicator_is_displayed_correctly() = runUiTest { uiGraph ->
        val ctx = uiGraph

        setContent {
            context(ctx.gameOfLifeProgressIndicatorCtx) {
                GameOfLifeProgressIndicator()
            }
        }

        onNode(SemanticsMatcher.keyIsDefined(SemanticsProperties.ProgressBarRangeInfo))
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo.Indeterminate))
    }
}
