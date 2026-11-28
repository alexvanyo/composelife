/*
 * Copyright 2026 The Android Open Source Project
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

package com.alexvanyo.composelife.ui.app

import androidx.compose.foundation.layout.size
import androidx.compose.material3.adaptive.currentWindowAdaptiveInfoV2
import androidx.compose.runtime.CompositionLocalProvider
import androidx.compose.runtime.remember
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.onNodeWithContentDescription
import androidx.compose.ui.test.performClick
import androidx.compose.ui.unit.dp
import androidx.navigationevent.NavigationEventDispatcher
import androidx.navigationevent.NavigationEventDispatcherOwner
import androidx.navigationevent.compose.LocalNavigationEventDispatcherOwner
import com.alexvanyo.composelife.model.CellStateParser
import com.alexvanyo.composelife.model.rememberTemporalGameOfLifeState
import com.alexvanyo.composelife.model.toCellState
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResolver
import com.alexvanyo.composelife.preferences.TestComposeLifePreferences
import com.alexvanyo.composelife.scopes.ApplicationGraph
import com.alexvanyo.composelife.scopes.UiGraph
import com.alexvanyo.composelife.scopes.UiScope
import com.alexvanyo.composelife.test.BaseUiInjectTest
import com.alexvanyo.composelife.test.runUiTest
import com.alexvanyo.composelife.ui.app.resources.DisableAutofit
import com.alexvanyo.composelife.ui.app.resources.EnableAutofit
import com.alexvanyo.composelife.ui.app.resources.Strings
import com.alexvanyo.composelife.ui.cells.MutableCellWindowViewportState
import com.alexvanyo.composelife.ui.cells.offset
import com.alexvanyo.composelife.ui.cells.scale
import com.alexvanyo.composelife.ui.util.ClipboardReaderWriter
import com.alexvanyo.composelife.ui.util.FullscreenModeManager
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.asContribution
import kotlin.test.Test
import kotlin.test.assertEquals

@ContributesTo(UiScope::class)
interface InteractiveCellUniverseAutofitTestsUiCtx {
    val interactiveCellUniverse: InteractiveCellUniverse
    val cellStateParser: CellStateParser
    val clipboardReaderWriter: ClipboardReaderWriter
    val fullscreenModeManager: FullscreenModeManager
    val testComposeLifePreferences: TestComposeLifePreferences
}

val UiGraph.interactiveCellUniverseAutofitTestsUiCtx: InteractiveCellUniverseAutofitTestsUiCtx get() =
    this as InteractiveCellUniverseAutofitTestsUiCtx

@OptIn(ExperimentalTestApi::class)
class InteractiveCellUniverseAutofitTests :
    BaseUiInjectTest(
        { globalGraph.asContribution<ApplicationGraph.Factory>().create(it) },
    ) {

    @Suppress("LongMethod")
    @Test
    fun autofit_updates_viewport_to_fit_pattern() = runUiTest { uiGraph ->
        val uiCtx = uiGraph.interactiveCellUniverseAutofitTestsUiCtx
        uiCtx.testComposeLifePreferences.disableAGSL = true
        val mutableCellWindowViewportState = MutableCellWindowViewportState(
            offset = Offset.Zero,
            scale = 1f,
        )

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()

            val navigationEventDispatcherOwner = remember {
                object : NavigationEventDispatcherOwner {
                    override val navigationEventDispatcher = NavigationEventDispatcher(
                        onBackCompletedFallback = {},
                    )
                }
            }

            CompositionLocalProvider(
                LocalNavigationEventDispatcherOwner provides navigationEventDispatcherOwner,
            ) {
                val temporalGameOfLifeState = rememberTemporalGameOfLifeState(
                    seedCellState = setOf(
                        10 to 10,
                        14 to 14,
                    ).toCellState(),
                    isRunning = false,
                )

                context(
                    uiCtx.interactiveCellUniverse,
                    uiCtx.cellStateParser,
                    uiCtx.clipboardReaderWriter,
                    uiCtx.fullscreenModeManager,
                ) {
                    val interactiveCellUniverseState = rememberInteractiveCellUniverseState(
                        temporalGameOfLifeState = temporalGameOfLifeState,
                        mutableCellWindowViewportState = mutableCellWindowViewportState,
                    )

                    InteractiveCellUniverse(
                        temporalGameOfLifeState = temporalGameOfLifeState,
                        windowSizeClass = currentWindowAdaptiveInfoV2().windowSizeClass,
                        onSeeMoreSettingsClicked = {},
                        onOpenInSettingsClicked = {},
                        onViewDeserializationInfo = {},
                        modifier = Modifier.size(300.dp, 300.dp),
                        interactiveCellUniverseState = interactiveCellUniverseState,
                    )
                }
            }
        }

        onNodeWithContentDescription(resolver(Strings.EnableAutofit))
            .performClick()

        waitForIdle()

        onNodeWithContentDescription(resolver(Strings.DisableAutofit))
            .assertExists()

        assertEquals(12.0f, mutableCellWindowViewportState.offset.x, absoluteTolerance = 0.05f)
        assertEquals(12.0f, mutableCellWindowViewportState.offset.y, absoluteTolerance = 0.05f)
        assertEquals(6.25f / 9f, mutableCellWindowViewportState.scale, absoluteTolerance = 0.05f)
    }
}
