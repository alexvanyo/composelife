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

package com.alexvanyo.composelife.ui

import androidx.compose.foundation.layout.BoxWithConstraints
import androidx.compose.material3.Surface
import androidx.compose.material3.windowsizeclass.ExperimentalMaterial3WindowSizeClassApi
import androidx.compose.material3.windowsizeclass.WindowSizeClass
import androidx.compose.runtime.Composable
import androidx.compose.ui.unit.DpSize
import com.alexvanyo.composelife.algorithm.GameOfLifeAlgorithm
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.model.rememberTemporalGameOfLifeState
import com.alexvanyo.composelife.model.rememberTemporalGameOfLifeStateMutator
import com.alexvanyo.composelife.model.toCellState
import com.alexvanyo.composelife.ui.theme.ComposeLifeTheme
import com.alexvanyo.composelife.ui.util.SizePreviews
import com.alexvanyo.composelife.ui.entrypoints.algorithm.inject as injectAlgorithm
import com.alexvanyo.composelife.ui.entrypoints.dispatchers.inject as injectDispatchers

@Composable
fun ComposeLifeApp(
    windowSizeClass: WindowSizeClass,
    gameOfLifeAlgorithm: GameOfLifeAlgorithm = injectAlgorithm(),
    dispatchers: ComposeLifeDispatchers = injectDispatchers(),
) {
    val temporalGameOfLifeState = rememberTemporalGameOfLifeState(
        cellState = gosperGliderGun,
        isRunning = false,
    )

    rememberTemporalGameOfLifeStateMutator(
        temporalGameOfLifeState = temporalGameOfLifeState,
        gameOfLifeAlgorithm = gameOfLifeAlgorithm,
        dispatchers = dispatchers,
    )

    InteractiveCellUniverse(
        temporalGameOfLifeState = temporalGameOfLifeState,
        windowSizeClass = windowSizeClass,
    )
}

private val gosperGliderGun = """
    |........................O...........
    |......................O.O...........
    |............OO......OO............OO
    |...........O...O....OO............OO
    |OO........O.....O...OO..............
    |OO........O...O.OO....O.O...........
    |..........O.....O.......O...........
    |...........O...O....................
    |............OO......................
""".toCellState()

@OptIn(ExperimentalMaterial3WindowSizeClassApi::class)
@SizePreviews
@Composable
fun InteractiveCellUniversePreview() {
    ComposeLifeTheme {
        BoxWithConstraints {
            val size = DpSize(maxWidth, maxHeight)
            Surface {
                InteractiveCellUniverse(
                    temporalGameOfLifeState = rememberTemporalGameOfLifeState(
                        cellState = gosperGliderGun,
                        isRunning = false,
                    ),
                    windowSizeClass = WindowSizeClass.calculateFromSize(size),
                )
            }
        }
    }
}
