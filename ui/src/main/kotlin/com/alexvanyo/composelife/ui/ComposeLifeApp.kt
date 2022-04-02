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

import androidx.compose.material3.Surface
import androidx.compose.runtime.Composable
import androidx.compose.runtime.SideEffect
import androidx.compose.ui.graphics.Color
import androidx.hilt.navigation.compose.hiltViewModel
import com.alexvanyo.composelife.model.rememberTemporalGameOfLifeState
import com.alexvanyo.composelife.model.rememberTemporalGameOfLifeStateMutator
import com.alexvanyo.composelife.model.toCellState
import com.alexvanyo.composelife.ui.entrypoints.ComposeLifeDispatchersEntryPoint
import com.alexvanyo.composelife.ui.entrypoints.GameOfLifeAlgorithmEntryPoint
import com.alexvanyo.composelife.ui.theme.ComposeLifeTheme
import com.google.accompanist.systemuicontroller.rememberSystemUiController

@Composable
fun ComposeLifeApp() {
    ComposeLifeTheme {
        val useDarkIcons = ComposeLifeTheme.isLight
        val systemUiController = rememberSystemUiController()

        SideEffect {
            systemUiController.setSystemBarsColor(
                color = Color.Transparent,
                darkIcons = useDarkIcons,
            )
        }

        val temporalGameOfLifeState = rememberTemporalGameOfLifeState(
            cellState = gosperGliderGun,
        )

        val gameOfLifeAlgorithm = hiltViewModel<GameOfLifeAlgorithmEntryPoint>().gameOfLifeAlgorithm
        val dispatchers = hiltViewModel<ComposeLifeDispatchersEntryPoint>().dispatchers

        rememberTemporalGameOfLifeStateMutator(
            temporalGameOfLifeState = temporalGameOfLifeState,
            gameOfLifeAlgorithm = gameOfLifeAlgorithm,
            dispatchers = dispatchers,
        )

        // A surface container using the 'background' color from the theme
        Surface {
            InteractiveCellUniverse(
                temporalGameOfLifeState = temporalGameOfLifeState,
            )
        }
    }
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
