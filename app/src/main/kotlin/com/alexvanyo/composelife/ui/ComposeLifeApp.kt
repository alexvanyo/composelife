package com.alexvanyo.composelife.ui

import androidx.compose.material.MaterialTheme
import androidx.compose.material.Surface
import androidx.compose.runtime.Composable
import androidx.compose.runtime.SideEffect
import androidx.compose.ui.graphics.Color
import androidx.hilt.navigation.compose.hiltViewModel
import androidx.lifecycle.ViewModel
import com.alexvanyo.composelife.algorithm.GameOfLifeAlgorithm
import com.alexvanyo.composelife.model.rememberTemporalGameOfLifeState
import com.alexvanyo.composelife.model.rememberTemporalGameOfLifeStateMutator
import com.alexvanyo.composelife.model.toCellState
import com.alexvanyo.composelife.ui.theme.ComposeLifeTheme
import com.google.accompanist.systemuicontroller.rememberSystemUiController
import dagger.hilt.android.lifecycle.HiltViewModel
import javax.inject.Inject

@Composable
fun ComposeLifeApp() {
    ComposeLifeTheme {
        val useDarkIcons = MaterialTheme.colors.isLight
        val systemUiController = rememberSystemUiController()

        SideEffect {
            systemUiController.setSystemBarsColor(
                color = Color.Transparent,
                darkIcons = useDarkIcons
            )
        }

        val temporalGameOfLifeState = rememberTemporalGameOfLifeState(
            cellState = gosperGliderGun
        )

        val viewModel = hiltViewModel<ComposeLifeAppViewModel>()

        rememberTemporalGameOfLifeStateMutator(
            temporalGameOfLifeState = temporalGameOfLifeState,
            gameOfLifeAlgorithm = viewModel.gameOfLifeAlgorithm
        )

        // A surface container using the 'background' color from the theme
        Surface(color = MaterialTheme.colors.background) {
            InteractiveCellUniverse(
                temporalGameOfLifeState = temporalGameOfLifeState
            )
        }
    }
}

@HiltViewModel
class ComposeLifeAppViewModel @Inject constructor(
    val gameOfLifeAlgorithm: GameOfLifeAlgorithm
) : ViewModel()

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
