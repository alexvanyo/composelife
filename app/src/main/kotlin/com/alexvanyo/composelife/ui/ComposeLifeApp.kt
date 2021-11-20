package com.alexvanyo.composelife.ui

import androidx.compose.material.MaterialTheme
import androidx.compose.material.Surface
import androidx.compose.runtime.Composable
import androidx.compose.runtime.SideEffect
import androidx.compose.ui.graphics.Color
import com.alexvanyo.composelife.data.NaiveGameOfLifeAlgorithm
import com.alexvanyo.composelife.data.model.toCellState
import com.alexvanyo.composelife.data.rememberTemporalGameOfLifeState
import com.alexvanyo.composelife.data.rememberTemporalGameOfLifeStateMutator
import com.alexvanyo.composelife.ui.theme.ComposeLifeTheme
import com.google.accompanist.insets.ProvideWindowInsets
import com.google.accompanist.systemuicontroller.rememberSystemUiController
import kotlinx.coroutines.Dispatchers

@Composable
fun ComposeLifeApp() {
    ComposeLifeTheme {
        ProvideWindowInsets {
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

            rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = NaiveGameOfLifeAlgorithm(Dispatchers.Default)
            )

            // A surface container using the 'background' color from the theme
            Surface(color = MaterialTheme.colors.background) {
                CellUniverse(
                    gameOfLifeState = temporalGameOfLifeState
                )
            }
        }
    }
}

private val gosperGliderGun = """
    |                        X
    |                      X X
    |            XX      XX            XX
    |           X   X    XX            XX
    |XX        X     X   XX
    |XX        X   X XX    X X
    |          X     X       X
    |           X   X
    |            XX
""".toCellState()
