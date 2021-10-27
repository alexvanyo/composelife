package com.alexvanyo.composelife.ui

import androidx.compose.material.MaterialTheme
import androidx.compose.material.Surface
import androidx.compose.runtime.Composable
import androidx.compose.runtime.SideEffect
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.ui.graphics.Color
import com.alexvanyo.composelife.data.NaiveGameOfLifeAlgorithm
import com.alexvanyo.composelife.data.TemporalGameOfLifeState
import com.alexvanyo.composelife.data.model.toCellState
import com.alexvanyo.composelife.ui.theme.ComposeLifeTheme
import com.google.accompanist.insets.ProvideWindowInsets
import com.google.accompanist.systemuicontroller.rememberSystemUiController

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

            val coroutineScope = rememberCoroutineScope()

            val gameOfLifeState = remember(coroutineScope) {
                TemporalGameOfLifeState(
                    coroutineScope = coroutineScope,
                    gameOfLifeAlgorithm = NaiveGameOfLifeAlgorithm,
                    cellState = gosperGliderGun.toCellState(),
                    generationsPerStep = 10,
                )
            }

            // A surface container using the 'background' color from the theme
            Surface(color = MaterialTheme.colors.background) {
                CellUniverse(
                    gameOfLifeState = gameOfLifeState
                )
            }
        }
    }
}

private val gosperGliderGun = setOf(
    25 to 1,
    23 to 2,
    25 to 2,
    13 to 3,
    14 to 3,
    21 to 3,
    22 to 3,
    35 to 3,
    36 to 3,
    12 to 4,
    16 to 4,
    21 to 4,
    22 to 4,
    35 to 4,
    36 to 4,
    1 to 5,
    2 to 5,
    11 to 5,
    17 to 5,
    21 to 5,
    22 to 5,
    1 to 6,
    2 to 6,
    11 to 6,
    15 to 6,
    17 to 6,
    18 to 6,
    23 to 6,
    25 to 6,
    11 to 7,
    17 to 7,
    25 to 7,
    12 to 8,
    16 to 8,
    13 to 9,
    14 to 9,
)

