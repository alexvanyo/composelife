package com.alexvanyo.composelife

import android.os.Bundle
import androidx.activity.ComponentActivity
import androidx.activity.compose.setContent
import androidx.compose.material.MaterialTheme
import androidx.compose.material.Surface
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.remember
import com.alexvanyo.composelife.ui.theme.ComposeLifeTheme
import kotlinx.coroutines.delay

class MainActivity : ComponentActivity() {
    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        setContent {
            ComposeLifeTheme {
                val gameOfLifeState = remember {
                    MutableGameOfLifeStateImpl(
                        cellState = gosperGliderGun
                    )
                }

                LaunchedEffect(gameOfLifeState) {
                    while (true) {
                        delay(1000)
                        gameOfLifeState.cellState =
                            NaiveGameOfLifeAlgorithm.computeNextGeneration(gameOfLifeState.cellState)
                    }
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
}

val gosperGliderGun = setOf(
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
