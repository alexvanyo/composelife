package com.alexvanyo.composelife.patterns

import com.alexvanyo.composelife.model.toCellState

object BlinkerPattern : GameOfLifeTestPattern(
    patternName = "Blinker",
    """
    |...
    |OOO
    |...
    """.toCellState(),
    List(50) {
        if (it.rem(2) == 0) {
            """
            |.O.
            |.O.
            |.O.
            """.toCellState()
        } else {
            """
            |...
            |OOO
            |...
            """.toCellState()
        }
    }
)

object ToadPattern : GameOfLifeTestPattern(
    patternName = "Toad",
    """
    |.OO.
    |O...
    |...O
    |.OO.
    """.toCellState(),
    List(50) {
        if (it.rem(2) == 0) {
            """
            |.O..
            |.OO.
            |.OO.
            |..O.
            """.toCellState()
        } else {
            """
            |.OO.
            |O...
            |...O
            |.OO.
            """.toCellState()
        }
    }
)

object BeaconPattern : GameOfLifeTestPattern(
    patternName = "Beacon",
    """
    |OO..
    |O...
    |...O
    |..OO
    """.toCellState(),
    List(50) {
        if (it.rem(2) == 0) {
            """
            |OO..
            |OO..
            |..OO
            |..OO
            """.toCellState()
        } else {
            """
            |OO..
            |O...
            |...O
            |..OO
            """.toCellState()
        }
    }
)
