package com.alexvanyo.composelife.patterns

import com.alexvanyo.composelife.model.toCellState

object BlinkerPattern : GameOfLifeTestPattern(
    patternName = "Blinker",
    """
    |
    |XXX
    |
    """.toCellState(),
    List(50) {
        if (it.rem(2) == 0) {
            """
            | X
            | X
            | X
            """.toCellState()
        } else {
            """
            |
            |XXX
            |
            """.toCellState()
        }
    }
)

object ToadPattern : GameOfLifeTestPattern(
    patternName = "Toad",
    """
    | XX
    |X
    |   X
    | XX
    """.toCellState(),
    List(50) {
        if (it.rem(2) == 0) {
            """
            | X
            | XX
            | XX
            |  X
            """.toCellState()
        } else {
            """
            | XX
            |X
            |   X
            | XX
            """.toCellState()
        }
    }
)

object BeaconPattern : GameOfLifeTestPattern(
    patternName = "Beacon",
    """
    |XX
    |X
    |   X
    |  XX
    """.toCellState(),
    List(50) {
        if (it.rem(2) == 0) {
            """
            |XX
            |XX
            |  XX
            |  XX
            """.toCellState()
        } else {
            """
            |XX
            |X
            |   X
            |  XX
            """.toCellState()
        }
    }
)
