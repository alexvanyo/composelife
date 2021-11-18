package com.alexvanyo.composelife.data

import com.alexvanyo.composelife.data.model.emptyCellState
import com.alexvanyo.composelife.data.model.toCellState

object SingleCellPattern : GameOfLifeTestPattern(
    patternName = "Single cell",
    """
    |🟨
    """.toCellState(),
    List(50) { emptyCellState() }
)

object SixLongLinePattern : GameOfLifeTestPattern(
    patternName = "Six long line",
    """
    |
    |
    |  XXXXXX
    |
    |
    """.toCellState(),
    listOf(
        """
        |
        |   XXXX
        |   XXXX
        |   XXXX
        |
        """.toCellState(),
        """
        |    XX
        |   X  X
        |  X    X
        |   X  X
        |    XX
        """.toCellState(),
        """
        |    XX
        |   XXXX
        |  XX  XX
        |   XXXX
        |    XX
        """.toCellState(),
        """
        |   X  X
        |  X    X
        |  X    X
        |  X    X
        |   X  X
        """.toCellState(),
        """
        |
        |  XX  XX
        | XXX  XXX
        |  XX  XX
        |
        """.toCellState(),
        """
        |
        | X X  X X
        | X  XX  X
        | X X  X X
        |
        """.toCellState(),
        """
        |
        |  X XX X
        |XX XXXX XX
        |  X XX X
        |
        """.toCellState(),
        """
        |
        | XX    XX
        | X      X
        | XX    XX
        |
        """.toCellState(),
        """
        |
        | XX    XX
        |X        X
        | XX    XX
        |
        """.toCellState(),
        """
        |
        | X      X
        |X        X
        | X      X
        |
        """.toCellState(),
        """
        |
        |
        |XX      XX
        |
        |
        """.toCellState()
    ) + List(50) { emptyCellState() }
)
