package com.alexvanyo.composelife.patterns

import com.alexvanyo.composelife.model.emptyCellState
import com.alexvanyo.composelife.model.toCellState

object SingleCellPattern : GameOfLifeTestPattern(
    patternName = "Single cell",
    """
    |O
    """.toCellState(),
    List(50) { emptyCellState() }
)

object SixLongLinePattern : GameOfLifeTestPattern(
    patternName = "Six long line",
    """
    |........
    |........
    |..OOOOOO
    |........
    |........
    """.toCellState(),
    listOf(
        """
        |.......
        |...OOOO
        |...OOOO
        |...OOOO
        |.......
        """.toCellState(),
        """
        |....OO..
        |...O..O.
        |..O....O
        |...O..O.
        |....OO..
        """.toCellState(),
        """
        |....OO..
        |...OOOO.
        |..OO..OO
        |...OOOO.
        |....OO..
        """.toCellState(),
        """
        |...O..O.
        |..O....O
        |..O....O
        |..O....O
        |...O..O.
        """.toCellState(),
        """
        |.........
        |..OO..OO.
        |.OOO..OOO
        |..OO..OO.
        |.........
        """.toCellState(),
        """
        |.........
        |.O.O..O.O
        |.O..OO..O
        |.O.O..O.O
        |.........
        """.toCellState(),
        """
        |..........
        |..O.OO.O..
        |OO.OOOO.OO
        |..O.OO.O..
        |..........
        """.toCellState(),
        """
        |.........
        |.OO....OO
        |.O......O
        |.OO....OO
        |.........
        """.toCellState(),
        """
        |..........
        |.OO....OO.
        |O........O
        |.OO....OO.
        |..........
        """.toCellState(),
        """
        |..........
        |.O......O.
        |O........O
        |.O......O.
        |..........
        """.toCellState(),
        """
        |..........
        |..........
        |OO......OO
        |..........
        |..........
        """.toCellState()
    ) + List(50) { emptyCellState() }
)
