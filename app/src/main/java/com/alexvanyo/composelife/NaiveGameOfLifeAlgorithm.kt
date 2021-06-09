package com.alexvanyo.composelife

object NaiveGameOfLifeAlgorithm : GameOfLifeAlgorithm {
    override fun computeNextGeneration(cellState: Set<Pair<Int, Int>>): Set<Pair<Int, Int>> {
        val xCoordinates = cellState.map { it.first }
        val yCoordinates = cellState.map { it.second }
        val minX = xCoordinates.minOrNull() ?: 0
        val maxX = xCoordinates.maxOrNull() ?: 0
        val minY = yCoordinates.minOrNull() ?: 0
        val maxY = yCoordinates.maxOrNull() ?: 0

        val outputState = mutableSetOf<Pair<Int, Int>>()

        (minX - 1..maxX + 1).forEach { x ->
            (minY - 1..maxY + 1).forEach { y ->
                val cell = x to y
                val neighborCount = cellState.intersect(getNeighbors(x, y)).count()

                if (neighborCount == 3 || (neighborCount == 2 && cell in cellState)) {
                    outputState.add(cell)
                }
            }
        }

        return outputState
    }
}

private fun getNeighbors(x: Int, y: Int): List<Pair<Int, Int>> = listOf(
    x - 1 to y - 1,
    x to y - 1,
    x + 1 to y - 1,
    x - 1 to y,
    x + 1 to y,
    x - 1 to y + 1,
    x to y + 1,
    x + 1 to y + 1
)
