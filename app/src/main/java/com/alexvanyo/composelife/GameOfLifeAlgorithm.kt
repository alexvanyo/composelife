package com.alexvanyo.composelife

interface GameOfLifeAlgorithm {

    fun computeNextGeneration(
        cellState: Set<Pair<Int, Int>>,
    ): Set<Pair<Int, Int>>
}
