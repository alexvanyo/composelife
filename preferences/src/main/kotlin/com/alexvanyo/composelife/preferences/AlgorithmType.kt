package com.alexvanyo.composelife.preferences

sealed interface AlgorithmType {
    object NaiveAlgorithm : AlgorithmType
    object HashLifeAlgorithm : AlgorithmType
}
