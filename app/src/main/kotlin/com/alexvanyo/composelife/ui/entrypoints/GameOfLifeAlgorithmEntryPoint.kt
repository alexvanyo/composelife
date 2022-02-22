package com.alexvanyo.composelife.ui.entrypoints

import androidx.lifecycle.ViewModel
import com.alexvanyo.composelife.algorithm.GameOfLifeAlgorithm
import dagger.hilt.android.lifecycle.HiltViewModel
import javax.inject.Inject

@HiltViewModel
class GameOfLifeAlgorithmEntryPoint @Inject constructor(
    val gameOfLifeAlgorithm: GameOfLifeAlgorithm,
) : ViewModel()
