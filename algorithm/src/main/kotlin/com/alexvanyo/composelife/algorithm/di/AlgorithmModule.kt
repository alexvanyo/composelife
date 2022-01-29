package com.alexvanyo.composelife.algorithm.di

import com.alexvanyo.composelife.algorithm.GameOfLifeAlgorithm
import com.alexvanyo.composelife.algorithm.HashLifeAlgorithm
import dagger.Binds
import dagger.Module
import dagger.hilt.InstallIn
import dagger.hilt.components.SingletonComponent

@Module
@InstallIn(SingletonComponent::class)
interface AlgorithmModule {

    @Binds
    fun bindsGameOfLifeAlgorithm(hashLifeAlgorithm: HashLifeAlgorithm): GameOfLifeAlgorithm
}
