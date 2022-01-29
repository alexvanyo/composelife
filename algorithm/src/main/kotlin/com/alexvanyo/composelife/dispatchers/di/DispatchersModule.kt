package com.alexvanyo.composelife.dispatchers.di

import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.dispatchers.DefaultComposeLifeDispatchers
import dagger.Binds
import dagger.Module
import dagger.hilt.InstallIn
import dagger.hilt.components.SingletonComponent

@Module
@InstallIn(SingletonComponent::class)
interface DispatchersModule {

    @Binds
    fun bindsDispatchers(defaultComposeLifeDispatchers: DefaultComposeLifeDispatchers): ComposeLifeDispatchers
}
