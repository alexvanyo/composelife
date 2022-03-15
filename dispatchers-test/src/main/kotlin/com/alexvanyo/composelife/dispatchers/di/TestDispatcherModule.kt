package com.alexvanyo.composelife.dispatchers.di

import dagger.Module
import dagger.Provides
import dagger.hilt.InstallIn
import dagger.hilt.components.SingletonComponent
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.test.StandardTestDispatcher
import kotlinx.coroutines.test.TestDispatcher
import javax.inject.Singleton

@Module
@InstallIn(SingletonComponent::class)
@OptIn(ExperimentalCoroutinesApi::class)
interface TestDispatcherModule {
    companion object {
        @Provides
        @Singleton
        fun providesTestDispatcher(): TestDispatcher = StandardTestDispatcher()
    }
}
