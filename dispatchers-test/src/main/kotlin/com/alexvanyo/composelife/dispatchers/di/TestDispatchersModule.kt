package com.alexvanyo.composelife.dispatchers.di

import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.dispatchers.TestComposeLifeDispatchers
import dagger.Binds
import dagger.Module
import dagger.Provides
import dagger.hilt.components.SingletonComponent
import dagger.hilt.testing.TestInstallIn
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.test.StandardTestDispatcher
import kotlinx.coroutines.test.TestDispatcher
import javax.inject.Singleton

@Module
@TestInstallIn(
    components = [SingletonComponent::class],
    replaces = [DispatchersModule::class]
)
@OptIn(ExperimentalCoroutinesApi::class)
interface TestDispatchersModule {

    @Binds
    fun bindsDispatchers(testComposeLifeDispatchers: TestComposeLifeDispatchers): ComposeLifeDispatchers

    companion object {

        @Provides
        @Singleton
        fun providesTestDispatcher(): TestDispatcher = StandardTestDispatcher()
    }
}
