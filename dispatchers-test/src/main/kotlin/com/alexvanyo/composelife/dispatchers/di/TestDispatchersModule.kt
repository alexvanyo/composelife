package com.alexvanyo.composelife.dispatchers.di

import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.dispatchers.TestComposeLifeDispatchers
import dagger.Binds
import dagger.Module
import dagger.hilt.components.SingletonComponent
import dagger.hilt.testing.TestInstallIn

@Module
@TestInstallIn(
    components = [SingletonComponent::class],
    replaces = [DispatchersModule::class]
)
interface TestDispatchersModule {

    @Binds
    fun bindsDispatchers(testComposeLifeDispatchers: TestComposeLifeDispatchers): ComposeLifeDispatchers
}
