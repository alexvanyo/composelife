package com.alexvanyo.composelife.preferences.di

import com.alexvanyo.composelife.preferences.ComposeLifePreferences
import com.alexvanyo.composelife.preferences.TestComposeLifePreferences
import dagger.Binds
import dagger.Module
import dagger.hilt.components.SingletonComponent
import dagger.hilt.testing.TestInstallIn

@Module
@TestInstallIn(
    components = [SingletonComponent::class],
    replaces = [PreferencesModule::class]
)
interface TestPreferencesModule {

    @Binds
    fun bindsComposeLifePreferences(
        testComposeLifePreferences: TestComposeLifePreferences,
    ): ComposeLifePreferences
}
