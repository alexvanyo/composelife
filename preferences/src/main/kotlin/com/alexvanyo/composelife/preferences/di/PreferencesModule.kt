package com.alexvanyo.composelife.preferences.di

import com.alexvanyo.composelife.preferences.ComposeLifePreferences
import com.alexvanyo.composelife.preferences.DefaultComposeLifePreferences
import dagger.Binds
import dagger.Module
import dagger.hilt.InstallIn
import dagger.hilt.components.SingletonComponent

@Module
@InstallIn(SingletonComponent::class)
interface PreferencesModule {

    @Binds
    fun bindsComposeLifePreferences(
        defaultComposeLifePreferences: DefaultComposeLifePreferences,
    ): ComposeLifePreferences
}
