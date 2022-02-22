package com.alexvanyo.composelife.preferences.di

import com.alexvanyo.composelife.preferences.FileProvider
import com.alexvanyo.composelife.preferences.PreferencesProtoFile
import dagger.Module
import dagger.Provides
import dagger.hilt.components.SingletonComponent
import dagger.hilt.testing.TestInstallIn
import java.io.File

@Module
@TestInstallIn(
    components = [SingletonComponent::class],
    replaces = [PreferencesProtoModule::class]
)
interface TestPreferencesProtoModule {
    companion object {
        @Provides
        @PreferencesProtoFile
        fun providesDataStoreFile(
            fileProvider: FileProvider,
        ): File = fileProvider.get()
    }
}
