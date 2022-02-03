package com.alexvanyo.composelife.preferences.di

import com.alexvanyo.composelife.preferences.FileProvider
import com.alexvanyo.composelife.preferences.PreferencesProto
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
        @PreferencesProto
        fun providesDataStoreFile(
            fileProvider: FileProvider
        ): File = fileProvider.get()
    }
}
