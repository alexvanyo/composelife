package com.alexvanyo.composelife.preferences.di

import android.content.Context
import androidx.datastore.dataStoreFile
import com.alexvanyo.composelife.preferences.PreferencesProto
import dagger.Module
import dagger.Provides
import dagger.hilt.InstallIn
import dagger.hilt.android.qualifiers.ApplicationContext
import dagger.hilt.components.SingletonComponent
import java.io.File

@Module
@InstallIn(SingletonComponent::class)
interface PreferencesProtoModule {

    companion object {
        @Provides
        @PreferencesProto
        fun providesDataStoreFile(
            @ApplicationContext context: Context,
        ): File = context.dataStoreFile("preferences.pb")
    }
}
