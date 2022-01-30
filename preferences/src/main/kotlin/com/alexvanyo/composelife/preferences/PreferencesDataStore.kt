package com.alexvanyo.composelife.preferences

import androidx.datastore.core.CorruptionException
import androidx.datastore.core.DataStore
import androidx.datastore.core.DataStoreFactory
import androidx.datastore.core.Serializer
import com.alexvanyo.composelife.preferences.proto.Preferences
import com.google.protobuf.InvalidProtocolBufferException
import java.io.File
import java.io.InputStream
import java.io.OutputStream
import javax.inject.Inject
import javax.inject.Qualifier
import javax.inject.Singleton

@Qualifier
annotation class PreferencesProto

@Singleton
class PreferencesDataStore @Inject constructor(
    @PreferencesProto file: File,
) : DataStore<Preferences> by DataStoreFactory.create(
    serializer = object : Serializer<Preferences> {
        override val defaultValue: Preferences = Preferences.getDefaultInstance()

        override suspend fun readFrom(input: InputStream): Preferences =
            try {
                @Suppress("BlockingMethodInNonBlockingContext")
                Preferences.parseFrom(input)
            } catch (exception: InvalidProtocolBufferException) {
                throw CorruptionException("Cannot read proto.", exception)
            }

        @Suppress("BlockingMethodInNonBlockingContext")
        override suspend fun writeTo(t: Preferences, output: OutputStream) =
            t.writeTo(output)
    },
    produceFile = { file }
)
