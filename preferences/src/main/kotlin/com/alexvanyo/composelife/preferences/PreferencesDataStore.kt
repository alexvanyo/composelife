/*
 * Copyright 2022 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.alexvanyo.composelife.preferences

import androidx.datastore.core.CorruptionException
import androidx.datastore.core.DataStore
import androidx.datastore.core.DataStoreFactory
import androidx.datastore.core.Serializer
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.preferences.proto.PreferencesProto
import com.google.protobuf.InvalidProtocolBufferException
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.SupervisorJob
import java.io.File
import java.io.InputStream
import java.io.OutputStream
import javax.inject.Inject
import javax.inject.Qualifier
import javax.inject.Singleton

@Qualifier
annotation class PreferencesProtoFile

@Singleton
class PreferencesDataStore @Inject constructor(
    @PreferencesProtoFile file: File,
    dispatchers: ComposeLifeDispatchers,
) : DataStore<PreferencesProto> by DataStoreFactory.create(
    serializer = object : Serializer<PreferencesProto> {
        override val defaultValue: PreferencesProto = PreferencesProto.getDefaultInstance()

        override suspend fun readFrom(input: InputStream): PreferencesProto =
            try {
                @Suppress("BlockingMethodInNonBlockingContext")
                PreferencesProto.parseFrom(input)
            } catch (exception: InvalidProtocolBufferException) {
                throw CorruptionException("Cannot read proto.", exception)
            }

        @Suppress("BlockingMethodInNonBlockingContext")
        override suspend fun writeTo(t: PreferencesProto, output: OutputStream) =
            t.writeTo(output)
    },
    scope = CoroutineScope(
        @Suppress("InjectDispatcher") // Dispatchers are injected via dispatchers
        dispatchers.IO + SupervisorJob(),
    ),
    produceFile = { file },
)
