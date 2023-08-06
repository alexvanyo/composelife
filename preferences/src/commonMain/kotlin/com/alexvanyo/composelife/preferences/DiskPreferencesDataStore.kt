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
import androidx.datastore.core.okio.OkioSerializer
import androidx.datastore.core.okio.OkioStorage
import com.alexvanyo.composelife.preferences.proto.PreferencesProto
import com.alexvanyo.composelife.scopes.Singleton
import kotlinx.coroutines.CoroutineScope
import me.tatarka.inject.annotations.Inject
import okio.BufferedSink
import okio.BufferedSource
import okio.FileSystem
import okio.Path
import java.io.IOException

typealias PreferencesProtoPath = Path

typealias PreferencesCoroutineScope = CoroutineScope

@Singleton
class DiskPreferencesDataStore @Inject constructor(
    fileSystem: FileSystem,
    path: PreferencesProtoPath,
    scope: PreferencesCoroutineScope,
) : PreferencesDataStore,
    DataStore<PreferencesProto> by DataStoreFactory.create(
        storage = OkioStorage(
            fileSystem = fileSystem,
            serializer = object : OkioSerializer<PreferencesProto> {
                override val defaultValue: PreferencesProto
                    get() = PreferencesProto()

                override suspend fun readFrom(source: BufferedSource): PreferencesProto =
                    try {
                        PreferencesProto.ADAPTER.decode(source)
                    } catch (exception: IOException) {
                        throw CorruptionException("Cannot read proto.", exception)
                    }

                override suspend fun writeTo(t: PreferencesProto, sink: BufferedSink) =
                    PreferencesProto.ADAPTER.encode(sink, t)
            },
            producePath = { path },
        ),
        corruptionHandler = null,
        migrations = emptyList(),
        scope = scope,
    )
