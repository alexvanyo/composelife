/*
 * Copyright 2024 The Android Open Source Project
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

package com.alexvanyo.composelife.imageloader.di

import coil3.disk.DiskCache
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.BindingContainer
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.Provides
import dev.zacsweers.metro.SingleIn
import okio.FileSystem

@ContributesTo(AppScope::class)
@BindingContainer
interface ImageLoaderDiskCacheBindings {
    companion object {
        @SingleIn(AppScope::class)
        @Provides
        fun providesDiskCache(
            dispatchers: ComposeLifeDispatchers,
            fileSystem: FileSystem,
        ): DiskCache = DiskCache.Builder()
            .directory(FileSystem.SYSTEM_TEMPORARY_DIRECTORY / "coil3_disk_cache")
            .fileSystem(fileSystem)
            .cleanupCoroutineContext(dispatchers.IO)
            .build()
    }
}
