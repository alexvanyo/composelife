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

import coil3.ImageLoader
import coil3.PlatformContext
import coil3.annotation.ExperimentalCoilApi
import coil3.disk.DiskCache
import coil3.memory.MemoryCache
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.updatable.Updatable
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.BindingContainer
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.ForScope
import dev.zacsweers.metro.IntoSet
import dev.zacsweers.metro.Provides
import dev.zacsweers.metro.SingleIn
import kotlinx.coroutines.awaitCancellation
import okio.FileSystem

@ContributesTo(AppScope::class)
@BindingContainer
interface ImageLoaderBindings {

    companion object {
        @SingleIn(AppScope::class)
        @Provides
        internal fun providesMemoryCache(
            context: PlatformContext,
        ): MemoryCache = MemoryCache.Builder()
            .maxSizePercent(context)
            .build()

        @OptIn(ExperimentalCoilApi::class)
        @Suppress("LongParameterList")
        @SingleIn(AppScope::class)
        @Provides
        internal fun providesImageLoader(
            context: PlatformContext,
            memoryCache: Lazy<MemoryCache>,
            diskCache: Lazy<DiskCache>,
            fetcherFactoriesWithType: Set<FetcherFactoryWithType<out Any>>,
            keyers: Set<KeyerWithType<out Any>>,
            dispatchers: ComposeLifeDispatchers,
            fileSystem: FileSystem,
        ): ImageLoader = ImageLoader.Builder(context)
            .fileSystem(fileSystem)
            .memoryCache(memoryCache::value)
            .diskCache(diskCache::value)
            .components {
                addFetcherFactories { fetcherFactoriesWithType.map { it.fetcherFactory to it.type } }
                keyers.forEach { it.addTo(this) }
            }
            .coroutineContext(dispatchers.IO)
            .mainCoroutineContext { dispatchers.MainImmediate }
            .build()

        @Provides
        @SingleIn(AppScope::class)
        @IntoSet
        @ForScope(AppScope::class)
        internal fun providesImageLoaderShutdownIntoUpdatable(
            imageLoader: ImageLoader,
        ): Updatable = object : Updatable {
            override suspend fun update(): Nothing =
                try {
                    awaitCancellation()
                } finally {
                    imageLoader.shutdown()
                }
        }
    }
}
