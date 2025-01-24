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
import coil3.disk.DiskCache
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.updatable.Updatable
import kotlinx.coroutines.awaitCancellation
import me.tatarka.inject.annotations.IntoSet
import me.tatarka.inject.annotations.Provides
import okio.FileSystem
import software.amazon.lastmile.kotlin.inject.anvil.AppScope
import software.amazon.lastmile.kotlin.inject.anvil.ContributesTo
import software.amazon.lastmile.kotlin.inject.anvil.SingleIn

@ContributesTo(AppScope::class)
interface ImageLoaderComponent {

    @Suppress("LongParameterList")
    @SingleIn(AppScope::class)
    @Provides
    fun providesImageLoader(
        context: PlatformContext,
        diskCache: Lazy<DiskCache>,
        fetcherFactoriesWithType: Set<FetcherFactoryWithType<out Any>>,
        keyers: Set<KeyerWithType<out Any>>,
        dispatchers: ComposeLifeDispatchers,
        fileSystem: FileSystem,
    ): ImageLoader = ImageLoader.Builder(context)
        .fileSystem(fileSystem)
        .diskCache(diskCache::value)
        .components {
            addFetcherFactories { fetcherFactoriesWithType.map { it.fetcherFactory to it.type } }
            keyers.forEach { it.addTo(this) }
        }
        .fetcherCoroutineContext(dispatchers.IO)
        .decoderCoroutineContext(dispatchers.IO)
        .build()

    @Provides
    @SingleIn(AppScope::class)
    @IntoSet
    fun providesImagerLoaderShutdownIntoUpdatable(
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
