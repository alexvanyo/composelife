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
import com.alexvanyo.composelife.filesystem.di.FileSystemModule
import com.alexvanyo.composelife.scopes.Singleton
import com.alexvanyo.composelife.updatable.Updatable
import kotlinx.coroutines.awaitCancellation
import me.tatarka.inject.annotations.IntoSet
import me.tatarka.inject.annotations.Provides

interface ImageLoaderComponent :
    ImageLoaderModule,
    FileSystemModule,
    PlatformContextComponent,
    ImageLoaderDiskCacheComponent,
    ImageLoaderFetcherFactoryComponent,
    ImageLoaderKeyerComponent {

    @Singleton
    @Provides
    fun providesImageLoader(
        context: PlatformContext,
        diskCache: Lazy<DiskCache>,
        fetcherFactoriesWithType: Set<FetcherFactoryWithType<out Any>>,
        keyers: Set<KeyerWithType<out Any>>,
    ): ImageLoader = ImageLoader.Builder(context)
        .diskCache(diskCache::value)
        .components {
            addFetcherFactories { fetcherFactoriesWithType.map { it.fetcherFactory to it.type } }
            keyers.forEach { it.addTo(this) }
        }
        .build()

    @Provides
    @Singleton
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
