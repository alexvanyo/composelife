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

package com.alexvanyo.composelife.filesystem.di

import com.alexvanyo.composelife.updatable.Updatable
import kotlinx.coroutines.awaitCancellation
import me.tatarka.inject.annotations.IntoSet
import me.tatarka.inject.annotations.Provides
import okio.FileSystem
import okio.fakefilesystem.FakeFileSystem
import software.amazon.lastmile.kotlin.inject.anvil.AppScope
import software.amazon.lastmile.kotlin.inject.anvil.ContributesTo
import software.amazon.lastmile.kotlin.inject.anvil.SingleIn
import kotlin.time.Clock

@ContributesTo(AppScope::class, replaces = [FileSystemComponent::class])
interface TestFileSystemComponent {
    @Provides
    @SingleIn(AppScope::class)
    fun providesFakeFileSystem(
        clock: Clock,
    ): FakeFileSystem = FakeFileSystem(
        clock = clock,
    )

    @Provides
    fun providesFileSystem(
        fakeFileSystem: FakeFileSystem,
    ): FileSystem = fakeFileSystem

    @Provides
    @SingleIn(AppScope::class)
    @IntoSet
    fun providesFakeFileSystemIntoUpdatable(
        fakeFileSystem: FakeFileSystem,
    ): Updatable = object : Updatable {
        override suspend fun update(): Nothing =
            try {
                awaitCancellation()
            } finally {
                fakeFileSystem.checkNoOpenFiles()
            }
    }
}
