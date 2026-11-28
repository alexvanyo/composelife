/*
 * Copyright 2025 The Android Open Source Project
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

import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.BindingContainer
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.ExperimentalMetroApi
import dev.zacsweers.metro.OnGraphClose
import dev.zacsweers.metro.Provides
import dev.zacsweers.metro.SingleIn
import okio.fakefilesystem.FakeFileSystem
import kotlin.time.Clock

@ContributesTo(AppScope::class)
@BindingContainer
interface FakeFileSystemBindings {
    companion object {
        @Provides
        @SingleIn(AppScope::class)
        internal fun providesFakeFileSystem(clock: Clock): FakeFileSystem = FakeFileSystem(
            clock = clock,
        )
    }
}

@OptIn(ExperimentalMetroApi::class)
@ContributesTo(AppScope::class)
interface FakeFileSystemLifecycle {
    @OnGraphClose
    fun checkNoOpenFiles(fakeFileSystem: Lazy<FakeFileSystem>) {
        if (fakeFileSystem.isInitialized()) {
            fakeFileSystem.value.checkNoOpenFiles()
        }
    }
}
