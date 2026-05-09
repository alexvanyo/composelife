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

package com.alexvanyo.composelife.filesystem

import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.ContributesBinding
import dev.zacsweers.metro.Inject
import kotlinx.coroutines.withContext
import okio.BufferedSink
import okio.BufferedSource
import okio.FileHandle
import okio.FileMetadata
import okio.FileSystem
import okio.Path
import okio.Sink
import okio.Source
import okio.openZip

@Suppress("TooManyFunctions")
@Inject
@ContributesBinding(AppScope::class)
class OkioAsyncFileSystem(
    private val dispatchers: ComposeLifeDispatchers,
    private val fileSystem: FileSystem,
) : AsyncFileSystem {
    override suspend fun canonicalize(path: Path): Path =
        withContext(dispatchers.IO) {
            fileSystem.canonicalize(path)
        }

    override suspend fun metadata(path: Path): FileMetadata =
        withContext(dispatchers.IO) {
            fileSystem.metadata(path)
        }

    override suspend fun metadataOrNull(path: Path): FileMetadata? =
        withContext(dispatchers.IO) {
            fileSystem.metadataOrNull(path)
        }

    override suspend fun exists(path: Path): Boolean =
        withContext(dispatchers.IO) {
            fileSystem.exists(path)
        }

    override suspend fun list(dir: Path): List<Path> =
        withContext(dispatchers.IO) {
            fileSystem.list(dir)
        }

    override suspend fun listOrNull(dir: Path): List<Path>? =
        withContext(dispatchers.IO) {
            fileSystem.listOrNull(dir)
        }

    override suspend fun listRecursively(
        dir: Path,
        followSymlinks: Boolean,
    ): Sequence<Path> =
        withContext(dispatchers.IO) {
            fileSystem.listRecursively(dir, followSymlinks)
        }

    override suspend fun openReadOnly(file: Path): FileHandle =
        withContext(dispatchers.IO) {
            fileSystem.openReadOnly(file)
        }

    override suspend fun openReadWrite(
        file: Path,
        mustCreate: Boolean,
        mustExist: Boolean,
    ): FileHandle =
        withContext(dispatchers.IO) {
            fileSystem.openReadWrite(file, mustCreate, mustExist)
        }

    override suspend fun source(file: Path): Source =
        withContext(dispatchers.IO) {
            fileSystem.source(file)
        }

    override suspend fun <T> read(file: Path, readerAction: BufferedSource.() -> T): T =
        withContext(dispatchers.IO) {
            fileSystem.read(file, readerAction)
        }

    override suspend fun sink(file: Path, mustCreate: Boolean): Sink =
        withContext(dispatchers.IO) {
            fileSystem.sink(file, mustCreate)
        }

    override suspend fun <T> write(
        file: Path,
        mustCreate: Boolean,
        writerAction: BufferedSink.() -> T,
    ): T =
        withContext(dispatchers.IO) {
            fileSystem.write(file, mustCreate, writerAction)
        }

    override suspend fun appendingSink(file: Path, mustExist: Boolean): Sink =
        withContext(dispatchers.IO) {
            fileSystem.appendingSink(file, mustExist)
        }

    override suspend fun createDirectory(dir: Path, mustCreate: Boolean) {
        withContext(dispatchers.IO) {
            fileSystem.createDirectory(dir, mustCreate)
        }
    }

    override suspend fun createDirectories(dir: Path, mustCreate: Boolean) {
        withContext(dispatchers.IO) {
            fileSystem.createDirectories(dir, mustCreate)
        }
    }

    override suspend fun atomicMove(source: Path, target: Path) {
        withContext(dispatchers.IO) {
            fileSystem.atomicMove(source, target)
        }
    }

    override suspend fun copy(source: Path, target: Path) {
        withContext(dispatchers.IO) {
            fileSystem.copy(source, target)
        }
    }

    override suspend fun delete(path: Path, mustExist: Boolean) {
        withContext(dispatchers.IO) {
            fileSystem.delete(path, mustExist)
        }
    }

    override suspend fun deleteRecursively(fileOrDirectory: Path, mustExist: Boolean) {
        withContext(dispatchers.IO) {
            fileSystem.deleteRecursively(fileOrDirectory, mustExist)
        }
    }

    override suspend fun createSymlink(source: Path, target: Path) {
        withContext(dispatchers.IO) {
            fileSystem.createSymlink(source, target)
        }
    }

    override suspend fun openZip(zipPath: Path): AsyncFileSystem =
        withContext(dispatchers.IO) {
            OkioAsyncFileSystem(
                dispatchers = dispatchers,
                fileSystem = fileSystem.openZip(zipPath),
            )
        }

    override fun close() {
        fileSystem.close()
    }
}
