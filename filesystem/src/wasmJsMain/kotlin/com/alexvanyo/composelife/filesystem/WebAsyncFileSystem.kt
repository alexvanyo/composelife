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

@file:Suppress("TooManyFunctions")

package com.alexvanyo.composelife.filesystem

import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.ContributesBinding
import dev.zacsweers.metro.Inject
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.await
import kotlinx.coroutines.launch
import kotlinx.coroutines.withContext
import okio.BufferedSink
import okio.BufferedSource
import okio.FileHandle
import okio.FileMetadata
import okio.IOException
import okio.Path
import okio.Sink
import okio.Source
import okio.Timeout
import okio.buffer
import okio.use
import kotlin.js.Promise

@Suppress("TooManyFunctions")
@OptIn(ExperimentalWasmJsInterop::class)
@Inject
@ContributesBinding(AppScope::class)
class WebAsyncFileSystem(
    private val dispatchers: ComposeLifeDispatchers,
    private val navigator: org.w3c.dom.Navigator,
) : AsyncFileSystem {

    private suspend fun getRoot(): FileSystemDirectoryHandle =
        getStorageManager(navigator).getDirectory().await()

    @Suppress("ReturnCount")
    private suspend fun getHandle(
        path: Path,
        createFile: Boolean = false,
        createDirectory: Boolean = false,
        createIntermediateDirectories: Boolean = false,
    ): FileSystemHandle? {
        var current: FileSystemHandle = getRoot()
        val segments = path.segments.filter { it.isNotEmpty() && it != "." }
        if (segments.isEmpty()) return current

        for (i in segments.indices) {
            val segment = segments[i]
            val isLast = i == segments.size - 1
            val directoryHandle = current as? FileSystemDirectoryHandle ?: return null

            val next = if (isLast) {
                if (createFile) {
                    getFileHandleSafe(directoryHandle, segment, true).await()
                } else if (createDirectory) {
                    getDirectoryHandleSafe(directoryHandle, segment, true).await()
                } else {
                    getHandleSafe(directoryHandle, segment).await()
                }
            } else {
                getDirectoryHandleSafe(directoryHandle, segment, createIntermediateDirectories).await()
            }
            current = next ?: return null
        }
        return current
    }

    override suspend fun canonicalize(path: Path): Path =
        withContext(dispatchers.IO) {
            path
        }

    override suspend fun metadata(path: Path): FileMetadata =
        withContext(dispatchers.IO) {
            metadataOrNull(path) ?: throw IOException("File not found: $path")
        }

    override suspend fun metadataOrNull(path: Path): FileMetadata? =
        withContext(dispatchers.IO) {
            when (val handle = getHandle(path)) {
                is FileSystemFileHandle -> {
                    val file = handle.getFile().await()
                    FileMetadata(
                        isRegularFile = true,
                        isDirectory = false,
                        size = file.size.toDouble().toLong(),
                        createdAtMillis = null,
                        lastModifiedAtMillis = file.lastModified.toDouble().toLong(),
                        lastAccessedAtMillis = null,
                    )
                }

                is FileSystemDirectoryHandle -> {
                    FileMetadata(
                        isRegularFile = false,
                        isDirectory = true,
                        size = null,
                        createdAtMillis = null,
                        lastModifiedAtMillis = null,
                        lastAccessedAtMillis = null,
                    )
                }

                else -> null
            }
        }

    override suspend fun exists(path: Path): Boolean =
        withContext(dispatchers.IO) {
            metadataOrNull(path) != null
        }

    override suspend fun list(dir: Path): List<Path> =
        withContext(dispatchers.IO) {
            listOrNull(dir) ?: throw IOException("Directory not found: $dir")
        }

    override suspend fun listOrNull(dir: Path): List<Path>? =
        withContext(dispatchers.IO) {
            val handle = getHandle(dir) as? FileSystemDirectoryHandle ?: return@withContext null
            val result = mutableListOf<Path>()
            val iterator = getKeysIterator(handle)
            while (true) {
                val next = iterator.next().await()
                if (next.done) break
                result.add(dir / next.value.toString())
            }
            result.sorted()
        }

    override suspend fun listRecursively(dir: Path, followSymlinks: Boolean): Sequence<Path> =
        withContext(dispatchers.IO) {
            val result = mutableListOf<Path>()
            suspend fun recursiveList(currentDir: Path) {
                val children = listOrNull(currentDir) ?: return
                for (child in children) {
                    result.add(child)
                    val metadata = metadataOrNull(child)
                    if (metadata?.isDirectory == true) {
                        recursiveList(child)
                    }
                }
            }
            recursiveList(dir)
            result.asSequence()
        }

    override suspend fun openReadOnly(file: Path): FileHandle {
        TODO("Not yet implemented")
    }

    override suspend fun openReadWrite(file: Path, mustCreate: Boolean, mustExist: Boolean): FileHandle {
        TODO("Not yet implemented")
    }

    override suspend fun source(file: Path): Source =
        withContext(dispatchers.IO) {
            val handle = getHandle(file) as? FileSystemFileHandle ?: throw IOException("File not found: $file")
            val fileData = handle.getFile().await()
            val arrayBuffer = fileData.arrayBuffer().await()
            val bytes = getInt8Array(arrayBuffer)
            val buffer = okio.Buffer()
            for (i in 0 until getInt8ArrayLength(bytes)) {
                buffer.writeByte(getInt8ArrayValue(bytes, i).toInt())
            }
            buffer
        }

    override suspend fun <T> read(file: Path, readerAction: BufferedSource.() -> T): T =
        source(file).buffer().use(readerAction)

    override suspend fun sink(file: Path, mustCreate: Boolean): Sink =
        withContext(dispatchers.IO) {
            val handle = getHandle(
                path = file,
                createFile = true,
                createIntermediateDirectories = true,
            ) as? FileSystemFileHandle
                ?: throw IOException("Could not create file: $file")
            WebWritableSink(dispatchers, handle, append = false)
        }

    override suspend fun <T> write(file: Path, mustCreate: Boolean, writerAction: BufferedSink.() -> T): T =
        withContext(dispatchers.IO) {
            val handle = getHandle(
                path = file,
                createFile = true,
                createIntermediateDirectories = true,
            ) as? FileSystemFileHandle
                ?: throw IOException("Could not create file: $file")

            val buffer = okio.Buffer()
            val result = buffer.writerAction()

            val writable = handle.createWritable().await()
            writable.write(createInt8ArrayFromKotlin(buffer.readByteArray())).await()
            writable.close().await()
            result
        }

    override suspend fun appendingSink(file: Path, mustExist: Boolean): Sink =
        withContext(dispatchers.IO) {
            val handle = getHandle(
                path = file,
                createFile = !mustExist,
                createIntermediateDirectories = !mustExist,
            ) as? FileSystemFileHandle
                ?: throw IOException("Could not find/create file: $file")
            WebWritableSink(dispatchers, handle, append = true)
        }

    override suspend fun createDirectory(dir: Path, mustCreate: Boolean) {
        withContext(dispatchers.IO) {
            getHandle(
                path = dir,
                createDirectory = true,
                createIntermediateDirectories = true,
            ) ?: throw IOException("Could not create directory: $dir")
        }
    }

    override suspend fun createDirectories(dir: Path, mustCreate: Boolean) {
        withContext(dispatchers.IO) {
            getHandle(
                path = dir,
                createDirectory = true,
                createIntermediateDirectories = true,
            ) ?: throw IOException("Could not create directories: $dir")
        }
    }

    override suspend fun atomicMove(source: Path, target: Path) {
        withContext(dispatchers.IO) {
            val sourceHandle = getHandle(source) ?: throw IOException("Source not found: $source")
            val targetParentPath = target.parent ?: throw IOException("Target must have a parent")
            val targetParentHandle = getHandle(targetParentPath) as? FileSystemDirectoryHandle
                ?: throw IOException("Target parent not found: $targetParentPath")

            sourceHandle.move(targetParentHandle, target.name).await()
        }
    }

    override suspend fun copy(source: Path, target: Path) {
        withContext(dispatchers.IO) {
            val bytes = read(source) { readByteArray() }
            write(target) { write(bytes) }
        }
    }

    override suspend fun delete(path: Path, mustExist: Boolean) {
        withContext(dispatchers.IO) {
            val parentPath = path.parent ?: return@withContext
            val parentHandle = getHandle(parentPath) as? FileSystemDirectoryHandle ?: return@withContext
            removeEntrySafe(parentHandle, path.name, false).await()
        }
    }

    override suspend fun deleteRecursively(fileOrDirectory: Path, mustExist: Boolean) {
        withContext(dispatchers.IO) {
            val parentPath = fileOrDirectory.parent ?: return@withContext
            val parentHandle = getHandle(parentPath) as? FileSystemDirectoryHandle ?: return@withContext
            removeEntrySafe(parentHandle, fileOrDirectory.name, true).await()
        }
    }

    override suspend fun createSymlink(source: Path, target: Path) {
        throw IOException("Symlinks not supported in OPFS")
    }

    override suspend fun openZip(zipPath: Path): AsyncFileSystem {
        TODO("Not yet implemented")
    }

    override fun close() = Unit
}

private class WebWritableSink(
    private val dispatchers: ComposeLifeDispatchers,
    private val handle: FileSystemFileHandle,
    private val append: Boolean,
) : Sink {
    private val buffer = okio.Buffer()

    override fun write(source: okio.Buffer, byteCount: Long) {
        buffer.write(source, byteCount)
    }

    override fun flush() {
        // No-op
    }

    override fun timeout(): Timeout = Timeout.NONE

    @OptIn(ExperimentalWasmJsInterop::class)
    override fun close() {
        if (buffer.size == 0L) return
        val bytes = buffer.readByteArray()
        // We have to use a global scope or similar because we can't block.
        // This is not ideal but Sink.close() is synchronous.
        CoroutineScope(dispatchers.IO).launch {
            val writable = if (append) {
                val file = handle.getFile().await()
                val options = createWritableOptions(keepExistingData = true)
                handle.createWritable(options).await().apply {
                    seek(file.size).await()
                }
            } else {
                handle.createWritable().await()
            }
            writable.write(createInt8ArrayFromKotlin(bytes)).await()
            writable.close().await()
        }
    }
}

@OptIn(ExperimentalWasmJsInterop::class)
@Suppress("UNUSED_PARAMETER")
internal fun getStorageManager(navigator: org.w3c.dom.Navigator): StorageManager =
    js("navigator.storage")

@OptIn(ExperimentalWasmJsInterop::class)
internal open external class FileSystemHandle : JsAny {
    val kind: String
    val name: String
    fun move(name: String): Promise<JsAny?>
    fun move(parent: FileSystemDirectoryHandle): Promise<JsAny?>
    fun move(parent: FileSystemDirectoryHandle, name: String): Promise<JsAny?>
}

@OptIn(ExperimentalWasmJsInterop::class)
internal external class FileSystemFileHandle : FileSystemHandle {
    fun getFile(): Promise<WebFile>
    fun createWritable(): Promise<FileSystemWritableFileStream>
    fun createWritable(options: JsAny): Promise<FileSystemWritableFileStream>
}

@OptIn(ExperimentalWasmJsInterop::class)
internal external class FileSystemDirectoryHandle : FileSystemHandle

@OptIn(ExperimentalWasmJsInterop::class)
internal external class StorageManager : JsAny {
    fun getDirectory(): Promise<FileSystemDirectoryHandle>
}

@OptIn(ExperimentalWasmJsInterop::class)
internal external class FileSystemWritableFileStream : JsAny {
    fun write(data: JsAny): Promise<JsAny?>
    fun seek(position: JsNumber): Promise<JsAny?>
    fun close(): Promise<JsAny?>
}

@OptIn(ExperimentalWasmJsInterop::class)
internal external class WebFile : JsAny {
    val size: JsNumber
    val lastModified: JsNumber
    fun arrayBuffer(): Promise<JsAny>
}

@OptIn(ExperimentalWasmJsInterop::class)
internal external class AsyncIterator : JsAny {
    fun next(): Promise<AsyncIteratorResult>
}

@OptIn(ExperimentalWasmJsInterop::class)
internal external class AsyncIteratorResult : JsAny {
    val done: Boolean
    val value: JsAny?
}

@OptIn(ExperimentalWasmJsInterop::class)
@Suppress("UNUSED_PARAMETER")
internal fun getHandleSafe(handle: FileSystemDirectoryHandle, name: String): Promise<FileSystemHandle?> =
    js(
        """
        handle.getFileHandle(name)
            .catch(e => {
                if (e.name === 'TypeMismatchError') {
                    return handle.getDirectoryHandle(name);
                }
                throw e;
            })
            .catch(e => {
                if (e.name === 'NotFoundError') {
                    return null;
                }
                throw e;
            })
        """,
    )

@OptIn(ExperimentalWasmJsInterop::class)
@Suppress("UNUSED_PARAMETER")
internal fun getFileHandleSafe(
    handle: FileSystemDirectoryHandle,
    name: String,
    create: Boolean,
): Promise<FileSystemFileHandle?> =
    js(
        """
        handle.getFileHandle(name, { create: create })
            .catch(e => {
                if (e.name === 'TypeMismatchError' || e.name === 'NotFoundError') {
                    return null;
                }
                throw e;
            })
        """,
    )

@OptIn(ExperimentalWasmJsInterop::class)
@Suppress("UNUSED_PARAMETER")
internal fun getDirectoryHandleSafe(
    handle: FileSystemDirectoryHandle,
    name: String,
    create: Boolean,
): Promise<FileSystemDirectoryHandle?> =
    js(
        """
        handle.getDirectoryHandle(name, { create: create })
            .catch(e => {
                if (e.name === 'TypeMismatchError' || e.name === 'NotFoundError') {
                    return null;
                }
                throw e;
            })
        """,
    )

@OptIn(ExperimentalWasmJsInterop::class)
@Suppress("UNUSED_PARAMETER")
internal fun removeEntrySafe(handle: FileSystemDirectoryHandle, name: String, recursive: Boolean): Promise<JsAny?> =
    js(
        """
        handle.removeEntry(name, { recursive: recursive })
            .catch(e => {
                if (e.name === 'NotFoundError') {
                    return null;
                }
                throw e;
            })
        """,
    )

@OptIn(ExperimentalWasmJsInterop::class)
@Suppress("UNUSED_PARAMETER")
internal fun getKeysIterator(handle: FileSystemDirectoryHandle): AsyncIterator =
    js("handle.keys()[Symbol.asyncIterator]()")

@OptIn(ExperimentalWasmJsInterop::class)
@Suppress("UNUSED_PARAMETER")
internal fun createWritableOptions(keepExistingData: Boolean): JsAny =
    js("({ keepExistingData: keepExistingData })")

@OptIn(ExperimentalWasmJsInterop::class)
@Suppress("UNUSED_PARAMETER")
internal fun getInt8Array(buffer: JsAny): JsAny =
    js("new Int8Array(buffer)")

@OptIn(ExperimentalWasmJsInterop::class)
internal fun createInt8ArrayFromKotlin(array: ByteArray): JsAny {
    val result = createInt8ArrayOfSize(array.size)
    for (i in array.indices) {
        setInt8ArrayValue(result, i, array[i])
    }
    return result
}

@OptIn(ExperimentalWasmJsInterop::class)
@Suppress("UNUSED_PARAMETER")
internal fun createInt8ArrayOfSize(size: Int): JsAny =
    js("new Int8Array(size)")

@OptIn(ExperimentalWasmJsInterop::class)
@Suppress("UNUSED_PARAMETER")
internal fun setInt8ArrayValue(array: JsAny, index: Int, value: Byte): Unit =
    js("array[index] = value")

@OptIn(ExperimentalWasmJsInterop::class)
@Suppress("UNUSED_PARAMETER")
internal fun getInt8ArrayLength(array: JsAny): Int =
    js("array.length")

@OptIn(ExperimentalWasmJsInterop::class)
@Suppress("UNUSED_PARAMETER")
internal fun getInt8ArrayValue(array: JsAny, index: Int): Byte =
    js("array[index]")
