/*
 * Copyright 2026 The Android Open Source Project
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

@file:OptIn(kotlin.js.ExperimentalWasmJsInterop::class)
@file:Suppress(
    "LongMethod",
    "TooManyFunctions",
    "ComplexCondition",
    "ReturnCount",
    "ThrowsCount",
)

package com.alexvanyo.composelife.filesystem

import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import kotlinx.coroutines.await
import kotlinx.coroutines.withContext
import okio.BufferedSink
import okio.BufferedSource
import okio.FileHandle
import okio.FileMetadata
import okio.FileSystem
import okio.IOException
import okio.Path
import okio.Path.Companion.toPath
import okio.Sink
import okio.Source
import okio.Timeout
import okio.buffer
import okio.use
import kotlin.js.Promise

class ZipEntry(
    val name: String,
    val compressionMethod: Short,
    val compressedSize: Int,
    val uncompressedSize: Int,
    val localHeaderOffset: Int,
)

class ZipArchive(val entries: Map<Path, ZipEntry>, val directories: Set<Path>, val bytes: ByteArray) {
    companion object {
        fun parse(bytes: ByteArray): ZipArchive {
            var eocdOffset = -1
            val minOffset = maxOf(0, bytes.size - 22 - 65535)
            for (i in bytes.size - 22 downTo minOffset) {
                if (bytes[i] == 0x50.toByte() &&
                    bytes[i + 1] == 0x4b.toByte() &&
                    bytes[i + 2] == 0x05.toByte() &&
                    bytes[i + 3] == 0x06.toByte()
                ) {
                    eocdOffset = i
                    break
                }
            }
            if (eocdOffset == -1) {
                throw IOException("EOCD not found")
            }

            val cdEntriesCount = readShort(bytes, eocdOffset + 10).toInt() and 0xffff
            val cdOffset = readInt(bytes, eocdOffset + 16)

            val entries = mutableMapOf<Path, ZipEntry>()
            val directories = mutableSetOf<Path>()
            directories.add("/".toPath())

            var currentOffset = cdOffset
            for (i in 0 until cdEntriesCount) {
                if (currentOffset + 46 > bytes.size) {
                    throw IOException("Central Directory entry out of bounds")
                }
                val signature = readInt(bytes, currentOffset)
                if (signature != 0x02014b50) {
                    throw IOException("Invalid Central Directory signature: $signature")
                }
                val compressionMethod = readShort(bytes, currentOffset + 10)
                val compressedSize = readInt(bytes, currentOffset + 20)
                val uncompressedSize = readInt(bytes, currentOffset + 24)
                val fileNameLength = readShort(bytes, currentOffset + 28).toInt() and 0xffff
                val extraFieldLength = readShort(bytes, currentOffset + 30).toInt() and 0xffff
                val fileCommentLength = readShort(bytes, currentOffset + 32).toInt() and 0xffff
                val localHeaderOffset = readInt(bytes, currentOffset + 42)

                if (currentOffset + 46 + fileNameLength > bytes.size) {
                    throw IOException("File name out of bounds")
                }
                val name = bytes.decodeToString(currentOffset + 46, currentOffset + 46 + fileNameLength)
                val path = "/".toPath() / name

                if (name.endsWith("/")) {
                    directories.add(path)
                } else {
                    entries[path] = ZipEntry(
                        name = name,
                        compressionMethod = compressionMethod,
                        compressedSize = compressedSize,
                        uncompressedSize = uncompressedSize,
                        localHeaderOffset = localHeaderOffset,
                    )
                    var parent = path.parent
                    while (parent != null) {
                        directories.add(parent)
                        parent = parent.parent
                    }
                }
                currentOffset += 46 + fileNameLength + extraFieldLength + fileCommentLength
            }

            return ZipArchive(entries, directories, bytes)
        }
    }
}

class ZipFileSystem(private val archive: ZipArchive) : FileSystem() {
    private val directories: Set<Path> = archive.directories
    private val files: Map<Path, ZipEntry> = archive.entries

    override fun canonicalize(path: Path): Path = "/".toPath() / path

    override fun metadataOrNull(path: Path): FileMetadata? {
        val canonical = canonicalize(path)
        if (canonical in directories) {
            return FileMetadata(
                isRegularFile = false,
                isDirectory = true,
                size = null,
                createdAtMillis = null,
                lastModifiedAtMillis = null,
                lastAccessedAtMillis = null,
            )
        }
        val entry = files[canonical]
        if (entry != null) {
            return FileMetadata(
                isRegularFile = true,
                isDirectory = false,
                size = entry.uncompressedSize.toLong(),
                createdAtMillis = null,
                lastModifiedAtMillis = null,
                lastAccessedAtMillis = null,
            )
        }
        return null
    }

    override fun list(dir: Path): List<Path> = listOrNull(dir) ?: throw IOException("Directory not found: $dir")

    override fun listOrNull(dir: Path): List<Path>? {
        val canonicalDir = canonicalize(dir)
        if (canonicalDir !in directories) return null

        val result = mutableSetOf<Path>()
        for (file in files.keys) {
            if (file.parent == canonicalDir) {
                result.add(file)
            }
        }
        for (d in directories) {
            if (d.parent == canonicalDir && d != canonicalDir) {
                result.add(d)
            }
        }
        return result.sorted()
    }

    override fun openReadOnly(file: Path): FileHandle = throw IOException("Unsupported operation")

    override fun openReadWrite(file: Path, mustCreate: Boolean, mustExist: Boolean): FileHandle =
        throw IOException("Unsupported operation")

    override fun source(file: Path): Source {
        val canonical = canonicalize(file)
        val entry = files[canonical] ?: throw IOException("File not found: $file")

        val lfhOffset = entry.localHeaderOffset
        val signature = readInt(archive.bytes, lfhOffset)
        if (signature != 0x04034b50) {
            throw IOException("Invalid Local File Header signature: $signature at $lfhOffset")
        }
        val fileNameLength = readShort(archive.bytes, lfhOffset + 26).toInt() and 0xffff
        val extraFieldLength = readShort(archive.bytes, lfhOffset + 28).toInt() and 0xffff
        val dataOffset = lfhOffset + 30 + fileNameLength + extraFieldLength

        val decompressedBytes = when (entry.compressionMethod.toInt()) {
            0 -> {
                archive.bytes.copyOfRange(dataOffset, dataOffset + entry.compressedSize)
            }

            8 -> {
                throw IOException(
                    "Deflate decompression not supported synchronously on WasmJs. Use AsyncFileSystem instead.",
                )
            }

            else -> throw IOException("Unsupported compression method: ${entry.compressionMethod}")
        }

        val buffer = okio.Buffer()
        buffer.write(decompressedBytes)
        return buffer
    }

    override fun sink(file: Path, mustCreate: Boolean): Sink = throw IOException("Read-only file system")

    override fun appendingSink(file: Path, mustExist: Boolean): Sink = throw IOException("Read-only file system")

    override fun createDirectory(dir: Path, mustCreate: Boolean): Unit = throw IOException("Read-only file system")

    override fun atomicMove(source: Path, target: Path): Unit = throw IOException("Read-only file system")

    override fun delete(path: Path, mustExist: Boolean): Unit = throw IOException("Read-only file system")

    override fun createSymlink(source: Path, target: Path): Unit = throw IOException("Read-only file system")
}

class ZipAsyncFileSystem(private val dispatchers: ComposeLifeDispatchers, private val archive: ZipArchive) :
    AsyncFileSystem {

    override suspend fun canonicalize(path: Path): Path = withContext(dispatchers.IO) {
        "/".toPath() / path
    }

    override suspend fun metadata(path: Path): FileMetadata = withContext(dispatchers.IO) {
        metadataOrNull(path) ?: throw IOException("File not found: $path")
    }

    override suspend fun metadataOrNull(path: Path): FileMetadata? = withContext(dispatchers.IO) {
        val canonical = canonicalize(path)
        if (canonical in archive.directories) {
            FileMetadata(
                isRegularFile = false,
                isDirectory = true,
                size = null,
                createdAtMillis = null,
                lastModifiedAtMillis = null,
                lastAccessedAtMillis = null,
            )
        } else {
            val entry = archive.entries[canonical]
            if (entry != null) {
                FileMetadata(
                    isRegularFile = true,
                    isDirectory = false,
                    size = entry.uncompressedSize.toLong(),
                    createdAtMillis = null,
                    lastModifiedAtMillis = null,
                    lastAccessedAtMillis = null,
                )
            } else {
                null
            }
        }
    }

    override suspend fun exists(path: Path): Boolean = withContext(dispatchers.IO) {
        metadataOrNull(path) != null
    }

    override suspend fun list(dir: Path): List<Path> = withContext(dispatchers.IO) {
        listOrNull(dir) ?: throw IOException("Directory not found: $dir")
    }

    override suspend fun listOrNull(dir: Path): List<Path>? = withContext(dispatchers.IO) {
        val canonicalDir = canonicalize(dir)
        if (canonicalDir !in archive.directories) return@withContext null

        val result = mutableSetOf<Path>()
        for (file in archive.entries.keys) {
            if (file.parent == canonicalDir) {
                result.add(file)
            }
        }
        for (d in archive.directories) {
            if (d.parent == canonicalDir && d != canonicalDir) {
                result.add(d)
            }
        }
        result.sorted()
    }

    override suspend fun listRecursively(dir: Path, followSymlinks: Boolean): Sequence<Path> =
        withContext(dispatchers.IO) {
            val canonicalDir = canonicalize(dir)
            if (canonicalDir !in archive.directories) throw IOException("Directory not found: $dir")

            val result = mutableListOf<Path>()
            for (file in archive.entries.keys) {
                if (file.segments.take(canonicalDir.segments.size) == canonicalDir.segments && file != canonicalDir) {
                    result.add(file)
                }
            }
            for (d in archive.directories) {
                if (d.segments.take(canonicalDir.segments.size) == canonicalDir.segments && d != canonicalDir) {
                    result.add(d)
                }
            }
            result.sorted().asSequence()
        }

    override suspend fun openReadOnly(file: Path): FileHandle {
        TODO("Not yet implemented")
    }

    override suspend fun openReadWrite(file: Path, mustCreate: Boolean, mustExist: Boolean): FileHandle {
        TODO("Not yet implemented")
    }

    override suspend fun source(file: Path): Source = withContext(dispatchers.IO) {
        val canonical = canonicalize(file)
        val entry = archive.entries[canonical] ?: throw IOException("File not found: $file")

        val lfhOffset = entry.localHeaderOffset
        if (lfhOffset + 30 > archive.bytes.size) {
            throw IOException("Local File Header out of bounds")
        }
        val signature = readInt(archive.bytes, lfhOffset)
        if (signature != 0x04034b50) {
            throw IOException("Invalid Local File Header signature: $signature at $lfhOffset")
        }
        val fileNameLength = readShort(archive.bytes, lfhOffset + 26).toInt() and 0xffff
        val extraFieldLength = readShort(archive.bytes, lfhOffset + 28).toInt() and 0xffff
        val dataOffset = lfhOffset + 30 + fileNameLength + extraFieldLength

        if (dataOffset + entry.compressedSize > archive.bytes.size) {
            throw IOException("Entry data out of bounds")
        }

        val decompressedBytes = when (entry.compressionMethod.toInt()) {
            0 -> {
                archive.bytes.copyOfRange(dataOffset, dataOffset + entry.compressedSize)
            }

            8 -> {
                val compressedData = archive.bytes.copyOfRange(dataOffset, dataOffset + entry.compressedSize)
                val compressedJsArray = createInt8ArrayFromKotlin(compressedData)
                val decompressedJsArray = decompressDeflateRaw(compressedJsArray).await()
                val length = getInt8ArrayLength(decompressedJsArray)
                val byteArray = ByteArray(length)
                for (i in 0 until length) {
                    byteArray[i] = getInt8ArrayValue(decompressedJsArray, i)
                }
                byteArray
            }

            else -> throw IOException("Unsupported compression method: ${entry.compressionMethod}")
        }

        val buffer = okio.Buffer()
        buffer.write(decompressedBytes)
        buffer
    }

    override suspend fun <T> read(file: Path, readerAction: BufferedSource.() -> T): T =
        source(file).buffer().use(readerAction)

    override suspend fun sink(file: Path, mustCreate: Boolean): Sink = throw IOException("Read-only file system")

    override suspend fun <T> write(file: Path, mustCreate: Boolean, writerAction: BufferedSink.() -> T): T =
        throw IOException("Read-only file system")

    override suspend fun appendingSink(file: Path, mustExist: Boolean): Sink =
        throw IOException("Read-only file system")

    override suspend fun createDirectory(dir: Path, mustCreate: Boolean): Unit =
        throw IOException("Read-only file system")

    override suspend fun createDirectories(dir: Path, mustCreate: Boolean): Unit =
        throw IOException("Read-only file system")

    override suspend fun atomicMove(source: Path, target: Path): Unit = throw IOException("Read-only file system")

    override suspend fun copy(source: Path, target: Path): Unit = throw IOException("Read-only file system")

    override suspend fun delete(path: Path, mustExist: Boolean): Unit = throw IOException("Read-only file system")

    override suspend fun deleteRecursively(fileOrDirectory: Path, mustExist: Boolean): Unit =
        throw IOException("Read-only file system")

    override suspend fun createSymlink(source: Path, target: Path): Unit = throw IOException("Read-only file system")

    override suspend fun openZip(zipPath: Path): AsyncFileSystem = throw IOException("Unsupported operation")

    override fun close() = Unit
}

private fun readShort(bytes: ByteArray, offset: Int): Short {
    val b0 = bytes[offset].toInt() and 0xff
    val b1 = bytes[offset + 1].toInt() and 0xff
    return ((b1 shl 8) or b0).toShort()
}

private fun readInt(bytes: ByteArray, offset: Int): Int {
    val b0 = bytes[offset].toInt() and 0xff
    val b1 = bytes[offset + 1].toInt() and 0xff
    val b2 = bytes[offset + 2].toInt() and 0xff
    val b3 = bytes[offset + 3].toInt() and 0xff
    return (b3 shl 24) or (b2 shl 16) or (b1 shl 8) or b0
}

@OptIn(ExperimentalWasmJsInterop::class)
@Suppress("UNUSED_PARAMETER")
internal fun decompressDeflateRaw(compressedBytes: JsAny): Promise<JsAny> = js(
    """
    (async () => {
        const stream = new ReadableStream({
            start(controller) {
                controller.enqueue(compressedBytes);
                controller.close();
            }
        });
        const decompressedStream = stream.pipeThrough(new DecompressionStream("deflate-raw"));
        const response = new Response(decompressedStream);
        const buffer = await response.arrayBuffer();
        return new Int8Array(buffer);
    })()
    """,
)
