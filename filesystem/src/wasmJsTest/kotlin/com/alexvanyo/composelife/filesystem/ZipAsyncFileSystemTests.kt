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

package com.alexvanyo.composelife.filesystem

import com.alexvanyo.composelife.dispatchers.TestComposeLifeDispatchers
import kotlinx.coroutines.await
import kotlinx.coroutines.test.StandardTestDispatcher
import kotlinx.coroutines.test.runTest
import okio.Path.Companion.toPath
import kotlin.js.Promise
import kotlin.test.Test
import kotlin.test.assertContentEquals
import kotlin.test.assertEquals
import kotlin.test.assertTrue

class ZipAsyncFileSystemTests {

    private val testDispatcher = StandardTestDispatcher()
    private val dispatchers = TestComposeLifeDispatchers(testDispatcher, testDispatcher)

    @Test
    fun stored_zip_unzipping_works() = runTest(testDispatcher) {
        val file1Content = "Hello, world!".encodeToByteArray()
        val file2Content = "Short content".encodeToByteArray()

        val zipBytes = buildZipBytes(
            entries = listOf(
                "hello.txt" to file1Content,
                "nested/folder/short.txt" to file2Content,
            ),
            deflate = false,
        )

        val archive = ZipArchive.parse(zipBytes)
        val fileSystem = ZipAsyncFileSystem(dispatchers, archive)

        // Verify existence of entries
        assertTrue(fileSystem.exists("hello.txt".toPath()))
        assertTrue(fileSystem.exists("nested/folder/short.txt".toPath()))
        assertTrue(fileSystem.exists("nested/folder".toPath()))
        assertTrue(fileSystem.exists("nested".toPath()))

        // Verify file contents
        assertContentEquals(file1Content, fileSystem.read("hello.txt".toPath()) { readByteArray() })
        assertContentEquals(file2Content, fileSystem.read("nested/folder/short.txt".toPath()) { readByteArray() })

        // Verify listing
        val rootList = fileSystem.list("/".toPath())
        assertEquals(
            listOf("/hello.txt".toPath(), "/nested".toPath()).sorted(),
            rootList.sorted(),
        )

        val nestedList = fileSystem.list("/nested/folder".toPath())
        assertEquals(
            listOf("/nested/folder/short.txt".toPath()),
            nestedList,
        )
    }

    @Test
    fun deflated_zip_unzipping_works() = runTest(testDispatcher) {
        val file1Content = "Deflated Hello, world! Deflated Hello, world! Deflated Hello, world!".encodeToByteArray()
        val file2Content = "Another deflated entry".encodeToByteArray()

        val zipBytes = buildZipBytes(
            entries = listOf(
                "hello_deflated.txt" to file1Content,
                "nested/deflated.txt" to file2Content,
            ),
            deflate = true,
        )

        val archive = ZipArchive.parse(zipBytes)
        val fileSystem = ZipAsyncFileSystem(dispatchers, archive)

        // Verify existence
        assertTrue(fileSystem.exists("hello_deflated.txt".toPath()))
        assertTrue(fileSystem.exists("nested/deflated.txt".toPath()))

        // Verify contents
        assertContentEquals(file1Content, fileSystem.read("hello_deflated.txt".toPath()) { readByteArray() })
        assertContentEquals(file2Content, fileSystem.read("nested/deflated.txt".toPath()) { readByteArray() })
    }

    private suspend fun buildZipBytes(entries: List<Pair<String, ByteArray>>, deflate: Boolean): ByteArray {
        val buffer = okio.Buffer()
        val localHeaders = mutableListOf<Pair<Long, ByteArray>>()

        for (entry in entries) {
            val nameBytes = entry.first.encodeToByteArray()
            val originalData = entry.second
            val compressedData = if (deflate) {
                val compressedJsArray = createInt8ArrayFromKotlin(originalData)
                val decompressedJsArray = compressDeflateRaw(compressedJsArray).await()
                val length = getInt8ArrayLength(decompressedJsArray)
                val byteArray = ByteArray(length)
                for (i in 0 until length) {
                    byteArray[i] = getInt8ArrayValue(decompressedJsArray, i)
                }
                byteArray
            } else {
                originalData
            }

            val compressionMethod: Short = if (deflate) 8 else 0
            val offset = buffer.size

            buffer.writeIntLe(0x04034b50)
            buffer.writeShortLe(20)
            buffer.writeShortLe(0)
            buffer.writeShortLe(compressionMethod)
            buffer.writeShortLe(0)
            buffer.writeShortLe(0)
            buffer.writeIntLe(0) // CRC32 placeholder
            buffer.writeIntLe(compressedData.size)
            buffer.writeIntLe(originalData.size)
            buffer.writeShortLe(nameBytes.size.toShort())
            buffer.writeShortLe(0) // Extra field length
            buffer.write(nameBytes)
            buffer.write(compressedData)

            localHeaders.add(
                offset to buildCentralDirectoryHeader(
                    name = entry.first,
                    compressionMethod = compressionMethod,
                    compressedSize = compressedData.size,
                    uncompressedSize = originalData.size,
                    localHeaderOffset = offset.toInt(),
                ),
            )
        }

        val cdOffset = buffer.size
        var cdSize = 0L
        for (header in localHeaders) {
            buffer.write(header.second)
            cdSize += header.second.size
        }

        buffer.writeIntLe(0x06054b50)
        buffer.writeShortLe(0)
        buffer.writeShortLe(0)
        buffer.writeShortLe(entries.size.toShort())
        buffer.writeShortLe(entries.size.toShort())
        buffer.writeIntLe(cdSize.toInt())
        buffer.writeIntLe(cdOffset.toInt())
        buffer.writeShortLe(0) // Comment length

        return buffer.readByteArray()
    }

    private fun buildCentralDirectoryHeader(
        name: String,
        compressionMethod: Short,
        compressedSize: Int,
        uncompressedSize: Int,
        localHeaderOffset: Int,
    ): ByteArray {
        val buffer = okio.Buffer()
        val nameBytes = name.encodeToByteArray()
        buffer.writeIntLe(0x02014b50)
        buffer.writeShortLe(20)
        buffer.writeShortLe(20)
        buffer.writeShortLe(0)
        buffer.writeShortLe(compressionMethod)
        buffer.writeShortLe(0)
        buffer.writeShortLe(0)
        buffer.writeIntLe(0) // CRC32
        buffer.writeIntLe(compressedSize)
        buffer.writeIntLe(uncompressedSize)
        buffer.writeShortLe(nameBytes.size.toShort())
        buffer.writeShortLe(0)
        buffer.writeShortLe(0)
        buffer.writeShortLe(0)
        buffer.writeShortLe(0)
        buffer.writeIntLe(0)
        buffer.writeIntLe(localHeaderOffset)
        buffer.write(nameBytes)

        return buffer.readByteArray()
    }

    private fun okio.Buffer.writeShortLe(value: Short) {
        writeByte(value.toInt() and 0xff)
        writeByte((value.toInt() ushr 8) and 0xff)
    }

    private fun okio.Buffer.writeIntLe(value: Int) {
        writeByte(value and 0xff)
        writeByte((value ushr 8) and 0xff)
        writeByte((value ushr 16) and 0xff)
        writeByte((value ushr 24) and 0xff)
    }
}

@OptIn(ExperimentalWasmJsInterop::class)
@Suppress("UNUSED_PARAMETER")
internal fun compressDeflateRaw(bytes: JsAny): Promise<JsAny> = js(
    """
    (async () => {
        const stream = new ReadableStream({
            start(controller) {
                controller.enqueue(bytes);
                controller.close();
            }
        });
        const compressedStream = stream.pipeThrough(new CompressionStream("deflate-raw"));
        const response = new Response(compressedStream);
        const buffer = await response.arrayBuffer();
        return new Int8Array(buffer);
    })()
    """,
)
