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

import com.alexvanyo.composelife.dispatchers.TestComposeLifeDispatchers
import kotlinx.browser.window
import kotlinx.coroutines.test.StandardTestDispatcher
import kotlinx.coroutines.test.runTest
import okio.Path
import okio.Path.Companion.toPath
import kotlin.test.Test
import kotlin.test.assertContentEquals
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue

class WebAsyncFileSystemTests {

    private val testDispatcher = StandardTestDispatcher()
    private val dispatchers = TestComposeLifeDispatchers(testDispatcher, testDispatcher)

    private val fileSystem = WebAsyncFileSystem(
        dispatchers = dispatchers,
        navigator = window.navigator,
    )

    private fun runFileSystemTest(block: suspend (Path) -> Unit) = runTest(testDispatcher) {
        val testDir = "test-dir".toPath()
        fileSystem.createDirectory(testDir)
        try {
            block(testDir)
        } finally {
            fileSystem.deleteRecursively(testDir)
        }
    }

    @Test
    fun write_and_read_file_works() = runFileSystemTest { testDir ->
        val filePath = testDir / "test.txt"
        val content = "Hello, world!".encodeToByteArray()

        fileSystem.write(filePath) {
            write(content)
        }

        assertTrue(fileSystem.exists(filePath))

        val readContent = fileSystem.read(filePath) {
            readByteArray()
        }

        assertContentEquals(content, readContent)
    }

    @Test
    fun create_directory_works() = runFileSystemTest { testDir ->
        val dirPath = testDir / "sub-dir"
        fileSystem.createDirectory(dirPath)

        assertTrue(fileSystem.exists(dirPath))
        assertTrue(fileSystem.metadata(dirPath).isDirectory)
    }

    @Test
    fun delete_file_works() = runFileSystemTest { testDir ->
        val filePath = testDir / "test-delete.txt"
        fileSystem.write(filePath) {
            write("to be deleted".encodeToByteArray())
        }

        assertTrue(fileSystem.exists(filePath))
        fileSystem.delete(filePath)
        assertFalse(fileSystem.exists(filePath))
    }

    @Test
    fun list_works() = runFileSystemTest { testDir ->
        val file1 = testDir / "file1.txt"
        val file2 = testDir / "file2.txt"

        fileSystem.write(file1) { write("1".encodeToByteArray()) }
        fileSystem.write(file2) { write("2".encodeToByteArray()) }

        val list = fileSystem.list(testDir)
        assertEquals(listOf(file1, file2), list)
    }

    @Test
    fun atomic_move_works() = runFileSystemTest { testDir ->
        val source = testDir / "source.txt"
        val target = testDir / "target.txt"
        val content = "move me".encodeToByteArray()

        fileSystem.write(source) { write(content) }
        fileSystem.atomicMove(source, target)

        assertFalse(fileSystem.exists(source))
        assertTrue(fileSystem.exists(target))
        assertContentEquals(content, fileSystem.read(target) { readByteArray() })
    }

    @Test
    fun copy_works() = runFileSystemTest { testDir ->
        val source = testDir / "source-copy.txt"
        val target = testDir / "target-copy.txt"
        val content = "copy me".encodeToByteArray()

        fileSystem.write(source) { write(content) }
        fileSystem.copy(source, target)

        assertTrue(fileSystem.exists(source))
        assertTrue(fileSystem.exists(target))
        assertContentEquals(content, fileSystem.read(target) { readByteArray() })
    }

    @Test
    fun list_recursively_works() = runFileSystemTest { testDir ->
        val dir1 = testDir / "dir1"
        val file1 = dir1 / "file1.txt"
        val dir2 = dir1 / "dir2"
        val file2 = dir2 / "file2.txt"

        fileSystem.createDirectories(dir2)
        fileSystem.write(file1) { write("1".encodeToByteArray()) }
        fileSystem.write(file2) { write("2".encodeToByteArray()) }

        val list = fileSystem.listRecursively(testDir).toList().sorted()
        val expected = listOf(dir1, file1, dir2, file2).sorted()

        assertEquals(expected, list)
    }
}
