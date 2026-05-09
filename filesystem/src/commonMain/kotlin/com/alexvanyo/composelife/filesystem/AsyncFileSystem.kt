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

import okio.BufferedSink
import okio.BufferedSource
import okio.Closeable
import okio.FileHandle
import okio.FileMetadata
import okio.IOException
import okio.Path
import okio.Sink
import okio.Source

@Suppress("TooManyFunctions")
interface AsyncFileSystem : Closeable {

    /**
     * Resolves [path] against the current working directory and symlinks in this file system. The
     * returned path identifies the same file as [path], but with an absolute path that does not
     * include any symbolic links.
     *
     * This is similar to `File.getCanonicalFile()` on the JVM and `realpath` on POSIX. Unlike
     * `File.getCanonicalFile()`, this throws if the file doesn't exist.
     *
     * @throws IOException if [path] cannot be resolved. This will occur if the file doesn't exist,
     *     if the current working directory doesn't exist or is inaccessible, or if another failure
     *     occurs while resolving the path.
     */
    @Throws(IOException::class)
    suspend fun canonicalize(path: Path): Path

    /**
     * Returns metadata of the file, directory, or object identified by [path].
     *
     * @throws IOException if [path] does not exist or its metadata cannot be read.
     */
    @Throws(IOException::class)
    suspend fun metadata(path: Path): FileMetadata

    /**
     * Returns metadata of the file, directory, or object identified by [path]. This returns null if
     * there is no file at [path].
     *
     * @throws IOException if [path] cannot be accessed due to a connectivity problem, permissions
     *     problem, or other issue.
     */
    @Throws(IOException::class)
    suspend fun metadataOrNull(path: Path): FileMetadata?

    /**
     * Returns true if [path] identifies an object on this file system.
     *
     * @throws IOException if [path] cannot be accessed due to a connectivity problem, permissions
     *     problem, or other issue.
     */
    @Throws(IOException::class)
    suspend fun exists(path: Path): Boolean

    /**
     * Returns the children of [dir]. The returned list is sorted using natural ordering. If [dir] is
     * a relative path, the returned elements will also be relative paths. If it is an absolute path,
     * the returned elements will also be absolute paths.
     *
     * Note that a path does not need to be a [directory][FileMetadata.isDirectory] for this function
     * to return successfully. For example, mounted storage devices may have child files but do not
     * identify themselves as directories.
     *
     * @throws IOException if [dir] does not exist or cannot be listed. A path cannot be listed if the
     *     current process doesn't have access to [dir], or if there's a loop of symbolic links, or if
     *     any name is too long.
     */
    @Throws(IOException::class)
    suspend fun list(dir: Path): List<Path>

    /**
     * Returns the children of the directory identified by [dir]. The returned list is sorted using
     * natural ordering. If [dir] is a relative path, the returned elements will also be relative
     * paths. If it is an absolute path, the returned elements will also be absolute paths.
     *
     * This returns null if [dir] does not exist or cannot be listed. A directory cannot be listed if
     * the current process doesn't have access to [dir], or if there's a loop of symbolic links, or if
     * any name is too long.
     */
    suspend fun listOrNull(dir: Path): List<Path>?

    /**
     * Returns a sequence that **lazily** traverses the children of [dir] using repeated calls to
     * [list]. If none of [dir]'s children are directories this returns the same elements as [list].
     *
     * The returned sequence visits the tree of files in depth-first order. Parent paths are returned
     * before their children.
     *
     * Note that [listRecursively] does not throw exceptions but the returned sequence does. When it
     * is iterated, the returned sequence throws a [FileNotFoundException] if [dir] does not exist, or
     * an [IOException] if [dir] cannot be listed.
     *
     * @param followSymlinks true to follow symlinks while traversing the children. If [dir] itself is
     *     a symlink it will be followed even if this parameter is false.
     */
    suspend fun listRecursively(dir: Path, followSymlinks: Boolean = false): Sequence<Path>

    /**
     * Returns a handle to read [file]. This will fail if the file doesn't already exist.
     *
     * @throws IOException if [file] does not exist, is not a file, or cannot be accessed. A file
     *     cannot be accessed if the current process doesn't have sufficient permissions for [file],
     *     if there's a loop of symbolic links, or if any name is too long.
     */
    @Throws(IOException::class)
    suspend fun openReadOnly(file: Path): FileHandle

    /**
     * Returns a handle to read and write [file]. This will create the file if it doesn't already
     * exist.
     *
     * @param mustCreate true to throw an [IOException] instead of overwriting an existing file.
     *     This is equivalent to `O_EXCL` on POSIX and `CREATE_NEW` on Windows.
     * @param mustExist true to throw an [IOException] instead of creating a new file. This is
     *     equivalent to `r+` on POSIX and `OPEN_EXISTING` on Windows.
     * @throws IOException if [file] is not a file, or cannot be accessed. A file cannot be accessed
     *     if the current process doesn't have sufficient reading and writing permissions for [file],
     *     if there's a loop of symbolic links, or if any name is too long.
     */
    @Throws(IOException::class)
    suspend fun openReadWrite(
        file: Path,
        mustCreate: Boolean = false,
        mustExist: Boolean = false,
    ): FileHandle

    /**
     * Returns a source that reads the bytes of [file] from beginning to end.
     *
     * @throws IOException if [file] does not exist, is not a file, or cannot be read. A file cannot
     *     be read if the current process doesn't have access to [file], if there's a loop of symbolic
     *     links, or if any name is too long.
     */
    @Throws(IOException::class)
    suspend fun source(file: Path): Source

    /**
     * Creates a source to read [file], executes [readerAction] to read it, and then closes the
     * source. This is a compact way to read the contents of a file.
     */
    @Throws(IOException::class)
    suspend fun <T> read(file: Path, readerAction: BufferedSource.() -> T): T

    /**
     * Returns a sink that writes bytes to [file] from beginning to end. If [file] already exists it
     * will be replaced with the new data.
     *
     * @param mustCreate true to throw an [IOException] instead of overwriting an existing file.
     *     This is equivalent to `O_EXCL` on POSIX and `CREATE_NEW` on Windows.
     *
     * @throws IOException if [file] cannot be written. A file cannot be written if its enclosing
     *     directory does not exist, if the current process doesn't have access to [file], if there's
     *     a loop of symbolic links, or if any name is too long.
     */
    @Throws(IOException::class)
    suspend fun sink(file: Path, mustCreate: Boolean = false): Sink

    /**
     * Creates a sink to write [file], executes [writerAction] to write it, and then closes the sink.
     * This is a compact way to write a file.
     *
     * @param mustCreate true to throw an [IOException] instead of overwriting an existing file.
     *     This is equivalent to `O_EXCL` on POSIX and `CREATE_NEW` on Windows.
     */
    @Throws(IOException::class)
    suspend fun <T> write(
        file: Path,
        mustCreate: Boolean = false,
        writerAction: BufferedSink.() -> T,
    ): T

    /**
     * Returns a sink that appends bytes to the end of [file], creating it if it doesn't already
     * exist.
     *
     * @param mustExist true to throw an [IOException] instead of creating a new file. This is
     *     equivalent to `r+` on POSIX and `OPEN_EXISTING` on Windows.
     *
     * @throws IOException if [file] cannot be written. A file cannot be written if its enclosing
     *     directory does not exist, if the current process doesn't have access to [file], if there's
     *     a loop of symbolic links, or if any name is too long.
     */
    @Throws(IOException::class)
    suspend fun appendingSink(file: Path, mustExist: Boolean = false): Sink

    /**
     * Creates a directory at the path identified by [dir].
     *
     * @param mustCreate true to throw an [IOException] if the directory already exists.
     * @throws IOException if [dir]'s parent does not exist, is not a directory, or cannot be written.
     *     A directory cannot be created if the current process doesn't have access, if there's a loop
     *     of symbolic links, or if any name is too long.
     */
    @Throws(IOException::class)
    suspend fun createDirectory(dir: Path, mustCreate: Boolean = false)

    /**
     * Creates a directory at the path identified by [dir], and any enclosing parent path directories,
     * recursively.
     *
     * @param mustCreate true to throw an [IOException] instead of overwriting an existing directory.
     * @throws IOException if any [metadata] or [createDirectory] operation fails.
     */
    @Throws(IOException::class)
    suspend fun createDirectories(dir: Path, mustCreate: Boolean = false)

    /**
     * Moves [source] to [target] in-place if the underlying file system supports it. If [target]
     * exists, it is first removed. If `source == target`, this operation does nothing. This may be
     * used to move a file or a directory.
     *
     * **Only as Atomic as the Underlying File System Supports**
     *
     * FAT and NTFS file systems cannot atomically move a file over an existing file. If the target
     * file already exists, the move is performed into two steps:
     *
     *  1. Atomically delete the target file.
     *  2. Atomically rename the source file to the target file.
     *
     * The delete step and move step are each atomic but not atomic in aggregate! If this process
     * crashes, the host operating system crashes, or the hardware fails it is possible that the
     * delete step will succeed and the rename will not.
     *
     * **Entire-file or nothing**
     *
     * These are the possible results of this operation:
     *
     *  * This operation returns normally, the source file is absent, and the target file contains the
     *    data previously held by the source file. This is the success case.
     *
     *  * The operation throws an [IOException] and the file system is unchanged. For example, this
     *    occurs if this process lacks permissions to perform the move.
     *
     *  * This operation throws an [IOException], the target file is deleted, but the source file is
     *    unchanged. This is the partial failure case described above and is only possible on
     *    file systems like FAT and NTFS that do not support atomic file replacement. Typically in
     *    such cases this operation won't return at all because the process or operating system has
     *    also crashed.
     *
     * There is no failure mode where the target file holds a subset of the bytes of the source file.
     * If the rename step cannot be performed atomically, this function will throw an [IOException]
     * before attempting a move. Typically this occurs if the source and target files are on different
     * physical volumes.
     *
     * **Non-Atomic Moves**
     *
     * If you need to move files across volumes, use [copy] followed by [delete], and change your
     * application logic to recover should the copy step suffer a partial failure.
     *
     * @throws IOException if the move cannot be performed, or cannot be performed atomically. Moves
     *     fail if the source doesn't exist, if the target is not writable, if the target already
     *     exists and cannot be replaced, or if the move would cause physical or quota limits to be
     *     exceeded. This list of potential problems is not exhaustive.
     */
    @Throws(IOException::class)
    suspend fun atomicMove(source: Path, target: Path)

    /**
     * Copies all the bytes from the file at [source] to the file at [target]. This does not copy
     * file metadata like last modified time, permissions, or extended attributes.
     *
     * This function is not atomic; a failure may leave [target] in an inconsistent state. For
     * example, [target] may be empty or contain only a prefix of [source].
     *
     * @throws IOException if [source] cannot be read or if [target] cannot be written.
     */
    @Throws(IOException::class)
    suspend fun copy(source: Path, target: Path)

    /**
     * Deletes the file or directory at [path].
     *
     * @param mustExist true to throw an [IOException] if there is nothing at [path] to delete.
     * @throws IOException if there is a file or directory but it could not be deleted. Deletes fail
     *     if the current process doesn't have access, if the file system is readonly, or if [path]
     *     is a non-empty directory. This list of potential problems is not exhaustive.
     */
    @Throws(IOException::class)
    suspend fun delete(path: Path, mustExist: Boolean = false)

    /**
     * Recursively deletes all children of [fileOrDirectory] if it is a directory, then deletes
     * [fileOrDirectory] itself.
     *
     * This function does not defend against race conditions. For example, if child files are created
     * or deleted in [fileOrDirectory] while this function is executing, this may fail with an
     * [IOException].
     *
     * @param mustExist true to throw an [IOException] if there is nothing at [fileOrDirectory] to
     *     delete.
     * @throws IOException if any [metadata], [list], or [delete] operation fails.
     */
    @Throws(IOException::class)
    suspend fun deleteRecursively(fileOrDirectory: Path, mustExist: Boolean = false)

    /**
     * Creates a symbolic link at [source] that resolves to [target]. If [target] is a relative path,
     * it is relative to `source.parent`.
     *
     * @throws IOException if [source] cannot be created. This may be because it already exists
     *     or because its storage doesn't support symlinks. This list of potential problems is not
     *     exhaustive.
     */
    @Throws(IOException::class)
    suspend fun createSymlink(source: Path, target: Path)

    suspend fun openZip(zipPath: Path): AsyncFileSystem

    @Throws(IOException::class)
    override fun close()
}
