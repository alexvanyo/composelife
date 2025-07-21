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

package com.alexvanyo.composelife.data

import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateMapOf
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.setValue
import androidx.compose.runtime.snapshots.Snapshot
import app.cash.sqldelight.async.coroutines.awaitAsList
import app.cash.sqldelight.coroutines.asFlow
import app.cash.sqldelight.coroutines.mapToList
import com.alexvanyo.composelife.data.model.PatternCollection
import com.alexvanyo.composelife.database.CellStateQueries
import com.alexvanyo.composelife.database.PatternCollectionId
import com.alexvanyo.composelife.database.PatternCollectionQueries
import com.alexvanyo.composelife.database.awaitLastInsertedId
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.filesystem.PersistedDataPath
import com.alexvanyo.composelife.logging.Logger
import com.alexvanyo.composelife.resourcestate.ResourceState
import com.alexvanyo.composelife.resourcestate.map
import com.alexvanyo.composelife.updatable.PowerableUpdatable
import com.alexvanyo.composelife.updatable.Updatable
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.ContributesBinding
import dev.zacsweers.metro.ContributesIntoSet
import dev.zacsweers.metro.Inject
import dev.zacsweers.metro.SingleIn
import dev.zacsweers.metro.binding
import io.ktor.client.HttpClient
import io.ktor.client.plugins.onDownload
import io.ktor.client.request.prepareGet
import io.ktor.client.statement.bodyAsChannel
import io.ktor.utils.io.readBuffer
import kotlinx.coroutines.async
import kotlinx.coroutines.awaitAll
import kotlinx.coroutines.coroutineScope
import kotlinx.coroutines.ensureActive
import kotlinx.coroutines.flow.catch
import kotlinx.coroutines.flow.collect
import kotlinx.coroutines.flow.onEach
import kotlinx.coroutines.flow.retry
import kotlinx.coroutines.sync.Mutex
import kotlinx.coroutines.sync.withLock
import kotlinx.coroutines.withContext
import kotlinx.io.okio.asOkioSource
import okio.ByteString.Companion.toByteString
import okio.FileSystem
import okio.HashingSink
import okio.Path
import okio.Path.Companion.toPath
import okio.blackholeSink
import okio.buffer
import okio.openZip
import okio.use
import kotlin.time.Clock

@Inject
@ContributesBinding(AppScope::class, binding = binding<PatternCollectionRepository>())
@ContributesIntoSet(AppScope::class, binding = binding<Updatable>())
@SingleIn(AppScope::class)
@Suppress("LongParameterList")
class PatternCollectionRepositoryImpl(
    private val dispatchers: ComposeLifeDispatchers,
    private val cellStateQueries: CellStateQueries,
    private val patternCollectionQueries: PatternCollectionQueries,
    private val fileSystem: FileSystem,
    httpClient: Lazy<HttpClient>,
    private val logger: Logger,
    private val clock: Clock,
    @PersistedDataPath persistedDataPath: Lazy<Path>,
) : PatternCollectionRepository, Updatable {
    private val httpClient by httpClient
    private val persistedDataPath by persistedDataPath

    private var databaseCollections:
        ResourceState<List<com.alexvanyo.composelife.database.PatternCollection>> by mutableStateOf(
            ResourceState.Loading,
        )

    private val synchronizationInformation = mutableStateMapOf<PatternCollectionId, Boolean>()

    override val collections: ResourceState<List<PatternCollection>> get() =
        databaseCollections.map { databasePatternCollections ->
            databasePatternCollections.map { databasePatternCollection ->
                PatternCollection(
                    id = databasePatternCollection.id,
                    sourceUrl = databasePatternCollection.sourceUrl,
                    lastSuccessfulSynchronizationTimestamp =
                    databasePatternCollection.lastSuccessfulSynchronizationTimestamp,
                    lastUnsuccessfulSynchronizationTimestamp =
                    databasePatternCollection.lastUnsuccessfulSynchronizationTimestamp,
                    synchronizationFailureMessage = databasePatternCollection.synchronizationFailureMessage,
                    isSynchronizing = synchronizationInformation.getOrDefault(databasePatternCollection.id, false),
                )
            }
        }

    private val powerableUpdatable = PowerableUpdatable {
        patternCollectionQueries.getPatternCollections()
            .asFlow()
            .mapToList(dispatchers.IO)
            .retry()
            .onEach { databasePatternCollections ->
                Snapshot.withMutableSnapshot {
                    databaseCollections = ResourceState.Success(databasePatternCollections)
                }
            }
            .catch { throwable ->
                Snapshot.withMutableSnapshot {
                    databaseCollections = ResourceState.Failure(throwable)
                }
            }
            .collect()

        error("getPatternCollections can not complete normally")
    }

    private val synchronizeMutex = Mutex()

    override suspend fun update(): Nothing = powerableUpdatable.update()

    override suspend fun observePatternCollections(): Nothing = powerableUpdatable.press()

    override suspend fun addPatternCollection(
        sourceUrl: String,
    ): PatternCollectionId = withContext(dispatchers.IO) {
        patternCollectionQueries.transactionWithResult {
            patternCollectionQueries.insertPatternCollection(
                sourceUrl = sourceUrl,
                lastSuccessfulSynchronizationTimestamp = null,
                lastUnsuccessfulSynchronizationTimestamp = null,
                synchronizationFailureMessage = null,
            )
            patternCollectionQueries.awaitLastInsertedId()
        }
    }

    override suspend fun deletePatternCollection(
        patternCollectionId: PatternCollectionId,
    ): Unit = withContext(dispatchers.IO) {
        patternCollectionQueries.transactionWithResult {
            patternCollectionQueries.deletePatternCollection(patternCollectionId)
        }
        val archivePathParent = persistedDataPath /
            collectionsFolder /
            patternCollectionId.value.toString()
        fileSystem.deleteRecursively(archivePathParent)
    }

    override suspend fun synchronizePatternCollections(): Boolean =
        synchronizeMutex.withLock {
            try {
                synchronizationInformation.clear()
                // Fetch the current list of pattern collections
                val databasePatternCollections = withContext(dispatchers.IO) {
                    patternCollectionQueries.getPatternCollections().awaitAsList()
                }
                databasePatternCollections.forEach { databasePatternCollection ->
                    synchronizationInformation[databasePatternCollection.id] = true
                }

                // In parallel, synchronize each of the pattern collections we have
                return coroutineScope {
                    databasePatternCollections.map { databasePatternCollection ->
                        async {
                            synchronizePatternCollection(databasePatternCollection).also {
                                synchronizationInformation[databasePatternCollection.id] = false
                            }
                        }
                    }
                        .awaitAll()
                        .all { it }
                }
            } finally {
                synchronizationInformation.clear()
            }
        }

    @Suppress("ThrowsCount", "TooGenericExceptionCaught", "LongMethod", "CyclomaticComplexMethod")
    private suspend fun synchronizePatternCollection(
        databasePatternCollection: com.alexvanyo.composelife.database.PatternCollection,
    ): Boolean = withContext(dispatchers.IO) {
        val sourceUrl = databasePatternCollection.sourceUrl
        val archivePathParent = persistedDataPath /
            collectionsFolder /
            databasePatternCollection.id.value.toString()

        val archivePath = archivePathParent / archiveFileName
        val archiveHashPath = archivePathParent / archiveHashFileName

        try {
            fileSystem.createDirectories(archivePathParent)

            httpClient
                .prepareGet(sourceUrl) {
                    onDownload { bytesSentTotal: Long, contentLength: Long? ->
                        // TODO: Make this visible in the UI
                        if (contentLength != null) {
                            logger.d {
                                "Progress: ${ "%.1f".format(bytesSentTotal * 100f / contentLength) }%"
                            }
                        }
                    }
                }
                .execute { response ->
                    fileSystem.sink(archivePath).buffer().use { sink ->
                        response.bodyAsChannel().readBuffer().asOkioSource().buffer().use { source ->
                            source.readAll(sink)
                        }
                    }
                }
        } catch (exception: Exception) {
            coroutineContext.ensureActive()
            logger.e(exception) { "Failed fetching" }

            patternCollectionQueries.updatePatternCollection(
                id = databasePatternCollection.id,
                sourceUrl = databasePatternCollection.sourceUrl,
                lastSuccessfulSynchronizationTimestamp =
                databasePatternCollection.lastSuccessfulSynchronizationTimestamp,
                lastUnsuccessfulSynchronizationTimestamp = clock.now(),
                synchronizationFailureMessage = "Failed fetching",
            )

            return@withContext false
        }

        try {
            val hashingSink = HashingSink.sha256(blackholeSink())
            val hash = hashingSink.buffer().use { sink ->
                fileSystem.source(archivePath).buffer().use { source ->
                    source.readAll(sink)
                    hashingSink.hash
                }
            }
            val oldHash = if (fileSystem.exists(archiveHashPath)) {
                fileSystem.source(archiveHashPath).buffer().use { source ->
                    source.readByteArray().toByteString()
                }
            } else {
                null
            }

            if (hash == oldHash) {
                logger.d("Archive file had same hash")
            } else {
                // The hash has changed, extract all contained patterns
                val archiveFileSystem = fileSystem.openZip(archivePath)
                val filesToExtract = archiveFileSystem.listRecursively("/".toPath()).filterNot {
                    it.toFile().isDirectory
                }
                filesToExtract.forEach { file ->
                    logger.d("Found file: ${file.name}")
                    val extractedFile = archivePathParent / extractedPatternsFolder / file.relativeTo("/".toPath())
                    extractedFile.parent?.let(fileSystem::createDirectories)
                    fileSystem.sink(extractedFile).buffer().use { sink ->
                        archiveFileSystem.source(file).buffer().use { source ->
                            source.readAll(sink)
                        }
                    }
                }
                val extractedFiles = filesToExtract.map { file ->
                    archivePathParent / extractedPatternsFolder / file.relativeTo("/".toPath())
                }.toSet()

                // Synchronize the cell states with the updated pattern collection
                synchronizeCellStateWithPatternCollection(
                    patternCollectionId = databasePatternCollection.id,
                    extractedFiles = extractedFiles,
                )

                // Update the hash after processing everything
                fileSystem.sink(archiveHashPath).buffer().use { sink ->
                    sink.write(hash)
                }
            }
        } catch (exception: Exception) {
            coroutineContext.ensureActive()
            logger.e(exception) { "Failed processing archive" }

            patternCollectionQueries.updatePatternCollection(
                id = databasePatternCollection.id,
                sourceUrl = databasePatternCollection.sourceUrl,
                lastSuccessfulSynchronizationTimestamp =
                databasePatternCollection.lastSuccessfulSynchronizationTimestamp,
                lastUnsuccessfulSynchronizationTimestamp = clock.now(),
                synchronizationFailureMessage = "Failed processing archive",
            )

            return@withContext false
        }

        patternCollectionQueries.updatePatternCollection(
            id = databasePatternCollection.id,
            sourceUrl = databasePatternCollection.sourceUrl,
            lastSuccessfulSynchronizationTimestamp = clock.now(),
            lastUnsuccessfulSynchronizationTimestamp = null,
            synchronizationFailureMessage = null,
        )

        true
    }

    private suspend fun synchronizeCellStateWithPatternCollection(
        patternCollectionId: PatternCollectionId,
        extractedFiles: Set<Path>,
    ) = withContext(dispatchers.IO) {
        logger.d {
            "synchronizing cell states for pattern collection $patternCollectionId " +
                "with extracted files $extractedFiles"
        }
        val cellStates =
            cellStateQueries.getCellStatesByPatternCollectionId(patternCollectionId).executeAsList()
        cellStates.forEach { databaseCellState ->
            val serializedCellStateFile = databaseCellState.serializedCellStateFile?.toPath()
            if (serializedCellStateFile != null) {
                if (serializedCellStateFile !in extractedFiles) {
                    logger.d { "$serializedCellStateFile was removed from archive, deleting from cell states" }
                    // Delete the cell state before deleting the underlying file to avoid a race where the
                    // file no longer exists
                    cellStateQueries.deleteCellState(databaseCellState.id)
                    fileSystem.delete(persistedDataPath / serializedCellStateFile)
                } else {
                    // TODO: Update metadata for updated pattern with the same file
                }
            }
        }
        val serializedCellStateFiles = cellStates.mapNotNull { it.serializedCellStateFile?.toPath() }.toSet()
        (extractedFiles - serializedCellStateFiles).forEach { newlyExtractedFile ->
            cellStateQueries.insertCellState(
                name = null,
                description = null,
                formatExtension = newlyExtractedFile.toString().substringAfterLast(".", ""),
                serializedCellState = null,
                serializedCellStateFile = newlyExtractedFile.relativeTo(persistedDataPath).toString(),
                generation = 0,
                wasAutosaved = false,
                patternCollectionId = patternCollectionId,
            )
        }
    }
}

private const val collectionsFolder = "PatternCollections"
private const val archiveFileName = "archive.zip"
private const val archiveHashFileName = "archive.sha256"
private const val extractedPatternsFolder = "extracted"
