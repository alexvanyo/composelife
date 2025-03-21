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
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.setValue
import androidx.compose.runtime.snapshots.Snapshot
import app.cash.sqldelight.coroutines.asFlow
import app.cash.sqldelight.coroutines.mapToList
import com.alexvanyo.composelife.data.model.PatternCollection
import com.alexvanyo.composelife.database.PatternCollectionId
import com.alexvanyo.composelife.database.PatternCollectionQueries
import com.alexvanyo.composelife.database.executeLastInsertedId
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.filesystem.PersistedDataPath
import com.alexvanyo.composelife.logging.Logger
import com.alexvanyo.composelife.resourcestate.ResourceState
import com.alexvanyo.composelife.updatable.PowerableUpdatable
import com.alexvanyo.composelife.updatable.Updatable
import io.ktor.client.HttpClient
import io.ktor.client.plugins.onDownload
import io.ktor.client.request.prepareGet
import io.ktor.client.statement.bodyAsChannel
import io.ktor.utils.io.readBuffer
import kotlinx.coroutines.coroutineScope
import kotlinx.coroutines.ensureActive
import kotlinx.coroutines.flow.catch
import kotlinx.coroutines.flow.collect
import kotlinx.coroutines.flow.map
import kotlinx.coroutines.flow.onEach
import kotlinx.coroutines.flow.retry
import kotlinx.coroutines.launch
import kotlinx.coroutines.withContext
import kotlinx.datetime.Clock
import kotlinx.io.okio.asOkioSource
import me.tatarka.inject.annotations.Inject
import okio.ByteString.Companion.toByteString
import okio.FileSystem
import okio.HashingSink
import okio.Path
import okio.Path.Companion.toPath
import okio.blackholeSink
import okio.buffer
import okio.openZip
import okio.use
import software.amazon.lastmile.kotlin.inject.anvil.AppScope
import software.amazon.lastmile.kotlin.inject.anvil.ContributesBinding
import software.amazon.lastmile.kotlin.inject.anvil.SingleIn

@Inject
@ContributesBinding(AppScope::class, boundType = PatternCollectionRepository::class)
@ContributesBinding(AppScope::class, boundType = Updatable::class, multibinding = true)
@SingleIn(AppScope::class)
@Suppress("LongParameterList")
class PatternCollectionRepositoryImpl(
    private val dispatchers: ComposeLifeDispatchers,
    private val patternCollectionQueries: PatternCollectionQueries,
    private val fileSystem: FileSystem,
    httpClient: Lazy<HttpClient>,
    private val logger: Logger,
    private val clock: Clock,
    persistedDataPath: @PersistedDataPath Lazy<Path>,
) : PatternCollectionRepository, Updatable {
    private val httpClient by httpClient
    private val persistedDataPath by persistedDataPath

    override var collections: ResourceState<List<PatternCollection>> by mutableStateOf(ResourceState.Loading)
        private set

    private val powerableUpdatable = PowerableUpdatable {
        patternCollectionQueries.getPatternCollections()
            .asFlow()
            .mapToList(dispatchers.IO)
            .retry()
            .map { patternCollections ->
                patternCollections.map { patternCollection ->
                    PatternCollection(
                        id = patternCollection.id,
                        sourceUrl = patternCollection.sourceUrl,
                        lastSuccessfulSynchronizationTimestamp =
                            patternCollection.lastSuccessfulSynchronizationTimestamp,
                    )
                }
            }
            .onEach { patternCollections ->
                Snapshot.withMutableSnapshot {
                    collections = ResourceState.Success(patternCollections)
                }
            }
            .catch { throwable ->
                Snapshot.withMutableSnapshot {
                    collections = ResourceState.Failure(throwable)
                }
            }
            .collect()

        error("getPatternCollections can not complete normally")
    }

    override suspend fun update(): Nothing = powerableUpdatable.update()

    override suspend fun observePatternCollections(): Nothing = powerableUpdatable.press()

    override suspend fun addPatternCollection(
        sourceUrl: String,
    ): PatternCollectionId = withContext(dispatchers.IO) {
        patternCollectionQueries.transactionWithResult {
            patternCollectionQueries.insertPatternCollection(
                sourceUrl = sourceUrl,
                lastSuccessfulSynchronizationTimestamp = null,
            )
            patternCollectionQueries.executeLastInsertedId()
        }
    }

    override suspend fun deletePatternCollection(
        patternCollectionId: PatternCollectionId,
    ) = withContext(dispatchers.IO) {
        patternCollectionQueries.transactionWithResult {
            patternCollectionQueries.deletePatternCollection(patternCollectionId)
        }
    }

    override suspend fun synchronizePatternCollections() {
        // Fetch the current list of pattern collections
        val patternCollections = withContext(dispatchers.IO) {
            patternCollectionQueries.getPatternCollections().executeAsList()
        }

        // In parallel, synchronize each of the pattern collections we have
        coroutineScope {
            patternCollections.forEach { patternCollection ->
                launch {
                    synchronizePatternCollection(patternCollection)
                }
            }
        }
    }

    @Suppress("ThrowsCount", "TooGenericExceptionCaught", "LongMethod", "CyclomaticComplexMethod")
    private suspend fun synchronizePatternCollection(
        patternCollection: com.alexvanyo.composelife.database.PatternCollection,
    ) = withContext(dispatchers.IO) {
        val sourceUrl = patternCollection.sourceUrl
        val archivePathParent = persistedDataPath /
                collectionsFolder /
                patternCollection.id.value.toString()

        val archivePath = archivePathParent / archiveFileName
        val archiveHashPath = archivePathParent / archiveHashFileName

        try {
            fileSystem.createDirectories(archivePathParent)
        } catch (exception: Exception) {
            // TODO: handle I/O exceptions
            logger.e(exception) { "Failed to create directories" }
            throw exception
        } catch (throwable: Throwable) {
            coroutineContext.ensureActive()
            throw throwable
        }

        try {
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
            // TODO: handle I/O exceptions
            logger.e(exception) { "Failed fetching" }
            throw exception
        } catch (throwable: Throwable) {
            coroutineContext.ensureActive()
            throw throwable
        }

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
            fileSystem.sink(archiveHashPath).buffer().use { sink ->
                sink.write(hash)
            }

            try {
                val archiveFileSystem = fileSystem.openZip(archivePath)
                archiveFileSystem.listRecursively("/".toPath()).forEach { file ->
                    logger.d("Found file: ${file.name}")
                }
            } catch (exception: Exception) {
                // TODO: handle I/O exceptions
                logger.e(exception) { "Failed fetching" }
                throw exception
            } catch (throwable: Throwable) {
                coroutineContext.ensureActive()
                throw throwable
            }
        }

        patternCollectionQueries.updatePatternCollection(
            id = patternCollection.id,
            sourceUrl = patternCollection.sourceUrl,
            lastSuccessfulSynchronizationTimestamp = clock.now(),
        )
    }
}

private const val collectionsFolder = "PatternCollections"
private const val archiveFileName = "archive.zip"
private const val archiveHashFileName = "archive.sha256"
