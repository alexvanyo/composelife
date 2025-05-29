/*
 * Copyright 2022 The Android Open Source Project
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

import com.alexvanyo.composelife.data.model.CellStateMetadata
import com.alexvanyo.composelife.data.model.SaveableCellState
import com.alexvanyo.composelife.database.CellStateId
import com.alexvanyo.composelife.database.CellStateQueries
import com.alexvanyo.composelife.database.executeLastInsertedId
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.filesystem.PersistedDataPath
import com.alexvanyo.composelife.model.CellState
import com.alexvanyo.composelife.model.CellStateFormat
import com.alexvanyo.composelife.model.DeserializationResult
import com.alexvanyo.composelife.model.FlexibleCellStateSerializer
import com.alexvanyo.composelife.model.fromFileExtension
import kotlinx.coroutines.withContext
import kotlinx.datetime.Clock
import kotlinx.datetime.Instant
import me.tatarka.inject.annotations.Inject
import okio.FileSystem
import okio.Path
import okio.Path.Companion.toPath
import okio.buffer
import okio.use
import software.amazon.lastmile.kotlin.inject.anvil.AppScope
import software.amazon.lastmile.kotlin.inject.anvil.ContributesBinding
import kotlin.time.Duration
import kotlin.uuid.Uuid

@Inject
@ContributesBinding(AppScope::class)
class CellStateRepositoryImpl(
    private val flexibleCellStateSerializer: FlexibleCellStateSerializer,
    private val cellStateQueries: CellStateQueries,
    private val dispatchers: ComposeLifeDispatchers,
    private val fileSystem: FileSystem,
    persistedDataPath: @PersistedDataPath Lazy<Path>,
    private val clock: Clock,
) : CellStateRepository {
    private val persistedDataPath by persistedDataPath

    override suspend fun autosaveCellState(saveableCellState: SaveableCellState): CellStateId {
        val fileExtension = "rle"
        val serializedCellStateUniqueId = Uuid.random()
        val serializedCellStateFile = autosavedCellStatesFolder.toPath() / "$serializedCellStateUniqueId.rle"
        val file = persistedDataPath / serializedCellStateFile
        writeCellStateToFile(
            fileSystem = fileSystem,
            serializer = flexibleCellStateSerializer,
            cellState = saveableCellState.cellState,
            file = file,
            format = CellStateFormat.FixedFormat.RunLengthEncoding,
        )

        val insertedId: CellStateId = withContext(dispatchers.IO) {
            cellStateQueries.transactionWithResult {
                if (saveableCellState.cellStateMetadata.id == null) {
                    cellStateQueries.insertCellState(
                        name = saveableCellState.cellStateMetadata.name,
                        description = saveableCellState.cellStateMetadata.description,
                        formatExtension = fileExtension,
                        serializedCellState = null,
                        serializedCellStateFile = serializedCellStateFile.toString(),
                        generation = saveableCellState.cellStateMetadata.generation,
                        wasAutosaved = true,
                        patternCollectionId = null,
                    )
                    cellStateQueries.executeLastInsertedId()
                } else {
                    cellStateQueries.updateCellState(
                        id = saveableCellState.cellStateMetadata.id,
                        name = saveableCellState.cellStateMetadata.name,
                        description = saveableCellState.cellStateMetadata.description,
                        formatExtension = fileExtension,
                        serializedCellState = null,
                        serializedCellStateFile = serializedCellStateFile.toString(),
                        generation = saveableCellState.cellStateMetadata.generation,
                        wasAutosaved = true,
                        patternCollectionId = null,
                    )
                    saveableCellState.cellStateMetadata.id
                }
            }
        }

        return insertedId
    }

    override suspend fun getAutosavedCellState(): SaveableCellState? {
        val cellState = withContext(dispatchers.IO) {
            cellStateQueries.getMostRecentAutosavedCellState().executeAsOneOrNull()
        } ?: return null
        check(cellState.wasAutosaved)

        val serializedCellStateFile = cellState.serializedCellStateFile
        val format = CellStateFormat.fromFileExtension(cellState.formatExtension)

        val deserializationResult = if (serializedCellStateFile == null) {
            flexibleCellStateSerializer.deserializeToCellState(
                format = format,
                lines = checkNotNull(cellState.serializedCellState) {
                    "No serialized cell state or saved file!"
                }.lineSequence(),
            )
        } else {
            val file = persistedDataPath / serializedCellStateFile
            readCellStateFromFile(
                fileSystem = fileSystem,
                serializer = flexibleCellStateSerializer,
                file = file,
                format = format,
            )
        }
        val cellStateMetadata = CellStateMetadata(
            id = cellState.id,
            name = cellState.name,
            description = cellState.description,
            generation = cellState.generation,
            wasAutosaved = cellState.wasAutosaved,
        )

        return when (deserializationResult) {
            is DeserializationResult.Successful -> SaveableCellState(
                cellState = deserializationResult.cellState,
                cellStateMetadata = cellStateMetadata,
            )
            is DeserializationResult.Unsuccessful -> null
        }
    }

    override suspend fun pruneUnusedCellStates() {
        pruneUnusedAutosavedCellStates()
    }

    private suspend fun pruneUnusedAutosavedCellStates(
        maxAge: Duration = Duration.ZERO,
    ) = withContext(dispatchers.IO) {
        // Capture the timestamp to compare duration against
        val pruningTimestamp = clock.now()
        // Get the list of all current autosaved cell states and find their corresponding files
        val currentAutosavedCellStates = cellStateQueries.getAutosavedCellStates().executeAsList()
            .mapNotNull { it.serializedCellStateFile }
            .toSet()
        fileSystem.listOrNull(persistedDataPath / autosavedCellStatesFolder)
            .orEmpty()
            .forEach { file ->
                if (file.relativeTo(persistedDataPath).toString() !in currentAutosavedCellStates) {
                    val lastModifiedTime = fileSystem
                        .metadata(file)
                        .lastModifiedAtMillis
                        ?.let(Instant::fromEpochMilliseconds) ?: pruningTimestamp
                    if (pruningTimestamp - lastModifiedTime > maxAge) {
                        fileSystem.delete(file)
                    }
                }
            }
    }
}

private suspend fun writeCellStateToFile(
    fileSystem: FileSystem,
    serializer: FlexibleCellStateSerializer,
    cellState: CellState,
    file: Path,
    format: CellStateFormat.FixedFormat,
) {
    file.parent?.let(fileSystem::createDirectories)
    fileSystem.sink(file).buffer().use { sink ->
        serializer
            .serializeToString(
                format = format,
                cellState = cellState,
            )
            .forEachIndexed { index, line ->
                if (index != 0) {
                    sink.writeUtf8("\n")
                }
                sink.writeUtf8(line)
            }
    }
}

private suspend fun readCellStateFromFile(
    fileSystem: FileSystem,
    serializer: FlexibleCellStateSerializer,
    file: Path,
    format: CellStateFormat,
): DeserializationResult =
    fileSystem.source(file).buffer().use { source ->
        serializer.deserializeToCellState(
            format = format,
            lines = generateSequence(source::readUtf8Line),
        )
    }

private const val autosavedCellStatesFolder = "AutosavedCellStates"
