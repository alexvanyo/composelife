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

import com.alexvanyo.composelife.data.model.CellStateMetadata
import com.alexvanyo.composelife.data.model.PatternCollection
import com.alexvanyo.composelife.database.CellState
import com.alexvanyo.composelife.database.CellStateQueries
import com.alexvanyo.composelife.database.PatternCollectionQueries
import com.alexvanyo.composelife.dispatchers.GeneralTestDispatcher
import com.alexvanyo.composelife.filesystem.PersistedDataPath
import com.alexvanyo.composelife.model.MacrocellCellStateSerializer
import com.alexvanyo.composelife.model.toCellState
import com.alexvanyo.composelife.network.FakeRequestHandler
import com.alexvanyo.composelife.resourcestate.ResourceState
import com.alexvanyo.composelife.scopes.ApplicationComponent
import com.alexvanyo.composelife.test.BaseInjectTest
import io.ktor.client.engine.mock.respond
import kotlin.time.Instant
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.async
import kotlinx.coroutines.launch
import kotlinx.coroutines.test.TestDispatcher
import kotlinx.coroutines.test.runCurrent
import okio.Path
import okio.Path.Companion.toPath
import okio.fakefilesystem.FakeFileSystem
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.asContribution
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotNull
import kotlin.test.assertTrue

@ContributesTo(AppScope::class)
interface PatternCollectionRepositoryTestsEntryPoint {
    val patternCollectionRepository: PatternCollectionRepository
    val patternCollectionQueries: PatternCollectionQueries
    val cellStateRepository: CellStateRepository
    val cellStateQueries: CellStateQueries
    @GeneralTestDispatcher val generalTestDispatcher: TestDispatcher
    val fakeRequestHandler: FakeRequestHandler
    val fakeFileSystem: FakeFileSystem
    @PersistedDataPath val persistedDataPath: Path
}

@OptIn(ExperimentalCoroutinesApi::class)
class PatternCollectionRepositoryTests : BaseInjectTest(
    { globalGraph.asContribution<ApplicationComponent.Factory>().create(it) },
) {
    private val entryPoint get() = applicationComponent as PatternCollectionRepositoryTestsEntryPoint

    private val patternCollectionRepository: PatternCollectionRepository
        get() = entryPoint.patternCollectionRepository

    private val cellStateRepository get() = entryPoint.cellStateRepository

    private val patternCollectionQueries get() = entryPoint.patternCollectionQueries

    private val cellStateQueries get() = entryPoint.cellStateQueries

    private val testDispatcher get() = entryPoint.generalTestDispatcher

    private val fakeRequestHandler: FakeRequestHandler get() = entryPoint.fakeRequestHandler

    private val fakeFileSystem get() = entryPoint.fakeFileSystem

    private val persistedDataPath get() = entryPoint.persistedDataPath

    @Test
    fun pattern_collection_is_empty_initially() = runAppTest(testDispatcher) {
        backgroundScope.launch {
            patternCollectionRepository.observePatternCollections()
        }

        runCurrent()

        assertEquals(
            ResourceState.Success(emptyList()),
            patternCollectionRepository.collections,
        )
    }

    @Test
    fun adding_pattern_collection_updates_collections() = runAppTest(testDispatcher) {
        backgroundScope.launch {
            patternCollectionRepository.observePatternCollections()
        }

        val patternCollectionId = patternCollectionRepository.addPatternCollection(
            sourceUrl = "https://alex.vanyo.dev/composelife/patterns.zip",
        )

        runCurrent()

        assertEquals(
            ResourceState.Success(
                listOf(
                    PatternCollection(
                        id = patternCollectionId,
                        sourceUrl = "https://alex.vanyo.dev/composelife/patterns.zip",
                        lastSuccessfulSynchronizationTimestamp = null,
                        lastUnsuccessfulSynchronizationTimestamp = null,
                        synchronizationFailureMessage = null,
                        isSynchronizing = false,
                    )
                )
            ),
            patternCollectionRepository.collections,
        )
    }

    @Test
    fun after_adding_pattern_collection_synchronization_updates() = runAppTest(testDispatcher) {
        backgroundScope.launch {
            patternCollectionRepository.observePatternCollections()
        }

        val patternCollectionId = patternCollectionRepository.addPatternCollection(
            sourceUrl = "https://alex.vanyo.dev/composelife/patterns.zip",
        )

        val synchronizationJob = async {
            patternCollectionRepository.synchronizePatternCollections()
        }

        runCurrent()

        assertEquals(
            ResourceState.Success(
                listOf(
                    PatternCollection(
                        id = patternCollectionId,
                        sourceUrl = "https://alex.vanyo.dev/composelife/patterns.zip",
                        lastSuccessfulSynchronizationTimestamp = null,
                        lastUnsuccessfulSynchronizationTimestamp = null,
                        synchronizationFailureMessage = null,
                        isSynchronizing = true,
                    )
                )
            ),
            patternCollectionRepository.collections,
        )

        fakeRequestHandler.addRequestHandler { request ->
            assertEquals("https://alex.vanyo.dev/composelife/patterns.zip", request.url.toString())
            respond(
                this::class.java
                    .getResource("/patternfiles/patterns.zip")!!
                    .readBytes()
            )
        }

        assertTrue(synchronizationJob.await())

        assertEquals(
            ResourceState.Success(
                listOf(
                    PatternCollection(
                        id = patternCollectionId,
                        sourceUrl = "https://alex.vanyo.dev/composelife/patterns.zip",
                        lastSuccessfulSynchronizationTimestamp = Instant.fromEpochSeconds(0),
                        lastUnsuccessfulSynchronizationTimestamp = null,
                        synchronizationFailureMessage = null,
                        isSynchronizing = false,
                    )
                )
            ),
            patternCollectionRepository.collections,
        )

        // Validate that the cell state was extracted on disk
        val cellStateEntity = cellStateQueries
            .getCellStatesByPatternCollectionId(patternCollectionId)
            .executeAsOne()

        assertNotNull(cellStateEntity)
        val serializedCellStateFile = cellStateEntity.serializedCellStateFile
        assertNotNull(serializedCellStateFile)
        assertEquals(
            "PatternCollections/${patternCollectionId.value}/extracted/pulsarpixeldisplay.mc",
            serializedCellStateFile,
        )
        val expectedPath = serializedCellStateFile.toPath()
        assertEquals(
            CellState(
                id = cellStateEntity.id,
                name = null,
                description = null,
                generation = 0,
                formatExtension = "mc",
                serializedCellState = null,
                serializedCellStateFile = expectedPath.toString(),
                wasAutosaved = false,
                patternCollectionId = patternCollectionId,
            ),
            cellStateEntity,
        )
        assertEquals(
            setOf(
                "PatternCollections".toPath(),
                "PatternCollections/${patternCollectionId.value}".toPath(),
                "PatternCollections/${patternCollectionId.value}/archive.zip".toPath(),
                "PatternCollections/${patternCollectionId.value}/archive.sha256".toPath(),
                "PatternCollections/${patternCollectionId.value}/extracted".toPath(),
                "PatternCollections/${patternCollectionId.value}/extracted/pulsarpixeldisplay.mc".toPath(),
            ),
            fakeFileSystem.listRecursively(persistedDataPath)
                .map { it.relativeTo(persistedDataPath) }
                .toSet(),
        )
        assertEquals(
            this::class.java
                .getResource("/patternfiles/pulsarpixeldisplay.mc")!!
                .readText(),
            fakeFileSystem.read(persistedDataPath / expectedPath) { readUtf8() },
        )

        // Validate that the cell state is queryable through the cell state repository
        val cellStates = cellStateRepository.getCellStates()
        assertEquals(1, cellStates.size)
        val cellStateId = cellStates.first().cellStateMetadata.id
        assertEquals(
            CellStateMetadata(
                id = cellStateId,
                name = null,
                description = null,
                generation = 0,
                wasAutosaved = false,
                patternCollectionId = patternCollectionId,
            ),
            cellStates.first().cellStateMetadata,
        )
        assertEquals(
            this::class.java
                .getResource("/patternfiles/pulsarpixeldisplay.mc")!!
                .readText()
                .toCellState(fixedFormatCellStateSerializer = MacrocellCellStateSerializer),
            cellStates.first().cellState
        )
    }

    @Test
    fun deleting_pattern_collection_removes_files() = runAppTest(testDispatcher) {
        backgroundScope.launch {
            patternCollectionRepository.observePatternCollections()
        }

        val patternCollectionId = patternCollectionRepository.addPatternCollection(
            sourceUrl = "https://alex.vanyo.dev/composelife/patterns.zip",
        )

        val synchronizationJob = async {
            patternCollectionRepository.synchronizePatternCollections()
        }

        runCurrent()

        fakeRequestHandler.addRequestHandler { request ->
            assertEquals("https://alex.vanyo.dev/composelife/patterns.zip", request.url.toString())
            respond(
                this::class.java
                    .getResource("/patternfiles/patterns.zip")!!
                    .readBytes()
            )
        }
        assertTrue(synchronizationJob.await())

        patternCollectionRepository.deletePatternCollection(patternCollectionId)

        runCurrent()

        assertEquals(
            ResourceState.Success(emptyList(),),
            patternCollectionRepository.collections,
        )
        assertEquals(
            emptyList(),
            cellStateRepository.getCellStates(),
        )
        assertEquals(
            setOf(
                "PatternCollections".toPath(),
            ),
            fakeFileSystem.listRecursively(persistedDataPath)
                .map { it.relativeTo(persistedDataPath) }
                .toSet(),
        )
    }

    @Test
    fun deleting_pattern_from_archive_removes_files() = runAppTest(testDispatcher) {
        backgroundScope.launch {
            patternCollectionRepository.observePatternCollections()
        }

        val patternCollectionId = patternCollectionRepository.addPatternCollection(
            sourceUrl = "https://alex.vanyo.dev/composelife/patterns.zip",
        )

        val synchronizationJob = async {
            patternCollectionRepository.synchronizePatternCollections()
        }

        runCurrent()

        assertEquals(
            ResourceState.Success(
                listOf(
                    PatternCollection(
                        id = patternCollectionId,
                        sourceUrl = "https://alex.vanyo.dev/composelife/patterns.zip",
                        lastSuccessfulSynchronizationTimestamp = null,
                        lastUnsuccessfulSynchronizationTimestamp = null,
                        synchronizationFailureMessage = null,
                        isSynchronizing = true,
                    )
                )
            ),
            patternCollectionRepository.collections,
        )

        fakeRequestHandler.addRequestHandler { request ->
            assertEquals("https://alex.vanyo.dev/composelife/patterns.zip", request.url.toString())
            respond(
                this::class.java
                    .getResource("/patternfiles/patterns.zip")!!
                    .readBytes()
            )
        }

        assertTrue(synchronizationJob.await())

        assertEquals(
            ResourceState.Success(
                listOf(
                    PatternCollection(
                        id = patternCollectionId,
                        sourceUrl = "https://alex.vanyo.dev/composelife/patterns.zip",
                        lastSuccessfulSynchronizationTimestamp = Instant.fromEpochSeconds(0),
                        lastUnsuccessfulSynchronizationTimestamp = null,
                        synchronizationFailureMessage = null,
                        isSynchronizing = false,
                    )
                )
            ),
            patternCollectionRepository.collections,
        )

        fakeRequestHandler.addRequestHandler { request ->
            assertEquals("https://alex.vanyo.dev/composelife/patterns.zip", request.url.toString())
            respond(
                this::class.java
                    .getResource("/patternfiles/empty.zip")!!
                    .readBytes()
            )
        }

        assertTrue(patternCollectionRepository.synchronizePatternCollections())

        // Validate that the cell state was deleted
        val cellStates = cellStateRepository.getCellStates()
        assertEquals(emptyList(), cellStates)
        assertEquals(
            setOf(
                "PatternCollections".toPath(),
                "PatternCollections/${patternCollectionId.value}".toPath(),
                "PatternCollections/${patternCollectionId.value}/archive.zip".toPath(),
                "PatternCollections/${patternCollectionId.value}/archive.sha256".toPath(),
                "PatternCollections/${patternCollectionId.value}/extracted".toPath(),
            ),
            fakeFileSystem.listRecursively(persistedDataPath)
                .map { it.relativeTo(persistedDataPath) }
                .toSet(),
        )
    }
}
