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

import app.cash.sqldelight.async.coroutines.awaitAsOne
import com.alexvanyo.composelife.data.model.CellStateMetadata
import com.alexvanyo.composelife.data.model.SaveableCellState
import com.alexvanyo.composelife.database.CellState
import com.alexvanyo.composelife.database.CellStateQueries
import com.alexvanyo.composelife.filesystem.PersistedDataPath
import com.alexvanyo.composelife.model.toCellState
import com.alexvanyo.composelife.scopes.ApplicationGraph
import com.alexvanyo.composelife.test.BaseInjectTest
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.asContribution
import kotlinx.coroutines.delay
import okio.Path
import okio.Path.Companion.toPath
import okio.fakefilesystem.FakeFileSystem
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertNotNull
import kotlin.test.assertNull
import kotlin.test.assertTrue
import kotlin.uuid.Uuid

@ContributesTo(AppScope::class)
interface CellStateRepositoryTestsCtx {
    val cellStateRepository: CellStateRepository
    val cellStateQueries: CellStateQueries
    val fakeFileSystem: FakeFileSystem

    @PersistedDataPath val persistedDataPath: Path
}

// TODO: Replace with asContribution()
internal val ApplicationGraph.cellStateRepositoryTestsCtx: CellStateRepositoryTestsCtx get() =
    this as CellStateRepositoryTestsCtx

@Suppress("TooManyFunctions")
class CellStateRepositoryTests :
    BaseInjectTest(
        { globalGraph.asContribution<ApplicationGraph.Factory>().create(it) },
    ) {
    private val ctx get() = applicationGraph.cellStateRepositoryTestsCtx

    private val cellStateRepository get() = ctx.cellStateRepository

    private val cellStateQueries get() = ctx.cellStateQueries

    private val fakeFileSystem get() = ctx.fakeFileSystem

    private val persistedDataPath get() = ctx.persistedDataPath

    @Test
    fun get_autosaved_cell_state_returns_null_initially() = runAppTest {
        assertNull(cellStateRepository.getAutosavedCellState())
    }

    @Suppress("LongMethod")
    @Test
    fun save_autosaved_cell_state_then_get_returns_new_cell_state() = runAppTest {
        val insertedId = cellStateRepository.autosaveCellState(
            SaveableCellState(
                cellState = "O".toCellState(),
                cellStateMetadata = CellStateMetadata(
                    id = null,
                    name = "name",
                    description = "description",
                    generation = 123,
                    wasAutosaved = false,
                    patternCollectionId = null,
                ),
            ),
        )

        val actualCellState = cellStateRepository.getAutosavedCellState()

        assertNotNull(actualCellState)
        assertEquals(
            SaveableCellState(
                cellState = "O".toCellState(),
                cellStateMetadata = CellStateMetadata(
                    id = insertedId,
                    name = "name",
                    description = "description",
                    generation = 123,
                    wasAutosaved = true,
                    patternCollectionId = null,
                ),
            ),
            actualCellState,
        )

        val mostRecentCellStateEntity = cellStateQueries.getMostRecentAutosavedCellState().awaitAsOne()

        assertNotNull(mostRecentCellStateEntity)
        val serializedCellStateFile = mostRecentCellStateEntity.serializedCellStateFile
        assertNotNull(serializedCellStateFile)
        val match = Regex("AutosavedCellStates/(.*).rle").matchEntire(serializedCellStateFile)
        assertNotNull(match)
        val fileId = Uuid.parse(match.groupValues[1])
        val expectedPath = "AutosavedCellStates/$fileId.rle".toPath()
        assertEquals(
            CellState(
                id = insertedId,
                name = "name",
                description = "description",
                formatExtension = "rle",
                serializedCellState = null,
                serializedCellStateFile = expectedPath.toString(),
                generation = 123,
                wasAutosaved = true,
                patternCollectionId = null,
            ),
            mostRecentCellStateEntity,
        )
        assertEquals(
            setOf(
                "AutosavedCellStates".toPath(),
                expectedPath,
                "datastore".toPath(),
                "datastore/preferences.pb".toPath(),
            ),
            fakeFileSystem.listRecursively(persistedDataPath)
                .map { it.relativeTo(persistedDataPath) }
                .toSet(),
        )
        assertEquals(
            """
            |#R 0 0
            |x = 1, y = 1, rule = B3/S23
            |o!
            """.trimMargin(),
            fakeFileSystem.read(persistedDataPath / expectedPath) { readUtf8() },
        )
    }

    @Test
    fun get_cell_states_and_get_autosaved_cell_states_returns_saved_states() = runAppTest {
        val insertedId = cellStateRepository.autosaveCellState(
            SaveableCellState(
                cellState = "O".toCellState(),
                cellStateMetadata = CellStateMetadata(
                    id = null,
                    name = "name",
                    description = "description",
                    generation = 123,
                    wasAutosaved = false,
                    patternCollectionId = null,
                ),
            ),
        )

        val autosavedStates = cellStateRepository.getAutosavedCellStates()
        val allCellStates = cellStateRepository.getCellStates()

        val expected = SaveableCellState(
            cellState = "O".toCellState(),
            cellStateMetadata = CellStateMetadata(
                id = insertedId,
                name = "name",
                description = "description",
                generation = 123,
                wasAutosaved = true,
                patternCollectionId = null,
            ),
        )
        assertEquals(listOf(expected), autosavedStates)
        assertEquals(listOf(expected), allCellStates)
    }

    @Test
    fun get_cell_states_with_inline_serialized_state_is_correct() = runAppTest {
        cellStateQueries.insertCellState(
            name = "inline name",
            description = "inline description",
            formatExtension = "rle",
            serializedCellState = """
                |#R 0 0
                |x = 1, y = 1, rule = B3/S23
                |o!
            """.trimMargin(),
            serializedCellStateFile = null,
            generation = 42,
            wasAutosaved = true,
            patternCollectionId = null,
        )

        val autosavedStates = cellStateRepository.getAutosavedCellStates()
        assertEquals(1, autosavedStates.size)
        val state = autosavedStates.first()
        assertEquals("inline name", state.cellStateMetadata.name)
        assertEquals("inline description", state.cellStateMetadata.description)
        assertEquals(42, state.cellStateMetadata.generation)
        assertEquals("O".toCellState(), state.cellState)
    }

    @Test
    fun prune_unused_autosaved_cell_states_with_empty_folder_succeeds() = runAppTest {
        val result = cellStateRepository.pruneUnusedCellStates()
        assertTrue(result)
    }

    @Test
    fun prune_unused_autosaved_cell_states_prunes_only_old_orphaned_files() = runAppTest {
        val insertedId = cellStateRepository.autosaveCellState(
            SaveableCellState(
                cellState = "O".toCellState(),
                cellStateMetadata = CellStateMetadata(
                    id = null,
                    name = "active",
                    description = "active",
                    generation = 1,
                    wasAutosaved = false,
                    patternCollectionId = null,
                ),
            ),
        )
        val activeEntity = cellStateQueries.getCellStateById(insertedId).awaitAsOne()
        val activePath = persistedDataPath / requireNotNull(activeEntity.serializedCellStateFile)

        val oldOrphanedPath = persistedDataPath / "AutosavedCellStates/old_orphaned.rle"
        fakeFileSystem.write(oldOrphanedPath) {
            writeUtf8("old orphaned")
        }

        val pruneResult1 = cellStateRepository.pruneUnusedCellStates()
        assertTrue(pruneResult1)
        assertTrue(fakeFileSystem.exists(oldOrphanedPath))
        assertTrue(fakeFileSystem.exists(activePath))

        delay(1000)

        val pruneResult2 = cellStateRepository.pruneUnusedCellStates()
        assertTrue(pruneResult2)
        assertFalse(fakeFileSystem.exists(oldOrphanedPath))
        assertTrue(fakeFileSystem.exists(activePath))
    }
}
