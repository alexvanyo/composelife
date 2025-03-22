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
import com.alexvanyo.composelife.database.CellState
import com.alexvanyo.composelife.database.CellStateQueries
import com.alexvanyo.composelife.dispatchers.GeneralTestDispatcher
import com.alexvanyo.composelife.filesystem.PersistedDataPath
import com.alexvanyo.composelife.model.toCellState
import com.alexvanyo.composelife.scopes.ApplicationGraph
import com.alexvanyo.composelife.test.BaseInjectTest
import kotlinx.coroutines.test.TestDispatcher
import okio.Path
import okio.Path.Companion.toPath
import okio.fakefilesystem.FakeFileSystem
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.asContribution
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotNull
import kotlin.test.assertNull
import kotlin.uuid.Uuid

@ContributesTo(AppScope::class)
interface CellStateRepositoryTestsEntryPoint {
    val cellStateRepository: CellStateRepository
    val cellStateQueries: CellStateQueries
    @GeneralTestDispatcher val generalTestDispatcher: TestDispatcher
    val fakeFileSystem: FakeFileSystem
    @PersistedDataPath val persistedDataPath: Path
}

// TODO: Replace with asContribution()
internal val ApplicationGraph.cellStateRepositoryTestsEntryPoint: CellStateRepositoryTestsEntryPoint get() =
    this as CellStateRepositoryTestsEntryPoint

class CellStateRepositoryTests : BaseInjectTest(
    { globalGraph.asContribution<ApplicationGraph.Factory>().create(it) },
) {
    private val entryPoint get() = applicationGraph.cellStateRepositoryTestsEntryPoint

    private val cellStateRepository get() = entryPoint.cellStateRepository

    private val cellStateQueries get() = entryPoint.cellStateQueries

    private val testDispatcher get() = entryPoint.generalTestDispatcher

    private val fakeFileSystem get() = entryPoint.fakeFileSystem

    private val persistedDataPath get() = entryPoint.persistedDataPath

    @Test
    fun get_autosaved_cell_state_returns_null_initially() = runAppTest(testDispatcher) {
        assertNull(cellStateRepository.getAutosavedCellState())
    }

    @Suppress("LongMethod")
    @Test
    fun save_autosaved_cell_state_then_get_returns_new_cell_state() = runAppTest(testDispatcher) {
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

        val mostRecentCellStateEntity = cellStateQueries.getMostRecentAutosavedCellState().executeAsOne()

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
}
