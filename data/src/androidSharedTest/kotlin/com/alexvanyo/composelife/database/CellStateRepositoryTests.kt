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

package com.alexvanyo.composelife.database

import androidx.test.ext.junit.runners.AndroidJUnit4
import com.alexvanyo.composelife.data.CellStateRepository
import com.alexvanyo.composelife.data.model.CellStateMetadata
import com.alexvanyo.composelife.data.model.SaveableCellState
import com.alexvanyo.composelife.model.toCellState
import com.alexvanyo.composelife.test.BaseHiltTest
import dagger.hilt.android.testing.HiltAndroidTest
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.flow.first
import kotlinx.coroutines.test.TestDispatcher
import org.junit.runner.RunWith
import javax.inject.Inject
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotNull
import kotlin.test.assertNull

@OptIn(ExperimentalCoroutinesApi::class)
@HiltAndroidTest
@RunWith(AndroidJUnit4::class)
class CellStateRepositoryTests : BaseHiltTest() {

    @Inject
    lateinit var cellStateRepository: CellStateRepository

    @Inject
    lateinit var cellStateDao: CellStateDao

    @Inject
    lateinit var testDispatcher: TestDispatcher

    @Test
    fun get_autosaved_cell_state_returns_null_initially() = runAppTest(testDispatcher) {
        assertNull(cellStateRepository.getAutosavedCellState())
    }

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
                ),
            ),
            actualCellState,
        )

        val mostRecentCellStateEntity = cellStateDao.getMostRecentAutosavedCellState().first()

        assertNotNull(mostRecentCellStateEntity)
        assertEquals(
            CellStateEntity(
                id = insertedId,
                name = "name",
                description = "description",
                formatExtension = "cells",
                serializedCellState = "O",
                generation = 123,
                wasAutosaved = true,
            ),
            mostRecentCellStateEntity,
        )
    }
}
