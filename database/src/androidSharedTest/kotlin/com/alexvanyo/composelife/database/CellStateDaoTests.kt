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
import app.cash.turbine.test
import app.cash.turbine.withTurbineTimeout
import dagger.hilt.android.testing.HiltAndroidRule
import dagger.hilt.android.testing.HiltAndroidTest
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.test.TestDispatcher
import kotlinx.coroutines.test.runTest
import org.junit.Before
import org.junit.Rule
import org.junit.Test
import org.junit.runner.RunWith
import javax.inject.Inject
import kotlin.test.assertEquals
import kotlin.test.assertNull
import kotlin.time.Duration.Companion.seconds

@OptIn(ExperimentalCoroutinesApi::class)
@HiltAndroidTest
@RunWith(AndroidJUnit4::class)
class CellStateDaoTests {

    @get:Rule
    val hiltAndroidRule = HiltAndroidRule(this)

    @Inject
    lateinit var cellStateDao: CellStateDao

    @Inject
    lateinit var testDispatcher: TestDispatcher

    @Before
    fun setup() {
        hiltAndroidRule.inject()
    }

    @Test
    fun get_cell_states_returns_empty_initially() = runTest(testDispatcher) {
        withTurbineTimeout(5.seconds) {
            cellStateDao.getCellStates().test {
                assertEquals(emptyList(), awaitItem())
            }
        }
    }

    @Test
    fun get_cell_states_returns_value_once_saved() = runTest(testDispatcher) {
        withTurbineTimeout(5.seconds) {
            cellStateDao.getCellStates().test {
                assertEquals(emptyList(), awaitItem())

                val insertedId = cellStateDao.upsertCellState(
                    CellStateEntity(
                        id = 0,
                        name = null,
                        description = null,
                        formatExtension = null,
                        serializedCellState = "O",
                        generation = 0,
                        wasAutosaved = true,
                    ),
                )

                assertEquals(
                    listOf(
                        CellStateEntity(
                            id = insertedId,
                            name = null,
                            description = null,
                            formatExtension = null,
                            serializedCellState = "O",
                            generation = 0,
                            wasAutosaved = true,
                        ),
                    ),
                    awaitItem(),
                )
            }
        }
    }

    @Test
    fun get_cell_states_returns_value_if_saved_before() = runTest(testDispatcher) {
        withTurbineTimeout(5.seconds) {
            val insertedId = cellStateDao.upsertCellState(
                CellStateEntity(
                    id = 0,
                    name = null,
                    description = null,
                    formatExtension = null,
                    serializedCellState = "O",
                    generation = 0,
                    wasAutosaved = true,
                ),
            )

            cellStateDao.getCellStates().test {
                assertEquals(
                    listOf(
                        CellStateEntity(
                            id = insertedId,
                            name = null,
                            description = null,
                            formatExtension = null,
                            serializedCellState = "O",
                            generation = 0,
                            wasAutosaved = true,
                        ),
                    ),
                    awaitItem(),
                )
            }
        }
    }

    @Test
    fun get_cell_states_returns_empty_once_deleted() = runTest(testDispatcher) {
        withTurbineTimeout(5.seconds) {
            cellStateDao.getCellStates().test {
                assertEquals(emptyList(), awaitItem())

                val insertedId = cellStateDao.upsertCellState(
                    CellStateEntity(
                        id = 0,
                        name = null,
                        description = null,
                        formatExtension = null,
                        serializedCellState = "O",
                        generation = 0,
                        wasAutosaved = true,
                    ),
                )

                assertEquals(
                    listOf(
                        CellStateEntity(
                            id = insertedId,
                            name = null,
                            description = null,
                            formatExtension = null,
                            serializedCellState = "O",
                            generation = 0,
                            wasAutosaved = true,
                        ),
                    ),
                    awaitItem(),
                )

                cellStateDao.deleteCellState(insertedId)

                assertEquals(emptyList(), awaitItem())
            }
        }
    }

    @Test
    fun get_cell_state_by_id_returns_null_initially() = runTest(testDispatcher) {
        withTurbineTimeout(5.seconds) {
            cellStateDao.getCellStateById(123).test {
                assertNull(awaitItem())
            }
        }
    }

    @Test
    fun get_cell_state_by_id_returns_value_once_saved() = runTest(testDispatcher) {
        withTurbineTimeout(5.seconds) {
            cellStateDao.getCellStateById(123).test {
                assertNull(awaitItem())

                cellStateDao.upsertCellState(
                    CellStateEntity(
                        id = 123,
                        name = null,
                        description = null,
                        formatExtension = null,
                        serializedCellState = "O",
                        generation = 0,
                        wasAutosaved = true,
                    ),
                )

                assertEquals(
                    CellStateEntity(
                        id = 123,
                        name = null,
                        description = null,
                        formatExtension = null,
                        serializedCellState = "O",
                        generation = 0,
                        wasAutosaved = true,
                    ),
                    awaitItem(),
                )
            }
        }
    }

    @Test
    fun get_cell_state_by_id_returns_value_if_saved_before() = runTest(testDispatcher) {
        withTurbineTimeout(5.seconds) {
            val insertedId = cellStateDao.upsertCellState(
                CellStateEntity(
                    id = 0,
                    name = null,
                    description = null,
                    formatExtension = null,
                    serializedCellState = "O",
                    generation = 0,
                    wasAutosaved = true,
                ),
            )

            cellStateDao.getCellStateById(insertedId).test {
                assertEquals(
                    CellStateEntity(
                        id = insertedId,
                        name = null,
                        description = null,
                        formatExtension = null,
                        serializedCellState = "O",
                        generation = 0,
                        wasAutosaved = true,
                    ),
                    awaitItem(),
                )
            }
        }
    }

    @Test
    fun get_cell_states_returns_null_once_deleted() = runTest(testDispatcher) {
        withTurbineTimeout(5.seconds) {
            val insertedId = cellStateDao.upsertCellState(
                CellStateEntity(
                    id = 0,
                    name = null,
                    description = null,
                    formatExtension = null,
                    serializedCellState = "O",
                    generation = 0,
                    wasAutosaved = true,
                ),
            )

            cellStateDao.getCellStateById(insertedId).test {
                assertEquals(
                    CellStateEntity(
                        id = insertedId,
                        name = null,
                        description = null,
                        formatExtension = null,
                        serializedCellState = "O",
                        generation = 0,
                        wasAutosaved = true,
                    ),
                    awaitItem(),
                )

                cellStateDao.deleteCellState(insertedId)

                assertNull(awaitItem())
            }
        }
    }

    @Test
    fun get_most_recent_autosaved_cell_state_returns_null_initially() = runTest(testDispatcher) {
        withTurbineTimeout(5.seconds) {
            cellStateDao.getMostRecentAutosavedCellState().test {
                assertNull(awaitItem())
            }
        }
    }

    @Test
    fun get_most_recent_autosaved_cell_state_returns_null_if_not_autosaved_before() = runTest(testDispatcher) {
        withTurbineTimeout(5.seconds) {
            cellStateDao.upsertCellState(
                CellStateEntity(
                    id = 0,
                    name = null,
                    description = null,
                    formatExtension = null,
                    serializedCellState = "O",
                    generation = 0,
                    wasAutosaved = false,
                ),
            )

            cellStateDao.getMostRecentAutosavedCellState().test {
                assertEquals(null, awaitItem())
            }
        }
    }

    @Test
    fun get_most_recent_autosaved_cell_state_returns_value_if_autosaved_before() = runTest(testDispatcher) {
        withTurbineTimeout(5.seconds) {
            val insertedId = cellStateDao.upsertCellState(
                CellStateEntity(
                    id = 0,
                    name = null,
                    description = null,
                    formatExtension = null,
                    serializedCellState = "O",
                    generation = 0,
                    wasAutosaved = true,
                ),
            )

            cellStateDao.getMostRecentAutosavedCellState().test {
                assertEquals(
                    CellStateEntity(
                        id = insertedId,
                        name = null,
                        description = null,
                        formatExtension = null,
                        serializedCellState = "O",
                        generation = 0,
                        wasAutosaved = true,
                    ),
                    awaitItem(),
                )
            }
        }
    }

    @Test
    fun get_most_recent_autosaved_cell_state_returns_value_once_autosaved() = runTest(testDispatcher) {
        withTurbineTimeout(5.seconds) {
            cellStateDao.getMostRecentAutosavedCellState().test {
                assertNull(awaitItem())

                val insertedId = cellStateDao.upsertCellState(
                    CellStateEntity(
                        id = 0,
                        name = null,
                        description = null,
                        formatExtension = null,
                        serializedCellState = "O",
                        generation = 0,
                        wasAutosaved = true,
                    ),
                )

                assertEquals(
                    CellStateEntity(
                        id = insertedId,
                        name = null,
                        description = null,
                        formatExtension = null,
                        serializedCellState = "O",
                        generation = 0,
                        wasAutosaved = true,
                    ),
                    awaitItem(),
                )
            }
        }
    }
}
