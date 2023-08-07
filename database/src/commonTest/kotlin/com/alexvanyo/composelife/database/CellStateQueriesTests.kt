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

import app.cash.sqldelight.coroutines.asFlow
import app.cash.sqldelight.coroutines.mapToList
import app.cash.sqldelight.coroutines.mapToOneOrNull
import app.cash.turbine.test
import app.cash.turbine.withTurbineTimeout
import com.alexvanyo.composelife.kmpandroidrunner.KmpAndroidJUnit4
import com.alexvanyo.composelife.test.BaseInjectTest
import kotlinx.coroutines.test.runTest
import org.junit.runner.RunWith
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNull
import kotlin.time.Duration.Companion.seconds

@RunWith(KmpAndroidJUnit4::class)
class CellStateQueriesTests : BaseInjectTest<TestComposeLifeApplicationComponent>(
    { TestComposeLifeApplicationComponent.create() }
) {
    private val cellStateQueries get() = applicationComponent.cellStateQueries

    private val testDispatcher get() = applicationComponent.testDispatcher

    @Test
    fun get_cell_states_returns_empty_initially() = runAppTest(testDispatcher) {
        withTurbineTimeout(60.seconds) {
            cellStateQueries.getCellStates().asFlow().mapToList(testDispatcher).test {
                assertEquals(emptyList(), awaitItem())
            }
        }
    }

    @Test
    fun get_cell_states_returns_value_once_saved() = runAppTest(testDispatcher) {
        withTurbineTimeout(60.seconds) {
            cellStateQueries.getCellStates().asFlow().mapToList(testDispatcher).test {
                assertEquals(emptyList(), awaitItem())

                val insertedId = cellStateQueries.transactionWithResult {
                    cellStateQueries.insertCellState(
                        name = null,
                        description = null,
                        formatExtension = null,
                        serializedCellState = "O",
                        generation = 0,
                        wasAutosaved = true,
                    )
                    cellStateQueries.lastInsertedRowId().executeAsOne()
                }

                assertEquals(
                    listOf(
                        CellState(
                            id = CellStateId(insertedId),
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
        withTurbineTimeout(60.seconds) {
            val insertedId = cellStateQueries.transactionWithResult {
                cellStateQueries.insertCellState(
                    name = null,
                    description = null,
                    formatExtension = null,
                    serializedCellState = "O",
                    generation = 0,
                    wasAutosaved = true,
                )
                cellStateQueries.lastInsertedRowId().executeAsOne()
            }

            cellStateQueries.getCellStates().asFlow().mapToList(testDispatcher).test {
                assertEquals(
                    listOf(
                        CellState(
                            id = CellStateId(insertedId),
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
    fun get_cell_states_returns_empty_once_deleted() = runAppTest(testDispatcher) {
        withTurbineTimeout(60.seconds) {
            cellStateQueries.getCellStates().asFlow().mapToList(testDispatcher).test {
                assertEquals(emptyList(), awaitItem())

                val insertedId = cellStateQueries.transactionWithResult {
                    cellStateQueries.insertCellState(
                        name = null,
                        description = null,
                        formatExtension = null,
                        serializedCellState = "O",
                        generation = 0,
                        wasAutosaved = true,
                    )
                    cellStateQueries.lastInsertedRowId().executeAsOne()
                }

                assertEquals(
                    listOf(
                        CellState(
                            id = CellStateId(insertedId),
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

                cellStateQueries.deleteCellState(CellStateId(insertedId))

                assertEquals(emptyList(), awaitItem())
            }
        }
    }

    @Test
    fun get_cell_state_by_id_returns_null_initially() = runAppTest(testDispatcher) {
        withTurbineTimeout(60.seconds) {
            cellStateQueries.getCellStateById(CellStateId(123)).asFlow().mapToOneOrNull(testDispatcher).test {
                assertNull(awaitItem())
            }
        }
    }

    @Test
    fun get_cell_state_by_id_returns_value_if_saved_before() = runAppTest(testDispatcher) {
        withTurbineTimeout(60.seconds) {
            val insertedId = cellStateQueries.transactionWithResult {
                cellStateQueries.insertCellState(
                    name = null,
                    description = null,
                    formatExtension = null,
                    serializedCellState = "O",
                    generation = 0,
                    wasAutosaved = true,
                )
                cellStateQueries.lastInsertedRowId().executeAsOne()
            }

            cellStateQueries.getCellStateById(CellStateId(insertedId)).asFlow().mapToOneOrNull(testDispatcher).test {
                assertEquals(
                    CellState(
                        id = CellStateId(insertedId),
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
    fun get_cell_states_returns_null_once_deleted() = runAppTest(testDispatcher) {
        withTurbineTimeout(60.seconds) {
            val insertedId = cellStateQueries.transactionWithResult {
                cellStateQueries.insertCellState(
                    name = null,
                    description = null,
                    formatExtension = null,
                    serializedCellState = "O",
                    generation = 0,
                    wasAutosaved = true,
                )
                cellStateQueries.lastInsertedRowId().executeAsOne()
            }

            cellStateQueries.getCellStateById(CellStateId(insertedId)).asFlow().mapToOneOrNull(testDispatcher).test {
                assertEquals(
                    CellState(
                        id = CellStateId(insertedId),
                        name = null,
                        description = null,
                        formatExtension = null,
                        serializedCellState = "O",
                        generation = 0,
                        wasAutosaved = true,
                    ),
                    awaitItem(),
                )

                cellStateQueries.deleteCellState(CellStateId(insertedId))

                assertNull(awaitItem())
            }
        }
    }

    @Test
    fun get_most_recent_autosaved_cell_state_returns_null_initially() = runAppTest(testDispatcher) {
        withTurbineTimeout(60.seconds) {
            cellStateQueries.getMostRecentAutosavedCellState().asFlow().mapToOneOrNull(testDispatcher).test {
                assertNull(awaitItem())
            }
        }
    }

    @Test
    fun get_most_recent_autosaved_cell_state_returns_null_if_not_autosaved_before() = runAppTest(testDispatcher) {
        withTurbineTimeout(60.seconds) {
            cellStateQueries.transactionWithResult {
                cellStateQueries.insertCellState(
                    name = null,
                    description = null,
                    formatExtension = null,
                    serializedCellState = "O",
                    generation = 0,
                    wasAutosaved = false,
                )
                cellStateQueries.lastInsertedRowId().executeAsOne()
            }

            cellStateQueries.getMostRecentAutosavedCellState().asFlow().mapToOneOrNull(testDispatcher).test {
                assertNull(awaitItem())
            }
        }
    }

    @Test
    fun get_most_recent_autosaved_cell_state_returns_value_if_autosaved_before() = runAppTest(testDispatcher) {
        withTurbineTimeout(60.seconds) {
            val insertedId = cellStateQueries.transactionWithResult {
                cellStateQueries.insertCellState(
                    name = null,
                    description = null,
                    formatExtension = null,
                    serializedCellState = "O",
                    generation = 0,
                    wasAutosaved = true,
                )
                cellStateQueries.lastInsertedRowId().executeAsOne()
            }

            cellStateQueries.getMostRecentAutosavedCellState().asFlow().mapToOneOrNull(testDispatcher).test {
                assertEquals(
                    CellState(
                        id = CellStateId(insertedId),
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
    fun get_most_recent_autosaved_cell_state_returns_value_once_autosaved() = runAppTest(testDispatcher) {
        withTurbineTimeout(60.seconds) {
            cellStateQueries.getMostRecentAutosavedCellState().asFlow().mapToOneOrNull(testDispatcher).test {
                assertNull(awaitItem())

                val insertedId = cellStateQueries.transactionWithResult {
                    cellStateQueries.insertCellState(
                        name = null,
                        description = null,
                        formatExtension = null,
                        serializedCellState = "O",
                        generation = 0,
                        wasAutosaved = true,
                    )
                    cellStateQueries.lastInsertedRowId().executeAsOne()
                }

                assertEquals(
                    CellState(
                        id = CellStateId(insertedId),
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
