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

import app.cash.sqldelight.async.coroutines.awaitAsOne
import app.cash.sqldelight.coroutines.asFlow
import app.cash.sqldelight.coroutines.mapToList
import app.cash.sqldelight.coroutines.mapToOneOrNull
import app.cash.turbine.test
import app.cash.turbine.withTurbineTimeout
import com.alexvanyo.composelife.dispatchers.GeneralTestDispatcher
import com.alexvanyo.composelife.scopes.ApplicationGraph
import com.alexvanyo.composelife.test.BaseInjectTest
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.asContribution
import kotlinx.coroutines.test.TestDispatcher
import kotlin.coroutines.EmptyCoroutineContext
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNull
import kotlin.time.Duration.Companion.seconds

@ContributesTo(AppScope::class)
interface CellStateQueriesTestsEntryPoint {
    val cellStateQueries: CellStateQueries
}

// TODO: Replace with asContribution()
internal val ApplicationGraph.cellStateQueriesTestsEntryPoint: CellStateQueriesTestsEntryPoint get() =
    this as CellStateQueriesTestsEntryPoint

class CellStateQueriesTests : BaseInjectTest(
    globalGraph.asContribution<ApplicationGraph.Factory>()::create,
) {
    private val entryPoint get() = applicationGraph.cellStateQueriesTestsEntryPoint
    private val cellStateQueries get() = entryPoint.cellStateQueries

    @Test
    fun get_cell_states_returns_empty_initially() = runAppTest {
        withTurbineTimeout(60.seconds) {
            cellStateQueries.getCellStates().asFlow().mapToList(EmptyCoroutineContext).test {
                assertEquals(emptyList(), awaitItem())
            }
        }
    }

    @Test
    fun get_cell_states_returns_value_once_saved() = runAppTest {
        withTurbineTimeout(60.seconds) {
            cellStateQueries.getCellStates().asFlow().mapToList(EmptyCoroutineContext).test {
                assertEquals(emptyList(), awaitItem())

                val insertedId = cellStateQueries.transactionWithResult {
                    cellStateQueries.insertCellState(
                        name = null,
                        description = null,
                        formatExtension = null,
                        serializedCellState = "O",
                        serializedCellStateFile = null,
                        generation = 0,
                        wasAutosaved = true,
                        patternCollectionId = null,
                    )
                    cellStateQueries.lastInsertedRowId().awaitAsOne()
                }

                assertEquals(
                    listOf(
                        CellState(
                            id = CellStateId(insertedId),
                            name = null,
                            description = null,
                            formatExtension = null,
                            serializedCellState = "O",
                            serializedCellStateFile = null,
                            generation = 0,
                            wasAutosaved = true,
                            patternCollectionId = null,
                        ),
                    ),
                    awaitItem(),
                )
            }
        }
    }

    @Test
    fun get_cell_states_returns_value_if_saved_before() = runAppTest {
        withTurbineTimeout(60.seconds) {
            val insertedId = cellStateQueries.transactionWithResult {
                cellStateQueries.insertCellState(
                    name = null,
                    description = null,
                    formatExtension = null,
                    serializedCellState = "O",
                    serializedCellStateFile = null,
                    generation = 0,
                    wasAutosaved = true,
                    patternCollectionId = null,
                )
                cellStateQueries.lastInsertedRowId().awaitAsOne()
            }

            cellStateQueries.getCellStates().asFlow().mapToList(EmptyCoroutineContext).test {
                assertEquals(
                    listOf(
                        CellState(
                            id = CellStateId(insertedId),
                            name = null,
                            description = null,
                            formatExtension = null,
                            serializedCellState = "O",
                            serializedCellStateFile = null,
                            generation = 0,
                            wasAutosaved = true,
                            patternCollectionId = null,
                        ),
                    ),
                    awaitItem(),
                )
            }
        }
    }

    @Test
    fun get_cell_states_returns_empty_once_deleted() = runAppTest {
        withTurbineTimeout(60.seconds) {
            cellStateQueries.getCellStates().asFlow().mapToList(EmptyCoroutineContext).test {
                assertEquals(emptyList(), awaitItem())

                val insertedId = cellStateQueries.transactionWithResult {
                    cellStateQueries.insertCellState(
                        name = null,
                        description = null,
                        formatExtension = null,
                        serializedCellState = "O",
                        serializedCellStateFile = null,
                        generation = 0,
                        wasAutosaved = true,
                        patternCollectionId = null,
                    )
                    cellStateQueries.lastInsertedRowId().awaitAsOne()
                }

                assertEquals(
                    listOf(
                        CellState(
                            id = CellStateId(insertedId),
                            name = null,
                            description = null,
                            formatExtension = null,
                            serializedCellState = "O",
                            serializedCellStateFile = null,
                            generation = 0,
                            wasAutosaved = true,
                            patternCollectionId = null,
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
    fun get_cell_state_by_id_returns_null_initially() = runAppTest {
        withTurbineTimeout(60.seconds) {
            cellStateQueries.getCellStateById(CellStateId(123)).asFlow().mapToOneOrNull(EmptyCoroutineContext).test {
                assertNull(awaitItem())
            }
        }
    }

    @Test
    fun get_cell_state_by_id_returns_value_if_saved_before() = runAppTest {
        withTurbineTimeout(60.seconds) {
            val insertedId = cellStateQueries.transactionWithResult {
                cellStateQueries.insertCellState(
                    name = null,
                    description = null,
                    formatExtension = null,
                    serializedCellState = "O",
                    serializedCellStateFile = null,
                    generation = 0,
                    wasAutosaved = true,
                    patternCollectionId = null,
                )
                cellStateQueries.lastInsertedRowId().awaitAsOne()
            }

            cellStateQueries.getCellStateById(
                CellStateId(insertedId),
            ).asFlow().mapToOneOrNull(EmptyCoroutineContext).test {
                assertEquals(
                    CellState(
                        id = CellStateId(insertedId),
                        name = null,
                        description = null,
                        formatExtension = null,
                        serializedCellState = "O",
                        serializedCellStateFile = null,
                        generation = 0,
                        wasAutosaved = true,
                        patternCollectionId = null,
                    ),
                    awaitItem(),
                )
            }
        }
    }

    @Test
    fun get_cell_states_returns_null_once_deleted() = runAppTest {
        withTurbineTimeout(60.seconds) {
            val insertedId = cellStateQueries.transactionWithResult {
                cellStateQueries.insertCellState(
                    name = null,
                    description = null,
                    formatExtension = null,
                    serializedCellState = "O",
                    serializedCellStateFile = null,
                    generation = 0,
                    wasAutosaved = true,
                    patternCollectionId = null,
                )
                cellStateQueries.lastInsertedRowId().awaitAsOne()
            }

            cellStateQueries.getCellStateById(
                CellStateId(insertedId),
            ).asFlow().mapToOneOrNull(EmptyCoroutineContext).test {
                assertEquals(
                    CellState(
                        id = CellStateId(insertedId),
                        name = null,
                        description = null,
                        formatExtension = null,
                        serializedCellState = "O",
                        serializedCellStateFile = null,
                        generation = 0,
                        wasAutosaved = true,
                        patternCollectionId = null,
                    ),
                    awaitItem(),
                )

                cellStateQueries.deleteCellState(CellStateId(insertedId))

                assertNull(awaitItem())
            }
        }
    }

    @Test
    fun get_most_recent_autosaved_cell_state_returns_null_initially() = runAppTest {
        withTurbineTimeout(60.seconds) {
            cellStateQueries.getMostRecentAutosavedCellState().asFlow().mapToOneOrNull(EmptyCoroutineContext).test {
                assertNull(awaitItem())
            }
        }
    }

    @Test
    fun get_most_recent_autosaved_cell_state_returns_null_if_not_autosaved_before() = runAppTest {
        withTurbineTimeout(60.seconds) {
            cellStateQueries.transactionWithResult {
                cellStateQueries.insertCellState(
                    name = null,
                    description = null,
                    formatExtension = null,
                    serializedCellState = "O",
                    serializedCellStateFile = null,
                    generation = 0,
                    wasAutosaved = false,
                    patternCollectionId = null,
                )
                cellStateQueries.lastInsertedRowId().awaitAsOne()
            }

            cellStateQueries.getMostRecentAutosavedCellState().asFlow().mapToOneOrNull(EmptyCoroutineContext).test {
                assertNull(awaitItem())
            }
        }
    }

    @Test
    fun get_most_recent_autosaved_cell_state_returns_value_if_autosaved_before() = runAppTest {
        withTurbineTimeout(60.seconds) {
            val insertedId = cellStateQueries.transactionWithResult {
                cellStateQueries.insertCellState(
                    name = null,
                    description = null,
                    formatExtension = null,
                    serializedCellState = "O",
                    serializedCellStateFile = null,
                    generation = 0,
                    wasAutosaved = true,
                    patternCollectionId = null,
                )
                cellStateQueries.lastInsertedRowId().awaitAsOne()
            }

            cellStateQueries.getMostRecentAutosavedCellState().asFlow().mapToOneOrNull(EmptyCoroutineContext).test {
                assertEquals(
                    CellState(
                        id = CellStateId(insertedId),
                        name = null,
                        description = null,
                        formatExtension = null,
                        serializedCellState = "O",
                        serializedCellStateFile = null,
                        generation = 0,
                        wasAutosaved = true,
                        patternCollectionId = null,
                    ),
                    awaitItem(),
                )
            }
        }
    }

    @Test
    fun get_most_recent_autosaved_cell_state_returns_value_once_autosaved() = runAppTest {
        withTurbineTimeout(60.seconds) {
            cellStateQueries.getMostRecentAutosavedCellState().asFlow().mapToOneOrNull(EmptyCoroutineContext).test {
                assertNull(awaitItem())

                val insertedId = cellStateQueries.transactionWithResult {
                    cellStateQueries.insertCellState(
                        name = null,
                        description = null,
                        formatExtension = null,
                        serializedCellState = "O",
                        serializedCellStateFile = null,
                        generation = 0,
                        wasAutosaved = true,
                        patternCollectionId = null,
                    )
                    cellStateQueries.lastInsertedRowId().awaitAsOne()
                }

                assertEquals(
                    CellState(
                        id = CellStateId(insertedId),
                        name = null,
                        description = null,
                        formatExtension = null,
                        serializedCellState = "O",
                        serializedCellStateFile = null,
                        generation = 0,
                        wasAutosaved = true,
                        patternCollectionId = null,
                    ),
                    awaitItem(),
                )
            }
        }
    }
}
