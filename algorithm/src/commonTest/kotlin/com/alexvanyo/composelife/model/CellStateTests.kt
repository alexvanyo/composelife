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

package com.alexvanyo.composelife.model

import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.IntRect
import com.google.testing.junit.testparameterinjector.TestParameter
import com.google.testing.junit.testparameterinjector.TestParameterInjector
import org.junit.runner.RunWith
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue

@RunWith(TestParameterInjector::class)
class CellStateTests {

    class CellStateFactory(
        val cellStateName: String,
        val factory: (cellState: CellState) -> CellState,
    ) {
        override fun toString(): String = cellStateName

        class Provider : TestParameter.TestParameterValuesProvider {
            override fun provideValues() =
                listOf(
                    CellStateFactory("Default cell state") { CellState(it.aliveCells.toSet()) },
                    CellStateFactory("Hash life cell state") { it.toHashLifeCellState() },
                )
        }
    }

    @TestParameter(valuesProvider = CellStateFactory.Provider::class)
    lateinit var cellStateFactory: CellStateFactory

    @Test
    fun conversion_is_correct() {
        val expectedCellState = """
            |.O.O.O
            |.O.O..
            |.O....
            |......
        """.trimMargin().toCellState()

        val testCellState = cellStateFactory.factory(expectedCellState)

        assertEquals(expectedCellState, testCellState)
    }

    @Test
    fun size_of_empty_cell_state_is_correct() {
        val testCellState = cellStateFactory.factory(
            """
            |.O.O.O
            |.O.O..
            |.O....
            |......
            """.trimMargin().toCellState(),
        )

        assertEquals(6, testCellState.aliveCells.size)
    }

    @Test
    fun offset_by_is_correct() {
        val testCellState = cellStateFactory.factory(
            """
            |.O.O.O
            |.O.O..
            |.O....
            |......
            """.trimMargin().toCellState(),
        ).offsetBy(IntOffset(2, 2))

        assertEquals(
            """
            |.O.O.O
            |.O.O..
            |.O....
            |......
            """.trimMargin().toCellState(topLeftOffset = IntOffset(2, 2)),
            testCellState,
        )
    }

    @Test
    fun contains_all_is_correct() {
        val testCellState = cellStateFactory.factory(
            """
            |.O.O.O
            |.O.O..
            |.O....
            |......
            """.trimMargin().toCellState(),
        )

        assertTrue(
            testCellState.aliveCells.containsAll(
                setOf(
                    IntOffset(1, 0),
                    IntOffset(3, 0),
                    IntOffset(5, 0),
                    IntOffset(1, 1),
                    IntOffset(3, 1),
                    IntOffset(1, 2),
                ),
            ),
        )

        assertFalse(
            testCellState.aliveCells.containsAll(
                setOf(
                    IntOffset(0, 0),
                ),
            ),
        )
    }

    @Test
    fun with_offset_is_correct() {
        val testCellState = cellStateFactory.factory(
            """
            |.O.O.O
            |.O.O..
            |.O....
            |......
            """.trimMargin().toCellState(),
        ).offsetBy(IntOffset(2, 2)).withCell(IntOffset.Zero, true)

        assertEquals(
            """
            |O.......
            |........
            |...O.O.O
            |...O.O..
            |...O....
            |........
            """.trimMargin().toCellState(),
            testCellState,
        )
    }

    @Test
    fun bounding_box_is_correct() {
        val testCellState = cellStateFactory.factory(
            """
            |.O.O.O
            |.O.O..
            |.O....
            |......
            """.trimMargin().toCellState(),
        )

        assertEquals(
            IntRect(
                left = 1,
                top = 0,
                right = 5,
                bottom = 2,
            ),
            testCellState.boundingBox,
        )
    }

    @Test
    fun empty_bounding_box_is_correct() {
        val testCellState = cellStateFactory.factory(emptyCellState())

        assertEquals(
            IntRect.Zero,
            testCellState.boundingBox,
        )
    }
}
