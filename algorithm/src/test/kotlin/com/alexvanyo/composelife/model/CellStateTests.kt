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
import org.junit.jupiter.api.extension.ExtensionContext
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.ArgumentsProvider
import org.junit.jupiter.params.provider.ArgumentsSource
import java.util.stream.Stream
import kotlin.test.assertEquals
import kotlin.test.assertTrue

class CellStateTests {

    class CellStateFactory(
        val cellStateName: String,
        val factory: (cellState: CellState) -> CellState,
    )

    class CellStateTestArguments(
        val cellStateFactory: CellStateFactory,
    ) {
        override fun toString(): String = "cell state type: ${cellStateFactory.cellStateName}"
    }

    class CellStateTestProvider : ArgumentsProvider {
        override fun provideArguments(context: ExtensionContext?): Stream<out Arguments> =
            listOf(
                CellStateFactory("Default cell state") { CellState(it.aliveCells.toSet()) },
                CellStateFactory("Hash life cell state") { it.toHashLifeCellState() }
            )
                .map(::CellStateTestArguments)
                .stream()
                .map(Arguments::of)
    }

    @ParameterizedTest(name = "{displayName}: {0}")
    @ArgumentsSource(CellStateTestProvider::class)
    fun `conversion is correct`(args: CellStateTestArguments) {
        val expectedCellState = """
            |.O.O.O
            |.O.O..
            |.O....
            |......
        """.trimMargin().toCellState()

        val testCellState = args.cellStateFactory.factory(expectedCellState)

        assertEquals(expectedCellState, testCellState)
    }

    @ParameterizedTest(name = "{displayName}: {0}")
    @ArgumentsSource(CellStateTestProvider::class)
    fun `size of empty cell state is correct`(args: CellStateTestArguments) {
        val testCellState = args.cellStateFactory.factory(
            """
            |.O.O.O
            |.O.O..
            |.O....
            |......
            """.trimMargin().toCellState()
        )

        assertEquals(6, testCellState.aliveCells.size)
    }

    @ParameterizedTest(name = "{displayName}: {0}")
    @ArgumentsSource(CellStateTestProvider::class)
    fun `offset by is correct`(args: CellStateTestArguments) {
        val testCellState = args.cellStateFactory.factory(
            """
            |.O.O.O
            |.O.O..
            |.O....
            |......
            """.trimMargin().toCellState()
        ).offsetBy(IntOffset(2, 2))

        assertEquals(
            """
            |.O.O.O
            |.O.O..
            |.O....
            |......
            """.trimMargin().toCellState(topLeftOffset = IntOffset(2, 2)),
            testCellState
        )
    }

    @ParameterizedTest(name = "{displayName}: {0}")
    @ArgumentsSource(CellStateTestProvider::class)
    fun `contains all is correct`(args: CellStateTestArguments) {
        val testCellState = args.cellStateFactory.factory(
            """
            |.O.O.O
            |.O.O..
            |.O....
            |......
            """.trimMargin().toCellState()
        )

        assertTrue(
            testCellState.aliveCells.containsAll(
                setOf(
                    IntOffset(1, 0),
                    IntOffset(3, 0),
                    IntOffset(5, 0),
                    IntOffset(1, 1),
                    IntOffset(3, 1),
                    IntOffset(1, 2)
                )
            )
        )
    }

    @ParameterizedTest(name = "{displayName}: {0}")
    @ArgumentsSource(CellStateTestProvider::class)
    fun `with offset is correct`(args: CellStateTestArguments) {
        val testCellState = args.cellStateFactory.factory(
            """
            |.O.O.O
            |.O.O..
            |.O....
            |......
            """.trimMargin().toCellState()
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
            testCellState
        )
    }
}
