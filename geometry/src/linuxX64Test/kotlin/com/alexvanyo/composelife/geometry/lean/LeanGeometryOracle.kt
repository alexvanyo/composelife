/*
 * Copyright 2026 The Android Open Source Project
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

package com.alexvanyo.composelife.geometry.lean

import com.alexvanyo.composelife.geometry.IntOffset
import com.alexvanyo.composelife.geometry.Offset
import com.alexvanyo.composelife.geometry.lean.cinterop.CellListC
import com.alexvanyo.composelife.geometry.lean.cinterop.lean_geometry_cell_intersections_path
import com.alexvanyo.composelife.geometry.lean.cinterop.lean_geometry_cell_intersections_segment
import com.alexvanyo.composelife.geometry.lean.cinterop.lean_geometry_free_cells
import com.alexvanyo.composelife.geometry.lean.cinterop.lean_geometry_init_runtime
import kotlinx.cinterop.ExperimentalForeignApi
import kotlinx.cinterop.FloatVar
import kotlinx.cinterop.alloc
import kotlinx.cinterop.allocArray
import kotlinx.cinterop.convert
import kotlinx.cinterop.get
import kotlinx.cinterop.memScoped
import kotlinx.cinterop.ptr
import kotlinx.cinterop.set

/**
 * An in-memory differential oracle running the formal Lean 4 geometry specification.
 */
@OptIn(ExperimentalForeignApi::class)
internal class LeanGeometryOracle {
    init {
        lean_geometry_init_runtime()
    }

    /**
     * Computes the set of discrete grid cells intersected by the line segment from [start] to [end]
     * using the formal Lean 4 specification.
     */
    fun cellIntersectionsSegment(start: Offset, end: Offset): Set<IntOffset> = memScoped {
        val outCells = alloc<CellListC>()
        val res = lean_geometry_cell_intersections_segment(
            x1 = start.x,
            y1 = start.y,
            x2 = end.x,
            y2 = end.y,
            out_cells = outCells.ptr,
        )
        check(res == 0) { "lean_geometry_cell_intersections_segment failed with status $res" }
        try {
            readCells(outCells)
        } finally {
            lean_geometry_free_cells(outCells.ptr)
        }
    }

    /**
     * Computes the set of discrete grid cells intersected by the multi-point path
     * using the formal Lean 4 specification.
     */
    fun cellIntersectionsPath(points: List<Offset>): Set<IntOffset> = memScoped {
        require(points.isNotEmpty())
        val count = points.size
        val coords = allocArray<FloatVar>(count * 2)
        for (i in 0 until count) {
            coords[2 * i] = points[i].x
            coords[2 * i + 1] = points[i].y
        }
        val outCells = alloc<CellListC>()
        val res = lean_geometry_cell_intersections_path(
            coords = coords,
            num_points = count.convert(),
            out_cells = outCells.ptr,
        )
        check(res == 0) { "lean_geometry_cell_intersections_path failed with status $res" }
        try {
            readCells(outCells)
        } finally {
            lean_geometry_free_cells(outCells.ptr)
        }
    }

    private fun readCells(cellList: CellListC): Set<IntOffset> {
        val count = cellList.count.toInt()
        val ptr = cellList.cells ?: return emptySet()
        val result = mutableSetOf<IntOffset>()
        for (i in 0 until count) {
            val cell = ptr[i]
            result.add(IntOffset(cell.x, cell.y))
        }
        return result
    }
}
