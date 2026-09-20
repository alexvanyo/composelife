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

#ifndef GEOMETRY_BRIDGE_H
#define GEOMETRY_BRIDGE_H

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct {
    int32_t x;
    int32_t y;
} CellC;

typedef struct {
    CellC* cells;
    size_t count;
} CellListC;

void lean_geometry_init_runtime(void);

int32_t lean_geometry_cell_intersections_segment(
    float x1,
    float y1,
    float x2,
    float y2,
    CellListC* out_cells
);

int32_t lean_geometry_cell_intersections_path(
    const float* coords,
    size_t num_points,
    CellListC* out_cells
);

void lean_geometry_free_cells(CellListC* cells);

#ifdef __cplusplus
}
#endif

#endif // GEOMETRY_BRIDGE_H
