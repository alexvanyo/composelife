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

#include "geometry_bridge.h"
#include <lean/lean.h>
#include <stdlib.h>
#include <string.h>

extern lean_object* initialize_Geometry_Geometry_Bridge(uint8_t builtin);
void lean_initialize_runtime_module(void);

extern lean_object* geometry_cell_intersections_segment(float x1, float y1, float x2, float y2);
extern lean_object* geometry_cell_intersections_path(lean_object* coords);

static bool g_lean_runtime_initialized = false;

void lean_geometry_init_runtime(void) {
    if (g_lean_runtime_initialized) {
        return;
    }
    lean_initialize_runtime_module();
    lean_object* res = initialize_Geometry_Geometry_Bridge(1);
    if (lean_io_result_is_ok(res)) {
        lean_dec_ref(res);
    }
    lean_io_mark_end_initialization();
    g_lean_runtime_initialized = true;
}

static int32_t populate_cell_list(lean_object* res_arr, CellListC* out_cells) {
    size_t res_size = lean_array_size(res_arr);
    out_cells->count = res_size;
    if (res_size == 0) {
        out_cells->cells = NULL;
    } else {
        out_cells->cells = (CellC*)malloc(res_size * sizeof(CellC));
        if (out_cells->cells == NULL) {
            lean_dec_ref(res_arr);
            return -1;
        }
        for (size_t i = 0; i < res_size; i++) {
            lean_object* pair = lean_array_uget(res_arr, i);
            lean_object* x_obj = lean_ctor_get(pair, 0);
            lean_object* y_obj = lean_ctor_get(pair, 1);
            out_cells->cells[i].x = (int32_t)(int64_t)lean_int64_of_int(x_obj);
            out_cells->cells[i].y = (int32_t)(int64_t)lean_int64_of_int(y_obj);
            lean_dec_ref(pair);
        }
    }
    lean_dec_ref(res_arr);
    return 0;
}

int32_t lean_geometry_cell_intersections_segment(
    float x1,
    float y1,
    float x2,
    float y2,
    CellListC* out_cells
) {
    lean_geometry_init_runtime();

    lean_object* res_arr = geometry_cell_intersections_segment(x1, y1, x2, y2);
    return populate_cell_list(res_arr, out_cells);
}

int32_t lean_geometry_cell_intersections_path(
    const float* coords,
    size_t num_points,
    CellListC* out_cells
) {
    lean_geometry_init_runtime();

    size_t total_floats = num_points * 2;
    lean_object* arr = lean_alloc_array(0, total_floats);
    for (size_t i = 0; i < total_floats; i++) {
        lean_object* f_obj = lean_box_float32(coords[i]);
        arr = lean_array_push(arr, f_obj);
    }

    lean_object* res_arr = geometry_cell_intersections_path(arr);
    return populate_cell_list(res_arr, out_cells);
}

void lean_geometry_free_cells(CellListC* cells) {
    if (cells == NULL) return;
    if (cells->cells != NULL) {
        free(cells->cells);
        cells->cells = NULL;
    }
    cells->count = 0;
}
