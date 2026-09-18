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

#include "algorithm_bridge.h"
#include <lean/lean.h>
#include <stdlib.h>
#include <string.h>

extern lean_object* initialize_Algorithm_Algorithm_Bridge(uint8_t builtin);
void lean_initialize_runtime_module(void);
extern lean_object* algorithm_step_coords(lean_object* coords, lean_object* steps);
extern lean_object* algorithm_step_4x4_bits(lean_object* bits);
extern lean_object* algorithm_step_leaf_bits(lean_object* bits);

static bool g_lean_runtime_initialized = false;

void lean_algorithm_init_runtime(void) {
    if (g_lean_runtime_initialized) {
        return;
    }
    lean_initialize_runtime_module();
    lean_object* res = initialize_Algorithm_Algorithm_Bridge(1);
    if (lean_io_result_is_ok(res)) {
        lean_dec_ref(res);
    }
    lean_io_mark_end_initialization();
    g_lean_runtime_initialized = true;
}

uint16_t lean_algorithm_step_4x4_bits(uint16_t bits) {
    lean_algorithm_init_runtime();
    lean_object* bits_obj = lean_uint64_to_nat((uint64_t)bits);
    lean_object* res_obj = algorithm_step_4x4_bits(bits_obj);
    uint16_t res = (uint16_t)lean_uint64_of_nat_mk(res_obj);
    return res;
}

uint16_t lean_algorithm_step_leaf_bits(uint64_t bits) {
    lean_algorithm_init_runtime();
    lean_object* bits_obj = lean_uint64_to_nat(bits);
    lean_object* res_obj = algorithm_step_leaf_bits(bits_obj);
    uint16_t res = (uint16_t)lean_uint64_of_nat_mk(res_obj);
    return res;
}

int32_t lean_algorithm_step(
    const CellPointC* in_points,
    size_t in_count,
    uint32_t step,
    CellGridC* out_grid
) {
    lean_algorithm_init_runtime();

    lean_object* arr = lean_alloc_array(0, in_count);
    for (size_t i = 0; i < in_count; i++) {
        lean_object* x = lean_int64_to_int((int64_t)in_points[i].x);
        lean_object* y = lean_int64_to_int((int64_t)in_points[i].y);
        lean_object* pair = lean_alloc_ctor(0, 2, 0);
        lean_ctor_set(pair, 0, x);
        lean_ctor_set(pair, 1, y);
        arr = lean_array_push(arr, pair);
    }

    lean_object* steps_obj = lean_uint64_to_nat((uint64_t)step);
    lean_object* res_arr = algorithm_step_coords(arr, steps_obj);

    size_t res_size = lean_array_size(res_arr);
    out_grid->count = res_size;
    if (res_size == 0) {
        out_grid->points = NULL;
    } else {
        out_grid->points = (CellPointC*)malloc(res_size * sizeof(CellPointC));
        if (out_grid->points == NULL) {
            lean_dec_ref(res_arr);
            return -1;
        }
        for (size_t i = 0; i < res_size; i++) {
            lean_object* pair = lean_array_uget(res_arr, i);
            lean_object* x_obj = lean_ctor_get(pair, 0);
            lean_object* y_obj = lean_ctor_get(pair, 1);
            out_grid->points[i].x = (int32_t)(int64_t)lean_int64_of_int(x_obj);
            out_grid->points[i].y = (int32_t)(int64_t)lean_int64_of_int(y_obj);
            lean_dec_ref(pair);
        }
    }
    lean_dec_ref(res_arr);
    return 0;
}

void lean_algorithm_free_grid(CellGridC* grid) {
    if (grid == NULL) return;
    if (grid->points != NULL) {
        free(grid->points);
        grid->points = NULL;
    }
    grid->count = 0;
}
