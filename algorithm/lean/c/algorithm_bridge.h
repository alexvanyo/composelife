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

#ifndef ALGORITHM_BRIDGE_H
#define ALGORITHM_BRIDGE_H

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct {
    int32_t x;
    int32_t y;
} CellPointC;

typedef struct {
    CellPointC* points;
    size_t count;
} CellGridC;

void lean_algorithm_init_runtime(void);

uint16_t lean_algorithm_step_4x4_bits(uint16_t bits);

int32_t lean_algorithm_step(
    const CellPointC* in_points,
    size_t in_count,
    uint32_t step,
    CellGridC* out_grid
);

void lean_algorithm_free_grid(CellGridC* grid);

#ifdef __cplusplus
}
#endif

#endif // ALGORITHM_BRIDGE_H
