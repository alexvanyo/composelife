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

#ifndef SESSION_VALUE_BRIDGE_H
#define SESSION_VALUE_BRIDGE_H

#include <stdint.h>
#include <stdbool.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct {
    uint64_t most_significant_bits;
    uint64_t least_significant_bits;
} LeanUuidC;

typedef struct {
    LeanUuidC exposed_session_id;
    LeanUuidC exposed_value_id;
    const char* exposed_value;
    bool is_local_session_active;
    LeanUuidC local_session_id;
    LeanUuidC pre_local_session_id;
    bool is_upstream_up_to_date;
    LeanUuidC last_expected_session_id;
    LeanUuidC last_expected_value_id;
} LeanStateSnapshotC;

typedef struct LeanOracleSession LeanOracleSession;

void lean_session_value_init_runtime(void);

LeanOracleSession* lean_oracle_create(
    uint64_t upstream_session_id_msb,
    uint64_t upstream_session_id_lsb,
    uint64_t upstream_value_id_msb,
    uint64_t upstream_value_id_lsb,
    const char* upstream_value,
    uint64_t local_session_id_msb,
    uint64_t local_session_id_lsb
);

void lean_oracle_step_set_value(
    LeanOracleSession* session,
    const char* new_val,
    uint64_t val_id_msb,
    uint64_t val_id_lsb,
    LeanStateSnapshotC* out_snapshot
);

void lean_oracle_step_set_upstream(
    LeanOracleSession* session,
    uint64_t upstream_session_id_msb,
    uint64_t upstream_session_id_lsb,
    uint64_t upstream_value_id_msb,
    uint64_t upstream_value_id_lsb,
    const char* upstream_value,
    uint64_t fresh_local_id_msb,
    uint64_t fresh_local_id_lsb,
    LeanStateSnapshotC* out_snapshot
);

void lean_oracle_get_snapshot(
    LeanOracleSession* session,
    LeanStateSnapshotC* out_snapshot
);

void lean_oracle_free(LeanOracleSession* session);

#ifdef __cplusplus
}
#endif

#endif // SESSION_VALUE_BRIDGE_H
