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

#include "session_value_bridge.h"
#include <lean/lean.h>
#include <stdlib.h>
#include <string.h>

extern lean_object* initialize_SessionValue_SessionValue_Bridge(uint8_t builtin);
void lean_initialize_runtime_module(void);
extern lean_object* session_value_initial_state(lean_object* uSess, lean_object* uVal, lean_object* uValStr, lean_object* locId);
extern lean_object* session_value_step_set_value(lean_object* st, lean_object* valStr, lean_object* valId);
extern lean_object* session_value_step_set_upstream(lean_object* st, lean_object* uSess, lean_object* uVal, lean_object* uValStr, lean_object* freshId);
extern lean_object* session_value_make_snapshot(lean_object* st, lean_object* lastExp);

struct LeanOracleSession {
    lean_object* state;
    lean_object* last_exp;
    char* cached_exposed_value;
};

static bool g_lean_runtime_initialized = false;

void lean_session_value_init_runtime(void) {
    if (g_lean_runtime_initialized) {
        return;
    }
    lean_initialize_runtime_module();
    lean_object* res = initialize_SessionValue_SessionValue_Bridge(1);
    if (lean_io_result_is_ok(res)) {
        lean_dec_ref(res);
    }
    lean_io_mark_end_initialization();
    g_lean_runtime_initialized = true;
}

static inline lean_object* lean_mk_uuid(uint64_t msb, uint64_t lsb) {
    lean_object* obj = lean_alloc_ctor(0, 0, 16);
    lean_ctor_set_uint64(obj, 0, msb);
    lean_ctor_set_uint64(obj, 8, lsb);
    return obj;
}

static inline LeanUuidC lean_to_uuid_c(lean_object* obj) {
    LeanUuidC u;
    u.most_significant_bits = lean_ctor_get_uint64(obj, 0);
    u.least_significant_bits = lean_ctor_get_uint64(obj, 8);
    return u;
}

static void fill_snapshot(LeanOracleSession* session, lean_object* snap_obj, LeanStateSnapshotC* out_snapshot) {
    lean_object* exp_sess = lean_ctor_get(snap_obj, 0);
    lean_object* exp_val_id = lean_ctor_get(snap_obj, 1);
    lean_object* exp_val_str = lean_ctor_get(snap_obj, 2);
    lean_object* loc_sess = lean_ctor_get(snap_obj, 3);
    lean_object* pre_loc_sess = lean_ctor_get(snap_obj, 4);
    lean_object* last_exp_sess = lean_ctor_get(snap_obj, 5);
    lean_object* last_exp_val_id = lean_ctor_get(snap_obj, 6);
    uint8_t is_active = lean_ctor_get_uint8(snap_obj, sizeof(void*)*7);
    uint8_t is_up_to_date = lean_ctor_get_uint8(snap_obj, sizeof(void*)*7 + 1);

    out_snapshot->exposed_session_id = lean_to_uuid_c(exp_sess);
    out_snapshot->exposed_value_id = lean_to_uuid_c(exp_val_id);
    out_snapshot->local_session_id = lean_to_uuid_c(loc_sess);
    out_snapshot->pre_local_session_id = lean_to_uuid_c(pre_loc_sess);
    out_snapshot->last_expected_session_id = lean_to_uuid_c(last_exp_sess);
    out_snapshot->last_expected_value_id = lean_to_uuid_c(last_exp_val_id);
    out_snapshot->is_local_session_active = (bool)is_active;
    out_snapshot->is_upstream_up_to_date = (bool)is_up_to_date;

    const char* str_cstr = lean_string_cstr(exp_val_str);
    if (session->cached_exposed_value != NULL) {
        free(session->cached_exposed_value);
    }
    session->cached_exposed_value = strdup(str_cstr);
    out_snapshot->exposed_value = session->cached_exposed_value;
}

LeanOracleSession* lean_oracle_create(
    uint64_t upstream_session_id_msb,
    uint64_t upstream_session_id_lsb,
    uint64_t upstream_value_id_msb,
    uint64_t upstream_value_id_lsb,
    const char* upstream_value,
    uint64_t local_session_id_msb,
    uint64_t local_session_id_lsb
) {
    lean_session_value_init_runtime();

    lean_object* u_sess = lean_mk_uuid(upstream_session_id_msb, upstream_session_id_lsb);
    lean_object* u_val = lean_mk_uuid(upstream_value_id_msb, upstream_value_id_lsb);
    lean_object* u_val_str = lean_mk_string(upstream_value);
    lean_object* loc_id = lean_mk_uuid(local_session_id_msb, local_session_id_lsb);

    lean_object* pair = session_value_initial_state(u_sess, u_val, u_val_str, loc_id);
    lean_object* st = lean_ctor_get(pair, 0);
    lean_object* exp = lean_ctor_get(pair, 1);
    lean_inc_ref(st);
    lean_inc_ref(exp);
    lean_dec_ref(pair);

    LeanOracleSession* session = (LeanOracleSession*)malloc(sizeof(LeanOracleSession));
    session->state = st;
    session->last_exp = exp;
    session->cached_exposed_value = NULL;
    return session;
}

void lean_oracle_step_set_value(
    LeanOracleSession* session,
    const char* new_val,
    uint64_t val_id_msb,
    uint64_t val_id_lsb,
    LeanStateSnapshotC* out_snapshot
) {
    lean_object* val_str = lean_mk_string(new_val);
    lean_object* vid = lean_mk_uuid(val_id_msb, val_id_lsb);

    lean_object* pair = session_value_step_set_value(session->state, val_str, vid);
    lean_object* next_st = lean_ctor_get(pair, 0);
    lean_object* exp = lean_ctor_get(pair, 1);
    lean_inc_ref(next_st);
    lean_inc_ref(exp);
    lean_dec_ref(pair);

    lean_dec_ref(session->last_exp);
    session->state = next_st;
    session->last_exp = exp;

    lean_oracle_get_snapshot(session, out_snapshot);
}

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
) {
    lean_object* u_sess = lean_mk_uuid(upstream_session_id_msb, upstream_session_id_lsb);
    lean_object* u_val = lean_mk_uuid(upstream_value_id_msb, upstream_value_id_lsb);
    lean_object* u_val_str = lean_mk_string(upstream_value);
    lean_object* fresh_id = lean_mk_uuid(fresh_local_id_msb, fresh_local_id_lsb);

    lean_object* pair = session_value_step_set_upstream(session->state, u_sess, u_val, u_val_str, fresh_id);
    lean_object* next_st = lean_ctor_get(pair, 0);
    lean_object* exp = lean_ctor_get(pair, 1);
    lean_inc_ref(next_st);
    lean_inc_ref(exp);
    lean_dec_ref(pair);

    lean_dec_ref(session->last_exp);
    session->state = next_st;
    session->last_exp = exp;

    lean_oracle_get_snapshot(session, out_snapshot);
}

void lean_oracle_get_snapshot(
    LeanOracleSession* session,
    LeanStateSnapshotC* out_snapshot
) {
    lean_inc_ref(session->state);
    lean_inc_ref(session->last_exp);
    lean_object* snap = session_value_make_snapshot(session->state, session->last_exp);
    fill_snapshot(session, snap, out_snapshot);
    lean_dec_ref(snap);
}

void lean_oracle_free(LeanOracleSession* session) {
    if (session == NULL) return;
    if (session->state != NULL) {
        lean_dec_ref(session->state);
        session->state = NULL;
    }
    if (session->last_exp != NULL) {
        lean_dec_ref(session->last_exp);
        session->last_exp = NULL;
    }
    if (session->cached_exposed_value != NULL) {
        free(session->cached_exposed_value);
        session->cached_exposed_value = NULL;
    }
    free(session);
}

