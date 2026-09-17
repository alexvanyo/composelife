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
#include <jni.h>
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

    out_snapshot->exposed_session_id = lean_uint64_of_nat(exp_sess);
    out_snapshot->exposed_value_id = lean_uint64_of_nat(exp_val_id);
    out_snapshot->local_session_id = lean_uint64_of_nat(loc_sess);
    out_snapshot->pre_local_session_id = lean_uint64_of_nat(pre_loc_sess);
    out_snapshot->last_expected_session_id = lean_uint64_of_nat(last_exp_sess);
    out_snapshot->last_expected_value_id = lean_uint64_of_nat(last_exp_val_id);
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
    uint64_t upstream_session_id,
    uint64_t upstream_value_id,
    const char* upstream_value,
    uint64_t local_session_id
) {
    lean_session_value_init_runtime();

    lean_object* u_sess = lean_uint64_to_nat(upstream_session_id);
    lean_object* u_val = lean_uint64_to_nat(upstream_value_id);
    lean_object* u_val_str = lean_mk_string(upstream_value);
    lean_object* loc_id = lean_uint64_to_nat(local_session_id);

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
    uint64_t val_id,
    LeanStateSnapshotC* out_snapshot
) {
    lean_object* val_str = lean_mk_string(new_val);
    lean_object* vid = lean_uint64_to_nat(val_id);

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
    uint64_t upstream_session_id,
    uint64_t upstream_value_id,
    const char* upstream_value,
    uint64_t fresh_local_id,
    LeanStateSnapshotC* out_snapshot
) {
    lean_object* u_sess = lean_uint64_to_nat(upstream_session_id);
    lean_object* u_val = lean_uint64_to_nat(upstream_value_id);
    lean_object* u_val_str = lean_mk_string(upstream_value);
    lean_object* fresh_id = lean_uint64_to_nat(fresh_local_id);

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

static jobject create_snapshot_object(JNIEnv* env, const LeanStateSnapshotC* snap) {
    jclass cls = (*env)->FindClass(env, "com/alexvanyo/composelife/sessionvalue/lean/LeanSnapshot");
    if (cls == NULL) return NULL;
    jmethodID init_mid = (*env)->GetMethodID(env, cls, "<init>", "(JJLjava/lang/String;ZJJZJJ)V");
    if (init_mid == NULL) return NULL;
    jstring str = (*env)->NewStringUTF(env, snap->exposed_value ? snap->exposed_value : "");
    jobject obj = (*env)->NewObject(
        env,
        cls,
        init_mid,
        (jlong)snap->exposed_session_id,
        (jlong)snap->exposed_value_id,
        str,
        (jboolean)snap->is_local_session_active,
        (jlong)snap->local_session_id,
        (jlong)snap->pre_local_session_id,
        (jboolean)snap->is_upstream_up_to_date,
        (jlong)snap->last_expected_session_id,
        (jlong)snap->last_expected_value_id
    );
    return obj;
}

JNIEXPORT jlong JNICALL Java_com_alexvanyo_composelife_sessionvalue_lean_LeanSessionValueOracle_create(
    JNIEnv* env,
    jclass cls,
    jlong upstream_session_id,
    jlong upstream_value_id,
    jstring upstream_value,
    jlong local_session_id
) {
    const char* val_cstr = (*env)->GetStringUTFChars(env, upstream_value, NULL);
    LeanOracleSession* session = lean_oracle_create(
        (uint64_t)upstream_session_id,
        (uint64_t)upstream_value_id,
        val_cstr,
        (uint64_t)local_session_id
    );
    (*env)->ReleaseStringUTFChars(env, upstream_value, val_cstr);
    return (jlong)(intptr_t)session;
}

JNIEXPORT jobject JNICALL Java_com_alexvanyo_composelife_sessionvalue_lean_LeanSessionValueOracle_nativeStepSetValue(
    JNIEnv* env,
    jclass cls,
    jlong session_ptr,
    jstring value,
    jlong value_id
) {
    LeanOracleSession* session = (LeanOracleSession*)(intptr_t)session_ptr;
    const char* val_cstr = (*env)->GetStringUTFChars(env, value, NULL);
    LeanStateSnapshotC snap;
    lean_oracle_step_set_value(session, val_cstr, (uint64_t)value_id, &snap);
    (*env)->ReleaseStringUTFChars(env, value, val_cstr);
    return create_snapshot_object(env, &snap);
}

JNIEXPORT jobject JNICALL Java_com_alexvanyo_composelife_sessionvalue_lean_LeanSessionValueOracle_nativeStepSetUpstream(
    JNIEnv* env,
    jclass cls,
    jlong session_ptr,
    jlong upstream_session_id,
    jlong upstream_value_id,
    jstring upstream_value,
    jlong fresh_local_id
) {
    LeanOracleSession* session = (LeanOracleSession*)(intptr_t)session_ptr;
    const char* val_cstr = (*env)->GetStringUTFChars(env, upstream_value, NULL);
    LeanStateSnapshotC snap;
    lean_oracle_step_set_upstream(
        session,
        (uint64_t)upstream_session_id,
        (uint64_t)upstream_value_id,
        val_cstr,
        (uint64_t)fresh_local_id,
        &snap
    );
    (*env)->ReleaseStringUTFChars(env, upstream_value, val_cstr);
    return create_snapshot_object(env, &snap);
}

JNIEXPORT jobject JNICALL Java_com_alexvanyo_composelife_sessionvalue_lean_LeanSessionValueOracle_nativeGetSnapshot(
    JNIEnv* env,
    jclass cls,
    jlong session_ptr
) {
    LeanOracleSession* session = (LeanOracleSession*)(intptr_t)session_ptr;
    LeanStateSnapshotC snap;
    lean_oracle_get_snapshot(session, &snap);
    return create_snapshot_object(env, &snap);
}

JNIEXPORT void JNICALL Java_com_alexvanyo_composelife_sessionvalue_lean_LeanSessionValueOracle_nativeDestroy(
    JNIEnv* env,
    jclass cls,
    jlong session_ptr
) {
    LeanOracleSession* session = (LeanOracleSession*)(intptr_t)session_ptr;
    lean_oracle_free(session);
}

