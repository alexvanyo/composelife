/-
 * Copyright 2024 The Android Open Source Project
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
 -/

import SessionValue.Basic
import SessionValue.StateMachine

namespace SessionValue

/-!
# Master Verification Theorems for `session-value`

This file contains the formal proofs guaranteeing that the state machine, invariants,
synchronicity, and concurrency semantics of `SessionValueHolder` hold unconditionally.
-/

/--
Theorem 1: Initial state satisfies the `ValidState` invariant.
-/
theorem initialState_valid (u0 : SessionValue α) (initLocalId : Uuid) :
    ValidState (initialState u0 initLocalId) := by
  constructor
  · intro _
    rfl
  · intro _ h_some
    contradiction

/--
Theorem 2: `stepSetValue` preserves the `ValidState` invariant.
-/
theorem stepSetValue_preserves_valid (st : State α) (v : α) (vid : Uuid) :
    ValidState (stepSetValue st v vid).1 := by
  constructor
  · intro h_none
    dsimp [stepSetValue] at h_none
    contradiction
  · intro lv h_some
    dsimp [stepSetValue] at h_some
    injection h_some with h_eq
    rw [← h_eq]
    rfl

/--
Theorem 3: `stepSetValueFromUpstream` preserves the `ValidState` invariant,
given fresh ID generation (`freshLocalSessionId ≠ newUpstream.sessionId`).
-/
theorem stepSetValueFromUpstream_preserves_valid (st : State α) (newUpstream : SessionValue α)
    (freshLocalSessionId : Uuid) (h_valid : ValidState st)
    (h_fresh : freshLocalSessionId ≠ newUpstream.sessionId) :
    ValidState (stepSetValueFromUpstream st newUpstream freshLocalSessionId) := by
  dsimp [stepSetValueFromUpstream]
  split
  · exact h_valid
  · cases h_loc : st.localSessionValue with
    | none =>
      dsimp
      have h_fresh_bne : (freshLocalSessionId != newUpstream.sessionId) = true :=
        bne_iff_ne.mpr h_fresh
      simp only [h_fresh_bne]
      constructor
      · intro _
        rfl
      · intro _ h_some
        contradiction
    | some lv =>
      dsimp
      by_cases h_diff : newUpstream.sessionId = lv.sessionId
      · have h_not_bne : (newUpstream.sessionId != lv.sessionId) = false := by
          rw [h_diff, bne_self_eq_false]
        have h_lv_id := h_valid.active_sound lv h_loc
        have h_same_id : (st.localSessionId != newUpstream.sessionId) = false := by
          rw [← h_lv_id, ← h_diff, bne_self_eq_false]
        simp only [h_not_bne]
        constructor
        · intro h_none
          contradiction
        · intro lv' h_some
          injection h_some with h_eq
          rw [← h_eq]
          exact h_lv_id
      · have h_bne : (newUpstream.sessionId != lv.sessionId) = true :=
          bne_iff_ne.mpr h_diff
        have h_fresh_bne : (freshLocalSessionId != newUpstream.sessionId) = true :=
          bne_iff_ne.mpr h_fresh
        simp [h_bne, h_fresh_bne]
        constructor
        · intro _
          rfl
        · intro _ h_some
          contradiction

/--
Theorem 4 (Local Synchronicity): Immediately after calling `stepSetValue`,
the exposed `sessionValue` reflects the new value, new valueId, and local sessionId.
Local UI components observe zero latency.
-/
theorem local_synchronicity (st : State α) (v : α) (vid : Uuid) :
    let st' := (stepSetValue st v vid).1
    st'.sessionValue.value = v ∧
    st'.sessionValue.sessionId = st.localSessionId ∧
    st'.sessionValue.valueId = vid := by
  dsimp [stepSetValue, State.sessionValue]
  exact ⟨rfl, rfl, rfl⟩

/--
Theorem 5a (Local Session ID Stability): Upgrading from `Inactive` to `Active` via
`stepSetValue` preserves `info.localSessionId`.
-/
theorem id_stability_localSessionId (st : State α) (v : α) (vid : Uuid)
    (h_inactive : st.localSessionValue = none) :
    let st' := (stepSetValue st v vid).1
    st'.info.localSessionId = st.info.localSessionId := by
  dsimp [stepSetValue, State.info, LocalSessionInfo.localSessionId]
  rw [h_inactive]

/--
Theorem 5b (Pre-Local Session ID Stability): Upgrading from `Inactive` to `Active` via
`stepSetValue` preserves `info.preLocalSessionId`.
-/
theorem id_stability_preLocalSessionId (st : State α) (v : α) (vid : Uuid)
    (h_valid : ValidState st) (h_inactive : st.localSessionValue = none) :
    let st' := (stepSetValue st v vid).1
    st'.info.preLocalSessionId = st.info.preLocalSessionId := by
  have h_before := h_valid.inactive_sound h_inactive
  dsimp [stepSetValue, State.info, LocalSessionInfo.preLocalSessionId]
  rw [h_inactive]
  dsimp
  exact h_before

/--
Theorem 6a (Upstream Echo Keeps Active): When an upstream update echoes the local
session ID, the local session remains active (`localSessionValue` is preserved).
-/
theorem upstream_echo_keeps_active (st : State α) (lv : SessionValue α) (newUpstream : SessionValue α)
    (freshId : Uuid)
    (h_active : st.localSessionValue = some lv)
    (h_echo : newUpstream.sessionId = lv.sessionId) :
    let st' := stepSetValueFromUpstream st newUpstream freshId
    st'.localSessionValue = some lv := by
  dsimp [stepSetValueFromUpstream]
  split
  · exact h_active
  · rw [h_active]
    dsimp
    have h_not_diff : (newUpstream.sessionId != lv.sessionId) = false := by
      rw [h_echo, bne_self_eq_false]
    simp only [h_not_diff]
    rfl

/--
Theorem 6b (Upstream Echo Catches Up): When an upstream update matches both
the local session ID and the latest local valueId, the holder state's info
identifies the upstream as up-to-date.
-/
theorem upstream_echo_up_to_date (st : State α) (lv : SessionValue α) (newUpstream : SessionValue α)
    (freshId : Uuid)
    (h_valid : ValidState st)
    (h_active : st.localSessionValue = some lv)
    (h_echo_session : newUpstream.sessionId = lv.sessionId)
    (h_echo_value : newUpstream.valueId = lv.valueId) :
    let st' := stepSetValueFromUpstream st newUpstream freshId
    st'.info = LocalSessionInfo.active st.localSessionId true st.upstreamSessionIdBeforeLocalSession := by
  have h_lv_id := h_valid.active_sound lv h_active
  dsimp [stepSetValueFromUpstream]
  split
  · dsimp [State.info]
    rw [h_active]
    rename_i h_not_changed
    have h_not : (newUpstream.sessionId != st.upstreamSessionValue.sessionId ||
                  newUpstream.valueId != st.upstreamSessionValue.valueId) = false := by
      revert h_not_changed
      cases (newUpstream.sessionId != st.upstreamSessionValue.sessionId ||
             newUpstream.valueId != st.upstreamSessionValue.valueId) <;> decide
    rw [Bool.or_eq_false_iff] at h_not
    have h_sess := bne_eq_false_iff_eq.mp h_not.1
    have h_val := bne_eq_false_iff_eq.mp h_not.2
    have h1 : (st.upstreamSessionValue.sessionId == lv.sessionId) = true := by
      rw [← h_sess, h_echo_session, beq_self_eq_true]
    have h2 : (st.upstreamSessionValue.valueId == lv.valueId) = true := by
      rw [← h_val, h_echo_value, beq_self_eq_true]
    simp only [h1, h2]
    rfl
  · rw [h_active]
    dsimp
    have h_not_diff : (newUpstream.sessionId != lv.sessionId) = false := by
      rw [h_echo_session, bne_self_eq_false]
    have h_same_id : (st.localSessionId != newUpstream.sessionId) = false := by
      rw [← h_lv_id, ← h_echo_session, bne_self_eq_false]
    simp only [h_not_diff]
    dsimp [State.info]
    have h1 : (newUpstream.sessionId == lv.sessionId) = true := by
      rw [h_echo_session, beq_self_eq_true]
    have h2 : (newUpstream.valueId == lv.valueId) = true := by
      rw [h_echo_value, beq_self_eq_true]
    simp only [h1, h2, h_same_id]
    rfl

/--
Theorem 7 (Conflicting Session Invalidation & Safety): When an upstream update arrives
from a foreign session (`newUpstream.sessionId ≠ lv.sessionId`), the local active session
is cleanly invalidated (`localSessionValue = none`), reverting to the new upstream value.
-/
theorem upstream_conflict_invalidates (st : State α) (lv : SessionValue α) (newUpstream : SessionValue α)
    (freshId : Uuid)
    (h_changed : (newUpstream.sessionId != st.upstreamSessionValue.sessionId ||
                  newUpstream.valueId != st.upstreamSessionValue.valueId) = true)
    (h_active : st.localSessionValue = some lv)
    (h_conflict : newUpstream.sessionId ≠ lv.sessionId)
    (_h_fresh : freshId ≠ newUpstream.sessionId) :
    let st' := stepSetValueFromUpstream st newUpstream freshId
    st'.localSessionValue = none ∧
    st'.sessionValue = newUpstream ∧
    st'.info.isLocalSessionActive = false := by
  dsimp [stepSetValueFromUpstream]
  rw [h_changed]
  dsimp
  rw [h_active]
  dsimp
  have h_diff : (newUpstream.sessionId != lv.sessionId) = true :=
    bne_iff_ne.mpr h_conflict
  simp [h_diff, State.sessionValue, State.info, LocalSessionInfo.isLocalSessionActive]

/--
Theorem 8 (CAS Precondition Soundness): The `expected` session value emitted by
`stepSetValue` matches the exact value currently held in the holder.
-/
theorem cas_expected_soundness (st : State α) (v : α) (vid : Uuid) :
    (stepSetValue st v vid).2.1 = st.sessionValue := by
  rfl

end SessionValue
