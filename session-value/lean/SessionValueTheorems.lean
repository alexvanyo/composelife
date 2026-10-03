/-
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
 -/

import SessionValue.Basic
import SessionValue.StateMachine
import SessionValueDefs
import SessionValueProofs

namespace SessionValue

/--
Theorem 1: Initial state satisfies the `ValidState` invariant.
-/
theorem initialState_valid (u0 : SessionValue α) (initLocalId : Uuid) :
    ValidState (initialState u0 initLocalId) :=
  initialState_valid_Impl u0 initLocalId

/--
Theorem 2: `stepSetValue` preserves the `ValidState` invariant.
-/
theorem stepSetValue_preserves_valid (st : State α) (v : α) (vid : Uuid) :
    ValidState (stepSetValue st v vid).1 :=
  stepSetValue_preserves_valid_Impl st v vid

/--
Theorem 3: `stepSetValueFromUpstream` preserves the `ValidState` invariant,
given fresh ID generation (`freshLocalSessionId ≠ newUpstream.sessionId`).
-/
theorem stepSetValueFromUpstream_preserves_valid (st : State α) (newUpstream : SessionValue α)
    (freshLocalSessionId : Uuid) (h_valid : ValidState st)
    (h_fresh : freshLocalSessionId ≠ newUpstream.sessionId) :
    ValidState (stepSetValueFromUpstream st newUpstream freshLocalSessionId) :=
  stepSetValueFromUpstream_preserves_valid_Impl st newUpstream freshLocalSessionId h_valid h_fresh

/--
Theorem 4 (Local Synchronicity): Immediately after calling `stepSetValue`,
the exposed `sessionValue` reflects the new value, new valueId, and local sessionId.
Local UI components observe zero latency.
-/
theorem local_synchronicity (st : State α) (v : α) (vid : Uuid) :
    let st' := (stepSetValue st v vid).1
    st'.sessionValue.value = v ∧
    st'.sessionValue.sessionId = st.localSessionId ∧
    st'.sessionValue.valueId = vid :=
  local_synchronicity_Impl st v vid

/--
Theorem 5a (Local Session ID Stability): Upgrading from `Inactive` to `Active` via
`stepSetValue` preserves `info.localSessionId`.
-/
theorem id_stability_localSessionId (st : State α) (v : α) (vid : Uuid)
    (h_inactive : st.localSessionValue = none) :
    let st' := (stepSetValue st v vid).1
    st'.info.localSessionId = st.info.localSessionId :=
  id_stability_localSessionId_Impl st v vid h_inactive

/--
Theorem 5b (Pre-Local Session ID Stability): Upgrading from `Inactive` to `Active` via
`stepSetValue` preserves `info.preLocalSessionId`.
-/
theorem id_stability_preLocalSessionId (st : State α) (v : α) (vid : Uuid)
    (h_valid : ValidState st) (h_inactive : st.localSessionValue = none) :
    let st' := (stepSetValue st v vid).1
    st'.info.preLocalSessionId = st.info.preLocalSessionId :=
  id_stability_preLocalSessionId_Impl st v vid h_valid h_inactive

/--
Theorem 6a (Upstream Echo Keeps Active): When an upstream update echoes the local
session ID, the local session remains active (`localSessionValue` is preserved).
-/
theorem upstream_echo_keeps_active (st : State α) (lv : SessionValue α) (newUpstream : SessionValue α)
    (freshId : Uuid)
    (h_active : st.localSessionValue = some lv)
    (h_echo : newUpstream.sessionId = lv.sessionId) :
    let st' := stepSetValueFromUpstream st newUpstream freshId
    st'.localSessionValue = some lv :=
  upstream_echo_keeps_active_Impl st lv newUpstream freshId h_active h_echo

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
    st'.info = LocalSessionInfo.active st.localSessionId true st.upstreamSessionIdBeforeLocalSession :=
  upstream_echo_up_to_date_Impl st lv newUpstream freshId h_valid h_active h_echo_session h_echo_value

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
    (h_fresh : freshId ≠ newUpstream.sessionId) :
    let st' := stepSetValueFromUpstream st newUpstream freshId
    st'.localSessionValue = none ∧
    st'.sessionValue = newUpstream ∧
    st'.info.isLocalSessionActive = false :=
  upstream_conflict_invalidates_Impl st lv newUpstream freshId h_changed h_active h_conflict h_fresh

/--
Theorem 8 (CAS Precondition Soundness): The `expected` session value emitted by
`stepSetValue` matches the exact value currently held in the holder.
-/
theorem cas_expected_soundness (st : State α) (v : α) (vid : Uuid) :
    (stepSetValue st v vid).2.1 = st.sessionValue :=
  cas_expected_soundness_Impl st v vid

end SessionValue
