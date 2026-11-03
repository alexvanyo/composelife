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
theorem initialState_valid (u0 : SessionValue α) (initLocalId : Uuid)
    (h_fresh : initLocalId ≠ u0.sessionId) :
    ValidState (initialState u0 initLocalId) :=
  initialState_valid_Impl u0 initLocalId h_fresh

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
    (h_conflict : newUpstream.sessionId ≠ lv.sessionId) :
    let st' := stepSetValueFromUpstream st newUpstream freshId
    st'.localSessionValue = none ∧
    st'.sessionValue = newUpstream ∧
    st'.info.isLocalSessionActive = false :=
  upstream_conflict_invalidates_Impl st lv newUpstream freshId h_changed h_active h_conflict

/--
Theorem 8 (CAS Expected Value Soundness): The `expected` field of the update emitted by
`stepSetValue` is identical to the current exposed `sessionValue`.
-/
theorem cas_expected_soundness (st : State α) (v : α) (vid : Uuid) :
    (stepSetValue st v vid).2.1 = st.sessionValue :=
  cas_expected_soundness_Impl st v vid

/--
Theorem 8b (CAS Emission Soundness): Under `ValidState`, the emitted update pair `(expected, newValue)`
satisfies `expected.sessionId ∈ {info.localSessionId, info.preLocalSessionId}`, `newValue.sessionId = info.localSessionId`,
and the local session ID is preserved.
-/
theorem cas_emission_soundness (st : State α) (v : α) (vid : Uuid) (h_valid : ValidState st) :
    let ((st', (expected, newValue))) := stepSetValue st v vid
    (expected.sessionId = st.info.localSessionId ∨ expected.sessionId = st.info.preLocalSessionId) ∧
    newValue.sessionId = st.info.localSessionId ∧
    st'.localSessionId = st.localSessionId :=
  cas_emission_soundness_Impl st v vid h_valid

/--
Theorem 9 (CAS Batching): For any non-empty chained queue `q` and any upstream whose compare-and-set
accepts a value as matching itself, applying the updates one after another has exactly the same
outcome as applying the single batched update `(q.head.1, q.last.2)`.
-/
theorem batch_cas_equivalence (accepts : SessionValue α → SessionValue α → Bool)
    (h_refl : ∀ v, accepts v v = true) (current : SessionValue α)
    (q : List (Update α)) (hq : q ≠ []) (h_chain : CASChained q) :
    casApplyAllWith accepts current q =
      casApplyWith accepts current (batchUpdate q hq).1 (batchUpdate q hq).2 :=
  batch_cas_equivalence_Impl accepts h_refl current q hq h_chain

/--
Theorem 9a: Both upstream compare-and-set policies used in the app accept a value as matching itself,
so Theorem 9 applies to them.
-/
theorem cas_policies_reflexive [DecidableEq α] (v : SessionValue α) :
    fullMatch v v = true ∧ idMatch v v = true :=
  cas_policies_reflexive_Impl v

/--
Theorem 10a (Async Queue Invariant): Every state reachable by `rememberAsyncSessionValueHolder`,
through any interleaving of local edits, upstream changes and flushes, satisfies `ValidState`, and its
update queue is a block of stale updates followed by the chained updates of the current local session.
-/
theorem asyncReachable_invariant {st : State α} {q : List (Update α)} (h : AsyncReachable st q) :
    ValidState st ∧ QueueInv st q :=
  asyncReachable_invariant_Impl h

/--
Theorem 10b (Stale-Update Pruning Is Exact): Under the queue invariant, `pruneStaleUpdates` drops
exactly the stale updates: what it removes is a prefix written by earlier local sessions, and what
it keeps is the chained queue of the current local session, ending in the value the holder shows.
-/
theorem pruneStaleUpdates_exact {st : State α} {q : List (Update α)} (h : QueueInv st q) :
    ∃ stale, q = stale ++ pruneStaleUpdates st.info q ∧
      (∀ u ∈ stale, u.2.sessionId ≠ st.info.localSessionId) ∧
      (∀ u ∈ pruneStaleUpdates st.info q, u.2.sessionId = st.info.localSessionId) ∧
      CASChained (pruneStaleUpdates st.info q) ∧
      (∀ u ∈ (pruneStaleUpdates st.info q).getLast?, u.2 = st.sessionValue) :=
  pruneStaleUpdates_exact_Impl h

/--
Theorem 10c (Async Batch Soundness): In every reachable state, the single update that
`rememberAsyncSessionValueHolder` sends for its pruned queue has the same compare-and-set outcome as
sending each queued update of the current session in order, and it writes exactly the value that
the holder shows.
-/
theorem async_batch_sound {st : State α} {q : List (Update α)} (h : AsyncReachable st q)
    (accepts : SessionValue α → SessionValue α → Bool) (h_refl : ∀ v, accepts v v = true)
    (current : SessionValue α) (hp : pruneStaleUpdates st.info q ≠ []) :
    casApplyAllWith accepts current (pruneStaleUpdates st.info q) =
      casApplyWith accepts current (batchUpdate _ hp).1 (batchUpdate _ hp).2 ∧
    (batchUpdate _ hp).2 = st.sessionValue :=
  async_batch_sound_Impl h accepts h_refl current hp

/--
Theorem 11a (Functorial Identity): `SessionValue.map id` is the identity.
-/
theorem sessionValue_map_id (sv : SessionValue α) : sv.map id = sv :=
  sessionValue_map_id_Impl sv

/--
Theorem 11b (Functorial Composition): `SessionValue.map` commutes with composition.
-/
theorem sessionValue_map_comp (f : α → β) (g : β → γ) (sv : SessionValue α) :
    (sv.map f).map g = sv.map (g ∘ f) :=
  sessionValue_map_comp_Impl f g sv

/--
Theorem 11c (Mapped Holder Round-Trip): `MappedSessionValueHolder.setValue(b, vid)` sets
`transformFrom b` with the same `vid` on the underlying holder. When `transformTo` is a left inverse
of `transformFrom`, the mapped holder then shows exactly `b`, tagged with the local session id and
the given value id.
-/
theorem mapped_setValue_roundtrip (st : State α) (transformTo : α → β) (transformFrom : β → α)
    (h_retract : ∀ b, transformTo (transformFrom b) = b) (b : β) (vid : Uuid) :
    let (st', _) := stepSetValue st (transformFrom b) vid
    (st'.map transformTo).sessionValue = { sessionId := st.localSessionId, valueId := vid, value := b } :=
  mapped_setValue_roundtrip_Impl st transformTo transformFrom h_retract b vid

end SessionValue
