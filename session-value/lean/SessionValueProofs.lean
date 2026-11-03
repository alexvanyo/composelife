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

namespace SessionValue

/--
Implementation proof of `initialState_valid`.
-/
theorem initialState_valid_Impl (u0 : SessionValue α) (initLocalId : Uuid)
    (h_fresh : initLocalId ≠ u0.sessionId) :
    ValidState (initialState u0 initLocalId) := by
  constructor
  · intro _
    rfl
  · intro _
    exact h_fresh
  · intro _ h_some
    contradiction

/--
Implementation proof of `stepSetValue_preserves_valid`.
-/
theorem stepSetValue_preserves_valid_Impl (st : State α) (v : α) (vid : Uuid) :
    ValidState (stepSetValue st v vid).1 := by
  constructor
  · intro h_none
    dsimp [stepSetValue] at h_none
    contradiction
  · intro h_none
    dsimp [stepSetValue] at h_none
    contradiction
  · intro lv h_some
    dsimp [stepSetValue] at h_some
    injection h_some with h_eq
    rw [← h_eq]
    rfl

/--
Implementation proof of `stepSetValueFromUpstream_preserves_valid`.
-/
theorem stepSetValueFromUpstream_preserves_valid_Impl (st : State α) (newUpstream : SessionValue α)
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
      · intro _
        exact h_fresh
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
        · intro _
          exact h_fresh
        · intro _ h_some
          contradiction

/--
Implementation proof of `local_synchronicity`.
-/
theorem local_synchronicity_Impl (st : State α) (v : α) (vid : Uuid) :
    let st' := (stepSetValue st v vid).1
    st'.sessionValue.value = v ∧
    st'.sessionValue.sessionId = st.localSessionId ∧
    st'.sessionValue.valueId = vid := by
  dsimp [stepSetValue, State.sessionValue]
  exact ⟨rfl, rfl, rfl⟩

/--
Implementation proof of `id_stability_localSessionId`.
-/
theorem id_stability_localSessionId_Impl (st : State α) (v : α) (vid : Uuid)
    (h_inactive : st.localSessionValue = none) :
    let st' := (stepSetValue st v vid).1
    st'.info.localSessionId = st.info.localSessionId := by
  dsimp [stepSetValue, State.info, LocalSessionInfo.localSessionId]
  rw [h_inactive]

/--
Implementation proof of `id_stability_preLocalSessionId`.
-/
theorem id_stability_preLocalSessionId_Impl (st : State α) (v : α) (vid : Uuid)
    (h_valid : ValidState st) (h_inactive : st.localSessionValue = none) :
    let st' := (stepSetValue st v vid).1
    st'.info.preLocalSessionId = st.info.preLocalSessionId := by
  have h_before := h_valid.inactive_sound h_inactive
  dsimp [stepSetValue, State.info, LocalSessionInfo.preLocalSessionId]
  rw [h_inactive]
  dsimp
  exact h_before

/--
Implementation proof of `upstream_echo_keeps_active`.
-/
theorem upstream_echo_keeps_active_Impl (st : State α) (lv : SessionValue α) (newUpstream : SessionValue α)
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
Implementation proof of `upstream_echo_up_to_date`.
-/
theorem upstream_echo_up_to_date_Impl (st : State α) (lv : SessionValue α) (newUpstream : SessionValue α)
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
Implementation proof of `upstream_conflict_invalidates`.
-/
theorem upstream_conflict_invalidates_Impl (st : State α) (lv : SessionValue α) (newUpstream : SessionValue α)
    (freshId : Uuid)
    (h_changed : (newUpstream.sessionId != st.upstreamSessionValue.sessionId ||
                  newUpstream.valueId != st.upstreamSessionValue.valueId) = true)
    (h_active : st.localSessionValue = some lv)
    (h_conflict : newUpstream.sessionId ≠ lv.sessionId) :
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
Implementation proof of `cas_expected_soundness`.
-/
theorem cas_expected_soundness_Impl (st : State α) (v : α) (vid : Uuid) :
    (stepSetValue st v vid).2.1 = st.sessionValue :=
  rfl

/--
Implementation proof of `cas_emission_soundness`.
-/
theorem cas_emission_soundness_Impl (st : State α) (v : α) (vid : Uuid) (h_valid : ValidState st) :
    let ((st', (expected, newValue))) := stepSetValue st v vid
    (expected.sessionId = st.info.localSessionId ∨ expected.sessionId = st.info.preLocalSessionId) ∧
    newValue.sessionId = st.info.localSessionId ∧
    st'.localSessionId = st.localSessionId := by
  dsimp [stepSetValue]
  constructor
  · cases h_loc : st.localSessionValue with
    | none =>
      right
      dsimp [State.sessionValue, State.info]
      rw [h_loc]
      dsimp [LocalSessionInfo.preLocalSessionId]
    | some lv =>
      left
      dsimp [State.sessionValue, State.info]
      rw [h_loc]
      dsimp [LocalSessionInfo.localSessionId]
      exact h_valid.active_sound lv h_loc
  · constructor
    · cases h_loc : st.localSessionValue with
      | none =>
        dsimp [State.info]
        rw [h_loc]
        rfl
      | some lv =>
        dsimp [State.info]
        rw [h_loc]
        rfl
    · rfl

/--
Implementation proof of `batch_cas_equivalence` for arbitrary chained lists of updates.
-/
theorem batch_cas_equivalence_Impl (accepts : SessionValue α → SessionValue α → Bool)
    (h_refl : ∀ v, accepts v v = true) (current : SessionValue α)
    (q : List (Update α)) (hq : q ≠ []) (h_chain : CASChained q) :
    casApplyAllWith accepts current q =
      casApplyWith accepts current (batchUpdate q hq).1 (batchUpdate q hq).2 := by
  induction q generalizing current with
  | nil => contradiction
  | cons u rest ih =>
    rcases u with ⟨e1, n1⟩
    cases rest with
    | nil =>
      simp only [casApplyAllWith, casApplyWith, batchUpdate, List.head_cons, List.getLast_singleton]
      by_cases h : accepts current e1 = true <;> simp [h]
    | cons u2 rest' =>
      rcases u2 with ⟨e2, n2⟩
      obtain ⟨h_eq12, h_chain_rest⟩ := h_chain
      subst h_eq12
      have ih' := ih n1 (List.cons_ne_nil _ _) h_chain_rest
      simp only [casApplyWith, h_refl, ↓reduceIte, batchUpdate, List.head_cons] at ih'
      by_cases h : accepts current e1 = true
      · simp only [casApplyAllWith, casApplyWith, h, ↓reduceIte]
        simp only [casApplyAllWith, casApplyWith] at ih'
        rw [ih']
        simp [batchUpdate, h]
      · simp [casApplyAllWith, casApplyWith, batchUpdate, h]

/--
Implementation proof of `cas_policies_reflexive`.
-/
theorem cas_policies_reflexive_Impl [DecidableEq α] (v : SessionValue α) :
    fullMatch v v = true ∧ idMatch v v = true := by
  simp [fullMatch, idMatch]

/--
The local session id reported by `info` is the state's local session id, whether or not the local
session is active.
-/
theorem State.info_localSessionId (st : State α) : st.info.localSessionId = st.localSessionId := by
  unfold State.info
  split <;> rfl

/--
Appending an update whose `expected` is the last `newValue` keeps a queue chained.
-/
theorem CASChained.append_single {l : List (Update α)} {u : Update α} (h : CASChained l)
    (h_last : ∀ x ∈ l.getLast?, x.2 = u.1) : CASChained (l ++ [u]) := by
  induction l with
  | nil => trivial
  | cons a rest ih =>
    cases rest with
    | nil =>
      rcases a with ⟨e, n⟩
      rcases u with ⟨e', n'⟩
      exact ⟨h_last (e, n) rfl, trivial⟩
    | cons b rest' =>
      rcases a with ⟨ea, na⟩
      rcases b with ⟨eb, nb⟩
      obtain ⟨h1, h2⟩ := h
      exact ⟨h1, ih h2 (by simpa [List.getLast?_cons_cons] using h_last)⟩

/--
An upstream change either keeps the local session, with the same local id and the same shown
value, or starts a new local session with the fresh id.
-/
theorem stepSetValueFromUpstream_session (st : State α) (newUpstream : SessionValue α) (freshId : Uuid) :
    ((stepSetValueFromUpstream st newUpstream freshId).localSessionId = st.localSessionId ∧
      (stepSetValueFromUpstream st newUpstream freshId).sessionValue = st.sessionValue) ∨
    (stepSetValueFromUpstream st newUpstream freshId).localSessionId = freshId := by
  unfold stepSetValueFromUpstream
  by_cases hc : (newUpstream.sessionId != st.upstreamSessionValue.sessionId ||
      newUpstream.valueId != st.upstreamSessionValue.valueId) = true
  · simp only [hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases h : st.localSessionValue with
    | none =>
      right
      simp
    | some lv =>
      by_cases hd : newUpstream.sessionId = lv.sessionId
      · left
        simp [hd, State.sessionValue, h]
      · right
        simp [hd]
  · simp only [Bool.not_eq_true] at hc
    simp [hc]

theorem QueueInv.empty (st : State α) : QueueInv st [] :=
  ⟨[], [], rfl, by simp, ⟨by simp, trivial, by simp⟩⟩

theorem QueueInv.setValue {st : State α} {q : List (Update α)} (v : α) (vid : Uuid)
    (h : QueueInv st q) :
    QueueInv (stepSetValue st v vid).1 (q ++ [(stepSetValue st v vid).2]) := by
  obtain ⟨stale, cur, rfl, hstale, hcur⟩ := h
  refine ⟨stale, cur ++ [(stepSetValue st v vid).2], by simp, hstale, ?_, ?_, ?_⟩
  · intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · exact hcur.tagged u hu
    · simp only [List.mem_singleton] at hu
      subst hu
      rfl
  · exact CASChained.append_single hcur.chained (fun x hx => hcur.last_shown x hx)
  · intro u hu
    simp only [List.getLast?_concat, Option.mem_def, Option.some.injEq] at hu
    subst hu
    rfl

theorem QueueInv.upstream {st : State α} {q : List (Update α)} (newUpstream : SessionValue α)
    (freshId : Uuid) (h_unused : ∀ u ∈ q, u.2.sessionId ≠ freshId) (h : QueueInv st q) :
    QueueInv (stepSetValueFromUpstream st newUpstream freshId) q := by
  rcases stepSetValueFromUpstream_session st newUpstream freshId with ⟨hid, hsv⟩ | hid
  · obtain ⟨stale, cur, hq, hstale, hcur⟩ := h
    refine ⟨stale, cur, hq, ?_, ?_, hcur.chained, ?_⟩
    · intro u hu
      rw [hid]
      exact hstale u hu
    · intro u hu
      rw [hid]
      exact hcur.tagged u hu
    · intro u hu
      rw [hsv]
      exact hcur.last_shown u hu
  · refine ⟨q, [], by simp, ?_, ⟨by simp, trivial, by simp⟩⟩
    intro u hu
    rw [hid]
    exact h_unused u hu

/--
Implementation proof of `asyncReachable_invariant`.
-/
theorem asyncReachable_invariant_Impl {st : State α} {q : List (Update α)} (h : AsyncReachable st q) :
    ValidState st ∧ QueueInv st q := by
  induction h with
  | init u0 localId h_fresh =>
    exact ⟨initialState_valid_Impl u0 localId h_fresh, QueueInv.empty _⟩
  | setValue v vid _ ih =>
    exact ⟨stepSetValue_preserves_valid_Impl _ v vid, ih.2.setValue v vid⟩
  | upstream newUpstream freshId h_fresh h_unused _ ih =>
    exact ⟨stepSetValueFromUpstream_preserves_valid_Impl _ newUpstream freshId ih.1 h_fresh,
      ih.2.upstream newUpstream freshId h_unused⟩
  | flush _ ih =>
    exact ⟨ih.1, QueueInv.empty _⟩

theorem pruneStaleUpdates_stale_append (info : LocalSessionInfo) (stale cur : List (Update α))
    (hstale : ∀ u ∈ stale, info.isCurrentSessionUpdate u.2 = false)
    (hcur : ∀ u ∈ cur.head?, info.isCurrentSessionUpdate u.2 = true) :
    pruneStaleUpdates info (stale ++ cur) = cur := by
  unfold pruneStaleUpdates
  induction stale with
  | nil =>
    cases cur with
    | nil => rfl
    | cons c rest =>
      simp [hcur c rfl]
  | cons s rest ih =>
    simp only [List.cons_append, List.dropWhile_cons, hstale s List.mem_cons_self, Bool.not_false,
      ↓reduceIte]
    exact ih (fun u hu => hstale u (List.mem_cons_of_mem _ hu))

/--
Implementation proof of `pruneStaleUpdates_exact`.
-/
theorem pruneStaleUpdates_exact_Impl {st : State α} {q : List (Update α)} (h : QueueInv st q) :
    ∃ stale, q = stale ++ pruneStaleUpdates st.info q ∧
      (∀ u ∈ stale, u.2.sessionId ≠ st.info.localSessionId) ∧
      (∀ u ∈ pruneStaleUpdates st.info q, u.2.sessionId = st.info.localSessionId) ∧
      CASChained (pruneStaleUpdates st.info q) ∧
      (∀ u ∈ (pruneStaleUpdates st.info q).getLast?, u.2 = st.sessionValue) := by
  obtain ⟨stale, cur, rfl, hstale, hcur⟩ := h
  have hid := State.info_localSessionId st
  have hp : pruneStaleUpdates st.info (stale ++ cur) = cur := by
    apply pruneStaleUpdates_stale_append
    · intro u hu
      simp [LocalSessionInfo.isCurrentSessionUpdate, hid, hstale u hu]
    · intro u hu
      simp [LocalSessionInfo.isCurrentSessionUpdate, hid,
        hcur.tagged u (List.mem_of_mem_head? hu)]
  rw [hp, hid]
  exact ⟨stale, rfl, hstale, hcur.tagged, hcur.chained, hcur.last_shown⟩

/--
Implementation proof of `async_batch_sound`.
-/
theorem async_batch_sound_Impl {st : State α} {q : List (Update α)} (h : AsyncReachable st q)
    (accepts : SessionValue α → SessionValue α → Bool) (h_refl : ∀ v, accepts v v = true)
    (current : SessionValue α) (hp : pruneStaleUpdates st.info q ≠ []) :
    casApplyAllWith accepts current (pruneStaleUpdates st.info q) =
      casApplyWith accepts current (batchUpdate _ hp).1 (batchUpdate _ hp).2 ∧
    (batchUpdate _ hp).2 = st.sessionValue := by
  obtain ⟨_, hq⟩ := asyncReachable_invariant_Impl h
  obtain ⟨_, _, _, _, hchain, hlast⟩ := pruneStaleUpdates_exact_Impl hq
  refine ⟨batch_cas_equivalence_Impl accepts h_refl current _ hp hchain, ?_⟩
  exact hlast ((pruneStaleUpdates st.info q).getLast hp) (List.getLast?_eq_some_getLast hp)

/--
Implementation proof of functorial identity for `SessionValue.map`.
-/
theorem sessionValue_map_id_Impl (sv : SessionValue α) : sv.map id = sv := by
  cases sv
  rfl

/--
Implementation proof of functorial composition for `SessionValue.map`.
-/
theorem sessionValue_map_comp_Impl (f : α → β) (g : β → γ) (sv : SessionValue α) :
    (sv.map f).map g = sv.map (g ∘ f) := by
  cases sv
  rfl

/--
Implementation proof of `mapped_setValue_roundtrip`.
-/
theorem mapped_setValue_roundtrip_Impl (st : State α) (transformTo : α → β) (transformFrom : β → α)
    (h_retract : ∀ b, transformTo (transformFrom b) = b) (b : β) (vid : Uuid) :
    let (st', _) := stepSetValue st (transformFrom b) vid
    (st'.map transformTo).sessionValue = { sessionId := st.localSessionId, valueId := vid, value := b } := by
  dsimp [stepSetValue, State.map, State.sessionValue, SessionValue.map]
  rw [h_retract]

end SessionValue
