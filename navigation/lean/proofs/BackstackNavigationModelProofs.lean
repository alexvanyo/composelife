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

import models.BackstackNavigationModel

namespace Navigation.Model

/-! ### Basic Map & Chain Helper Lemmas -/

theorem toChain_length_eq_depth {α : Type} (e : BackstackEntry α) :
    e.toChain.length = e.depth := by
  induction e with
  | root v id => simp [BackstackEntry.toChain, BackstackEntry.depth]
  | node v prev id ih =>
    simp only [BackstackEntry.toChain, BackstackEntry.depth, List.length_cons]
    omega

theorem mem_toChain_self {α : Type} (e : BackstackEntry α) : e ∈ e.toChain := by
  cases e <;> simp [BackstackEntry.toChain]

theorem mem_toChain_depth_le {α : Type} {e head : BackstackEntry α}
    (hm : e ∈ head.toChain) : e.depth ≤ head.depth := by
  induction head with
  | root v id =>
    simp only [BackstackEntry.toChain, List.mem_singleton] at hm
    subst hm
    exact Nat.le_refl _
  | node v prev id ih =>
    simp only [BackstackEntry.toChain, List.mem_cons] at hm
    rcases hm with rfl | hp
    · exact Nat.le_refl _
    · have hle := ih hp
      simp only [BackstackEntry.depth]
      omega

theorem not_mem_prev_toChain {α : Type} (v : α) (prev : BackstackEntry α) (id : EntryId) :
    BackstackEntry.node v prev id ∉ prev.toChain := by
  intro hm
  have hle := mem_toChain_depth_le hm
  simp only [BackstackEntry.depth] at hle
  omega

theorem mem_toChain_of_prev {α : Type} {e p head : BackstackEntry α}
    (hm : e ∈ p.toChain) (hp : head.previous = some p) : e ∈ head.toChain := by
  cases head with
  | root _ _ => simp [BackstackEntry.previous] at hp
  | node v prev id =>
    simp only [BackstackEntry.previous, Option.some.injEq] at hp
    subst hp
    simp only [BackstackEntry.toChain, List.mem_cons]
    exact Or.inr hm

theorem toChain_nodup {α : Type} (e : BackstackEntry α) : e.toChain.Nodup := by
  induction e with
  | root _ _ => simp [BackstackEntry.toChain]
  | node v prev id ih =>
    simp only [BackstackEntry.toChain, List.nodup_cons]
    exact ⟨not_mem_prev_toChain v prev id, ih⟩

theorem toChain_sub_of_mem {α : Type} {x y : BackstackEntry α}
    (hmem : y ∈ x.toChain) : ∀ z ∈ y.toChain, z ∈ x.toChain := by
  induction x with
  | root v id =>
    simp only [BackstackEntry.toChain, List.mem_singleton] at hmem
    subst hmem
    exact fun _ hz => hz
  | node v prev id ih =>
    simp only [BackstackEntry.toChain, List.mem_cons] at hmem
    rcases hmem with rfl | hp
    · exact fun _ hz => hz
    · intro z hz
      simp only [BackstackEntry.toChain, List.mem_cons]
      exact Or.inr (ih hp z hz)

theorem mem_of_mem_drop {α : Type} {l : List α} {k : Nat} {x : α}
    (h : x ∈ l.drop k) : x ∈ l := by
  induction l generalizing k with
  | nil => simp at h
  | cons a tl ih =>
    cases k with
    | zero => simpa using h
    | succ k' =>
      simp only [List.drop_succ_cons] at h
      exact List.mem_cons_of_mem a (ih h)

theorem list_take_succ_eq_append {α : Type} (l : List α) (k : Nat) (x : α) (hx : l[k]? = some x) :
    l.take (k + 1) = l.take k ++ [x] := by
  induction l generalizing k with
  | nil => simp at hx
  | cons a tl ih =>
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      subst hx
      simp
    | succ k' =>
      simp only [List.getElem?_cons_succ] at hx
      simp only [List.take_succ_cons, List.cons_append]
      exact congrArg (a :: ·) (ih k' hx)

theorem list_drop_eq_cons {α : Type} (l : List α) (k : Nat) (x : α) (hx : l[k]? = some x) :
    l.drop k = x :: l.drop (k + 1) := by
  induction l generalizing k with
  | nil => simp at hx
  | cons a tl ih =>
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      subst hx
      simp
    | succ k' =>
      simp only [List.getElem?_cons_succ] at hx
      simp only [List.drop_succ_cons]
      exact ih k' hx

theorem mapLookup_none_of_not_mem_keys {α : Type} {m : BackstackMap α} {k : EntryId}
    (h : k ∉ mapKeys m) : mapLookup m k = none := by
  induction m with
  | nil => rfl
  | cons hd tl ih =>
    simp only [mapKeys, List.map_cons, List.mem_cons, not_or] at h
    have hne : (hd.1 == k) = false := beq_false_of_ne (Ne.symm h.1)
    simp only [mapLookup, List.find?_cons, hne]
    exact ih h.2

private theorem mem_mapKeys_filter {α : Type} (l : BackstackMap α)
    (p : EntryId × BackstackEntry α → Bool) {x : EntryId}
    (hmem : x ∈ mapKeys (l.filter p)) : x ∈ mapKeys l := by
  induction l with
  | nil => simp [mapKeys] at hmem
  | cons a rest ihr =>
    simp only [List.filter_cons] at hmem
    split at hmem
    · simp only [mapKeys, List.map_cons, List.mem_cons] at hmem ⊢
      rcases hmem with rfl | hmem'
      · exact Or.inl rfl
      · exact Or.inr (ihr hmem')
    · simp only [mapKeys, List.map_cons, List.mem_cons]
      exact Or.inr (ihr hmem)

theorem mapKeys_filter_nodup {α : Type} (m : BackstackMap α) (p : EntryId × BackstackEntry α → Bool)
    (hnd : (mapKeys m).Nodup) : (mapKeys (m.filter p)).Nodup := by
  induction m with
  | nil => exact hnd
  | cons hd tl ih =>
    simp only [mapKeys, List.map_cons, List.nodup_cons] at hnd
    simp only [List.filter_cons]
    split
    · simp only [mapKeys, List.map_cons, List.nodup_cons]
      exact ⟨fun hmem => hnd.1 (mem_mapKeys_filter tl p hmem), ih hnd.2⟩
    · exact ih hnd.2

theorem mapKeys_mapRemove_nodup {α : Type} {m : BackstackMap α} (k : EntryId)
    (hnd : (mapKeys m).Nodup) : (mapKeys (mapRemove m k)).Nodup :=
  mapKeys_filter_nodup m (fun p => p.1 != k) hnd

theorem not_mem_mapKeys_mapRemove {α : Type} (m : BackstackMap α) (k : EntryId) :
    k ∉ mapKeys (mapRemove m k) := by
  induction m with
  | nil => simp [mapRemove, mapKeys]
  | cons hd tl ih =>
    simp only [mapRemove, List.filter_cons]
    split
    · next hne =>
      simp only [bne_iff_ne, ne_eq] at hne
      simp only [mapKeys, List.map_cons, List.mem_cons, not_or]
      exact ⟨Ne.symm hne, ih⟩
    · exact ih

theorem mapKeys_mapPut_nodup {α : Type} {m : BackstackMap α} (k : EntryId) (v : BackstackEntry α)
    (hnd : (mapKeys m).Nodup) : (mapKeys (mapPut m k v)).Nodup := by
  simp only [mapPut, mapKeys, List.map_cons, List.nodup_cons]
  exact ⟨not_mem_mapKeys_mapRemove m k, mapKeys_mapRemove_nodup k hnd⟩

theorem mapLookup_mapRemove_self {α : Type} (m : BackstackMap α) (k : EntryId) :
    mapLookup (mapRemove m k) k = none :=
  mapLookup_none_of_not_mem_keys (not_mem_mapKeys_mapRemove m k)

theorem mapLookup_mapRemove_ne {α : Type} (m : BackstackMap α) {k q : EntryId} (hne : q ≠ k) :
    mapLookup (mapRemove m k) q = mapLookup m q := by
  induction m with
  | nil => rfl
  | cons hd tl ih =>
    simp only [mapRemove, List.filter_cons]
    by_cases hhk : hd.1 = k
    · have h1 : (hd.1 != k) = false := by simp [hhk]
      have h2 : (hd.1 == q) = false := beq_false_of_ne (by rw [hhk]; exact Ne.symm hne)
      simp only [h1, Bool.false_eq_true, ↓reduceIte, mapLookup, List.find?_cons, h2]
      exact ih
    · have h1 : (hd.1 != k) = true := by simp [hhk]
      simp only [h1, ↓reduceIte, mapLookup, List.find?_cons]
      by_cases hhq : hd.1 = q
      · simp [hhq]
      · have h2 : (hd.1 == q) = false := beq_false_of_ne hhq
        simp only [h2]
        exact ih

theorem mapRemove_of_lookup_none {α : Type} {m : BackstackMap α} {k : EntryId}
    (hnone : mapLookup m k = none) : mapRemove m k = m := by
  induction m with
  | nil => rfl
  | cons hd tl ih =>
    by_cases heq : hd.1 = k
    · simp [mapLookup, heq] at hnone
    · have hne : (hd.1 == k) = false := beq_false_of_ne heq
      simp only [mapLookup, List.find?_cons, hne] at hnone
      have hbne : (hd.1 != k) = true := bne_iff_ne.mpr heq
      simp only [mapRemove, List.filter_cons, hbne, ↓reduceIte]
      exact congrArg (hd :: ·) (ih hnone)

theorem mapLookup_mapPut_self {α : Type} (m : BackstackMap α) (k : EntryId) (v : BackstackEntry α) :
    mapLookup (mapPut m k v) k = some v := by
  simp [mapPut, mapLookup]

theorem mapLookup_mapPut_ne {α : Type} (m : BackstackMap α) {k q : EntryId} (v : BackstackEntry α)
    (hne : q ≠ k) : mapLookup (mapPut m k v) q = mapLookup m q := by
  have hkq : (k == q) = false := beq_false_of_ne (Ne.symm hne)
  simp only [mapPut, mapLookup, List.find?_cons, hkq]
  exact mapLookup_mapRemove_ne m hne

theorem mapPut_of_lookup_none {α : Type} {m : BackstackMap α} {k : EntryId} (v : BackstackEntry α)
    (hnone : mapLookup m k = none) : mapPut m k v = (k, v) :: m := by
  change (k, v) :: mapRemove m k = (k, v) :: m
  rw [mapRemove_of_lookup_none hnone]

theorem mapRemove_cons_eq {α : Type} (m : BackstackMap α) (k : EntryId) (v : BackstackEntry α)
    (hnone : mapLookup m k = none) :
    mapRemove ((k, v) :: m) k = m := by
  have hfalse : (k != k) = false := by simp
  simp only [mapRemove, List.filter_cons, hfalse, Bool.false_eq_true, ↓reduceIte]
  exact mapRemove_of_lookup_none hnone

/-! ### WellFormedBackstack Helpers -/

theorem wellFormed_chain_ids_distinct {α : Type} {m : BackstackMap α} {curId : EntryId}
    (hwf : WellFormedBackstack m curId) {head e1 e2 : BackstackEntry α}
    (hhead : mapLookup m curId = some head)
    (he1 : e1 ∈ head.toChain) (he2 : e2 ∈ head.toChain) (hid : e1.id = e2.id) :
    e1 = e2 := by
  have hm1 : mapLookup m e1.id = some e1 := (hwf.chainMatchesMap head hhead e1.id e1).mpr ⟨he1, rfl⟩
  have hm2 : mapLookup m e2.id = some e2 := (hwf.chainMatchesMap head hhead e2.id e2).mpr ⟨he2, rfl⟩
  rw [hid] at hm1
  rw [hm1] at hm2
  exact Option.some.inj hm2

/-! ### 1. Navigate Theorem Proofs -/

theorem navigate_preserves_wellFormed_Impl {α : Type}
    (m : BackstackMap α) (curId : EntryId) (vf : BackstackEntry α → α) (freshId : EntryId)
    (hwf : WellFormedBackstack m curId) (hfresh : mapLookup m freshId = none) :
    ∃ head' m',
      navigateModel m curId vf freshId = .ok m' freshId ∧
      WellFormedBackstack m' freshId ∧
      mapLookup m' freshId = some head' ∧
      (∀ k, mapLookup m k ≠ none → mapLookup m' k = mapLookup m k) ∧
      (∀ head, mapLookup m curId = some head → head'.depth = head.depth + 1) := by
  obtain ⟨head, hhead⟩ := hwf.headSome
  let head' : BackstackEntry α := .node (vf head) head freshId
  let m' : BackstackMap α := mapPut m freshId head'
  have hnav : navigateModel m curId vf freshId = .ok m' freshId := by
    simp [navigateModel, hhead, head', m']
  have hlookup_new : mapLookup m' freshId = some head' := mapLookup_mapPut_self m freshId head'
  have hwf' : WellFormedBackstack m' freshId := {
    noDupKeys := mapKeys_mapPut_nodup freshId head' hwf.noDupKeys
    headSome := ⟨head', hlookup_new⟩
    chainMatchesMap := by
      intro h0 hh0 k e
      rw [hlookup_new] at hh0
      have h0eq : head' = h0 := Option.some.inj hh0
      subst h0eq
      by_cases hkf : k = freshId
      · subst hkf
        rw [hlookup_new]
        constructor
        · intro heq
          have he : head' = e := Option.some.inj heq
          subst he
          exact ⟨mem_toChain_self head', rfl⟩
        · rintro ⟨hmem, heid⟩
          simp only [head', BackstackEntry.toChain, List.mem_cons] at hmem
          rcases hmem with rfl | hprev
          · rfl
          · have hm : mapLookup m e.id = some e := (hwf.chainMatchesMap head hhead e.id e).mpr ⟨hprev, rfl⟩
            rw [heid, hfresh] at hm
            cases hm
      · rw [mapLookup_mapPut_ne m head' hkf]
        rw [hwf.chainMatchesMap head hhead k e]
        constructor
        · rintro ⟨hmem, heid⟩
          exact ⟨by simp only [head', BackstackEntry.toChain, List.mem_cons]; exact Or.inr hmem, heid⟩
        · rintro ⟨hmem, heid⟩
          simp only [head', BackstackEntry.toChain, List.mem_cons] at hmem
          rcases hmem with rfl | hprev
          · exact absurd heid (Ne.symm hkf)
          · exact ⟨hprev, heid⟩
  }
  refine ⟨head', m', hnav, hwf', hlookup_new, ?_, ?_⟩
  · intro k hk
    have hne : k ≠ freshId := fun heq => hk (by simpa [heq] using hfresh)
    exact mapLookup_mapPut_ne m head' hne
  · intro h1 hh1
    rw [hhead] at hh1
    have h1eq : head = h1 := Option.some.inj hh1
    subst h1eq
    dsimp only [head', BackstackEntry.depth]
    omega

/-! ### 2. PopBackstack Theorem Proofs -/

theorem popBackstack_throws_on_root_Impl {α : Type}
    (m : BackstackMap α) (curId : EntryId) (head : BackstackEntry α)
    (hhead : mapLookup m curId = some head) (hdepth : head.depth = 1) :
    popBackstackModel m curId = .error .popLastEntry := by
  cases head with
  | root v id => simp [popBackstackModel, hhead, BackstackEntry.previous]
  | node v p id =>
    simp only [BackstackEntry.depth] at hdepth
    have hp : 1 ≤ p.depth := by
      cases p <;> simp [BackstackEntry.depth] <;> omega
    omega

theorem popBackstack_preserves_wellFormed_Impl {α : Type}
    (m : BackstackMap α) (curId : EntryId) (head prev : BackstackEntry α)
    (hwf : WellFormedBackstack m curId)
    (hhead : mapLookup m curId = some head)
    (hprev : head.previous = some prev) :
    popBackstackModel m curId = .ok (mapRemove m head.id) prev.id ∧
    WellFormedBackstack (mapRemove m head.id) prev.id ∧
    mapLookup (mapRemove m head.id) head.id = none ∧
    (∀ k, k ≠ head.id → mapLookup (mapRemove m head.id) k = mapLookup m k) := by
  have hpop : popBackstackModel m curId = .ok (mapRemove m head.id) prev.id := by
    simp [popBackstackModel, hhead, hprev]
  have hprev_mem : prev ∈ head.toChain := by
    cases head with
    | root _ _ => simp [BackstackEntry.previous] at hprev
    | node v p0 id0 =>
      simp only [BackstackEntry.previous, Option.some.injEq] at hprev
      rw [← hprev]
      simp only [BackstackEntry.toChain, List.mem_cons]
      exact Or.inr (mem_toChain_self p0)
  have hne_ids : prev.id ≠ head.id := by
    intro heq
    have hpeq := wellFormed_chain_ids_distinct hwf hhead hprev_mem (mem_toChain_self head) heq
    have hdep := congrArg BackstackEntry.depth hpeq
    cases head with
    | root _ _ => simp [BackstackEntry.previous] at hprev
    | node v p0 id0 =>
      simp only [BackstackEntry.previous, Option.some.injEq] at hprev
      rw [← hprev] at hdep
      simp only [BackstackEntry.depth] at hdep
      omega
  have hprev_lookup : mapLookup (mapRemove m head.id) prev.id = some prev := by
    rw [mapLookup_mapRemove_ne m hne_ids]
    exact (hwf.chainMatchesMap head hhead prev.id prev).mpr ⟨hprev_mem, rfl⟩
  have hwf' : WellFormedBackstack (mapRemove m head.id) prev.id := {
    noDupKeys := mapKeys_mapRemove_nodup head.id hwf.noDupKeys
    headSome := ⟨prev, hprev_lookup⟩
    chainMatchesMap := by
      intro h0 hh0 k e
      rw [hprev_lookup] at hh0
      have h0eq : prev = h0 := Option.some.inj hh0
      subst h0eq
      by_cases hkh : k = head.id
      · subst hkh
        rw [mapLookup_mapRemove_self]
        constructor
        · intro h; cases h
        · rintro ⟨hmem, heid⟩
          have hmem' : e ∈ head.toChain := mem_toChain_of_prev hmem hprev
          have heq := wellFormed_chain_ids_distinct hwf hhead hmem' (mem_toChain_self head) heid
          have hdep := mem_toChain_depth_le hmem
          have hdep_eq := congrArg BackstackEntry.depth heq
          cases head with
          | root _ _ => simp [BackstackEntry.previous] at hprev
          | node v p0 id0 =>
            simp only [BackstackEntry.previous, Option.some.injEq] at hprev
            rw [← hprev] at hdep
            simp only [BackstackEntry.depth] at hdep hdep_eq
            omega
      · rw [mapLookup_mapRemove_ne m hkh]
        rw [hwf.chainMatchesMap head hhead k e]
        constructor
        · rintro ⟨hmem, heid⟩
          cases head with
          | root _ _ => simp [BackstackEntry.previous] at hprev
          | node v p0 id0 =>
            simp only [BackstackEntry.previous, Option.some.injEq] at hprev
            simp only [BackstackEntry.toChain, List.mem_cons] at hmem
            rcases hmem with rfl | hp
            · exact absurd heid (Ne.symm hkh)
            · rw [← hprev]; exact ⟨hp, heid⟩
        · rintro ⟨hmem, heid⟩
          exact ⟨mem_toChain_of_prev hmem hprev, heid⟩
  }
  refine ⟨hpop, hwf', mapLookup_mapRemove_self m head.id, fun k hne => mapLookup_mapRemove_ne m hne⟩

/-! ### 3. Roundtrip `popBackstack ∘ navigate(freshId)` Theorem Proof -/

theorem popBackstack_navigate_inverse_Impl {α : Type}
    (m : BackstackMap α) (curId : EntryId) (vf : BackstackEntry α → α) (freshId : EntryId)
    (hwf : WellFormedBackstack m curId) (hfresh : mapLookup m freshId = none) :
    match navigateModel m curId vf freshId with
    | .ok m' newId => popBackstackModel m' newId = .ok m curId
    | .error _ => False := by
  obtain ⟨head, hhead⟩ := hwf.headSome
  have hid : head.id = curId := ((hwf.chainMatchesMap head hhead curId head).mp hhead).2
  let head' : BackstackEntry α := .node (vf head) head freshId
  have hput : mapPut m freshId head' = (freshId, head') :: m := mapPut_of_lookup_none head' hfresh
  have hnav : navigateModel m curId vf freshId = .ok ((freshId, head') :: m) freshId := by
    simp [navigateModel, hhead, head', hput]
  rw [hnav]
  have hlookup : mapLookup ((freshId, head') :: m) freshId = some head' := by
    simp [mapLookup]
  have hrem : mapRemove ((freshId, head') :: m) freshId = m := mapRemove_cons_eq m freshId head' hfresh
  simp [popBackstackModel, hlookup, head', BackstackEntry.previous, BackstackEntry.id, hrem]
  exact hid

/-! ### 4. `popUpTo` Termination & Exact Popped-Slice Proofs -/

private theorem popUpToWalk_step_none {α : Type} (pred : BackstackEntry α → Bool)
    {m : BackstackMap α} {curId : EntryId} (hwf : WellFormedBackstack m curId)
    {head : BackstackEntry α} (hhead : mapLookup m curId = some head)
    (hm : matchDistance? pred head = none) :
    popUpToWalk pred m head = none := by
  induction head generalizing m curId with
  | root v id =>
    have hpred : pred (.root v id) = false := by
      cases hp : pred (.root v id)
      · rfl
      · simp [matchDistance?, hp] at hm
    simp [popUpToWalk, hpred]
  | node v p id ih =>
    have hpred : pred (.node v p id) = false := by
      cases hp : pred (.node v p id)
      · rfl
      · simp [matchDistance?, hp] at hm
    have hm_p : matchDistance? pred p = none := by
      simp only [matchDistance?, hpred] at hm
      cases hd : matchDistance? pred p <;> simp [hd] at hm
      rfl
    have hpop := popBackstack_preserves_wellFormed_Impl m curId (.node v p id) p hwf hhead rfl
    have hne_p : p.id ≠ id := by
      intro heq
      have hmem : p ∈ (BackstackEntry.node v p id).toChain := by
        simp only [BackstackEntry.toChain, List.mem_cons]
        exact Or.inr (mem_toChain_self p)
      have he := wellFormed_chain_ids_distinct hwf hhead hmem (mem_toChain_self _) heq
      have hdep := congrArg BackstackEntry.depth he
      simp only [BackstackEntry.depth] at hdep
      omega
    have hlookup_p : mapLookup (mapRemove m id) p.id = some p := by
      have h2 := hpop.2.2.2 p.id hne_p
      change mapLookup (mapRemove m id) p.id = mapLookup m p.id at h2
      rw [h2]
      exact (hwf.chainMatchesMap (.node v p id) hhead p.id p).mpr
        ⟨by simp only [BackstackEntry.toChain, List.mem_cons]; exact Or.inr (mem_toChain_self p), rfl⟩
    simp only [popUpToWalk, hpred]
    exact ih hpop.2.1 hlookup_p hm_p

private theorem popUpToWalk_fuel_and_slice {α : Type} (pred : BackstackEntry α → Bool)
    {m : BackstackMap α} {curId : EntryId} (hwf : WellFormedBackstack m curId)
    {head : BackstackEntry α} (hhead : mapLookup m curId = some head)
    {k : Nat} (hk : matchDistance? pred head = some k) :
    ∃ m' target,
      popUpToWalk pred m head = popUpToWalkFuel pred k m head ∧
      popUpToWalk pred m head = some (m', target) ∧
      WellFormedBackstack m' target.id ∧
      mapLookup m' target.id = some target ∧
      head.toChain[k]? = some target ∧
      (∀ e ∈ head.toChain.take k, mapLookup m' e.id = none) ∧
      (∀ e ∈ head.toChain.drop k, mapLookup m' e.id = some e) := by
  induction k generalizing m curId head with
  | zero =>
    have hpred : pred head = true := by
      cases hp : pred head
      · cases head with
        | root v i => simp [matchDistance?, hp] at hk
        | node v p i => cases hd : matchDistance? pred p <;> simp [matchDistance?, hp, hd] at hk
      · rfl
    have hid : head.id = curId := ((hwf.chainMatchesMap head hhead curId head).mp hhead).2
    have hwf' : WellFormedBackstack m head.id := by rw [hid]; exact hwf
    have hlookup_self : mapLookup m head.id = some head := by rw [hid]; exact hhead
    have hhd : head.toChain[0]? = some head := by
      cases head <;> simp [BackstackEntry.toChain]
    refine ⟨m, head, ?_, ?_, hwf', hlookup_self, hhd, ?_, ?_⟩
    · cases head <;> simp [popUpToWalk, popUpToWalkFuel, hpred]
    · cases head <;> simp [popUpToWalk, hpred]
    · intro e he; simp at he
    · intro e he
      simp only [List.drop_zero] at he
      exact (hwf.chainMatchesMap head hhead e.id e).mpr ⟨he, rfl⟩
  | succ k' ih =>
    cases head with
    | root v id =>
      cases hp : pred (.root v id) <;> simp [matchDistance?, hp] at hk
    | node v p id =>
      have hpred : pred (.node v p id) = false := by
        cases hp : pred (.node v p id)
        · rfl
        · simp [matchDistance?, hp] at hk
      simp only [matchDistance?, hpred] at hk
      cases hdp : matchDistance? pred p with
      | none => simp [hdp] at hk
      | some d =>
        have hdk : d = k' := by
          simp [hdp] at hk
          omega
        subst hdk
        have hpop := popBackstack_preserves_wellFormed_Impl m curId (.node v p id) p hwf hhead rfl
        have hne_p : p.id ≠ id := by
          intro heq
          have hmem : p ∈ (BackstackEntry.node v p id).toChain := by
            simp only [BackstackEntry.toChain, List.mem_cons]
            exact Or.inr (mem_toChain_self p)
          have he := wellFormed_chain_ids_distinct hwf hhead hmem (mem_toChain_self _) heq
          have hdep := congrArg BackstackEntry.depth he
          simp only [BackstackEntry.depth] at hdep
          omega
        have hlookup_p : mapLookup (mapRemove m id) p.id = some p := by
          have h2 := hpop.2.2.2 p.id hne_p
          change mapLookup (mapRemove m id) p.id = mapLookup m p.id at h2
          rw [h2]
          exact (hwf.chainMatchesMap (.node v p id) hhead p.id p).mpr
            ⟨by simp only [BackstackEntry.toChain, List.mem_cons]; exact Or.inr (mem_toChain_self p), rfl⟩
        obtain ⟨m', target, hfuel, hwalk, hwf', hlookup_t, hget', htake', hdrop'⟩ :=
          ih hpop.2.1 hlookup_p hdp
        refine ⟨m', target, ?_, ?_, hwf', hlookup_t, ?_, ?_, ?_⟩
        · simp only [popUpToWalk, popUpToWalkFuel, hpred]
          exact hfuel
        · simp only [popUpToWalk, hpred]
          exact hwalk
        · simpa [BackstackEntry.toChain] using hget'
        · intro e he
          simp only [BackstackEntry.toChain, List.take_succ_cons, List.mem_cons] at he
          rcases he with rfl | he'
          · dsimp only [BackstackEntry.id]
            cases hm'_id : mapLookup m' id with
            | none => rfl
            | some e0 =>
              have hmem_e0 : e0 ∈ target.toChain :=
                ((hwf'.chainMatchesMap target hlookup_t id e0).mp hm'_id).1
              have he0_id : e0.id = id :=
                ((hwf'.chainMatchesMap target hlookup_t id e0).mp hm'_id).2
              have htar_in_p : target ∈ p.toChain := List.mem_of_getElem? hget'
              have he0_p : e0 ∈ p.toChain := toChain_sub_of_mem htar_in_p e0 hmem_e0
              have hin : e0 ∈ (BackstackEntry.node v p id).toChain :=
                mem_toChain_of_prev he0_p rfl
              have he0_eq := wellFormed_chain_ids_distinct hwf hhead hin (mem_toChain_self _) he0_id
              subst he0_eq
              exact absurd he0_p (not_mem_prev_toChain v p id)
          · exact htake' e he'
        · intro e he
          simp only [BackstackEntry.toChain, List.drop_succ_cons] at he
          exact hdrop' e he

theorem popUpTo_terminates_and_slices_Impl {α : Type}
    (m : BackstackMap α) (curId : EntryId) (pred : BackstackEntry α → Bool)
    (inclusive : Bool) (head : BackstackEntry α) (k : Nat)
    (hwf : WellFormedBackstack m curId) (hhead : mapLookup m curId = some head)
    (hk : matchDistance? pred head = some k) :
    popUpToWalk pred m head = popUpToWalkFuel pred k m head ∧
    ∃ target, head.toChain[k]? = some target ∧
    if inclusive then
      match target.previous with
      | none => popUpToModel m curId pred true = .error .popLastEntry
      | some prev =>
        ∃ m',
          popUpToModel m curId pred true = .ok m' prev.id ∧
          WellFormedBackstack m' prev.id ∧
          (∀ e ∈ head.toChain.take (k + 1), mapLookup m' e.id = none) ∧
          (∀ e ∈ head.toChain.drop (k + 1), mapLookup m' e.id = some e)
    else
      ∃ m',
        popUpToModel m curId pred false = .ok m' target.id ∧
        WellFormedBackstack m' target.id ∧
        (∀ e ∈ head.toChain.take k, mapLookup m' e.id = none) ∧
        (∀ e ∈ head.toChain.drop k, mapLookup m' e.id = some e) := by
  obtain ⟨m1, target, hfuel, hwalk, hwf1, hlookup_t, hget, htake, hdrop⟩ :=
    popUpToWalk_fuel_and_slice pred hwf hhead hk
  refine ⟨hfuel, target, hget, ?_⟩
  cases inclusive
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨m1, ?_, hwf1, htake, hdrop⟩
    simp [popUpToModel, hhead, hwalk]
  · simp only [↓reduceIte]
    cases hprev : target.previous with
    | none =>
      simp [popUpToModel, hhead, hwalk, hprev]
    | some prev =>
      have hpop := popBackstack_preserves_wellFormed_Impl m1 target.id target prev hwf1 hlookup_t hprev
      refine ⟨mapRemove m1 target.id, ?_, hpop.2.1, ?_, ?_⟩
      · simp [popUpToModel, hhead, hwalk, hprev]
      · intro e he
        rw [list_take_succ_eq_append head.toChain k target hget, List.mem_append, List.mem_singleton] at he
        rcases he with he_take | he_eq
        · by_cases hid_eq : e.id = target.id
          · rw [hid_eq]
            exact hpop.2.2.1
          · rw [hpop.2.2.2 e.id hid_eq]
            exact htake e he_take
        · rw [he_eq]
          exact hpop.2.2.1
      · intro e he
        have he_drop_k : e ∈ head.toChain.drop k := by
          rw [list_drop_eq_cons head.toChain k target hget]
          exact List.mem_cons_of_mem _ he
        have he_chain : e ∈ head.toChain := mem_of_mem_drop he_drop_k
        have htar_chain : target ∈ head.toChain := List.mem_of_getElem? hget
        have he_ne_tar : e.id ≠ target.id := by
          intro hid_eq
          have he_eq_tar := wellFormed_chain_ids_distinct hwf hhead he_chain htar_chain hid_eq
          subst he_eq_tar
          have hnd : head.toChain.Nodup := toChain_nodup head
          have hdrop_nd : (head.toChain.drop k).Nodup := hnd.sublist (List.drop_sublist k head.toChain)
          rw [list_drop_eq_cons head.toChain k e hget, List.nodup_cons] at hdrop_nd
          exact hdrop_nd.1 he
        rw [hpop.2.2.2 e.id he_ne_tar]
        exact hdrop e he_drop_k

theorem popUpTo_throws_when_no_match_Impl {α : Type}
    (m : BackstackMap α) (curId : EntryId) (pred : BackstackEntry α → Bool)
    (inclusive : Bool) (head : BackstackEntry α)
    (hwf : WellFormedBackstack m curId) (hhead : mapLookup m curId = some head)
    (hnone : matchDistance? pred head = none) :
    popUpToModel m curId pred inclusive = .error .predicateNotFound := by
  have hwalk := popUpToWalk_step_none pred hwf hhead hnone
  simp [popUpToModel, hhead, hwalk]

private theorem matchDistance_toChain_pred {α : Type} (pred : BackstackEntry α → Bool)
    (head : BackstackEntry α) (k : Nat) (target : BackstackEntry α)
    (hk : matchDistance? pred head = some k) (hget : head.toChain[k]? = some target) :
    pred target = true := by
  induction head generalizing k with
  | root v id =>
    cases hp : pred (.root v id)
    · simp [matchDistance?, hp] at hk
    · simp only [matchDistance?, hp, ↓reduceIte, Option.some.injEq] at hk
      subst hk
      simp only [BackstackEntry.toChain, List.getElem?_cons_zero, Option.some.injEq] at hget
      rw [← hget]
      exact hp
  | node v p id ih =>
    cases hp : pred (.node v p id)
    · simp only [matchDistance?, hp, Bool.false_eq_true, ↓reduceIte] at hk
      cases hd : matchDistance? pred p with
      | none => simp [hd] at hk
      | some d =>
        simp only [hd, Option.map_some, Option.some.injEq] at hk
        subst hk
        simp only [BackstackEntry.toChain, List.getElem?_cons_succ] at hget
        exact ih d hd hget
    · simp only [matchDistance?, hp, ↓reduceIte, Option.some.injEq] at hk
      subst hk
      simp only [BackstackEntry.toChain, List.getElem?_cons_zero, Option.some.injEq] at hget
      rw [← hget]
      exact hp

theorem popUpToId_slices_to_ancestor_Impl {α : Type}
    (m : BackstackMap α) (curId targetId : EntryId) (inclusive : Bool)
    (head : BackstackEntry α) (k : Nat)
    (hwf : WellFormedBackstack m curId) (hhead : mapLookup m curId = some head)
    (hk : matchDistance? (fun e => e.id == targetId) head = some k) :
    ∃ target, head.toChain[k]? = some target ∧
    target.id = targetId ∧
    if inclusive then
      match target.previous with
      | none => popUpToIdModel m curId targetId true = .error .popLastEntry
      | some prev =>
        ∃ m',
          popUpToIdModel m curId targetId true = .ok m' prev.id ∧
          WellFormedBackstack m' prev.id
    else
      ∃ m',
        popUpToIdModel m curId targetId false = .ok m' targetId ∧
        WellFormedBackstack m' targetId := by
  have hmain := popUpTo_terminates_and_slices_Impl m curId (fun e => e.id == targetId)
    inclusive head k hwf hhead hk
  obtain ⟨_, target, hget, hbody⟩ := hmain
  have htar_pred : (target.id == targetId) = true :=
    matchDistance_toChain_pred (fun e => e.id == targetId) head k target hk hget
  have hid_eq : target.id = targetId := beq_iff_eq.mp htar_pred
  refine ⟨target, hget, hid_eq, ?_⟩
  cases inclusive
  · obtain ⟨m', hok, hwf', _, _⟩ := hbody
    rw [hid_eq] at hok hwf'
    exact ⟨m', hok, hwf'⟩
  · cases hprev : target.previous with
    | none => simpa [popUpToIdModel, hprev] using hbody
    | some prev =>
      simp only [↓reduceIte, hprev] at hbody
      obtain ⟨m', hok, hwf', _, _⟩ := hbody
      exact ⟨m', hok, hwf'⟩

theorem popUpToValue_slices_to_matching_value_Impl {α : Type}
    (m : BackstackMap α) (curId : EntryId) (pred : α → Bool) (inclusive : Bool)
    (head : BackstackEntry α) (k : Nat)
    (hwf : WellFormedBackstack m curId) (hhead : mapLookup m curId = some head)
    (hk : matchDistance? (fun e => pred e.value) head = some k) :
    popUpToWalk (fun e => pred e.value) m head =
      popUpToWalkFuel (fun e => pred e.value) k m head ∧
    ∃ target, head.toChain[k]? = some target ∧
    if inclusive then
      match target.previous with
      | none => popUpToValueModel m curId pred true = .error .popLastEntry
      | some prev =>
        ∃ m',
          popUpToValueModel m curId pred true = .ok m' prev.id ∧
          WellFormedBackstack m' prev.id
    else
      ∃ m',
        popUpToValueModel m curId pred false = .ok m' target.id ∧
        WellFormedBackstack m' target.id := by
  have hmain := popUpTo_terminates_and_slices_Impl m curId (fun e => pred e.value)
    inclusive head k hwf hhead hk
  obtain ⟨hfuel, target, hget, hbody⟩ := hmain
  refine ⟨hfuel, target, hget, ?_⟩
  cases inclusive
  · obtain ⟨m', hok, hwf', _, _⟩ := hbody
    exact ⟨m', hok, hwf'⟩
  · cases hprev : target.previous with
    | none => simpa [popUpToValueModel, hprev] using hbody
    | some prev =>
      simp only [↓reduceIte, hprev] at hbody
      obtain ⟨m', hok, hwf', _, _⟩ := hbody
      exact ⟨m', hok, hwf'⟩

end Navigation.Model
