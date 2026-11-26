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

import Navigation.Backstack
import NavigationDefs

namespace Navigation

/-! ## Section 1: Entry Accessors and Chain Iteration -/

theorem mkEntry_spec_Impl (val : α) (prev : Option (BackstackEntry α)) (id : Uuid) :
    (BackstackEntry.mkEntry val prev id).value = val ∧
    (BackstackEntry.mkEntry val prev id).previous = prev ∧
    (BackstackEntry.mkEntry val prev id).id = id :=
  ⟨rfl, rfl, rfl⟩

theorem iterateBackstackEntryList_mk_none (v : α) (i : Uuid) :
    iterateBackstackEntryList (.mk v none i) = [.mk v none i] := by
  unfold iterateBackstackEntryList
  rfl

theorem iterateBackstackEntryList_mk_some (v : α) (prev : BackstackEntry α) (i : Uuid) :
    iterateBackstackEntryList (.mk v (some prev) i) =
      (.mk v (some prev) i) :: iterateBackstackEntryList prev := by
  conv => lhs; unfold iterateBackstackEntryList
  rfl

theorem iterateBackstackEntryList_eq_entryChain (entry : BackstackEntry α) :
    iterateBackstackEntryList entry = entryChain entry := by
  cases entry with
  | mk v p i =>
    cases p with
    | none =>
      rw [iterateBackstackEntryList_mk_none]
      rfl
    | some prev =>
      rw [iterateBackstackEntryList_mk_some]
      dsimp [entryChain]
      rw [iterateBackstackEntryList_eq_entryChain prev]
termination_by sizeOf entry
decreasing_by decreasing_tactic

theorem iterateBackstackEntry_eq_entryChain_Impl (entry : BackstackEntry α) :
    (iterateBackstackEntry entry).toList = entryChain entry := by
  unfold iterateBackstackEntry
  exact iterateBackstackEntryList_eq_entryChain entry

theorem iterateBackstackEntryList_cons (entry : BackstackEntry α) :
    ∃ tail, iterateBackstackEntryList entry = entry :: tail := by
  cases entry with
  | mk v p i =>
    cases p with
    | none =>
      exact ⟨[], iterateBackstackEntryList_mk_none v i⟩
    | some prev =>
      exact ⟨iterateBackstackEntryList prev, iterateBackstackEntryList_mk_some v prev i⟩

theorem self_mem_iterateBackstackEntryList (entry : BackstackEntry α) :
    entry ∈ iterateBackstackEntryList entry := by
  rcases iterateBackstackEntryList_cons entry with ⟨tail, h⟩
  rw [h]
  exact List.Mem.head tail

theorem iterateBackstackEntry_nonempty_and_head_Impl (entry : BackstackEntry α) :
    (iterateBackstackEntry entry).size > 0 ∧
    (iterateBackstackEntry entry)[0]? = some entry := by
  unfold iterateBackstackEntry
  rcases iterateBackstackEntryList_cons entry with ⟨tail, h⟩
  rw [h]
  simp

theorem iterateBackstackEntry_last_is_root_Impl (entry : BackstackEntry α) :
    ∃ root ∈ (iterateBackstackEntryList entry).getLast?, root.previous = none := by
  cases entry with
  | mk v p i =>
    cases p with
    | none =>
      rw [iterateBackstackEntryList_mk_none]
      exact ⟨.mk v none i, rfl, rfl⟩
    | some prev =>
      rw [iterateBackstackEntryList_mk_some]
      rcases iterateBackstackEntryList_cons prev with ⟨tail, h_prev⟩
      have ih := iterateBackstackEntry_last_is_root_Impl prev
      rw [h_prev] at ih ⊢
      exact ih
termination_by sizeOf entry
decreasing_by decreasing_tactic

theorem previousEntryId_spec_Impl (entry : BackstackEntry α) :
    previousEntryId entry = entry.previous.map BackstackEntry.id := by
  cases entry with
  | mk v p i =>
    cases p <;> rfl

theorem canNavigateBack_iff_Impl (entry : BackstackEntry α) :
    canNavigateBack entry = (previousEntryId entry).isSome := by
  cases entry with
  | mk v p i =>
    cases p <;> rfl

theorem isExpectedActor_iff_Impl (currentEntryId : Uuid) (actorEntryId : Option Uuid) :
    isExpectedActor currentEntryId actorEntryId = true ↔
      (actorEntryId = none ∨ actorEntryId = some currentEntryId) := by
  cases actorEntryId with
  | none =>
    simp [isExpectedActor]
  | some actorId =>
    simp [isExpectedActor, beq_iff_eq]

/-! ## Section 2: Ancestor Chain Structural Lemmas -/

theorem mem_iterateBackstackEntryList_of_prev {cur prev : BackstackEntry α}
    (hp : cur.previous = some prev) {a : BackstackEntry α}
    (ha : a ∈ iterateBackstackEntryList prev) :
    a ∈ iterateBackstackEntryList cur := by
  cases cur with
  | mk v p i =>
    dsimp [BackstackEntry.previous] at hp
    subst hp
    rw [iterateBackstackEntryList_mk_some]
    exact List.Mem.tail _ ha

theorem sizeOf_le_of_mem_iterateBackstackEntryList (cur : BackstackEntry α) {a : BackstackEntry α}
    (ha : a ∈ iterateBackstackEntryList cur) :
    sizeOf a ≤ sizeOf cur := by
  cases cur with
  | mk v p i =>
    cases p with
    | none =>
      rw [iterateBackstackEntryList_mk_none] at ha
      simp at ha
      subst ha
      omega
    | some prev =>
      rw [iterateBackstackEntryList_mk_some] at ha
      rcases List.mem_cons.mp ha with rfl | ha_prev
      · omega
      · have ih := sizeOf_le_of_mem_iterateBackstackEntryList prev ha_prev
        have h_lt : sizeOf prev < sizeOf (BackstackEntry.mk v (some prev) i) := by
          decreasing_tactic
        omega
termination_by sizeOf cur
decreasing_by decreasing_tactic

theorem ne_of_mem_prev_iterateBackstackEntryList {cur prev a : BackstackEntry α}
    (hp : cur.previous = some prev)
    (ha : a ∈ iterateBackstackEntryList prev) :
    a ≠ cur := by
  cases cur with
  | mk v p i =>
    dsimp [BackstackEntry.previous] at hp
    subst hp
    have h_sz := sizeOf_le_of_mem_iterateBackstackEntryList prev ha
    have h_lt : sizeOf prev < sizeOf (BackstackEntry.mk v (some prev) i) := by
      decreasing_tactic
    intro h_eq
    subst h_eq
    omega

/-! ## Section 3: List Lookup, Filter, and Duplicate IDs -/

theorem findEntryList_eq_some_mem_and_id {entries : List (BackstackEntry α)} {targetId : Uuid}
    {e : BackstackEntry α} (h : findEntryList entries targetId = some e) :
    e ∈ entries ∧ e.id = targetId := by
  unfold findEntryList at h
  have h_mem := List.mem_of_find?_eq_some h
  have h_pred := List.find?_some h
  rw [beq_iff_eq] at h_pred
  exact ⟨h_mem, h_pred⟩

theorem findEntryList_eq_none_iff {entries : List (BackstackEntry α)} {targetId : Uuid} :
    findEntryList entries targetId = none ↔ ∀ e ∈ entries, e.id ≠ targetId := by
  unfold findEntryList
  rw [List.find?_eq_none]
  simp [beq_iff_eq]

theorem findEntryList_append {xs ys : List (BackstackEntry α)} {targetId : Uuid} :
    findEntryList (xs ++ ys) targetId = (findEntryList xs targetId).or (findEntryList ys targetId) := by
  unfold findEntryList
  exact List.find?_append

theorem findEntryList_append_of_some {xs ys : List (BackstackEntry α)} {targetId : Uuid}
    {e : BackstackEntry α} (h : findEntryList xs targetId = some e) :
    findEntryList (xs ++ ys) targetId = some e := by
  rw [findEntryList_append, h]
  rfl

theorem findEntryList_append_of_none {xs ys : List (BackstackEntry α)} {targetId : Uuid}
    (h : findEntryList xs targetId = none) :
    findEntryList (xs ++ ys) targetId = findEntryList ys targetId := by
  rw [findEntryList_append, h]
  rfl

theorem findEntryList_singleton_self (e : BackstackEntry α) :
    findEntryList [e] e.id = some e := by
  unfold findEntryList
  simp

theorem findEntryList_removeEntryList_self (entries : List (BackstackEntry α)) (targetId : Uuid) :
    findEntryList (removeEntryList entries targetId) targetId = none := by
  rw [findEntryList_eq_none_iff]
  intro e he
  unfold removeEntryList at he
  rw [List.mem_filter] at he
  exact bne_iff_ne.mp he.2

theorem findEntryList_removeEntryList_of_ne (entries : List (BackstackEntry α))
    {id targetId : Uuid} (hne : id ≠ targetId) :
    findEntryList (removeEntryList entries targetId) id = findEntryList entries id := by
  induction entries with
  | nil => rfl
  | cons x xs ih =>
    unfold removeEntryList findEntryList
    dsimp [List.filter]
    cases h_xt : x.id != targetId with
    | false =>
      have h_eq : x.id = targetId := by
        rw [bne_eq_false_iff_eq] at h_xt
        exact h_xt
      have h_xi : (x.id == id) = false := by
        rw [h_eq]
        exact beq_false_of_ne (Ne.symm hne)
      dsimp [List.find?]
      rw [h_xi]
      exact ih
    | true =>
      dsimp [List.find?]
      cases x.id == id with
      | true => rfl
      | false => exact ih

theorem removeEntryList_eq_self_of_findEntryList_none {entries : List (BackstackEntry α)} {targetId : Uuid}
    (h_none : findEntryList entries targetId = none) :
    removeEntryList entries targetId = entries := by
  unfold removeEntryList
  rw [List.filter_eq_self]
  intro e he
  have hne := (findEntryList_eq_none_iff.mp h_none) e he
  exact bne_iff_ne.mpr hne

theorem removeEntry_eq_self_of_findEntry_none {entries : Array (BackstackEntry α)} {targetId : Uuid}
    (h_none : findEntry entries targetId = none) :
    removeEntry entries targetId = entries := by
  unfold removeEntry findEntry at *
  rw [removeEntryList_eq_self_of_findEntryList_none h_none]

theorem removeEntryList_append (xs ys : List (BackstackEntry α)) (targetId : Uuid) :
    removeEntryList (xs ++ ys) targetId = removeEntryList xs targetId ++ removeEntryList ys targetId := by
  unfold removeEntryList
  exact List.filter_append xs ys

theorem hasDuplicateId_cons_false_iff {x : Uuid} {xs : List Uuid} :
    hasDuplicateId (x :: xs) = false ↔ (xs.contains x = false ∧ hasDuplicateId xs = false) := by
  conv => lhs; unfold hasDuplicateId
  exact Bool.or_eq_false_iff

theorem contains_map_id_eq_false_of_findEntryList_none {entries : List (BackstackEntry α)} {targetId : Uuid}
    (h_none : findEntryList entries targetId = none) :
    (entries.map BackstackEntry.id).contains targetId = false := by
  rw [Bool.eq_false_iff]
  intro h_cont
  rw [List.contains_iff_mem, List.mem_map] at h_cont
  rcases h_cont with ⟨e, he, hid⟩
  exact (findEntryList_eq_none_iff.mp h_none) e he hid

theorem contains_sublist_false {xs ys : List Uuid} {x : Uuid}
    (h_sub : ∀ y ∈ xs, y ∈ ys) (h_cont : ys.contains x = false) :
    xs.contains x = false := by
  rw [Bool.eq_false_iff]
  intro h_in
  rw [List.contains_iff_mem] at h_in
  have h_in_ys : ys.contains x = true := List.contains_iff_mem.mpr (h_sub x h_in)
  rw [h_cont] at h_in_ys
  contradiction

theorem hasDuplicateId_filter_map {entries : List (BackstackEntry α)} (p : BackstackEntry α → Bool)
    (h_nodup : hasDuplicateId (entries.map BackstackEntry.id) = false) :
    hasDuplicateId ((entries.filter p).map BackstackEntry.id) = false := by
  induction entries with
  | nil => rfl
  | cons x xs ih =>
    dsimp [List.map] at h_nodup
    rcases hasDuplicateId_cons_false_iff.mp h_nodup with ⟨h_not_in, h_xs⟩
    dsimp [List.filter]
    cases p x with
    | false => exact ih h_xs
    | true =>
      dsimp [List.map]
      rw [hasDuplicateId_cons_false_iff]
      refine ⟨?_, ih h_xs⟩
      apply contains_sublist_false _ h_not_in
      intro y hy
      rw [List.mem_map] at hy ⊢
      rcases hy with ⟨a, ha, rfl⟩
      rw [List.mem_filter] at ha
      exact ⟨a, ha.1, rfl⟩

theorem allDistinctEntryIds_removeEntry {entries : Array (BackstackEntry α)} (targetId : Uuid)
    (h_dist : allDistinctEntryIds entries = true) :
    allDistinctEntryIds (removeEntry entries targetId) = true := by
  unfold allDistinctEntryIds removeEntry removeEntryList at *
  rw [Bool.not_eq_true'] at h_dist ⊢
  exact hasDuplicateId_filter_map (fun e => e.id != targetId) h_dist

theorem hasDuplicateId_snoc {ids : List Uuid} {newId : Uuid}
    (h_nodup : hasDuplicateId ids = false)
    (h_fresh : ids.contains newId = false) :
    hasDuplicateId (ids ++ [newId]) = false := by
  induction ids with
  | nil => rfl
  | cons x xs ih =>
    rcases hasDuplicateId_cons_false_iff.mp h_nodup with ⟨h_x_not_in, h_xs⟩
    have h_x_ne : x ≠ newId := by
      intro h_eq
      subst h_eq
      have h_in : (x :: xs).contains x = true := List.contains_iff_mem.mpr (List.Mem.head xs)
      rw [h_fresh] at h_in
      contradiction
    have h_fresh_xs : xs.contains newId = false := by
      apply contains_sublist_false _ h_fresh
      intro y hy
      exact List.Mem.tail x hy
    dsimp
    rw [hasDuplicateId_cons_false_iff]
    refine ⟨?_, ih h_xs h_fresh_xs⟩
    rw [Bool.eq_false_iff]
    intro h_in
    rw [List.contains_iff_mem, List.mem_append] at h_in
    rcases h_in with h_in_xs | h_in_single
    · have h_in_b : xs.contains x = true := List.contains_iff_mem.mpr h_in_xs
      rw [h_x_not_in] at h_in_b
      contradiction
    · simp at h_in_single
      exact h_x_ne h_in_single

theorem removeEntry_preserves_chain {entries : Array (BackstackEntry α)} {cur prev : BackstackEntry α}
    (h_chain : ∀ a ∈ iterateBackstackEntryList cur, findEntry entries a.id = some a)
    (hp : cur.previous = some prev) :
    ∀ a ∈ iterateBackstackEntryList prev, findEntry (removeEntry entries cur.id) a.id = some a := by
  intro a ha
  have ha_cur : a ∈ iterateBackstackEntryList cur := mem_iterateBackstackEntryList_of_prev hp ha
  have h_find_a : findEntry entries a.id = some a := h_chain a ha_cur
  have h_find_cur : findEntry entries cur.id = some cur :=
    h_chain cur (self_mem_iterateBackstackEntryList cur)
  have h_ne_entry : a ≠ cur := ne_of_mem_prev_iterateBackstackEntryList hp ha
  have h_ne_id : a.id ≠ cur.id := by
    intro h_eq
    rw [h_eq] at h_find_a
    rw [h_find_a] at h_find_cur
    injection h_find_cur with h_eq'
    exact h_ne_entry h_eq'
  unfold findEntry removeEntry at *
  rw [findEntryList_removeEntryList_of_ne entries.toList h_ne_id]
  exact h_find_a

/-! ## Section 4: Initial State, Navigate, and Pop (Theorems 4, 5a-c, 6a-d) -/

theorem initialBackstack_valid_Impl (rootId : Uuid) (val : α) :
    ValidBackstackState (initialBackstack rootId val) ∧
    ValidTopologicalEntries (initialBackstack rootId val).entries.toList := by
  refine ⟨?_, ?_⟩
  · unfold ValidBackstackState initialBackstack allDistinctEntryIds hasDuplicateId findEntry findEntryList
    refine ⟨rfl, BackstackEntry.mkEntry val none rootId, ?_, ?_⟩
    · simp [BackstackEntry.mkEntry, BackstackEntry.id]
    · intro a ha
      dsimp [BackstackEntry.mkEntry] at ha ⊢
      rw [iterateBackstackEntryList_mk_none] at ha
      simp at ha
      subst ha
      simp [BackstackEntry.id]
  · unfold ValidTopologicalEntries ValidTopologicalEntriesAfter initialBackstack
    dsimp [BackstackEntry.mkEntry]
    refine ⟨rfl, ?_, trivial⟩
    intro prev hp
    dsimp [BackstackEntry.previous] at hp
    contradiction

theorem navigateWithFactory_preserves_valid_Impl (state : BackstackState α)
    (valueFactory : BackstackEntry α → α) (newId : Uuid)
    (h_valid : ValidBackstackState state)
    (h_fresh : findEntry state.entries newId = none) :
    ∃ state' cur,
      findEntry state.entries state.currentEntryId = some cur ∧
      navigateWithFactory state valueFactory newId = some state' ∧
      ValidBackstackState state' ∧
      state'.currentEntryId = newId ∧
      findEntry state'.entries newId = some (BackstackEntry.mkEntry (valueFactory cur) (some cur) newId) := by
  rcases h_valid with ⟨h_dist, cur, h_cur, h_chain⟩
  let newEntry := BackstackEntry.mkEntry (valueFactory cur) (some cur) newId
  let state' : BackstackState α := { entries := state.entries.push newEntry, currentEntryId := newId }
  have h_rem : removeEntry state.entries newId = state.entries :=
    removeEntry_eq_self_of_findEntry_none h_fresh
  have h_nav : navigateWithFactory state valueFactory newId = some state' := by
    unfold navigateWithFactory
    rw [h_cur]
    dsimp
    rw [h_rem]
  have h_find_new : findEntry state'.entries newId = some newEntry := by
    unfold findEntry
    dsimp [state']
    rw [Array.toList_push]
    rw [findEntryList_append_of_none h_fresh]
    exact findEntryList_singleton_self newEntry
  refine ⟨state', cur, h_cur, h_nav, ?_, rfl, h_find_new⟩
  refine ⟨?_, newEntry, h_find_new, ?_⟩
  · unfold allDistinctEntryIds at h_dist ⊢
    dsimp [state']
    rw [Array.toList_push, List.map_append, List.map_singleton]
    rw [Bool.not_eq_true'] at h_dist ⊢
    exact hasDuplicateId_snoc h_dist (contains_map_id_eq_false_of_findEntryList_none h_fresh)
  · intro a ha
    dsimp [newEntry, BackstackEntry.mkEntry] at ha
    rw [iterateBackstackEntryList_mk_some] at ha
    rcases List.mem_cons.mp ha with rfl | ha_prev
    · exact h_find_new
    · have h_find_a := h_chain a ha_prev
      unfold findEntry at h_find_a ⊢
      dsimp [state']
      rw [Array.toList_push]
      exact findEntryList_append_of_some h_find_a

theorem ValidTopologicalEntriesAfter_snoc {seen entries : List (BackstackEntry α)} {newEntry : BackstackEntry α}
    (h_top : ValidTopologicalEntriesAfter seen entries)
    (h_fresh : findEntryList (seen ++ entries) newEntry.id = none)
    (h_prev : ∀ prev, newEntry.previous = some prev → findEntryList (seen ++ entries) prev.id = some prev) :
    ValidTopologicalEntriesAfter seen (entries ++ [newEntry]) := by
  induction entries generalizing seen with
  | nil =>
    rw [List.append_nil] at h_fresh h_prev
    exact ⟨h_fresh, h_prev, trivial⟩
  | cons e rest ih =>
    rcases h_top with ⟨h_e_fresh, h_e_prev, h_rest⟩
    refine ⟨h_e_fresh, h_e_prev, ?_⟩
    apply ih h_rest
    · rw [List.append_assoc, List.singleton_append]
      exact h_fresh
    · intro prev hp
      rw [List.append_assoc, List.singleton_append]
      exact h_prev prev hp

theorem navigateWithFactory_preserves_topological_Impl (state : BackstackState α)
    (valueFactory : BackstackEntry α → α) (newId : Uuid)
    (_h_valid : ValidBackstackState state)
    (h_top : ValidTopologicalEntries state.entries.toList)
    (h_fresh : findEntry state.entries newId = none)
    (h_nav : navigateWithFactory state valueFactory newId = some state') :
    ValidTopologicalEntries state'.entries.toList := by
  unfold navigateWithFactory at h_nav
  cases h_cur : findEntry state.entries state.currentEntryId with
  | none =>
    rw [h_cur] at h_nav
    contradiction
  | some cur =>
    rw [h_cur] at h_nav
    dsimp at h_nav
    have h_rem : removeEntry state.entries newId = state.entries :=
      removeEntry_eq_self_of_findEntry_none h_fresh
    rw [h_rem] at h_nav
    injection h_nav with h_eq
    subst h_eq
    dsimp
    rw [Array.toList_push]
    unfold ValidTopologicalEntries at h_top ⊢
    apply ValidTopologicalEntriesAfter_snoc h_top
    · dsimp [BackstackEntry.mkEntry, BackstackEntry.id]
      exact h_fresh
    · intro prev hp
      dsimp [BackstackEntry.mkEntry, BackstackEntry.previous] at hp
      injection hp with h_prev_eq
      subst h_prev_eq
      have h_id := (findEntryList_eq_some_mem_and_id h_cur).2
      dsimp
      rw [h_id]
      exact h_cur

theorem navigate_preserves_valid_Impl (state : BackstackState α) (val : α) (newId : Uuid)
    (h_valid : ValidBackstackState state)
    (h_top : ValidTopologicalEntries state.entries.toList)
    (h_fresh : findEntry state.entries newId = none) :
    ∃ state',
      navigate state val newId = some state' ∧
      ValidBackstackState state' ∧
      ValidTopologicalEntries state'.entries.toList ∧
      state'.currentEntryId = newId := by
  unfold navigate
  rcases navigateWithFactory_preserves_valid_Impl state (fun _ => val) newId h_valid h_fresh with
    ⟨state', cur, _, h_nav, h_valid', h_cur_id, _⟩
  have h_top' := navigateWithFactory_preserves_topological_Impl state (fun _ => val) newId h_valid h_top h_fresh h_nav
  exact ⟨state', h_nav, h_valid', h_top', h_cur_id⟩

theorem popBackstack_root_fails_Impl (state : BackstackState α)
    (h_cur : findEntry state.entries state.currentEntryId = some cur)
    (h_root : cur.previous = none) :
    popBackstack state = none := by
  unfold popBackstack
  rw [h_cur]
  dsimp
  rw [h_root]

theorem popBackstack_preserves_valid_Impl (state : BackstackState α)
    (h_valid : ValidBackstackState state)
    (h_pop : popBackstack state = some state') :
    ValidBackstackState state' ∧
    findEntry state'.entries state.currentEntryId = none := by
  rcases h_valid with ⟨h_dist, cur, h_cur, h_chain⟩
  unfold popBackstack at h_pop
  rw [h_cur] at h_pop
  dsimp at h_pop
  cases hp : cur.previous with
  | none =>
    rw [hp] at h_pop
    contradiction
  | some prev =>
    rw [hp] at h_pop
    injection h_pop with h_eq
    subst h_eq
    have h_cur_id : cur.id = state.currentEntryId := (findEntryList_eq_some_mem_and_id h_cur).2
    have h_chain' := removeEntry_preserves_chain h_chain hp
    have h_find_prev : findEntry (removeEntry state.entries cur.id) prev.id = some prev :=
      h_chain' prev (self_mem_iterateBackstackEntryList prev)
    refine ⟨⟨allDistinctEntryIds_removeEntry cur.id h_dist, prev, h_find_prev, h_chain'⟩, ?_⟩
    dsimp
    rw [← h_cur_id]
    unfold findEntry removeEntry
    exact findEntryList_removeEntryList_self state.entries.toList cur.id

theorem pop_after_navigateWithFactory_eq_original_Impl (state : BackstackState α)
    (valueFactory : BackstackEntry α → α) (newId : Uuid)
    (h_valid : ValidBackstackState state)
    (h_fresh : findEntry state.entries newId = none)
    (h_nav : navigateWithFactory state valueFactory newId = some state') :
    popBackstack state' = some state := by
  rcases navigateWithFactory_preserves_valid_Impl state valueFactory newId h_valid h_fresh with
    ⟨state1, cur, h_cur, h_nav1, _, h_cur_id1, h_find_new⟩
  rw [h_nav] at h_nav1
  injection h_nav1 with h_eq
  subst h_eq
  unfold navigateWithFactory at h_nav
  rw [h_cur] at h_nav
  dsimp at h_nav
  have h_rem : removeEntry state.entries newId = state.entries :=
    removeEntry_eq_self_of_findEntry_none h_fresh
  rw [h_rem] at h_nav
  injection h_nav with h_state'
  unfold popBackstack
  rw [h_cur_id1, h_find_new]
  dsimp [BackstackEntry.mkEntry, BackstackEntry.previous]
  have h_cur_id : cur.id = state.currentEntryId := (findEntryList_eq_some_mem_and_id h_cur).2
  have h_new_id : (BackstackEntry.mk (valueFactory cur) (some cur) newId).id = newId := rfl
  have h_rem_push : removeEntry state'.entries newId = state.entries := by
    rw [← h_state']
    unfold removeEntry
    dsimp
    rw [Array.toList_push, removeEntryList_append]
    rw [removeEntryList_eq_self_of_findEntryList_none h_fresh]
    have h_single : removeEntryList [BackstackEntry.mkEntry (valueFactory cur) (some cur) newId] newId = [] := by
      unfold removeEntryList
      simp [BackstackEntry.mkEntry, BackstackEntry.id]
    rw [h_single, List.append_nil]
  rw [h_new_id, h_rem_push, h_cur_id]

theorem pop_after_navigate_eq_original_Impl (state : BackstackState α) (val : α) (newId : Uuid)
    (h_valid : ValidBackstackState state)
    (h_fresh : findEntry state.entries newId = none)
    (h_nav : navigate state val newId = some state') :
    popBackstack state' = some state :=
  pop_after_navigateWithFactory_eq_original_Impl state (fun _ => val) newId h_valid h_fresh h_nav

/-! ## Section 5: Multi-Step `popUpTo` Theorems (Theorems 7a-j) -/

theorem popUpToWalk_eq (entries : Array (BackstackEntry α)) (current : BackstackEntry α)
    (p : BackstackEntry α → Bool) (inclusive : Bool) :
    popUpToWalk entries current p inclusive =
      if p current then
        if inclusive then
          match current.previous with
          | none => none
          | some prev => some { entries := removeEntry entries current.id, currentEntryId := prev.id }
        else
          some { entries := entries, currentEntryId := current.id }
      else
        match current.previous with
        | none => none
        | some prev => popUpToWalk (removeEntry entries current.id) prev p inclusive := by
  conv => lhs; unfold popUpToWalk
  cases p current <;> cases current.previous <;> rfl

theorem popUpToWalk_preserves_valid (entries : Array (BackstackEntry α)) (cur : BackstackEntry α)
    (p : BackstackEntry α → Bool) (inclusive : Bool) {state' : BackstackState α}
    (h_dist : allDistinctEntryIds entries = true)
    (h_chain : ∀ a ∈ iterateBackstackEntryList cur, findEntry entries a.id = some a)
    (h_walk : popUpToWalk entries cur p inclusive = some state') :
    ValidBackstackState state' := by
  rw [popUpToWalk_eq] at h_walk
  cases hp_cur : p cur with
  | true =>
    rw [hp_cur] at h_walk
    dsimp at h_walk
    cases inclusive with
    | false =>
      dsimp at h_walk
      injection h_walk with h_eq
      subst h_eq
      exact ⟨h_dist, cur, h_chain cur (self_mem_iterateBackstackEntryList cur), h_chain⟩
    | true =>
      dsimp at h_walk
      cases h_prev : cur.previous with
      | none =>
        rw [h_prev] at h_walk
        contradiction
      | some prev =>
        rw [h_prev] at h_walk
        injection h_walk with h_eq
        subst h_eq
        have h_chain' := removeEntry_preserves_chain h_chain h_prev
        exact ⟨allDistinctEntryIds_removeEntry cur.id h_dist, prev,
          h_chain' prev (self_mem_iterateBackstackEntryList prev), h_chain'⟩
  | false =>
    rw [hp_cur] at h_walk
    dsimp at h_walk
    cases h_prev : cur.previous with
    | none =>
      rw [h_prev] at h_walk
      contradiction
    | some prev =>
      rw [h_prev] at h_walk
      have h_chain' := removeEntry_preserves_chain h_chain h_prev
      have h_dist' := allDistinctEntryIds_removeEntry cur.id h_dist
      exact popUpToWalk_preserves_valid (removeEntry entries cur.id) prev p inclusive h_dist' h_chain' h_walk
termination_by sizeOf cur
decreasing_by
  cases cur with
  | mk v prevOpt i =>
    dsimp [BackstackEntry.previous] at h_prev
    subst h_prev
    decreasing_tactic

theorem popUpTo_preserves_valid_Impl (state : BackstackState α) (p : BackstackEntry α → Bool) (inclusive : Bool)
    (h_valid : ValidBackstackState state)
    (h_pop : popUpTo state p inclusive = some state') :
    ValidBackstackState state' := by
  rcases h_valid with ⟨h_dist, cur, h_cur, h_chain⟩
  unfold popUpTo at h_pop
  rw [h_cur] at h_pop
  exact popUpToWalk_preserves_valid state.entries cur p inclusive h_dist h_chain h_pop

theorem popUpToWalk_non_inclusive_sound (entries : Array (BackstackEntry α)) (cur : BackstackEntry α)
    (p : BackstackEntry α → Bool) {state' : BackstackState α}
    (h_chain : ∀ a ∈ iterateBackstackEntryList cur, findEntry entries a.id = some a)
    (h_walk : popUpToWalk entries cur p false = some state') :
    ∃ target ∈ iterateBackstackEntryList cur,
      state'.currentEntryId = target.id ∧
      findEntry state'.entries target.id = some target ∧
      p target = true := by
  rw [popUpToWalk_eq] at h_walk
  cases hp_cur : p cur with
  | true =>
    rw [hp_cur] at h_walk
    dsimp at h_walk
    injection h_walk with h_eq
    subst h_eq
    exact ⟨cur, self_mem_iterateBackstackEntryList cur, rfl,
      h_chain cur (self_mem_iterateBackstackEntryList cur), hp_cur⟩
  | false =>
    rw [hp_cur] at h_walk
    dsimp at h_walk
    cases h_prev : cur.previous with
    | none =>
      rw [h_prev] at h_walk
      contradiction
    | some prev =>
      rw [h_prev] at h_walk
      have h_chain' := removeEntry_preserves_chain h_chain h_prev
      rcases popUpToWalk_non_inclusive_sound (removeEntry entries cur.id) prev p h_chain' h_walk with
        ⟨target, h_mem_prev, h_id, h_find, h_p⟩
      exact ⟨target, mem_iterateBackstackEntryList_of_prev h_prev h_mem_prev, h_id, h_find, h_p⟩
termination_by sizeOf cur
decreasing_by
  cases cur with
  | mk v prevOpt i =>
    dsimp [BackstackEntry.previous] at h_prev
    subst h_prev
    decreasing_tactic

theorem popUpTo_non_inclusive_sound_Impl (state : BackstackState α) (p : BackstackEntry α → Bool)
    (h_valid : ValidBackstackState state)
    (h_cur : findEntry state.entries state.currentEntryId = some cur)
    (h_pop : popUpTo state p false = some state') :
    ∃ target ∈ iterateBackstackEntryList cur,
      state'.currentEntryId = target.id ∧
      findEntry state'.entries target.id = some target ∧
      p target = true := by
  rcases h_valid with ⟨_, cur', h_cur', h_chain⟩
  rw [h_cur] at h_cur'
  injection h_cur' with h_eq
  subst h_eq
  unfold popUpTo at h_pop
  rw [h_cur] at h_pop
  exact popUpToWalk_non_inclusive_sound state.entries cur p h_chain h_pop

theorem popUpToWalk_inclusive_sound (entries : Array (BackstackEntry α)) (cur : BackstackEntry α)
    (p : BackstackEntry α → Bool) {state' : BackstackState α}
    (h_chain : ∀ a ∈ iterateBackstackEntryList cur, findEntry entries a.id = some a)
    (h_walk : popUpToWalk entries cur p true = some state') :
    ∃ matched ∈ iterateBackstackEntryList cur, ∃ prev,
      matched.previous = some prev ∧
      p matched = true ∧
      state'.currentEntryId = prev.id ∧
      findEntry state'.entries prev.id = some prev ∧
      findEntry state'.entries matched.id = none := by
  rw [popUpToWalk_eq] at h_walk
  cases hp_cur : p cur with
  | true =>
    rw [hp_cur] at h_walk
    dsimp at h_walk
    cases h_prev : cur.previous with
    | none =>
      rw [h_prev] at h_walk
      contradiction
    | some prev =>
      rw [h_prev] at h_walk
      injection h_walk with h_eq
      subst h_eq
      have h_chain' := removeEntry_preserves_chain h_chain h_prev
      have h_find_prev := h_chain' prev (self_mem_iterateBackstackEntryList prev)
      have h_find_cur : findEntry (removeEntry entries cur.id) cur.id = none :=
        findEntryList_removeEntryList_self entries.toList cur.id
      exact ⟨cur, self_mem_iterateBackstackEntryList cur, prev, h_prev, hp_cur, rfl, h_find_prev, h_find_cur⟩
  | false =>
    rw [hp_cur] at h_walk
    dsimp at h_walk
    cases h_prev : cur.previous with
    | none =>
      rw [h_prev] at h_walk
      contradiction
    | some prev =>
      rw [h_prev] at h_walk
      have h_chain' := removeEntry_preserves_chain h_chain h_prev
      rcases popUpToWalk_inclusive_sound (removeEntry entries cur.id) prev p h_chain' h_walk with
        ⟨matched, h_mem_prev, prev', h_m_prev, h_p, h_id, h_find_prev', h_find_matched⟩
      exact ⟨matched, mem_iterateBackstackEntryList_of_prev h_prev h_mem_prev, prev',
        h_m_prev, h_p, h_id, h_find_prev', h_find_matched⟩
termination_by sizeOf cur
decreasing_by
  cases cur with
  | mk v prevOpt i =>
    dsimp [BackstackEntry.previous] at h_prev
    subst h_prev
    decreasing_tactic

theorem popUpTo_inclusive_sound_Impl (state : BackstackState α) (p : BackstackEntry α → Bool)
    (h_valid : ValidBackstackState state)
    (h_cur : findEntry state.entries state.currentEntryId = some cur)
    (h_pop : popUpTo state p true = some state') :
    ∃ matched ∈ iterateBackstackEntryList cur, ∃ prev,
      matched.previous = some prev ∧
      p matched = true ∧
      state'.currentEntryId = prev.id ∧
      findEntry state'.entries prev.id = some prev ∧
      findEntry state'.entries matched.id = none := by
  rcases h_valid with ⟨_, cur', h_cur', h_chain⟩
  rw [h_cur] at h_cur'
  injection h_cur' with h_eq
  subst h_eq
  unfold popUpTo at h_pop
  rw [h_cur] at h_pop
  exact popUpToWalk_inclusive_sound state.entries cur p h_chain h_pop

theorem popUpToWalk_complete_non_inclusive (entries : Array (BackstackEntry α)) (cur : BackstackEntry α)
    (p : BackstackEntry α → Bool)
    (h_exists : ∃ target ∈ iterateBackstackEntryList cur, p target = true) :
    (popUpToWalk entries cur p false).isSome = true := by
  rw [popUpToWalk_eq]
  cases hp_cur : p cur with
  | true =>
    simp
  | false =>
    dsimp
    rcases h_exists with ⟨target, h_mem, hp_target⟩
    cases cur with
    | mk v prevOpt i =>
      cases prevOpt with
      | none =>
        rw [iterateBackstackEntryList_mk_none] at h_mem
        simp at h_mem
        subst h_mem
        rw [hp_cur] at hp_target
        contradiction
      | some prev =>
        dsimp [BackstackEntry.previous]
        rw [iterateBackstackEntryList_mk_some] at h_mem
        rcases List.mem_cons.mp h_mem with h_eq | h_mem_prev
        · subst h_eq
          rw [hp_cur] at hp_target
          contradiction
        · exact popUpToWalk_complete_non_inclusive (removeEntry entries (BackstackEntry.mk v (some prev) i).id) prev p
            ⟨target, h_mem_prev, hp_target⟩
termination_by sizeOf cur
decreasing_by decreasing_tactic

theorem popUpTo_complete_non_inclusive_Impl (state : BackstackState α) (p : BackstackEntry α → Bool)
    (h_cur : findEntry state.entries state.currentEntryId = some cur)
    (h_exists : ∃ target ∈ iterateBackstackEntryList cur, p target = true) :
    (popUpTo state p false).isSome = true := by
  unfold popUpTo
  rw [h_cur]
  exact popUpToWalk_complete_non_inclusive state.entries cur p h_exists

theorem popUpToWalk_none_when_no_match (entries : Array (BackstackEntry α)) (cur : BackstackEntry α)
    (p : BackstackEntry α → Bool) (inclusive : Bool)
    (h_none : ∀ a ∈ iterateBackstackEntryList cur, p a = false) :
    popUpToWalk entries cur p inclusive = none := by
  rw [popUpToWalk_eq]
  have hp_cur : p cur = false := h_none cur (self_mem_iterateBackstackEntryList cur)
  rw [hp_cur]
  dsimp
  cases h_prev : cur.previous with
  | none => rfl
  | some prev =>
    apply popUpToWalk_none_when_no_match
    intro a ha
    exact h_none a (mem_iterateBackstackEntryList_of_prev h_prev ha)
termination_by sizeOf cur
decreasing_by
  cases cur with
  | mk v prevOpt i =>
    dsimp [BackstackEntry.previous] at h_prev
    subst h_prev
    decreasing_tactic

theorem popUpTo_none_when_no_match_Impl (state : BackstackState α) (p : BackstackEntry α → Bool) (inclusive : Bool)
    (h_cur : findEntry state.entries state.currentEntryId = some cur)
    (h_none : ∀ a ∈ iterateBackstackEntryList cur, p a = false) :
    popUpTo state p inclusive = none := by
  unfold popUpTo
  rw [h_cur]
  exact popUpToWalk_none_when_no_match state.entries cur p inclusive h_none

theorem popUpTo_current_non_inclusive_Impl (state : BackstackState α) (p : BackstackEntry α → Bool)
    (_h_valid : ValidBackstackState state)
    (h_cur : findEntry state.entries state.currentEntryId = some cur)
    (h_match : p cur = true) :
    popUpTo state p false = some state := by
  unfold popUpTo
  rw [h_cur]
  dsimp
  rw [popUpToWalk_eq, h_match]
  dsimp
  have h_id : cur.id = state.currentEntryId := (findEntryList_eq_some_mem_and_id h_cur).2
  rw [h_id]

theorem popUpTo_current_inclusive_eq_pop_Impl (state : BackstackState α) (p : BackstackEntry α → Bool)
    (h_cur : findEntry state.entries state.currentEntryId = some cur)
    (h_match : p cur = true) :
    popUpTo state p true = popBackstack state := by
  unfold popUpTo popBackstack
  rw [h_cur]
  dsimp
  rw [popUpToWalk_eq, h_match]
  rfl

theorem popUpTo_step_when_not_matching_Impl (state : BackstackState α) (p : BackstackEntry α → Bool) (inclusive : Bool)
    (h_valid : ValidBackstackState state)
    (h_cur : findEntry state.entries state.currentEntryId = some cur)
    (h_no_match : p cur = false) :
    popUpTo state p inclusive = (popBackstack state).bind (fun prevState => popUpTo prevState p inclusive) := by
  rcases h_valid with ⟨_, cur', h_cur', h_chain⟩
  rw [h_cur] at h_cur'
  injection h_cur' with h_eq
  subst h_eq
  unfold popUpTo popBackstack
  rw [h_cur]
  dsimp
  rw [popUpToWalk_eq, h_no_match]
  dsimp
  cases h_prev : cur.previous with
  | none => rfl
  | some prev =>
    dsimp [Option.bind]
    have h_chain' := removeEntry_preserves_chain h_chain h_prev
    have h_find_prev := h_chain' prev (self_mem_iterateBackstackEntryList prev)
    rw [h_find_prev]

theorem popUpToId_spec_Impl (state : BackstackState α) (targetId : Uuid)
    (h_valid : ValidBackstackState state)
    (h_pop : popUpToId state targetId false = some state') :
    ValidBackstackState state' ∧
    state'.currentEntryId = targetId ∧
    hasEntry state'.entries targetId = true := by
  unfold popUpToId at h_pop
  have h_valid' := popUpTo_preserves_valid_Impl state (fun e => e.id == targetId) false h_valid h_pop
  rcases h_valid with ⟨h_dist, cur, h_cur, h_chain⟩
  rcases popUpTo_non_inclusive_sound_Impl state (fun e => e.id == targetId)
    ⟨h_dist, cur, h_cur, h_chain⟩ h_cur h_pop with
    ⟨target, _, h_cur_id, h_find, h_match⟩
  rw [beq_iff_eq] at h_match
  subst h_match
  refine ⟨h_valid', h_cur_id, ?_⟩
  unfold hasEntry
  rw [h_find]
  rfl

theorem popUpToValue_spec_Impl (state : BackstackState α) (p : α → Bool)
    (h_valid : ValidBackstackState state)
    (h_pop : popUpToValue state p false = some state') :
    ValidBackstackState state' ∧
    ∃ target, findEntry state'.entries state'.currentEntryId = some target ∧ p target.value = true := by
  unfold popUpToValue at h_pop
  have h_valid' := popUpTo_preserves_valid_Impl state (fun e => p e.value) false h_valid h_pop
  rcases h_valid with ⟨h_dist, cur, h_cur, h_chain⟩
  rcases popUpTo_non_inclusive_sound_Impl state (fun e => p e.value)
    ⟨h_dist, cur, h_cur, h_chain⟩ h_cur h_pop with
    ⟨target, _, h_cur_id, h_find, h_match⟩
  rw [← h_cur_id] at h_find
  exact ⟨h_valid', target, h_find, h_match⟩

/-! ## Section 6: Topological Serialization and Deserialization (Theorems 8a-f) -/

theorem serializeEntryChainList_eq (toSurrogate : α → σ) (entry : BackstackEntry α)
    (acc : List (BackstackEntrySurrogate σ)) :
    serializeEntryChainList toSurrogate entry acc =
      let accAfterPrev :=
        match entry.previous with
        | none => acc
        | some prev => serializeEntryChainList toSurrogate prev acc
      if hasSurrogateIdList accAfterPrev entry.id then
        accAfterPrev
      else
        accAfterPrev ++ [entryToSurrogate toSurrogate entry] := by
  conv => lhs; unfold serializeEntryChainList
  cases entry.previous <;> rfl

theorem hasSurrogateIdList_eq_contains_map_id (surrogates : List (BackstackEntrySurrogate σ)) (targetId : Uuid) :
    hasSurrogateIdList surrogates targetId = (surrogates.map (·.id)).contains targetId := by
  induction surrogates with
  | nil => rfl
  | cons s rest ih =>
    unfold hasSurrogateIdList at ih ⊢
    dsimp [List.find?, List.map]
    rw [List.contains_cons]
    cases h_eq : s.id == targetId with
    | true =>
      rw [beq_iff_eq] at h_eq
      subst h_eq
      simp
    | false =>
      have h_symm : (targetId == s.id) = false := by
        cases h2 : targetId == s.id with
        | false => rfl
        | true =>
          rw [beq_iff_eq] at h2
          subst h2
          simp at h_eq
      rw [h_symm]
      dsimp
      exact ih

theorem hasSurrogateIdList_append (xs ys : List (BackstackEntrySurrogate σ)) (targetId : Uuid) :
    hasSurrogateIdList (xs ++ ys) targetId = (hasSurrogateIdList xs targetId || hasSurrogateIdList ys targetId) := by
  unfold hasSurrogateIdList
  rw [List.find?_append, Option.isSome_or]

theorem hasSurrogateIdList_singleton_self (s : BackstackEntrySurrogate σ) :
    hasSurrogateIdList [s] s.id = true := by
  unfold hasSurrogateIdList
  simp

theorem hasSurrogateIdList_serializeEntryChainList_self (toSurrogate : α → σ) (entry : BackstackEntry α)
    (acc : List (BackstackEntrySurrogate σ)) :
    hasSurrogateIdList (serializeEntryChainList toSurrogate entry acc) entry.id = true := by
  rw [serializeEntryChainList_eq]
  dsimp
  let accAfterPrev :=
    match entry.previous with
    | none => acc
    | some prev => serializeEntryChainList toSurrogate prev acc
  cases h2 : hasSurrogateIdList accAfterPrev entry.id with
  | true => exact h2
  | false =>
    dsimp
    rw [hasSurrogateIdList_append]
    have h_self : hasSurrogateIdList [entryToSurrogate toSurrogate entry] entry.id = true :=
      hasSurrogateIdList_singleton_self (entryToSurrogate toSurrogate entry)
    rw [h_self, Bool.or_true]

theorem hasSurrogateIdList_serializeEntryChainList_mono (toSurrogate : α → σ) (entry : BackstackEntry α)
    (acc : List (BackstackEntrySurrogate σ)) {id : Uuid}
    (h_in : hasSurrogateIdList acc id = true) :
    hasSurrogateIdList (serializeEntryChainList toSurrogate entry acc) id = true := by
  rw [serializeEntryChainList_eq]
  dsimp
  have h_prev_mono :
      hasSurrogateIdList
        (match entry.previous with
        | none => acc
        | some prev => serializeEntryChainList toSurrogate prev acc) id = true := by
    cases h_prev : entry.previous with
    | none => exact h_in
    | some prev =>
      exact hasSurrogateIdList_serializeEntryChainList_mono toSurrogate prev acc h_in
  cases h2 : hasSurrogateIdList
      (match entry.previous with
      | none => acc
      | some prev => serializeEntryChainList toSurrogate prev acc) entry.id with
  | true => exact h_prev_mono
  | false =>
    dsimp
    rw [hasSurrogateIdList_append, h_prev_mono, Bool.true_or]
termination_by sizeOf entry
decreasing_by
  cases entry with
  | mk v prevOpt i =>
    dsimp [BackstackEntry.previous] at h_prev
    subst h_prev
    decreasing_tactic

theorem hasSurrogateIdList_serializeEntriesList_mono (toSurrogate : α → σ)
    (entries : List (BackstackEntry α)) (acc : List (BackstackEntrySurrogate σ)) {id : Uuid}
    (h_in : hasSurrogateIdList acc id = true) :
    hasSurrogateIdList (serializeEntriesList toSurrogate entries acc) id = true := by
  induction entries generalizing acc with
  | nil => exact h_in
  | cons e rest ih =>
    unfold serializeEntriesList
    exact ih (serializeEntryChainList toSurrogate e acc)
      (hasSurrogateIdList_serializeEntryChainList_mono toSurrogate e acc h_in)

theorem hasSurrogateIdList_serializeEntryChainList_chain (toSurrogate : α → σ)
    (entry : BackstackEntry α) (acc : List (BackstackEntrySurrogate σ)) :
    ∀ a ∈ iterateBackstackEntryList entry,
      hasSurrogateIdList (serializeEntryChainList toSurrogate entry acc) a.id = true := by
  cases entry with
  | mk v prevOpt i =>
    intro a ha
    cases prevOpt with
    | none =>
      rw [iterateBackstackEntryList_mk_none] at ha
      simp at ha
      subst ha
      exact hasSurrogateIdList_serializeEntryChainList_self toSurrogate (.mk v none i) acc
    | some prev =>
      rw [iterateBackstackEntryList_mk_some] at ha
      rcases List.mem_cons.mp ha with rfl | ha_prev
      · exact hasSurrogateIdList_serializeEntryChainList_self toSurrogate (.mk v (some prev) i) acc
      · have h_prev_chain := hasSurrogateIdList_serializeEntryChainList_chain toSurrogate prev acc a ha_prev
        rw [serializeEntryChainList_eq]
        dsimp [BackstackEntry.previous]
        cases hasSurrogateIdList (serializeEntryChainList toSurrogate prev acc)
            (BackstackEntry.mk v (some prev) i).id with
        | true =>
          dsimp
          exact h_prev_chain
        | false =>
          dsimp
          rw [hasSurrogateIdList_append, h_prev_chain, Bool.true_or]
termination_by sizeOf entry
decreasing_by decreasing_tactic

theorem hasSurrogateIdList_serializeEntriesList_contains_all (toSurrogate : α → σ)
    (entries : List (BackstackEntry α)) (acc : List (BackstackEntrySurrogate σ))
    {e : BackstackEntry α} (he : e ∈ entries) :
    ∀ a ∈ iterateBackstackEntryList e,
      hasSurrogateIdList (serializeEntriesList toSurrogate entries acc) a.id = true := by
  induction entries generalizing acc with
  | nil => contradiction
  | cons x rest ih =>
    unfold serializeEntriesList
    rcases List.mem_cons.mp he with rfl | he_rest
    · intro a ha
      have h_in := hasSurrogateIdList_serializeEntryChainList_chain toSurrogate e acc a ha
      exact hasSurrogateIdList_serializeEntriesList_mono toSurrogate rest
        (serializeEntryChainList toSurrogate e acc) h_in
    · exact ih (serializeEntryChainList toSurrogate x acc) he_rest

theorem serializeBackstackEntries_contains_all_Impl (entries : Array (BackstackEntry α))
    (toSurrogate : α → σ) (e : BackstackEntry α) (he : e ∈ entries.toList) :
    ∀ a ∈ iterateBackstackEntryList e,
      hasSurrogateId (serializeBackstackEntries entries toSurrogate) a.id = true := by
  unfold hasSurrogateId serializeBackstackEntries
  exact hasSurrogateIdList_serializeEntriesList_contains_all toSurrogate entries.toList [] he

theorem isTopologicalOrderList_snoc (seen : List Uuid) (xs : List (BackstackEntrySurrogate σ))
    (s : BackstackEntrySurrogate σ)
    (h_top : isTopologicalOrderList seen xs = true)
    (h_prev : ∀ pid, s.previousId = some pid →
      (seen.contains pid = true ∨ (xs.map BackstackEntrySurrogate.id).contains pid = true)) :
    isTopologicalOrderList seen (xs ++ [s]) = true := by
  induction xs generalizing seen with
  | nil =>
    dsimp [List.nil_append]
    unfold isTopologicalOrderList
    cases hp : s.previousId with
    | none => rfl
    | some pid =>
      dsimp
      rcases h_prev pid hp with h_seen | h_nil
      · rw [h_seen]
        rfl
      · contradiction
  | cons x rest ih =>
    dsimp [List.cons_append]
    unfold isTopologicalOrderList at h_top ⊢
    have h_prev' : ∀ pid, s.previousId = some pid →
        ((x.id :: seen).contains pid = true ∨ (rest.map BackstackEntrySurrogate.id).contains pid = true) := by
      intro pid hp
      rcases h_prev pid hp with h_seen | h_map
      · left
        rw [List.contains_cons, h_seen, Bool.or_true]
      · dsimp [List.map] at h_map
        rw [List.contains_cons] at h_map
        rcases Bool.or_eq_true_iff.mp h_map with h_eq | h_rest
        · left
          rw [List.contains_cons, h_eq, Bool.true_or]
        · right
          exact h_rest
    cases h_xp : x.previousId with
    | none =>
      rw [h_xp] at h_top
      exact ih (x.id :: seen) h_top h_prev'
    | some qid =>
      rw [h_xp] at h_top
      dsimp at h_top ⊢
      rcases Bool.and_eq_true_iff.mp h_top with ⟨h_q, h_rest_top⟩
      rw [h_q, Bool.true_and]
      exact ih (x.id :: seen) h_rest_top h_prev'

theorem serializeEntryChainList_preserves_distinct_and_topological (toSurrogate : α → σ)
    (entry : BackstackEntry α) (acc : List (BackstackEntrySurrogate σ))
    (h_nodup : hasDuplicateId (acc.map BackstackEntrySurrogate.id) = false)
    (h_top : isTopologicalOrderList [] acc = true) :
    hasDuplicateId ((serializeEntryChainList toSurrogate entry acc).map BackstackEntrySurrogate.id) = false ∧
    isTopologicalOrderList [] (serializeEntryChainList toSurrogate entry acc) = true := by
  rw [serializeEntryChainList_eq]
  dsimp
  have h_after_prev :
      hasDuplicateId
        ((match entry.previous with
          | none => acc
          | some prev => serializeEntryChainList toSurrogate prev acc).map BackstackEntrySurrogate.id) = false ∧
      isTopologicalOrderList []
        (match entry.previous with
        | none => acc
        | some prev => serializeEntryChainList toSurrogate prev acc) = true := by
    cases h_prev : entry.previous with
    | none => exact ⟨h_nodup, h_top⟩
    | some prev =>
      exact serializeEntryChainList_preserves_distinct_and_topological toSurrogate prev acc h_nodup h_top
  rcases h_after_prev with ⟨h_nodup_prev, h_top_prev⟩
  cases h2 : hasSurrogateIdList
      (match entry.previous with
      | none => acc
      | some prev => serializeEntryChainList toSurrogate prev acc) entry.id with
  | true => exact ⟨h_nodup_prev, h_top_prev⟩
  | false =>
    dsimp
    refine ⟨?_, ?_⟩
    · rw [List.map_append, List.map_singleton]
      rw [hasSurrogateIdList_eq_contains_map_id] at h2
      exact hasDuplicateId_snoc h_nodup_prev h2
    · apply isTopologicalOrderList_snoc [] _ (entryToSurrogate toSurrogate entry) h_top_prev
      intro pid hp
      dsimp [entryToSurrogate, previousEntryId] at hp
      cases h_prev : entry.previous with
      | none =>
        rw [h_prev] at hp
        contradiction
      | some prev =>
        rw [h_prev] at hp
        dsimp [h_prev]
        injection hp with h_pid
        subst h_pid
        right
        rw [← hasSurrogateIdList_eq_contains_map_id]
        exact hasSurrogateIdList_serializeEntryChainList_self toSurrogate prev acc
termination_by sizeOf entry
decreasing_by
  cases entry with
  | mk v prevOpt i =>
    dsimp [BackstackEntry.previous] at h_prev
    subst h_prev
    decreasing_tactic

theorem serializeEntriesList_preserves_distinct_and_topological (toSurrogate : α → σ)
    (entries : List (BackstackEntry α)) (acc : List (BackstackEntrySurrogate σ))
    (h_nodup : hasDuplicateId (acc.map BackstackEntrySurrogate.id) = false)
    (h_top : isTopologicalOrderList [] acc = true) :
    hasDuplicateId ((serializeEntriesList toSurrogate entries acc).map BackstackEntrySurrogate.id) = false ∧
    isTopologicalOrderList [] (serializeEntriesList toSurrogate entries acc) = true := by
  induction entries generalizing acc with
  | nil => exact ⟨h_nodup, h_top⟩
  | cons e rest ih =>
    unfold serializeEntriesList
    rcases serializeEntryChainList_preserves_distinct_and_topological toSurrogate e acc h_nodup h_top with
      ⟨h_nodup', h_top'⟩
    exact ih (serializeEntryChainList toSurrogate e acc) h_nodup' h_top'

theorem serializeBackstackEntries_distinct_and_topological_Impl (entries : Array (BackstackEntry α))
    (toSurrogate : α → σ) :
    allDistinctIds (serializeBackstackEntries entries toSurrogate) = true ∧
    isTopologicalOrder (serializeBackstackEntries entries toSurrogate) = true := by
  unfold allDistinctIds isTopologicalOrder serializeBackstackEntries
  rcases serializeEntriesList_preserves_distinct_and_topological toSurrogate entries.toList [] rfl rfl with
    ⟨h_nodup, h_top⟩
  rw [Bool.not_eq_true']
  exact ⟨h_nodup, h_top⟩

theorem ValidTopologicalEntriesAfter_no_dup {seen entries : List (BackstackEntry α)}
    (h_top : ValidTopologicalEntriesAfter seen entries)
    (h_nodup : hasDuplicateId (seen.map BackstackEntry.id) = false) :
    hasDuplicateId ((seen ++ entries).map BackstackEntry.id) = false := by
  induction entries generalizing seen with
  | nil =>
    rw [List.append_nil]
    exact h_nodup
  | cons e rest ih =>
    rcases h_top with ⟨h_fresh, _, h_rest⟩
    have h_nodup' : hasDuplicateId ((seen ++ [e]).map BackstackEntry.id) = false := by
      rw [List.map_append, List.map_singleton]
      exact hasDuplicateId_snoc h_nodup (contains_map_id_eq_false_of_findEntryList_none h_fresh)
    have h_ih := ih h_rest h_nodup'
    rw [List.append_assoc, List.singleton_append] at h_ih
    exact h_ih

theorem ValidTopologicalEntriesAfter_closed {seen entries : List (BackstackEntry α)}
    (h_top : ValidTopologicalEntriesAfter seen entries) :
    ∀ e ∈ entries,
      findEntryList (seen ++ entries) e.id = some e ∧
      (∀ prev, e.previous = some prev → findEntryList (seen ++ entries) prev.id = some prev) := by
  induction entries generalizing seen with
  | nil =>
    intro e he
    contradiction
  | cons x rest ih =>
    rcases h_top with ⟨h_fresh, h_prev, h_rest⟩
    intro e he
    rw [ ← List.singleton_append, ← List.append_assoc]
    rcases List.mem_cons.mp he with rfl | he_rest
    · refine ⟨?_, ?_⟩
      · have h_in_snoc : findEntryList (seen ++ [e]) e.id = some e := by
          rw [findEntryList_append_of_none h_fresh]
          exact findEntryList_singleton_self e
        exact findEntryList_append_of_some h_in_snoc
      · intro prev hp
        have h_in_seen := h_prev prev hp
        have h_in_snoc : findEntryList (seen ++ [e]) prev.id = some prev :=
          findEntryList_append_of_some h_in_seen
        exact findEntryList_append_of_some h_in_snoc
    · exact ih h_rest e he_rest

theorem ValidTopologicalEntries_chain_in_list (entries : List (BackstackEntry α))
    (h_top : ValidTopologicalEntries entries) (cur : BackstackEntry α) :
    cur ∈ entries → ∀ a ∈ iterateBackstackEntryList cur, findEntryList entries a.id = some a := by
  cases cur with
  | mk v prevOpt i =>
    intro h_mem a ha
    have h_closed := ValidTopologicalEntriesAfter_closed h_top (.mk v prevOpt i) h_mem
    dsimp at h_closed
    cases prevOpt with
    | none =>
      rw [iterateBackstackEntryList_mk_none] at ha
      simp at ha
      subst ha
      exact h_closed.1
    | some prev =>
      rw [iterateBackstackEntryList_mk_some] at ha
      rcases List.mem_cons.mp ha with rfl | ha_prev
      · exact h_closed.1
      · have h_find_prev := h_closed.2 prev rfl
        have h_prev_mem := (findEntryList_eq_some_mem_and_id h_find_prev).1
        exact ValidTopologicalEntries_chain_in_list entries h_top prev h_prev_mem a ha_prev
termination_by sizeOf cur
decreasing_by
  clear h_prev_mem h_mem
  decreasing_tactic

theorem deserializeEntriesList_spec (fromSurrogate : σ → Option (BackstackEntry α) → α)
    (surrogates : List (BackstackEntrySurrogate σ)) (acc : List (BackstackEntry α))
    {res : List (BackstackEntry α)}
    (h_deser : deserializeEntriesList fromSurrogate surrogates acc = some res) :
    ∃ added : List (BackstackEntry α),
      res = acc ++ added ∧
      added.map BackstackEntry.id = surrogates.map BackstackEntrySurrogate.id ∧
      ValidTopologicalEntriesAfter acc added ∧
      (∀ seen : List Uuid, (∀ e ∈ acc, seen.contains e.id = true) →
        isTopologicalOrderList seen surrogates = true) := by
  induction surrogates generalizing acc with
  | nil =>
    unfold deserializeEntriesList at h_deser
    injection h_deser with h_eq
    subst h_eq
    refine ⟨[], ?_, rfl, trivial, ?_⟩
    · rw [List.append_nil]
    · intro _ _
      rfl
  | cons s rest ih =>
    unfold deserializeEntriesList at h_deser
    cases h_fresh : findEntryList acc s.id with
    | some _ =>
      rw [h_fresh] at h_deser
      contradiction
    | none =>
      rw [h_fresh] at h_deser
      dsimp at h_deser
      cases hp : s.previousId with
      | none =>
        rw [hp] at h_deser
        dsimp at h_deser
        let entry := BackstackEntry.mkEntry (fromSurrogate s.surrogate none) none s.id
        rcases ih (acc ++ [entry]) h_deser with ⟨addedRest, h_res, h_ids, h_top_rest, h_topo_bool⟩
        refine ⟨entry :: addedRest, ?_, ?_, ?_, ?_⟩
        · rw [h_res, List.append_assoc, List.singleton_append]
        · dsimp [List.map, entry, BackstackEntry.mkEntry, BackstackEntry.id]
          rw [h_ids]
        · refine ⟨h_fresh, ?_, h_top_rest⟩
          intro prev h_prev
          dsimp [entry, BackstackEntry.mkEntry, BackstackEntry.previous] at h_prev
          contradiction
        · intro seen h_seen
          unfold isTopologicalOrderList
          rw [hp]
          apply h_topo_bool (s.id :: seen)
          intro e he
          rw [List.mem_append] at he
          rcases he with he_acc | he_single
          · rw [List.contains_cons, h_seen e he_acc, Bool.or_true]
          · simp at he_single
            subst he_single
            dsimp [entry, BackstackEntry.mkEntry, BackstackEntry.id]
            rw [List.contains_cons]
            simp
      | some pid =>
        rw [hp] at h_deser
        dsimp at h_deser
        cases h_find_prev : findEntryList acc pid with
        | none =>
          rw [h_find_prev] at h_deser
          contradiction
        | some prev =>
          rw [h_find_prev] at h_deser
          dsimp at h_deser
          let entry := BackstackEntry.mkEntry (fromSurrogate s.surrogate (some prev)) (some prev) s.id
          rcases ih (acc ++ [entry]) h_deser with ⟨addedRest, h_res, h_ids, h_top_rest, h_topo_bool⟩
          have h_prev_mem_id := findEntryList_eq_some_mem_and_id h_find_prev
          refine ⟨entry :: addedRest, ?_, ?_, ?_, ?_⟩
          · rw [h_res, List.append_assoc, List.singleton_append]
          · dsimp [List.map, entry, BackstackEntry.mkEntry, BackstackEntry.id]
            rw [h_ids]
          · refine ⟨h_fresh, ?_, h_top_rest⟩
            intro prev' h_prev'
            dsimp [entry, BackstackEntry.mkEntry, BackstackEntry.previous] at h_prev'
            injection h_prev' with h_eq_prev
            subst h_eq_prev
            rw [h_prev_mem_id.2]
            exact h_find_prev
          · intro seen h_seen
            unfold isTopologicalOrderList
            rw [hp]
            dsimp
            have h_pid_in_seen : seen.contains pid = true := by
              rw [← h_prev_mem_id.2]
              exact h_seen prev h_prev_mem_id.1
            rw [h_pid_in_seen, Bool.true_and]
            apply h_topo_bool (s.id :: seen)
            intro e he
            rw [List.mem_append] at he
            rcases he with he_acc | he_single
            · rw [List.contains_cons, h_seen e he_acc, Bool.or_true]
            · simp at he_single
              subst he_single
              dsimp [entry, BackstackEntry.mkEntry, BackstackEntry.id]
              rw [List.contains_cons]
              simp

theorem deserializeBackstackEntries_sound_Impl (surrogates : Array (BackstackEntrySurrogate σ))
    (fromSurrogate : σ → Option (BackstackEntry α) → α)
    (h_deser : deserializeBackstackEntries surrogates fromSurrogate = some entries) :
    allDistinctIds surrogates = true ∧
    isTopologicalOrder surrogates = true ∧
    allDistinctEntryIds entries = true ∧
    ValidTopologicalEntries entries.toList := by
  unfold deserializeBackstackEntries at h_deser
  cases h_list : deserializeEntriesList fromSurrogate surrogates.toList [] with
  | none =>
    rw [h_list] at h_deser
    contradiction
  | some list =>
    rw [h_list] at h_deser
    injection h_deser with h_eq
    subst h_eq
    rcases deserializeEntriesList_spec fromSurrogate surrogates.toList [] h_list with
      ⟨added, h_res, h_ids, h_top, h_topo_bool⟩
    dsimp at h_res
    rw [h_res]
    have h_nodup_entries : hasDuplicateId (List.map BackstackEntry.id added) = false :=
      ValidTopologicalEntriesAfter_no_dup h_top rfl
    have h_nodup_surr : hasDuplicateId (List.map BackstackEntrySurrogate.id surrogates.toList) = false := by
      rw [← h_ids]
      exact h_nodup_entries
    have h_topo_surr : isTopologicalOrder surrogates = true := by
      unfold isTopologicalOrder
      apply h_topo_bool []
      intro e he
      contradiction
    refine ⟨?_, h_topo_surr, ?_, h_top⟩
    · unfold allDistinctIds
      rw [Bool.not_eq_true']
      exact h_nodup_surr
    · unfold allDistinctEntryIds
      rw [Bool.not_eq_true']
      exact h_nodup_entries

theorem deserializeBackstack_preserves_valid_Impl (surrogates : Array (BackstackEntrySurrogate σ))
    (fromSurrogate : σ → Option (BackstackEntry α) → α) (currentId : Uuid)
    (h_deser : deserializeBackstack surrogates fromSurrogate currentId = some state) :
    ValidBackstackState state ∧
    ValidTopologicalEntries state.entries.toList := by
  unfold deserializeBackstack at h_deser
  cases h_entries : deserializeBackstackEntries surrogates fromSurrogate with
  | none =>
    rw [h_entries] at h_deser
    contradiction
  | some entries =>
    rw [h_entries] at h_deser
    dsimp at h_deser
    cases h_has : hasEntry entries currentId with
    | false =>
      rw [h_has] at h_deser
      contradiction
    | true =>
      rw [h_has] at h_deser
      injection h_deser with h_eq
      subst h_eq
      rcases deserializeBackstackEntries_sound_Impl surrogates fromSurrogate h_entries with
        ⟨_, _, h_dist, h_top⟩
      unfold hasEntry at h_has
      rcases Option.isSome_iff_exists.mp h_has with ⟨cur, h_cur⟩
      have h_cur_mem := (findEntryList_eq_some_mem_and_id h_cur).1
      have h_chain := ValidTopologicalEntries_chain_in_list entries.toList h_top cur h_cur_mem
      exact ⟨⟨h_dist, cur, h_cur, h_chain⟩, h_top⟩

theorem map_entryToSurrogate_id (toSurrogate : α → σ) (entries : List (BackstackEntry α)) :
    (entries.map (entryToSurrogate toSurrogate)).map BackstackEntrySurrogate.id = entries.map BackstackEntry.id := by
  induction entries with
  | nil => rfl
  | cons e rest ih =>
    dsimp [List.map, entryToSurrogate]
    rw [ih]

theorem hasSurrogateIdList_map_entryToSurrogate (toSurrogate : α → σ) (entries : List (BackstackEntry α))
    (targetId : Uuid) :
    hasSurrogateIdList (entries.map (entryToSurrogate toSurrogate)) targetId =
      (entries.map BackstackEntry.id).contains targetId := by
  rw [hasSurrogateIdList_eq_contains_map_id, map_entryToSurrogate_id]

theorem serializeEntryChainList_eq_acc_of_chain_in (toSurrogate : α → σ)
    (p : BackstackEntry α) (acc : List (BackstackEntrySurrogate σ))
    (h_in : ∀ a ∈ iterateBackstackEntryList p, hasSurrogateIdList acc a.id = true) :
    serializeEntryChainList toSurrogate p acc = acc := by
  rw [serializeEntryChainList_eq]
  dsimp
  have h_prev_eq :
      (match p.previous with
      | none => acc
      | some prev => serializeEntryChainList toSurrogate prev acc) = acc := by
    cases hp : p.previous with
    | none => rfl
    | some prev =>
      apply serializeEntryChainList_eq_acc_of_chain_in toSurrogate prev acc
      intro a ha
      exact h_in a (mem_iterateBackstackEntryList_of_prev hp ha)
  rw [h_prev_eq]
  have h_self : hasSurrogateIdList acc p.id = true :=
    h_in p (self_mem_iterateBackstackEntryList p)
  rw [h_self]
  rfl
termination_by sizeOf p
decreasing_by
  cases p with
  | mk v prevOpt i =>
    dsimp [BackstackEntry.previous] at hp
    subst hp
    decreasing_tactic

theorem serializeEntriesList_of_topological (toSurrogate : α → σ)
    {seen entries : List (BackstackEntry α)}
    (h_seen : ValidTopologicalEntries seen)
    (h_top : ValidTopologicalEntriesAfter seen entries) :
    serializeEntriesList toSurrogate entries (seen.map (entryToSurrogate toSurrogate)) =
      (seen ++ entries).map (entryToSurrogate toSurrogate) := by
  induction entries generalizing seen with
  | nil =>
    rw [List.append_nil]
    rfl
  | cons e rest ih =>
    rcases h_top with ⟨h_fresh, h_prev, h_rest⟩
    unfold serializeEntriesList
    have h_e_not_in : hasSurrogateIdList (seen.map (entryToSurrogate toSurrogate)) e.id = false := by
      rw [hasSurrogateIdList_map_entryToSurrogate]
      exact contains_map_id_eq_false_of_findEntryList_none h_fresh
    have h_chain_step :
        serializeEntryChainList toSurrogate e (seen.map (entryToSurrogate toSurrogate)) =
          (seen ++ [e]).map (entryToSurrogate toSurrogate) := by
      rw [serializeEntryChainList_eq]
      dsimp
      have h_after_prev :
          (match e.previous with
          | none => seen.map (entryToSurrogate toSurrogate)
          | some prev => serializeEntryChainList toSurrogate prev (seen.map (entryToSurrogate toSurrogate))) =
            seen.map (entryToSurrogate toSurrogate) := by
        cases hp : e.previous with
        | none => rfl
        | some prev =>
          dsimp
          have h_find_prev := h_prev prev hp
          have h_prev_mem := (findEntryList_eq_some_mem_and_id h_find_prev).1
          apply serializeEntryChainList_eq_acc_of_chain_in toSurrogate prev (seen.map (entryToSurrogate toSurrogate))
          intro a ha
          have h_find_a := ValidTopologicalEntries_chain_in_list seen h_seen prev h_prev_mem a ha
          have h_a_mem := (findEntryList_eq_some_mem_and_id h_find_a).1
          rw [hasSurrogateIdList_map_entryToSurrogate, List.contains_iff_mem]
          exact List.mem_map_of_mem h_a_mem
      rw [h_after_prev, h_e_not_in]
      dsimp
      rw [List.map_append, List.map_singleton]
    rw [h_chain_step]
    have h_seen' : ValidTopologicalEntries (seen ++ [e]) :=
      ValidTopologicalEntriesAfter_snoc h_seen h_fresh h_prev
    have h_ih := ih h_seen' h_rest
    rw [List.append_assoc, List.singleton_append] at h_ih
    exact h_ih

theorem deserializeEntriesList_of_topological (toSurrogate : α → σ)
    (fromSurrogate : σ → Option (BackstackEntry α) → α)
    {seen entries : List (BackstackEntry α)}
    (h_top : ValidTopologicalEntriesAfter seen entries)
    (h_val : ∀ e : BackstackEntry α, fromSurrogate (toSurrogate e.value) e.previous = e.value) :
    deserializeEntriesList fromSurrogate (entries.map (entryToSurrogate toSurrogate)) seen =
      some (seen ++ entries) := by
  induction entries generalizing seen with
  | nil =>
    rw [List.append_nil]
    rfl
  | cons e rest ih =>
    rcases h_top with ⟨h_fresh, h_prev, h_rest⟩
    dsimp [List.map]
    unfold deserializeEntriesList
    have h_not_some : (findEntryList seen (entryToSurrogate toSurrogate e).id).isSome = false := by
      dsimp [entryToSurrogate]
      rw [h_fresh]
      rfl
    rw [h_not_some]
    dsimp
    cases e with
    | mk v prevOpt i =>
      cases prevOpt with
      | none =>
        dsimp [entryToSurrogate, previousEntryId, BackstackEntry.previous, BackstackEntry.value, BackstackEntry.id]
        have hv : fromSurrogate (toSurrogate v) none = v := h_val (.mk v none i)
        rw [hv]
        dsimp [BackstackEntry.mkEntry]
        have h_ih := ih h_rest
        rw [List.append_assoc, List.singleton_append] at h_ih
        exact h_ih
      | some prev =>
        have h_find_prev : findEntryList seen prev.id = some prev := h_prev prev rfl
        have h_prev_id : (entryToSurrogate toSurrogate (.mk v (some prev) i)).previousId = some prev.id := rfl
        have h_surr : (entryToSurrogate toSurrogate (.mk v (some prev) i)).surrogate = toSurrogate v := rfl
        have h_id : (entryToSurrogate toSurrogate (.mk v (some prev) i)).id = i := rfl
        rw [h_prev_id, h_surr, h_id]
        dsimp
        rw [h_find_prev]
        dsimp
        have hv : fromSurrogate (toSurrogate v) (some prev) = v := h_val (.mk v (some prev) i)
        rw [hv]
        dsimp [BackstackEntry.mkEntry]
        have h_ih := ih h_rest
        rw [List.append_assoc, List.singleton_append] at h_ih
        exact h_ih

theorem deserialize_serialize_entries_roundtrip_Impl (entries : Array (BackstackEntry α))
    (toSurrogate : α → σ) (fromSurrogate : σ → Option (BackstackEntry α) → α)
    (h_top : ValidTopologicalEntries entries.toList)
    (h_val : ∀ e : BackstackEntry α, fromSurrogate (toSurrogate e.value) e.previous = e.value) :
    deserializeBackstackEntries (serializeBackstackEntries entries toSurrogate) fromSurrogate = some entries := by
  unfold deserializeBackstackEntries serializeBackstackEntries
  have h_ser : serializeEntriesList toSurrogate entries.toList [] =
      entries.toList.map (entryToSurrogate toSurrogate) :=
    @serializeEntriesList_of_topological _ _ toSurrogate [] entries.toList trivial h_top
  have h_deser : deserializeEntriesList fromSurrogate (entries.toList.map (entryToSurrogate toSurrogate)) [] =
      some entries.toList :=
    deserializeEntriesList_of_topological toSurrogate fromSurrogate h_top h_val
  dsimp
  rw [h_ser, h_deser]

theorem deserialize_serialize_backstack_roundtrip_Impl (state : BackstackState α)
    (toSurrogate : α → σ) (fromSurrogate : σ → Option (BackstackEntry α) → α)
    (h_valid : ValidBackstackState state)
    (h_top : ValidTopologicalEntries state.entries.toList)
    (h_val : ∀ e : BackstackEntry α, fromSurrogate (toSurrogate e.value) e.previous = e.value) :
    deserializeBackstack (serializeBackstack state toSurrogate) fromSurrogate state.currentEntryId = some state := by
  unfold deserializeBackstack serializeBackstack
  rw [deserialize_serialize_entries_roundtrip_Impl state.entries toSurrogate fromSurrogate h_top h_val]
  dsimp
  rcases h_valid with ⟨_, cur, h_cur, _⟩
  have h_has : hasEntry state.entries state.currentEntryId = true := by
    unfold hasEntry
    rw [h_cur]
    rfl
  rw [h_has]
  rfl

end Navigation
