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
import NavigationTheorems

namespace Navigation

/-!
# Mutation and Non-Vacuity Proofs for `navigation`

1. **Non-vacuity theorems**: Demonstrate that the hypotheses of the master theorems in
   `NavigationTheorems.lean` are simultaneously satisfiable on concrete multi-entry backstack states.
2. **Mutation refutation theorems**: Each mutant below represents a plausible buggy implementation of
   backstack operations. For each mutant, we prove that it violates a master theorem in
   `NavigationTheorems.lean`, ensuring the specification catches real regressions.
-/

/-! ## Non-Vacuity Witnesses -/

theorem nonvacuous_navigate_and_pop :
    ∃ (s0 s1 : BackstackState Nat),
      s0 = initialBackstack ⟨1, 0⟩ 10 ∧
      ValidBackstackState s0 ∧
      ValidTopologicalEntries s0.entries.toList ∧
      findEntry s0.entries ⟨2, 0⟩ = none ∧
      navigate s0 20 ⟨2, 0⟩ = some s1 ∧
      ValidBackstackState s1 ∧
      ValidTopologicalEntries s1.entries.toList ∧
      popBackstack s1 = some s0 := by
  let s0 := initialBackstack ⟨1, 0⟩ 10
  have h_init := initialBackstack_valid ⟨1, 0⟩ 10
  have h_fresh : findEntry s0.entries ⟨2, 0⟩ = none := rfl
  rcases navigate_preserves_valid s0 20 ⟨2, 0⟩ h_init.1 h_init.2 h_fresh with
    ⟨s1, h_nav, h_valid1, h_top1, _⟩
  have h_pop := pop_after_navigate_eq_original s0 20 ⟨2, 0⟩ h_init.1 h_fresh h_nav
  exact ⟨s0, s1, rfl, h_init.1, h_init.2, h_fresh, h_nav, h_valid1, h_top1, h_pop⟩

theorem nonvacuous_roundtrip :
    ∃ (s0 : BackstackState Nat),
      ValidBackstackState s0 ∧
      ValidTopologicalEntries s0.entries.toList ∧
      deserializeBackstack (serializeBackstack s0 id) (fun x _ => x) s0.currentEntryId = some s0 := by
  let s0 := initialBackstack ⟨1, 0⟩ 42
  have h_init := initialBackstack_valid ⟨1, 0⟩ 42
  have h_rt := deserialize_serialize_backstack_roundtrip s0 id (fun x _ => x) h_init.1 h_init.2 (fun _ => rfl)
  exact ⟨s0, h_init.1, h_init.2, h_rt⟩

/-! ## Mutant 1: `navigate` that forgets to update `currentEntryId` -/

def mutantNavigateRetainCurrent (state : BackstackState α) (newVal : α) (newId : Uuid) :
    Option (BackstackState α) :=
  match findEntry state.entries state.currentEntryId with
  | none => none
  | some previous =>
    let newEntry := BackstackEntry.mkEntry newVal (some previous) newId
    some { entries := state.entries.push newEntry, currentEntryId := state.currentEntryId }

theorem mutant1_violates_pop_after_navigate :
    ¬ ∀ (state state' : BackstackState Nat) (val : Nat) (newId : Uuid),
      ValidBackstackState state →
      findEntry state.entries newId = none →
      mutantNavigateRetainCurrent state val newId = some state' →
      popBackstack state' = some state := by
  intro h
  let s0 := initialBackstack ⟨1, 0⟩ 42
  have h_valid : ValidBackstackState s0 := (initialBackstack_valid ⟨1, 0⟩ 42).1
  have h_fresh : findEntry s0.entries ⟨2, 0⟩ = none := rfl
  let e1 := BackstackEntry.mkEntry 42 none ⟨1, 0⟩
  let e2 := BackstackEntry.mkEntry 99 (some e1) ⟨2, 0⟩
  let s1 : BackstackState Nat := { entries := #[e1, e2], currentEntryId := ⟨1, 0⟩ }
  have h_nav : mutantNavigateRetainCurrent s0 99 ⟨2, 0⟩ = some s1 := rfl
  have h_contra := h s0 s1 99 ⟨2, 0⟩ h_valid h_fresh h_nav
  have h_pop_none : popBackstack s1 = none := rfl
  rw [h_pop_none] at h_contra
  contradiction

/-! ## Mutant 2: `navigate` that drops the `previous` link on the new entry -/

def mutantNavigateDropPrevious (state : BackstackState α) (newVal : α) (newId : Uuid) :
    Option (BackstackState α) :=
  match findEntry state.entries state.currentEntryId with
  | none => none
  | some _ =>
    let newEntry := BackstackEntry.mkEntry newVal none newId
    some { entries := state.entries.push newEntry, currentEntryId := newId }

theorem mutant2_violates_pop_after_navigate :
    ¬ ∀ (state state' : BackstackState Nat) (val : Nat) (newId : Uuid),
      ValidBackstackState state →
      findEntry state.entries newId = none →
      mutantNavigateDropPrevious state val newId = some state' →
      popBackstack state' = some state := by
  intro h
  let s0 := initialBackstack ⟨1, 0⟩ 42
  have h_valid : ValidBackstackState s0 := (initialBackstack_valid ⟨1, 0⟩ 42).1
  have h_fresh : findEntry s0.entries ⟨2, 0⟩ = none := rfl
  let e1 := BackstackEntry.mkEntry 42 none ⟨1, 0⟩
  let e2 := BackstackEntry.mkEntry 99 none ⟨2, 0⟩
  let s1 : BackstackState Nat := { entries := #[e1, e2], currentEntryId := ⟨2, 0⟩ }
  have h_nav : mutantNavigateDropPrevious s0 99 ⟨2, 0⟩ = some s1 := rfl
  have h_contra := h s0 s1 99 ⟨2, 0⟩ h_valid h_fresh h_nav
  have h_pop_none : popBackstack s1 = none := rfl
  rw [h_pop_none] at h_contra
  contradiction

/-! ## Mutant 3: `popBackstack` that updates `currentEntryId` without removing the popped entry -/

def mutantPopRetainEntry (state : BackstackState α) : Option (BackstackState α) :=
  match findEntry state.entries state.currentEntryId with
  | none => none
  | some cur =>
    match cur.previous with
    | none => none
    | some prev =>
      some { entries := state.entries, currentEntryId := prev.id }

theorem mutant3_violates_popBackstack_evicts_current :
    ¬ ∀ (state state' : BackstackState Nat),
      ValidBackstackState state →
      mutantPopRetainEntry state = some state' →
      findEntry state'.entries state.currentEntryId = none := by
  intro h
  let s0 := initialBackstack ⟨1, 0⟩ 42
  have h_init := initialBackstack_valid ⟨1, 0⟩ 42
  have h_fresh : findEntry s0.entries ⟨2, 0⟩ = none := rfl
  rcases navigate_preserves_valid s0 99 ⟨2, 0⟩ h_init.1 h_init.2 h_fresh with
    ⟨s1, h_nav, h_valid1, _, _⟩
  let e1 := BackstackEntry.mkEntry 42 none ⟨1, 0⟩
  let e2 := BackstackEntry.mkEntry 99 (some e1) ⟨2, 0⟩
  have h_s1 : s1 = { entries := #[e1, e2], currentEntryId := ⟨2, 0⟩ } := by
    have h_nav_eq : navigate s0 99 ⟨2, 0⟩ = some { entries := #[e1, e2], currentEntryId := ⟨2, 0⟩ } := rfl
    rw [h_nav_eq] at h_nav
    injection h_nav with h_eq
    exact h_eq.symm
  let s2 : BackstackState Nat := { entries := #[e1, e2], currentEntryId := ⟨1, 0⟩ }
  have h_pop : mutantPopRetainEntry s1 = some s2 := by
    rw [h_s1]
    rfl
  have h_contra := h s1 s2 h_valid1 h_pop
  rw [h_s1] at h_contra
  have h_still_there : findEntry s2.entries ⟨2, 0⟩ = some e2 := rfl
  dsimp at h_contra
  rw [h_still_there] at h_contra
  contradiction

/-! ## Mutant 4: `popUpTo` that ignores `inclusive = false` and always pops inclusively -/

def mutantPopUpToAlwaysInclusive (state : BackstackState α) (p : BackstackEntry α → Bool) :
    Option (BackstackState α) :=
  popUpTo state p true

theorem mutant4_violates_popUpTo_current_non_inclusive :
    ¬ ∀ (state : BackstackState Nat) (p : BackstackEntry Nat → Bool) (cur : BackstackEntry Nat),
      ValidBackstackState state →
      findEntry state.entries state.currentEntryId = some cur →
      p cur = true →
      mutantPopUpToAlwaysInclusive state p = some state := by
  intro h
  let s0 := initialBackstack ⟨1, 0⟩ 42
  let e1 := BackstackEntry.mkEntry 42 none ⟨1, 0⟩
  have h_valid : ValidBackstackState s0 := (initialBackstack_valid ⟨1, 0⟩ 42).1
  have h_cur : findEntry s0.entries s0.currentEntryId = some e1 := rfl
  have h_contra := h s0 (fun _ => true) e1 h_valid h_cur rfl
  have h_none : mutantPopUpToAlwaysInclusive s0 (fun _ => true) = none := by
    unfold mutantPopUpToAlwaysInclusive
    rw [popUpTo_current_inclusive_eq_pop s0 (fun _ => true) h_cur rfl]
    exact popBackstack_root_fails s0 h_cur rfl
  rw [h_none] at h_contra
  contradiction

/-! ## Mutant 5: `deserializeBackstackEntries` that skips duplicate ID checking -/

def mutantDeserializeEntriesList (fromSurrogate : σ → Option (BackstackEntry α) → α)
    (surrogates : List (BackstackEntrySurrogate σ))
    (acc : List (BackstackEntry α)) : Option (List (BackstackEntry α)) :=
  match surrogates with
  | [] => some acc
  | s :: rest =>
    match s.previousId with
    | none =>
      let val := fromSurrogate s.surrogate none
      let entry := BackstackEntry.mkEntry val none s.id
      mutantDeserializeEntriesList fromSurrogate rest (acc ++ [entry])
    | some _ => none

theorem mutant5_violates_deserialize_sound :
    ∃ (surrogates : List (BackstackEntrySurrogate Nat)) (res : List (BackstackEntry Nat)),
      mutantDeserializeEntriesList (fun x _ => x) surrogates [] = some res ∧
      hasDuplicateId (surrogates.map BackstackEntrySurrogate.id) = true := by
  let s1 : BackstackEntrySurrogate Nat := ⟨⟨1, 0⟩, none, 10⟩
  let s2 : BackstackEntrySurrogate Nat := ⟨⟨1, 0⟩, none, 20⟩
  let e1 := BackstackEntry.mkEntry 10 none ⟨1, 0⟩
  let e2 := BackstackEntry.mkEntry 20 none ⟨1, 0⟩
  exact ⟨[s1, s2], [e1, e2], rfl, rfl⟩

/-! ## Mutant 6: `popUpTo` that only checks the current entry without walking ancestors -/

def mutantPopUpToNoWalk (state : BackstackState α) (p : BackstackEntry α → Bool) :
    Option (BackstackState α) :=
  match findEntry state.entries state.currentEntryId with
  | none => none
  | some current =>
    if p current then
      some { entries := state.entries, currentEntryId := current.id }
    else
      none

theorem mutant6_violates_popUpTo_complete_non_inclusive :
    ¬ ∀ (state : BackstackState Nat) (p : BackstackEntry Nat → Bool) (cur : BackstackEntry Nat),
      findEntry state.entries state.currentEntryId = some cur →
      (∃ target ∈ iterateBackstackEntryList cur, p target = true) →
      (mutantPopUpToNoWalk state p).isSome = true := by
  intro h
  let e1 := BackstackEntry.mkEntry 10 none ⟨1, 0⟩
  let e2 := BackstackEntry.mkEntry 20 (some e1) ⟨2, 0⟩
  let s1 : BackstackState Nat := { entries := #[e1, e2], currentEntryId := ⟨2, 0⟩ }
  let p : BackstackEntry Nat → Bool := fun e => e.id == ⟨1, 0⟩
  have h_cur : findEntry s1.entries s1.currentEntryId = some e2 := rfl
  have h_mem : e1 ∈ iterateBackstackEntryList e2 := by
    dsimp [e2, BackstackEntry.mkEntry]
    rw [iterateBackstackEntryList_mk_some]
    exact List.Mem.tail _ (self_mem_iterateBackstackEntryList e1)
  have h_exists : ∃ target ∈ iterateBackstackEntryList e2, p target = true := ⟨e1, h_mem, rfl⟩
  have h_contra := h s1 p e2 h_cur h_exists
  have h_none : (mutantPopUpToNoWalk s1 p).isSome = false := rfl
  rw [h_none] at h_contra
  contradiction

end Navigation
