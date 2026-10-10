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

import Algorithm.Basic
import AlgorithmDefs
import proofs.ConfinementProofs

local notation "ℕ" => Nat
local notation "ℤ" => Int

namespace Algorithm

-- =========================================================================
-- List Deduplication and cellsEqual Equivalence Infrastructure
-- =========================================================================

theorem list_all_contains_self [DecidableEq α] (l : List α) :
    l.all (l.contains ·) = true := by
  rw [List.all_eq_true]
  intro x hx
  rw [List.contains_iff_mem]
  exact hx

private def dedupStep [DecidableEq α] (acc : List α) (y : α) : List α :=
  if acc.contains y then acc else acc.concat y

private theorem mem_foldl_dedupStep [DecidableEq α] (xs : List α) (acc : List α) (x : α) :
    x ∈ xs.foldl dedupStep acc ↔ x ∈ acc ∨ x ∈ xs := by
  induction xs generalizing acc with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldl_cons]
    dsimp [dedupStep]
    split
    · rename_i h_cont
      rw [List.contains_iff_mem] at h_cont
      rw [ih acc]
      simp only [List.mem_cons]
      constructor
      · intro h
        rcases h with hacc | hys
        · left; exact hacc
        · right; right; exact hys
      · intro h
        rcases h with hacc | (rfl | hys)
        · left; exact hacc
        · left; exact h_cont
        · right; exact hys
    · rw [ih (acc.concat y)]
      rw [List.concat_eq_append, List.mem_append, List.mem_singleton]
      simp only [List.mem_cons]
      constructor
      · intro h
        rcases h with (hacc | rfl) | hys
        · left; exact hacc
        · right; left; rfl
        · right; right; exact hys
      · intro h
        rcases h with hacc | (rfl | hys)
        · left; left; exact hacc
        · left; right; rfl
        · right; exact hys

theorem mem_deduplicate_iff [DecidableEq α] (x : α) (xs : List α) :
    x ∈ deduplicate xs ↔ x ∈ xs := by
  change x ∈ xs.foldl dedupStep [] ↔ x ∈ xs
  rw [mem_foldl_dedupStep]
  simp

theorem cellsEqual_of_same_elements (a b : List Coord)
    (h : ∀ c, c ∈ a ↔ c ∈ b) :
    cellsEqual a b = true := by
  dsimp [cellsEqual]
  have ha : (deduplicate a).all ((deduplicate b).contains ·) = true := by
    rw [List.all_eq_true]
    intro x hx
    rw [List.contains_iff_mem]
    rw [mem_deduplicate_iff] at hx ⊢
    exact (h x).mp hx
  have hb : (deduplicate b).all ((deduplicate a).contains ·) = true := by
    rw [List.all_eq_true]
    intro x hx
    rw [List.contains_iff_mem]
    rw [mem_deduplicate_iff] at hx ⊢
    exact (h x).mpr hx
  rw [ha, hb]
  rfl

theorem cellsEqual_refl (xs : List Coord) :
    cellsEqual xs xs = true := by
  apply cellsEqual_of_same_elements
  intro c
  rfl

theorem cellsEqual_deduplicate_self (xs : List Coord) :
    cellsEqual xs (deduplicate xs) = true := by
  apply cellsEqual_of_same_elements
  intro c
  rw [mem_deduplicate_iff]

theorem cellsEqual_symm {a b : List Coord}
    (h : cellsEqual a b = true) : cellsEqual b a = true := by
  dsimp [cellsEqual] at h ⊢
  rw [Bool.and_comm]
  exact h

theorem cellsEqual_iff_mem (a b : List Coord) :
    cellsEqual a b = true ↔ (∀ c, c ∈ a ↔ c ∈ b) := by
  constructor
  · intro h c
    dsimp [cellsEqual] at h
    rw [Bool.and_eq_true] at h
    rcases h with ⟨ha, hb⟩
    rw [List.all_eq_true] at ha hb
    constructor
    · intro hca
      have hca' : c ∈ deduplicate a := by rw [mem_deduplicate_iff]; exact hca
      have hcont := ha c hca'
      rw [List.contains_iff_mem, mem_deduplicate_iff] at hcont
      exact hcont
    · intro hcb
      have hcb' : c ∈ deduplicate b := by rw [mem_deduplicate_iff]; exact hcb
      have hcont := hb c hcb'
      rw [List.contains_iff_mem, mem_deduplicate_iff] at hcont
      exact hcont
  · intro h
    exact cellsEqual_of_same_elements a b h

theorem cellsEqual_trans {a b c : List Coord}
    (h1 : cellsEqual a b = true)
    (h2 : cellsEqual b c = true) :
    cellsEqual a c = true := by
  rw [cellsEqual_iff_mem] at h1 h2 ⊢
  intro x
  rw [h1 x, h2 x]

theorem cellsEqual_append_append {a1 a2 b1 b2 : List Coord}
    (h1 : cellsEqual a1 b1 = true)
    (h2 : cellsEqual a2 b2 = true) :
    cellsEqual (a1 ++ a2) (b1 ++ b2) = true := by
  rw [cellsEqual_iff_mem] at h1 h2 ⊢
  intro x
  simp only [List.mem_append]
  rw [h1 x, h2 x]

private theorem foldl_dedupStep_of_nodup [DecidableEq α] (xs : List α) (acc : List α)
    (h_nodup : xs.Nodup) (h_disj : ∀ x ∈ xs, ¬ x ∈ acc) :
    xs.foldl dedupStep acc = acc ++ xs := by
  induction xs generalizing acc with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldl_cons]
    have hy_not_acc : ¬ y ∈ acc := h_disj y (List.Mem.head ys)
    have h_contains : acc.contains y = false := by
      rw [Bool.eq_false_iff]
      intro h_cont
      rw [List.contains_iff_mem] at h_cont
      exact hy_not_acc h_cont
    have h_step : dedupStep acc y = acc ++ [y] := by
      dsimp [dedupStep]
      rw [h_contains]
      simp [List.concat_eq_append]
    rw [h_step]
    have h_nodup_ys : ys.Nodup := (List.nodup_cons.mp h_nodup).2
    have hy_not_ys : ¬ y ∈ ys := (List.nodup_cons.mp h_nodup).1
    have h_disj_ys : ∀ x ∈ ys, ¬ x ∈ acc ++ [y] := by
      intro x hx_in_ys hx_in_acc_y
      rw [List.mem_append, List.mem_singleton] at hx_in_acc_y
      rcases hx_in_acc_y with hx_acc | hx_y
      · exact h_disj x (List.Mem.tail y hx_in_ys) hx_acc
      · subst hx_y
        exact hy_not_ys hx_in_ys
    rw [ih (acc ++ [y]) h_nodup_ys h_disj_ys]
    rw [List.append_assoc]
    rfl

private theorem nodup_foldl_dedupStep [DecidableEq α] (xs : List α) (acc : List α)
    (h_acc : acc.Nodup) :
    (xs.foldl dedupStep acc).Nodup := by
  induction xs generalizing acc with
  | nil => exact h_acc
  | cons y ys ih =>
    simp only [List.foldl_cons]
    dsimp [dedupStep]
    split
    · exact ih acc h_acc
    · rename_i h
      rw [List.concat_eq_append]
      apply ih
      rw [List.nodup_append]
      have h_sing : [y].Nodup := by simp [List.Nodup]
      refine ⟨h_acc, h_sing, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst hb
      intro h_eq
      subst h_eq
      have : acc.contains a = true := by rw [List.contains_iff_mem]; exact ha
      exact h this

theorem nodup_deduplicate [DecidableEq α] (xs : List α) :
    (deduplicate xs).Nodup := by
  change (xs.foldl dedupStep []).Nodup
  exact nodup_foldl_dedupStep xs [] List.nodup_nil

theorem deduplicate_of_nodup [DecidableEq α] (xs : List α) (h : xs.Nodup) :
    deduplicate xs = xs := by
  change xs.foldl dedupStep [] = xs
  have := foldl_dedupStep_of_nodup xs [] h (fun _ _ => List.not_mem_nil)
  simpa using this

theorem deduplicate_idempotent [DecidableEq α] (xs : List α) :
    deduplicate (deduplicate xs) = deduplicate xs :=
  deduplicate_of_nodup (deduplicate xs) (nodup_deduplicate xs)

theorem cellsEqual_of_eq {a b : List Coord} (h : a = b) :
    cellsEqual a b = true := by
  subst h
  exact cellsEqual_refl a

theorem stepGrid_deduplicate (s : List Coord) :
    stepGrid (deduplicate s) = stepGrid s := by
  dsimp [stepGrid]
  rw [deduplicate_idempotent]

theorem stepN_zero_cellsEqual (s : List Coord) :
    cellsEqual s (stepN 0 s) = true := by
  dsimp [stepN]
  exact cellsEqual_deduplicate_self s

theorem stepGrid_cellsEqual_stepGrid {a b : List Coord}
    (h : cellsEqual a b = true) :
    cellsEqual (stepGrid a) (stepGrid b) = true := by
  rw [cellsEqual_iff_mem] at h ⊢
  intro c
  dsimp [stepGrid]
  simp only [List.mem_filter]
  have h_cand : c ∈ candidateCells (deduplicate a) ↔ c ∈ candidateCells (deduplicate b) := by
    dsimp [candidateCells]
    rw [mem_deduplicate_iff, mem_deduplicate_iff]
    simp only [List.mem_append, List.mem_flatMap]
    constructor
    · intro hc
      rcases hc with hca | ⟨p, hpa, hcp⟩
      · rw [mem_deduplicate_iff] at hca
        left; rw [mem_deduplicate_iff]; exact (h c).mp hca
      · rw [mem_deduplicate_iff] at hpa
        right; refine ⟨p, ?_, hcp⟩
        rw [mem_deduplicate_iff]; exact (h p).mp hpa
    · intro hc
      rcases hc with hcb | ⟨p, hpb, hcp⟩
      · rw [mem_deduplicate_iff] at hcb
        left; rw [mem_deduplicate_iff]; exact (h c).mpr hcb
      · rw [mem_deduplicate_iff] at hpb
        right; refine ⟨p, ?_, hcp⟩
        rw [mem_deduplicate_iff]; exact (h p).mpr hpb
  have h_rule :
    lifeRule ((deduplicate a).contains c) (countAliveNeighbors c (deduplicate a)) =
    lifeRule ((deduplicate b).contains c) (countAliveNeighbors c (deduplicate b)) := by
    have h_cont : (deduplicate a).contains c = (deduplicate b).contains c := by
      rw [Bool.eq_iff_iff]
      rw [List.contains_iff_mem, List.contains_iff_mem]
      rw [mem_deduplicate_iff, mem_deduplicate_iff]
      exact h c
    have h_nbr : countAliveNeighbors c (deduplicate a) = countAliveNeighbors c (deduplicate b) := by
      dsimp [countAliveNeighbors]
      have h_filt :
        (mooreNeighbors c).filter (fun n => (deduplicate a).contains n) =
        (mooreNeighbors c).filter (fun n => (deduplicate b).contains n) := by
        apply List.filter_congr
        intro n _
        rw [Bool.eq_iff_iff]
        rw [List.contains_iff_mem, List.contains_iff_mem]
        rw [mem_deduplicate_iff, mem_deduplicate_iff]
        exact h n
      rw [h_filt]
    rw [h_cont, h_nbr]
  rw [h_cand, h_rule]

theorem stepGrid_support (s : List Coord) (c : Coord) (hc : c ∈ stepGrid s) :
    ∃ p ∈ s, max (c.1 - p.1).natAbs (c.2 - p.2).natAbs ≤ 1 := by
  dsimp [stepGrid] at hc
  rw [List.mem_filter] at hc
  have hcand := hc.1
  dsimp [candidateCells] at hcand
  rw [mem_deduplicate_iff] at hcand
  rw [List.mem_append] at hcand
  rcases hcand with h_in | h_nbr
  · rw [mem_deduplicate_iff] at h_in
    refine ⟨c, h_in, ?_⟩
    simp
  · rw [List.mem_flatMap] at h_nbr
    rcases h_nbr with ⟨p, hp, hcp⟩
    rw [mem_deduplicate_iff] at hp
    refine ⟨p, hp, ?_⟩
    dsimp [mooreNeighbors] at hcp
    rw [List.mem_map] at hcp
    rcases hcp with ⟨⟨dx, dy⟩, hoff, heq⟩
    have hdist := mooreOffsets_chebyshevDist (dx, dy) hoff
    rw [← heq]
    dsimp
    have hx : p.1 + dx - p.1 = dx := by omega
    have hy : p.2 + dy - p.2 = dy := by omega
    rw [hx, hy]
    exact hdist

theorem stepN_cellsEqual_stepN (n : ℕ) {a b : List Coord}
    (h : cellsEqual a b = true) :
    cellsEqual (stepN n a) (stepN n b) = true := by
  induction n with
  | zero =>
    dsimp [stepN]
    have ha : cellsEqual (deduplicate a) a = true := cellsEqual_symm (cellsEqual_deduplicate_self a)
    have hb : cellsEqual b (deduplicate b) = true := cellsEqual_deduplicate_self b
    exact cellsEqual_trans (cellsEqual_trans ha h) hb
  | succ n ih =>
    dsimp [stepN]
    exact stepGrid_cellsEqual_stepGrid ih

theorem stepN_stepGrid_cellsEqual (n : ℕ) (s : List Coord) :
    cellsEqual (stepN n (stepGrid s)) (stepN (n + 1) s) = true := by
  induction n with
  | zero =>
    dsimp [stepN]
    rw [stepGrid_deduplicate]
    exact cellsEqual_symm (cellsEqual_deduplicate_self (stepGrid s))
  | succ n ih =>
    dsimp [stepN]
    exact stepGrid_cellsEqual_stepGrid ih

theorem mem_mooreNeighbors_symm (c p : Coord) :
    p ∈ mooreNeighbors c ↔ c ∈ mooreNeighbors p := by
  dsimp [mooreNeighbors]
  simp only [List.mem_map]
  constructor
  · intro ⟨⟨dx, dy⟩, hoff, heq⟩
    refine ⟨(-dx, -dy), ?_, ?_⟩
    · simp only [mooreOffsets, List.mem_cons, List.not_mem_nil] at hoff ⊢
      rcases hoff with h | h | h | h | h | h | h | (h | hf)
      · injection h with hx hy; subst hx hy; decide
      · injection h with hx hy; subst hx hy; decide
      · injection h with hx hy; subst hx hy; decide
      · injection h with hx hy; subst hx hy; decide
      · injection h with hx hy; subst hx hy; decide
      · injection h with hx hy; subst hx hy; decide
      · injection h with hx hy; subst hx hy; decide
      · injection h with hx hy; subst hx hy; decide
      · nomatch hf
    · dsimp; rw [← heq]; ext <;> dsimp <;> omega
  · intro ⟨⟨dx, dy⟩, hoff, heq⟩
    refine ⟨(-dx, -dy), ?_, ?_⟩
    · simp only [mooreOffsets, List.mem_cons, List.not_mem_nil] at hoff ⊢
      rcases hoff with h | h | h | h | h | h | h | (h | hf)
      · injection h with hx hy; subst hx hy; decide
      · injection h with hx hy; subst hx hy; decide
      · injection h with hx hy; subst hx hy; decide
      · injection h with hx hy; subst hx hy; decide
      · injection h with hx hy; subst hx hy; decide
      · injection h with hx hy; subst hx hy; decide
      · injection h with hx hy; subst hx hy; decide
      · injection h with hx hy; subst hx hy; decide
      · nomatch hf
    · dsimp; rw [← heq]; ext <;> dsimp <;> omega

theorem candidateCells_of_lifeRule (c : Coord) (alive : List Coord)
    (h_rule : lifeRule ((deduplicate alive).contains c) (countAliveNeighbors c (deduplicate alive)) = true) :
    c ∈ candidateCells (deduplicate alive) := by
  dsimp [lifeRule] at h_rule
  rw [Bool.or_eq_true] at h_rule
  dsimp [candidateCells]
  rw [mem_deduplicate_iff]
  rw [List.mem_append]
  rcases h_rule with h3 | h2
  · have h_count : countAliveNeighbors c (deduplicate alive) = 3 := by
      rw [beq_iff_eq] at h3; exact h3
    dsimp [countAliveNeighbors] at h_count
    cases h_list : (mooreNeighbors c).filter (fun n => (deduplicate alive).contains n) with
    | nil =>
      rw [h_list] at h_count
      contradiction
    | cons p ps =>
      have hp_in : p ∈ (mooreNeighbors c).filter (fun n => (deduplicate alive).contains n) := by
        rw [h_list]; exact List.Mem.head ps
      rw [List.mem_filter] at hp_in
      rcases hp_in with ⟨hp_nbr, hp_alive⟩
      rw [List.contains_iff_mem] at hp_alive
      right
      rw [List.mem_flatMap]
      refine ⟨p, hp_alive, ?_⟩
      rw [mem_mooreNeighbors_symm]
      exact hp_nbr
  · rw [Bool.and_eq_true] at h2
    have hc_alive : (deduplicate alive).contains c = true := h2.2
    rw [List.contains_iff_mem] at hc_alive
    left
    exact hc_alive

theorem mem_stepGrid_iff (c : Coord) (alive : List Coord) :
    c ∈ stepGrid alive ↔
    lifeRule ((deduplicate alive).contains c) (countAliveNeighbors c (deduplicate alive)) = true := by
  dsimp [stepGrid]
  rw [List.mem_filter]
  constructor
  · intro ⟨_, h_rule⟩; exact h_rule
  · intro h_rule; refine ⟨candidateCells_of_lifeRule c alive h_rule, h_rule⟩

theorem non_candidate_dead_sg (alive : List Coord) (c : Coord)
    (h_not_cand : ¬ c ∈ candidateCells (deduplicate alive)) :
    ¬ c ∈ stepGrid alive := by
  intro h_in
  dsimp [stepGrid] at h_in
  rw [List.mem_filter] at h_in
  exact h_not_cand h_in.1

theorem not_mem_candidateCells_of_chebyshevDist_gt_one
    (alive : List Coord) (c : Coord)
    (h_dist : ∀ p ∈ deduplicate alive, chebyshevDist c p > 1) :
    ¬ c ∈ candidateCells (deduplicate alive) := by
  intro h_cand
  dsimp [candidateCells] at h_cand
  rw [mem_deduplicate_iff] at h_cand
  rw [List.mem_append] at h_cand
  rcases h_cand with h_self | h_nbr
  · have h0 := h_dist c h_self
    dsimp [chebyshevDist] at h0
    omega
  · rw [List.mem_flatMap] at h_nbr
    rcases h_nbr with ⟨p, hp, hcp⟩
    have hd := h_dist p hp
    dsimp [mooreNeighbors] at hcp
    rw [List.mem_map] at hcp
    rcases hcp with ⟨⟨dx, dy⟩, hoff, heq⟩
    have hcheb := mooreOffsets_chebyshevDist (dx, dy) hoff
    rw [← heq] at hd
    dsimp [chebyshevDist] at hd
    have hx : p.1 + dx - p.1 = dx := by omega
    have hy : p.2 + dy - p.2 = dy := by omega
    rw [hx, hy] at hd
    omega

end Algorithm
