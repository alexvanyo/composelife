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

import AlgorithmDefs
import models.GameOfLifeStepModel

namespace Algorithm.KotlinModel

private theorem mem_dedupCoords_aux (acc xs : List (Int32 × Int32)) (x : Int32 × Int32) :
    x ∈ xs.foldl (fun a y => if a.contains y then a else a ++ [y]) acc ↔ x ∈ acc ∨ x ∈ xs := by
  induction xs generalizing acc with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldl]
    rw [ih]
    by_cases hy : y ∈ acc
    · simp only [List.contains_iff_mem, hy, ↓reduceIte, List.mem_cons]
      grind
    · simp only [List.contains_iff_mem, hy, ↓reduceIte, List.mem_cons, List.mem_append]
      grind

private theorem mem_dedupCoords (xs : List (Int32 × Int32)) (x : Int32 × Int32) :
    x ∈ dedupCoords xs ↔ x ∈ xs := by
  dsimp only [dedupCoords]
  rw [mem_dedupCoords_aux [] xs x]
  simp

private theorem int32_add_neg_pair (x a b : Int32) (h : a + b = 0) : (x + a) + b = x := by
  rw [Int32.add_assoc, h, Int32.add_zero]

private theorem mooreNeighbors_symm {p q : Int32 × Int32} :
    p ∈ mooreNeighbors32 q ↔ q ∈ mooreNeighbors32 p := by
  have symmAux : ∀ {u v : Int32 × Int32}, u ∈ mooreNeighbors32 v → v ∈ mooreNeighbors32 u := by
    intro ⟨u1, u2⟩ ⟨v1, v2⟩ hu
    dsimp only [mooreNeighbors32, mooreDeltas32, addOffset32] at hu ⊢
    rw [List.mem_map] at hu ⊢
    rcases hu with ⟨⟨dx, dy⟩, hmem, heq⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h | h | h | h | h | h | h <;> cases h <;>
      rcases Prod.ext_iff.mp heq with ⟨rfl, rfl⟩
    · exact ⟨(1, 1), by simp, Prod.ext (int32_add_neg_pair _ _ _ (by decide)) (int32_add_neg_pair _ _ _ (by decide))⟩
    · exact ⟨(0, 1), by simp, Prod.ext (int32_add_neg_pair _ _ _ (by decide)) (int32_add_neg_pair _ _ _ (by decide))⟩
    · exact ⟨(-1, 1), by simp, Prod.ext (int32_add_neg_pair _ _ _ (by decide)) (int32_add_neg_pair _ _ _ (by decide))⟩
    · exact ⟨(1, 0), by simp, Prod.ext (int32_add_neg_pair _ _ _ (by decide)) (int32_add_neg_pair _ _ _ (by decide))⟩
    · exact ⟨(-1, 0), by simp, Prod.ext (int32_add_neg_pair _ _ _ (by decide)) (int32_add_neg_pair _ _ _ (by decide))⟩
    · exact ⟨(1, -1), by simp, Prod.ext (int32_add_neg_pair _ _ _ (by decide)) (int32_add_neg_pair _ _ _ (by decide))⟩
    · exact ⟨(0, -1), by simp, Prod.ext (int32_add_neg_pair _ _ _ (by decide)) (int32_add_neg_pair _ _ _ (by decide))⟩
    · exact ⟨(-1, -1), by simp, Prod.ext (int32_add_neg_pair _ _ _ (by decide)) (int32_add_neg_pair _ _ _ (by decide))⟩
  exact ⟨symmAux, symmAux⟩

theorem stepGenerationModel_candidate_sound_Impl (alive : List (Int32 × Int32)) (c : Int32 × Int32)
    (hc : c ∈ stepGenerationModel alive) :
    c ∈ alive ∨ ∃ p ∈ alive, c ∈ mooreNeighbors32 p := by
  dsimp only [stepGenerationModel] at hc
  rw [List.mem_filter] at hc
  rw [mem_dedupCoords, List.mem_append, List.mem_flatMap] at hc
  rcases hc.1 with ⟨p, hp, hcp⟩ | hcal
  · rw [mem_dedupCoords] at hp
    exact Or.inr ⟨p, hp, hcp⟩
  · rw [mem_dedupCoords] at hcal
    exact Or.inl hcal

theorem stepGenerationModel_conway_iff_Impl (alive : List (Int32 × Int32)) (c : Int32 × Int32) :
    c ∈ stepGenerationModel alive ↔
      neighborCountCoords alive c = 3 ∨
      (neighborCountCoords alive c = 2 ∧ c ∈ alive) := by
  dsimp only [stepGenerationModel, neighborCountCoords]
  rw [List.mem_filter, mem_dedupCoords, List.mem_append, List.mem_flatMap]
  simp only [mem_dedupCoords]
  constructor
  · rintro ⟨_, hrule⟩
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, List.contains_iff_mem,
      mem_dedupCoords] at hrule
    exact hrule
  · intro hrule
    refine ⟨?_, ?_⟩
    · rcases hrule with h3 | ⟨_, hmem⟩
      · have hne : ((mooreNeighbors32 c).filter fun n => (dedupCoords alive).contains n) ≠ [] := by
          intro hem
          rw [hem] at h3
          simp at h3
        rcases List.exists_mem_of_ne_nil _ hne with ⟨n, hn⟩
        rw [List.mem_filter, List.contains_iff_mem, mem_dedupCoords] at hn
        exact Or.inl ⟨n, hn.2, mooreNeighbors_symm.mp hn.1⟩
      · exact Or.inr hmem
    · simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, List.contains_iff_mem,
        mem_dedupCoords]
      exact hrule

theorem stepGenerationModel_empty_Impl :
    stepGenerationModel [] = [] := by
  decide

theorem stepGenerationsModel_nonpositive_Impl (alive : List (Int32 × Int32)) (step : Int32)
    (hs : step.toInt ≤ 0) :
    stepGenerationsModel alive step = alive := by
  simp only [stepGenerationsModel, hs, ↓reduceIte]

theorem stepGenerationsModel_succ_Impl (alive : List (Int32 × Int32)) (n : Nat) :
    stepGenerationsLoop (n + 1) alive = stepGenerationsLoop n (stepGenerationModel alive) :=
  rfl

theorem stepGenerationsModel_add_Impl (alive : List (Int32 × Int32)) (a b : Nat) :
    stepGenerationsLoop (a + b) alive = stepGenerationsLoop b (stepGenerationsLoop a alive) := by
  induction a generalizing alive with
  | zero => simp [stepGenerationsLoop]
  | succ k ih =>
    rw [show k + 1 + b = (k + b) + 1 by omega]
    dsimp only [stepGenerationsLoop]
    exact ih (stepGenerationModel alive)

theorem stepGenerationsModel_pos_Impl (alive : List (Int32 × Int32)) (step : Int32) (hs : 0 < step.toInt) :
    stepGenerationsModel alive step = stepGenerationsModel (stepGenerationModel alive) (step - 1) := by
  have hsub : (step - 1).toInt = step.toInt - 1 := by
    rw [Int32.toInt_sub_of_le step 1 (by decide) (Int32.le_iff_toInt_le.mpr (by
      rw [show (1 : Int32).toInt = 1 from rfl]; omega))]
    rfl
  unfold stepGenerationsModel
  simp only [show ¬ step.toInt ≤ 0 by omega, ↓reduceIte, hsub]
  rw [show step.toInt.toNat = (step.toInt - 1).toNat + 1 by omega]
  by_cases h1 : step.toInt - 1 ≤ 0
  · simp only [h1, ↓reduceIte, show (step.toInt - 1).toNat = 0 by omega]
    rfl
  · simp only [h1, ↓reduceIte]
    rfl

theorem stepGenerationModel_block_Impl :
    ∀ p, p ∈ stepGenerationModel [(0, 0), (1, 0), (0, 1), (1, 1)] ↔
      p ∈ ([(0, 0), (1, 0), (0, 1), (1, 1)] : List (Int32 × Int32)) := by
  have hsub : ∀ p ∈ stepGenerationModel [(0, 0), (1, 0), (0, 1), (1, 1)],
      p ∈ ([(0, 0), (1, 0), (0, 1), (1, 1)] : List (Int32 × Int32)) := by decide
  have h00 : (0, 0) ∈ stepGenerationModel [(0, 0), (1, 0), (0, 1), (1, 1)] := by decide
  have h10 : (1, 0) ∈ stepGenerationModel [(0, 0), (1, 0), (0, 1), (1, 1)] := by decide
  have h01 : (0, 1) ∈ stepGenerationModel [(0, 0), (1, 0), (0, 1), (1, 1)] := by decide
  have h11 : (1, 1) ∈ stepGenerationModel [(0, 0), (1, 0), (0, 1), (1, 1)] := by decide
  intro p
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · intro hp
    have := hsub p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    exact this
  · rintro (rfl | rfl | rfl | rfl)
    · exact h00
    · exact h10
    · exact h01
    · exact h11

theorem stepGenerationModel_blinker_period2_Impl :
    ∀ p, p ∈ stepGenerationsLoop 2 [(0, 1), (1, 1), (2, 1)] ↔
      p ∈ ([(0, 1), (1, 1), (2, 1)] : List (Int32 × Int32)) := by
  have hsub : ∀ p ∈ stepGenerationsLoop 2 [(0, 1), (1, 1), (2, 1)],
      p ∈ ([(0, 1), (1, 1), (2, 1)] : List (Int32 × Int32)) := by decide
  have h01 : (0, 1) ∈ stepGenerationsLoop 2 [(0, 1), (1, 1), (2, 1)] := by decide
  have h11 : (1, 1) ∈ stepGenerationsLoop 2 [(0, 1), (1, 1), (2, 1)] := by decide
  have h21 : (2, 1) ∈ stepGenerationsLoop 2 [(0, 1), (1, 1), (2, 1)] := by decide
  intro p
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · intro hp
    have := hsub p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    exact this
  · rintro (rfl | rfl | rfl)
    · exact h01
    · exact h11
    · exact h21

private theorem mooreOffsets_toInt32 :
    Algorithm.mooreOffsets.map (fun d => ((Int32.ofInt d.1, Int32.ofInt d.2) : Int32 × Int32)) = mooreDeltas32 := by
  decide

/-- `neighborCountCoords` is the Moore neighbor count of the shared Conway specification. -/
private theorem neighborCountCoords_eq_neighborCountAt (alive : List (Int32 × Int32)) (c : Int32 × Int32) :
    neighborCountCoords alive c =
      Algorithm.neighborCountAt (fun x y => decide ((Int32.ofInt x, Int32.ofInt y) ∈ alive)) c.1.toInt c.2.toInt := by
  unfold neighborCountCoords Algorithm.neighborCountAt mooreNeighbors32
  dsimp only
  rw [← mooreOffsets_toInt32, List.map_map, List.filter_map, List.length_map]
  congr 2
  funext d
  simp only [Function.comp_apply, addOffset32, Int32.ofInt_add, Int32.ofInt_toInt]
  rw [Bool.eq_iff_iff, List.contains_iff_mem, mem_dedupCoords, decide_eq_true_eq]

theorem mem_stepGenerationModel_iff_nextGenAt_Impl (alive : List (Int32 × Int32)) (c : Int32 × Int32) :
    c ∈ stepGenerationModel alive ↔
      Algorithm.nextGenAt (fun x y => decide ((Int32.ofInt x, Int32.ofInt y) ∈ alive)) c.1.toInt c.2.toInt = true := by
  rw [stepGenerationModel_conway_iff_Impl, neighborCountCoords_eq_neighborCountAt]
  simp only [Algorithm.nextGenAt, Algorithm.lifeRule, Int32.ofInt_toInt, Bool.or_eq_true,
    beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq]

end Algorithm.KotlinModel
