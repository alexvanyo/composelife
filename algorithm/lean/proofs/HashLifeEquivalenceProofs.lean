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
import Algorithm.BitComputation
import Algorithm.MacroCell
import Algorithm.HashLife
import AlgorithmDefs
import proofs.HashLifeProofs
import proofs.ConfinementProofs
import proofs.GridEquivalenceProofs
import proofs.HashLifeSingleStepProofs

local notation "ℕ" => Nat
local notation "ℤ" => Int

namespace Algorithm

-- =========================================================================
-- Universal Master Equivalence Theorems (Single-Step & N-Step)
-- =========================================================================

theorem hashlife_single_step_soundness
    (st : HashLifeCellState)
    (h_wf : isWellFormed st.macroCell)
    (h_depth : st.macroCell.depth ≤ 30)
    (c : Coord)
    (h_hl : c ∈ hashLifeToGrid (hashLifeNextGeneration st)) :
    c ∈ stepGrid (hashLifeToGrid st) :=
  ((hashLifeNextGeneration_correct st h_wf h_depth).2.2 c).mp h_hl

theorem hashlife_single_step_completeness
    (st : HashLifeCellState)
    (h_wf : isWellFormed st.macroCell)
    (h_depth : st.macroCell.depth ≤ 30)
    (c : Coord)
    (h_sg : c ∈ stepGrid (hashLifeToGrid st)) :
    c ∈ hashLifeToGrid (hashLifeNextGeneration st) :=
  ((hashLifeNextGeneration_correct st h_wf h_depth).2.2 c).mpr h_sg

theorem hashlife_single_step_equivalence_Impl
    (st : HashLifeCellState)
    (h_wf : isWellFormed st.macroCell)
    (h_depth : st.macroCell.depth ≤ 30) :
    cellsEqual
      (hashLifeToGrid (hashLifeNextGeneration st))
      (stepGrid (hashLifeToGrid st)) = true := by
  apply cellsEqual_of_same_elements
  intro c
  constructor
  · exact hashlife_single_step_soundness st h_wf h_depth c
  · exact hashlife_single_step_completeness st h_wf h_depth c

theorem hashlife_n_step_equivalence_aux
    (n : ℕ)
    (st : HashLifeCellState)
    (h_ok : ∀ k ≤ n, isWellFormed (hashLifeStepN k st).macroCell ∧ (hashLifeStepN k st).macroCell.depth ≤ 30) :
    cellsEqual
      (hashLifeToGrid (hashLifeStepN n st))
      (stepN n (hashLifeToGrid st)) = true := by
  induction n generalizing st with
  | zero =>
    dsimp [hashLifeStepN, stepN]
    exact cellsEqual_deduplicate_self (hashLifeToGrid st)
  | succ n ih =>
    dsimp [hashLifeStepN]
    have h0 := h_ok 0 (by omega)
    have h_single := hashlife_single_step_equivalence_Impl st h0.1 h0.2
    have h_stepN_single := stepN_cellsEqual_stepN n h_single
    have h_trans2 := stepN_stepGrid_cellsEqual n (hashLifeToGrid st)
    have h_ok_next : ∀ k ≤ n, isWellFormed (hashLifeStepN k (hashLifeNextGeneration st)).macroCell ∧
        (hashLifeStepN k (hashLifeNextGeneration st)).macroCell.depth ≤ 30 := by
      intro k hk
      exact h_ok (k + 1) (by omega)
    have ih_next := ih (hashLifeNextGeneration st) h_ok_next
    exact cellsEqual_trans (cellsEqual_trans ih_next h_stepN_single) h_trans2

theorem hashLifeStepN_succ_eq (k : ℕ) (st : HashLifeCellState) :
    hashLifeStepN (k + 1) st = hashLifeNextGeneration (hashLifeStepN k st) := by
  induction k generalizing st with
  | zero => rfl
  | succ k ih =>
    show hashLifeStepN (k + 1) (hashLifeNextGeneration st) = _
    rw [ih]
    rfl

/--
Along `n` generations from a well-formed state of depth `d` with `d + n ≤ 30`, every state is well-formed and
the depth after `k` generations is at most `d + k`.
-/
theorem hashLifeStepN_wf_depth (n : ℕ) (st : HashLifeCellState) (h_wf : isWellFormed st.macroCell)
    (h_depth : st.macroCell.depth + n ≤ 30) :
    ∀ k ≤ n, isWellFormed (hashLifeStepN k st).macroCell ∧
      (hashLifeStepN k st).macroCell.depth ≤ st.macroCell.depth + k := by
  intro k hk
  induction k with
  | zero => exact ⟨h_wf, by simp [hashLifeStepN]⟩
  | succ k ih =>
    obtain ⟨hw, hd⟩ := ih (by omega)
    rw [hashLifeStepN_succ_eq]
    obtain ⟨hw', hd', _⟩ := hashLifeNextGeneration_correct _ hw (by omega)
    exact ⟨hw', by omega⟩

theorem hashlife_n_step_equivalence_Impl
    (n : ℕ)
    (st : HashLifeCellState)
    (h_wf : isWellFormed st.macroCell)
    (h_depth : st.macroCell.depth + n ≤ 30) :
    cellsEqual
      (hashLifeToGrid (hashLifeStepN n st))
      (stepN n (hashLifeToGrid st)) = true := by
  apply hashlife_n_step_equivalence_aux n st
  intro k hk
  obtain ⟨hw, hd⟩ := hashLifeStepN_wf_depth n st h_wf h_depth k hk
  exact ⟨hw, by omega⟩

end Algorithm
