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
import Algorithm.HashLifeEquivalence
import AlgorithmDefs
import proofs.HashLifeProofs
import proofs.BitComputationProofs
import proofs.SpatialTilingProofs
import proofs.ConfinementProofs
import proofs.BitEquivalenceProofs
import proofs.GridEquivalenceProofs
import proofs.HashLifeSingleStepProofs

local notation "ℕ" => Nat
local notation "ℤ" => Int

namespace Algorithm

-- =========================================================================
-- Empty Grid and Inductive Base Cases
-- =========================================================================

theorem cellsEqual_empty_empty :
    cellsEqual [] [] = true := by
  decide

/--
Empty Universe Equivalence:
For any empty quadtree of level k + 5 and arbitrary integer offsets (ox, oy),
HashLife stepping and canonical Naive Game of Life grid stepping produce
identically empty cell configurations.
-/
theorem hashlife_step_equivalence_emptyNode_Impl (k : ℕ) (ox oy : ℤ) :
    cellsEqual
      (hashLifeToGrid (hashLifeNextGenerationStep { offset := (ox, oy), macroCell := emptyNode (k + 5) }))
      (stepGrid (hashLifeToGrid { offset := (ox, oy), macroCell := emptyNode (k + 5) })) = true := by
  rw [hashlife_step_equivalence_empty_Impl k ox oy]
  exact cellsEqual_refl _

-- =========================================================================
-- Canonical Pattern Soundness Bridges
-- =========================================================================

theorem hashlife_block_equivalence_Impl :
    let nw := makeLevel1 false false false true
    let ne := makeLevel1 false false true false
    let sw := makeLevel1 false true false false
    let se := makeLevel1 true false false false
    let block4x4 := makeLevel2 nw ne sw se
    let grid := microCellToGrid 0 0 block4x4
    let classicalStep := central2x2Window (stepGrid grid)
    let hashLifeResult := microCellToGrid 1 1 (hashLifeStepLevel2 block4x4)
    cellsEqual classicalStep hashLifeResult = true :=
  hashlife_step_soundness_block_Impl

theorem hashlife_blinker_equivalence_Impl :
    let nw := makeLevel1 false false false true
    let ne := makeLevel1 false false true true
    let sw := makeLevel1 false false false false
    let se := makeLevel1 false false false false
    let blinker4x4 := makeLevel2 nw ne sw se
    let grid := microCellToGrid 0 0 blinker4x4
    let classicalStep := central2x2Window (stepGrid grid)
    let hashLifeResult := microCellToGrid 1 1 (hashLifeStepLevel2 blinker4x4)
    cellsEqual classicalStep hashLifeResult = true :=
  hashlife_step_soundness_blinker_Impl

theorem hashlife_tub_equivalence_Impl :
    let nw := makeLevel1 false true true false
    let ne := makeLevel1 false false true false
    let sw := makeLevel1 false true false false
    let se := makeLevel1 false false false false
    let tub4x4 := makeLevel2 nw ne sw se
    let grid := microCellToGrid 0 0 tub4x4
    let classicalStep := central2x2Window (stepGrid grid)
    let hashLifeResult := microCellToGrid 1 1 (hashLifeStepLevel2 tub4x4)
    cellsEqual classicalStep hashLifeResult = true :=
  hashlife_step_soundness_tub_Impl

theorem hashlife_boat_equivalence_Impl :
    let nw := makeLevel1 false false false true
    let ne := makeLevel1 false false true false
    let sw := makeLevel1 false true false false
    let se := makeLevel1 false true true false
    let boat4x4 := makeLevel2 nw ne sw se
    let grid := microCellToGrid 0 0 boat4x4
    let classicalStep := central2x2Window (stepGrid grid)
    let hashLifeResult := microCellToGrid 1 1 (hashLifeStepLevel2 boat4x4)
    cellsEqual classicalStep hashLifeResult = true :=
  hashlife_step_soundness_boat_Impl

theorem hashlife_glider_equivalence_Impl :
    let nw := makeLevel1 false false false true
    let ne := makeLevel1 false false true false
    let sw := makeLevel1 false false false false
    let se := makeLevel1 true true true false
    let glider4x4 := makeLevel2 nw ne sw se
    let grid := microCellToGrid 0 0 glider4x4
    let classicalStep := central2x2Window (stepGrid grid)
    let hashLifeResult := microCellToGrid 1 1 (hashLifeStepLevel2 glider4x4)
    cellsEqual classicalStep hashLifeResult = true :=
  hashlife_step_soundness_glider_Impl

-- =========================================================================
-- Universal Master Equivalence Theorems (Single-Step & N-Step)
-- =========================================================================

theorem isWellFormed_makeLevel4Node (nw ne sw se : UInt64) :
    isWellFormed (makeLevel4Node nw ne sw se) :=
  trivial

theorem hashlife_single_step_soundness
    (st : HashLifeCellState)
    (h_wf : isWellFormed st.macroCell)
    (h_bounds : isInInt32Bounds st)
    (c : Coord)
    (h_hl : c ∈ hashLifeToGrid (hashLifeNextGeneration st)) :
    c ∈ stepGrid (hashLifeToGrid st) :=
  ((hashLifeNextGeneration_correct st h_wf h_bounds).2 c).mp h_hl

theorem hashlife_single_step_completeness
    (st : HashLifeCellState)
    (h_wf : isWellFormed st.macroCell)
    (h_bounds : isInInt32Bounds st)
    (c : Coord)
    (h_sg : c ∈ stepGrid (hashLifeToGrid st)) :
    c ∈ hashLifeToGrid (hashLifeNextGeneration st) :=
  ((hashLifeNextGeneration_correct st h_wf h_bounds).2 c).mpr h_sg

theorem hashlife_single_step_equivalence_Impl
    (st : HashLifeCellState)
    (h_wf : isWellFormed st.macroCell)
    (h_bounds : isInInt32Bounds st) :
    cellsEqual
      (hashLifeToGrid (hashLifeNextGeneration st))
      (stepGrid (hashLifeToGrid st)) = true := by
  apply cellsEqual_of_same_elements
  intro c
  constructor
  · exact hashlife_single_step_soundness st h_wf h_bounds c
  · exact hashlife_single_step_completeness st h_wf h_bounds c

theorem hashlife_n_step_equivalence_aux
    (n : ℕ)
    (st : HashLifeCellState)
    (h_wf : ∀ k ≤ n, isWellFormed (hashLifeStepN k st).macroCell)
    (h_bounds : isInInt32BoundsN n st) :
    cellsEqual
      (hashLifeToGrid (hashLifeStepN n st))
      (stepN n (hashLifeToGrid st)) = true := by
  induction n generalizing st with
  | zero =>
    dsimp [hashLifeStepN, stepN]
    exact cellsEqual_deduplicate_self (hashLifeToGrid st)
  | succ n ih =>
    dsimp [hashLifeStepN]
    have h_single := hashlife_single_step_equivalence_Impl st (h_wf 0 (by omega)) (h_bounds 0 (by omega))
    have h_stepN_single := stepN_cellsEqual_stepN n h_single
    have h_trans2 := stepN_stepGrid_cellsEqual n (hashLifeToGrid st)
    have h_bounds_next : isInInt32BoundsN n (hashLifeNextGeneration st) := by
      intro k hk
      have : k + 1 ≤ n + 1 := by omega
      have hst := h_bounds (k + 1) this
      dsimp [hashLifeStepN] at hst
      exact hst
    have h_wf_next : ∀ k ≤ n, isWellFormed (hashLifeStepN k (hashLifeNextGeneration st)).macroCell := by
      intro k hk
      have : k + 1 ≤ n + 1 := by omega
      have hst := h_wf (k + 1) this
      dsimp [hashLifeStepN] at hst
      exact hst
    have ih_next := ih (hashLifeNextGeneration st) h_wf_next h_bounds_next
    exact cellsEqual_trans (cellsEqual_trans ih_next h_stepN_single) h_trans2

theorem hashLifeStepN_succ_eq (k : ℕ) (st : HashLifeCellState) :
    hashLifeStepN (k + 1) st = hashLifeNextGeneration (hashLifeStepN k st) := by
  induction k generalizing st with
  | zero => rfl
  | succ k ih =>
    show hashLifeStepN (k + 1) (hashLifeNextGeneration st) = _
    rw [ih]
    rfl

theorem hashlife_n_step_equivalence_Impl
    (n : ℕ)
    (st : HashLifeCellState)
    (h_wf : isWellFormed st.macroCell)
    (h_bounds : isInInt32BoundsN n st) :
    cellsEqual
      (hashLifeToGrid (hashLifeStepN n st))
      (stepN n (hashLifeToGrid st)) = true := by
  have h_wf_all : ∀ k ≤ n, isWellFormed (hashLifeStepN k st).macroCell := by
    intro k hk
    induction k with
    | zero => exact h_wf
    | succ k ih =>
      rw [hashLifeStepN_succ_eq]
      exact (hashLifeNextGeneration_correct _ (ih (by omega)) (h_bounds k (by omega))).1
  exact hashlife_n_step_equivalence_aux n st h_wf_all h_bounds

end Algorithm

