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
import proofs.HashLifeEquivalenceProofs

local notation "ℕ" => Nat
local notation "ℤ" => Int

namespace Algorithm

-- =========================================================================
-- Coordinate Set Equality Infrastructure
-- =========================================================================

theorem mem_deduplicate_iff_thm [DecidableEq α] (x : α) (xs : List α) :
    x ∈ deduplicate xs ↔ x ∈ xs :=
  mem_deduplicate_iff x xs

theorem cellsEqual_of_same_elements_thm (a b : List Coord)
    (h : ∀ c, c ∈ a ↔ c ∈ b) :
    cellsEqual a b = true :=
  cellsEqual_of_same_elements a b h

theorem cellsEqual_refl_thm (xs : List Coord) :
    cellsEqual xs xs = true :=
  cellsEqual_refl xs

theorem cellsEqual_deduplicate_self_thm (xs : List Coord) :
    cellsEqual xs (deduplicate xs) = true :=
  cellsEqual_deduplicate_self xs

theorem cellsEqual_symm_thm {a b : List Coord}
    (h : cellsEqual a b = true) : cellsEqual b a = true :=
  cellsEqual_symm h

theorem stepGrid_deduplicate_thm (s : List Coord) :
    stepGrid (deduplicate s) = stepGrid s :=
  stepGrid_deduplicate s

-- =========================================================================
-- Empty Universe Equivalence Theorem
-- =========================================================================

/--
Empty Universe Equivalence Theorem:
For any empty quadtree of level k + 5 and arbitrary integer offsets (ox, oy),
HashLife stepping and canonical Naive Game of Life grid stepping produce
identically empty cell configurations under coordinate set equality.
-/
theorem hashlife_step_equivalence_emptyNode (k : ℕ) (ox oy : ℤ) :
    cellsEqual
      (hashLifeToGrid (hashLifeNextGenerationStep { offset := (ox, oy), macroCell := emptyNode (k + 5) }))
      (stepGrid (hashLifeToGrid { offset := (ox, oy), macroCell := emptyNode (k + 5) })) = true :=
  hashlife_step_equivalence_emptyNode_Impl k ox oy

-- =========================================================================
-- Canonical Pattern Equivalence Theorems
-- =========================================================================

/--
Block Pattern Equivalence:
HashLife stepping matches naive Conway stepping on a 2x2 block.
-/
theorem hashlife_block_equivalence :
    let nw := makeLevel1 false false false true
    let ne := makeLevel1 false false true false
    let sw := makeLevel1 false true false false
    let se := makeLevel1 true false false false
    let block4x4 := makeLevel2 nw ne sw se
    let grid := microCellToGrid 0 0 block4x4
    let classicalStep := central2x2Window (stepGrid grid)
    let hashLifeResult := microCellToGrid 1 1 (hashLifeStepLevel2 block4x4)
    cellsEqual classicalStep hashLifeResult = true :=
  hashlife_block_equivalence_Impl

/--
Blinker Pattern Equivalence:
HashLife stepping matches naive Conway stepping on an oscillator (blinker).
-/
theorem hashlife_blinker_equivalence :
    let nw := makeLevel1 false false false true
    let ne := makeLevel1 false false true true
    let sw := makeLevel1 false false false false
    let se := makeLevel1 false false false false
    let blinker4x4 := makeLevel2 nw ne sw se
    let grid := microCellToGrid 0 0 blinker4x4
    let classicalStep := central2x2Window (stepGrid grid)
    let hashLifeResult := microCellToGrid 1 1 (hashLifeStepLevel2 blinker4x4)
    cellsEqual classicalStep hashLifeResult = true :=
  hashlife_blinker_equivalence_Impl

/--
Tub Pattern Equivalence:
HashLife stepping matches naive Conway stepping on a tub still life.
-/
theorem hashlife_tub_equivalence :
    let nw := makeLevel1 false true true false
    let ne := makeLevel1 false false true false
    let sw := makeLevel1 false true false false
    let se := makeLevel1 false false false false
    let tub4x4 := makeLevel2 nw ne sw se
    let grid := microCellToGrid 0 0 tub4x4
    let classicalStep := central2x2Window (stepGrid grid)
    let hashLifeResult := microCellToGrid 1 1 (hashLifeStepLevel2 tub4x4)
    cellsEqual classicalStep hashLifeResult = true :=
  hashlife_tub_equivalence_Impl

/--
Boat Pattern Equivalence:
HashLife stepping matches naive Conway stepping on a boat still life.
-/
theorem hashlife_boat_equivalence :
    let nw := makeLevel1 false false false true
    let ne := makeLevel1 false false true false
    let sw := makeLevel1 false true false false
    let se := makeLevel1 false true true false
    let boat4x4 := makeLevel2 nw ne sw se
    let grid := microCellToGrid 0 0 boat4x4
    let classicalStep := central2x2Window (stepGrid grid)
    let hashLifeResult := microCellToGrid 1 1 (hashLifeStepLevel2 boat4x4)
    cellsEqual classicalStep hashLifeResult = true :=
  hashlife_boat_equivalence_Impl

/--
Glider Pattern Equivalence:
HashLife stepping matches naive Conway stepping on a glider spaceship.
-/
theorem hashlife_glider_equivalence :
    let nw := makeLevel1 false false false true
    let ne := makeLevel1 false false true false
    let sw := makeLevel1 false false false false
    let se := makeLevel1 true true true false
    let glider4x4 := makeLevel2 nw ne sw se
    let grid := microCellToGrid 0 0 glider4x4
    let classicalStep := central2x2Window (stepGrid grid)
    let hashLifeResult := microCellToGrid 1 1 (hashLifeStepLevel2 glider4x4)
    cellsEqual classicalStep hashLifeResult = true :=
  hashlife_glider_equivalence_Impl

-- =========================================================================
-- Master Universal HashLife Equivalence Theorems
-- =========================================================================

/--
Master Universal HashLife Single-Step Equivalence Theorem:
For any well-formed MacroCell configuration representable within standard signed 32-bit
integer coordinate bounds, HashLife stepping and canonical Naive Game of Life grid stepping
produce identically equal cell configurations under coordinate set equality.
-/
theorem hashlife_single_step_equivalence
    (st : HashLifeCellState)
    (h_wf : isWellFormed st.macroCell)
    (h_bounds : isInInt32Bounds st) :
    cellsEqual
      (hashLifeToGrid (hashLifeNextGeneration st))
      (stepGrid (hashLifeToGrid st)) = true :=
  hashlife_single_step_equivalence_Impl st h_wf h_bounds

/--
Master Universal HashLife N-Step Multi-Generation Equivalence Theorem:
For any number of generations n and any well-formed MacroCell configuration whose trajectory
remains representable within standard signed 32-bit integer limits, n generations of HashLife
stepping and n generations of canonical Naive Game of Life grid stepping produce identically
equal cell configurations under coordinate set equality.
-/
theorem hashlife_n_step_equivalence
    (n : ℕ)
    (st : HashLifeCellState)
    (h_wf : isWellFormed st.macroCell)
    (h_bounds : isInInt32BoundsN n st) :
    cellsEqual
      (hashLifeToGrid (hashLifeStepN n st))
      (stepN n (hashLifeToGrid st)) = true :=
  hashlife_n_step_equivalence_Impl n st h_wf h_bounds

end Algorithm

