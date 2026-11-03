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
-- Master Universal HashLife Equivalence Theorems
-- =========================================================================

/--
Master Universal HashLife Single-Step Equivalence Theorem:
For any well-formed MacroCell of depth at most 30 (so that its population fits in the `UInt64` counts
that `needToExpand` compares), at any offset, HashLife stepping and canonical Naive Game of Life grid
stepping produce identically equal cell configurations under coordinate set equality.
-/
theorem hashlife_single_step_equivalence
    (st : HashLifeCellState)
    (h_wf : isWellFormed st.macroCell)
    (h_depth : st.macroCell.depth ≤ 30) :
    cellsEqual
      (hashLifeToGrid (hashLifeNextGeneration st))
      (stepGrid (hashLifeToGrid st)) = true :=
  hashlife_single_step_equivalence_Impl st h_wf h_depth

/--
Master Universal HashLife N-Step Multi-Generation Equivalence Theorem:
For any number of generations `n` and any well-formed MacroCell of depth `d` with `d + n ≤ 30`, at any
offset, `n` generations of HashLife stepping and `n` generations of canonical Naive Game of Life grid
stepping produce identically equal cell configurations under coordinate set equality. (Each generation
grows the depth by at most one, so the hypothesis only constrains the input.)
-/
theorem hashlife_n_step_equivalence
    (n : ℕ)
    (st : HashLifeCellState)
    (h_wf : isWellFormed st.macroCell)
    (h_depth : st.macroCell.depth + n ≤ 30) :
    cellsEqual
      (hashLifeToGrid (hashLifeStepN n st))
      (stepN n (hashLifeToGrid st)) = true :=
  hashlife_n_step_equivalence_Impl n st h_wf h_depth

end Algorithm

