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

local notation "ℕ" => Nat
local notation "ℤ" => Int

namespace Algorithm

-- =========================================================================
-- Layer 3: Speed of Light & Boundary Confinement
-- =========================================================================

theorem emptyGrid_step_empty :
    stepGrid [] = [] :=
  stepGrid_empty

theorem speed_of_light_chebyshev (dx dy : ℤ) (hx : dx.natAbs ≤ 1) (hy : dy.natAbs ≤ 1) :
    max dx.natAbs dy.natAbs ≤ 1 := by
  omega

theorem mooreOffsets_chebyshevDist (off : Coord) (hoff : off ∈ mooreOffsets) :
    max off.1.natAbs off.2.natAbs ≤ 1 := by
  simp only [mooreOffsets, List.mem_cons, List.not_mem_nil] at hoff
  rcases hoff with rfl | rfl | rfl | rfl | rfl | rfl | rfl | (rfl | hfalse)
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · nomatch hfalse

theorem expandCentered_confinement_bound (nw ne sw se : MacroCell) :
    macroCellSize (centeredSubSubnode (expandCentered (makeCellNode nw ne sw se))) =
    macroCellSize (expandCentered (makeCellNode nw ne sw se)) :=
  expandCentered_confinement_Impl nw ne sw se

theorem expandOffsetDelta_neg_three_mul (k : ℕ) :
    expandOffsetDelta (k + 1) = -3 * (2 : ℤ) ^ k :=
  expandOffsetDelta_succ_Impl k

theorem stepOffsetDelta_pow_two (k : ℕ) :
    stepOffsetDelta (k + 2) = (2 : ℤ) ^ k :=
  stepOffsetDelta_succ_Impl k

end Algorithm
