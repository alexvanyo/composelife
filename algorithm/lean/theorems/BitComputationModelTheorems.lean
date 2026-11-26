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

import Algorithm.BitComputation
import AlgorithmDefs
import models.BitComputationModel
import proofs.BitComputationModelProofs

local notation "ℕ" => Nat
local notation "ℤ" => Int

namespace Algorithm.KotlinModel

/-!
# Formal Theorems About Hand-Written `BitComputation.kt` Model

Mathematical properties proved about `computeQuadInfoModel` and
`computeNextGenerationPureKotlinModel` (defined in `models/BitComputationModel.lean`),
without using Lean codegen as source of truth.
-/

/-- `computeQuadInfoModel` packs all six overlapping sub-quadrant slices into bits `0..23` with bits `24..31` zero. -/
theorem computeQuadInfoModel_bitSpec (q : UInt32) :
    (computeQuadInfoModel q &&& (0xF : UInt32) = Algorithm.extractCenterUInt q) ∧
    (((computeQuadInfoModel q >>> 4) &&& (0x5 : UInt32)) =
      (((q >>> 7) &&& (1 : UInt32)) ||| (((q >>> 13) &&& (1 : UInt32)) <<< 2))) ∧
    (((computeQuadInfoModel q >>> 8) &&& (0xA : UInt32)) =
      ((((q >>> 2) &&& (1 : UInt32)) <<< 1) ||| (((q >>> 8) &&& (1 : UInt32)) <<< 3))) ∧
    (((computeQuadInfoModel q >>> 12) &&& (0x3 : UInt32)) =
      (((q >>> 11) &&& (1 : UInt32)) ||| (((q >>> 14) &&& (1 : UInt32)) <<< 1))) ∧
    (((computeQuadInfoModel q >>> 16) &&& (0xC : UInt32)) =
      ((((q >>> 1) &&& (1 : UInt32)) <<< 2) ||| (((q >>> 4) &&& (1 : UInt32)) <<< 3))) ∧
    ((computeQuadInfoModel q >>> 20) &&& (0xF : UInt32) =
      (((q >>> 15) &&& (1 : UInt32)) ||| (((q >>> 10) &&& (1 : UInt32)) <<< 1) |||
        (((q >>> 5) &&& (1 : UInt32)) <<< 2) ||| ((q &&& (1 : UInt32)) <<< 3))) ∧
    computeQuadInfoModel q < 0x1000000 :=
  computeQuadInfoModel_bitSpec_Impl q

/-- For non-zero 8×8 leaves, the four 4×4 subgrid indices assembled from `QUAD_INFO_LUT` match `computeLeafNextGen8x8FastUInt`. -/
theorem pureKotlin_subgrids_eq (nextGenLut : UInt32 → UInt32) (w : UInt64) (hw : w ≠ 0) :
    computeNextGenerationPureKotlinModelWith nextGenLut w =
      let nw := nextGenLut (Algorithm.extractCenterUInt (Algorithm.quad0UInt w) |||
        (Algorithm.extractHorizontalMidUInt (Algorithm.quad0UInt w) (Algorithm.quad1UInt w) <<< 4) |||
        (Algorithm.extractVerticalMidUInt (Algorithm.quad0UInt w) (Algorithm.quad2UInt w) <<< 8) |||
        (Algorithm.extractCenterMidUInt (Algorithm.quad0UInt w) (Algorithm.quad1UInt w)
          (Algorithm.quad2UInt w) (Algorithm.quad3UInt w) <<< 12))
      let ne := nextGenLut (Algorithm.extractHorizontalMidUInt (Algorithm.quad0UInt w) (Algorithm.quad1UInt w) |||
        (Algorithm.extractCenterUInt (Algorithm.quad1UInt w) <<< 4) |||
        (Algorithm.extractCenterMidUInt (Algorithm.quad0UInt w) (Algorithm.quad1UInt w)
          (Algorithm.quad2UInt w) (Algorithm.quad3UInt w) <<< 8) |||
        (Algorithm.extractVerticalMidUInt (Algorithm.quad1UInt w) (Algorithm.quad3UInt w) <<< 12))
      let sw := nextGenLut (Algorithm.extractVerticalMidUInt (Algorithm.quad0UInt w) (Algorithm.quad2UInt w) |||
        (Algorithm.extractCenterMidUInt (Algorithm.quad0UInt w) (Algorithm.quad1UInt w)
          (Algorithm.quad2UInt w) (Algorithm.quad3UInt w) <<< 4) |||
        (Algorithm.extractCenterUInt (Algorithm.quad2UInt w) <<< 8) |||
        (Algorithm.extractHorizontalMidUInt (Algorithm.quad2UInt w) (Algorithm.quad3UInt w) <<< 12))
      let se := nextGenLut (Algorithm.extractCenterMidUInt (Algorithm.quad0UInt w) (Algorithm.quad1UInt w)
          (Algorithm.quad2UInt w) (Algorithm.quad3UInt w) |||
        (Algorithm.extractVerticalMidUInt (Algorithm.quad1UInt w) (Algorithm.quad3UInt w) <<< 4) |||
        (Algorithm.extractHorizontalMidUInt (Algorithm.quad2UInt w) (Algorithm.quad3UInt w) <<< 8) |||
        (Algorithm.extractCenterUInt (Algorithm.quad3UInt w) <<< 12))
      nw ||| (ne <<< 4) ||| (sw <<< 8) ||| (se <<< 12) :=
  pureKotlin_subgrids_eq_Impl nextGenLut w hw

/-- The pure Kotlin LUT model computes identically to `Algorithm.computeLeafNextGen8x8FastUInt` on all `UInt64` leaves. -/
theorem computeNextGenerationPureKotlinModel_eq_fast (w : UInt64) :
    computeNextGenerationPureKotlinModel w = Algorithm.computeLeafNextGen8x8FastUInt w :=
  computeNextGenerationPureKotlinModel_eq_fast_Impl w

/-- Main correctness theorem: each output bit `0..15` matches exact Conway's Game of Life at `2 ≤ x < 6, 2 ≤ y < 6`. -/
theorem computeNextGenerationPureKotlinModel_correct (w : UInt64) (x y : ℤ)
    (hx : 2 ≤ x ∧ x < 6) (hy : 2 ≤ y ∧ y < 6) :
    (computeNextGenerationPureKotlinModel w).toBitVec.getLsbD (mortonIndex4 (x - 2).toNat (y - 2).toNat) =
      nextGenAt (leafAt w) x y :=
  computeNextGenerationPureKotlinModel_correct_Impl w x y hx hy

/-- Fixed-point invariant: the empty 8×8 leaf maps to the empty 4×4 center (`0`). -/
theorem computeNextGenerationPureKotlinModel_zero :
    computeNextGenerationPureKotlinModel 0 = 0 :=
  computeNextGenerationPureKotlinModel_zero_Impl

/-- Range invariant: only bits `0..15` can be set in the output. -/
theorem computeNextGenerationPureKotlinModel_lt_65536 (w : UInt64) :
    (computeNextGenerationPureKotlinModel w).toNat < 65536 :=
  computeNextGenerationPureKotlinModel_lt_65536_Impl w

/-- Outer-corner independence: toggling `(0,0), (7,0), (0,7), (7,7)` never alters the next generation. -/
theorem computeNextGenerationPureKotlinModel_corner_indep (w c : UInt64)
    (hc : c &&& ~~~outerCornerMask = 0) :
    computeNextGenerationPureKotlinModel (w ^^^ c) = computeNextGenerationPureKotlinModel w :=
  computeNextGenerationPureKotlinModel_corner_indep_Impl w c hc

end Algorithm.KotlinModel
