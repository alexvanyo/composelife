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

import Std.Tactic.BVDecide
import Algorithm.BitComputation
import AlgorithmDefs
import models.BitComputationModel
import theorems.BitComputationTheorems

local notation "ℕ" => Nat
local notation "ℤ" => Int

namespace Algorithm.KotlinModel

/-- Mask selecting only the four outer corners `(0,0), (7,0), (0,7), (7,7)` of an 8×8 Morton leaf. -/
def outerCornerMask : UInt64 :=
  ((1 : UInt64) <<< 0) ||| ((1 : UInt64) <<< 21) ||| ((1 : UInt64) <<< 42) ||| ((1 : UInt64) <<< 63)

theorem computeQuadInfoModel_center_Impl (q : UInt32) :
    computeQuadInfoModel q &&& (0xF : UInt32) = Algorithm.extractCenterUInt q := by
  unfold computeQuadInfoModel Algorithm.extractCenterUInt
  bv_check "lrat/BitComputationModelProofs.Algorithm.KotlinModel.computeQuadInfoModel_center_Impl.lrat"

theorem computeQuadInfoModel_right_Impl (q : UInt32) :
    ((computeQuadInfoModel q >>> 4) &&& (0x5 : UInt32)) =
      (((q >>> 7) &&& (1 : UInt32)) ||| (((q >>> 13) &&& (1 : UInt32)) <<< 2)) := by
  unfold computeQuadInfoModel
  bv_check "lrat/BitComputationModelProofs.Algorithm.KotlinModel.computeQuadInfoModel_right_Impl.lrat"

theorem computeQuadInfoModel_left_Impl (q : UInt32) :
    ((computeQuadInfoModel q >>> 8) &&& (0xA : UInt32)) =
      ((((q >>> 2) &&& (1 : UInt32)) <<< 1) ||| (((q >>> 8) &&& (1 : UInt32)) <<< 3)) := by
  unfold computeQuadInfoModel
  bv_check "lrat/BitComputationModelProofs.Algorithm.KotlinModel.computeQuadInfoModel_left_Impl.lrat"

theorem computeQuadInfoModel_bottom_Impl (q : UInt32) :
    ((computeQuadInfoModel q >>> 12) &&& (0x3 : UInt32)) =
      (((q >>> 11) &&& (1 : UInt32)) ||| (((q >>> 14) &&& (1 : UInt32)) <<< 1)) := by
  unfold computeQuadInfoModel
  bv_check "lrat/BitComputationModelProofs.Algorithm.KotlinModel.computeQuadInfoModel_bottom_Impl.lrat"

theorem computeQuadInfoModel_top_Impl (q : UInt32) :
    ((computeQuadInfoModel q >>> 16) &&& (0xC : UInt32)) =
      ((((q >>> 1) &&& (1 : UInt32)) <<< 2) ||| (((q >>> 4) &&& (1 : UInt32)) <<< 3)) := by
  unfold computeQuadInfoModel
  bv_check "lrat/BitComputationModelProofs.Algorithm.KotlinModel.computeQuadInfoModel_top_Impl.lrat"

theorem computeQuadInfoModel_corner_Impl (q : UInt32) :
    (computeQuadInfoModel q >>> 20) &&& (0xF : UInt32) =
      (((q >>> 15) &&& (1 : UInt32)) ||| (((q >>> 10) &&& (1 : UInt32)) <<< 1) |||
        (((q >>> 5) &&& (1 : UInt32)) <<< 2) ||| ((q &&& (1 : UInt32)) <<< 3)) := by
  unfold computeQuadInfoModel
  bv_check "lrat/BitComputationModelProofs.Algorithm.KotlinModel.computeQuadInfoModel_corner_Impl.lrat"

theorem computeQuadInfoModel_lt_Impl (q : UInt32) :
    computeQuadInfoModel q < 0x1000000 := by
  unfold computeQuadInfoModel
  bv_check "lrat/BitComputationModelProofs.Algorithm.KotlinModel.computeQuadInfoModel_lt_Impl.lrat"

theorem pk_nw_in_eq (w : UInt64) :
    let q0 : UInt32 := (w &&& (0xFFFF : UInt64)).toUInt32
    let q1 : UInt32 := ((w >>> 16) &&& (0xFFFF : UInt64)).toUInt32
    let q2 : UInt32 := ((w >>> 32) &&& (0xFFFF : UInt64)).toUInt32
    let q3 : UInt32 := (w >>> 48).toUInt32
    let info0 : UInt32 := computeQuadInfoModel q0
    let info1 : UInt32 := computeQuadInfoModel q1
    let info2 : UInt32 := computeQuadInfoModel q2
    let info3 : UInt32 := computeQuadInfoModel q3
    let n00 : UInt32 := info0 &&& (0xF : UInt32)
    let n01 : UInt32 := ((info0 >>> 4) &&& (0x5 : UInt32)) ||| ((info1 >>> 8) &&& (0xA : UInt32))
    let n10 : UInt32 := ((info0 >>> 12) &&& (0x3 : UInt32)) ||| ((info2 >>> 16) &&& (0xC : UInt32))
    let n11 : UInt32 := ((info0 >>> 20) &&& (1 : UInt32)) ||| ((info1 >>> 20) &&& (2 : UInt32)) |||
      ((info2 >>> 20) &&& (4 : UInt32)) ||| ((info3 >>> 20) &&& (8 : UInt32))
    (n00 ||| (n01 <<< 4) ||| (n10 <<< 8) ||| (n11 <<< 12)) =
      (Algorithm.extractCenterUInt (Algorithm.quad0UInt w) |||
        (Algorithm.extractHorizontalMidUInt (Algorithm.quad0UInt w) (Algorithm.quad1UInt w) <<< 4) |||
        (Algorithm.extractVerticalMidUInt (Algorithm.quad0UInt w) (Algorithm.quad2UInt w) <<< 8) |||
        (Algorithm.extractCenterMidUInt (Algorithm.quad0UInt w) (Algorithm.quad1UInt w)
          (Algorithm.quad2UInt w) (Algorithm.quad3UInt w) <<< 12)) := by
  unfold computeQuadInfoModel Algorithm.extractCenterUInt Algorithm.extractHorizontalMidUInt
    Algorithm.extractVerticalMidUInt Algorithm.extractCenterMidUInt
    Algorithm.quad0UInt Algorithm.quad1UInt Algorithm.quad2UInt Algorithm.quad3UInt
  bv_check "lrat/BitComputationModelProofs.Algorithm.KotlinModel.pk_nw_in_eq.lrat"

theorem pk_ne_in_eq (w : UInt64) :
    let q0 : UInt32 := (w &&& (0xFFFF : UInt64)).toUInt32
    let q1 : UInt32 := ((w >>> 16) &&& (0xFFFF : UInt64)).toUInt32
    let q2 : UInt32 := ((w >>> 32) &&& (0xFFFF : UInt64)).toUInt32
    let q3 : UInt32 := (w >>> 48).toUInt32
    let info0 : UInt32 := computeQuadInfoModel q0
    let info1 : UInt32 := computeQuadInfoModel q1
    let info2 : UInt32 := computeQuadInfoModel q2
    let info3 : UInt32 := computeQuadInfoModel q3
    let n02 : UInt32 := info1 &&& (0xF : UInt32)
    let n01 : UInt32 := ((info0 >>> 4) &&& (0x5 : UInt32)) ||| ((info1 >>> 8) &&& (0xA : UInt32))
    let n12 : UInt32 := ((info1 >>> 12) &&& (0x3 : UInt32)) ||| ((info3 >>> 16) &&& (0xC : UInt32))
    let n11 : UInt32 := ((info0 >>> 20) &&& (1 : UInt32)) ||| ((info1 >>> 20) &&& (2 : UInt32)) |||
      ((info2 >>> 20) &&& (4 : UInt32)) ||| ((info3 >>> 20) &&& (8 : UInt32))
    (n01 ||| (n02 <<< 4) ||| (n11 <<< 8) ||| (n12 <<< 12)) =
      (Algorithm.extractHorizontalMidUInt (Algorithm.quad0UInt w) (Algorithm.quad1UInt w) |||
        (Algorithm.extractCenterUInt (Algorithm.quad1UInt w) <<< 4) |||
        (Algorithm.extractCenterMidUInt (Algorithm.quad0UInt w) (Algorithm.quad1UInt w)
          (Algorithm.quad2UInt w) (Algorithm.quad3UInt w) <<< 8) |||
        (Algorithm.extractVerticalMidUInt (Algorithm.quad1UInt w) (Algorithm.quad3UInt w) <<< 12)) := by
  unfold computeQuadInfoModel Algorithm.extractCenterUInt Algorithm.extractHorizontalMidUInt
    Algorithm.extractVerticalMidUInt Algorithm.extractCenterMidUInt
    Algorithm.quad0UInt Algorithm.quad1UInt Algorithm.quad2UInt Algorithm.quad3UInt
  bv_check "lrat/BitComputationModelProofs.Algorithm.KotlinModel.pk_ne_in_eq.lrat"

theorem pk_sw_in_eq (w : UInt64) :
    let q0 : UInt32 := (w &&& (0xFFFF : UInt64)).toUInt32
    let q1 : UInt32 := ((w >>> 16) &&& (0xFFFF : UInt64)).toUInt32
    let q2 : UInt32 := ((w >>> 32) &&& (0xFFFF : UInt64)).toUInt32
    let q3 : UInt32 := (w >>> 48).toUInt32
    let info0 : UInt32 := computeQuadInfoModel q0
    let info1 : UInt32 := computeQuadInfoModel q1
    let info2 : UInt32 := computeQuadInfoModel q2
    let info3 : UInt32 := computeQuadInfoModel q3
    let n20 : UInt32 := info2 &&& (0xF : UInt32)
    let n21 : UInt32 := ((info2 >>> 4) &&& (0x5 : UInt32)) ||| ((info3 >>> 8) &&& (0xA : UInt32))
    let n10 : UInt32 := ((info0 >>> 12) &&& (0x3 : UInt32)) ||| ((info2 >>> 16) &&& (0xC : UInt32))
    let n11 : UInt32 := ((info0 >>> 20) &&& (1 : UInt32)) ||| ((info1 >>> 20) &&& (2 : UInt32)) |||
      ((info2 >>> 20) &&& (4 : UInt32)) ||| ((info3 >>> 20) &&& (8 : UInt32))
    (n10 ||| (n11 <<< 4) ||| (n20 <<< 8) ||| (n21 <<< 12)) =
      (Algorithm.extractVerticalMidUInt (Algorithm.quad0UInt w) (Algorithm.quad2UInt w) |||
        (Algorithm.extractCenterMidUInt (Algorithm.quad0UInt w) (Algorithm.quad1UInt w)
          (Algorithm.quad2UInt w) (Algorithm.quad3UInt w) <<< 4) |||
        (Algorithm.extractCenterUInt (Algorithm.quad2UInt w) <<< 8) |||
        (Algorithm.extractHorizontalMidUInt (Algorithm.quad2UInt w) (Algorithm.quad3UInt w) <<< 12)) := by
  unfold computeQuadInfoModel Algorithm.extractCenterUInt Algorithm.extractHorizontalMidUInt
    Algorithm.extractVerticalMidUInt Algorithm.extractCenterMidUInt
    Algorithm.quad0UInt Algorithm.quad1UInt Algorithm.quad2UInt Algorithm.quad3UInt
  bv_check "lrat/BitComputationModelProofs.Algorithm.KotlinModel.pk_sw_in_eq.lrat"

theorem pk_se_in_eq (w : UInt64) :
    let q0 : UInt32 := (w &&& (0xFFFF : UInt64)).toUInt32
    let q1 : UInt32 := ((w >>> 16) &&& (0xFFFF : UInt64)).toUInt32
    let q2 : UInt32 := ((w >>> 32) &&& (0xFFFF : UInt64)).toUInt32
    let q3 : UInt32 := (w >>> 48).toUInt32
    let info0 : UInt32 := computeQuadInfoModel q0
    let info1 : UInt32 := computeQuadInfoModel q1
    let info2 : UInt32 := computeQuadInfoModel q2
    let info3 : UInt32 := computeQuadInfoModel q3
    let n22 : UInt32 := info3 &&& (0xF : UInt32)
    let n21 : UInt32 := ((info2 >>> 4) &&& (0x5 : UInt32)) ||| ((info3 >>> 8) &&& (0xA : UInt32))
    let n12 : UInt32 := ((info1 >>> 12) &&& (0x3 : UInt32)) ||| ((info3 >>> 16) &&& (0xC : UInt32))
    let n11 : UInt32 := ((info0 >>> 20) &&& (1 : UInt32)) ||| ((info1 >>> 20) &&& (2 : UInt32)) |||
      ((info2 >>> 20) &&& (4 : UInt32)) ||| ((info3 >>> 20) &&& (8 : UInt32))
    (n11 ||| (n12 <<< 4) ||| (n21 <<< 8) ||| (n22 <<< 12)) =
      (Algorithm.extractCenterMidUInt (Algorithm.quad0UInt w) (Algorithm.quad1UInt w)
          (Algorithm.quad2UInt w) (Algorithm.quad3UInt w) |||
        (Algorithm.extractVerticalMidUInt (Algorithm.quad1UInt w) (Algorithm.quad3UInt w) <<< 4) |||
        (Algorithm.extractHorizontalMidUInt (Algorithm.quad2UInt w) (Algorithm.quad3UInt w) <<< 8) |||
        (Algorithm.extractCenterUInt (Algorithm.quad3UInt w) <<< 12)) := by
  unfold computeQuadInfoModel Algorithm.extractCenterUInt Algorithm.extractHorizontalMidUInt
    Algorithm.extractVerticalMidUInt Algorithm.extractCenterMidUInt
    Algorithm.quad0UInt Algorithm.quad1UInt Algorithm.quad2UInt Algorithm.quad3UInt
  bv_check "lrat/BitComputationModelProofs.Algorithm.KotlinModel.pk_se_in_eq.lrat"

theorem pureKotlin_subgrids_eq_Impl (nextGenLut : UInt32 → UInt32) (w : UInt64) (hw : w ≠ 0) :
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
      nw ||| (ne <<< 4) ||| (sw <<< 8) ||| (se <<< 12) := by
  have hbeq : (w == 0) = false := beq_false_of_ne hw
  unfold computeNextGenerationPureKotlinModelWith
  simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
  rw [pk_nw_in_eq w, pk_ne_in_eq w, pk_sw_in_eq w, pk_se_in_eq w]

theorem computeNextGenerationPureKotlinModel_eq_fast_Impl (w : UInt64) :
    computeNextGenerationPureKotlinModel w = Algorithm.computeLeafNextGen8x8FastUInt w := by
  by_cases hw : w = 0
  · subst hw; decide
  · unfold computeNextGenerationPureKotlinModel
    rw [pureKotlin_subgrids_eq_Impl Algorithm.computeNextGen4x4BitwiseUInt w hw]
    rfl

theorem computeNextGenerationPureKotlinModel_correct_Impl (w : UInt64) (x y : ℤ)
    (hx : 2 ≤ x ∧ x < 6) (hy : 2 ≤ y ∧ y < 6) :
    (computeNextGenerationPureKotlinModel w).toBitVec.getLsbD (mortonIndex4 (x - 2).toNat (y - 2).toNat) =
      nextGenAt (leafAt w) x y := by
  rw [computeNextGenerationPureKotlinModel_eq_fast_Impl, ← Algorithm.computeLeafNextGen8x8BranchUInt_eq_fastUInt]
  exact Algorithm.computeLeafNextGen8x8BranchUInt_correct w x y hx hy

theorem computeNextGenerationPureKotlinModel_zero_Impl :
    computeNextGenerationPureKotlinModel 0 = 0 := by
  decide

theorem pk_lt_65536 (nw ne sw se : UInt32)
    (hnw : nw < 16) (hne : ne < 16) (hsw : sw < 16) (hse : se < 16) :
    (nw ||| (ne <<< 4) ||| (sw <<< 8) ||| (se <<< 12)) < 65536 := by
  bv_check "lrat/BitComputationModelProofs.Algorithm.KotlinModel.pk_lt_65536.lrat"

theorem computeNextGenerationPureKotlinModel_lt_65536_Impl (w : UInt64) :
    (computeNextGenerationPureKotlinModel w).toNat < 65536 := by
  rw [computeNextGenerationPureKotlinModel_eq_fast_Impl]
  unfold Algorithm.computeLeafNextGen8x8FastUInt
  dsimp only
  change _ < (65536 : UInt32).toNat
  apply pk_lt_65536 <;> exact Algorithm.computeNextGen4x4UInt_lt_16 _

theorem ci_q0 (w c : UInt64) (hc : c &&& ~~~outerCornerMask = 0) :
    Algorithm.extractCenterUInt (Algorithm.quad0UInt (w ^^^ c)) =
      Algorithm.extractCenterUInt (Algorithm.quad0UInt w) := by
  unfold Algorithm.extractCenterUInt Algorithm.quad0UInt outerCornerMask at *
  bv_check "lrat/BitComputationModelProofs.Algorithm.KotlinModel.ci_q0.lrat"

theorem ci_q1 (w c : UInt64) (hc : c &&& ~~~outerCornerMask = 0) :
    Algorithm.extractCenterUInt (Algorithm.quad1UInt (w ^^^ c)) =
      Algorithm.extractCenterUInt (Algorithm.quad1UInt w) := by
  unfold Algorithm.extractCenterUInt Algorithm.quad1UInt outerCornerMask at *
  bv_check "lrat/BitComputationModelProofs.Algorithm.KotlinModel.ci_q1.lrat"

theorem ci_q2 (w c : UInt64) (hc : c &&& ~~~outerCornerMask = 0) :
    Algorithm.extractCenterUInt (Algorithm.quad2UInt (w ^^^ c)) =
      Algorithm.extractCenterUInt (Algorithm.quad2UInt w) := by
  unfold Algorithm.extractCenterUInt Algorithm.quad2UInt outerCornerMask at *
  bv_check "lrat/BitComputationModelProofs.Algorithm.KotlinModel.ci_q2.lrat"

theorem ci_q3 (w c : UInt64) (hc : c &&& ~~~outerCornerMask = 0) :
    Algorithm.extractCenterUInt (Algorithm.quad3UInt (w ^^^ c)) =
      Algorithm.extractCenterUInt (Algorithm.quad3UInt w) := by
  unfold Algorithm.extractCenterUInt Algorithm.quad3UInt outerCornerMask at *
  bv_check "lrat/BitComputationModelProofs.Algorithm.KotlinModel.ci_q3.lrat"

theorem ci_h01 (w c : UInt64) (hc : c &&& ~~~outerCornerMask = 0) :
    Algorithm.extractHorizontalMidUInt (Algorithm.quad0UInt (w ^^^ c)) (Algorithm.quad1UInt (w ^^^ c)) =
      Algorithm.extractHorizontalMidUInt (Algorithm.quad0UInt w) (Algorithm.quad1UInt w) := by
  unfold Algorithm.extractHorizontalMidUInt Algorithm.quad0UInt Algorithm.quad1UInt outerCornerMask at *
  bv_check "lrat/BitComputationModelProofs.Algorithm.KotlinModel.ci_h01.lrat"

theorem ci_h23 (w c : UInt64) (hc : c &&& ~~~outerCornerMask = 0) :
    Algorithm.extractHorizontalMidUInt (Algorithm.quad2UInt (w ^^^ c)) (Algorithm.quad3UInt (w ^^^ c)) =
      Algorithm.extractHorizontalMidUInt (Algorithm.quad2UInt w) (Algorithm.quad3UInt w) := by
  unfold Algorithm.extractHorizontalMidUInt Algorithm.quad2UInt Algorithm.quad3UInt outerCornerMask at *
  bv_check "lrat/BitComputationModelProofs.Algorithm.KotlinModel.ci_h23.lrat"

theorem ci_v02 (w c : UInt64) (hc : c &&& ~~~outerCornerMask = 0) :
    Algorithm.extractVerticalMidUInt (Algorithm.quad0UInt (w ^^^ c)) (Algorithm.quad2UInt (w ^^^ c)) =
      Algorithm.extractVerticalMidUInt (Algorithm.quad0UInt w) (Algorithm.quad2UInt w) := by
  unfold Algorithm.extractVerticalMidUInt Algorithm.quad0UInt Algorithm.quad2UInt outerCornerMask at *
  bv_check "lrat/BitComputationModelProofs.Algorithm.KotlinModel.ci_v02.lrat"

theorem ci_v13 (w c : UInt64) (hc : c &&& ~~~outerCornerMask = 0) :
    Algorithm.extractVerticalMidUInt (Algorithm.quad1UInt (w ^^^ c)) (Algorithm.quad3UInt (w ^^^ c)) =
      Algorithm.extractVerticalMidUInt (Algorithm.quad1UInt w) (Algorithm.quad3UInt w) := by
  unfold Algorithm.extractVerticalMidUInt Algorithm.quad1UInt Algorithm.quad3UInt outerCornerMask at *
  bv_check "lrat/BitComputationModelProofs.Algorithm.KotlinModel.ci_v13.lrat"

theorem ci_mid (w c : UInt64) (hc : c &&& ~~~outerCornerMask = 0) :
    Algorithm.extractCenterMidUInt (Algorithm.quad0UInt (w ^^^ c)) (Algorithm.quad1UInt (w ^^^ c))
        (Algorithm.quad2UInt (w ^^^ c)) (Algorithm.quad3UInt (w ^^^ c)) =
      Algorithm.extractCenterMidUInt (Algorithm.quad0UInt w) (Algorithm.quad1UInt w)
        (Algorithm.quad2UInt w) (Algorithm.quad3UInt w) := by
  unfold Algorithm.extractCenterMidUInt Algorithm.quad0UInt Algorithm.quad1UInt
    Algorithm.quad2UInt Algorithm.quad3UInt outerCornerMask at *
  bv_check "lrat/BitComputationModelProofs.Algorithm.KotlinModel.ci_mid.lrat"

theorem computeNextGenerationPureKotlinModel_corner_indep_Impl (w c : UInt64)
    (hc : c &&& ~~~outerCornerMask = 0) :
    computeNextGenerationPureKotlinModel (w ^^^ c) = computeNextGenerationPureKotlinModel w := by
  rw [computeNextGenerationPureKotlinModel_eq_fast_Impl, computeNextGenerationPureKotlinModel_eq_fast_Impl]
  unfold Algorithm.computeLeafNextGen8x8FastUInt
  dsimp only
  rw [ci_q0 w c hc, ci_q1 w c hc, ci_q2 w c hc, ci_q3 w c hc,
    ci_h01 w c hc, ci_h23 w c hc, ci_v02 w c hc, ci_v13 w c hc, ci_mid w c hc]

end Algorithm.KotlinModel
