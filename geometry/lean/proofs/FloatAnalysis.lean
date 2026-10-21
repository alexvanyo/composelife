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

import models.Basic
import models.FloatModel
import GeometryDefs
import proofs.FloatSemantics
import proofs.FloatBounds
import Geometry.LineSegment
import FloatLib
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith

namespace Geometry

open FloatLib.Floats
open FloatLib.Numerics
open FloatLib.Floats.Formats.BinaryInterchange

theorem toRat?_isSome_of_isFinite (x : Binary32) (hx : binary32IsFinite x = true) :
    ∃ q : ℚ, ExecFloat.Binary.toRat? x = some q := by
  have h_model_fin : ExecFloat.Binary.isFinite x = true := hx
  unfold binary32IsFinite ExecFloat.Binary.isFinite at hx
  unfold ExecFloat.Binary.toRat?
  have h_ieee_fin : Formats.BinaryInterchange.Model.IEEE.isFinite (ExecFloat.Binary.toModel x) = true := hx
  obtain ⟨d, hd⟩ := Model.exists_ieeeToDyadic?_of_isFinite h_ieee_fin
  have h_dyadic : Model.toDyadic? (ExecFloat.Binary.toModel x) = some d := by
    unfold Model.toDyadic?
    simp [hd]
  unfold Model.toRat?
  rw [h_dyadic]
  exact ⟨d.toRat, rfl⟩

theorem floorBinary32_eq_toInt_binary32ToRat (f : Binary32) (h_fin : binary32IsFinite f = true) :
    floorBinary32 f = toInt (binary32ToRat f) := by
  obtain ⟨q, hq⟩ := toRat?_isSome_of_isFinite f h_fin
  unfold floorBinary32 binary32ToRat toInt
  rw [hq]
  simp

theorem floorPoint32_eq_floorPoint (p : Point32) (h_fin : p.isFinite) :
    floorPoint32 p = floorPoint p.toPoint := by
  unfold floorPoint32 floorPoint Point32.toPoint
  rcases h_fin with ⟨hx, hy⟩
  rw [floorBinary32_eq_toInt_binary32ToRat p.x hx]
  rw [floorBinary32_eq_toInt_binary32ToRat p.y hy]

theorem toReal_eq_cast_toRat (x : Binary32) (hx : binary32IsFinite x = true) :
    Model.toReal (ExecFloat.Binary.toModel x) = ((binary32ToRat x : ℚ) : ℝ) := by
  have h_model_fin : ExecFloat.Binary.isFinite x = true := hx
  unfold binary32IsFinite ExecFloat.Binary.isFinite at hx
  have h_ieee_fin : Model.IEEE.isFinite (ExecFloat.Binary.toModel x) = true := hx
  obtain ⟨d, hd⟩ := Model.exists_ieeeToDyadic?_of_isFinite h_ieee_fin
  have h_dyadic : Model.toDyadic? (ExecFloat.Binary.toModel x) = some d := by
    unfold Model.toDyadic?
    simp [hd]
  have h_toRat : ExecFloat.Binary.toRat? x = some d.toRat := by
    unfold ExecFloat.Binary.toRat? Model.toRat?
    rw [h_dyadic]
    rfl
  have h_rat : binary32ToRat x = d.toRat := by
    unfold binary32ToRat
    rw [h_toRat]
    rfl
  rw [h_rat]
  unfold Model.toReal Model.toReal?
  rw [h_dyadic]
  exact (Dyadic.cast_toRat d).symm

/--
Any positive integer N bounded by the unscaled significand capacity is well within the
positive finite representable range of IEEE-754 formats of sufficient width.
-/
theorem nat_le_posMaxFinite (fmt : FloatFormat) (N : ℕ) (hN : 0 < N)
    (hm : N ≤ Model.pow2 fmt.fracWidth + fmt.maxFiniteFracField)
    (hexp : 0 ≤ fmt.maxNormalExponent - Int.ofNat fmt.fracWidth) :
    (N : ℝ) ≤ Model.toReal (Model.posMaxFinite fmt) := by
  have h := Model.abs_signed_mul_bpow_le_toReal_posMaxFinite fmt false N 0 hm hexp
  simp only [Bool.false_eq_true, ite_false, one_mul, Model.bpow_zero, mul_one] at h
  rw [abs_of_pos (by positivity)] at h
  exact h

theorem toReal_eq_int_mul_posMinSubnormal (x : Binary32) (hx : binary32IsFinite x = true) :
    ∃ n : ℤ, Model.toReal (ExecFloat.Binary.toModel x) =
      (n : ℝ) * Model.toReal (Model.posMinSubnormal FloatFormat.binary32) := by
  have h_model_fin : ExecFloat.Binary.isFinite x = true := hx
  unfold binary32IsFinite ExecFloat.Binary.isFinite at hx
  have h_ieee_fin : Model.IEEE.isFinite (ExecFloat.Binary.toModel x) = true := hx
  obtain ⟨d, hd⟩ := Model.exists_ieeeToDyadic?_of_isFinite h_ieee_fin
  have h_dyadic : Model.toDyadic? (ExecFloat.Binary.toModel x) = some d := by
    unfold Model.toDyadic?
    simp [hd]
  have h_toReal : Model.toReal (ExecFloat.Binary.toModel x) = d.toReal := by
    unfold Model.toReal Model.toReal?
    rw [h_dyadic]
  have hexp : FloatFormat.binary32.minSubnormalExponent ≤ d.exponent :=
    Model.minSubnormalExponent_le_toDyadic? (ExecFloat.Binary.toModel x) h_dyadic
  have hd_toReal : d.toReal = (d.signedSignificand : ℝ) * Model.bpow d.exponent := rfl
  have h_exp_sub : 0 ≤ d.exponent - FloatFormat.binary32.minSubnormalExponent := by omega
  set k : ℕ := (d.exponent - FloatFormat.binary32.minSubnormalExponent).toNat with hk_def
  have hk : (k : ℤ) = d.exponent - FloatFormat.binary32.minSubnormalExponent :=
    Int.toNat_of_nonneg h_exp_sub
  have h_exp_eq : d.exponent = (k : ℤ) + FloatFormat.binary32.minSubnormalExponent := by omega
  have hbpow : Model.bpow d.exponent =
      ((2 ^ k : ℕ) : ℝ) * Model.bpow FloatFormat.binary32.minSubnormalExponent := by
    rw [h_exp_eq, Model.bpow_add, Model.bpow_natCast]
    push_cast
    rfl
  have h_posMin : Model.toReal (Model.posMinSubnormal FloatFormat.binary32) =
      Model.bpow FloatFormat.binary32.minSubnormalExponent :=
    Model.toReal_posMinSubnormal FloatFormat.binary32
  use d.signedSignificand * (2 ^ k : ℤ)
  rw [h_toReal, hd_toReal, hbpow, h_posMin]
  push_cast
  ring

theorem decodeTo_of_toDyadic? (x : Binary32) (d : FloatLib.Numerics.Dyadic)
    (hd : Model.toDyadic? (ExecFloat.Binary.toModel x) = some d) :
    FloatLib.Floats.ExecFloat.ExactDecoder.decodeTo (TargetExact := SignedRat) x =
      .finite (SignedRat.ofDyadic d) := by
  unfold FloatLib.Floats.ExecFloat.ExactDecoder.decodeTo
  rw [ExecFloat.Binary.Conversion.exactDecoder_run]
  unfold ExecFloat.Binary.decode
  unfold Model.exactNumericalSystem
  simp only [hd]
  rfl

theorem widen32To64_eq_roundRat (x : Binary32) (d : FloatLib.Numerics.Dyadic)
    (hd : Model.toDyadic? (ExecFloat.Binary.toModel x) = some d) :
    ExecFloat.Binary.toModel (widen32To64 x) =
      Model.roundRat FloatFormat.binary64 d.negative d.toRat.num.natAbs d.toRat.den := by
  have hdec := decodeTo_of_toDyadic? x d hd
  have hcast : (ExecFloat.cast (target := Binary64) x) =
      .success
        (ExecFloat.Binary.ofModel (Model.roundRat FloatFormat.binary64 d.negative d.toRat.num.natAbs d.toRat.den))
        _ :=
    ExecFloat.Binary.Conversion.cast_eq_roundRat_of_decodeTo_eq_finite x (SignedRat.ofDyadic d) hdec
  unfold widen32To64
  change ExecFloat.Binary.toModel ((ExecFloat.cast (target := Binary64) x).value?.getD (0.0 : Binary64)) = _
  rw [hcast]
  exact Configured.Family.toModel_ofModel _

theorem signedRat_toReal (exact : SignedRat) (hvalue : exact.value ≠ 0) :
    Model.signedScaledRatToReal exact.negative exact.value.num.natAbs exact.value.den 0 =
      (exact.value : ℝ) := by
  have hmagnitude :
      (exact.value.num.natAbs : ℝ) / exact.value.den = |(exact.value : ℝ)| := by
    simp [Rat.cast_def, abs_div]
  simp only [Model.signedScaledRatToReal, Model.scaledRatToReal, Model.bpow_zero, mul_one,
    hmagnitude, exact.negative_eq_of_ne_zero hvalue]
  by_cases hnegative : exact.value < 0
  · have hnegativeReal : (exact.value : ℝ) < 0 := by exact_mod_cast hnegative
    simp [hnegative, abs_of_neg hnegativeReal]
  · have hnonnegativeReal : 0 ≤ (exact.value : ℝ) := by
      exact_mod_cast le_of_not_gt hnegative
    simp [hnegative, abs_of_nonneg hnonnegativeReal]

theorem posMaxFinite_binary32_le_binary64 :
    Model.toReal (Model.posMaxFinite FloatFormat.binary32) ≤
      Model.toReal (Model.posMaxFinite FloatFormat.binary64) := by
  have h := Model.abs_signed_mul_bpow_le_toReal_posMaxFinite FloatFormat.binary64 false
    (Model.pow2 FloatFormat.binary32.fracWidth + FloatFormat.binary32.maxFiniteFracField)
    (FloatFormat.binary32.maxNormalExponent - Int.ofNat FloatFormat.binary32.fracWidth)
    (by decide) (by decide)
  simp only [Bool.false_eq_true, ite_false, one_mul] at h
  rw [← Model.toReal_posMaxFinite FloatFormat.binary32] at h
  have hnonneg : 0 ≤ Model.toReal (Model.posMaxFinite FloatFormat.binary32) := by
    rw [Model.toReal_posMaxFinite]
    exact mul_nonneg (by positivity) (Model.bpow_nonneg _)
  rwa [abs_of_nonneg hnonneg] at h

/--
Widening a finite 32-bit float to 64-bit preserves its exact real-number value.
-/
theorem widen32To64_toReal_eq (x : Binary32) (hx : binary32IsFinite x = true) :
    Model.toReal (ExecFloat.Binary.toModel (widen32To64 x)) = Model.toReal (ExecFloat.Binary.toModel x) := by
  have h_ieee_fin : Model.IEEE.isFinite (ExecFloat.Binary.toModel x) = true := hx
  obtain ⟨d, hd⟩ := Model.exists_ieeeToDyadic?_of_isFinite h_ieee_fin
  have h_dyadic : Model.toDyadic? (ExecFloat.Binary.toModel x) = some d := by
    unfold Model.toDyadic?
    simp [hd]
  have h_toReal_x : Model.toReal (ExecFloat.Binary.toModel x) = (d.toRat : ℝ) := by
    unfold Model.toReal Model.toReal?
    rw [h_dyadic]
    exact (Dyadic.cast_toRat d).symm
  rw [show Model.toReal (ExecFloat.Binary.toModel (widen32To64 x)) =
        Model.toReal (Model.roundRat FloatFormat.binary64 d.negative d.toRat.num.natAbs d.toRat.den) from
      congrArg Model.toReal (widen32To64_eq_roundRat x d h_dyadic)]
  by_cases hzero : d.toRat = 0
  · have hnum : d.toRat.num.natAbs = 0 := by simp [hzero]
    rw [hnum]
    rw [Model.roundRat, Model.roundRatScaled_num_zero FloatFormat.binary64 d.negative d.toRat.den 0 d.toRat.den_nz]
    rw [Model.toReal_zero]
    rw [h_toReal_x, hzero, Rat.cast_zero]
  · have hnum : d.toRat.num.natAbs ≠ 0 := by simpa using hzero
    have hden : d.toRat.den ≠ 0 := d.toRat.den_nz
    have hfmt : FloatFormat.binary64.isIEEE = true := rfl
    have hbound :
        |Model.signedScaledRatToReal d.negative d.toRat.num.natAbs d.toRat.den 0| ≤
          Model.toReal (Model.posMaxFinite FloatFormat.binary64) := by
      have h_signed := signedRat_toReal (SignedRat.ofDyadic d) hzero
      change Model.signedScaledRatToReal d.negative d.toRat.num.natAbs d.toRat.den 0 = (d.toRat : ℝ) at h_signed
      rw [h_signed, ← h_toReal_x]
      exact le_trans
        (Model.abs_toReal_le_posMaxFinite_of_isIEEE_of_isFinite (ExecFloat.Binary.toModel x) (by rfl) hx)
        posMaxFinite_binary32_le_binary64
    have hfinite :
        Model.isFinite (Model.roundRatScaled FloatFormat.binary64 d.negative d.toRat.num.natAbs d.toRat.den 0) = true :=
      Model.isFinite_roundRatScaled_of_abs_le_posMaxFinite FloatFormat.binary64 d.negative
        d.toRat.num.natAbs d.toRat.den 0 hfmt hden hbound
    rw [Model.roundRat, Model.toReal_roundRatScaled_eq_roundAt FloatFormat.binary64 d.negative
      d.toRat.num.natAbs d.toRat.den 0 hfmt hnum hden hfinite]
    have h_signed := signedRat_toReal (SignedRat.ofDyadic d) hzero
    change Model.signedScaledRatToReal d.negative d.toRat.num.natAbs d.toRat.den 0 = (d.toRat : ℝ) at h_signed
    rw [h_signed, ← h_toReal_x]
    exact FloatLib.Floats.Formats.Flocq.round_preserves_generic
      FloatLib.Floats.Formats.Flocq.nearestEven
      (Model.toReal (ExecFloat.Binary.toModel x))
      (Model.genericFormat_of_gridExtension
        (by decide) (by decide)
        (Model.toReal_genericFormat_of_isFinite (ExecFloat.Binary.toModel x) hx))

/--
Converting an integer with magnitude bounded by mainCoordBound.floor + 2 to Binary64 via intToBinary64
preserves its exact real value.
-/
theorem intToBinary64_toReal_eq (n : Int) (hn : |n| ≤ (mainCoordBoundNat : ℤ) + 2) :
    Model.toReal (ExecFloat.Binary.toModel (intToBinary64 n)) = (n : ℝ) := by
  have h_toModel : ExecFloat.Binary.toModel (intToBinary64 n) =
      Model.roundDyadic FloatFormat.binary64 (Dyadic.ofScaledInt n 0) :=
    ExecFloat.Binary.toModel_ofFloat_ofInt n
  have hrepr := Model.roundDyadic_of_representable FloatFormat.binary64 (by rfl)
    (Dyadic.ofScaledInt n 0) n.natAbs 0
    (by simp [Dyadic.ofScaledInt])
    (by
      have h1 : -((mainCoordBoundNat : ℤ) + 2) ≤ n ∧ n ≤ (mainCoordBoundNat : ℤ) + 2 := abs_le.mp hn
      have h2 : n.natAbs ≤ mainCoordBoundNat + 2 := by omega
      have h_bound : mainCoordBoundNat + 2 < 2 ^ 53 := by decide
      exact Nat.lt_of_le_of_lt h2 h_bound)
    (by
      simp only [Dyadic.ofScaledInt]
      decide)
    (by
      rw [Model.Dyadic.toReal_ofScaledInt_zero]
      have h_le : |(n : ℝ)| ≤ (((mainCoordBoundNat : ℤ) + 2 : ℤ) : ℝ) := by
        rw [← Int.cast_abs]
        exact_mod_cast hn
      have h_cast : (((mainCoordBoundNat : ℤ) + 2 : ℤ) : ℝ) = ((mainCoordBoundNat + 2 : ℕ) : ℝ) := by
        push_cast; rfl
      rw [h_cast] at h_le
      have h_posMax := nat_le_posMaxFinite FloatFormat.binary64 (mainCoordBoundNat + 2)
        (by decide) (by decide) (by decide)
      exact le_trans h_le h_posMax)
  calc
    Model.toReal (ExecFloat.Binary.toModel (intToBinary64 n)) =
        Model.toReal (Model.roundDyadic FloatFormat.binary64 (Dyadic.ofScaledInt n 0)) :=
      congrArg Model.toReal h_toModel
    _ = (Dyadic.ofScaledInt n 0).toReal := hrepr.2
    _ = (n : ℝ) := Model.Dyadic.toReal_ofScaledInt_zero n

/--
Converting an integer with magnitude bounded by mainCoordBound.floor + 2 to Binary64 via intToBinary64
yields a finite float.
-/
theorem intToBinary64_isFinite (n : Int) (hn : |n| ≤ (mainCoordBoundNat : ℤ) + 2) :
    ExecFloat.Binary.isFinite (intToBinary64 n) = true := by
  have h_toModel : ExecFloat.Binary.toModel (intToBinary64 n) =
      Model.roundDyadic FloatFormat.binary64 (Dyadic.ofScaledInt n 0) :=
    ExecFloat.Binary.toModel_ofFloat_ofInt n
  have hrepr := Model.roundDyadic_of_representable FloatFormat.binary64 (by rfl)
    (Dyadic.ofScaledInt n 0) n.natAbs 0
    (by simp [Dyadic.ofScaledInt])
    (by
      have h1 : -((mainCoordBoundNat : ℤ) + 2) ≤ n ∧ n ≤ (mainCoordBoundNat : ℤ) + 2 := abs_le.mp hn
      have h2 : n.natAbs ≤ mainCoordBoundNat + 2 := by omega
      have h_bound : mainCoordBoundNat + 2 < 2 ^ 53 := by decide
      exact Nat.lt_of_le_of_lt h2 h_bound)
    (by
      simp only [Dyadic.ofScaledInt]
      decide)
    (by
      rw [Model.Dyadic.toReal_ofScaledInt_zero]
      have h_le : |(n : ℝ)| ≤ (((mainCoordBoundNat : ℤ) + 2 : ℤ) : ℝ) := by
        rw [← Int.cast_abs]
        exact_mod_cast hn
      have h_cast : (((mainCoordBoundNat : ℤ) + 2 : ℤ) : ℝ) = ((mainCoordBoundNat + 2 : ℕ) : ℝ) := by
        push_cast; rfl
      rw [h_cast] at h_le
      have h_posMax := nat_le_posMaxFinite FloatFormat.binary64 (mainCoordBoundNat + 2)
        (by decide) (by decide) (by decide)
      exact le_trans h_le h_posMax)
  change Model.isFinite (ExecFloat.Binary.toModel (intToBinary64 n)) = true
  rw [h_toModel]
  exact hrepr.1

/--
The result of a single rational rayMarchStep is either the done-pair or one of three non-done cells.
This helper records both the cell and done-bit as a conjunction for easier case matching.
-/
private theorem rayMarchStep_done_or_cases (start ptEnd : Point) (dx dy : ℚ) (stepX stepY : ℤ) (c : Cell) :
    ((rayMarchStep start ptEnd dx dy stepX stepY c).2 = true ∧
     (rayMarchStep start ptEnd dx dy stepX stepY c).1 = c) ∨
    ((rayMarchStep start ptEnd dx dy stepX stepY c).2 = false ∧
     ((rayMarchStep start ptEnd dx dy stepX stepY c).1 = ⟨c.x + stepX, c.y⟩ ∨
      (rayMarchStep start ptEnd dx dy stepX stepY c).1 = ⟨c.x, c.y + stepY⟩ ∨
      (rayMarchStep start ptEnd dx dy stepX stepY c).1 = ⟨c.x + stepX, c.y + stepY⟩)) := by
  have h := rayMarchStep_mem start ptEnd dx dy stepX stepY c
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h
  · left
    exact ⟨congrArg Prod.snd h, congrArg Prod.fst h⟩
  · right
    exact ⟨congrArg Prod.snd h, Or.inl (congrArg Prod.fst h)⟩
  · right
    exact ⟨congrArg Prod.snd h, Or.inr (Or.inl (congrArg Prod.fst h))⟩
  · right
    exact ⟨congrArg Prod.snd h, Or.inr (Or.inr (congrArg Prod.fst h))⟩

/--
The result of a single float rayMarchStepFloat is either the done-pair or one of three non-done cells.
-/
theorem rayMarchStepFloat_done_or_cases (start : Point32) (dx dy : Binary64) (stepX stepY : ℤ) (c : Cell) :
    ((rayMarchStepFloat start dx dy stepX stepY c).2 = true ∧
     (rayMarchStepFloat start dx dy stepX stepY c).1 = c) ∨
    ((rayMarchStepFloat start dx dy stepX stepY c).2 = false ∧
     ((rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x + stepX, c.y⟩ ∨
      (rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x, c.y + stepY⟩ ∨
      (rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x + stepX, c.y + stepY⟩)) := by
  unfold rayMarchStepFloat
  dsimp only []
  by_cases hx0 : stepX == 0
  · simp only [hx0, ite_true]
    split_ifs <;> simp
  · simp only [hx0, Bool.false_eq_true, ite_false]
    by_cases hy0 : stepY == 0
    · simp only [hy0, ite_true]
      split_ifs <;> simp
    · simp only [hy0, Bool.false_eq_true, ite_false]
      split_ifs <;> simp

end Geometry

