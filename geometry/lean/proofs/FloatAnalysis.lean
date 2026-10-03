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

import Geometry.Basic
import Geometry.FloatModel
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

theorem compareLess_iff_toRat_lt (x y : Binary32)
    (hx : binary32IsFinite x = true) (hy : binary32IsFinite y = true) :
    (x < y) ↔ binary32ToRat x < binary32ToRat y := by
  rw [ExecFloat.Binary.lt_iff_compare_eq_lt]
  have hx_fin : Model.isFinite (ExecFloat.Binary.toModel x) = true := hx
  have hy_fin : Model.isFinite (ExecFloat.Binary.toModel y) = true := hy
  rw [Model.compare_eq_some_lt_iff_toReal_lt_of_isFinite
    (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y) hx_fin hy_fin]
  rw [toReal_eq_cast_toRat x hx]
  rw [toReal_eq_cast_toRat y hy]
  exact Rat.cast_lt

theorem compareGreater_iff_toRat_gt (x y : Binary32)
    (hx : binary32IsFinite x = true) (hy : binary32IsFinite y = true) :
    (x > y) ↔ binary32ToRat x > binary32ToRat y :=
  compareLess_iff_toRat_lt y x hy hx

/--
Decoded Model of Binary32 subtraction agrees with Model.sub.
-/
theorem toModel_sub (x y : Binary32) :
    ExecFloat.Binary.toModel (x - y) = Model.sub (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y) := by
  change ExecFloat.Binary.toModel (ExecFloat.sub x y) = _
  rw [ExecFloat.Proof.sub_eq_spec]
  change Configured.Family.toModel
    (ExecFloat.ModelCodec.liftBinary Model.Spec.sub x y) = _
  simp [Configured.Family.toModel, ExecFloat.Binary.toModel, Model.Proof.sub_eq_spec]

theorem toModel_zero : ExecFloat.Binary.toModel (0.0 : Binary32) = Model.posZero _ := by
  change Configured.Family.toModel (Configured.Family.ofModel (Model.roundRatQ _ (OfScientific.ofScientific 0 true 1 : Rat))) = _
  rw [Configured.Family.toModel_ofModel]
  have h_rat : (OfScientific.ofScientific 0 true 1 : Rat) = 0 := by norm_num
  rw [h_rat]
  unfold Model.roundRatQ Model.roundRatQWithRounding Model.roundRatWithRounding Model.roundRatWithRoundingScaled
  simp [Model.roundRatScaled, Model.ieeeRoundRatScaled]

/--
IEEE-754 0.0 in Binary32 is finite.
-/
theorem binary32_zero_isFinite : binary32IsFinite (0.0 : Binary32) = true := by
  unfold binary32IsFinite ExecFloat.Binary.isFinite
  rw [toModel_zero]
  exact Model.isFinite_posZero _

/--
Rational decoding of 0.0 in Binary32 is exactly 0.
-/
theorem binary32_zero_toRat : binary32ToRat (0.0 : Binary32) = 0 := by
  have h_fin := binary32_zero_isFinite
  have h_real := toReal_eq_cast_toRat (0.0 : Binary32) h_fin
  rw [toModel_zero, Model.toReal_posZero _ (by rfl)] at h_real
  exact_mod_cast h_real.symm

/--
2000 is well within the positive finite representable range of IEEE-754 formats of sufficient width.
-/
theorem two_thousand_le_posMaxFinite (fmt : FloatFormat)
    (hm : 2000 ≤ Model.pow2 fmt.fracWidth + fmt.maxFiniteFracField)
    (hexp : 0 ≤ fmt.maxNormalExponent - Int.ofNat fmt.fracWidth) :
    (2000 : ℝ) ≤ Model.toReal (Model.posMaxFinite fmt) := by
  have h := Model.abs_signed_mul_bpow_le_toReal_posMaxFinite fmt false 2000 0 hm hexp
  simp only [Bool.false_eq_true, ite_false, one_mul, Model.bpow_zero, mul_one] at h
  rw [abs_of_pos (by norm_num)] at h
  exact h

/--
Subtraction of two bounded finite Binary32 values does not overflow and remains finite.
-/
theorem binary32_sub_isFinite (a b : Binary32)
    (ha : binary32IsFinite a = true) (hb : binary32IsFinite b = true)
    (hbound_a : |binary32ToRat a| ≤ 1000) (hbound_b : |binary32ToRat b| ≤ 1000) :
    binary32IsFinite (b - a) = true := by
  unfold binary32IsFinite ExecFloat.Binary.isFinite
  rw [toModel_sub]
  apply Model.isFinite_sub_of_abs_add_le_posMaxFinite (ExecFloat.Binary.toModel b) (ExecFloat.Binary.toModel a) (by rfl) hb ha
  have h_le : |Model.toReal (ExecFloat.Binary.toModel b)| + |Model.toReal (ExecFloat.Binary.toModel a)| ≤ (2000 : ℝ) := by
    rw [toReal_eq_cast_toRat b hb, toReal_eq_cast_toRat a ha]
    have h1 : |((binary32ToRat b : ℚ) : ℝ)| ≤ (1000 : ℝ) := by
      rw [← Rat.cast_abs]
      exact_mod_cast hbound_b
    have h2 : |((binary32ToRat a : ℚ) : ℝ)| ≤ (1000 : ℝ) := by
      rw [← Rat.cast_abs]
      exact_mod_cast hbound_a
    linarith
  apply le_trans h_le
  apply two_thousand_le_posMaxFinite _ (by decide) (by decide)

/--
Decoded real value of Binary32 subtraction is exact real difference rounded once.
-/
theorem toReal_sub_eq_roundAt (a b : Binary32)
    (ha : binary32IsFinite a = true) (hb : binary32IsFinite b = true)
    (hbound_a : |binary32ToRat a| ≤ 1000) (hbound_b : |binary32ToRat b| ≤ 1000) :
    Model.toReal (ExecFloat.Binary.toModel (b - a)) =
      Model.roundAt FloatFormat.binary32 (Model.toReal (ExecFloat.Binary.toModel b) - Model.toReal (ExecFloat.Binary.toModel a)) := by
  rw [toModel_sub]
  have hfin : (Model.sub (ExecFloat.Binary.toModel b) (ExecFloat.Binary.toModel a)).isFinite = true := by
    have h := binary32_sub_isFinite a b ha hb hbound_a hbound_b
    unfold binary32IsFinite ExecFloat.Binary.isFinite at h
    rwa [toModel_sub] at h
  exact Model.toReal_sub_eq_roundAt (ExecFloat.Binary.toModel b) (ExecFloat.Binary.toModel a) (by rfl) hb ha hfin

/--
Nearest-even rounding of any real greater than or equal to posMinSubnormal is strictly positive.
-/
theorem roundAt_pos_of_ge_posMinSubnormal (fmt : FloatFormat) (r : ℝ)
    (hr : Model.toReal (Model.posMinSubnormal fmt) ≤ r) :
    0 < Model.roundAt fmt r := by
  have hgen : FloatLib.Floats.Formats.Flocq.genericFormat FloatLib.Numerics.binaryRadix (Model.fexpOf fmt) (Model.toReal (Model.posMinSubnormal fmt)) := by
    apply Model.toReal_genericFormat_of_isFinite
    exact Model.isFinite_posMinSubnormal fmt
  have hle := FloatLib.Floats.Formats.Flocq.generic_le_round FloatLib.Floats.Formats.Flocq.nearestEven hgen hr
  have hpos : 0 < Model.toReal (Model.posMinSubnormal fmt) := by
    rw [Model.toReal_posMinSubnormal]
    exact Model.bpow_pos fmt.minSubnormalExponent
  exact lt_of_lt_of_le hpos hle

/--
Real decoding of negMinSubnormal.
-/
theorem toReal_negMinSubnormal (fmt : FloatFormat) :
    Model.toReal (Model.negMinSubnormal fmt) = - Model.bpow fmt.minSubnormalExponent := by
  rw [← Model.neg_posMinSubnormal, Model.toReal_neg _ (Model.isFinite_posMinSubnormal fmt), Model.toReal_posMinSubnormal]

/--
Nearest-even rounding of any real less than or equal to negMinSubnormal is strictly negative.
-/
theorem roundAt_neg_of_le_negMinSubnormal (fmt : FloatFormat) (r : ℝ)
    (hr : r ≤ Model.toReal (Model.negMinSubnormal fmt)) :
    Model.roundAt fmt r < 0 := by
  rw [← neg_pos, ← Model.roundAt_neg]
  have hpos : Model.toReal (Model.posMinSubnormal fmt) ≤ -r := by
    rw [toReal_negMinSubnormal] at hr
    rw [Model.toReal_posMinSubnormal]
    linarith
  exact roundAt_pos_of_ge_posMinSubnormal fmt (-r) hpos

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

theorem toReal_posMinSubnormal_le_sub (a b : Binary32)
    (ha : binary32IsFinite a = true) (hb : binary32IsFinite b = true)
    (h : binary32ToRat a < binary32ToRat b) :
    Model.toReal (Model.posMinSubnormal FloatFormat.binary32) ≤
      Model.toReal (ExecFloat.Binary.toModel b) - Model.toReal (ExecFloat.Binary.toModel a) := by
  obtain ⟨na, hna⟩ := toReal_eq_int_mul_posMinSubnormal a ha
  obtain ⟨nb, hnb⟩ := toReal_eq_int_mul_posMinSubnormal b hb
  have h_lt_real : Model.toReal (ExecFloat.Binary.toModel a) < Model.toReal (ExecFloat.Binary.toModel b) := by
    rw [toReal_eq_cast_toRat a ha, toReal_eq_cast_toRat b hb]
    exact Rat.cast_lt.mpr h
  set u := Model.toReal (Model.posMinSubnormal FloatFormat.binary32) with hu_def
  have hu_pos : 0 < u := by
    rw [hu_def, Model.toReal_posMinSubnormal]
    exact Model.bpow_pos FloatFormat.binary32.minSubnormalExponent
  have h_mul_lt : (na : ℝ) * u < (nb : ℝ) * u := by
    rwa [hna, hnb] at h_lt_real
  have h_na_lt_nb_real : (na : ℝ) < (nb : ℝ) := (mul_lt_mul_iff_of_pos_right hu_pos).mp h_mul_lt
  have h_na_lt_nb : na < nb := by exact_mod_cast h_na_lt_nb_real
  have h_diff_ge_one : 1 ≤ nb - na := by omega
  have h_diff_ge_one_real : (1 : ℝ) ≤ ((nb - na : ℤ) : ℝ) := by exact_mod_cast h_diff_ge_one
  have h_le : 1 * u ≤ ((nb - na : ℤ) : ℝ) * u := mul_le_mul_of_nonneg_right h_diff_ge_one_real (le_of_lt hu_pos)
  rw [one_mul] at h_le
  have h_sub_eq : Model.toReal (ExecFloat.Binary.toModel b) - Model.toReal (ExecFloat.Binary.toModel a) =
      ((nb - na : ℤ) : ℝ) * u := by
    rw [hna, hnb]
    push_cast
    ring
  rw [h_sub_eq]
  exact h_le

/--
The sign of Binary32 subtraction matches the sign of exact rational subtraction.
-/
theorem binary32_sub_sign_eq (a b : Binary32)
    (ha : binary32IsFinite a = true) (hb : binary32IsFinite b = true)
    (hbound_a : |binary32ToRat a| ≤ 1000) (hbound_b : |binary32ToRat b| ≤ 1000) :
    (if b - a > 0.0 then 1 else if b - a < 0.0 then -1 else 0 : ℤ) =
    (if binary32ToRat b - binary32ToRat a > 0 then 1 else if binary32ToRat b - binary32ToRat a < 0 then -1 else 0 : ℤ) := by
  have hsub_fin : binary32IsFinite (b - a) = true := binary32_sub_isFinite a b ha hb hbound_a hbound_b
  have hzero_fin : binary32IsFinite (0.0 : Binary32) = true := binary32_zero_isFinite
  have hzero_rat : binary32ToRat (0.0 : Binary32) = 0 := binary32_zero_toRat
  have hgt_iff : (b - a > 0.0) ↔ binary32ToRat (b - a) > 0 := by
    have h := compareGreater_iff_toRat_gt (b - a) 0.0 hsub_fin hzero_fin
    rwa [hzero_rat] at h
  have hlt_iff : (b - a < 0.0) ↔ binary32ToRat (b - a) < 0 := by
    have h := compareLess_iff_toRat_lt (b - a) 0.0 hsub_fin hzero_fin
    rwa [hzero_rat] at h
  have htoReal_sub := toReal_sub_eq_roundAt a b ha hb hbound_a hbound_b
  have htoReal_ba := toReal_eq_cast_toRat (b - a) hsub_fin
  have htoReal_b := toReal_eq_cast_toRat b hb
  have htoReal_a := toReal_eq_cast_toRat a ha
  have h_cast_sub : Model.toReal (ExecFloat.Binary.toModel b) - Model.toReal (ExecFloat.Binary.toModel a) =
      (((binary32ToRat b - binary32ToRat a : ℚ) : ℝ)) := by
    rw [htoReal_b, htoReal_a]
    push_cast
    rfl
  rcases lt_trichotomy (binary32ToRat b) (binary32ToRat a) with hlt | heq | hgt
  · have h_diff_neg : binary32ToRat b - binary32ToRat a < 0 := sub_neg.mpr hlt
    have h_diff_not_pos : ¬(binary32ToRat b - binary32ToRat a > 0) := not_lt_of_gt h_diff_neg
    have h_ge_min : Model.toReal (Model.posMinSubnormal FloatFormat.binary32) ≤
        Model.toReal (ExecFloat.Binary.toModel a) - Model.toReal (ExecFloat.Binary.toModel b) :=
      toReal_posMinSubnormal_le_sub b a hb ha hlt
    have h_le_neg_min : Model.toReal (ExecFloat.Binary.toModel b) - Model.toReal (ExecFloat.Binary.toModel a) ≤
        Model.toReal (Model.negMinSubnormal FloatFormat.binary32) := by
      rw [toReal_negMinSubnormal]
      have h_pos_eq := Model.toReal_posMinSubnormal FloatFormat.binary32
      rw [h_pos_eq] at h_ge_min
      linarith
    have h_round_neg : Model.roundAt FloatFormat.binary32
        (Model.toReal (ExecFloat.Binary.toModel b) - Model.toReal (ExecFloat.Binary.toModel a)) < 0 :=
      roundAt_neg_of_le_negMinSubnormal FloatFormat.binary32 _ h_le_neg_min
    rw [← htoReal_sub] at h_round_neg
    rw [htoReal_ba] at h_round_neg
    have h_rat_neg : binary32ToRat (b - a) < 0 := Rat.cast_lt_zero.mp h_round_neg
    have h_lt : b - a < 0.0 := hlt_iff.mpr h_rat_neg
    have h_not_gt : ¬(b - a > 0.0) := by
      rw [hgt_iff]
      exact not_lt_of_gt h_rat_neg
    simp [h_lt, h_not_gt, h_diff_neg, h_diff_not_pos]
  · have h_diff : binary32ToRat b - binary32ToRat a = 0 := sub_eq_zero.mpr heq
    have h_round_zero : Model.toReal (ExecFloat.Binary.toModel (b - a)) = 0 := by
      rw [htoReal_sub, h_cast_sub, h_diff]
      push_cast
      exact Model.roundAt_zero FloatFormat.binary32
    have h_toRat_zero : binary32ToRat (b - a) = 0 := by
      rw [htoReal_ba] at h_round_zero
      exact Rat.cast_eq_zero.mp h_round_zero
    have h_not_gt : ¬(b - a > 0.0) := by
      rw [hgt_iff, h_toRat_zero]
      exact lt_irrefl 0
    have h_not_lt : ¬(b - a < 0.0) := by
      rw [hlt_iff, h_toRat_zero]
      exact lt_irrefl 0
    have h_not_gt_rat : ¬(binary32ToRat b - binary32ToRat a > 0) := by
      rw [h_diff]
      exact lt_irrefl 0
    have h_not_lt_rat : ¬(binary32ToRat b - binary32ToRat a < 0) := by
      rw [h_diff]
      exact lt_irrefl 0
    simp [h_not_gt, h_not_lt, h_not_gt_rat, h_not_lt_rat]
  · have h_diff_pos : binary32ToRat b - binary32ToRat a > 0 := sub_pos.mpr hgt
    have h_ge_min : Model.toReal (Model.posMinSubnormal FloatFormat.binary32) ≤
        Model.toReal (ExecFloat.Binary.toModel b) - Model.toReal (ExecFloat.Binary.toModel a) :=
      toReal_posMinSubnormal_le_sub a b ha hb hgt
    have h_round_pos : 0 < Model.roundAt FloatFormat.binary32
        (Model.toReal (ExecFloat.Binary.toModel b) - Model.toReal (ExecFloat.Binary.toModel a)) :=
      roundAt_pos_of_ge_posMinSubnormal FloatFormat.binary32 _ h_ge_min
    rw [← htoReal_sub] at h_round_pos
    rw [htoReal_ba] at h_round_pos
    have h_rat_pos : 0 < binary32ToRat (b - a) := Rat.cast_pos.mp h_round_pos
    have h_gt : b - a > 0.0 := hgt_iff.mpr h_rat_pos
    simp [h_gt, h_diff_pos]

/--
Step X sign agreement: The floating-point step direction along X matches the rational step direction.
-/
theorem step_signs_agree_X (A B : Point32)
    (h_finiteA : A.isFinite) (h_finiteB : B.isFinite)
    (h_bound : inCoordBounds 1000 A.toPoint B.toPoint) :
    (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0) =
    (if B.toPoint.x - A.toPoint.x > 0 then 1 else if B.toPoint.x - A.toPoint.x < 0 then -1 else 0) := by
  rcases h_bound with ⟨hAx, _, hBx, _⟩
  exact binary32_sub_sign_eq A.x B.x h_finiteA.1 h_finiteB.1 hAx hBx

/--
Step Y sign agreement: The floating-point step direction along Y matches the rational step direction.
-/
theorem step_signs_agree_Y (A B : Point32)
    (h_finiteA : A.isFinite) (h_finiteB : B.isFinite)
    (h_bound : inCoordBounds 1000 A.toPoint B.toPoint) :
    (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0) =
    (if B.toPoint.y - A.toPoint.y > 0 then 1 else if B.toPoint.y - A.toPoint.y < 0 then -1 else 0) := by
  rcases h_bound with ⟨_, hAy, _, hBy⟩
  exact binary32_sub_sign_eq A.y B.y h_finiteA.2 h_finiteB.2 hAy hBy

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
        (Configured.Family.ofModel (Model.roundRat FloatFormat.binary64 d.negative d.toRat.num.natAbs d.toRat.den))
        _ :=
    ExecFloat.Binary.Conversion.cast_eq_roundRat_of_decodeTo_eq_finite x (SignedRat.ofDyadic d) hdec
  unfold widen32To64
  change ExecFloat.Binary.toModel ((ExecFloat.cast (target := Binary64) x).value?.getD (0.0 : Binary64)) = _
  rw [hcast]
  change ExecFloat.Binary.toModel (Configured.Family.ofModel _) = _
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
Converting an integer with magnitude at most 1001 to Binary32 via intToBinary32 preserves its exact real value.
-/
theorem intToBinary32_toReal_eq (n : Int) (hn : |n| ≤ 1001) :
    Model.toReal (ExecFloat.Binary.toModel (intToBinary32 n)) = (n : ℝ) := by
  have h_toModel : ExecFloat.Binary.toModel (intToBinary32 n) =
      Model.roundDyadic FloatFormat.binary32 (Dyadic.ofScaledInt n 0) :=
    ExecFloat.Binary.toModel_ofFloat32_ofInt n
  have hrepr := Model.roundDyadic_of_representable FloatFormat.binary32 (by rfl)
    (Dyadic.ofScaledInt n 0) n.natAbs 0
    (by simp [Dyadic.ofScaledInt])
    (by
      have h1 : -1001 ≤ n ∧ n ≤ 1001 := abs_le.mp hn
      have h2 : n.natAbs ≤ 1001 := by omega
      change n.natAbs < 2 ^ 24
      omega)
    (by
      simp only [Dyadic.ofScaledInt]
      decide)
    (by
      rw [Model.Dyadic.toReal_ofScaledInt_zero]
      have h_le : |(n : ℝ)| ≤ (1001 : ℝ) := by
        rw [← Int.cast_abs]
        exact_mod_cast hn
      have h2000 : (1001 : ℝ) ≤ (2000 : ℝ) := by norm_num
      apply le_trans (le_trans h_le h2000)
      apply two_thousand_le_posMaxFinite _ (by decide) (by decide))
  calc
    Model.toReal (ExecFloat.Binary.toModel (intToBinary32 n)) =
        Model.toReal (Model.roundDyadic FloatFormat.binary32 (Dyadic.ofScaledInt n 0)) :=
      congrArg Model.toReal h_toModel
    _ = (Dyadic.ofScaledInt n 0).toReal := hrepr.2
    _ = (n : ℝ) := Model.Dyadic.toReal_ofScaledInt_zero n


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
private theorem rayMarchStepFloat_done_or_cases (start : Point32) (dx dy : Binary32) (stepX stepY : ℤ) (c : Cell) :
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





