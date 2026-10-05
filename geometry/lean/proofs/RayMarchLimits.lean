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
import GeometryDefs
import proofs.FloatAnalysis
import proofs.FloatProperties
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Instances
import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Mode

namespace Geometry

open FloatLib
open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange

theorem toReal_abs {fmt : FloatFormat} (x : Model fmt) (hfmt : fmt.isIEEE = true)
    (hx : Model.isFinite x = true) : Model.toReal (Model.abs x) = |Model.toReal x| := by
  have hsigned := FloatFormat.supportsSignedZero_eq_true_of_isIEEE fmt hfmt
  obtain ⟨d, hd⟩ := Model.exists_toDyadic?_of_isFinite hx
  have hsign := Model.sign_eq_signBit_of_toDyadic?_some hd
  have hreal : Model.toReal x = d.toReal := by simp [Model.toReal_eq, hd]
  have hp := FloatLib.Floats.Formats.Flocq.bpow.pos Numerics.binaryRadix d.exponent
  cases hs : Model.signBit x with
  | false =>
    have hn : 0 ≤ Model.toReal x := by
      rw [hreal]
      simp only [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand,
        hsign.trans hs, Bool.false_eq_true, ↓reduceIte]
      exact mul_nonneg (Nat.cast_nonneg _) hp.le
    simpa [Model.abs, Model.copySign, hsigned, hs] using (abs_of_nonneg hn).symm
  | true =>
    have hn : Model.toReal x ≤ 0 := by
      rw [hreal]
      simp only [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand,
        hsign.trans hs, ↓reduceIte, Int.cast_neg]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) hp.le
    have habs : Model.abs x = Model.neg x := by
      simp [Model.abs, Model.copySign, Model.neg, hsigned, hs]
    rw [habs, Model.toReal_neg x hx, abs_of_nonpos hn]

theorem toReal_sub_eq_roundAt_binary64 (x y : Binary64)
    (hx : ExecFloat.Binary.isFinite x = true) (hy : ExecFloat.Binary.isFinite y = true)
    (hbound : |Model.toReal (ExecFloat.Binary.toModel x)| + |Model.toReal (ExecFloat.Binary.toModel y)| ≤
              Model.toReal (Model.posMaxFinite FloatFormat.binary64)) :
    Model.toReal (ExecFloat.Binary.toModel (x - y)) =
      Model.roundAt FloatFormat.binary64
        (Model.toReal (ExecFloat.Binary.toModel x) - Model.toReal (ExecFloat.Binary.toModel y)) := by
  have hsub : ExecFloat.Binary.toModel (x - y) =
      Model.Spec.sub (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y) := by
    change ExecFloat.Binary.toModel (ExecFloat.sub x y) = _
    rw [ExecFloat.Proof.sub_eq_spec]
    change Configured.Family.toModel (ExecFloat.ModelCodec.liftBinary Model.Spec.sub x y) = _
    simp [Configured.Family.toModel, ExecFloat.Binary.toModel]
  rw [hsub]
  have hfin : Model.isFinite (Model.Spec.sub (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y)) = true := by
    rw [← Model.Proof.sub_eq_spec]
    apply Model.isFinite_sub_of_abs_add_le_posMaxFinite
      (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y) (by rfl) hx hy hbound
  rw [← Model.Proof.sub_eq_spec]
  exact Model.toReal_sub_eq_roundAt_of_abs_add_le_posMaxFinite
    (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y) (by rfl) hx hy hbound

theorem toReal_sub_mono_binary64 (x1 y1 x2 y2 : Binary64)
    (hx1 : ExecFloat.Binary.isFinite x1 = true) (hy1 : ExecFloat.Binary.isFinite y1 = true)
    (hx2 : ExecFloat.Binary.isFinite x2 = true) (hy2 : ExecFloat.Binary.isFinite y2 = true)
    (hbound1 : |Model.toReal (ExecFloat.Binary.toModel x1)| + |Model.toReal (ExecFloat.Binary.toModel y1)| ≤
               Model.toReal (Model.posMaxFinite FloatFormat.binary64))
    (hbound2 : |Model.toReal (ExecFloat.Binary.toModel x2)| + |Model.toReal (ExecFloat.Binary.toModel y2)| ≤
               Model.toReal (Model.posMaxFinite FloatFormat.binary64))
    (h_ge : Model.toReal (ExecFloat.Binary.toModel x1) - Model.toReal (ExecFloat.Binary.toModel y1) ≥
            Model.toReal (ExecFloat.Binary.toModel x2) - Model.toReal (ExecFloat.Binary.toModel y2)) :
    Model.toReal (ExecFloat.Binary.toModel (x1 - y1)) ≥
    Model.toReal (ExecFloat.Binary.toModel (x2 - y2)) := by
  rw [toReal_sub_eq_roundAt_binary64 x1 y1 hx1 hy1 hbound1]
  rw [toReal_sub_eq_roundAt_binary64 x2 y2 hx2 hy2 hbound2]
  exact Model.roundAt_mono FloatFormat.binary64 h_ge

theorem toReal_mul_mono_binary64
    (x y z : Binary64)
    (hx : ExecFloat.Binary.isFinite x = true)
    (hy : ExecFloat.Binary.isFinite y = true)
    (hz : ExecFloat.Binary.isFinite z = true)
    (h_xy : Model.toReal (ExecFloat.Binary.toModel x) ≥ Model.toReal (ExecFloat.Binary.toModel y))
    (hz_pos : Model.toReal (ExecFloat.Binary.toModel z) ≥ 0)
    (hprod_x : |Model.toReal (ExecFloat.Binary.toModel x)| * |Model.toReal (ExecFloat.Binary.toModel z)| ≤
               Model.toReal (Model.posMaxFinite FloatFormat.binary64))
    (hprod_y : |Model.toReal (ExecFloat.Binary.toModel y)| * |Model.toReal (ExecFloat.Binary.toModel z)| ≤
               Model.toReal (Model.posMaxFinite FloatFormat.binary64)) :
    Model.toReal (ExecFloat.Binary.toModel (x * z)) ≥
    Model.toReal (ExecFloat.Binary.toModel (y * z)) := by
  have hmul_x : Model.toReal (ExecFloat.Binary.toModel (x * z)) =
      Model.roundAt FloatFormat.binary64
        (Model.toReal (ExecFloat.Binary.toModel x) * Model.toReal (ExecFloat.Binary.toModel z)) := by
    change Model.toReal (ExecFloat.Binary.toModel (ExecFloat.Binary.mul x z Model.IEEERoundingMode.nearestEven)) = _
    rw [ExecFloat.Binary.toModel_mul]
    exact Model.toReal_mul_eq_roundAt_of_abs_mul_le_posMaxFinite
      (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel z) (by rfl) hx hz hprod_x
  have hmul_y : Model.toReal (ExecFloat.Binary.toModel (y * z)) =
      Model.roundAt FloatFormat.binary64
        (Model.toReal (ExecFloat.Binary.toModel y) * Model.toReal (ExecFloat.Binary.toModel z)) := by
    change Model.toReal (ExecFloat.Binary.toModel (ExecFloat.Binary.mul y z Model.IEEERoundingMode.nearestEven)) = _
    rw [ExecFloat.Binary.toModel_mul]
    exact Model.toReal_mul_eq_roundAt_of_abs_mul_le_posMaxFinite
      (ExecFloat.Binary.toModel y) (ExecFloat.Binary.toModel z) (by rfl) hy hz hprod_y
  rw [hmul_x, hmul_y]
  have hle : Model.toReal (ExecFloat.Binary.toModel y) * Model.toReal (ExecFloat.Binary.toModel z) ≤
             Model.toReal (ExecFloat.Binary.toModel x) * Model.toReal (ExecFloat.Binary.toModel z) := by
    nlinarith
  exact Model.roundAt_mono FloatFormat.binary64 hle

theorem ge_of_toReal_ge (x y : Binary64)
    (hx : ExecFloat.Binary.isFinite x = true)
    (hy : ExecFloat.Binary.isFinite y = true)
    (h_ge : Model.toReal (ExecFloat.Binary.toModel x) ≥ Model.toReal (ExecFloat.Binary.toModel y)) :
    x ≥ y := by
  have hx_fin : Model.isFinite (ExecFloat.Binary.toModel x) = true := hx
  have hy_fin : Model.isFinite (ExecFloat.Binary.toModel y) = true := hy
  change y ≤ x
  rcases lt_or_eq_of_le h_ge with hlt | heq
  · rw [ExecFloat.Binary.le_iff_compare_eq_lt_or_eq]
    left
    rw [Model.compare_eq_some_lt_iff_toReal_lt_of_isFinite
      (ExecFloat.Binary.toModel y) (ExecFloat.Binary.toModel x) hy_fin hx_fin]
    exact hlt
  · rw [ExecFloat.Binary.le_iff_compare_eq_lt_or_eq]
    right
    rw [Model.compare_eq_some_eq_iff_toReal_eq_of_isFinite
      (ExecFloat.Binary.toModel y) (ExecFloat.Binary.toModel x) hy_fin hx_fin]
    exact heq

theorem toReal_lt_of_lt_binary64 (x y : Binary64)
    (hx : ExecFloat.Binary.isFinite x = true)
    (hy : ExecFloat.Binary.isFinite y = true)
    (h : x < y) :
    Model.toReal (ExecFloat.Binary.toModel x) < Model.toReal (ExecFloat.Binary.toModel y) := by
  have hx_fin : Model.isFinite (ExecFloat.Binary.toModel x) = true := hx
  have hy_fin : Model.isFinite (ExecFloat.Binary.toModel y) = true := hy
  rw [ExecFloat.Binary.lt_iff_compare_eq_lt] at h
  rwa [Model.compare_eq_some_lt_iff_toReal_lt_of_isFinite
    (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y) hx_fin hy_fin] at h

theorem lt_of_toReal_lt_binary64 (x y : Binary64)
    (hx : ExecFloat.Binary.isFinite x = true)
    (hy : ExecFloat.Binary.isFinite y = true)
    (h : Model.toReal (ExecFloat.Binary.toModel x) < Model.toReal (ExecFloat.Binary.toModel y)) :
    x < y := by
  have hx_fin : Model.isFinite (ExecFloat.Binary.toModel x) = true := hx
  have hy_fin : Model.isFinite (ExecFloat.Binary.toModel y) = true := hy
  rw [ExecFloat.Binary.lt_iff_compare_eq_lt]
  rwa [Model.compare_eq_some_lt_iff_toReal_lt_of_isFinite
    (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y) hx_fin hy_fin]

theorem toReal_ge_of_ge_binary64 (x y : Binary64)
    (hx : ExecFloat.Binary.isFinite x = true)
    (hy : ExecFloat.Binary.isFinite y = true)
    (h : x ≥ y) :
    Model.toReal (ExecFloat.Binary.toModel x) ≥ Model.toReal (ExecFloat.Binary.toModel y) := by
  have hx_fin : Model.isFinite (ExecFloat.Binary.toModel x) = true := hx
  have hy_fin : Model.isFinite (ExecFloat.Binary.toModel y) = true := hy
  change y ≤ x at h
  rw [ExecFloat.Binary.le_iff_compare_eq_lt_or_eq] at h
  rcases h with hlt | heq
  · rw [Model.compare_eq_some_lt_iff_toReal_lt_of_isFinite
      (ExecFloat.Binary.toModel y) (ExecFloat.Binary.toModel x) hy_fin hx_fin] at hlt
    exact le_of_lt hlt
  · rw [Model.compare_eq_some_eq_iff_toReal_eq_of_isFinite
      (ExecFloat.Binary.toModel y) (ExecFloat.Binary.toModel x) hy_fin hx_fin] at heq
    exact le_of_eq heq

theorem trichotomy_of_isFinite_binary64 (x y : Binary64)
    (hx : ExecFloat.Binary.isFinite x = true)
    (hy : ExecFloat.Binary.isFinite y = true) :
    x < y ∨ y < x ∨
    Model.toReal (ExecFloat.Binary.toModel x) = Model.toReal (ExecFloat.Binary.toModel y) := by
  rcases lt_trichotomy
    (Model.toReal (ExecFloat.Binary.toModel x))
    (Model.toReal (ExecFloat.Binary.toModel y)) with hlt | heq | hgt
  · exact Or.inl (lt_of_toReal_lt_binary64 x y hx hy hlt)
  · exact Or.inr (Or.inr heq)
  · exact Or.inr (Or.inl (lt_of_toReal_lt_binary64 y x hy hx hgt))

theorem cross_ge_of_rem_ge
    (rem absDy absDx : Binary64)
    (hrem : ExecFloat.Binary.isFinite rem = true)
    (hdy : ExecFloat.Binary.isFinite absDy = true)
    (hdx : ExecFloat.Binary.isFinite absDx = true)
    (h_rem_dy : Model.toReal (ExecFloat.Binary.toModel rem) ≥ Model.toReal (ExecFloat.Binary.toModel absDy))
    (hdx_pos : Model.toReal (ExecFloat.Binary.toModel absDx) ≥ 0)
    (hprod1 : |Model.toReal (ExecFloat.Binary.toModel rem)| * |Model.toReal (ExecFloat.Binary.toModel absDx)| ≤
              Model.toReal (Model.posMaxFinite FloatFormat.binary64))
    (hprod2 : |Model.toReal (ExecFloat.Binary.toModel absDy)| * |Model.toReal (ExecFloat.Binary.toModel absDx)| ≤
              Model.toReal (Model.posMaxFinite FloatFormat.binary64))
    (hfin1 : ExecFloat.Binary.isFinite (rem * absDx) = true)
    (hfin2 : ExecFloat.Binary.isFinite (absDy * absDx) = true) :
    rem * absDx ≥ absDy * absDx := by
  have h_mono := toReal_mul_mono_binary64 rem absDy absDx hrem hdy hdx h_rem_dy hdx_pos hprod1 hprod2
  exact ge_of_toReal_ge (rem * absDx) (absDy * absDx) hfin1 hfin2 h_mono

theorem binary64_min_of_lt (x y : Binary64) (h : x < y) : min x y = x := by
  have h_lt : (ExecFloat.Binary.toModel x).compare (ExecFloat.Binary.toModel y) = some Ordering.lt :=
    ExecFloat.Binary.lt_iff_compare_eq_lt.mp h
  have h_both : Model.isNaN (ExecFloat.Binary.toModel x) = false ∧ Model.isNaN (ExecFloat.Binary.toModel y) = false := by
    have h_not := (Model.compare_eq_none_iff (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y)).not.mp
    rw [h_lt] at h_not
    simp only [not_or, Bool.not_eq_true] at h_not
    exact h_not (by intro; contradiction)
  have hchoose := Model.chooseNaN2_none_of_not_isNaN (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y) h_both.1 h_both.2
  have h_min : ExecFloat.Binary.toModel (min x y) = ExecFloat.Binary.toModel x := by
    rw [ExecFloat.Binary.toModel_min]
    simp [Model.minimum, hchoose, h_lt]
  rwa [← ExecFloat.Binary.toModel_inj]

theorem binary64_min_of_gt (x y : Binary64) (h : y < x) : min x y = y := by
  have h_lt : (ExecFloat.Binary.toModel y).compare (ExecFloat.Binary.toModel x) = some Ordering.lt :=
    ExecFloat.Binary.lt_iff_compare_eq_lt.mp h
  have h_both : Model.isNaN (ExecFloat.Binary.toModel x) = false ∧ Model.isNaN (ExecFloat.Binary.toModel y) = false := by
    have h_not := (Model.compare_eq_none_iff (ExecFloat.Binary.toModel y) (ExecFloat.Binary.toModel x)).not.mp
    rw [h_lt] at h_not
    simp only [not_or, Bool.not_eq_true] at h_not
    have := h_not (by intro; contradiction)
    exact ⟨this.2, this.1⟩
  obtain ⟨ex, hx⟩ := Model.exists_toEReal?_of_isNaN_eq_false _ h_both.1
  obtain ⟨ey, hy⟩ := Model.exists_toEReal?_of_isNaN_eq_false _ h_both.2
  have h_ey_lt_ex : ey < ex := (Model.compare_eq_some_lt_iff_toEReal_lt hy hx).mp h_lt
  have h_gt : (ExecFloat.Binary.toModel x).compare (ExecFloat.Binary.toModel y) = some Ordering.gt :=
    (Model.compare_eq_some_gt_iff_toEReal_gt hx hy).mpr h_ey_lt_ex
  have hchoose := Model.chooseNaN2_none_of_not_isNaN (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y) h_both.1 h_both.2
  have h_min : ExecFloat.Binary.toModel (min x y) = ExecFloat.Binary.toModel y := by
    rw [ExecFloat.Binary.toModel_min]
    simp [Model.minimum, hchoose, h_gt]
  rwa [← ExecFloat.Binary.toModel_inj]

theorem not_stepX_of_crossX_ge
    (crossX crossY limitCross : Binary64)
    (h_ge : crossX ≥ limitCross)
    (h_not_done : ¬ (min crossX crossY ≥ limitCross))
    (h_x : crossX < crossY) :
    False := by
  have h_min : min crossX crossY = crossX := binary64_min_of_lt crossX crossY h_x
  rw [h_min] at h_not_done
  exact h_not_done h_ge

theorem not_stepY_of_crossY_ge
    (crossX crossY limitCross : Binary64)
    (h_ge : crossY ≥ limitCross)
    (h_not_done : ¬ (min crossX crossY ≥ limitCross))
    (h_y : crossY < crossX) :
    False := by
  have h_min : min crossX crossY = crossY := binary64_min_of_gt crossX crossY h_y
  rw [h_min] at h_not_done
  exact h_not_done h_ge

theorem step_at_ge_limitCross_X_of_ne
    (start : Point32) (dx dy : Binary32) (stepX stepY : ℤ) (c : Cell)
    (hx0 : (stepX == 0) = false) (hy0 : (stepY == 0) = false) :
    let currentX := if stepX > 0 then c.x + 1 else c.x
    let currentY := if stepY > 0 then c.y + 1 else c.y
    let xb : Binary64 := widen32To64 (intToBinary32 currentX)
    let yb : Binary64 := widen32To64 (intToBinary32 currentY)
    let startX : Binary64 := widen32To64 start.x
    let startY : Binary64 := widen32To64 start.y
    let absDx : Binary64 := ExecFloat.Binary.abs (widen32To64 dx)
    let absDy : Binary64 := ExecFloat.Binary.abs (widen32To64 dy)
    let remX : Binary64 := ExecFloat.Binary.abs (xb - startX)
    let remY : Binary64 := ExecFloat.Binary.abs (yb - startY)
    let crossX : Binary64 := remX * absDy
    let crossY : Binary64 := remY * absDx
    let limitCross : Binary64 := absDx * absDy
    (crossX ≥ limitCross) →
    crossX < crossY ∨ crossY < crossX →
    (rayMarchStepFloat start dx dy stepX stepY c).2 = true ∨
    (rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x, c.y + stepY⟩ := by
  intro currentX currentY xb yb startX startY absDx absDy remX remY crossX crossY limitCross h_ge h_cases
  unfold rayMarchStepFloat
  rw [hx0, hy0]
  simp only [Bool.false_eq_true, ite_false]
  change (if (crossX ⊓ crossY ≥ limitCross) then (c, true)
          else if crossX < crossY then (⟨c.x + stepX, c.y⟩, false)
          else if crossY < crossX then (⟨c.x, c.y + stepY⟩, false)
          else (⟨c.x + stepX, c.y + stepY⟩, false)).2 = true ∨
         (if (crossX ⊓ crossY ≥ limitCross) then (c, true)
          else if crossX < crossY then (⟨c.x + stepX, c.y⟩, false)
          else if crossY < crossX then (⟨c.x, c.y + stepY⟩, false)
          else (⟨c.x + stepX, c.y + stepY⟩, false)).1 = ⟨c.x, c.y + stepY⟩
  split_ifs with h_done h_x h_y
  · left; rfl
  · exfalso
    exact not_stepX_of_crossX_ge crossX crossY limitCross h_ge h_done h_x
  · right; rfl
  · rcases h_cases with hx' | hy'
    · exfalso; exact h_x hx'
    · exfalso; exact h_y hy'

theorem step_at_ge_limitCross_Y_of_ne
    (start : Point32) (dx dy : Binary32) (stepX stepY : ℤ) (c : Cell)
    (hx0 : (stepX == 0) = false) (hy0 : (stepY == 0) = false) :
    let currentX := if stepX > 0 then c.x + 1 else c.x
    let currentY := if stepY > 0 then c.y + 1 else c.y
    let xb : Binary64 := widen32To64 (intToBinary32 currentX)
    let yb : Binary64 := widen32To64 (intToBinary32 currentY)
    let startX : Binary64 := widen32To64 start.x
    let startY : Binary64 := widen32To64 start.y
    let absDx : Binary64 := ExecFloat.Binary.abs (widen32To64 dx)
    let absDy : Binary64 := ExecFloat.Binary.abs (widen32To64 dy)
    let remX : Binary64 := ExecFloat.Binary.abs (xb - startX)
    let remY : Binary64 := ExecFloat.Binary.abs (yb - startY)
    let crossX : Binary64 := remX * absDy
    let crossY : Binary64 := remY * absDx
    let limitCross : Binary64 := absDx * absDy
    (crossY ≥ limitCross) →
    crossX < crossY ∨ crossY < crossX →
    (rayMarchStepFloat start dx dy stepX stepY c).2 = true ∨
    (rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x + stepX, c.y⟩ := by
  intro currentX currentY xb yb startX startY absDx absDy remX remY crossX crossY limitCross h_ge h_cases
  unfold rayMarchStepFloat
  rw [hx0, hy0]
  simp only [Bool.false_eq_true, ite_false]
  change (if (crossX ⊓ crossY ≥ limitCross) then (c, true)
          else if crossX < crossY then (⟨c.x + stepX, c.y⟩, false)
          else if crossY < crossX then (⟨c.x, c.y + stepY⟩, false)
          else (⟨c.x + stepX, c.y + stepY⟩, false)).2 = true ∨
         (if (crossX ⊓ crossY ≥ limitCross) then (c, true)
          else if crossX < crossY then (⟨c.x + stepX, c.y⟩, false)
          else if crossY < crossX then (⟨c.x, c.y + stepY⟩, false)
          else (⟨c.x + stepX, c.y + stepY⟩, false)).1 = ⟨c.x + stepX, c.y⟩
  split_ifs with h_done h_x h_y
  · left; rfl
  · right; rfl
  · exfalso
    exact not_stepY_of_crossY_ge crossX crossY limitCross h_ge h_done h_y
  · rcases h_cases with hx' | hy'
    · exfalso; exact h_x hx'
    · exfalso; exact h_y hy'

theorem step_done_of_both_ge
    (start : Point32) (dx dy : Binary32) (stepX stepY : ℤ) (c : Cell)
    (hx0 : (stepX == 0) = false) (hy0 : (stepY == 0) = false) :
    let currentX := if stepX > 0 then c.x + 1 else c.x
    let currentY := if stepY > 0 then c.y + 1 else c.y
    let xb : Binary64 := widen32To64 (intToBinary32 currentX)
    let yb : Binary64 := widen32To64 (intToBinary32 currentY)
    let startX : Binary64 := widen32To64 start.x
    let startY : Binary64 := widen32To64 start.y
    let absDx : Binary64 := ExecFloat.Binary.abs (widen32To64 dx)
    let absDy : Binary64 := ExecFloat.Binary.abs (widen32To64 dy)
    let remX : Binary64 := ExecFloat.Binary.abs (xb - startX)
    let remY : Binary64 := ExecFloat.Binary.abs (yb - startY)
    let crossX : Binary64 := remX * absDy
    let crossY : Binary64 := remY * absDx
    let limitCross : Binary64 := absDx * absDy
    (crossX ≥ limitCross) →
    (crossY ≥ limitCross) →
    crossX < crossY ∨ crossY < crossX →
    (rayMarchStepFloat start dx dy stepX stepY c).2 = true := by
  intro currentX currentY xb yb startX startY absDx absDy remX remY crossX crossY limitCross hx_ge hy_ge h_cases
  have h1 := step_at_ge_limitCross_X_of_ne start dx dy stepX stepY c hx0 hy0 hx_ge h_cases
  have h2 := step_at_ge_limitCross_Y_of_ne start dx dy stepX stepY c hx0 hy0 hy_ge h_cases
  rcases h1 with h1_done | h1_step
  · exact h1_done
  · rcases h2 with h2_done | h2_step
    · exact h2_done
    · exfalso
      have heq : (⟨c.x, c.y + stepY⟩ : Cell) = ⟨c.x + stepX, c.y⟩ := by
        rw [← h1_step, h2_step]
      have hx_eq := congr_arg Cell.x heq
      dsimp only [] at hx_eq
      have hx_ne : stepX ≠ 0 := by
        intro h
        have : (stepX == 0) = true := by rw [h]; rfl
        rw [this] at hx0; contradiction
      omega

theorem rayMarchStepFloat_he1_h_step
    (start : Point32) (dx dy : Binary32) (stepX stepY : ℤ) (startCell endCell : Cell)
    (hx0 : (stepX == 0) = false) (hy0 : (stepY == 0) = false)
    (he1 : endCell = ⟨startCell.x + stepX, startCell.y⟩)
    (hy_ge :
      let currentY := if stepY > 0 then startCell.y + 1 else startCell.y
      let yb : Binary64 := widen32To64 (intToBinary32 currentY)
      let startY : Binary64 := widen32To64 start.y
      let absDx : Binary64 := ExecFloat.Binary.abs (widen32To64 dx)
      let absDy : Binary64 := ExecFloat.Binary.abs (widen32To64 dy)
      let remY : Binary64 := ExecFloat.Binary.abs (yb - startY)
      let crossY : Binary64 := remY * absDx
      let limitCross : Binary64 := absDx * absDy
      crossY ≥ limitCross)
    (h_cases :
      let currentX := if stepX > 0 then startCell.x + 1 else startCell.x
      let currentY := if stepY > 0 then startCell.y + 1 else startCell.y
      let xb : Binary64 := widen32To64 (intToBinary32 currentX)
      let yb : Binary64 := widen32To64 (intToBinary32 currentY)
      let startX : Binary64 := widen32To64 start.x
      let startY : Binary64 := widen32To64 start.y
      let absDx : Binary64 := ExecFloat.Binary.abs (widen32To64 dx)
      let absDy : Binary64 := ExecFloat.Binary.abs (widen32To64 dy)
      let remX : Binary64 := ExecFloat.Binary.abs (xb - startX)
      let remY : Binary64 := ExecFloat.Binary.abs (yb - startY)
      let crossX : Binary64 := remX * absDy
      let crossY : Binary64 := remY * absDx
      crossX < crossY ∨ crossY < crossX) :
    (rayMarchStepFloat start dx dy stepX stepY startCell).2 = true ∨
    (rayMarchStepFloat start dx dy stepX stepY startCell).1 = endCell := by
  have h := step_at_ge_limitCross_Y_of_ne start dx dy stepX stepY startCell hx0 hy0 hy_ge h_cases
  rw [he1]
  exact h

theorem rayMarchStepFloat_he2_h_step
    (start : Point32) (dx dy : Binary32) (stepX stepY : ℤ) (startCell endCell : Cell)
    (hx0 : (stepX == 0) = false) (hy0 : (stepY == 0) = false)
    (he2 : endCell = ⟨startCell.x, startCell.y + stepY⟩)
    (hx_ge :
      let currentX := if stepX > 0 then startCell.x + 1 else startCell.x
      let xb : Binary64 := widen32To64 (intToBinary32 currentX)
      let startX : Binary64 := widen32To64 start.x
      let absDx : Binary64 := ExecFloat.Binary.abs (widen32To64 dx)
      let absDy : Binary64 := ExecFloat.Binary.abs (widen32To64 dy)
      let remX : Binary64 := ExecFloat.Binary.abs (xb - startX)
      let crossX : Binary64 := remX * absDy
      let limitCross : Binary64 := absDx * absDy
      crossX ≥ limitCross)
    (h_cases :
      let currentX := if stepX > 0 then startCell.x + 1 else startCell.x
      let currentY := if stepY > 0 then startCell.y + 1 else startCell.y
      let xb : Binary64 := widen32To64 (intToBinary32 currentX)
      let yb : Binary64 := widen32To64 (intToBinary32 currentY)
      let startX : Binary64 := widen32To64 start.x
      let startY : Binary64 := widen32To64 start.y
      let absDx : Binary64 := ExecFloat.Binary.abs (widen32To64 dx)
      let absDy : Binary64 := ExecFloat.Binary.abs (widen32To64 dy)
      let remX : Binary64 := ExecFloat.Binary.abs (xb - startX)
      let remY : Binary64 := ExecFloat.Binary.abs (yb - startY)
      let crossX : Binary64 := remX * absDy
      let crossY : Binary64 := remY * absDx
      crossX < crossY ∨ crossY < crossX) :
    (rayMarchStepFloat start dx dy stepX stepY startCell).2 = true ∨
    (rayMarchStepFloat start dx dy stepX stepY startCell).1 = endCell := by
  have h := step_at_ge_limitCross_X_of_ne start dx dy stepX stepY startCell hx0 hy0 hx_ge h_cases
  rw [he2]
  exact h

theorem rayMarchStepFloat_case8_hs2_done
    (A : Point32) (dx dy : Binary32) (stepX stepY : ℤ) (startCell : Cell)
    (hx0 : (stepX == 0) = false) (hy0 : (stepY == 0) = false)
    (h_crossX :
      let currentX := if stepX > 0 then (startCell.x + 2 * stepX) + 1 else startCell.x + 2 * stepX
      let xb : Binary64 := widen32To64 (intToBinary32 currentX)
      let startX : Binary64 := widen32To64 A.x
      let absDx : Binary64 := ExecFloat.Binary.abs (widen32To64 dx)
      let absDy : Binary64 := ExecFloat.Binary.abs (widen32To64 dy)
      let remX : Binary64 := ExecFloat.Binary.abs (xb - startX)
      let crossX : Binary64 := remX * absDy
      let limitCross : Binary64 := absDx * absDy
      crossX ≥ limitCross)
    (h_cases :
      let currentX := if stepX > 0 then (startCell.x + 2 * stepX) + 1 else startCell.x + 2 * stepX
      let currentY := if stepY > 0 then startCell.y + 1 else startCell.y
      let xb : Binary64 := widen32To64 (intToBinary32 currentX)
      let yb : Binary64 := widen32To64 (intToBinary32 currentY)
      let startX : Binary64 := widen32To64 A.x
      let startY : Binary64 := widen32To64 A.y
      let absDx : Binary64 := ExecFloat.Binary.abs (widen32To64 dx)
      let absDy : Binary64 := ExecFloat.Binary.abs (widen32To64 dy)
      let remX : Binary64 := ExecFloat.Binary.abs (xb - startX)
      let remY : Binary64 := ExecFloat.Binary.abs (yb - startY)
      let crossX : Binary64 := remX * absDy
      let crossY : Binary64 := remY * absDx
      crossX < crossY ∨ crossY < crossX) :
    (rayMarchStepFloat A dx dy stepX stepY (rayMarchStepFloat A dx dy stepX stepY startCell).1).2 = true ∨
    (rayMarchStepFloat A dx dy stepX stepY ⟨startCell.x + 2 * stepX, startCell.y⟩).2 = true ∨
    (rayMarchStepFloat A dx dy stepX stepY ⟨startCell.x + 2 * stepX, startCell.y⟩).1 =
      ⟨startCell.x + 2 * stepX, startCell.y + stepY⟩ := by
  right
  exact step_at_ge_limitCross_X_of_ne A dx dy stepX stepY ⟨startCell.x + 2 * stepX, startCell.y⟩ hx0 hy0 h_crossX h_cases

theorem rayMarchStepFloat_case8_hs3_done
    (A : Point32) (dx dy : Binary32) (stepX stepY : ℤ) (startCell : Cell)
    (hx0 : (stepX == 0) = false) (hy0 : (stepY == 0) = false)
    (hx_ge :
      let currentX := if stepX > 0 then (startCell.x + 2 * stepX) + 1 else startCell.x + 2 * stepX
      let xb : Binary64 := widen32To64 (intToBinary32 currentX)
      let startX : Binary64 := widen32To64 A.x
      let absDx : Binary64 := ExecFloat.Binary.abs (widen32To64 dx)
      let absDy : Binary64 := ExecFloat.Binary.abs (widen32To64 dy)
      let remX : Binary64 := ExecFloat.Binary.abs (xb - startX)
      let crossX : Binary64 := remX * absDy
      let limitCross : Binary64 := absDx * absDy
      crossX ≥ limitCross)
    (hy_ge :
      let currentY := if stepY > 0 then (startCell.y + stepY) + 1 else startCell.y + stepY
      let yb : Binary64 := widen32To64 (intToBinary32 currentY)
      let startY : Binary64 := widen32To64 A.y
      let absDx : Binary64 := ExecFloat.Binary.abs (widen32To64 dx)
      let absDy : Binary64 := ExecFloat.Binary.abs (widen32To64 dy)
      let remY : Binary64 := ExecFloat.Binary.abs (yb - startY)
      let crossY : Binary64 := remY * absDx
      let limitCross : Binary64 := absDx * absDy
      crossY ≥ limitCross)
    (h_cases :
      let currentX := if stepX > 0 then (startCell.x + 2 * stepX) + 1 else startCell.x + 2 * stepX
      let currentY := if stepY > 0 then (startCell.y + stepY) + 1 else startCell.y + stepY
      let xb : Binary64 := widen32To64 (intToBinary32 currentX)
      let yb : Binary64 := widen32To64 (intToBinary32 currentY)
      let startX : Binary64 := widen32To64 A.x
      let startY : Binary64 := widen32To64 A.y
      let absDx : Binary64 := ExecFloat.Binary.abs (widen32To64 dx)
      let absDy : Binary64 := ExecFloat.Binary.abs (widen32To64 dy)
      let remX : Binary64 := ExecFloat.Binary.abs (xb - startX)
      let remY : Binary64 := ExecFloat.Binary.abs (yb - startY)
      let crossX : Binary64 := remX * absDy
      let crossY : Binary64 := remY * absDx
      crossX < crossY ∨ crossY < crossX) :
    (rayMarchStepFloat A dx dy stepX stepY ⟨startCell.x + 2 * stepX, startCell.y + stepY⟩).2 = true := by
  exact step_done_of_both_ge A dx dy stepX stepY ⟨startCell.x + 2 * stepX, startCell.y + stepY⟩ hx0 hy0 hx_ge hy_ge h_cases

theorem rayMarchStepFloat_case9_hs2_done
    (A : Point32) (dx dy : Binary32) (stepX stepY : ℤ) (startCell : Cell)
    (hx0 : (stepX == 0) = false) (hy0 : (stepY == 0) = false)
    (hx_ge :
      let currentX := if stepX > 0 then (startCell.x + 2 * stepX) + 1 else startCell.x + 2 * stepX
      let xb : Binary64 := widen32To64 (intToBinary32 currentX)
      let startX : Binary64 := widen32To64 A.x
      let absDx : Binary64 := ExecFloat.Binary.abs (widen32To64 dx)
      let absDy : Binary64 := ExecFloat.Binary.abs (widen32To64 dy)
      let remX : Binary64 := ExecFloat.Binary.abs (xb - startX)
      let crossX : Binary64 := remX * absDy
      let limitCross : Binary64 := absDx * absDy
      crossX ≥ limitCross)
    (hy_ge :
      let currentY := if stepY > 0 then (startCell.y + stepY) + 1 else startCell.y + stepY
      let yb : Binary64 := widen32To64 (intToBinary32 currentY)
      let startY : Binary64 := widen32To64 A.y
      let absDx : Binary64 := ExecFloat.Binary.abs (widen32To64 dx)
      let absDy : Binary64 := ExecFloat.Binary.abs (widen32To64 dy)
      let remY : Binary64 := ExecFloat.Binary.abs (yb - startY)
      let crossY : Binary64 := remY * absDx
      let limitCross : Binary64 := absDx * absDy
      crossY ≥ limitCross)
    (h_cases :
      let currentX := if stepX > 0 then (startCell.x + 2 * stepX) + 1 else startCell.x + 2 * stepX
      let currentY := if stepY > 0 then (startCell.y + stepY) + 1 else startCell.y + stepY
      let xb : Binary64 := widen32To64 (intToBinary32 currentX)
      let yb : Binary64 := widen32To64 (intToBinary32 currentY)
      let startX : Binary64 := widen32To64 A.x
      let startY : Binary64 := widen32To64 A.y
      let absDx : Binary64 := ExecFloat.Binary.abs (widen32To64 dx)
      let absDy : Binary64 := ExecFloat.Binary.abs (widen32To64 dy)
      let remX : Binary64 := ExecFloat.Binary.abs (xb - startX)
      let remY : Binary64 := ExecFloat.Binary.abs (yb - startY)
      let crossX : Binary64 := remX * absDy
      let crossY : Binary64 := remY * absDx
      crossX < crossY ∨ crossY < crossX) :
    (rayMarchStepFloat A dx dy stepX stepY (rayMarchStepFloat A dx dy stepX stepY startCell).1).2 = true ∨
    (rayMarchStepFloat A dx dy stepX stepY ⟨startCell.x + 2 * stepX, startCell.y + stepY⟩).2 = true := by
  right
  exact step_done_of_both_ge A dx dy stepX stepY ⟨startCell.x + 2 * stepX, startCell.y + stepY⟩ hx0 hy0 hx_ge hy_ge h_cases

theorem rayMarchStepFloat_case10_hs2_done
    (A : Point32) (dx dy : Binary32) (stepX stepY : ℤ) (startCell : Cell)
    (hx0 : (stepX == 0) = false) (hy0 : (stepY == 0) = false)
    (hy_ge :
      let currentY := if stepY > 0 then (startCell.y + 2 * stepY) + 1 else startCell.y + 2 * stepY
      let yb : Binary64 := widen32To64 (intToBinary32 currentY)
      let startY : Binary64 := widen32To64 A.y
      let absDx : Binary64 := ExecFloat.Binary.abs (widen32To64 dx)
      let absDy : Binary64 := ExecFloat.Binary.abs (widen32To64 dy)
      let remY : Binary64 := ExecFloat.Binary.abs (yb - startY)
      let crossY : Binary64 := remY * absDx
      let limitCross : Binary64 := absDx * absDy
      crossY ≥ limitCross)
    (h_cases :
      let currentX := if stepX > 0 then startCell.x + 1 else startCell.x
      let currentY := if stepY > 0 then (startCell.y + 2 * stepY) + 1 else startCell.y + 2 * stepY
      let xb : Binary64 := widen32To64 (intToBinary32 currentX)
      let yb : Binary64 := widen32To64 (intToBinary32 currentY)
      let startX : Binary64 := widen32To64 A.x
      let startY : Binary64 := widen32To64 A.y
      let absDx : Binary64 := ExecFloat.Binary.abs (widen32To64 dx)
      let absDy : Binary64 := ExecFloat.Binary.abs (widen32To64 dy)
      let remX : Binary64 := ExecFloat.Binary.abs (xb - startX)
      let remY : Binary64 := ExecFloat.Binary.abs (yb - startY)
      let crossX : Binary64 := remX * absDy
      let crossY : Binary64 := remY * absDx
      crossX < crossY ∨ crossY < crossX) :
    (rayMarchStepFloat A dx dy stepX stepY (rayMarchStepFloat A dx dy stepX stepY startCell).1).2 = true ∨
    (rayMarchStepFloat A dx dy stepX stepY ⟨startCell.x, startCell.y + 2 * stepY⟩).2 = true ∨
    (rayMarchStepFloat A dx dy stepX stepY ⟨startCell.x, startCell.y + 2 * stepY⟩).1 =
      ⟨startCell.x + stepX, startCell.y + 2 * stepY⟩ := by
  right
  exact step_at_ge_limitCross_Y_of_ne A dx dy stepX stepY ⟨startCell.x, startCell.y + 2 * stepY⟩ hx0 hy0 hy_ge h_cases

theorem rayMarchStepFloat_case10_hs3_done
    (A : Point32) (dx dy : Binary32) (stepX stepY : ℤ) (startCell : Cell)
    (hx0 : (stepX == 0) = false) (hy0 : (stepY == 0) = false)
    (hx_ge :
      let currentX := if stepX > 0 then (startCell.x + stepX) + 1 else startCell.x + stepX
      let xb : Binary64 := widen32To64 (intToBinary32 currentX)
      let startX : Binary64 := widen32To64 A.x
      let absDx : Binary64 := ExecFloat.Binary.abs (widen32To64 dx)
      let absDy : Binary64 := ExecFloat.Binary.abs (widen32To64 dy)
      let remX : Binary64 := ExecFloat.Binary.abs (xb - startX)
      let crossX : Binary64 := remX * absDy
      let limitCross : Binary64 := absDx * absDy
      crossX ≥ limitCross)
    (hy_ge :
      let currentY := if stepY > 0 then (startCell.y + 2 * stepY) + 1 else startCell.y + 2 * stepY
      let yb : Binary64 := widen32To64 (intToBinary32 currentY)
      let startY : Binary64 := widen32To64 A.y
      let absDx : Binary64 := ExecFloat.Binary.abs (widen32To64 dx)
      let absDy : Binary64 := ExecFloat.Binary.abs (widen32To64 dy)
      let remY : Binary64 := ExecFloat.Binary.abs (yb - startY)
      let crossY : Binary64 := remY * absDx
      let limitCross : Binary64 := absDx * absDy
      crossY ≥ limitCross)
    (h_cases :
      let currentX := if stepX > 0 then (startCell.x + stepX) + 1 else startCell.x + stepX
      let currentY := if stepY > 0 then (startCell.y + 2 * stepY) + 1 else startCell.y + 2 * stepY
      let xb : Binary64 := widen32To64 (intToBinary32 currentX)
      let yb : Binary64 := widen32To64 (intToBinary32 currentY)
      let startX : Binary64 := widen32To64 A.x
      let startY : Binary64 := widen32To64 A.y
      let absDx : Binary64 := ExecFloat.Binary.abs (widen32To64 dx)
      let absDy : Binary64 := ExecFloat.Binary.abs (widen32To64 dy)
      let remX : Binary64 := ExecFloat.Binary.abs (xb - startX)
      let remY : Binary64 := ExecFloat.Binary.abs (yb - startY)
      let crossX : Binary64 := remX * absDy
      let crossY : Binary64 := remY * absDx
      crossX < crossY ∨ crossY < crossX) :
    (rayMarchStepFloat A dx dy stepX stepY ⟨startCell.x + stepX, startCell.y + 2 * stepY⟩).2 = true := by
  exact step_done_of_both_ge A dx dy stepX stepY ⟨startCell.x + stepX, startCell.y + 2 * stepY⟩ hx0 hy0 hx_ge hy_ge h_cases

theorem rayMarchStepFloat_case11_hs2_done
    (A : Point32) (dx dy : Binary32) (stepX stepY : ℤ) (startCell : Cell)
    (hx0 : (stepX == 0) = false) (hy0 : (stepY == 0) = false)
    (hx_ge :
      let currentX := if stepX > 0 then (startCell.x + stepX) + 1 else startCell.x + stepX
      let xb : Binary64 := widen32To64 (intToBinary32 currentX)
      let startX : Binary64 := widen32To64 A.x
      let absDx : Binary64 := ExecFloat.Binary.abs (widen32To64 dx)
      let absDy : Binary64 := ExecFloat.Binary.abs (widen32To64 dy)
      let remX : Binary64 := ExecFloat.Binary.abs (xb - startX)
      let crossX : Binary64 := remX * absDy
      let limitCross : Binary64 := absDx * absDy
      crossX ≥ limitCross)
    (hy_ge :
      let currentY := if stepY > 0 then (startCell.y + 2 * stepY) + 1 else startCell.y + 2 * stepY
      let yb : Binary64 := widen32To64 (intToBinary32 currentY)
      let startY : Binary64 := widen32To64 A.y
      let absDx : Binary64 := ExecFloat.Binary.abs (widen32To64 dx)
      let absDy : Binary64 := ExecFloat.Binary.abs (widen32To64 dy)
      let remY : Binary64 := ExecFloat.Binary.abs (yb - startY)
      let crossY : Binary64 := remY * absDx
      let limitCross : Binary64 := absDx * absDy
      crossY ≥ limitCross)
    (h_cases :
      let currentX := if stepX > 0 then (startCell.x + stepX) + 1 else startCell.x + stepX
      let currentY := if stepY > 0 then (startCell.y + 2 * stepY) + 1 else startCell.y + 2 * stepY
      let xb : Binary64 := widen32To64 (intToBinary32 currentX)
      let yb : Binary64 := widen32To64 (intToBinary32 currentY)
      let startX : Binary64 := widen32To64 A.x
      let startY : Binary64 := widen32To64 A.y
      let absDx : Binary64 := ExecFloat.Binary.abs (widen32To64 dx)
      let absDy : Binary64 := ExecFloat.Binary.abs (widen32To64 dy)
      let remX : Binary64 := ExecFloat.Binary.abs (xb - startX)
      let remY : Binary64 := ExecFloat.Binary.abs (yb - startY)
      let crossX : Binary64 := remX * absDy
      let crossY : Binary64 := remY * absDx
      crossX < crossY ∨ crossY < crossX) :
    (rayMarchStepFloat A dx dy stepX stepY (rayMarchStepFloat A dx dy stepX stepY startCell).1).2 = true ∨
    (rayMarchStepFloat A dx dy stepX stepY ⟨startCell.x + stepX, startCell.y + 2 * stepY⟩).2 = true := by
  right
  exact step_done_of_both_ge A dx dy stepX stepY ⟨startCell.x + stepX, startCell.y + 2 * stepY⟩ hx0 hy0 hx_ge hy_ge h_cases

theorem four_million_le_posMaxFinite_loc (fmt : FloatFormat)
    (hm : 4000000 ≤ Model.pow2 fmt.fracWidth + fmt.maxFiniteFracField)
    (hexp : 0 ≤ fmt.maxNormalExponent - Int.ofNat fmt.fracWidth) :
    (4000000 : ℝ) ≤ Model.toReal (Model.posMaxFinite fmt) := by
  have h := Model.abs_signed_mul_bpow_le_toReal_posMaxFinite fmt false 4000000 0 hm hexp
  simp only [Bool.false_eq_true, ite_false, one_mul, Model.bpow_zero, mul_one] at h
  rw [abs_of_pos (by norm_num)] at h
  exact h

theorem binary64_mul_isFinite_of_le_2000_loc (x y : Binary64)
    (hx : ExecFloat.Binary.isFinite x = true)
    (hy : ExecFloat.Binary.isFinite y = true)
    (hx_le : |Model.toReal (ExecFloat.Binary.toModel x)| ≤ 2000)
    (hy_le : |Model.toReal (ExecFloat.Binary.toModel y)| ≤ 2000) :
    ExecFloat.Binary.isFinite (x * y) = true ∧
    |Model.toReal (ExecFloat.Binary.toModel x)| * |Model.toReal (ExecFloat.Binary.toModel y)| ≤
      Model.toReal (Model.posMaxFinite FloatFormat.binary64) := by
  have hx_pos : 0 ≤ |Model.toReal (ExecFloat.Binary.toModel x)| := abs_nonneg _
  have hy_pos : 0 ≤ |Model.toReal (ExecFloat.Binary.toModel y)| := abs_nonneg _
  have hprod_le : |Model.toReal (ExecFloat.Binary.toModel x)| * |Model.toReal (ExecFloat.Binary.toModel y)| ≤ (4000000 : ℝ) := by
    nlinarith
  have hmax : (4000000 : ℝ) ≤ Model.toReal (Model.posMaxFinite FloatFormat.binary64) :=
    four_million_le_posMaxFinite_loc FloatFormat.binary64 (by decide) (by decide)
  have hprod : |Model.toReal (ExecFloat.Binary.toModel x)| * |Model.toReal (ExecFloat.Binary.toModel y)| ≤
      Model.toReal (Model.posMaxFinite FloatFormat.binary64) :=
    le_trans hprod_le hmax
  refine ⟨?_, hprod⟩
  change Model.isFinite (ExecFloat.Binary.toModel (ExecFloat.Binary.mul x y Model.IEEERoundingMode.nearestEven)) = true
  rw [ExecFloat.Binary.toModel_mul]
  exact Model.isFinite_mul_of_abs_mul_le_posMaxFinite
    (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y) (by rfl) hx hy hprod

theorem cross_ge_limitCross_of_rem_ge_bounded_loc
    (rem absDy absDx : Binary64)
    (hrem : ExecFloat.Binary.isFinite rem = true)
    (hdy : ExecFloat.Binary.isFinite absDy = true)
    (hdx : ExecFloat.Binary.isFinite absDx = true)
    (h_rem_dy : Model.toReal (ExecFloat.Binary.toModel rem) ≥ Model.toReal (ExecFloat.Binary.toModel absDx))
    (hdy_pos : Model.toReal (ExecFloat.Binary.toModel absDy) ≥ 0)
    (hrem_le : |Model.toReal (ExecFloat.Binary.toModel rem)| ≤ 2000)
    (hdy_le : |Model.toReal (ExecFloat.Binary.toModel absDy)| ≤ 2000)
    (hdx_le : |Model.toReal (ExecFloat.Binary.toModel absDx)| ≤ 2000) :
    rem * absDy ≥ absDx * absDy := by
  have ⟨hfin1, hprod1⟩ := binary64_mul_isFinite_of_le_2000_loc rem absDy hrem hdy hrem_le hdy_le
  have ⟨hfin2, hprod2⟩ := binary64_mul_isFinite_of_le_2000_loc absDx absDy hdx hdy hdx_le hdy_le
  exact cross_ge_of_rem_ge rem absDx absDy hrem hdx hdy h_rem_dy hdy_pos hprod1 hprod2 hfin1 hfin2

theorem real_rem_ge_absD_upper
    (A B : Point32) (_h_finA : A.isFinite) (h_finB : B.isFinite)
    (_h_bound : inCoordBounds mainCoordBound A.toPoint B.toPoint)
    (targetX : ℤ) (endCell : Cell) (h_cell_B : floorPoint32 B = endCell)
    (h_ge : targetX ≥ endCell.x + 1) :
    let xb : Binary64 := widen32To64 (intToBinary32 targetX)
    let startX : Binary64 := widen32To64 A.x
    let endX : Binary64 := widen32To64 B.x
    |targetX| ≤ 2000 →
    Model.toReal (ExecFloat.Binary.toModel xb) - Model.toReal (ExecFloat.Binary.toModel startX) ≥
    Model.toReal (ExecFloat.Binary.toModel endX) - Model.toReal (ExecFloat.Binary.toModel startX) := by
  intro xb startX endX h_target_bound
  have hB_fin : binary32IsFinite B.x = true := h_finB.1
  have h_xb_fin : ExecFloat.Binary.isFinite (intToBinary32 targetX) = true :=
    intToBinary32_isFinite_2000 targetX h_target_bound
  have h_xb_real : Model.toReal (ExecFloat.Binary.toModel xb) = (targetX : ℝ) := by
    dsimp [xb]
    rw [widen32To64_toReal_eq _ h_xb_fin]
    exact intToBinary32_toReal_eq_2000 targetX h_target_bound
  have h_endX_real : Model.toReal (ExecFloat.Binary.toModel endX) = Model.toReal (ExecFloat.Binary.toModel B.x) := by
    dsimp [endX]
    exact widen32To64_toReal_eq B.x hB_fin
  have h_floorB := floorPoint32_eq_floorPoint B h_finB
  rw [h_cell_B] at h_floorB
  have h_bx_lt : Model.toReal (ExecFloat.Binary.toModel B.x) < ((endCell.x + 1 : ℤ) : ℝ) := by
    have h_fp : (floorPoint B.toPoint).x = (endCell.x : ℤ) := by
      have h := congrArg Cell.x h_floorB
      unfold floorPoint toInt at h
      dsimp only [] at h
      exact h.symm
    unfold floorPoint toInt at h_fp
    dsimp only [] at h_fp
    have h_rat : (B.toPoint.x).floor = endCell.x := h_fp
    have h_lt := Rat.lt_floor_add_one B.toPoint.x
    rw [h_rat] at h_lt
    push_cast at h_lt
    have h_eq : Model.toReal (ExecFloat.Binary.toModel B.x) = ((B.toPoint.x : ℚ) : ℝ) := by
      exact toReal_eq_cast_toRat B.x hB_fin
    rw [h_eq]
    exact_mod_cast h_lt
  have h_ge_real : (targetX : ℝ) ≥ (endCell.x + 1 : ℝ) := by exact_mod_cast h_ge
  rw [h_xb_real, h_endX_real]
  push_cast at h_bx_lt
  linarith

theorem real_rem_ge_absD_lower
    (A B : Point32) (_h_finA : A.isFinite) (h_finB : B.isFinite)
    (_h_bound : inCoordBounds mainCoordBound A.toPoint B.toPoint)
    (targetX : ℤ) (endCell : Cell) (h_cell_B : floorPoint32 B = endCell)
    (h_le : targetX ≤ endCell.x) :
    let xb : Binary64 := widen32To64 (intToBinary32 targetX)
    let startX : Binary64 := widen32To64 A.x
    let endX : Binary64 := widen32To64 B.x
    |targetX| ≤ 2000 →
    Model.toReal (ExecFloat.Binary.toModel startX) - Model.toReal (ExecFloat.Binary.toModel xb) ≥
    Model.toReal (ExecFloat.Binary.toModel startX) - Model.toReal (ExecFloat.Binary.toModel endX) := by
  intro xb startX endX h_target_bound
  have hB_fin : binary32IsFinite B.x = true := h_finB.1
  have h_xb_fin : ExecFloat.Binary.isFinite (intToBinary32 targetX) = true :=
    intToBinary32_isFinite_2000 targetX h_target_bound
  have h_xb_real : Model.toReal (ExecFloat.Binary.toModel xb) = (targetX : ℝ) := by
    dsimp [xb]
    rw [widen32To64_toReal_eq _ h_xb_fin]
    exact intToBinary32_toReal_eq_2000 targetX h_target_bound
  have h_endX_real : Model.toReal (ExecFloat.Binary.toModel endX) = Model.toReal (ExecFloat.Binary.toModel B.x) := by
    dsimp [endX]
    exact widen32To64_toReal_eq B.x hB_fin
  have h_floorB := floorPoint32_eq_floorPoint B h_finB
  rw [h_cell_B] at h_floorB
  have h_bx_ge : Model.toReal (ExecFloat.Binary.toModel B.x) ≥ ((endCell.x : ℤ) : ℝ) := by
    have h_fp : (floorPoint B.toPoint).x = (endCell.x : ℤ) := by
      have h := congrArg Cell.x h_floorB
      unfold floorPoint toInt at h
      dsimp only [] at h
      exact h.symm
    unfold floorPoint toInt at h_fp
    dsimp only [] at h_fp
    have h_rat : (B.toPoint.x).floor = endCell.x := h_fp
    have h_le_floor := Rat.floor_le B.toPoint.x
    have h_eq : Model.toReal (ExecFloat.Binary.toModel B.x) = ((B.toPoint.x : ℚ) : ℝ) := by
      exact toReal_eq_cast_toRat B.x hB_fin
    rw [h_eq]
    exact_mod_cast (h_rat ▸ h_le_floor)
  have h_le_real : (targetX : ℝ) ≤ (endCell.x : ℝ) := by exact_mod_cast h_le
  rw [h_xb_real, h_endX_real]
  linarith

theorem step_at_ge_limitCross_general
    (start : Point32) (dx dy : Binary32) (stepX stepY : ℤ) (c : Cell)
    (hx0 : (stepX == 0) = false) (hy0 : (stepY == 0) = false) :
    let currentX := if stepX > 0 then c.x + 1 else c.x
    let _currentY := if stepY > 0 then c.y + 1 else c.y
    let xb : Binary64 := widen32To64 (intToBinary32 currentX)
    let _yb : Binary64 := widen32To64 (intToBinary32 _currentY)
    let startX : Binary64 := widen32To64 start.x
    let _startY : Binary64 := widen32To64 start.y
    let absDx : Binary64 := ExecFloat.Binary.abs (widen32To64 dx)
    let absDy : Binary64 := ExecFloat.Binary.abs (widen32To64 dy)
    let remX : Binary64 := ExecFloat.Binary.abs (xb - startX)
    let _remY : Binary64 := ExecFloat.Binary.abs (_yb - _startY)
    let crossX : Binary64 := remX * absDy
    let _crossY : Binary64 := _remY * absDx
    let limitCross : Binary64 := absDx * absDy
    (crossX ≥ limitCross) →
    (rayMarchStepFloat start dx dy stepX stepY c).2 = true ∨
    (rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x, c.y + stepY⟩ ∨
    (rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x + stepX, c.y + stepY⟩ := by
  intro currentX currentY xb yb startX startY absDx absDy remX remY crossX crossY limitCross h_ge
  unfold rayMarchStepFloat
  rw [hx0, hy0]
  simp only [Bool.false_eq_true, ite_false]
  change (if (crossX ⊓ crossY ≥ limitCross) then (c, true)
          else if crossX < crossY then (⟨c.x + stepX, c.y⟩, false)
          else if crossY < crossX then (⟨c.x, c.y + stepY⟩, false)
          else (⟨c.x + stepX, c.y + stepY⟩, false)).2 = true ∨
         (if (crossX ⊓ crossY ≥ limitCross) then (c, true)
          else if crossX < crossY then (⟨c.x + stepX, c.y⟩, false)
          else if crossY < crossX then (⟨c.x, c.y + stepY⟩, false)
          else (⟨c.x + stepX, c.y + stepY⟩, false)).1 = ⟨c.x, c.y + stepY⟩ ∨
         (if (crossX ⊓ crossY ≥ limitCross) then (c, true)
          else if crossX < crossY then (⟨c.x + stepX, c.y⟩, false)
          else if crossY < crossX then (⟨c.x, c.y + stepY⟩, false)
          else (⟨c.x + stepX, c.y + stepY⟩, false)).1 = ⟨c.x + stepX, c.y + stepY⟩
  split_ifs with h_done h_x h_y
  · left; rfl
  · exfalso
    exact not_stepX_of_crossX_ge crossX crossY limitCross h_ge h_done h_x
  · right; left; rfl
  · right; right; rfl

theorem step_at_ge_limitCross_general_Y
    (start : Point32) (dx dy : Binary32) (stepX stepY : ℤ) (c : Cell)
    (hx0 : (stepX == 0) = false) (hy0 : (stepY == 0) = false) :
    let _currentX := if stepX > 0 then c.x + 1 else c.x
    let currentY := if stepY > 0 then c.y + 1 else c.y
    let _xb : Binary64 := widen32To64 (intToBinary32 _currentX)
    let yb : Binary64 := widen32To64 (intToBinary32 currentY)
    let _startX : Binary64 := widen32To64 start.x
    let startY : Binary64 := widen32To64 start.y
    let absDx : Binary64 := ExecFloat.Binary.abs (widen32To64 dx)
    let absDy : Binary64 := ExecFloat.Binary.abs (widen32To64 dy)
    let _remX : Binary64 := ExecFloat.Binary.abs (_xb - _startX)
    let remY : Binary64 := ExecFloat.Binary.abs (yb - startY)
    let _crossX : Binary64 := _remX * absDy
    let crossY : Binary64 := remY * absDx
    let limitCross : Binary64 := absDx * absDy
    (crossY ≥ limitCross) →
    (rayMarchStepFloat start dx dy stepX stepY c).2 = true ∨
    (rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x + stepX, c.y⟩ ∨
    (rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x + stepX, c.y + stepY⟩ := by
  intro currentX currentY xb yb startX startY absDx absDy remX remY crossX crossY limitCross h_ge
  unfold rayMarchStepFloat
  rw [hx0, hy0]
  simp only [Bool.false_eq_true, ite_false]
  change (if (crossX ⊓ crossY ≥ limitCross) then (c, true)
          else if crossX < crossY then (⟨c.x + stepX, c.y⟩, false)
          else if crossY < crossX then (⟨c.x, c.y + stepY⟩, false)
          else (⟨c.x + stepX, c.y + stepY⟩, false)).2 = true ∨
         (if (crossX ⊓ crossY ≥ limitCross) then (c, true)
          else if crossX < crossY then (⟨c.x + stepX, c.y⟩, false)
          else if crossY < crossX then (⟨c.x, c.y + stepY⟩, false)
          else (⟨c.x + stepX, c.y + stepY⟩, false)).1 = ⟨c.x + stepX, c.y⟩ ∨
         (if (crossX ⊓ crossY ≥ limitCross) then (c, true)
          else if crossX < crossY then (⟨c.x + stepX, c.y⟩, false)
          else if crossY < crossX then (⟨c.x, c.y + stepY⟩, false)
          else (⟨c.x + stepX, c.y + stepY⟩, false)).1 = ⟨c.x + stepX, c.y + stepY⟩
  split_ifs with h_done h_x h_y
  · left; rfl
  · right; left; rfl
  · exfalso
    exact not_stepY_of_crossY_ge crossX crossY limitCross h_ge h_done h_y
  · right; right; rfl

theorem binary64_min_isFinite_and_toReal_eq_left_of_not_lt (x y : Binary64)
    (hx : ExecFloat.Binary.isFinite x = true)
    (hy : ExecFloat.Binary.isFinite y = true)
    (h1 : ¬ (x < y)) (h2 : ¬ (y < x)) :
    ExecFloat.Binary.isFinite (min x y) = true ∧
    Model.toReal (ExecFloat.Binary.toModel (min x y)) = Model.toReal (ExecFloat.Binary.toModel x) := by
  have htri := trichotomy_of_isFinite_binary64 x y hx hy
  rcases htri with hlt | hgt | heq
  · exfalso; exact h1 hlt
  · exfalso; exact h2 hgt
  · have hx_fin : Model.isFinite (ExecFloat.Binary.toModel x) = true := hx
    have hy_fin : Model.isFinite (ExecFloat.Binary.toModel y) = true := hy
    have h_eq_cmp : (ExecFloat.Binary.toModel x).compare (ExecFloat.Binary.toModel y) = some Ordering.eq :=
      (Model.compare_eq_some_eq_iff_toReal_eq_of_isFinite
        (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y) hx_fin hy_fin).mpr heq
    have h_both : Model.isNaN (ExecFloat.Binary.toModel x) = false ∧ Model.isNaN (ExecFloat.Binary.toModel y) = false := by
      have h_not := (Model.compare_eq_none_iff (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y)).not.mp
      rw [h_eq_cmp] at h_not
      simp only [not_or, Bool.not_eq_true] at h_not
      exact h_not (by intro; contradiction)
    have hchoose := Model.chooseNaN2_none_of_not_isNaN (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y) h_both.1 h_both.2
    have h_min : ExecFloat.Binary.toModel (min x y) =
        if ((ExecFloat.Binary.toModel x).isZero && (ExecFloat.Binary.toModel y).isZero) = true
        then Model.zero _ ((ExecFloat.Binary.toModel x).signBit || (ExecFloat.Binary.toModel y).signBit)
        else ExecFloat.Binary.toModel x := by
      rw [ExecFloat.Binary.toModel_min]
      simp [Model.minimum, hchoose, h_eq_cmp]
    split_ifs at h_min with hz
    · simp only [Bool.and_eq_true] at hz
      have hx0 : Model.toReal (ExecFloat.Binary.toModel x) = 0 :=
        Model.toReal_eq_zero_of_isZero (ExecFloat.Binary.toModel x) hz.1
      refine ⟨?_, ?_⟩
      · change Model.isFinite (ExecFloat.Binary.toModel (min x y)) = true
        rw [h_min]
        cases ((ExecFloat.Binary.toModel x).signBit || (ExecFloat.Binary.toModel y).signBit)
        · exact Model.isFinite_posZero _
        · exact Model.isFinite_negZero _ (by rfl)
      · rw [h_min, hx0]
        exact Model.toReal_zero _ _
    · refine ⟨?_, ?_⟩
      · change Model.isFinite (ExecFloat.Binary.toModel (min x y)) = true
        rw [h_min]; exact hx_fin
      · rw [h_min]

theorem min_ge_iff_of_isFinite_binary64 (x y z : Binary64)
    (hx : ExecFloat.Binary.isFinite x = true)
    (hy : ExecFloat.Binary.isFinite y = true)
    (hz : ExecFloat.Binary.isFinite z = true) :
    min x y ≥ z ↔ (x ≥ z ∧ y ≥ z) := by
  rcases trichotomy_of_isFinite_binary64 x y hx hy with hlt | hgt | heq
  · rw [binary64_min_of_lt x y hlt]
    constructor
    · intro hxz
      refine ⟨hxz, ?_⟩
      have h1 := toReal_ge_of_ge_binary64 x z hx hz hxz
      have h2 := toReal_lt_of_lt_binary64 x y hx hy hlt
      exact ge_of_toReal_ge y z hy hz (by linarith)
    · intro h; exact h.1
  · rw [binary64_min_of_gt x y hgt]
    constructor
    · intro hyz
      refine ⟨?_, hyz⟩
      have h1 := toReal_ge_of_ge_binary64 y z hy hz hyz
      have h2 := toReal_lt_of_lt_binary64 y x hy hx hgt
      exact ge_of_toReal_ge x z hx hz (by linarith)
    · intro h; exact h.2
  · have hnot1 : ¬ (x < y) := by
      intro h; have := toReal_lt_of_lt_binary64 x y hx hy h; linarith
    have hnot2 : ¬ (y < x) := by
      intro h; have := toReal_lt_of_lt_binary64 y x hy hx h; linarith
    obtain ⟨hmin_fin, hmin_real⟩ := binary64_min_isFinite_and_toReal_eq_left_of_not_lt x y hx hy hnot1 hnot2
    constructor
    · intro hmin_ge
      have h1 := toReal_ge_of_ge_binary64 (min x y) z hmin_fin hz hmin_ge
      rw [hmin_real] at h1
      refine ⟨ge_of_toReal_ge x z hx hz h1, ge_of_toReal_ge y z hy hz (by linarith)⟩
    · intro ⟨hxz, _⟩
      have h1 := toReal_ge_of_ge_binary64 x z hx hz hxz
      exact ge_of_toReal_ge (min x y) z hmin_fin hz (by linarith)

theorem bpow_le_bpow_of_le (e1 e2 : ℤ) (h : e1 ≤ e2) :
    Model.bpow e1 ≤ Model.bpow e2 := by
  rcases lt_or_eq_of_le h with hlt | rfl
  · exact le_of_lt ((Formats.Flocq.bpow_lt_bpow_iff Numerics.binaryRadix e1 e2).mpr hlt)
  · exact le_refl _

theorem bpow_neg23_eq : Model.bpow (-23) = (1 / 8388608 : ℝ) := by
  have h1 : Model.bpow (23 + (-23)) = Model.bpow 23 * Model.bpow (-23) :=
    Formats.Flocq.bpow.add_exp Numerics.binaryRadix 23 (-23)
  have h0 : Model.bpow (23 + (-23)) = 1 := Model.bpow_zero
  have h23 : Model.bpow (23 : ℕ) = (2 : ℝ) ^ 23 := Model.bpow_natCast 23
  change Model.bpow (23 : ℤ) = (2 : ℝ) ^ 23 at h23
  rw [h0, h23] at h1
  norm_num at h1
  linarith

theorem abs_roundAt_sub_le_rel_of_normal (fmt : FloatFormat) (x : ℝ)
    (hexp : 1 - Int.ofNat (fmt.fracWidth + 1) ≤ -23)
    (hnormal : Model.minNormalAt fmt ≤ |x|) :
    |Model.roundAt fmt x - x| ≤ (1 / 16777216 : ℝ) * |x| := by
  have hpos : 0 < Model.minNormalAt fmt := Model.bpow_pos fmt.minNormalExponent
  have hx_abs_pos : 0 < |x| := lt_of_lt_of_le hpos hnormal
  have hx : x ≠ 0 := abs_pos.mp hx_abs_pos
  have hrel := Model.relativeError_roundAt_le_of_normal fmt x hx hnormal
  unfold Formats.Flocq.ErrorBounds.relativeError at hrel
  have hbpow : Model.bpow (1 - Int.ofNat (fmt.fracWidth + 1)) ≤ Model.bpow (-23) :=
    bpow_le_bpow_of_le _ _ hexp
  rw [bpow_neg23_eq] at hbpow
  have hdiv : |Model.roundAt fmt x - x| / |x| ≤ (1 / 16777216 : ℝ) := by
    change |Model.roundAt fmt x - x| / |x| ≤ Model.bpow (1 - Int.ofNat (fmt.fracWidth + 1)) / 2 at hrel
    linarith
  rwa [div_le_iff₀ hx_abs_pos] at hdiv

theorem abs_toReal_ge_bpow_neg149_of_ne_zero (x : Binary32)
    (hx : binary32IsFinite x = true)
    (hne : Model.toReal (ExecFloat.Binary.toModel x) ≠ 0) :
    Model.bpow (-149) ≤ |Model.toReal (ExecFloat.Binary.toModel x)| := by
  obtain ⟨n, hn⟩ := toReal_eq_int_mul_posMinSubnormal x hx
  have h_posMin : Model.toReal (Model.posMinSubnormal FloatFormat.binary32) = Model.bpow (-149) :=
    Model.toReal_posMinSubnormal FloatFormat.binary32
  rw [h_posMin] at hn
  have hn_ne : n ≠ 0 := by
    intro h0; apply hne; rw [hn, h0]; simp
  have hn_abs : (1 : ℝ) ≤ |(n : ℝ)| := by
    rw [← Int.cast_abs]
    have : 1 ≤ |n| := Int.one_le_abs hn_ne
    exact_mod_cast this
  have hbpow_pos : 0 < Model.bpow (-149) := Model.bpow_pos (-149)
  rw [hn, abs_mul, abs_of_pos hbpow_pos]
  nlinarith

theorem abs_sub_toReal_ge_bpow_neg149_of_ne (x y : Binary32)
    (hx : binary32IsFinite x = true) (hy : binary32IsFinite y = true)
    (hne : Model.toReal (ExecFloat.Binary.toModel x) - Model.toReal (ExecFloat.Binary.toModel y) ≠ 0) :
    Model.bpow (-149) ≤ |Model.toReal (ExecFloat.Binary.toModel x) - Model.toReal (ExecFloat.Binary.toModel y)| := by
  obtain ⟨nx, hnx⟩ := toReal_eq_int_mul_posMinSubnormal x hx
  obtain ⟨ny, hny⟩ := toReal_eq_int_mul_posMinSubnormal y hy
  have h_posMin : Model.toReal (Model.posMinSubnormal FloatFormat.binary32) = Model.bpow (-149) :=
    Model.toReal_posMinSubnormal FloatFormat.binary32
  rw [h_posMin] at hnx hny
  have hsub : Model.toReal (ExecFloat.Binary.toModel x) - Model.toReal (ExecFloat.Binary.toModel y) =
      ((nx - ny : ℤ) : ℝ) * Model.bpow (-149) := by
    rw [hnx, hny]; push_cast; ring
  have hn_ne : nx - ny ≠ 0 := by
    intro h0; apply hne; rw [hsub, h0]; simp
  have hn_abs : (1 : ℝ) ≤ |((nx - ny : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    have : 1 ≤ |nx - ny| := Int.one_le_abs hn_ne
    exact_mod_cast this
  have hbpow_pos : 0 < Model.bpow (-149) := Model.bpow_pos (-149)
  rw [hsub, abs_mul, abs_of_pos hbpow_pos]
  nlinarith

theorem abs_toReal_sub_binary32_rel (a b : Binary32)
    (ha : binary32IsFinite a = true) (hb : binary32IsFinite b = true)
    (ha_le : |binary32ToRat a| ≤ mainCoordBound) (hb_le : |binary32ToRat b| ≤ mainCoordBound) :
    |Model.toReal (ExecFloat.Binary.toModel (b - a)) -
      (Model.toReal (ExecFloat.Binary.toModel b) - Model.toReal (ExecFloat.Binary.toModel a))| ≤
    (1 / 16777216 : ℝ) * |Model.toReal (ExecFloat.Binary.toModel b) - Model.toReal (ExecFloat.Binary.toModel a)| := by
  rw [toReal_sub_eq_roundAt a b ha hb ha_le hb_le]
  set r := Model.toReal (ExecFloat.Binary.toModel b) - Model.toReal (ExecFloat.Binary.toModel a)
  by_cases hnorm : Model.minNormalAt FloatFormat.binary32 ≤ |r|
  · exact abs_roundAt_sub_le_rel_of_normal FloatFormat.binary32 r (by decide) hnorm
  · have hnorm_le : |r| ≤ Model.minNormalAt FloatFormat.binary32 := le_of_not_ge hnorm
    let emin := FloatFormat.minSubnormalExponent FloatFormat.binary32
    let prec := Int.ofNat (FloatFormat.binary32.fracWidth + 1)
    have hprec : 0 < prec := by decide
    have : Formats.Flocq.ValidExp (Formats.Flocq.fltExp emin prec) :=
      Formats.Flocq.fltValidExp emin prec hprec
    have hgen_b : Formats.Flocq.genericFormat Numerics.binaryRadix (Formats.Flocq.fltExp emin prec)
        (Model.toReal (ExecFloat.Binary.toModel b)) :=
      Model.toReal_genericFormat_of_isFinite (ExecFloat.Binary.toModel b) hb
    have hgen_a : Formats.Flocq.genericFormat Numerics.binaryRadix (Formats.Flocq.fltExp emin prec)
        (-Model.toReal (ExecFloat.Binary.toModel a)) :=
      Formats.Flocq.generic_format_neg _
        (Model.toReal_genericFormat_of_isFinite (ExecFloat.Binary.toModel a) ha)
    have h_le : |Model.toReal (ExecFloat.Binary.toModel b) + (-Model.toReal (ExecFloat.Binary.toModel a))| ≤
        Model.bpow (prec + emin) := by
      rw [← sub_eq_add_neg]
      have h1 : Model.minNormalAt FloatFormat.binary32 ≤ Model.bpow (prec + emin) :=
        bpow_le_bpow_of_le _ _ (by decide)
      exact le_trans hnorm_le h1
    have hgen_sub : Formats.Flocq.genericFormat Numerics.binaryRadix (Model.fexpOf FloatFormat.binary32) r := by
      change Formats.Flocq.genericFormat Numerics.binaryRadix (Formats.Flocq.fltExp emin prec) r
      rw [show r = Model.toReal (ExecFloat.Binary.toModel b) + (-Model.toReal (ExecFloat.Binary.toModel a)) by ring]
      exact Formats.Flocq.generic_format_FLT_add_small emin prec hprec hgen_b hgen_a h_le
    have hround : Model.roundAt FloatFormat.binary32 r = r :=
      Formats.Flocq.round_preserves_generic Formats.Flocq.nearestEven r hgen_sub
    rw [hround, sub_self, abs_zero]
    positivity

theorem abs_roundAt_binary64_rel_of_ge_bpow_neg300 (x : ℝ)
    (hx : x = 0 ∨ Model.bpow (-300) ≤ |x|) :
    |Model.roundAt FloatFormat.binary64 x - x| ≤ (1 / 16777216 : ℝ) * |x| := by
  rcases hx with rfl | hge
  · rw [Model.roundAt_zero, sub_self, abs_zero, mul_zero]
  · have hnorm : Model.minNormalAt FloatFormat.binary64 ≤ |x| := by
      have h1 : Model.minNormalAt FloatFormat.binary64 ≤ Model.bpow (-300) :=
        bpow_le_bpow_of_le _ _ (by decide)
      exact le_trans h1 hge
    exact abs_roundAt_sub_le_rel_of_normal FloatFormat.binary64 x (by decide) hnorm

theorem ten_million_le_posMaxFinite_binary64 :
    (10000000 : ℝ) ≤ Model.toReal (Model.posMaxFinite FloatFormat.binary64) := by
  have h := Model.abs_signed_mul_bpow_le_toReal_posMaxFinite FloatFormat.binary64 false 10000000 0
    (by decide) (by decide)
  simp only [Bool.false_eq_true, ite_false, one_mul, Model.bpow_zero, mul_one] at h
  rw [abs_of_pos (by norm_num)] at h
  exact h

theorem binary64_mul_approx_rel (u v : Binary64) (u_I v_I : ℝ)
    (hu_fin : ExecFloat.Binary.isFinite u = true)
    (hv_fin : ExecFloat.Binary.isFinite v = true)
    (hu_I : 0 ≤ u_I ∧ u_I ≤ 3000)
    (hv_I : 0 ≤ v_I ∧ v_I ≤ 3000)
    (hu_rel : |Model.toReal (ExecFloat.Binary.toModel u) - u_I| ≤ (1 / 16777216 : ℝ) * u_I)
    (hv_rel : |Model.toReal (ExecFloat.Binary.toModel v) - v_I| ≤ (1 / 16777216 : ℝ) * v_I)
    (hu_bpow : Model.toReal (ExecFloat.Binary.toModel u) = 0 ∨
               Model.bpow (-150) ≤ |Model.toReal (ExecFloat.Binary.toModel u)|)
    (hv_bpow : Model.toReal (ExecFloat.Binary.toModel v) = 0 ∨
               Model.bpow (-150) ≤ |Model.toReal (ExecFloat.Binary.toModel v)|) :
    ExecFloat.Binary.isFinite (u * v) = true ∧
    |Model.toReal (ExecFloat.Binary.toModel (u * v)) - u_I * v_I| ≤
      (1 / 5000000 : ℝ) * (u_I * v_I) := by
  set ru := Model.toReal (ExecFloat.Binary.toModel u)
  set rv := Model.toReal (ExecFloat.Binary.toModel v)
  have hru_bounds := abs_le.mp hu_rel
  have hrv_bounds := abs_le.mp hv_rel
  have hru_nonneg : 0 ≤ ru := by linarith [hu_I.1]
  have hrv_nonneg : 0 ≤ rv := by linarith [hv_I.1]
  have hru_le : |ru| ≤ 3001 := by rw [abs_of_nonneg hru_nonneg]; linarith [hu_I.2]
  have hrv_le : |rv| ≤ 3001 := by rw [abs_of_nonneg hrv_nonneg]; linarith [hv_I.2]
  have hprod_le_max : |ru| * |rv| ≤ Model.toReal (Model.posMaxFinite FloatFormat.binary64) := by
    have h1 : |ru| * |rv| ≤ 10000000 := by
      have : 0 ≤ |ru| := abs_nonneg _
      have : 0 ≤ |rv| := abs_nonneg _
      nlinarith
    exact le_trans h1 ten_million_le_posMaxFinite_binary64
  have huv_fin : ExecFloat.Binary.isFinite (u * v) = true := by
    change Model.isFinite (ExecFloat.Binary.toModel (ExecFloat.Binary.mul u v Model.IEEERoundingMode.nearestEven)) = true
    rw [ExecFloat.Binary.toModel_mul]
    exact Model.isFinite_mul_of_abs_mul_le_posMaxFinite
      (ExecFloat.Binary.toModel u) (ExecFloat.Binary.toModel v) (by rfl) hu_fin hv_fin hprod_le_max
  have huv_toReal : Model.toReal (ExecFloat.Binary.toModel (u * v)) =
      Model.roundAt FloatFormat.binary64 (ru * rv) := by
    change Model.toReal (ExecFloat.Binary.toModel (ExecFloat.Binary.mul u v Model.IEEERoundingMode.nearestEven)) = _
    rw [ExecFloat.Binary.toModel_mul]
    exact Model.toReal_mul_eq_roundAt_of_abs_mul_le_posMaxFinite
      (ExecFloat.Binary.toModel u) (ExecFloat.Binary.toModel v) (by rfl) hu_fin hv_fin hprod_le_max
  have hprod_bpow : ru * rv = 0 ∨ Model.bpow (-300) ≤ |ru * rv| := by
    rcases hu_bpow with hu0 | hu_ge
    · left; rw [hu0, zero_mul]
    · rcases hv_bpow with hv0 | hv_ge
      · left; rw [hv0, mul_zero]
      · right
        rw [abs_mul]
        have hadd : Model.bpow (-150 + (-150)) = Model.bpow (-150) * Model.bpow (-150) :=
          Formats.Flocq.bpow.add_exp Numerics.binaryRadix (-150) (-150)
        norm_num at hadd
        rw [hadd]
        exact mul_le_mul hu_ge hv_ge (le_of_lt (Model.bpow_pos (-150))) (abs_nonneg _)
  have hround_err := abs_roundAt_binary64_rel_of_ge_bpow_neg300 (ru * rv) hprod_bpow
  rw [← huv_toReal] at hround_err
  rw [abs_of_nonneg (mul_nonneg hru_nonneg hrv_nonneg)] at hround_err
  have hround_bounds := abs_le.mp hround_err
  refine ⟨huv_fin, abs_le.mpr ⟨?_, ?_⟩⟩
  · nlinarith [hu_I.1, hv_I.1]
  · nlinarith [hu_I.1, hv_I.1]

theorem widen32To64_isFinite (x : Binary32) (hx : binary32IsFinite x = true) :
    ExecFloat.Binary.isFinite (widen32To64 x) = true := by
  have h_ieee_fin : Model.IEEE.isFinite (ExecFloat.Binary.toModel x) = true := hx
  obtain ⟨d, hd⟩ := Model.exists_ieeeToDyadic?_of_isFinite h_ieee_fin
  have h_dyadic : Model.toDyadic? (ExecFloat.Binary.toModel x) = some d := by
    unfold Model.toDyadic?
    simp [hd]
  have h_toReal_x : Model.toReal (ExecFloat.Binary.toModel x) = (d.toRat : ℝ) := by
    unfold Model.toReal Model.toReal?
    rw [h_dyadic]
    exact (Numerics.Dyadic.cast_toRat d).symm
  change Model.isFinite (ExecFloat.Binary.toModel (widen32To64 x)) = true
  rw [widen32To64_eq_roundRat x d h_dyadic]
  by_cases hzero : d.toRat = 0
  · have hnum : d.toRat.num.natAbs = 0 := by simp [hzero]
    rw [hnum, Model.roundRat,
        Model.roundRatScaled_num_zero FloatFormat.binary64 d.negative d.toRat.den 0 d.toRat.den_nz]
    cases d.negative <;> decide
  · have hden : d.toRat.den ≠ 0 := d.toRat.den_nz
    have hfmt : FloatFormat.binary64.isIEEE = true := rfl
    have hbound :
        |Model.signedScaledRatToReal d.negative d.toRat.num.natAbs d.toRat.den 0| ≤
          Model.toReal (Model.posMaxFinite FloatFormat.binary64) := by
      have h_signed := signedRat_toReal (Numerics.SignedRat.ofDyadic d) hzero
      change Model.signedScaledRatToReal d.negative d.toRat.num.natAbs d.toRat.den 0 = (d.toRat : ℝ) at h_signed
      rw [h_signed, ← h_toReal_x]
      exact le_trans
        (Model.abs_toReal_le_posMaxFinite_of_isIEEE_of_isFinite (ExecFloat.Binary.toModel x) (by rfl) hx)
        posMaxFinite_binary32_le_binary64
    exact Model.isFinite_roundRatScaled_of_abs_le_posMaxFinite FloatFormat.binary64 d.negative
      d.toRat.num.natAbs d.toRat.den 0 hfmt hden hbound

theorem abs_toReal_absD_binary64_rel (a b : Binary32)
    (ha : binary32IsFinite a = true) (hb : binary32IsFinite b = true)
    (ha_le : |binary32ToRat a| ≤ mainCoordBound) (hb_le : |binary32ToRat b| ≤ mainCoordBound) :
    let absD := ExecFloat.Binary.abs (widen32To64 (b - a))
    let d_I := |((binary32ToRat b - binary32ToRat a : ℚ) : ℝ)|
    ExecFloat.Binary.isFinite absD = true ∧
    (0 ≤ d_I ∧ d_I ≤ 3000) ∧
    |Model.toReal (ExecFloat.Binary.toModel absD) - d_I| ≤ (1 / 16777216 : ℝ) * d_I ∧
    (Model.toReal (ExecFloat.Binary.toModel absD) = 0 ∨
     Model.bpow (-150) ≤ |Model.toReal (ExecFloat.Binary.toModel absD)|) := by
  intro absD d_I
  have hsub_fin : binary32IsFinite (b - a) = true :=
    binary32_sub_isFinite a b ha hb ha_le hb_le
  have hw_fin : ExecFloat.Binary.isFinite (widen32To64 (b - a)) = true :=
    widen32To64_isFinite (b - a) hsub_fin
  have habs_fin : ExecFloat.Binary.isFinite absD = true := by
    change Model.isFinite (ExecFloat.Binary.toModel (ExecFloat.Binary.abs (widen32To64 (b - a)))) = true
    rw [ExecFloat.Binary.toModel_abs, Model.isFinite_abs]
    exact hw_fin
  have habs_toReal : Model.toReal (ExecFloat.Binary.toModel absD) =
      |Model.toReal (ExecFloat.Binary.toModel (b - a))| := by
    change Model.toReal (ExecFloat.Binary.toModel (ExecFloat.Binary.abs (widen32To64 (b - a)))) = _
    rw [ExecFloat.Binary.toModel_abs, toReal_abs _ (by rfl) hw_fin, widen32To64_toReal_eq _ hsub_fin]
  have hd_I_eq : d_I = |Model.toReal (ExecFloat.Binary.toModel b) - Model.toReal (ExecFloat.Binary.toModel a)| := by
    dsimp [d_I]
    rw [toReal_eq_cast_toRat b hb, toReal_eq_cast_toRat a ha]
    push_cast
    rfl
  have hd_I_bounds : 0 ≤ d_I ∧ d_I ≤ 3000 := by
    refine ⟨abs_nonneg _, ?_⟩
    have ha_r : |((binary32ToRat a : ℚ) : ℝ)| ≤ 1000 := by exact_mod_cast ha_le
    have hb_r : |((binary32ToRat b : ℚ) : ℝ)| ≤ 1000 := by exact_mod_cast hb_le
    dsimp [d_I]
    push_cast
    linarith [abs_le.mp ha_r, abs_le.mp hb_r, abs_sub ((binary32ToRat b : ℚ) : ℝ) ((binary32ToRat a : ℚ) : ℝ)]
  have hrel0 := abs_toReal_sub_binary32_rel a b ha hb ha_le hb_le
  have hrel : |Model.toReal (ExecFloat.Binary.toModel absD) - d_I| ≤ (1 / 16777216 : ℝ) * d_I := by
    rw [habs_toReal, hd_I_eq]
    exact le_trans (abs_abs_sub_abs_le _ _) hrel0
  have hbpow : Model.toReal (ExecFloat.Binary.toModel absD) = 0 ∨
      Model.bpow (-150) ≤ |Model.toReal (ExecFloat.Binary.toModel absD)| := by
    by_cases h0 : Model.toReal (ExecFloat.Binary.toModel (b - a)) = 0
    · left; rw [habs_toReal, h0, abs_zero]
    · right
      rw [habs_toReal, abs_abs]
      have h149 := abs_toReal_ge_bpow_neg149_of_ne_zero (b - a) hsub_fin h0
      exact le_trans (bpow_le_bpow_of_le (-150) (-149) (by decide)) h149
  exact ⟨habs_fin, hd_I_bounds, hrel, hbpow⟩

theorem abs_toReal_rem_binary64_rel (a : Binary32) (k : ℤ)
    (ha : binary32IsFinite a = true)
    (ha_le : |binary32ToRat a| ≤ mainCoordBound)
    (hk_le : |k| ≤ 2000) :
    let kb : Binary64 := widen32To64 (intToBinary32 k)
    let startA : Binary64 := widen32To64 a
    let rem : Binary64 := ExecFloat.Binary.abs (kb - startA)
    let rem_I : ℝ := |(k : ℝ) - ((binary32ToRat a : ℚ) : ℝ)|
    ExecFloat.Binary.isFinite rem = true ∧
    (0 ≤ rem_I ∧ rem_I ≤ 3000) ∧
    |Model.toReal (ExecFloat.Binary.toModel rem) - rem_I| ≤ (1 / 16777216 : ℝ) * rem_I ∧
    (Model.toReal (ExecFloat.Binary.toModel rem) = 0 ∨
     Model.bpow (-150) ≤ |Model.toReal (ExecFloat.Binary.toModel rem)|) := by
  intro kb startA rem rem_I
  have hk_fin32 : ExecFloat.Binary.isFinite (intToBinary32 k) = true :=
    intToBinary32_isFinite_2000 k hk_le
  have hk_real32 : Model.toReal (ExecFloat.Binary.toModel (intToBinary32 k)) = (k : ℝ) :=
    intToBinary32_toReal_eq_2000 k hk_le
  have hkb_fin : ExecFloat.Binary.isFinite kb = true :=
    widen32To64_isFinite (intToBinary32 k) hk_fin32
  have hkb_real : Model.toReal (ExecFloat.Binary.toModel kb) = (k : ℝ) := by
    dsimp [kb]
    rw [widen32To64_toReal_eq _ hk_fin32, hk_real32]
  have hstart_fin : ExecFloat.Binary.isFinite startA = true :=
    widen32To64_isFinite a ha
  have hstart_real : Model.toReal (ExecFloat.Binary.toModel startA) = ((binary32ToRat a : ℚ) : ℝ) := by
    dsimp [startA]
    rw [widen32To64_toReal_eq _ ha, toReal_eq_cast_toRat a ha]
  have ha_r : |((binary32ToRat a : ℚ) : ℝ)| ≤ 1000 := by exact_mod_cast ha_le
  have hk_r : |(k : ℝ)| ≤ 2000 := by exact_mod_cast hk_le
  have hadd_le_max : |Model.toReal (ExecFloat.Binary.toModel kb)| + |Model.toReal (ExecFloat.Binary.toModel startA)| ≤
      Model.toReal (Model.posMaxFinite FloatFormat.binary64) := by
    rw [hkb_real, hstart_real]
    have h1 : |(k : ℝ)| + |((binary32ToRat a : ℚ) : ℝ)| ≤ 10000000 := by linarith
    exact le_trans h1 ten_million_le_posMaxFinite_binary64
  have hsub_fin : ExecFloat.Binary.isFinite (kb - startA) = true := by
    have hsub : ExecFloat.Binary.toModel (kb - startA) =
        Model.Spec.sub (ExecFloat.Binary.toModel kb) (ExecFloat.Binary.toModel startA) := by
      change ExecFloat.Binary.toModel (ExecFloat.sub kb startA) = _
      rw [ExecFloat.Proof.sub_eq_spec]
      change Configured.Family.toModel (ExecFloat.ModelCodec.liftBinary Model.Spec.sub kb startA) = _
      simp [Configured.Family.toModel, ExecFloat.Binary.toModel]
    change Model.isFinite (ExecFloat.Binary.toModel (kb - startA)) = true
    rw [hsub, ← Model.Proof.sub_eq_spec]
    exact Model.isFinite_sub_of_abs_add_le_posMaxFinite
      (ExecFloat.Binary.toModel kb) (ExecFloat.Binary.toModel startA) (by rfl) hkb_fin hstart_fin hadd_le_max
  have hrem_fin : ExecFloat.Binary.isFinite rem = true := by
    change Model.isFinite (ExecFloat.Binary.toModel (ExecFloat.Binary.abs (kb - startA))) = true
    rw [ExecFloat.Binary.toModel_abs, Model.isFinite_abs]
    exact hsub_fin
  have hrem_toReal : Model.toReal (ExecFloat.Binary.toModel rem) =
      |Model.roundAt FloatFormat.binary64 ((k : ℝ) - ((binary32ToRat a : ℚ) : ℝ))| := by
    change Model.toReal (ExecFloat.Binary.toModel (ExecFloat.Binary.abs (kb - startA))) = _
    rw [ExecFloat.Binary.toModel_abs, toReal_abs _ (by rfl) hsub_fin,
        toReal_sub_eq_roundAt_binary64 kb startA hkb_fin hstart_fin hadd_le_max,
        hkb_real, hstart_real]
  have hrem_I_bounds : 0 ≤ rem_I ∧ rem_I ≤ 3000 := by
    refine ⟨abs_nonneg _, ?_⟩
    dsimp [rem_I]
    linarith [abs_le.mp ha_r, abs_le.mp hk_r, abs_sub (k : ℝ) ((binary32ToRat a : ℚ) : ℝ)]
  set r := (k : ℝ) - ((binary32ToRat a : ℚ) : ℝ)
  have hr_eq : r = Model.toReal (ExecFloat.Binary.toModel (intToBinary32 k)) -
      Model.toReal (ExecFloat.Binary.toModel a) := by
    rw [hk_real32, toReal_eq_cast_toRat a ha]
  have hr_bpow : r = 0 ∨ Model.bpow (-149) ≤ |r| := by
    by_cases h0 : r = 0
    · left; exact h0
    · right
      have hne : Model.toReal (ExecFloat.Binary.toModel (intToBinary32 k)) -
          Model.toReal (ExecFloat.Binary.toModel a) ≠ 0 := by
        rw [← hr_eq]; exact h0
      rw [hr_eq]
      exact abs_sub_toReal_ge_bpow_neg149_of_ne (intToBinary32 k) a hk_fin32 ha hne
  have hr_bpow300 : r = 0 ∨ Model.bpow (-300) ≤ |r| := by
    rcases hr_bpow with h0 | h149
    · left; exact h0
    · right; exact le_trans (bpow_le_bpow_of_le (-300) (-149) (by decide)) h149
  have hround_rel := abs_roundAt_binary64_rel_of_ge_bpow_neg300 r hr_bpow300
  have hrel : |Model.toReal (ExecFloat.Binary.toModel rem) - rem_I| ≤ (1 / 16777216 : ℝ) * rem_I := by
    rw [hrem_toReal]
    dsimp [rem_I]
    exact le_trans (abs_abs_sub_abs_le _ _) hround_rel
  have hbpow : Model.toReal (ExecFloat.Binary.toModel rem) = 0 ∨
      Model.bpow (-150) ≤ |Model.toReal (ExecFloat.Binary.toModel rem)| := by
    rcases hr_bpow with h0 | h149
    · left; rw [hrem_toReal, h0, Model.roundAt_zero, abs_zero]
    · right
      have hb149 : Model.bpow (-149) = Model.bpow (-150) * 2 := by
        have h := Formats.Flocq.bpow.add_exp Numerics.binaryRadix (-150) 1
        norm_num at h
        exact h
      have hrel_bounds := abs_le.mp hrel
      have hrem_nonneg : 0 ≤ Model.toReal (ExecFloat.Binary.toModel rem) := by
        rw [hrem_toReal]; exact abs_nonneg _
      rw [abs_of_nonneg hrem_nonneg]
      dsimp [rem_I] at hrel_bounds
      linarith
  exact ⟨hrem_fin, hrem_I_bounds, hrel, hbpow⟩

def remX_R (A : Point32) (stepX : ℤ) (cx : ℤ) : ℝ :=
  |((if stepX > 0 then cx + 1 else cx : ℤ) : ℝ) - (A.toPoint.x : ℝ)|

def remY_R (A : Point32) (stepY : ℤ) (cy : ℤ) : ℝ :=
  |((if stepY > 0 then cy + 1 else cy : ℤ) : ℝ) - (A.toPoint.y : ℝ)|

def absDx_R (A B : Point32) : ℝ :=
  |(B.toPoint.x : ℝ) - (A.toPoint.x : ℝ)|

def absDy_R (A B : Point32) : ℝ :=
  |(B.toPoint.y : ℝ) - (A.toPoint.y : ℝ)|

def crossX_R (A B : Point32) (stepX : ℤ) (cx : ℤ) : ℝ :=
  remX_R A stepX cx * absDy_R A B

def crossY_R (A B : Point32) (stepY : ℤ) (cy : ℤ) : ℝ :=
  remY_R A stepY cy * absDx_R A B

def limitCross_R (A B : Point32) : ℝ :=
  absDx_R A B * absDy_R A B

theorem crossProducts_R_bounds (A B : Point32) (stepX stepY : ℤ) (cx cy : ℤ)
    (h_bound : inCoordBounds mainCoordBound A.toPoint B.toPoint)
    (hcx : |cx| ≤ 1995) (hcy : |cy| ≤ 1995) :
    0 ≤ absDx_R A B ∧ absDx_R A B ≤ 2000 ∧
    0 ≤ absDy_R A B ∧ absDy_R A B ≤ 2000 ∧
    0 ≤ crossX_R A B stepX cx ∧ crossX_R A B stepX cx ≤ 3000 * absDy_R A B ∧
    0 ≤ crossY_R A B stepY cy ∧ crossY_R A B stepY cy ≤ 3000 * absDx_R A B ∧
    0 ≤ limitCross_R A B ∧
    limitCross_R A B ≤ 2000 * absDx_R A B ∧
    limitCross_R A B ≤ 2000 * absDy_R A B := by
  rcases h_bound with ⟨hAx_le, hAy_le, hBx_le, hBy_le⟩
  have hAx_r : |(A.toPoint.x : ℝ)| ≤ 1000 := by exact_mod_cast hAx_le
  have hAy_r : |(A.toPoint.y : ℝ)| ≤ 1000 := by exact_mod_cast hAy_le
  have hBx_r : |(B.toPoint.x : ℝ)| ≤ 1000 := by exact_mod_cast hBx_le
  have hBy_r : |(B.toPoint.y : ℝ)| ≤ 1000 := by exact_mod_cast hBy_le
  have hdx0 : 0 ≤ absDx_R A B := abs_nonneg _
  have hdy0 : 0 ≤ absDy_R A B := abs_nonneg _
  have hdx_le : absDx_R A B ≤ 2000 := by
    unfold absDx_R
    have := abs_le.mp hAx_r; have := abs_le.mp hBx_r
    rw [abs_le]; constructor <;> linarith
  have hdy_le : absDy_R A B ≤ 2000 := by
    unfold absDy_R
    have := abs_le.mp hAy_r; have := abs_le.mp hBy_r
    rw [abs_le]; constructor <;> linarith
  have hcurX : |(if stepX > 0 then cx + 1 else cx : ℤ)| ≤ 2000 := by
    have := abs_le.mp hcx; rw [abs_le]; split_ifs <;> omega
  have hcurY : |(if stepY > 0 then cy + 1 else cy : ℤ)| ≤ 2000 := by
    have := abs_le.mp hcy; rw [abs_le]; split_ifs <;> omega
  have hcurX_r : |((if stepX > 0 then cx + 1 else cx : ℤ) : ℝ)| ≤ 2000 := by exact_mod_cast hcurX
  have hcurY_r : |((if stepY > 0 then cy + 1 else cy : ℤ) : ℝ)| ≤ 2000 := by exact_mod_cast hcurY
  have hremX_le : remX_R A stepX cx ≤ 3000 := by
    unfold remX_R
    have := abs_le.mp hcurX_r; have := abs_le.mp hAx_r
    rw [abs_le]; constructor <;> linarith
  have hremY_le : remY_R A stepY cy ≤ 3000 := by
    unfold remY_R
    have := abs_le.mp hcurY_r; have := abs_le.mp hAy_r
    rw [abs_le]; constructor <;> linarith
  have hremX0 : 0 ≤ remX_R A stepX cx := abs_nonneg _
  have hremY0 : 0 ≤ remY_R A stepY cy := abs_nonneg _
  refine ⟨hdx0, hdx_le, hdy0, hdy_le, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold crossX_R; positivity
  · unfold crossX_R; nlinarith
  · unfold crossY_R; positivity
  · unfold crossY_R; nlinarith
  · unfold limitCross_R; positivity
  · unfold limitCross_R; nlinarith
  · unfold limitCross_R; nlinarith

theorem crossProducts_float_approx_rel (A B : Point32) (stepX stepY : ℤ) (c : Cell)
    (h_finA : A.isFinite) (h_finB : B.isFinite)
    (h_bound : inCoordBounds mainCoordBound A.toPoint B.toPoint)
    (hcx : |c.x| ≤ 1995) (hcy : |c.y| ≤ 1995) :
    let currentX := if stepX > 0 then c.x + 1 else c.x
    let currentY := if stepY > 0 then c.y + 1 else c.y
    let xb : Binary64 := widen32To64 (intToBinary32 currentX)
    let yb : Binary64 := widen32To64 (intToBinary32 currentY)
    let startX : Binary64 := widen32To64 A.x
    let startY : Binary64 := widen32To64 A.y
    let absDx : Binary64 := ExecFloat.Binary.abs (widen32To64 (B.x - A.x))
    let absDy : Binary64 := ExecFloat.Binary.abs (widen32To64 (B.y - A.y))
    let remX : Binary64 := ExecFloat.Binary.abs (xb - startX)
    let remY : Binary64 := ExecFloat.Binary.abs (yb - startY)
    let crossX : Binary64 := remX * absDy
    let crossY : Binary64 := remY * absDx
    let limitCross : Binary64 := absDx * absDy
    ExecFloat.Binary.isFinite crossX = true ∧
    ExecFloat.Binary.isFinite crossY = true ∧
    ExecFloat.Binary.isFinite limitCross = true ∧
    |Model.toReal (ExecFloat.Binary.toModel crossX) - crossX_R A B stepX c.x| ≤
      (1 / 5000000 : ℝ) * crossX_R A B stepX c.x ∧
    |Model.toReal (ExecFloat.Binary.toModel crossY) - crossY_R A B stepY c.y| ≤
      (1 / 5000000 : ℝ) * crossY_R A B stepY c.y ∧
    |Model.toReal (ExecFloat.Binary.toModel limitCross) - limitCross_R A B| ≤
      (1 / 5000000 : ℝ) * limitCross_R A B := by
  intro currentX currentY xb yb startX startY absDx absDy remX remY crossX crossY limitCross
  rcases h_bound with ⟨hAx_le, hAy_le, hBx_le, hBy_le⟩
  have hcurX_le : |currentX| ≤ 2000 := by
    have := abs_le.mp hcx; dsimp [currentX]; rw [abs_le]; split_ifs <;> omega
  have hcurY_le : |currentY| ≤ 2000 := by
    have := abs_le.mp hcy; dsimp [currentY]; rw [abs_le]; split_ifs <;> omega
  obtain ⟨hdx_fin, hdx_I, hdx_rel, hdx_bpow⟩ :=
    abs_toReal_absD_binary64_rel A.x B.x h_finA.1 h_finB.1 hAx_le hBx_le
  obtain ⟨hdy_fin, hdy_I, hdy_rel, hdy_bpow⟩ :=
    abs_toReal_absD_binary64_rel A.y B.y h_finA.2 h_finB.2 hAy_le hBy_le
  obtain ⟨hremX_fin, hremX_I, hremX_rel, hremX_bpow⟩ :=
    abs_toReal_rem_binary64_rel A.x currentX h_finA.1 hAx_le hcurX_le
  obtain ⟨hremY_fin, hremY_I, hremY_rel, hremY_bpow⟩ :=
    abs_toReal_rem_binary64_rel A.y currentY h_finA.2 hAy_le hcurY_le
  have hdx_eq : |((binary32ToRat B.x - binary32ToRat A.x : ℚ) : ℝ)| = absDx_R A B := by
    unfold absDx_R Point32.toPoint; push_cast; rfl
  have hdy_eq : |((binary32ToRat B.y - binary32ToRat A.y : ℚ) : ℝ)| = absDy_R A B := by
    unfold absDy_R Point32.toPoint; push_cast; rfl
  have hremX_eq : |(currentX : ℝ) - ((binary32ToRat A.x : ℚ) : ℝ)| = remX_R A stepX c.x := by
    unfold remX_R Point32.toPoint; rfl
  have hremY_eq : |(currentY : ℝ) - ((binary32ToRat A.y : ℚ) : ℝ)| = remY_R A stepY c.y := by
    unfold remY_R Point32.toPoint; rfl
  rw [hdx_eq] at hdx_I hdx_rel
  rw [hdy_eq] at hdy_I hdy_rel
  rw [hremX_eq] at hremX_I hremX_rel
  rw [hremY_eq] at hremY_I hremY_rel
  obtain ⟨hcrossX_fin, hcrossX_rel⟩ :=
    binary64_mul_approx_rel remX absDy (remX_R A stepX c.x) (absDy_R A B)
      hremX_fin hdy_fin hremX_I hdy_I hremX_rel hdy_rel hremX_bpow hdy_bpow
  obtain ⟨hcrossY_fin, hcrossY_rel⟩ :=
    binary64_mul_approx_rel remY absDx (remY_R A stepY c.y) (absDx_R A B)
      hremY_fin hdx_fin hremY_I hdx_I hremY_rel hdx_rel hremY_bpow hdx_bpow
  obtain ⟨hlimit_fin, hlimit_rel⟩ :=
    binary64_mul_approx_rel absDx absDy (absDx_R A B) (absDy_R A B)
      hdx_fin hdy_fin hdx_I hdy_I hdx_rel hdy_rel hdx_bpow hdy_bpow
  exact ⟨hcrossX_fin, hcrossY_fin, hlimit_fin, hcrossX_rel, hcrossY_rel, hlimit_rel⟩

theorem remX_R_step (A : Point32) (stepX cx : ℤ)
    (h : (stepX = 1 ∧ (floorPoint A.toPoint).x ≤ cx) ∨
         (stepX = -1 ∧ cx ≤ (floorPoint A.toPoint).x)) :
    remX_R A stepX (cx + stepX) = remX_R A stepX cx + 1 := by
  have hfl_le : ((floorPoint A.toPoint).x : ℝ) ≤ (A.toPoint.x : ℝ) := by
    have := Rat.floor_le A.toPoint.x
    exact_mod_cast this
  have hfl_lt : (A.toPoint.x : ℝ) < ((floorPoint A.toPoint).x : ℝ) + 1 := by
    have := Rat.lt_floor_add_one A.toPoint.x
    exact_mod_cast this
  rcases h with ⟨rfl, hle⟩ | ⟨rfl, hle⟩
  · have hle_r : ((floorPoint A.toPoint).x : ℝ) ≤ (cx : ℝ) := by exact_mod_cast hle
    unfold remX_R
    simp only [gt_iff_lt, zero_lt_one, ↓reduceIte, Int.cast_add, Int.cast_one]
    rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
    ring
  · have hle_r : (cx : ℝ) ≤ ((floorPoint A.toPoint).x : ℝ) := by exact_mod_cast hle
    unfold remX_R
    have hnot : ¬ ((-1 : ℤ) > 0) := by decide
    simp only [hnot, ↓reduceIte, Int.cast_add, Int.cast_neg, Int.cast_one]
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    ring

theorem remY_R_step (A : Point32) (stepY cy : ℤ)
    (h : (stepY = 1 ∧ (floorPoint A.toPoint).y ≤ cy) ∨
         (stepY = -1 ∧ cy ≤ (floorPoint A.toPoint).y)) :
    remY_R A stepY (cy + stepY) = remY_R A stepY cy + 1 := by
  have hfl_le : ((floorPoint A.toPoint).y : ℝ) ≤ (A.toPoint.y : ℝ) := by
    have := Rat.floor_le A.toPoint.y
    exact_mod_cast this
  have hfl_lt : (A.toPoint.y : ℝ) < ((floorPoint A.toPoint).y : ℝ) + 1 := by
    have := Rat.lt_floor_add_one A.toPoint.y
    exact_mod_cast this
  rcases h with ⟨rfl, hle⟩ | ⟨rfl, hle⟩
  · have hle_r : ((floorPoint A.toPoint).y : ℝ) ≤ (cy : ℝ) := by exact_mod_cast hle
    unfold remY_R
    simp only [gt_iff_lt, zero_lt_one, ↓reduceIte, Int.cast_add, Int.cast_one]
    rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
    ring
  · have hle_r : (cy : ℝ) ≤ ((floorPoint A.toPoint).y : ℝ) := by exact_mod_cast hle
    unfold remY_R
    have hnot : ¬ ((-1 : ℤ) > 0) := by decide
    simp only [hnot, ↓reduceIte, Int.cast_add, Int.cast_neg, Int.cast_one]
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    ring

theorem crossX_R_step (A B : Point32) (stepX cx : ℤ)
    (h : (stepX = 1 ∧ (floorPoint A.toPoint).x ≤ cx) ∨
         (stepX = -1 ∧ cx ≤ (floorPoint A.toPoint).x)) :
    crossX_R A B stepX (cx + stepX) = crossX_R A B stepX cx + absDy_R A B ∧
    crossX_R A B stepX (cx + 2 * stepX) = crossX_R A B stepX cx + 2 * absDy_R A B := by
  have h1 := remX_R_step A stepX cx h
  have h_next : (stepX = 1 ∧ (floorPoint A.toPoint).x ≤ cx + stepX) ∨
                (stepX = -1 ∧ cx + stepX ≤ (floorPoint A.toPoint).x) := by
    rcases h with ⟨rfl, hle⟩ | ⟨rfl, hle⟩
    · left; exact ⟨rfl, by omega⟩
    · right; exact ⟨rfl, by omega⟩
  have h2 := remX_R_step A stepX (cx + stepX) h_next
  have heq2 : cx + stepX + stepX = cx + 2 * stepX := by omega
  rw [heq2] at h2
  constructor
  · unfold crossX_R; rw [h1]; ring
  · unfold crossX_R; rw [h2, h1]; ring

theorem crossY_R_step (A B : Point32) (stepY cy : ℤ)
    (h : (stepY = 1 ∧ (floorPoint A.toPoint).y ≤ cy) ∨
         (stepY = -1 ∧ cy ≤ (floorPoint A.toPoint).y)) :
    crossY_R A B stepY (cy + stepY) = crossY_R A B stepY cy + absDx_R A B ∧
    crossY_R A B stepY (cy + 2 * stepY) = crossY_R A B stepY cy + 2 * absDx_R A B := by
  have h1 := remY_R_step A stepY cy h
  have h_next : (stepY = 1 ∧ (floorPoint A.toPoint).y ≤ cy + stepY) ∨
                (stepY = -1 ∧ cy + stepY ≤ (floorPoint A.toPoint).y) := by
    rcases h with ⟨rfl, hle⟩ | ⟨rfl, hle⟩
    · left; exact ⟨rfl, by omega⟩
    · right; exact ⟨rfl, by omega⟩
  have h2 := remY_R_step A stepY (cy + stepY) h_next
  have heq2 : cy + stepY + stepY = cy + 2 * stepY := by omega
  rw [heq2] at h2
  constructor
  · unfold crossY_R; rw [h1]; ring
  · unfold crossY_R; rw [h2, h1]; ring

theorem rayMarchStepFloat_real_bounds (A B : Point32) (stepX stepY : ℤ) (c : Cell)
    (h_finA : A.isFinite) (h_finB : B.isFinite)
    (h_bound : inCoordBounds mainCoordBound A.toPoint B.toPoint)
    (hx0 : (stepX == 0) = false) (hy0 : (stepY == 0) = false)
    (hcx : |c.x| ≤ 1995) (hcy : |c.y| ≤ 1995) :
    let ε : ℝ := 1 / 5000000
    let s := rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY c
    (s.2 = true →
      (1 - ε) * limitCross_R A B ≤ (1 + ε) * crossX_R A B stepX c.x ∧
      (1 - ε) * limitCross_R A B ≤ (1 + ε) * crossY_R A B stepY c.y) ∧
    (s.2 = false →
      ((1 - ε) * crossX_R A B stepX c.x < (1 + ε) * limitCross_R A B ∨
       (1 - ε) * crossY_R A B stepY c.y < (1 + ε) * limitCross_R A B) ∧
      (s.1 = ⟨c.x + stepX, c.y⟩ →
        (1 - ε) * crossX_R A B stepX c.x < (1 + ε) * crossY_R A B stepY c.y ∧
        (1 - ε) * crossX_R A B stepX c.x < (1 + ε) * limitCross_R A B) ∧
      (s.1 = ⟨c.x, c.y + stepY⟩ →
        (1 - ε) * crossY_R A B stepY c.y < (1 + ε) * crossX_R A B stepX c.x ∧
        (1 - ε) * crossY_R A B stepY c.y < (1 + ε) * limitCross_R A B) ∧
      (s.1 = ⟨c.x + stepX, c.y + stepY⟩ →
        (1 - ε) * crossX_R A B stepX c.x ≤ (1 + ε) * crossY_R A B stepY c.y ∧
        (1 - ε) * crossY_R A B stepY c.y ≤ (1 + ε) * crossX_R A B stepX c.x ∧
        (1 - ε) * crossX_R A B stepX c.x < (1 + ε) * limitCross_R A B ∧
        (1 - ε) * crossY_R A B stepY c.y < (1 + ε) * limitCross_R A B)) := by
  intro ε s
  obtain ⟨hcx_fin, hcy_fin, hlim_fin, hcx_rel, hcy_rel, hlim_rel⟩ :=
    crossProducts_float_approx_rel A B stepX stepY c h_finA h_finB h_bound hcx hcy
  have hcx_b := abs_le.mp hcx_rel
  have hcy_b := abs_le.mp hcy_rel
  have hlim_b := abs_le.mp hlim_rel
  have hx_ne : stepX ≠ 0 := by intro h; rw [h] at hx0; contradiction
  have hy_ne : stepY ≠ 0 := by intro h; rw [h] at hy0; contradiction
  set currentX := if stepX > 0 then c.x + 1 else c.x
  set currentY := if stepY > 0 then c.y + 1 else c.y
  set xb : Binary64 := widen32To64 (intToBinary32 currentX)
  set yb : Binary64 := widen32To64 (intToBinary32 currentY)
  set startX : Binary64 := widen32To64 A.x
  set startY : Binary64 := widen32To64 A.y
  set absDx : Binary64 := ExecFloat.Binary.abs (widen32To64 (B.x - A.x))
  set absDy : Binary64 := ExecFloat.Binary.abs (widen32To64 (B.y - A.y))
  set remX : Binary64 := ExecFloat.Binary.abs (xb - startX)
  set remY : Binary64 := ExecFloat.Binary.abs (yb - startY)
  set crossX : Binary64 := remX * absDy
  set crossY : Binary64 := remY * absDx
  set limitCross : Binary64 := absDx * absDy
  have hs_eq : s = (if (crossX ⊓ crossY ≥ limitCross) then (c, true)
          else if crossX < crossY then (⟨c.x + stepX, c.y⟩, false)
          else if crossY < crossX then (⟨c.x, c.y + stepY⟩, false)
          else (⟨c.x + stepX, c.y + stepY⟩, false)) := by
    dsimp [s]; unfold rayMarchStepFloat
    rw [hx0, hy0]
    simp only [Bool.false_eq_true, ite_false]
    rfl
  constructor
  · intro h_done
    rw [hs_eq] at h_done
    split_ifs at h_done with h_min
    · have ⟨h1, h2⟩ := (min_ge_iff_of_isFinite_binary64 crossX crossY limitCross hcx_fin hcy_fin hlim_fin).mp h_min
      have h1_r := toReal_ge_of_ge_binary64 crossX limitCross hcx_fin hlim_fin h1
      have h2_r := toReal_ge_of_ge_binary64 crossY limitCross hcy_fin hlim_fin h2
      dsimp [ε]; constructor <;> linarith
    all_goals (simp at h_done)
  · intro h_ndone
    have h_min : ¬(crossX ⊓ crossY ≥ limitCross) := by
      intro h_ge
      rw [hs_eq, if_pos h_ge] at h_ndone
      simp at h_ndone
    have h_not_both : ¬ (crossX ≥ limitCross ∧ crossY ≥ limitCross) := by
      intro hboth
      exact h_min ((min_ge_iff_of_isFinite_binary64 crossX crossY limitCross hcx_fin hcy_fin hlim_fin).mpr hboth)
    by_cases h_x : crossX < crossY
    · have hx_lt_y := toReal_lt_of_lt_binary64 crossX crossY hcx_fin hcy_fin h_x
      have hx_lt_lim : Model.toReal (ExecFloat.Binary.toModel crossX) <
          Model.toReal (ExecFloat.Binary.toModel limitCross) := by
        by_contra hge
        push_neg at hge
        have hcx_ge := ge_of_toReal_ge crossX limitCross hcx_fin hlim_fin hge
        have hcy_ge := ge_of_toReal_ge crossY limitCross hcy_fin hlim_fin (by linarith)
        exact h_not_both ⟨hcx_ge, hcy_ge⟩
      have hs1 : s.1 = ⟨c.x + stepX, c.y⟩ := by
        rw [hs_eq, if_neg h_min, if_pos h_x]
      refine ⟨Or.inl (by dsimp [ε]; linarith), ?_, ?_, ?_⟩
      · intro _; dsimp [ε]; constructor <;> linarith
      · intro h_eq; rw [hs1] at h_eq
        have := congr_arg Cell.x h_eq; dsimp only [] at this; omega
      · intro h_eq; rw [hs1] at h_eq
        have := congr_arg Cell.y h_eq; dsimp only [] at this; omega
    · by_cases h_y : crossY < crossX
      · have hy_lt_x := toReal_lt_of_lt_binary64 crossY crossX hcy_fin hcx_fin h_y
        have hy_lt_lim : Model.toReal (ExecFloat.Binary.toModel crossY) <
            Model.toReal (ExecFloat.Binary.toModel limitCross) := by
          by_contra hge
          push_neg at hge
          have hcy_ge := ge_of_toReal_ge crossY limitCross hcy_fin hlim_fin hge
          have hcx_ge := ge_of_toReal_ge crossX limitCross hcx_fin hlim_fin (by linarith)
          exact h_not_both ⟨hcx_ge, hcy_ge⟩
        have hs1 : s.1 = ⟨c.x, c.y + stepY⟩ := by
          rw [hs_eq, if_neg h_min, if_neg h_x, if_pos h_y]
        refine ⟨Or.inr (by dsimp [ε]; linarith), ?_, ?_, ?_⟩
        · intro h_eq; rw [hs1] at h_eq
          have := congr_arg Cell.x h_eq; dsimp only [] at this; omega
        · intro _; dsimp [ε]; constructor <;> linarith
        · intro h_eq; rw [hs1] at h_eq
          have := congr_arg Cell.x h_eq; dsimp only [] at this; omega
      · have h_eq_r : Model.toReal (ExecFloat.Binary.toModel crossX) =
            Model.toReal (ExecFloat.Binary.toModel crossY) := by
          rcases trichotomy_of_isFinite_binary64 crossX crossY hcx_fin hcy_fin with h1 | h2 | h3
          · exfalso; exact h_x h1
          · exfalso; exact h_y h2
          · exact h3
        have hx_lt_lim : Model.toReal (ExecFloat.Binary.toModel crossX) <
            Model.toReal (ExecFloat.Binary.toModel limitCross) := by
          by_contra hge
          push_neg at hge
          have hcx_ge := ge_of_toReal_ge crossX limitCross hcx_fin hlim_fin hge
          have hcy_ge := ge_of_toReal_ge crossY limitCross hcy_fin hlim_fin (by linarith)
          exact h_not_both ⟨hcx_ge, hcy_ge⟩
        have hs1 : s.1 = ⟨c.x + stepX, c.y + stepY⟩ := by
          rw [hs_eq, if_neg h_min, if_neg h_x, if_neg h_y]
        refine ⟨Or.inl (by dsimp [ε]; linarith), ?_, ?_, ?_⟩
        · intro h_eq; rw [hs1] at h_eq
          have := congr_arg Cell.y h_eq; dsimp only [] at this; omega
        · intro h_eq; rw [hs1] at h_eq
          have := congr_arg Cell.x h_eq; dsimp only [] at this; omega
        · intro _; dsimp [ε]; refine ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem rayMarchStep_real_bounds (A B : Point32) (stepX stepY : ℤ) (c : Cell)
    (hx0 : (stepX == 0) = false) (hy0 : (stepY == 0) = false) :
    let s := rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y) stepX stepY c
    (s.2 = true →
      limitCross_R A B ≤ crossX_R A B stepX c.x ∧
      limitCross_R A B ≤ crossY_R A B stepY c.y) ∧
    (s.2 = false →
      (crossX_R A B stepX c.x < limitCross_R A B ∨
       crossY_R A B stepY c.y < limitCross_R A B) ∧
      (s.1 = ⟨c.x + stepX, c.y⟩ →
        crossX_R A B stepX c.x < crossY_R A B stepY c.y ∧
        crossX_R A B stepX c.x < limitCross_R A B) ∧
      (s.1 = ⟨c.x, c.y + stepY⟩ →
        crossY_R A B stepY c.y < crossX_R A B stepX c.x ∧
        crossY_R A B stepY c.y < limitCross_R A B) ∧
      (s.1 = ⟨c.x + stepX, c.y + stepY⟩ →
        crossX_R A B stepX c.x = crossY_R A B stepY c.y ∧
        crossX_R A B stepX c.x < limitCross_R A B ∧
        crossY_R A B stepY c.y < limitCross_R A B)) := by
  intro s
  have hx_ne : stepX ≠ 0 := by intro h; rw [h] at hx0; contradiction
  have hy_ne : stepY ≠ 0 := by intro h; rw [h] at hy0; contradiction
  set currentX : ℚ := if stepX > 0 then Rat.ofInt (c.x + 1) else Rat.ofInt c.x
  set currentY : ℚ := if stepY > 0 then Rat.ofInt (c.y + 1) else Rat.ofInt c.y
  set remX : ℚ := if currentX ≥ A.toPoint.x then currentX - A.toPoint.x else A.toPoint.x - currentX
  set remY : ℚ := if currentY ≥ A.toPoint.y then currentY - A.toPoint.y else A.toPoint.y - currentY
  set absDx : ℚ := if B.toPoint.x - A.toPoint.x ≥ 0 then B.toPoint.x - A.toPoint.x else -(B.toPoint.x - A.toPoint.x)
  set absDy : ℚ := if B.toPoint.y - A.toPoint.y ≥ 0 then B.toPoint.y - A.toPoint.y else -(B.toPoint.y - A.toPoint.y)
  set crossX : ℚ := remX * absDy
  set crossY : ℚ := remY * absDx
  set limitCross : ℚ := absDx * absDy
  have hcurX_eq : (currentX : ℝ) = ((if stepX > 0 then c.x + 1 else c.x : ℤ) : ℝ) := by
    dsimp [currentX]; split_ifs <;> push_cast <;> ring
  have hcurY_eq : (currentY : ℝ) = ((if stepY > 0 then c.y + 1 else c.y : ℤ) : ℝ) := by
    dsimp [currentY]; split_ifs <;> push_cast <;> ring
  have hremX_eq : (remX : ℝ) = remX_R A stepX c.x := by
    unfold remX_R; rw [← hcurX_eq]; dsimp [remX]
    split_ifs with h
    · have h' : (A.toPoint.x : ℝ) ≤ (currentX : ℝ) := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]; push_cast; ring
    · have h' : (currentX : ℝ) < (A.toPoint.x : ℝ) := by exact_mod_cast not_le.mp h
      rw [abs_of_neg (by linarith)]; push_cast; ring
  have hremY_eq : (remY : ℝ) = remY_R A stepY c.y := by
    unfold remY_R; rw [← hcurY_eq]; dsimp [remY]
    split_ifs with h
    · have h' : (A.toPoint.y : ℝ) ≤ (currentY : ℝ) := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]; push_cast; ring
    · have h' : (currentY : ℝ) < (A.toPoint.y : ℝ) := by exact_mod_cast not_le.mp h
      rw [abs_of_neg (by linarith)]; push_cast; ring
  have habsDx_eq : (absDx : ℝ) = absDx_R A B := by
    unfold absDx_R; dsimp [absDx]
    split_ifs with h
    · have h' : (0 : ℝ) ≤ ((B.toPoint.x - A.toPoint.x : ℚ) : ℝ) := by exact_mod_cast h
      push_cast at h' ⊢; rw [abs_of_nonneg h']
    · have h' : ((B.toPoint.x - A.toPoint.x : ℚ) : ℝ) < 0 := by exact_mod_cast not_le.mp h
      push_cast at h' ⊢; rw [abs_of_neg h']
  have habsDy_eq : (absDy : ℝ) = absDy_R A B := by
    unfold absDy_R; dsimp [absDy]
    split_ifs with h
    · have h' : (0 : ℝ) ≤ ((B.toPoint.y - A.toPoint.y : ℚ) : ℝ) := by exact_mod_cast h
      push_cast at h' ⊢; rw [abs_of_nonneg h']
    · have h' : ((B.toPoint.y - A.toPoint.y : ℚ) : ℝ) < 0 := by exact_mod_cast not_le.mp h
      push_cast at h' ⊢; rw [abs_of_neg h']
  have hcx_eq : (crossX : ℝ) = crossX_R A B stepX c.x := by
    unfold crossX_R; dsimp [crossX]; push_cast; rw [hremX_eq, habsDy_eq]
  have hcy_eq : (crossY : ℝ) = crossY_R A B stepY c.y := by
    unfold crossY_R; dsimp [crossY]; push_cast; rw [hremY_eq, habsDx_eq]
  have hlim_eq : (limitCross : ℝ) = limitCross_R A B := by
    unfold limitCross_R; dsimp [limitCross]; push_cast; rw [habsDx_eq, habsDy_eq]
  have hs_eq : s = (if (min crossX crossY ≥ limitCross) then (c, true)
          else if crossX < crossY then (⟨c.x + stepX, c.y⟩, false)
          else if crossY < crossX then (⟨c.x, c.y + stepY⟩, false)
          else (⟨c.x + stepX, c.y + stepY⟩, false)) := by
    dsimp [s]; unfold rayMarchStep
    rw [hx0, hy0]
    simp only [Bool.false_eq_true, ite_false]
    rfl
  constructor
  · intro h_done
    rw [hs_eq] at h_done
    split_ifs at h_done with h_min
    · have h_min' : limitCross ≤ crossX ∧ limitCross ≤ crossY := le_inf_iff.mp h_min
      have h1 : (limitCross : ℝ) ≤ (crossX : ℝ) := by exact_mod_cast h_min'.1
      have h2 : (limitCross : ℝ) ≤ (crossY : ℝ) := by exact_mod_cast h_min'.2
      rw [hcx_eq, hlim_eq] at h1
      rw [hcy_eq, hlim_eq] at h2
      exact ⟨h1, h2⟩
    all_goals (simp at h_done)
  · intro h_ndone
    have h_min : ¬(min crossX crossY ≥ limitCross) := by
      intro h_ge
      rw [hs_eq, if_pos h_ge] at h_ndone
      simp at h_ndone
    have hmin_r : crossX_R A B stepX c.x < limitCross_R A B ∨ crossY_R A B stepY c.y < limitCross_R A B := by
      rcases min_lt_iff.mp (not_le.mp h_min) with h1 | h2
      · left; rw [← hcx_eq, ← hlim_eq]; exact_mod_cast h1
      · right; rw [← hcy_eq, ← hlim_eq]; exact_mod_cast h2
    by_cases h_x : crossX < crossY
    · have hx_r : crossX_R A B stepX c.x < crossY_R A B stepY c.y := by
        rw [← hcx_eq, ← hcy_eq]; exact_mod_cast h_x
      have hs1 : s.1 = ⟨c.x + stepX, c.y⟩ := by
        rw [hs_eq, if_neg h_min, if_pos h_x]
      refine ⟨hmin_r, ?_, ?_, ?_⟩
      · intro _; exact ⟨hx_r, by rcases hmin_r with h1 | h2 <;> linarith⟩
      · intro h_eq; rw [hs1] at h_eq
        have := congr_arg Cell.x h_eq; dsimp only [] at this; omega
      · intro h_eq; rw [hs1] at h_eq
        have := congr_arg Cell.y h_eq; dsimp only [] at this; omega
    · by_cases h_y : crossY < crossX
      · have hy_r : crossY_R A B stepY c.y < crossX_R A B stepX c.x := by
          rw [← hcx_eq, ← hcy_eq]; exact_mod_cast h_y
        have hs1 : s.1 = ⟨c.x, c.y + stepY⟩ := by
          rw [hs_eq, if_neg h_min, if_neg h_x, if_pos h_y]
        refine ⟨hmin_r, ?_, ?_, ?_⟩
        · intro h_eq; rw [hs1] at h_eq
          have := congr_arg Cell.x h_eq; dsimp only [] at this; omega
        · intro _; exact ⟨hy_r, by rcases hmin_r with h1 | h2 <;> linarith⟩
        · intro h_eq; rw [hs1] at h_eq
          have := congr_arg Cell.x h_eq; dsimp only [] at this; omega
      · have h_eq_q : crossX = crossY := le_antisymm (not_lt.mp h_y) (not_lt.mp h_x)
        have h_eq_r : crossX_R A B stepX c.x = crossY_R A B stepY c.y := by
          rw [← hcx_eq, ← hcy_eq]; exact_mod_cast h_eq_q
        have hs1 : s.1 = ⟨c.x + stepX, c.y + stepY⟩ := by
          rw [hs_eq, if_neg h_min, if_neg h_x, if_neg h_y]
        refine ⟨hmin_r, ?_, ?_, ?_⟩
        · intro h_eq; rw [hs1] at h_eq
          have := congr_arg Cell.y h_eq; dsimp only [] at this; omega
        · intro h_eq; rw [hs1] at h_eq
          have := congr_arg Cell.x h_eq; dsimp only [] at this; omega
        · intro _
          have hlt : crossX_R A B stepX c.x < limitCross_R A B := by
            rcases hmin_r with h1 | h2 <;> linarith
          exact ⟨h_eq_r, hlt, by linarith⟩

theorem floor_mono_rat {q1 q2 : ℚ} (h : q1 ≤ q2) : q1.floor ≤ q2.floor := by
  have h1 : ((q1.floor : ℤ) : ℚ) ≤ q1 := Rat.floor_le q1
  have h2 : q2 < (((q2.floor + 1 : ℤ) : ℚ)) := Rat.lt_floor_add_one q2
  have h3 : ((q1.floor : ℤ) : ℚ) < (((q2.floor + 1 : ℤ) : ℚ)) :=
    lt_of_le_of_lt (le_trans h1 h) h2
  have h4 : q1.floor < q2.floor + 1 := by exact_mod_cast h3
  omega

theorem floor_bounds_mainCoordBound {q : ℚ} (h : |q| ≤ mainCoordBound) :
    -1000 ≤ q.floor ∧ q.floor ≤ 1000 := by
  have h1000 : |q| ≤ 1000 := h
  obtain ⟨h1, h2⟩ := abs_le.mp h1000
  have hfl1 : ((-1000 : ℤ) : ℚ).floor ≤ q.floor := floor_mono_rat h1
  have hfl2 : q.floor ≤ ((1000 : ℤ) : ℚ).floor := floor_mono_rat h2
  have heq1 : ((-1000 : ℤ) : ℚ).floor = -1000 := by decide
  have heq2 : ((1000 : ℤ) : ℚ).floor = 1000 := by decide
  omega

theorem remX_R_ge_absDx_of_ge_endCell (A B : Point32) (stepX cx : ℤ)
    (h_step : (stepX = 1 ∧ A.toPoint.x ≤ B.toPoint.x ∧ (floorPoint B.toPoint).x ≤ cx) ∨
              (stepX = -1 ∧ B.toPoint.x ≤ A.toPoint.x ∧ cx ≤ (floorPoint B.toPoint).x)) :
    absDx_R A B ≤ remX_R A stepX cx := by
  unfold absDx_R remX_R
  rcases h_step with ⟨rfl, hab, hcx⟩ | ⟨rfl, hab, hcx⟩
  · have hab_r : (A.toPoint.x : ℝ) ≤ (B.toPoint.x : ℝ) := by exact_mod_cast hab
    have hfl := Rat.lt_floor_add_one B.toPoint.x
    change B.toPoint.x < (((floorPoint B.toPoint).x + 1 : ℤ) : ℚ) at hfl
    push_cast at hfl
    have hfl_r : (B.toPoint.x : ℝ) ≤ ((floorPoint B.toPoint).x : ℝ) + 1 :=
      le_of_lt (by exact_mod_cast hfl)
    have hcx_r : ((floorPoint B.toPoint).x : ℝ) ≤ (cx : ℝ) := by exact_mod_cast hcx
    have hpos : (0 : ℤ) < 1 := by decide
    rw [if_pos hpos]
    push_cast
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · have hab_r : (B.toPoint.x : ℝ) ≤ (A.toPoint.x : ℝ) := by exact_mod_cast hab
    have hfl : ((floorPoint B.toPoint).x : ℚ) ≤ B.toPoint.x :=
      Rat.floor_le B.toPoint.x
    have hfl_r : ((floorPoint B.toPoint).x : ℝ) ≤ (B.toPoint.x : ℝ) := by exact_mod_cast hfl
    have hcx_r : (cx : ℝ) ≤ ((floorPoint B.toPoint).x : ℝ) := by exact_mod_cast hcx
    have hneg : ¬ ((0 : ℤ) < -1) := by decide
    rw [if_neg hneg]
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith

theorem remY_R_ge_absDy_of_ge_endCell (A B : Point32) (stepY cy : ℤ)
    (h_step : (stepY = 1 ∧ A.toPoint.y ≤ B.toPoint.y ∧ (floorPoint B.toPoint).y ≤ cy) ∨
              (stepY = -1 ∧ B.toPoint.y ≤ A.toPoint.y ∧ cy ≤ (floorPoint B.toPoint).y)) :
    absDy_R A B ≤ remY_R A stepY cy := by
  unfold absDy_R remY_R
  rcases h_step with ⟨rfl, hab, hcy⟩ | ⟨rfl, hab, hcy⟩
  · have hab_r : (A.toPoint.y : ℝ) ≤ (B.toPoint.y : ℝ) := by exact_mod_cast hab
    have hfl := Rat.lt_floor_add_one B.toPoint.y
    change B.toPoint.y < (((floorPoint B.toPoint).y + 1 : ℤ) : ℚ) at hfl
    push_cast at hfl
    have hfl_r : (B.toPoint.y : ℝ) ≤ ((floorPoint B.toPoint).y : ℝ) + 1 :=
      le_of_lt (by exact_mod_cast hfl)
    have hcy_r : ((floorPoint B.toPoint).y : ℝ) ≤ (cy : ℝ) := by exact_mod_cast hcy
    have hpos : (0 : ℤ) < 1 := by decide
    rw [if_pos hpos]
    push_cast
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · have hab_r : (B.toPoint.y : ℝ) ≤ (A.toPoint.y : ℝ) := by exact_mod_cast hab
    have hfl : ((floorPoint B.toPoint).y : ℚ) ≤ B.toPoint.y :=
      Rat.floor_le B.toPoint.y
    have hfl_r : ((floorPoint B.toPoint).y : ℝ) ≤ (B.toPoint.y : ℝ) := by exact_mod_cast hfl
    have hcy_r : (cy : ℝ) ≤ ((floorPoint B.toPoint).y : ℝ) := by exact_mod_cast hcy
    have hneg : ¬ ((0 : ℤ) < -1) := by decide
    rw [if_neg hneg]
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith

theorem crossX_R_ge_limitCross_of_ge_endCell (A B : Point32) (stepX cx : ℤ)
    (h_step : (stepX = 1 ∧ A.toPoint.x ≤ B.toPoint.x ∧ (floorPoint B.toPoint).x ≤ cx) ∨
              (stepX = -1 ∧ B.toPoint.x ≤ A.toPoint.x ∧ cx ≤ (floorPoint B.toPoint).x)) :
    limitCross_R A B ≤ crossX_R A B stepX cx := by
  have hrem := remX_R_ge_absDx_of_ge_endCell A B stepX cx h_step
  have hdy : 0 ≤ absDy_R A B := abs_nonneg _
  unfold limitCross_R crossX_R
  exact mul_le_mul_of_nonneg_right hrem hdy

theorem crossY_R_ge_limitCross_of_ge_endCell (A B : Point32) (stepY cy : ℤ)
    (h_step : (stepY = 1 ∧ A.toPoint.y ≤ B.toPoint.y ∧ (floorPoint B.toPoint).y ≤ cy) ∨
              (stepY = -1 ∧ B.toPoint.y ≤ A.toPoint.y ∧ cy ≤ (floorPoint B.toPoint).y)) :
    limitCross_R A B ≤ crossY_R A B stepY cy := by
  have hrem := remY_R_ge_absDy_of_ge_endCell A B stepY cy h_step
  have hdx : 0 ≤ absDx_R A B := abs_nonneg _
  unfold limitCross_R crossY_R
  rw [mul_comm (absDx_R A B)]
  exact mul_le_mul_of_nonneg_right hrem hdx

def CellInBox (A B : Point32) (stepX stepY : ℤ) (c : Cell) : Prop :=
  ((stepX = 1 ∧ A.toPoint.x < B.toPoint.x ∧ (floorPoint A.toPoint).x ≤ c.x ∧ c.x ≤ (floorPoint B.toPoint).x) ∨
   (stepX = -1 ∧ B.toPoint.x < A.toPoint.x ∧ (floorPoint B.toPoint).x ≤ c.x ∧ c.x ≤ (floorPoint A.toPoint).x) ∨
   (stepX = 0 ∧ B.toPoint.x = A.toPoint.x ∧ c.x = (floorPoint A.toPoint).x ∧ c.x = (floorPoint B.toPoint).x)) ∧
  ((stepY = 1 ∧ A.toPoint.y < B.toPoint.y ∧ (floorPoint A.toPoint).y ≤ c.y ∧ c.y ≤ (floorPoint B.toPoint).y) ∨
   (stepY = -1 ∧ B.toPoint.y < A.toPoint.y ∧ (floorPoint B.toPoint).y ≤ c.y ∧ c.y ≤ (floorPoint A.toPoint).y) ∨
   (stepY = 0 ∧ B.toPoint.y = A.toPoint.y ∧ c.y = (floorPoint A.toPoint).y ∧ c.y = (floorPoint B.toPoint).y))

theorem cellInBox_bounds (A B : Point32) (stepX stepY : ℤ) (c : Cell)
    (h_bound : inCoordBounds mainCoordBound A.toPoint B.toPoint)
    (hc : CellInBox A B stepX stepY c) :
    |c.x| ≤ 1000 ∧ |c.y| ≤ 1000 := by
  obtain ⟨hAx, hAy, hBx, hBy⟩ := h_bound
  have hflAx : -1000 ≤ (floorPoint A.toPoint).x ∧ (floorPoint A.toPoint).x ≤ 1000 :=
    floor_bounds_mainCoordBound hAx
  have hflBx : -1000 ≤ (floorPoint B.toPoint).x ∧ (floorPoint B.toPoint).x ≤ 1000 :=
    floor_bounds_mainCoordBound hBx
  have hflAy : -1000 ≤ (floorPoint A.toPoint).y ∧ (floorPoint A.toPoint).y ≤ 1000 :=
    floor_bounds_mainCoordBound hAy
  have hflBy : -1000 ≤ (floorPoint B.toPoint).y ∧ (floorPoint B.toPoint).y ≤ 1000 :=
    floor_bounds_mainCoordBound hBy
  rcases hc with ⟨hcx, hcy⟩
  constructor
  · rcases hcx with ⟨_, _, h1, h2⟩ | ⟨_, _, h1, h2⟩ | ⟨_, _, h1, _⟩ <;>
      exact abs_le.mpr ⟨by omega, by omega⟩
  · rcases hcy with ⟨_, _, h1, h2⟩ | ⟨_, _, h1, h2⟩ | ⟨_, _, h1, _⟩ <;>
      exact abs_le.mpr ⟨by omega, by omega⟩

theorem cellInBox_start (A B : Point32)
    (h_stepX : (if B.x - A.x > 0.0 then (1 : ℤ) else if B.x - A.x < 0.0 then -1 else 0) =
               (if B.toPoint.x - A.toPoint.x > 0 then (1 : ℤ) else if B.toPoint.x - A.toPoint.x < 0 then -1 else 0))
    (h_stepY : (if B.y - A.y > 0.0 then (1 : ℤ) else if B.y - A.y < 0.0 then -1 else 0) =
               (if B.toPoint.y - A.toPoint.y > 0 then (1 : ℤ) else if B.toPoint.y - A.toPoint.y < 0 then -1 else 0)) :
    CellInBox A B
      (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0)
      (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0)
      (floorPoint A.toPoint) := by
  rw [h_stepX, h_stepY]
  constructor
  · split_ifs with hx1 hx2
    · left
      have hlt : A.toPoint.x < B.toPoint.x := by linarith
      have hle : (floorPoint A.toPoint).x ≤ (floorPoint B.toPoint).x :=
        floor_mono_rat (le_of_lt hlt)
      exact ⟨rfl, hlt, le_refl _, hle⟩
    · right; left
      have hlt : B.toPoint.x < A.toPoint.x := by linarith
      have hle : (floorPoint B.toPoint).x ≤ (floorPoint A.toPoint).x :=
        floor_mono_rat (le_of_lt hlt)
      exact ⟨rfl, hlt, hle, le_refl _⟩
    · right; right
      have heq : B.toPoint.x = A.toPoint.x := by linarith
      have hfl : (floorPoint A.toPoint).x = (floorPoint B.toPoint).x := by
        unfold floorPoint; rw [heq]
      exact ⟨rfl, heq, rfl, hfl⟩
  · split_ifs with hy1 hy2
    · left
      have hlt : A.toPoint.y < B.toPoint.y := by linarith
      have hle : (floorPoint A.toPoint).y ≤ (floorPoint B.toPoint).y :=
        floor_mono_rat (le_of_lt hlt)
      exact ⟨rfl, hlt, le_refl _, hle⟩
    · right; left
      have hlt : B.toPoint.y < A.toPoint.y := by linarith
      have hle : (floorPoint B.toPoint).y ≤ (floorPoint A.toPoint).y :=
        floor_mono_rat (le_of_lt hlt)
      exact ⟨rfl, hlt, hle, le_refl _⟩
    · right; right
      have heq : B.toPoint.y = A.toPoint.y := by linarith
      have hfl : (floorPoint A.toPoint).y = (floorPoint B.toPoint).y := by
        unfold floorPoint; rw [heq]
      exact ⟨rfl, heq, rfl, hfl⟩

theorem cx_ne_endCell_of_crossX_lt_limitCross (A B : Point32) (stepX : ℤ) (c : Cell)
    (hcx_box : (stepX = 1 ∧ A.toPoint.x < B.toPoint.x ∧ (floorPoint A.toPoint).x ≤ c.x ∧ c.x ≤ (floorPoint B.toPoint).x) ∨
               (stepX = -1 ∧ B.toPoint.x < A.toPoint.x ∧ (floorPoint B.toPoint).x ≤ c.x ∧ c.x ≤ (floorPoint A.toPoint).x))
    (hlt : crossX_R A B stepX c.x < limitCross_R A B) :
    c.x ≠ (floorPoint B.toPoint).x := by
  intro heq
  have hge : limitCross_R A B ≤ crossX_R A B stepX c.x := by
    apply crossX_R_ge_limitCross_of_ge_endCell
    rcases hcx_box with ⟨hs, hab, _, _⟩ | ⟨hs, hab, _, _⟩
    · left; exact ⟨hs, le_of_lt hab, by omega⟩
    · right; exact ⟨hs, le_of_lt hab, by omega⟩
  linarith

theorem cy_ne_endCell_of_crossY_lt_limitCross (A B : Point32) (stepY : ℤ) (c : Cell)
    (hcy_box : (stepY = 1 ∧ A.toPoint.y < B.toPoint.y ∧ (floorPoint A.toPoint).y ≤ c.y ∧ c.y ≤ (floorPoint B.toPoint).y) ∨
               (stepY = -1 ∧ B.toPoint.y < A.toPoint.y ∧ (floorPoint B.toPoint).y ≤ c.y ∧ c.y ≤ (floorPoint A.toPoint).y))
    (hlt : crossY_R A B stepY c.y < limitCross_R A B) :
    c.y ≠ (floorPoint B.toPoint).y := by
  intro heq
  have hge : limitCross_R A B ≤ crossY_R A B stepY c.y := by
    apply crossY_R_ge_limitCross_of_ge_endCell
    rcases hcy_box with ⟨hs, hab, _, _⟩ | ⟨hs, hab, _, _⟩
    · left; exact ⟨hs, le_of_lt hab, by omega⟩
    · right; exact ⟨hs, le_of_lt hab, by omega⟩
  linarith

theorem cell_eq_of_xy {c1 c2 : Cell} (hx : c1.x = c2.x) (hy : c1.y = c2.y) : c1 = c2 := by
  cases c1; cases c2; dsimp at hx hy; subst hx; subst hy; rfl

theorem rayMarchStep_preserves_cellInBox_and_dist (A B : Point32) (stepX stepY : ℤ) (c : Cell)
    (hc : CellInBox A B stepX stepY c)
    (hne : (c == floorPoint B.toPoint) = false)
    (h_ndone : (rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y) stepX stepY c).2 = false) :
    let next := (rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y) stepX stepY c).1
    CellInBox A B stepX stepY next ∧
    ((floorPoint B.toPoint).x - next.x).natAbs + ((floorPoint B.toPoint).y - next.y).natAbs <
      ((floorPoint B.toPoint).x - c.x).natAbs + ((floorPoint B.toPoint).y - c.y).natAbs := by
  dsimp only []
  set next := (rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y) stepX stepY c).1
  have hne_cell : c ≠ floorPoint B.toPoint := by
    intro h; rw [h, beq_self_eq_true] at hne; contradiction
  rcases hc with ⟨hcx_box, hcy_box⟩
  by_cases hx0 : (stepX == 0) = true
  · have hsx0 : stepX = 0 := eq_of_beq hx0
    obtain ⟨hcx_eq1, hcx_eq2, hcx_eq3⟩ : B.toPoint.x = A.toPoint.x ∧ c.x = (floorPoint A.toPoint).x ∧ c.x = (floorPoint B.toPoint).x := by
      rcases hcx_box with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h1, h2, h3⟩
      · omega
      · omega
      · exact ⟨h1, h2, h3⟩
    have hcy_ne : c.y ≠ (floorPoint B.toPoint).y :=
      fun hy => hne_cell (cell_eq_of_xy hcx_eq3 hy)
    have hnext_eq : next = ⟨c.x, c.y + stepY⟩ := by
      change (rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y) stepX stepY c).1 = _
      unfold rayMarchStep at h_ndone ⊢
      dsimp only [] at h_ndone ⊢
      rw [hx0, if_pos rfl] at h_ndone ⊢
      split_ifs at h_ndone ⊢ <;> simp at h_ndone ⊢
    rw [hnext_eq]
    dsimp only [CellInBox]
    rcases hcy_box with ⟨hsy, hab, h1, h2⟩ | ⟨hsy, hab, h1, h2⟩ | ⟨_, _, _, h3⟩
    · refine ⟨⟨Or.inr (Or.inr ⟨hsx0, hcx_eq1, hcx_eq2, hcx_eq3⟩),
               Or.inl ⟨hsy, hab, by omega, by omega⟩⟩, by omega⟩
    · refine ⟨⟨Or.inr (Or.inr ⟨hsx0, hcx_eq1, hcx_eq2, hcx_eq3⟩),
               Or.inr (Or.inl ⟨hsy, hab, by omega, by omega⟩)⟩, by omega⟩
    · exfalso; exact hcy_ne h3
  · have hx0_f : (stepX == 0) = false := Bool.eq_false_iff.mpr hx0
    have hcx_nz : (stepX = 1 ∧ A.toPoint.x < B.toPoint.x ∧ (floorPoint A.toPoint).x ≤ c.x ∧ c.x ≤ (floorPoint B.toPoint).x) ∨
                  (stepX = -1 ∧ B.toPoint.x < A.toPoint.x ∧ (floorPoint B.toPoint).x ≤ c.x ∧ c.x ≤ (floorPoint A.toPoint).x) := by
      rcases hcx_box with h1 | h2 | ⟨h3, _⟩
      · exact Or.inl h1
      · exact Or.inr h2
      · exfalso; rw [h3] at hx0_f; revert hx0_f; decide
    by_cases hy0 : (stepY == 0) = true
    · have hsy0 : stepY = 0 := eq_of_beq hy0
      obtain ⟨hcy_eq1, hcy_eq2, hcy_eq3⟩ : B.toPoint.y = A.toPoint.y ∧ c.y = (floorPoint A.toPoint).y ∧ c.y = (floorPoint B.toPoint).y := by
        rcases hcy_box with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h1, h2, h3⟩
        · omega
        · omega
        · exact ⟨h1, h2, h3⟩
      have hcx_ne : c.x ≠ (floorPoint B.toPoint).x :=
        fun hx => hne_cell (cell_eq_of_xy hx hcy_eq3)
      have hnext_eq : next = ⟨c.x + stepX, c.y⟩ := by
        change (rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y) stepX stepY c).1 = _
        unfold rayMarchStep at h_ndone ⊢
        dsimp only [] at h_ndone ⊢
        rw [hx0_f, hy0] at h_ndone ⊢
        simp only [Bool.false_eq_true, ite_false, ite_true] at h_ndone ⊢
        split_ifs at h_ndone ⊢ <;> simp at h_ndone ⊢
      rw [hnext_eq]
      dsimp only [CellInBox]
      rcases hcx_nz with ⟨hsx, hab, h1, h2⟩ | ⟨hsx, hab, h1, h2⟩
      · refine ⟨⟨Or.inl ⟨hsx, hab, by omega, by omega⟩,
                 Or.inr (Or.inr ⟨hsy0, hcy_eq1, hcy_eq2, hcy_eq3⟩)⟩, by omega⟩
      · refine ⟨⟨Or.inr (Or.inl ⟨hsx, hab, by omega, by omega⟩),
                 Or.inr (Or.inr ⟨hsy0, hcy_eq1, hcy_eq2, hcy_eq3⟩)⟩, by omega⟩
    · have hy0_f : (stepY == 0) = false := Bool.eq_false_iff.mpr hy0
      have hcy_nz : (stepY = 1 ∧ A.toPoint.y < B.toPoint.y ∧ (floorPoint A.toPoint).y ≤ c.y ∧ c.y ≤ (floorPoint B.toPoint).y) ∨
                    (stepY = -1 ∧ B.toPoint.y < A.toPoint.y ∧ (floorPoint B.toPoint).y ≤ c.y ∧ c.y ≤ (floorPoint A.toPoint).y) := by
        rcases hcy_box with h1 | h2 | ⟨h3, _⟩
        · exact Or.inl h1
        · exact Or.inr h2
        · exfalso; rw [h3] at hy0_f; revert hy0_f; decide
      have h_ideal := (rayMarchStep_real_bounds A B stepX stepY c hx0_f hy0_f).2 h_ndone
      have h_mem := rayMarchStep_mem A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y) stepX stepY c
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h_mem
      rcases h_mem with h_done | h_x | h_y | h_diag
      · have := congrArg Prod.snd h_done; rw [this] at h_ndone; contradiction
      · have hnext_x : next = ⟨c.x + stepX, c.y⟩ := congrArg Prod.fst h_x
        have hlt := (h_ideal.2.1 hnext_x).2
        have hcx_ne := cx_ne_endCell_of_crossX_lt_limitCross A B stepX c hcx_nz hlt
        rw [hnext_x]
        dsimp only [CellInBox]
        rcases hcx_nz with ⟨hsx, hab, h1, h2⟩ | ⟨hsx, hab, h1, h2⟩
        · refine ⟨⟨Or.inl ⟨hsx, hab, by omega, by omega⟩, hcy_box⟩, by omega⟩
        · refine ⟨⟨Or.inr (Or.inl ⟨hsx, hab, by omega, by omega⟩), hcy_box⟩, by omega⟩
      · have hnext_y : next = ⟨c.x, c.y + stepY⟩ := congrArg Prod.fst h_y
        have hlt := (h_ideal.2.2.1 hnext_y).2
        have hcy_ne := cy_ne_endCell_of_crossY_lt_limitCross A B stepY c hcy_nz hlt
        rw [hnext_y]
        dsimp only [CellInBox]
        rcases hcy_nz with ⟨hsy, hab, h1, h2⟩ | ⟨hsy, hab, h1, h2⟩
        · refine ⟨⟨hcx_box, Or.inl ⟨hsy, hab, by omega, by omega⟩⟩, by omega⟩
        · refine ⟨⟨hcx_box, Or.inr (Or.inl ⟨hsy, hab, by omega, by omega⟩)⟩, by omega⟩
      · have hnext_d : next = ⟨c.x + stepX, c.y + stepY⟩ := congrArg Prod.fst h_diag
        have hlt_x := (h_ideal.2.2.2 hnext_d).2.1
        have hlt_y := (h_ideal.2.2.2 hnext_d).2.2
        have hcx_ne := cx_ne_endCell_of_crossX_lt_limitCross A B stepX c hcx_nz hlt_x
        have hcy_ne := cy_ne_endCell_of_crossY_lt_limitCross A B stepY c hcy_nz hlt_y
        rw [hnext_d]
        dsimp only [CellInBox]
        rcases hcx_nz with ⟨hsx, habx, hx1, hx2⟩ | ⟨hsx, habx, hx1, hx2⟩ <;>
        rcases hcy_nz with ⟨hsy, haby, hy1, hy2⟩ | ⟨hsy, haby, hy1, hy2⟩
        · refine ⟨⟨Or.inl ⟨hsx, habx, by omega, by omega⟩, Or.inl ⟨hsy, haby, by omega, by omega⟩⟩, by omega⟩
        · refine ⟨⟨Or.inl ⟨hsx, habx, by omega, by omega⟩, Or.inr (Or.inl ⟨hsy, haby, by omega, by omega⟩)⟩, by omega⟩
        · refine ⟨⟨Or.inr (Or.inl ⟨hsx, habx, by omega, by omega⟩), Or.inl ⟨hsy, haby, by omega, by omega⟩⟩, by omega⟩
        · refine ⟨⟨Or.inr (Or.inl ⟨hsx, habx, by omega, by omega⟩), Or.inr (Or.inl ⟨hsy, haby, by omega, by omega⟩)⟩, by omega⟩

theorem cellInBox_real_facts (A B : Point32) (stepX stepY : ℤ) (c : Cell)
    (h_bound : inCoordBounds mainCoordBound A.toPoint B.toPoint)
    (hc : CellInBox A B stepX stepY c)
    (hx0 : (stepX == 0) = false) (hy0 : (stepY == 0) = false) :
    (|c.x| ≤ 1995 ∧ |c.y| ≤ 1995 ∧
     |c.x + stepX| ≤ 1995 ∧ |c.y + stepY| ≤ 1995) ∧
    (0 < absDx_R A B ∧ 0 < absDy_R A B ∧ 0 < limitCross_R A B ∧
     0 ≤ crossX_R A B stepX c.x ∧ 0 ≤ crossY_R A B stepY c.y) ∧
    (limitCross_R A B ≤ 2000 * absDx_R A B ∧
     limitCross_R A B ≤ 2000 * absDy_R A B ∧
     crossX_R A B stepX c.x ≤ 3000 * absDy_R A B ∧
     crossY_R A B stepY c.y ≤ 3000 * absDx_R A B) ∧
    (crossX_R A B stepX (c.x + stepX) = crossX_R A B stepX c.x + absDy_R A B ∧
     crossX_R A B stepX (c.x + 2 * stepX) = crossX_R A B stepX c.x + 2 * absDy_R A B ∧
     crossY_R A B stepY (c.y + stepY) = crossY_R A B stepY c.y + absDx_R A B ∧
     crossY_R A B stepY (c.y + 2 * stepY) = crossY_R A B stepY c.y + 2 * absDx_R A B) ∧
    ((c.x = (floorPoint B.toPoint).x → limitCross_R A B ≤ crossX_R A B stepX c.x) ∧
     (c.x + stepX = (floorPoint B.toPoint).x → limitCross_R A B ≤ crossX_R A B stepX c.x + absDy_R A B) ∧
     (c.y = (floorPoint B.toPoint).y → limitCross_R A B ≤ crossY_R A B stepY c.y) ∧
     (c.y + stepY = (floorPoint B.toPoint).y → limitCross_R A B ≤ crossY_R A B stepY c.y + absDx_R A B)) := by
  obtain ⟨hcx_abs, hcy_abs⟩ := cellInBox_bounds A B stepX stepY c h_bound hc
  rcases hc with ⟨hcx_box, hcy_box⟩
  have hcx_nz : (stepX = 1 ∧ A.toPoint.x < B.toPoint.x ∧ (floorPoint A.toPoint).x ≤ c.x ∧ c.x ≤ (floorPoint B.toPoint).x) ∨
                (stepX = -1 ∧ B.toPoint.x < A.toPoint.x ∧ (floorPoint B.toPoint).x ≤ c.x ∧ c.x ≤ (floorPoint A.toPoint).x) := by
    rcases hcx_box with h1 | h2 | ⟨h3, _⟩
    · exact Or.inl h1
    · exact Or.inr h2
    · exfalso; rw [h3] at hx0; revert hx0; decide
  have hcy_nz : (stepY = 1 ∧ A.toPoint.y < B.toPoint.y ∧ (floorPoint A.toPoint).y ≤ c.y ∧ c.y ≤ (floorPoint B.toPoint).y) ∨
                (stepY = -1 ∧ B.toPoint.y < A.toPoint.y ∧ (floorPoint B.toPoint).y ≤ c.y ∧ c.y ≤ (floorPoint A.toPoint).y) := by
    rcases hcy_box with h1 | h2 | ⟨h3, _⟩
    · exact Or.inl h1
    · exact Or.inr h2
    · exfalso; rw [h3] at hy0; revert hy0; decide
  have hcx_step_abs : |c.x + stepX| ≤ 1995 := by
    have := abs_le.mp hcx_abs
    rcases hcx_nz with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> exact abs_le.mpr ⟨by omega, by omega⟩
  have hcy_step_abs : |c.y + stepY| ≤ 1995 := by
    have := abs_le.mp hcy_abs
    rcases hcy_nz with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> exact abs_le.mpr ⟨by omega, by omega⟩
  have hcx_1995 : |c.x| ≤ 1995 := le_trans hcx_abs (by norm_num)
  have hcy_1995 : |c.y| ≤ 1995 := le_trans hcy_abs (by norm_num)
  rcases crossProducts_R_bounds A B stepX stepY c.x c.y h_bound hcx_1995 hcy_1995 with
    ⟨hdx_ge, hdx_le, hdy_ge, hdy_le, hcxR_ge, hcx_le_dy, hcyR_ge, hcy_le_dx,
     _, hlim_dx, hlim_dy⟩
  have hdx_pos : 0 < absDx_R A B := by
    unfold absDx_R
    rcases hcx_nz with ⟨_, hab, _⟩ | ⟨_, hab, _⟩
    · have : (A.toPoint.x : ℝ) < (B.toPoint.x : ℝ) := by exact_mod_cast hab
      exact abs_pos.mpr (by linarith)
    · have : (B.toPoint.x : ℝ) < (A.toPoint.x : ℝ) := by exact_mod_cast hab
      exact abs_pos.mpr (by linarith)
  have hdy_pos : 0 < absDy_R A B := by
    unfold absDy_R
    rcases hcy_nz with ⟨_, hab, _⟩ | ⟨_, hab, _⟩
    · have : (A.toPoint.y : ℝ) < (B.toPoint.y : ℝ) := by exact_mod_cast hab
      exact abs_pos.mpr (by linarith)
    · have : (B.toPoint.y : ℝ) < (A.toPoint.y : ℝ) := by exact_mod_cast hab
      exact abs_pos.mpr (by linarith)
  have hlim_pos : 0 < limitCross_R A B := mul_pos hdx_pos hdy_pos
  have hx_step_cond : (stepX = 1 ∧ (floorPoint A.toPoint).x ≤ c.x) ∨
                      (stepX = -1 ∧ c.x ≤ (floorPoint A.toPoint).x) := by
    rcases hcx_nz with ⟨h1, _, h2, _⟩ | ⟨h1, _, _, h2⟩
    · left; exact ⟨h1, h2⟩
    · right; exact ⟨h1, h2⟩
  have hy_step_cond : (stepY = 1 ∧ (floorPoint A.toPoint).y ≤ c.y) ∨
                      (stepY = -1 ∧ c.y ≤ (floorPoint A.toPoint).y) := by
    rcases hcy_nz with ⟨h1, _, h2, _⟩ | ⟨h1, _, _, h2⟩
    · left; exact ⟨h1, h2⟩
    · right; exact ⟨h1, h2⟩
  obtain ⟨hcx_step1, hcx_step2⟩ := crossX_R_step A B stepX c.x hx_step_cond
  obtain ⟨hcy_step1, hcy_step2⟩ := crossY_R_step A B stepY c.y hy_step_cond
  refine ⟨⟨hcx_1995, hcy_1995, hcx_step_abs, hcy_step_abs⟩,
          ⟨hdx_pos, hdy_pos, hlim_pos, hcxR_ge, hcyR_ge⟩,
          ⟨hlim_dx, hlim_dy, hcx_le_dy, hcy_le_dx⟩,
          ⟨hcx_step1, hcx_step2, hcy_step1, hcy_step2⟩,
          ⟨?_, ?_, ?_, ?_⟩⟩
  · intro heq
    apply crossX_R_ge_limitCross_of_ge_endCell
    rcases hcx_nz with ⟨hs, hab, _⟩ | ⟨hs, hab, _⟩
    · left; exact ⟨hs, le_of_lt hab, by omega⟩
    · right; exact ⟨hs, le_of_lt hab, by omega⟩
  · intro heq
    rw [← hcx_step1]
    apply crossX_R_ge_limitCross_of_ge_endCell
    rcases hcx_nz with ⟨hs, hab, _⟩ | ⟨hs, hab, _⟩
    · left; exact ⟨hs, le_of_lt hab, by omega⟩
    · right; exact ⟨hs, le_of_lt hab, by omega⟩
  · intro heq
    apply crossY_R_ge_limitCross_of_ge_endCell
    rcases hcy_nz with ⟨hs, hab, _⟩ | ⟨hs, hab, _⟩
    · left; exact ⟨hs, le_of_lt hab, by omega⟩
    · right; exact ⟨hs, le_of_lt hab, by omega⟩
  · intro heq
    rw [← hcy_step1]
    apply crossY_R_ge_limitCross_of_ge_endCell
    rcases hcy_nz with ⟨hs, hab, _⟩ | ⟨hs, hab, _⟩
    · left; exact ⟨hs, le_of_lt hab, by omega⟩
    · right; exact ⟨hs, le_of_lt hab, by omega⟩

/--
Axis-aligned case `(stepX == 0) = true`: both `RayMarchCasesFloatExt3` and `RayMarchCasesIdealExt3`
hold at any `c` satisfying `CellInBox`.
-/
theorem rayMarch_axis_aligned_stepX_zero
    (A B : Point32) (stepX stepY : ℤ) (c : Cell)
    (h_finiteA : A.isFinite) (h_finiteB : B.isFinite)
    (h_bound : inCoordBounds mainCoordBound A.toPoint B.toPoint)
    (hc : CellInBox A B stepX stepY c)
    (hx0 : (stepX == 0) = true) :
    RayMarchCasesFloatExt A B.toPoint (B.x - A.x) (B.y - A.y)
      (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y)
      stepX stepY (floorPoint B.toPoint) c ∧
    RayMarchCasesIdealExt A B.toPoint (B.x - A.x) (B.y - A.y)
      (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y)
      stepX stepY (floorPoint B.toPoint) c := by
  obtain ⟨hcx_abs, hcy_abs⟩ := cellInBox_bounds A B stepX stepY c h_bound hc
  rcases hc with ⟨hcx_box, hcy_box⟩
  have hsx0 : stepX = 0 := eq_of_beq hx0
  have hcx_eq : c.x = (floorPoint B.toPoint).x := by
    rcases hcx_box with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, _, h3⟩ <;> omega
  by_cases hy0 : (stepY == 0) = true
  · have hsy0 : stepY = 0 := eq_of_beq hy0
    have hcy_eq : c.y = (floorPoint B.toPoint).y := by
      rcases hcy_box with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, _, h3⟩ <;> omega
    have hceq : (c == floorPoint B.toPoint) = true :=
      beq_iff_eq.mpr (cell_eq_of_xy hcx_eq hcy_eq)
    exact ⟨Or.inr (Or.inl (Or.inl hceq)),
           Or.inr (Or.inl (Or.inl hceq))⟩
  · rw [Bool.not_eq_true] at hy0
    have hcy_nz : (stepY = 1 ∧ A.toPoint.y < B.toPoint.y ∧ (floorPoint A.toPoint).y ≤ c.y ∧ c.y ≤ (floorPoint B.toPoint).y) ∨
                  (stepY = -1 ∧ B.toPoint.y < A.toPoint.y ∧ (floorPoint B.toPoint).y ≤ c.y ∧ c.y ≤ (floorPoint A.toPoint).y) := by
      rcases hcy_box with h1 | h2 | ⟨h3, _⟩
      · exact Or.inl h1
      · exact Or.inr h2
      · exfalso; rw [h3] at hy0; revert hy0; decide
    have hy_step_cond : (stepY = 1 ∧ (floorPoint A.toPoint).y ≤ c.y) ∨
                        (stepY = -1 ∧ c.y ≤ (floorPoint A.toPoint).y) := by
      rcases hcy_nz with ⟨h1, _, h2, _⟩ | ⟨h1, _, _, h2⟩
      · left; exact ⟨h1, h2⟩
      · right; exact ⟨h1, h2⟩
    have hremy_step := remY_R_step A stepY c.y hy_step_cond
    rcases h_bound with ⟨_, hAy_le, _, hBy_le⟩
    set curY0 : ℤ := if stepY > 0 then c.y + 1 else c.y
    set curY1 : ℤ := if stepY > 0 then (c.y + stepY) + 1 else c.y + stepY
    have hcurY0_le : |curY0| ≤ 2000 := by
      have := abs_le.mp hcy_abs; dsimp [curY0]; rw [abs_le]; split_ifs <;> omega
    have hcurY1_le : |curY1| ≤ 2000 := by
      have := abs_le.mp hcy_abs
      rcases hcy_nz with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> { dsimp [curY1]; rw [abs_le]; omega }
    obtain ⟨hremY0_fin, hremY0_bds, hremY0_rel, _⟩ :=
      abs_toReal_rem_binary64_rel A.y curY0 h_finiteA.2 hAy_le hcurY0_le
    obtain ⟨hremY1_fin, hremY1_bds, hremY1_rel, _⟩ :=
      abs_toReal_rem_binary64_rel A.y curY1 h_finiteA.2 hAy_le hcurY1_le
    obtain ⟨habsDy_fin, habsDy_bds, habsDy_rel, _⟩ :=
      abs_toReal_absD_binary64_rel A.y B.y h_finiteA.2 h_finiteB.2 hAy_le hBy_le
    have hdI_y : |((binary32ToRat B.y - binary32ToRat A.y : ℚ) : ℝ)| = absDy_R A B := by
      unfold absDy_R Point32.toPoint; push_cast; rfl
    rw [hdI_y] at habsDy_rel habsDy_bds
    change |Model.toReal (ExecFloat.Binary.toModel (ExecFloat.Binary.abs (widen32To64 (intToBinary32 curY0) - widen32To64 A.y))) - remY_R A stepY c.y| ≤
      (1 / 16777216 : ℝ) * remY_R A stepY c.y at hremY0_rel
    change |Model.toReal (ExecFloat.Binary.toModel (ExecFloat.Binary.abs (widen32To64 (intToBinary32 curY1) - widen32To64 A.y))) - remY_R A stepY (c.y + stepY)| ≤
      (1 / 16777216 : ℝ) * remY_R A stepY (c.y + stepY) at hremY1_rel
    change 0 ≤ remY_R A stepY c.y ∧ remY_R A stepY c.y ≤ 3000 at hremY0_bds
    have hremY0_b := abs_le.mp hremY0_rel
    have hremY1_b := abs_le.mp hremY0_rel
    have hremY1_b' := abs_le.mp hremY1_rel
    have habsDy_b := abs_le.mp habsDy_rel
    let remY64 (cy : ℤ) : Binary64 :=
      ExecFloat.Binary.abs (widen32To64 (intToBinary32 (if stepY > 0 then cy + 1 else cy)) - widen32To64 A.y)
    let absDy64 : Binary64 := ExecFloat.Binary.abs (widen32To64 (B.y - A.y))
    let ybQ (cy : ℤ) : ℚ := if stepY > 0 then ofInt (cy + 1) else ofInt cy
    let remYQ (cy : ℤ) : ℚ := if ybQ cy >= A.toPoint.y then ybQ cy - A.toPoint.y else A.toPoint.y - ybQ cy
    let absDyQ : ℚ := if B.toPoint.y - A.toPoint.y >= 0 then B.toPoint.y - A.toPoint.y else -(B.toPoint.y - A.toPoint.y)
    have hremYQ_eq (cy : ℤ) : (remYQ cy : ℝ) = remY_R A stepY cy := by
      have hyb : (ybQ cy : ℝ) = ((if stepY > 0 then cy + 1 else cy : ℤ) : ℝ) := by
        dsimp [ybQ, ofInt]; split_ifs <;> push_cast <;> ring
      unfold remY_R; rw [← hyb]; dsimp [remYQ]
      split_ifs with h
      · have h' : (A.toPoint.y : ℝ) ≤ (ybQ cy : ℝ) := by exact_mod_cast h
        rw [abs_of_nonneg (by linarith)]; push_cast; ring
      · have h' : (ybQ cy : ℝ) < (A.toPoint.y : ℝ) := by exact_mod_cast not_le.mp h
        rw [abs_of_neg (by linarith)]; push_cast; ring
    have habsDyQ_eq : (absDyQ : ℝ) = absDy_R A B := by
      unfold absDy_R; dsimp [absDyQ]
      split_ifs with h
      · have h' : (0 : ℝ) ≤ ((B.toPoint.y - A.toPoint.y : ℚ) : ℝ) := by exact_mod_cast h
        push_cast at h' ⊢; rw [abs_of_nonneg h']
      · have h' : ((B.toPoint.y - A.toPoint.y : ℚ) : ℝ) < 0 := by exact_mod_cast not_le.mp h
        push_cast at h' ⊢; rw [abs_of_neg h']
    have hF_eval (c' : Cell) :
        rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY c' =
          if remY64 c'.y ≥ absDy64 then (c', true) else (⟨c'.x, c'.y + stepY⟩, false) := by
      unfold rayMarchStepFloat; dsimp only []; rw [hx0, if_pos rfl]
    have hI_eval (c' : Cell) :
        rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y) stepX stepY c' =
          if remYQ c'.y ≥ absDyQ then (c', true) else (⟨c'.x, c'.y + stepY⟩, false) := by
      unfold rayMarchStep; dsimp only []; rw [hx0, if_pos rfl]
    by_cases hcondF : remY64 c.y ≥ absDy64
    · by_cases hcondI : remYQ c.y ≥ absDyQ
      · have hF_c : rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY c = (c, true) := by
          rw [hF_eval c, if_pos hcondF]
        have hI_c : rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y) stepX stepY c = (c, true) := by
          rw [hI_eval c, if_pos hcondI]
        exact ⟨Or.inl ⟨by rw [hF_c, hI_c], by rw [hF_c, hI_c]⟩,
               Or.inl ⟨by rw [hF_c, hI_c], by rw [hF_c, hI_c]⟩⟩
      · have hF_c : rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY c = (c, true) := by
          rw [hF_eval c, if_pos hcondF]
        have hI_c : rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y) stepX stepY c = (⟨c.x, c.y + stepY⟩, false) := by
          rw [hI_eval c, if_neg hcondI]
        have hF_le := toReal_ge_of_ge_binary64 (remY64 c.y) absDy64 hremY0_fin habsDy_fin hcondF
        have hI_next_ge : remYQ (c.y + stepY) ≥ absDyQ := by
          have hR : absDy_R A B ≤ remY_R A stepY (c.y + stepY) := by linarith
          rw [← habsDyQ_eq, ← hremYQ_eq (c.y + stepY)] at hR
          exact_mod_cast hR
        have hI_c1 : rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y) stepX stepY ⟨c.x, c.y + stepY⟩ = (⟨c.x, c.y + stepY⟩, true) := by
          rw [hI_eval ⟨c.x, c.y + stepY⟩, if_pos hI_next_ge]
        refine ⟨Or.inr (Or.inl (Or.inr (Or.inl (by rw [hF_c])))),
                Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (by rw [hI_c, hI_c1])))))⟩
    · by_cases hcondI : remYQ c.y ≥ absDyQ
      · have hF_c : rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY c = (⟨c.x, c.y + stepY⟩, false) := by
          rw [hF_eval c, if_neg hcondF]
        have hI_c : rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y) stepX stepY c = (c, true) := by
          rw [hI_eval c, if_pos hcondI]
        have hI_le_R : absDy_R A B ≤ remY_R A stepY c.y := by
          rw [← habsDyQ_eq, ← hremYQ_eq c.y]
          exact_mod_cast hcondI
        have hF_next_ge : remY64 (c.y + stepY) ≥ absDy64 := by
          apply ge_of_toReal_ge (remY64 (c.y + stepY)) absDy64 hremY1_fin habsDy_fin
          linarith
        have hF_c1 : rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY ⟨c.x, c.y + stepY⟩ = (⟨c.x, c.y + stepY⟩, true) := by
          rw [hF_eval ⟨c.x, c.y + stepY⟩, if_pos hF_next_ge]
        refine ⟨Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (by rw [hF_c, hF_c1]))))),
                Or.inr (Or.inl (Or.inr (Or.inl (by rw [hI_c]))))⟩
      · have hF_c : rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY c = (⟨c.x, c.y + stepY⟩, false) := by
          rw [hF_eval c, if_neg hcondF]
        have hI_c : rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y) stepX stepY c = (⟨c.x, c.y + stepY⟩, false) := by
          rw [hI_eval c, if_neg hcondI]
        exact ⟨Or.inl ⟨by rw [hF_c, hI_c], by rw [hF_c, hI_c]⟩,
               Or.inl ⟨by rw [hF_c, hI_c], by rw [hF_c, hI_c]⟩⟩

/--
Axis-aligned case `(stepX == 0) = false` and `(stepY == 0) = true`: both `RayMarchCasesFloatExt`
and `RayMarchCasesIdealExt` hold at any `c` satisfying `CellInBox`.
-/
theorem rayMarch_axis_aligned_stepY_zero
    (A B : Point32) (stepX stepY : ℤ) (c : Cell)
    (h_finiteA : A.isFinite) (h_finiteB : B.isFinite)
    (h_bound : inCoordBounds mainCoordBound A.toPoint B.toPoint)
    (hc : CellInBox A B stepX stepY c)
    (hx0 : (stepX == 0) = false)
    (hy0 : (stepY == 0) = true) :
    RayMarchCasesFloatExt A B.toPoint (B.x - A.x) (B.y - A.y)
      (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y)
      stepX stepY (floorPoint B.toPoint) c ∧
    RayMarchCasesIdealExt A B.toPoint (B.x - A.x) (B.y - A.y)
      (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y)
      stepX stepY (floorPoint B.toPoint) c := by
  obtain ⟨hcx_abs, hcy_abs⟩ := cellInBox_bounds A B stepX stepY c h_bound hc
  rcases hc with ⟨hcx_box, _⟩
  have hcx_nz : (stepX = 1 ∧ A.toPoint.x < B.toPoint.x ∧ (floorPoint A.toPoint).x ≤ c.x ∧ c.x ≤ (floorPoint B.toPoint).x) ∨
                (stepX = -1 ∧ B.toPoint.x < A.toPoint.x ∧ (floorPoint B.toPoint).x ≤ c.x ∧ c.x ≤ (floorPoint A.toPoint).x) := by
    rcases hcx_box with h1 | h2 | ⟨h3, _⟩
    · exact Or.inl h1
    · exact Or.inr h2
    · exfalso; rw [h3] at hx0; revert hx0; decide
  have hx_step_cond : (stepX = 1 ∧ (floorPoint A.toPoint).x ≤ c.x) ∨
                      (stepX = -1 ∧ c.x ≤ (floorPoint A.toPoint).x) := by
    rcases hcx_nz with ⟨h1, _, h2, _⟩ | ⟨h1, _, _, h2⟩
    · left; exact ⟨h1, h2⟩
    · right; exact ⟨h1, h2⟩
  have hremx_step := remX_R_step A stepX c.x hx_step_cond
  rcases h_bound with ⟨hAx_le, _, hBx_le, _⟩
  set curX0 : ℤ := if stepX > 0 then c.x + 1 else c.x
  set curX1 : ℤ := if stepX > 0 then (c.x + stepX) + 1 else c.x + stepX
  have hcurX0_le : |curX0| ≤ 2000 := by
    have := abs_le.mp hcx_abs; dsimp [curX0]; rw [abs_le]; split_ifs <;> omega
  have hcurX1_le : |curX1| ≤ 2000 := by
    have := abs_le.mp hcx_abs
    rcases hcx_nz with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> { dsimp [curX1]; rw [abs_le]; omega }
  obtain ⟨hremX0_fin, hremX0_bds, hremX0_rel, _⟩ :=
    abs_toReal_rem_binary64_rel A.x curX0 h_finiteA.1 hAx_le hcurX0_le
  obtain ⟨hremX1_fin, hremX1_bds, hremX1_rel, _⟩ :=
    abs_toReal_rem_binary64_rel A.x curX1 h_finiteA.1 hAx_le hcurX1_le
  obtain ⟨habsDx_fin, habsDx_bds, habsDx_rel, _⟩ :=
    abs_toReal_absD_binary64_rel A.x B.x h_finiteA.1 h_finiteB.1 hAx_le hBx_le
  have hdI_x : |((binary32ToRat B.x - binary32ToRat A.x : ℚ) : ℝ)| = absDx_R A B := by
    unfold absDx_R Point32.toPoint; push_cast; rfl
  rw [hdI_x] at habsDx_rel habsDx_bds
  change |Model.toReal (ExecFloat.Binary.toModel (ExecFloat.Binary.abs (widen32To64 (intToBinary32 curX0) - widen32To64 A.x))) - remX_R A stepX c.x| ≤
    (1 / 16777216 : ℝ) * remX_R A stepX c.x at hremX0_rel
  change |Model.toReal (ExecFloat.Binary.toModel (ExecFloat.Binary.abs (widen32To64 (intToBinary32 curX1) - widen32To64 A.x))) - remX_R A stepX (c.x + stepX)| ≤
    (1 / 16777216 : ℝ) * remX_R A stepX (c.x + stepX) at hremX1_rel
  change 0 ≤ remX_R A stepX c.x ∧ remX_R A stepX c.x ≤ 3000 at hremX0_bds
  have hremX0_b := abs_le.mp hremX0_rel
  have hremX1_b := abs_le.mp hremX1_rel
  have habsDx_b := abs_le.mp habsDx_rel
  let remX64 (cx : ℤ) : Binary64 :=
    ExecFloat.Binary.abs (widen32To64 (intToBinary32 (if stepX > 0 then cx + 1 else cx)) - widen32To64 A.x)
  let absDx64 : Binary64 := ExecFloat.Binary.abs (widen32To64 (B.x - A.x))
  let xbQ (cx : ℤ) : ℚ := if stepX > 0 then ofInt (cx + 1) else ofInt cx
  let remXQ (cx : ℤ) : ℚ := if xbQ cx >= A.toPoint.x then xbQ cx - A.toPoint.x else A.toPoint.x - xbQ cx
  let absDxQ : ℚ := if B.toPoint.x - A.toPoint.x >= 0 then B.toPoint.x - A.toPoint.x else -(B.toPoint.x - A.toPoint.x)
  have hremXQ_eq (cx : ℤ) : (remXQ cx : ℝ) = remX_R A stepX cx := by
    have hxb : (xbQ cx : ℝ) = ((if stepX > 0 then cx + 1 else cx : ℤ) : ℝ) := by
      dsimp [xbQ, ofInt]; split_ifs <;> push_cast <;> ring
    unfold remX_R; rw [← hxb]; dsimp [remXQ]
    split_ifs with h
    · have h' : (A.toPoint.x : ℝ) ≤ (xbQ cx : ℝ) := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]; push_cast; ring
    · have h' : (xbQ cx : ℝ) < (A.toPoint.x : ℝ) := by exact_mod_cast not_le.mp h
      rw [abs_of_neg (by linarith)]; push_cast; ring
  have habsDxQ_eq : (absDxQ : ℝ) = absDx_R A B := by
    unfold absDx_R; dsimp [absDxQ]
    split_ifs with h
    · have h' : (0 : ℝ) ≤ ((B.toPoint.x - A.toPoint.x : ℚ) : ℝ) := by exact_mod_cast h
      push_cast at h' ⊢; rw [abs_of_nonneg h']
    · have h' : ((B.toPoint.x - A.toPoint.x : ℚ) : ℝ) < 0 := by exact_mod_cast not_le.mp h
      push_cast at h' ⊢; rw [abs_of_neg h']
  have hF_eval (c' : Cell) :
      rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY c' =
        if remX64 c'.x ≥ absDx64 then (c', true) else (⟨c'.x + stepX, c'.y⟩, false) := by
    unfold rayMarchStepFloat; dsimp only []; rw [hx0, if_neg Bool.false_ne_true, hy0, if_pos rfl]
  have hI_eval (c' : Cell) :
      rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y) stepX stepY c' =
        if remXQ c'.x ≥ absDxQ then (c', true) else (⟨c'.x + stepX, c'.y⟩, false) := by
    unfold rayMarchStep; dsimp only []; rw [hx0, if_neg Bool.false_ne_true, hy0, if_pos rfl]
  by_cases hcondF : remX64 c.x ≥ absDx64
  · by_cases hcondI : remXQ c.x ≥ absDxQ
    · have hF_c : rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY c = (c, true) := by
        rw [hF_eval c, if_pos hcondF]
      have hI_c : rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y) stepX stepY c = (c, true) := by
        rw [hI_eval c, if_pos hcondI]
      exact ⟨Or.inl ⟨by rw [hF_c, hI_c], by rw [hF_c, hI_c]⟩,
             Or.inl ⟨by rw [hF_c, hI_c], by rw [hF_c, hI_c]⟩⟩
    · have hF_c : rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY c = (c, true) := by
        rw [hF_eval c, if_pos hcondF]
      have hI_c : rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y) stepX stepY c = (⟨c.x + stepX, c.y⟩, false) := by
        rw [hI_eval c, if_neg hcondI]
      have hF_le := toReal_ge_of_ge_binary64 (remX64 c.x) absDx64 hremX0_fin habsDx_fin hcondF
      have hI_next_ge : remXQ (c.x + stepX) ≥ absDxQ := by
        have hR : absDx_R A B ≤ remX_R A stepX (c.x + stepX) := by linarith
        rw [← habsDxQ_eq, ← hremXQ_eq (c.x + stepX)] at hR
        exact_mod_cast hR
      have hI_c1 : rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y) stepX stepY ⟨c.x + stepX, c.y⟩ = (⟨c.x + stepX, c.y⟩, true) := by
        rw [hI_eval ⟨c.x + stepX, c.y⟩, if_pos hI_next_ge]
      refine ⟨Or.inr (Or.inl (Or.inr (Or.inl (by rw [hF_c])))),
              Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (by rw [hI_c, hI_c1])))))⟩
  · by_cases hcondI : remXQ c.x ≥ absDxQ
    · have hF_c : rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY c = (⟨c.x + stepX, c.y⟩, false) := by
        rw [hF_eval c, if_neg hcondF]
      have hI_c : rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y) stepX stepY c = (c, true) := by
        rw [hI_eval c, if_pos hcondI]
      have hI_le_R : absDx_R A B ≤ remX_R A stepX c.x := by
        rw [← habsDxQ_eq, ← hremXQ_eq c.x]
        exact_mod_cast hcondI
      have hF_next_ge : remX64 (c.x + stepX) ≥ absDx64 := by
        apply ge_of_toReal_ge (remX64 (c.x + stepX)) absDx64 hremX1_fin habsDx_fin
        linarith
      have hF_c1 : rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY ⟨c.x + stepX, c.y⟩ = (⟨c.x + stepX, c.y⟩, true) := by
        rw [hF_eval ⟨c.x + stepX, c.y⟩, if_pos hF_next_ge]
      refine ⟨Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (by rw [hF_c, hF_c1]))))),
              Or.inr (Or.inl (Or.inr (Or.inl (by rw [hI_c]))))⟩
    · have hF_c : rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY c = (⟨c.x + stepX, c.y⟩, false) := by
        rw [hF_eval c, if_neg hcondF]
      have hI_c : rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y) stepX stepY c = (⟨c.x + stepX, c.y⟩, false) := by
        rw [hI_eval c, if_neg hcondI]
      exact ⟨Or.inl ⟨by rw [hF_c, hI_c], by rw [hF_c, hI_c]⟩,
             Or.inl ⟨by rw [hF_c, hI_c], by rw [hF_c, hI_c]⟩⟩

theorem rayMarchStep_preserves_cellInBox_and_dist_2d (A B : Point32) (stepX stepY : ℤ) (c : Cell)
    (hx0 : (stepX == 0) = false) (hy0 : (stepY == 0) = false)
    (hc : CellInBox A B stepX stepY c)
    (hne : (c == floorPoint B.toPoint) = false)
    (h_ndone : (rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y) stepX stepY c).2 = false) :
    let next := (rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y) stepX stepY c).1
    CellInBox A B stepX stepY next ∧
    ((floorPoint B.toPoint).x - next.x).natAbs + ((floorPoint B.toPoint).y - next.y).natAbs <
      ((floorPoint B.toPoint).x - c.x).natAbs + ((floorPoint B.toPoint).y - c.y).natAbs ∧
    (next = ⟨c.x + stepX, c.y + stepY⟩ →
      ((floorPoint B.toPoint).x - (c.x + stepX)).natAbs + ((floorPoint B.toPoint).y - (c.y + stepY)).natAbs + 2 ≤
        ((floorPoint B.toPoint).x - c.x).natAbs + ((floorPoint B.toPoint).y - c.y).natAbs) := by
  dsimp only []
  obtain ⟨h_box, h_lt⟩ := rayMarchStep_preserves_cellInBox_and_dist A B stepX stepY c hc hne h_ndone
  refine ⟨h_box, h_lt, ?_⟩
  intro hnext_d
  rcases hc with ⟨hcx_box, hcy_box⟩
  have hcx_nz : (stepX = 1 ∧ A.toPoint.x < B.toPoint.x ∧ (floorPoint A.toPoint).x ≤ c.x ∧ c.x ≤ (floorPoint B.toPoint).x) ∨
                (stepX = -1 ∧ B.toPoint.x < A.toPoint.x ∧ (floorPoint B.toPoint).x ≤ c.x ∧ c.x ≤ (floorPoint A.toPoint).x) := by
    rcases hcx_box with h1 | h2 | ⟨h3, _⟩
    · exact Or.inl h1
    · exact Or.inr h2
    · exfalso; rw [h3] at hx0; revert hx0; decide
  have hcy_nz : (stepY = 1 ∧ A.toPoint.y < B.toPoint.y ∧ (floorPoint A.toPoint).y ≤ c.y ∧ c.y ≤ (floorPoint B.toPoint).y) ∨
                (stepY = -1 ∧ B.toPoint.y < A.toPoint.y ∧ (floorPoint B.toPoint).y ≤ c.y ∧ c.y ≤ (floorPoint A.toPoint).y) := by
    rcases hcy_box with h1 | h2 | ⟨h3, _⟩
    · exact Or.inl h1
    · exact Or.inr h2
    · exfalso; rw [h3] at hy0; revert hy0; decide
  have h_ideal := (rayMarchStep_real_bounds A B stepX stepY c hx0 hy0).2 h_ndone
  have hlt_x := (h_ideal.2.2.2 hnext_d).2.1
  have hlt_y := (h_ideal.2.2.2 hnext_d).2.2
  have hcx_ne := cx_ne_endCell_of_crossX_lt_limitCross A B stepX c hcx_nz hlt_x
  have hcy_ne := cy_ne_endCell_of_crossY_lt_limitCross A B stepY c hcy_nz hlt_y
  rcases hcx_nz with ⟨hsx, _, _, _⟩ | ⟨hsx, _, _, _⟩ <;>
  rcases hcy_nz with ⟨hsy, _, _, _⟩ | ⟨hsy, _, _, _⟩ <;> omega

theorem rayMarchFloat_near_rayMarch_of_ext
    (fuel : ℕ) (start : Point32) (ptEnd : Point)
    (dx dy : Binary32) (dxQ dyQ : ℚ) (stepX stepY : ℤ) (endCell current : Cell)
    (P : Cell → Prop) (hP : P current)
    (hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1) (hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1)
    (h_fuel : (endCell.x - current.x).natAbs + (endCell.y - current.y).natAbs + 2 ≤ fuel)
    (h_dist_I : ∀ c, P c →
      (c == endCell) = false → (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).2 = false →
      P (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 ∧
      (endCell.x - (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1.x).natAbs +
      (endCell.y - (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1.y).natAbs <
      (endCell.x - c.x).natAbs + (endCell.y - c.y).natAbs)
    (h_cases : ∀ c, P c →
      RayMarchCasesFloatExt start ptEnd dx dy dxQ dyQ stepX stepY endCell c) :
    ∀ c1 ∈ rayMarchFloat fuel start dx dy stepX stepY endCell current [],
      ∃ c2 ∈ dedupCells ([current, endCell] ++
        rayMarch fuel start.toPoint ptEnd dxQ dyQ stepX stepY endCell current []),
        chebyshevDistance c1 c2 ≤ 1 := by
  induction fuel using Nat.strong_induction_on generalizing current with
  | h fuel ih =>
    intro c1 hc1
    cases fuel with
    | zero => omega
    | succ fuel =>
      cases fuel with
      | zero => omega
      | succ fuel =>
        rcases h_cases current hP with h_agree | h_term1 | h_term2 | h_dia | h_diasymm
        · have h_not_end : (current == endCell) = false := by
            cases h : (current == endCell)
            · rfl
            · rw [rayMarchFloat_succ] at hc1; dsimp only [] at hc1; rw [h] at hc1; cases hc1
          have hdF : (rayMarchStepFloat start dx dy stepX stepY current).2 = false := by
            cases h : (rayMarchStepFloat start dx dy stepX stepY current).2
            · rfl
            · rw [rayMarchFloat_succ] at hc1; dsimp only [] at hc1; rw [h_not_end, h] at hc1; cases hc1
          have hdI : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY current).2 = false := by
            rw [← h_agree.2]; exact hdF
          obtain ⟨hP_next, h_step_d⟩ := h_dist_I current hP h_not_end hdI
          rw [← h_agree.1] at hP_next h_step_d
          have h_rec := ih (fuel + 1) (by omega) (rayMarchStepFloat start dx dy stepX stepY current).1
            hP_next (by omega)
          have h_rec' : ∀ c1 ∈ rayMarchFloat (fuel + 1) start dx dy stepX stepY endCell
              (rayMarchStepFloat start dx dy stepX stepY current).1 [],
            ∃ c2 ∈ dedupCells ([(rayMarchStepFloat start dx dy stepX stepY current).1, endCell] ++
              rayMarch (fuel + 1) start.toPoint ptEnd dxQ dyQ stepX stepY endCell
                (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY current).1 []),
              chebyshevDistance c1 c2 ≤ 1 := by
            intro c1' hc1'
            rcases h_rec c1' hc1' with ⟨c2, hc2, hd2⟩
            refine ⟨c2, ?_, hd2⟩
            rw [← h_agree.1]
            exact hc2
          exact rayMarchFloat_step_agree_near_rayMarch_endpoints (fuel + 1) start ptEnd dx dy dxQ dyQ stepX stepY
            endCell current hX hY h_agree.1 h_agree.2 h_rec' c1 hc1
        · exact rayMarchFloat_terminal_near_rayMarch_endpoints (fuel + 2) start ptEnd dx dy dxQ dyQ stepX stepY
            endCell current h_term1 c1 hc1
        · exact rayMarchFloat_two_step_terminal_near_rayMarch_endpoints_ext (fuel + 2) start ptEnd dx dy dxQ dyQ stepX stepY
            endCell current hX hY h_term2 c1 hc1
        · rcases h_dia with ⟨hne, hndF1, hstF1, hneF1, hndF2, hstF2, hndI1, hstI1, hneI1, hndI2, hstI2⟩
          obtain ⟨hP1, hd1⟩ := h_dist_I current hP hne hndI1
          rw [hstI1] at hP1 hd1
          obtain ⟨hP2, hd2⟩ := h_dist_I ⟨current.x, current.y + stepY⟩ hP1 hneI1 hndI2
          rw [hstI2] at hP2 hd2
          have h_rec := ih fuel (by omega) ⟨current.x + stepX, current.y + stepY⟩ hP2 (by omega)
          exact rayMarchFloat_diamond_near_rayMarch_endpoints fuel start ptEnd dx dy dxQ dyQ stepX stepY
            endCell current hX hY hne hndF1 hstF1 hneF1 hndF2 hstF2 hndI1 hstI1 hneI1 hndI2 hstI2 h_rec c1 hc1
        · rcases h_diasymm with ⟨hne, hndF1, hstF1, hneF1, hndF2, hstF2, hndI1, hstI1, hneI1, hndI2, hstI2⟩
          obtain ⟨hP1, hd1⟩ := h_dist_I current hP hne hndI1
          rw [hstI1] at hP1 hd1
          obtain ⟨hP2, hd2⟩ := h_dist_I ⟨current.x + stepX, current.y⟩ hP1 hneI1 hndI2
          rw [hstI2] at hP2 hd2
          have h_rec := ih fuel (by omega) ⟨current.x + stepX, current.y + stepY⟩ hP2 (by omega)
          exact rayMarchFloat_diamond_symm_near_rayMarch_endpoints fuel start ptEnd dx dy dxQ dyQ stepX stepY
            endCell current hX hY hne hndF1 hstF1 hneF1 hndF2 hstF2 hndI1 hstI1 hneI1 hndI2 hstI2 h_rec c1 hc1

theorem rayMarch_near_rayMarchFloat_of_ext
    (fuel : ℕ) (start : Point32) (ptEnd : Point)
    (dx dy : Binary32) (dxQ dyQ : ℚ) (stepX stepY : ℤ) (endCell current : Cell)
    (P : Cell → Prop) (hP : P current)
    (hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1) (hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1)
    (h_fuel : (endCell.x - current.x).natAbs + (endCell.y - current.y).natAbs + 2 ≤ fuel)
    (h_dist_I : ∀ c, P c →
      (c == endCell) = false → (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).2 = false →
      P (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 ∧
      (endCell.x - (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1.x).natAbs +
      (endCell.y - (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1.y).natAbs <
      (endCell.x - c.x).natAbs + (endCell.y - c.y).natAbs)
    (h_cases : ∀ c, P c →
      RayMarchCasesIdealExt start ptEnd dx dy dxQ dyQ stepX stepY endCell c) :
    ∀ c2 ∈ rayMarch fuel start.toPoint ptEnd dxQ dyQ stepX stepY endCell current [],
      ∃ c1 ∈ dedupCells ([current, endCell] ++
        rayMarchFloat fuel start dx dy stepX stepY endCell current []),
        chebyshevDistance c1 c2 ≤ 1 := by
  induction fuel using Nat.strong_induction_on generalizing current with
  | h fuel ih =>
    intro c2 hc2
    cases fuel with
    | zero => omega
    | succ fuel =>
      cases fuel with
      | zero => omega
      | succ fuel =>
        rcases h_cases current hP with h_agree | h_term1 | h_term2 | h_dia | h_diasymm
        · have h_not_end : (current == endCell) = false := by
            cases h : (current == endCell)
            · rfl
            · rw [rayMarch_succ] at hc2; dsimp only [] at hc2; rw [h] at hc2; cases hc2
          have hdI : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY current).2 = false := by
            cases h : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY current).2
            · rfl
            · rw [rayMarch_succ] at hc2; dsimp only [] at hc2; rw [h_not_end, h] at hc2; cases hc2
          obtain ⟨hP_next, h_step_d⟩ := h_dist_I current hP h_not_end hdI
          have h_rec := ih (fuel + 1) (by omega) (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY current).1
            hP_next (by omega)
          have h_rec' : ∀ c2 ∈ rayMarch (fuel + 1) start.toPoint ptEnd dxQ dyQ stepX stepY endCell
              (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY current).1 [],
            ∃ c1 ∈ dedupCells ([(rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY current).1, endCell] ++
              rayMarchFloat (fuel + 1) start dx dy stepX stepY endCell
                (rayMarchStepFloat start dx dy stepX stepY current).1 []),
              chebyshevDistance c1 c2 ≤ 1 := by
            intro c2' hc2'
            rcases h_rec c2' hc2' with ⟨c1, hc1, hd1⟩
            refine ⟨c1, ?_, hd1⟩
            rw [h_agree.1]
            exact hc1
          exact rayMarch_step_agree_near_rayMarchFloat_endpoints (fuel + 1) start ptEnd dx dy dxQ dyQ stepX stepY
            endCell current hX hY h_agree.1 h_agree.2 h_rec' c2 hc2
        · exact rayMarch_terminal_near_rayMarchFloat_endpoints (fuel + 2) start ptEnd dx dy dxQ dyQ stepX stepY
            endCell current h_term1 c2 hc2
        · exact rayMarch_two_step_terminal_near_rayMarchFloat_endpoints_ext (fuel + 2) start ptEnd dx dy dxQ dyQ stepX stepY
            endCell current hX hY h_term2 c2 hc2
        · rcases h_dia with ⟨hne, hndF1, hstF1, hneF1, hndF2, hstF2, hndI1, hstI1, hneI1, hndI2, hstI2⟩
          obtain ⟨hP1, hd1⟩ := h_dist_I current hP hne hndI1
          rw [hstI1] at hP1 hd1
          obtain ⟨hP2, hd2⟩ := h_dist_I ⟨current.x, current.y + stepY⟩ hP1 hneI1 hndI2
          rw [hstI2] at hP2 hd2
          have h_rec := ih fuel (by omega) ⟨current.x + stepX, current.y + stepY⟩ hP2 (by omega)
          exact rayMarch_diamond_near_rayMarchFloat_endpoints fuel start ptEnd dx dy dxQ dyQ stepX stepY
            endCell current hX hY hne hndF1 hstF1 hneF1 hndF2 hstF2 hndI1 hstI1 hneI1 hndI2 hstI2 h_rec c2 hc2
        · rcases h_diasymm with ⟨hne, hndF1, hstF1, hneF1, hndF2, hstF2, hndI1, hstI1, hneI1, hndI2, hstI2⟩
          obtain ⟨hP1, hd1⟩ := h_dist_I current hP hne hndI1
          rw [hstI1] at hP1 hd1
          obtain ⟨hP2, hd2⟩ := h_dist_I ⟨current.x + stepX, current.y⟩ hP1 hneI1 hndI2
          rw [hstI2] at hP2 hd2
          have h_rec := ih fuel (by omega) ⟨current.x + stepX, current.y + stepY⟩ hP2 (by omega)
          exact rayMarch_diamond_symm_near_rayMarchFloat_endpoints fuel start ptEnd dx dy dxQ dyQ stepX stepY
            endCell current hX hY hne hndF1 hstF1 hneF1 hndF2 hstF2 hndI1 hstI1 hneI1 hndI2 hstI2 h_rec c2 hc2

theorem cellIntersectionsSegmentFloat_hausdorff_bound_axis_aligned
    (A B : Point32)
    (h_finiteA : A.isFinite) (h_finiteB : B.isFinite)
    (h_bound : inCoordBounds mainCoordBound A.toPoint B.toPoint)
    (h_stepX : (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0) =
      (if B.toPoint.x - A.toPoint.x > 0 then 1 else if B.toPoint.x - A.toPoint.x < 0 then -1 else 0))
    (h_stepY : (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0) =
      (if B.toPoint.y - A.toPoint.y > 0 then 1 else if B.toPoint.y - A.toPoint.y < 0 then -1 else 0))
    (h_axis : ((if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else (0 : ℤ)) == 0) = true ∨
              ((if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else (0 : ℤ)) == 0) = true) :
    cellHausdorffDistanceLe
      (cellIntersectionsSegmentFloat A B)
      (cellIntersectionsSegment A.toPoint B.toPoint) 1 := by
  by_cases h_same : floorPoint32 A = floorPoint32 B
  · exact cellIntersectionsSegmentFloat_hausdorff_bound_same_cell A B h_finiteA h_finiteB h_same
  · have h_floorA := floorPoint32_eq_floorPoint A h_finiteA
    have h_floorB := floorPoint32_eq_floorPoint B h_finiteB
    have h_same_ideal : floorPoint A.toPoint ≠ floorPoint B.toPoint := by
      rw [← h_floorA, ← h_floorB]; exact h_same
    have h_same_bool : (floorPoint32 A == floorPoint32 B) = false := by
      cases h : (floorPoint32 A == floorPoint32 B)
      · rfl
      · exfalso; apply h_same; rw [eq_of_beq h]
    have h_same_ideal_bool : (floorPoint A.toPoint == floorPoint B.toPoint) = false := by
      cases h : (floorPoint A.toPoint == floorPoint B.toPoint)
      · rfl
      · exfalso; apply h_same_ideal; rw [eq_of_beq h]
    unfold cellIntersectionsSegmentFloat cellIntersectionsSegment
    dsimp only []
    rw [h_same_bool, h_same_ideal_bool]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [h_floorA, h_floorB]
    set stepX : ℤ := if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0
    set stepY : ℤ := if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0
    have hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1 := by dsimp [stepX]; split_ifs <;> simp
    have hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1 := by dsimp [stepY]; split_ifs <;> simp
    have h_cases_both : ∀ c, CellInBox A B stepX stepY c →
        RayMarchCasesFloatExt A B.toPoint (B.x - A.x) (B.y - A.y)
          (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y)
          stepX stepY (floorPoint B.toPoint) c ∧
        RayMarchCasesIdealExt A B.toPoint (B.x - A.x) (B.y - A.y)
          (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y)
          stepX stepY (floorPoint B.toPoint) c := by
      intro c hc
      by_cases hx0 : (stepX == 0) = true
      · exact rayMarch_axis_aligned_stepX_zero A B stepX stepY c h_finiteA h_finiteB h_bound hc hx0
      · rw [Bool.not_eq_true] at hx0
        have hy0 : (stepY == 0) = true := by
          rcases h_axis with h1 | h2
          · exfalso; rw [h1] at hx0; contradiction
          · exact h2
        exact rayMarch_axis_aligned_stepY_zero A B stepX stepY c h_finiteA h_finiteB h_bound hc hx0 hy0
    have h1 := rayMarchFloat_near_rayMarch_of_ext
      (((floorPoint B.toPoint).x - (floorPoint A.toPoint).x).natAbs +
       ((floorPoint B.toPoint).y - (floorPoint A.toPoint).y).natAbs + 2)
      A B.toPoint (B.x - A.x) (B.y - A.y)
      (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y)
      stepX stepY
      (floorPoint B.toPoint) (floorPoint A.toPoint)
      (CellInBox A B stepX stepY)
      (cellInBox_start A B h_stepX h_stepY)
      hX hY (le_refl _)
      (fun c hc hne hnd => rayMarchStep_preserves_cellInBox_and_dist A B stepX stepY c hc hne hnd)
      (fun c hc => (h_cases_both c hc).1)
    have h2 := rayMarch_near_rayMarchFloat_of_ext
      (((floorPoint B.toPoint).x - (floorPoint A.toPoint).x).natAbs +
       ((floorPoint B.toPoint).y - (floorPoint A.toPoint).y).natAbs + 2)
      A B.toPoint (B.x - A.x) (B.y - A.y)
      (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y)
      stepX stepY
      (floorPoint B.toPoint) (floorPoint A.toPoint)
      (CellInBox A B stepX stepY)
      (cellInBox_start A B h_stepX h_stepY)
      hX hY (le_refl _)
      (fun c hc hne hnd => rayMarchStep_preserves_cellInBox_and_dist A B stepX stepY c hc hne hnd)
      (fun c hc => (h_cases_both c hc).2)
    rw [← h_stepX, ← h_stepY]
    exact cellHausdorffDistanceLe_dedup_endpoints _ _ _ _ h1 h2

end Geometry





