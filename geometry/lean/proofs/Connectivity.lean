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
import proofs.FloatAnalysis
import proofs.FloatBounds
import proofs.RayMarchLimits
import proofs.MiniSegment
import proofs.Hausdorff
import proofs.NativeFloat
import Mathlib.Tactic

/-!
# The float ray march leaves no gaps

The Hausdorff bound alone allows the float output to skip a cell. This file proves the stronger,
visible property: the cells of `cellIntersectionsSegmentFloat` can be listed as a path of neighboring
cells from the start cell to the end cell.

Each float step moves at most one cell per axis toward the end. The error analysis of
`rayMarchStepFloat_real_bounds` shows that the march never moves more than one cell past the end
cell along an axis, and that it only stops within one cell of the end cell. Since every step uses up
at least one of the at most `|Δx| + |Δy| + 2` steps the box allows, the step budget never runs out
before that.
-/

namespace Geometry

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange

/-- The relative error budget used to bound one float march decision. -/
noncomputable def etaMarch : ℝ := 4 * (epsRayMarch : ℝ)

theorem etaMarch_small : etaMarch * ((maxCoordDelta : ℝ) + 2) < 1 := by
  unfold etaMarch
  rw [epsRayMarch_toReal_eval]
  unfold maxCoordDelta maxCoordDeltaNat mainCoordBoundNat
  norm_num

theorem etaMarch_nonneg : 0 ≤ etaMarch := by
  unfold etaMarch
  have := epsRayMarch_pos
  have : (0 : ℝ) < (epsRayMarch : ℝ) := by exact_mod_cast this
  linarith

/--
Real-valued consequences of one float march step along an active x axis: stopping means the next
x boundary is (nearly) past `B`, and moving in x means it is (nearly) not.
-/
theorem x_step_bounds (A B : Point32) (h_finA : A.isFinite) (h_finB : B.isFinite)
    (h_bound : inCoordBounds mainCoordBound A.toPoint B.toPoint) (stepX stepY : ℤ)
    (hx0 : stepX ≠ 0) (hy : stepY = 0 ∨ 0 < absDy_R A B)
    (c : Cell) (hcx : |c.x| ≤ mainCoordBound.floor + 1) (hcy : |c.y| ≤ mainCoordBound.floor + 1) :
    let s := rayMarchStepFloat A (deltaX A B) (deltaY A B) stepX stepY c
    (s.2 = true → absDx_R A B * (1 - etaMarch) ≤ remX_R A stepX c.x) ∧
    (s.2 = false → s.1.x = c.x + stepX → remX_R A stepX c.x < absDx_R A B * (1 + etaMarch)) := by
  intro s
  have heps : (0 : ℝ) < (epsRayMarch : ℝ) := by exact_mod_cast epsRayMarch_pos
  have heps1 : (epsRayMarch : ℝ) < 1 / 100 := by rw [epsRayMarch_toReal_eval]; norm_num
  have hdx0 : 0 ≤ absDx_R A B := abs_nonneg _
  have hrx0 : 0 ≤ remX_R A stepX c.x := abs_nonneg _
  have hx0b : (stepX == 0) = false := by simpa using hx0
  by_cases hy0 : stepY = 0
  · -- axis-aligned march along x
    subst hy0
    obtain ⟨hAx, hAy, hBx, hBy⟩ := h_bound
    have hk : |(if stepX > 0 then c.x + 1 else c.x)| ≤ mainCoordBound.floor + 2 := by
      split <;> rw [abs_le] at hcx ⊢ <;> constructor <;> omega
    obtain ⟨hremF, -, hremE, -⟩ := abs_toReal_rem_binary64_rel A.x _ h_finA.1 hAx hk
    obtain ⟨hdF, -, hdE, -⟩ := abs_toReal_absD_binary64_rel A.x B.x h_finA.1 h_finB.1 hAx hBx
    have hremR : |((if stepX > 0 then c.x + 1 else c.x : ℤ) : ℝ) - ((binary32ToRat A.x : ℚ) : ℝ)| =
        remX_R A stepX c.x := rfl
    have hdR : |((binary32ToRat B.x - binary32ToRat A.x : ℚ) : ℝ)| = absDx_R A B := by
      unfold absDx_R Point32.toPoint; push_cast; rfl
    rw [hremR] at hremE
    rw [hdR] at hdE
    obtain ⟨hr1, hr2⟩ := abs_le.mp hremE
    obtain ⟨hd1, hd2⟩ := abs_le.mp hdE
    have hcmp := binary_le_iff_real
      (ExecFloat.Binary.abs (deltaX A B))
      (ExecFloat.Binary.abs (intToBinary64 (if stepX > 0 then c.x + 1 else c.x) - widen32To64 A.x))
      hdF hremF
    unfold breal at hcmp
    have hs : s = (if ExecFloat.Binary.abs (intToBinary64 (if stepX > 0 then c.x + 1 else c.x) -
          widen32To64 A.x) ≥ ExecFloat.Binary.abs (deltaX A B) then (c, true)
        else (⟨c.x + stepX, c.y⟩, false)) := by
      simp only [s, rayMarchStepFloat, hx0b, Bool.false_eq_true, ↓reduceIte]
      rfl
    have hδ : (1 / 9007199254740992 : ℝ) ≤ (epsRayMarch : ℝ) := by
      rw [epsRayMarch_toReal_eval]; norm_num
    set rf := (ExecFloat.Binary.abs (intToBinary64 (if stepX > 0 then c.x + 1 else c.x) -
      widen32To64 A.x)).toModel.toReal
    set df := (ExecFloat.Binary.abs (widen32To64 B.x - widen32To64 A.x)).toModel.toReal
    set e := (epsRayMarch : ℝ)
    by_cases hge : ExecFloat.Binary.abs (intToBinary64 (if stepX > 0 then c.x + 1 else c.x) -
        widen32To64 A.x) ≥ ExecFloat.Binary.abs (deltaX A B)
    · have hsd : s = (c, true) := by rw [hs]; simp only [hge, ↓reduceIte]
      have hge' : df ≤ rf := hcmp.mp hge
      refine ⟨fun _ => ?_, fun hd => ?_⟩
      swap
      · rw [hsd] at hd; simp at hd
      have h1 : (1 - 1 / 9007199254740992) * absDx_R A B ≤
          (1 + 1 / 9007199254740992) * remX_R A stepX c.x := by linarith
      unfold etaMarch
      nlinarith [mul_nonneg hdx0 heps.le, mul_nonneg hrx0 heps.le]
    · have hsd : s = (⟨c.x + stepX, c.y⟩, false) := by rw [hs]; simp only [hge, ↓reduceIte]
      have hlt' : rf < df := by
        rw [← not_le]; exact fun h => hge (hcmp.mpr h)
      refine ⟨fun hd => ?_, fun _ _ => ?_⟩
      · rw [hsd] at hd; simp at hd
      have h1 : (1 - 1 / 9007199254740992) * remX_R A stepX c.x <
          (1 + 1 / 9007199254740992) * absDx_R A B := by linarith
      unfold etaMarch
      nlinarith [mul_nonneg hdx0 heps.le, mul_nonneg hrx0 heps.le]
  · -- diagonal march
    have hdy : 0 < absDy_R A B := hy.resolve_left hy0
    have hy0b : (stepY == 0) = false := by simpa using hy0
    obtain ⟨hdoneB, hmoveB⟩ :=
      rayMarchStepFloat_real_bounds A B stepX stepY c h_finA h_finB h_bound hx0b hy0b hcx hcy
    set e := (epsRayMarch : ℝ)
    constructor
    · intro hd
      obtain ⟨h1, -⟩ := hdoneB hd
      unfold limitCross_R crossX_R at h1
      have h2 : (1 - e) * absDx_R A B ≤ (1 + e) * remX_R A stepX c.x := by
        by_contra hcon
        rw [not_le] at hcon
        have := mul_lt_mul_of_pos_right hcon hdy
        nlinarith
      unfold etaMarch
      nlinarith [mul_nonneg hdx0 heps.le, mul_nonneg hrx0 heps.le]
    · intro hnd hmx
      have hcross : (1 - e) * crossX_R A B stepX c.x < (1 + e) * limitCross_R A B := by
        obtain ⟨-, hX, -, hD⟩ := hmoveB hnd
        rcases rayMarchStepFloat_done_or_cases A (deltaX A B) (deltaY A B) stepX stepY c with
          ⟨hd', -⟩ | ⟨-, h1 | h1 | h1⟩
        · exact absurd hd' (by rw [hnd]; simp)
        · exact (hX h1).2
        · exfalso
          have : s.1.x = c.x := by simp only [s, h1]
          omega
        · exact (hD h1).2.2.1
      unfold limitCross_R crossX_R at hcross
      have h2 : (1 - e) * remX_R A stepX c.x < (1 + e) * absDx_R A B := by
        by_contra hcon
        rw [not_lt] at hcon
        have := mul_le_mul_of_nonneg_right hcon hdy.le
        nlinarith
      unfold etaMarch
      nlinarith [mul_nonneg hdx0 heps.le, mul_nonneg hrx0 heps.le]
/--
Real-valued consequences of one float march step along an active y axis: stopping means the next
y boundary is (nearly) past `B`, and moving in y means it is (nearly) not.
-/
theorem y_step_bounds (A B : Point32) (h_finA : A.isFinite) (h_finB : B.isFinite)
    (h_bound : inCoordBounds mainCoordBound A.toPoint B.toPoint) (stepX stepY : ℤ)
    (hy0 : stepY ≠ 0) (hx : stepX = 0 ∨ 0 < absDx_R A B)
    (c : Cell) (hcx : |c.x| ≤ mainCoordBound.floor + 1) (hcy : |c.y| ≤ mainCoordBound.floor + 1) :
    let s := rayMarchStepFloat A (deltaX A B) (deltaY A B) stepX stepY c
    (s.2 = true → absDy_R A B * (1 - etaMarch) ≤ remY_R A stepY c.y) ∧
    (s.2 = false → s.1.y = c.y + stepY → remY_R A stepY c.y < absDy_R A B * (1 + etaMarch)) := by
  intro s
  have heps : (0 : ℝ) < (epsRayMarch : ℝ) := by exact_mod_cast epsRayMarch_pos
  have heps1 : (epsRayMarch : ℝ) < 1 / 100 := by rw [epsRayMarch_toReal_eval]; norm_num
  have hdy0 : 0 ≤ absDy_R A B := abs_nonneg _
  have hry0 : 0 ≤ remY_R A stepY c.y := abs_nonneg _
  have hy0b : (stepY == 0) = false := by simpa using hy0
  by_cases hx0 : stepX = 0
  · -- axis-aligned march along y
    subst hx0
    obtain ⟨hAx, hAy, hBx, hBy⟩ := h_bound
    have hk : |(if stepY > 0 then c.y + 1 else c.y)| ≤ mainCoordBound.floor + 2 := by
      split <;> rw [abs_le] at hcy ⊢ <;> constructor <;> omega
    obtain ⟨hremF, -, hremE, -⟩ := abs_toReal_rem_binary64_rel A.y _ h_finA.2 hAy hk
    obtain ⟨hdF, -, hdE, -⟩ := abs_toReal_absD_binary64_rel A.y B.y h_finA.2 h_finB.2 hAy hBy
    have hremR : |((if stepY > 0 then c.y + 1 else c.y : ℤ) : ℝ) - ((binary32ToRat A.y : ℚ) : ℝ)| =
        remY_R A stepY c.y := rfl
    have hdR : |((binary32ToRat B.y - binary32ToRat A.y : ℚ) : ℝ)| = absDy_R A B := by
      unfold absDy_R Point32.toPoint; push_cast; rfl
    rw [hremR] at hremE
    rw [hdR] at hdE
    obtain ⟨hr1, hr2⟩ := abs_le.mp hremE
    obtain ⟨hd1, hd2⟩ := abs_le.mp hdE
    have hcmp := binary_le_iff_real
      (ExecFloat.Binary.abs (deltaY A B))
      (ExecFloat.Binary.abs (intToBinary64 (if stepY > 0 then c.y + 1 else c.y) - widen32To64 A.y))
      hdF hremF
    unfold breal at hcmp
    have hs : s = (if ExecFloat.Binary.abs (intToBinary64 (if stepY > 0 then c.y + 1 else c.y) -
          widen32To64 A.y) ≥ ExecFloat.Binary.abs (deltaY A B) then (c, true)
        else (⟨c.x, c.y + stepY⟩, false)) := by
      simp only [s, rayMarchStepFloat]
      rfl
    set rf := (ExecFloat.Binary.abs (intToBinary64 (if stepY > 0 then c.y + 1 else c.y) -
      widen32To64 A.y)).toModel.toReal
    set df := (ExecFloat.Binary.abs (widen32To64 B.y - widen32To64 A.y)).toModel.toReal
    have hδ : (1 / 9007199254740992 : ℝ) ≤ (epsRayMarch : ℝ) := by
      rw [epsRayMarch_toReal_eval]; norm_num
    by_cases hge : ExecFloat.Binary.abs (intToBinary64 (if stepY > 0 then c.y + 1 else c.y) -
        widen32To64 A.y) ≥ ExecFloat.Binary.abs (deltaY A B)
    · have hsd : s = (c, true) := by rw [hs]; simp only [hge, ↓reduceIte]
      have hge' : df ≤ rf := hcmp.mp hge
      refine ⟨fun _ => ?_, fun hd => ?_⟩
      swap
      · rw [hsd] at hd; simp at hd
      have h1 : (1 - 1 / 9007199254740992) * absDy_R A B ≤
          (1 + 1 / 9007199254740992) * remY_R A stepY c.y := by linarith
      unfold etaMarch
      nlinarith [mul_nonneg hdy0 heps.le, mul_nonneg hry0 heps.le]
    · have hsd : s = (⟨c.x, c.y + stepY⟩, false) := by rw [hs]; simp only [hge, ↓reduceIte]
      have hlt' : rf < df := by
        rw [← not_le]; exact fun h => hge (hcmp.mpr h)
      refine ⟨fun hd => ?_, fun _ _ => ?_⟩
      · rw [hsd] at hd; simp at hd
      have h1 : (1 - 1 / 9007199254740992) * remY_R A stepY c.y <
          (1 + 1 / 9007199254740992) * absDy_R A B := by linarith
      unfold etaMarch
      nlinarith [mul_nonneg hdy0 heps.le, mul_nonneg hry0 heps.le]
  · -- diagonal march
    have hdx : 0 < absDx_R A B := hx.resolve_left hx0
    have hx0b : (stepX == 0) = false := by simpa using hx0
    obtain ⟨hdoneB, hmoveB⟩ :=
      rayMarchStepFloat_real_bounds A B stepX stepY c h_finA h_finB h_bound hx0b hy0b hcx hcy
    set e := (epsRayMarch : ℝ)
    constructor
    · intro hd
      obtain ⟨-, h1⟩ := hdoneB hd
      unfold limitCross_R crossY_R at h1
      have h2 : (1 - e) * absDy_R A B ≤ (1 + e) * remY_R A stepY c.y := by
        by_contra hcon
        rw [not_le] at hcon
        have := mul_lt_mul_of_pos_right hcon hdx
        nlinarith
      unfold etaMarch
      nlinarith [mul_nonneg hdy0 heps.le, mul_nonneg hry0 heps.le]
    · intro hnd hmy
      have hcross : (1 - e) * crossY_R A B stepY c.y < (1 + e) * limitCross_R A B := by
        obtain ⟨-, -, hY, hD⟩ := hmoveB hnd
        rcases rayMarchStepFloat_done_or_cases A (deltaX A B) (deltaY A B) stepX stepY c with
          ⟨hd', -⟩ | ⟨-, h1 | h1 | h1⟩
        · exact absurd hd' (by rw [hnd]; simp)
        · exfalso
          have : s.1.y = c.y := by simp only [s, h1]
          omega
        · exact (hY h1).2
        · exact (hD h1).2.2.2
      unfold limitCross_R crossY_R at hcross
      have h2 : (1 - e) * remY_R A stepY c.y < (1 + e) * absDy_R A B := by
        by_contra hcon
        rw [not_lt] at hcon
        have := mul_le_mul_of_nonneg_right hcon hdx.le
        nlinarith
      unfold etaMarch
      nlinarith [mul_nonneg hdy0 heps.le, mul_nonneg hry0 heps.le]

/-! ## One axis of the march -/

/-- Along one axis, a march cell lies between the start cell and one cell past the end cell. -/
def AxisBox (a b : ℚ) (cx : ℤ) : Prop :=
  (a < b ∧ a.floor ≤ cx ∧ cx ≤ b.floor + 1) ∨
  (b < a ∧ b.floor - 1 ≤ cx ∧ cx ≤ a.floor) ∨
  (a = b ∧ cx = a.floor)

/-- Along one axis, the number of steps left before the march is one cell past the end cell. -/
def axisPot (a b : ℚ) (cx : ℤ) : ℕ :=
  if a < b then (b.floor + 1 - cx).toNat else if b < a then (cx - (b.floor - 1)).toNat else 0

/-- The real direction of one axis. -/
def axisStep (a b : ℚ) : ℤ :=
  if b - a > 0 then 1 else if b - a < 0 then -1 else 0

theorem floor_cast_le (q : ℚ) : ((q.floor : ℤ) : ℝ) ≤ (q : ℝ) := by
  have := Rat.floor_le q
  exact_mod_cast this

theorem lt_floor_cast_add_one (q : ℚ) : (q : ℝ) < ((q.floor : ℤ) : ℝ) + 1 := by
  have := Rat.lt_floor_add_one q
  exact_mod_cast this

/-- Moving along an axis stays in the box and uses up one step of that axis. -/
theorem axis_move (a b : ℚ) (cx : ℤ) (hbox : AxisBox a b cx) (hs : axisStep a b ≠ 0)
    (η : ℝ) (hsmall : η * |(b : ℝ) - (a : ℝ)| < 1)
    (hM : |((if axisStep a b > 0 then cx + 1 else cx : ℤ) : ℝ) - (a : ℝ)| <
      |(b : ℝ) - (a : ℝ)| * (1 + η)) :
    AxisBox a b (cx + axisStep a b) ∧ axisPot a b (cx + axisStep a b) + 1 = axisPot a b cx := by
  have fa := floor_cast_le a
  have fa' := lt_floor_cast_add_one a
  have fb := floor_cast_le b
  have fb' := lt_floor_cast_add_one b
  rcases hbox with ⟨hab, h1, h2⟩ | ⟨hba, h1, h2⟩ | ⟨heq, -⟩
  · have hst : axisStep a b = 1 := by unfold axisStep; simp [sub_pos.mpr hab]
    have hab' : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
    rw [hst] at hM ⊢
    simp only [gt_iff_lt, zero_lt_one, ↓reduceIte] at hM
    have hle : cx ≤ b.floor := by
      by_contra hc
      have hcx : cx = b.floor + 1 := by omega
      subst hcx
      push_cast at hM
      rw [abs_of_pos (by linarith), abs_of_pos (by linarith)] at hM
      nlinarith [abs_of_pos (sub_pos.mpr hab'), abs_nonneg ((b : ℝ) - (a : ℝ))]
    refine ⟨Or.inl ⟨hab, by omega, by omega⟩, ?_⟩
    unfold axisPot
    simp only [hab, ↓reduceIte]
    omega
  · have hst : axisStep a b = -1 := by
      unfold axisStep; simp [not_lt.mpr (sub_nonpos.mpr hba.le), sub_neg.mpr hba]
    have hba' : (b : ℝ) < (a : ℝ) := by exact_mod_cast hba
    rw [hst] at hM ⊢
    simp only [gt_iff_lt, Left.neg_pos_iff, Int.reduceLT, ↓reduceIte] at hM
    have hge : b.floor ≤ cx := by
      by_contra hc
      have hcx : cx = b.floor - 1 := by omega
      subst hcx
      push_cast at hM
      rw [abs_of_neg (by linarith), abs_of_neg (by linarith)] at hM
      rw [abs_of_neg (sub_neg.mpr hba')] at hsmall
      nlinarith
    refine ⟨Or.inr (Or.inl ⟨hba, by omega, by omega⟩), ?_⟩
    unfold axisPot
    simp only [not_lt.mpr hba.le, hba, ↓reduceIte]
    omega
  · exfalso
    apply hs
    unfold axisStep
    simp [heq]

/-- When the march stops, each axis is within one cell of the end cell. -/
theorem axis_done (a b : ℚ) (cx : ℤ) (hbox : AxisBox a b cx)
    (η : ℝ) (hsmall : η * |(b : ℝ) - (a : ℝ)| < 1)
    (hD : axisStep a b ≠ 0 → |(b : ℝ) - (a : ℝ)| * (1 - η) ≤
      |((if axisStep a b > 0 then cx + 1 else cx : ℤ) : ℝ) - (a : ℝ)|) :
    (cx - b.floor).natAbs ≤ 1 := by
  have fa := floor_cast_le a
  have fa' := lt_floor_cast_add_one a
  have fb := floor_cast_le b
  have fb' := lt_floor_cast_add_one b
  rcases hbox with ⟨hab, h1, h2⟩ | ⟨hba, h1, h2⟩ | ⟨heq, h⟩
  · have hst : axisStep a b = 1 := by unfold axisStep; simp [sub_pos.mpr hab]
    have hab' : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
    have hD := hD (by rw [hst]; decide)
    rw [hst] at hD
    simp only [gt_iff_lt, zero_lt_one, ↓reduceIte] at hD
    have h1' : ((a.floor : ℤ) : ℝ) ≤ (cx : ℝ) := by exact_mod_cast h1
    push_cast at hD
    rw [abs_of_pos (by linarith), abs_of_pos (by linarith)] at hD
    rw [abs_of_pos (sub_pos.mpr hab')] at hsmall
    have : (b.floor : ℝ) - 2 < (cx : ℝ) := by nlinarith
    have : b.floor - 2 < cx := by exact_mod_cast this
    omega
  · have hst : axisStep a b = -1 := by
      unfold axisStep; simp [not_lt.mpr (sub_nonpos.mpr hba.le), sub_neg.mpr hba]
    have hba' : (b : ℝ) < (a : ℝ) := by exact_mod_cast hba
    have hD := hD (by rw [hst]; decide)
    rw [hst] at hD
    simp only [gt_iff_lt, Left.neg_pos_iff, Int.reduceLT, ↓reduceIte] at hD
    have h2' : (cx : ℝ) ≤ ((a.floor : ℤ) : ℝ) := by exact_mod_cast h2
    rw [abs_of_neg (by linarith), abs_of_nonpos (by linarith)] at hD
    rw [abs_of_neg (sub_neg.mpr hba')] at hsmall
    have : (cx : ℝ) < (b.floor : ℝ) + 2 := by nlinarith
    have : cx < b.floor + 2 := by exact_mod_cast this
    omega
  · subst heq
    omega

theorem axis_pot_zero (a b : ℚ) (cx : ℤ) (hbox : AxisBox a b cx) (h0 : axisPot a b cx = 0) :
    (cx - b.floor).natAbs ≤ 1 := by
  unfold axisPot at h0
  rcases hbox with ⟨hab, h1, h2⟩ | ⟨hba, h1, h2⟩ | ⟨heq, h⟩
  · simp only [hab, ↓reduceIte] at h0; omega
  · simp only [not_lt.mpr hba.le, hba, ↓reduceIte] at h0; omega
  · subst heq; omega

theorem axis_start (a b : ℚ) :
    AxisBox a b a.floor ∧ axisPot a b a.floor ≤ (b.floor - a.floor).natAbs + 1 := by
  have hmono : ∀ {p q : ℚ}, p ≤ q → p.floor ≤ q.floor := fun h => floor_mono_rat h
  rcases lt_trichotomy a b with hab | heq | hba
  · have := hmono hab.le
    refine ⟨Or.inl ⟨hab, le_refl _, by omega⟩, ?_⟩
    unfold axisPot; simp only [hab, ↓reduceIte]; omega
  · subst heq
    refine ⟨Or.inr (Or.inr ⟨rfl, rfl⟩), ?_⟩
    unfold axisPot; simp
  · have := hmono hba.le
    refine ⟨Or.inr (Or.inl ⟨hba, by omega, le_refl _⟩), ?_⟩
    unfold axisPot; simp only [not_lt.mpr hba.le, hba, ↓reduceIte]; omega

theorem axis_bound (a b : ℚ) (cx : ℤ) (hbox : AxisBox a b cx) (ha : |a| ≤ mainCoordBound)
    (hb : |b| ≤ mainCoordBound) : |cx| ≤ mainCoordBound.floor + 1 := by
  have fa := floor_bounds_mainCoordBound ha
  have fb := floor_bounds_mainCoordBound hb
  rw [abs_le]
  rcases hbox with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ | ⟨-, h⟩ <;> constructor <;> omega

theorem axisStep_ne_zero {a b : ℚ} (hs : axisStep a b ≠ 0) : 0 < |(b : ℝ) - (a : ℝ)| := by
  apply abs_pos.mpr
  intro h
  apply hs
  have : b = a := by
    have : (b : ℝ) = (a : ℝ) := by linarith
    exact_mod_cast this
  unfold axisStep; simp [this]

theorem axis_small (a b : ℚ) (ha : |a| ≤ mainCoordBound) (hb : |b| ≤ mainCoordBound) :
    etaMarch * |(b : ℝ) - (a : ℝ)| < 1 := by
  have hd := maxCoordDelta_eq_two_mul
  have ha' : |(a : ℝ)| ≤ (mainCoordBound : ℝ) := by exact_mod_cast ha
  have hb' : |(b : ℝ)| ≤ (mainCoordBound : ℝ) := by exact_mod_cast hb
  have hle : |(b : ℝ) - (a : ℝ)| ≤ (maxCoordDelta : ℝ) := by
    rw [hd]
    have := abs_sub (b : ℝ) (a : ℝ)
    linarith
  have := etaMarch_small
  have := etaMarch_nonneg
  nlinarith

theorem floorPoint_eq_floor (p : Point) : floorPoint p = ⟨p.x.floor, p.y.floor⟩ := rfl

theorem axisStep_range (a b : ℚ) : axisStep a b = -1 ∨ axisStep a b = 0 ∨ axisStep a b = 1 := by
  unfold axisStep; split_ifs <;> simp

theorem step_active_or_absD (a b : ℚ) : axisStep a b = 0 ∨ 0 < |(b : ℝ) - (a : ℝ)| := by
  by_cases h : axisStep a b = 0
  · exact Or.inl h
  · exact Or.inr (axisStep_ne_zero h)

/-- A step that does not stop the march stays in the box and uses up at least one step. -/
theorem march_step_box (A B : Point32) (hA : A.isFinite) (hB : B.isFinite)
    (hbnd : inCoordBounds mainCoordBound A.toPoint B.toPoint) (c : Cell)
    (hbx : AxisBox A.toPoint.x B.toPoint.x c.x) (hby : AxisBox A.toPoint.y B.toPoint.y c.y)
    (hce : c ≠ floorPoint B.toPoint)
    (hd : (rayMarchStepFloat A (deltaX A B) (deltaY A B) (axisStep A.toPoint.x B.toPoint.x)
      (axisStep A.toPoint.y B.toPoint.y) c).2 = false) :
    AxisBox A.toPoint.x B.toPoint.x (rayMarchStepFloat A (deltaX A B) (deltaY A B)
        (axisStep A.toPoint.x B.toPoint.x) (axisStep A.toPoint.y B.toPoint.y) c).1.x ∧
    AxisBox A.toPoint.y B.toPoint.y (rayMarchStepFloat A (deltaX A B) (deltaY A B)
        (axisStep A.toPoint.x B.toPoint.x) (axisStep A.toPoint.y B.toPoint.y) c).1.y ∧
    axisPot A.toPoint.x B.toPoint.x (rayMarchStepFloat A (deltaX A B) (deltaY A B)
        (axisStep A.toPoint.x B.toPoint.x) (axisStep A.toPoint.y B.toPoint.y) c).1.x +
      axisPot A.toPoint.y B.toPoint.y (rayMarchStepFloat A (deltaX A B) (deltaY A B)
        (axisStep A.toPoint.x B.toPoint.x) (axisStep A.toPoint.y B.toPoint.y) c).1.y + 1 ≤
      axisPot A.toPoint.x B.toPoint.x c.x + axisPot A.toPoint.y B.toPoint.y c.y := by
  obtain ⟨hAx, hAy, hBx, hBy⟩ := hbnd
  have hsmX := axis_small _ _ hAx hBx
  have hsmY := axis_small _ _ hAy hBy
  have hcbx := axis_bound _ _ _ hbx hAx hBx
  have hcby := axis_bound _ _ _ hby hAy hBy
  set sx := axisStep A.toPoint.x B.toPoint.x with hsx
  set sy := axisStep A.toPoint.y B.toPoint.y with hsy
  -- moving along an active axis
  have moveX : sx ≠ 0 →
      (rayMarchStepFloat A (deltaX A B) (deltaY A B) sx sy c).1.x = c.x + sx →
      AxisBox A.toPoint.x B.toPoint.x (c.x + sx) ∧
        axisPot A.toPoint.x B.toPoint.x (c.x + sx) + 1 = axisPot A.toPoint.x B.toPoint.x c.x := by
    intro hs hmv
    have hyc : sy = 0 ∨ 0 < absDy_R A B := by
      by_cases h : sy = 0
      · exact Or.inl h
      · exact Or.inr (axisStep_ne_zero h)
    have hM := (x_step_bounds A B hA hB ⟨hAx, hAy, hBx, hBy⟩ sx sy hs hyc c hcbx hcby).2 hd hmv
    exact axis_move _ _ _ hbx hs etaMarch hsmX hM
  have moveY : sy ≠ 0 →
      (rayMarchStepFloat A (deltaX A B) (deltaY A B) sx sy c).1.y = c.y + sy →
      AxisBox A.toPoint.y B.toPoint.y (c.y + sy) ∧
        axisPot A.toPoint.y B.toPoint.y (c.y + sy) + 1 = axisPot A.toPoint.y B.toPoint.y c.y := by
    intro hs hmv
    have hxc : sx = 0 ∨ 0 < absDx_R A B := by
      by_cases h : sx = 0
      · exact Or.inl h
      · exact Or.inr (axisStep_ne_zero h)
    have hM := (y_step_bounds A B hA hB ⟨hAx, hAy, hBx, hBy⟩ sx sy hs hxc c hcbx hcby).2 hd hmv
    exact axis_move _ _ _ hby hs etaMarch hsmY hM
  by_cases hx0 : sx = 0
  · -- vertical: only y moves
    have hy0 : sy ≠ 0 := by
      intro hy0
      apply hce
      have hxe : (axisStep A.toPoint.x B.toPoint.x) = 0 := hx0
      have hye : (axisStep A.toPoint.y B.toPoint.y) = 0 := hy0
      rcases hbx with ⟨hab, -⟩ | ⟨hba, -⟩ | ⟨heq, hcx⟩
      · exfalso; unfold axisStep at hxe; simp [sub_pos.mpr hab] at hxe
      · exfalso; unfold axisStep at hxe
        simp [not_lt.mpr (sub_nonpos.mpr hba.le), sub_neg.mpr hba] at hxe
      rcases hby with ⟨hab, -⟩ | ⟨hba, -⟩ | ⟨heq', hcy⟩
      · exfalso; unfold axisStep at hye; simp [sub_pos.mpr hab] at hye
      · exfalso; unfold axisStep at hye
        simp [not_lt.mpr (sub_nonpos.mpr hba.le), sub_neg.mpr hba] at hye
      rw [floorPoint_eq_floor, ← heq, ← heq']
      cases c; simp_all
    have hd0 := hd
    rw [hx0] at hd0
    have hnext := step_not_X_when_stepX_zero A (deltaX A B) (deltaY A B) sy c hd0
    rw [← hx0] at hnext
    rw [hnext]
    obtain ⟨hb', hp'⟩ := moveY hy0 (by rw [hnext])
    exact ⟨hbx, hb', by simp only; omega⟩
  · by_cases hy0 : sy = 0
    · -- horizontal: only x moves
      have hd0 := hd
      rw [hy0] at hd0
      have hnext := step_not_Y_when_stepY_zero A (deltaX A B) (deltaY A B) sx c hx0 hd0
      rw [← hy0] at hnext
      rw [hnext]
      obtain ⟨hb', hp'⟩ := moveX hx0 (by rw [hnext])
      exact ⟨hb', hby, by simp only; omega⟩
    · -- diagonal
      rcases rayMarchStepFloat_done_or_cases A (deltaX A B) (deltaY A B) sx sy c with
        ⟨hd', -⟩ | ⟨-, h1 | h1 | h1⟩
      · rw [hd] at hd'; cases hd'
      · rw [h1]
        obtain ⟨hb', hp'⟩ := moveX hx0 (by rw [h1])
        exact ⟨hb', hby, by simp only; omega⟩
      · rw [h1]
        obtain ⟨hb', hp'⟩ := moveY hy0 (by rw [h1])
        exact ⟨hbx, hb', by simp only; omega⟩
      · rw [h1]
        obtain ⟨hbx', hpx'⟩ := moveX hx0 (by rw [h1])
        obtain ⟨hby', hpy'⟩ := moveY hy0 (by rw [h1])
        exact ⟨hbx', hby', by simp only; omega⟩

theorem rayMarchFloat_cons (n : ℕ) (start : Point32) (dx dy : Binary64) (sx sy : ℤ) (e nx : Cell) :
    rayMarchFloat n start dx dy sx sy e nx [nx] = nx :: rayMarchFloat n start dx dy sx sy e nx [] := by
  rw [rayMarchFloat_acc]
  rfl

theorem path_step (c nx e : Cell) (rest : List Cell) (hadj : chebyshevDistance c nx ≤ 1)
    (hc : CellPathConnected (nx :: rest))
    (hl : chebyshevDistance ((nx :: rest).getLast (List.cons_ne_nil _ _)) e ≤ 1) :
    CellPathConnected (c :: nx :: rest) ∧
      chebyshevDistance ((c :: nx :: rest).getLast (List.cons_ne_nil _ _)) e ≤ 1 := by
  refine ⟨⟨hadj, hc⟩, ?_⟩
  rw [List.getLast_cons (List.cons_ne_nil _ _)]
  exact hl

/-- The float march from any cell in the box is connected and stops next to the end cell. -/
theorem march_connected (A B : Point32) (hA : A.isFinite) (hB : B.isFinite)
    (hbound : inCoordBounds mainCoordBound A.toPoint B.toPoint) :
    ∀ (n : ℕ) (c : Cell),
      AxisBox A.toPoint.x B.toPoint.x c.x → AxisBox A.toPoint.y B.toPoint.y c.y →
      axisPot A.toPoint.x B.toPoint.x c.x + axisPot A.toPoint.y B.toPoint.y c.y ≤ n →
      CellPathConnected (c :: rayMarchFloat n A (deltaX A B) (deltaY A B)
          (if deltaX A B > 0.0 then 1 else if deltaX A B < 0.0 then -1 else 0)
          (if deltaY A B > 0.0 then 1 else if deltaY A B < 0.0 then -1 else 0)
          (floorPoint B.toPoint) c []) ∧
      chebyshevDistance ((c :: rayMarchFloat n A (deltaX A B) (deltaY A B)
          (if deltaX A B > 0.0 then 1 else if deltaX A B < 0.0 then -1 else 0)
          (if deltaY A B > 0.0 then 1 else if deltaY A B < 0.0 then -1 else 0)
          (floorPoint B.toPoint) c []).getLast (List.cons_ne_nil _ _)) (floorPoint B.toPoint) ≤ 1 := by
  have hsX : (if deltaX A B > 0.0 then (1 : ℤ) else if deltaX A B < 0.0 then -1 else 0) =
      axisStep A.toPoint.x B.toPoint.x := step_signs_agree_X A B hA hB hbound
  have hsY : (if deltaY A B > 0.0 then (1 : ℤ) else if deltaY A B < 0.0 then -1 else 0) =
      axisStep A.toPoint.y B.toPoint.y := step_signs_agree_Y A B hA hB hbound
  rw [hsX, hsY]
  obtain ⟨hAx, hAy, hBx, hBy⟩ := hbound
  have hsmX := axis_small _ _ hAx hBx
  have hsmY := axis_small _ _ hAy hBy
  intro n
  induction n with
  | zero =>
    intro c hbx hby hpot
    refine ⟨trivial, ?_⟩
    simp only [rayMarchFloat, List.getLast_singleton, chebyshevDistance, floorPoint_eq_floor]
    have h1 := axis_pot_zero _ _ _ hbx (by omega)
    have h2 := axis_pot_zero _ _ _ hby (by omega)
    exact max_le h1 h2
  | succ n ih =>
    intro c hbx hby hpot
    have hcbx := axis_bound _ _ _ hbx hAx hBx
    have hcby := axis_bound _ _ _ hby hAy hBy
    have hbnd : inCoordBounds mainCoordBound A.toPoint B.toPoint := ⟨hAx, hAy, hBx, hBy⟩
    rw [rayMarchFloat]
    by_cases hce : (c == floorPoint B.toPoint) = true
    · simp only [hce, ↓reduceIte, List.getLast_singleton]
      refine ⟨trivial, ?_⟩
      rw [beq_iff_eq.mp hce]
      simp [chebyshevDistance]
    · simp only [hce, Bool.false_eq_true, ↓reduceIte]
      by_cases hd : (rayMarchStepFloat A (deltaX A B) (deltaY A B) (axisStep A.toPoint.x B.toPoint.x)
          (axisStep A.toPoint.y B.toPoint.y) c).2 = true
      · simp only [hd, ↓reduceIte, List.getLast_singleton]
        refine ⟨trivial, ?_⟩
        simp only [chebyshevDistance, floorPoint_eq_floor]
        have hx := axis_done _ _ _ hbx etaMarch hsmX (fun hs =>
          (x_step_bounds A B hA hB hbnd _ _ hs (step_active_or_absD _ _) c hcbx hcby).1 hd)
        have hy := axis_done _ _ _ hby etaMarch hsmY (fun hs =>
          (y_step_bounds A B hA hB hbnd _ _ hs (step_active_or_absD _ _) c hcbx hcby).1 hd)
        exact max_le hx hy
      · have hd' : (rayMarchStepFloat A (deltaX A B) (deltaY A B) (axisStep A.toPoint.x B.toPoint.x)
            (axisStep A.toPoint.y B.toPoint.y) c).2 = false := by simpa using hd
        simp only [hd, Bool.false_eq_true, ↓reduceIte, List.nil_append]
        have hce' : c ≠ floorPoint B.toPoint := by
          intro h
          apply hce
          rw [h]
          exact beq_self_eq_true _
        have hstep := march_step_box A B hA hB hbnd c hbx hby hce' hd'
        have hbx' := hstep.1
        have hby' := hstep.2.1
        have hpot' := hstep.2.2
        clear hstep
        have hadj := chebyshevDistance_stepFloat_le_one A (deltaX A B) (deltaY A B) _ _
          (axisStep_range A.toPoint.x B.toPoint.x) (axisStep_range A.toPoint.y B.toPoint.y) c
        have ih' := ih _ hbx' hby' (by omega)
        have key := path_step _ _ (floorPoint B.toPoint) _ hadj ih'.1 ih'.2
        simp only [rayMarchFloat_cons]
        exact key

theorem connected_append_last (l : List Cell) (hl : l ≠ []) (e : Cell) (hc : CellPathConnected l)
    (hd : chebyshevDistance (l.getLast hl) e ≤ 1) : CellPathConnected (l ++ [e]) := by
  induction l with
  | nil => exact absurd rfl hl
  | cons a rest ih =>
    cases rest with
    | nil =>
      simp only [List.getLast_singleton] at hd
      exact ⟨hd, trivial⟩
    | cons b rest' =>
      obtain ⟨hab, hrest⟩ := hc
      rw [List.getLast_cons (List.cons_ne_nil _ _)] at hd
      exact ⟨hab, ih (List.cons_ne_nil _ _) hrest hd⟩

/--
The float model's cells have no gaps: they can be listed as a path of neighboring cells (king moves)
from the start cell to the end cell.
-/
theorem cellIntersectionsSegmentFloat_connected_Impl (A B : Point32) (hA : A.isFinite)
    (hB : B.isFinite) (hbound : inCoordBounds mainCoordBound A.toPoint B.toPoint) :
    ∃ path : List Cell, path.head? = some (floorPoint32 A) ∧ path.getLast? = some (floorPoint32 B) ∧
      CellPathConnected path ∧ ∀ c, c ∈ path ↔ c ∈ cellIntersectionsSegmentFloat A B := by
  have hfA := floorPoint32_eq_floorPoint A hA
  have hfB := floorPoint32_eq_floorPoint B hB
  unfold cellIntersectionsSegmentFloat
  by_cases hsame : (floorPoint32 A == floorPoint32 B) = true
  · simp only [hsame, ↓reduceIte]
    refine ⟨[floorPoint32 A], rfl, ?_, trivial, fun _ => Iff.rfl⟩
    rw [beq_iff_eq.mp hsame]; rfl
  · simp only [hsame, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨hbx, hpx⟩ := axis_start A.toPoint.x B.toPoint.x
    obtain ⟨hby, hpy⟩ := axis_start A.toPoint.y B.toPoint.y
    have hmc := march_connected A B hA hB hbound
      (((floorPoint32 B).x - (floorPoint32 A).x).natAbs +
        ((floorPoint32 B).y - (floorPoint32 A).y).natAbs + 2) (floorPoint A.toPoint) hbx hby
      (by rw [hfA, hfB]; simp only [floorPoint_eq_floor]; omega)
    rw [← hfA, ← hfB] at hmc
    obtain ⟨hconn, hlast⟩ := hmc
    refine ⟨(floorPoint32 A :: rayMarchFloat
      (((floorPoint32 B).x - (floorPoint32 A).x).natAbs +
        ((floorPoint32 B).y - (floorPoint32 A).y).natAbs + 2) A (deltaX A B) (deltaY A B)
      (if deltaX A B > 0.0 then 1 else if deltaX A B < 0.0 then -1 else 0)
      (if deltaY A B > 0.0 then 1 else if deltaY A B < 0.0 then -1 else 0) (floorPoint32 B)
      (floorPoint32 A) []) ++ [floorPoint32 B], rfl, List.getLast?_concat, ?_, ?_⟩
    · exact connected_append_last _ (List.cons_ne_nil _ _) _ hconn hlast
    · intro c
      rw [mem_dedupCells]
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      tauto

end Geometry
