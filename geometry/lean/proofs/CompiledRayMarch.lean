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
import Geometry.LineSegment
import GeometryDefs
import proofs.FloatBounds
import proofs.FloatAnalysis
import proofs.RayMarchLimits
import proofs.NativeFloat
import Mathlib.Tactic

/-!
# The compiled ray march refines the float model

`rayMarchSegmentCoords` (`Geometry/LineSegment.lean`) is compiled to Kotlin and computes with
native `Float`s. This file proves that, within `InRange`, its output cells are exactly the cells of
the float model `cellIntersectionsSegmentFloat` (after removing duplicates), using the agreement
between native floats and FloatLib's binary64 from `proofs/NativeFloat.lean`.
-/

namespace Geometry

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange

/-- One iteration of the compiled `rayMarchLoop`: the next cell, or `none` when the march stops. -/
def nativeStep (startX startY absDx absDy : Float) (stepX stepY : Int32) (curX curY : Int32) :
    Option (Int32 × Int32) :=
  let xb : Float := if stepX > 0 then (curX + 1).toFloat else curX.toFloat
  let yb : Float := if stepY > 0 then (curY + 1).toFloat else curY.toFloat
  if stepX == 0 then
    let remY := absFloat (yb - startY)
    if remY >= absDy then none else some (curX, curY + stepY)
  else if stepY == 0 then
    let remX := absFloat (xb - startX)
    if remX >= absDx then none else some (curX + stepX, curY)
  else
    let remX := absFloat (xb - startX)
    let remY := absFloat (yb - startY)
    let crossX := remX * absDy
    let crossY := remY * absDx
    let limitCross := absDx * absDy
    let minCross := if crossX < crossY then crossX else crossY
    if minCross >= limitCross then none
    else
      some (if crossX <= crossY then curX + stepX else curX,
        if crossY <= crossX then curY + stepY else curY)

theorem rayMarchLoop_zero (startX startY dx dy absDx absDy : Float) (stepX stepY endX endY curX curY : Int32)
    (acc : Array (Int32 × Int32)) :
    rayMarchLoop 0 startX startY dx dy absDx absDy stepX stepY endX endY curX curY acc = acc := by
  rw [rayMarchLoop]
  simp

theorem rayMarchLoop_succ (fuel : UInt32) (hf : fuel ≠ 0) (startX startY dx dy absDx absDy : Float)
    (stepX stepY endX endY curX curY : Int32) (acc : Array (Int32 × Int32)) :
    rayMarchLoop fuel startX startY dx dy absDx absDy stepX stepY endX endY curX curY acc =
      if curX == endX && curY == endY then acc
      else match nativeStep startX startY absDx absDy stepX stepY curX curY with
        | none => acc
        | some (nx, ny) =>
          rayMarchLoop (fuel - 1) startX startY dx dy absDx absDy stepX stepY endX endY nx ny
            (acc.push (nx, ny)) := by
  rw [rayMarchLoop]
  have hf' : (fuel == 0) = false := by simpa using hf
  simp only [hf', Bool.false_eq_true, ↓reduceIte]
  by_cases hend : (curX == endX && curY == endY) = true
  · simp only [hend, ↓reduceIte]
  · simp only [hend, Bool.false_eq_true, ↓reduceIte, nativeStep]
    split_ifs <;> rfl

/-! ## Ranges -/

theorem int32_toInt_add (a b : Int32) (h1 : -2 ^ 31 ≤ a.toInt + b.toInt) (h2 : a.toInt + b.toInt < 2 ^ 31) :
    (a + b).toInt = a.toInt + b.toInt := by
  rw [Int32.toInt_add]
  exact Int.bmod_eq_of_le (by omega) (by omega)

theorem abs_roundAt_le (r : ℝ) (N : ℤ) (hN0 : 0 ≤ N) (hN : N ≤ (mainCoordBoundNat : ℤ) + 2)
    (hr : |r| ≤ N) : |Model.roundAt FloatFormat.binary64 r| ≤ N := by
  have hNabs : |N| ≤ (mainCoordBoundNat : ℤ) + 2 := by rw [abs_of_nonneg hN0]; exact hN
  have hfin := intToBinary64_isFinite N hNabs
  have hval := intToBinary64_toReal_eq N hNabs
  have hround : Model.roundAt FloatFormat.binary64 (N : ℝ) = N := by
    have := Model.roundAt_toReal_eq (ExecFloat.Binary.toModel (intToBinary64 N)) hfin
    rw [hval] at this
    exact this
  have h1 := Model.roundAt_mono FloatFormat.binary64 (le_abs_self r |>.trans hr)
  have h2 := Model.roundAt_mono FloatFormat.binary64 (neg_le_of_abs_le hr)
  rw [hround] at h1
  rw [Model.roundAt_neg, hround] at h2
  exact abs_le.mpr ⟨by linarith, h1⟩

theorem two_pow_62_le_posMaxFinite :
    (2 : ℝ) ^ 62 ≤ Model.toReal (Model.posMaxFinite FloatFormat.binary64) := by
  have h := Model.abs_signed_mul_bpow_le_toReal_posMaxFinite FloatFormat.binary64 false (2 ^ 52) 10
    (by decide) (by decide)
  simp only [Bool.false_eq_true, ite_false, one_mul] at h
  have hb : Model.bpow (10 : ℤ) = (2 : ℝ) ^ 10 := by
    rw [show (10 : ℤ) = ((10 : ℕ) : ℤ) by rfl, Model.bpow_natCast]
  rw [hb, abs_of_pos (by positivity)] at h
  have : ((2 ^ 52 : ℕ) : ℝ) * 2 ^ 10 = 2 ^ 62 := by push_cast; ring
  linarith

/-- Values that stay the same during the whole march, related between the compiled code and the model. -/
structure MarchCtx (A : Point32) (dxB dyB : Binary64) (stepXI stepYI : ℤ)
    (sx sy absDxN absDyN : Float) (stepXN stepYN : Int32) : Prop where
  hsx : Agree sx (widen32To64 A.x)
  hsy : Agree sy (widen32To64 A.y)
  hadx : Agree absDxN (ExecFloat.Binary.abs dxB)
  hady : Agree absDyN (ExecFloat.Binary.abs dyB)
  hstepX : stepXN.toInt = stepXI
  hstepY : stepYN.toInt = stepYI
  hsX : stepXI = -1 ∨ stepXI = 0 ∨ stepXI = 1
  hsY : stepYI = -1 ∨ stepYI = 0 ∨ stepYI = 1
  hAx : |breal (widen32To64 A.x)| ≤ 2 ^ 28
  hAy : |breal (widen32To64 A.y)| ≤ 2 ^ 28
  hdx : |breal (ExecFloat.Binary.abs dxB)| ≤ 2 ^ 30
  hdy : |breal (ExecFloat.Binary.abs dyB)| ≤ 2 ^ 30

/-- The distance from the march start to a cell boundary agrees between the compiled code and the model. -/
theorem rem_agree (k : Int32) (start : Float) (startB : Binary64) (hs : Agree start startB)
    (hsb : |breal startB| ≤ 2 ^ 28) (hk : |k.toInt| ≤ 2 ^ 30 + 2 ^ 29 + 1) :
    Agree (absFloat (k.toFloat - start)) (ExecFloat.Binary.abs (intToBinary64 k.toInt - startB)) ∧
      |breal (ExecFloat.Binary.abs (intToBinary64 k.toInt - startB))| ≤ 2 ^ 31 - 1 := by
  have hmain : (mainCoordBoundNat : ℤ) + 2 = 2 ^ 31 - 1 := by decide
  obtain ⟨hka, hkr⟩ := Agree.int32 k (by rw [hmain]; omega)
  have hkr' : |breal (intToBinary64 k.toInt)| ≤ 2 ^ 30 + 2 ^ 29 + 1 := by
    rw [hkr]; exact_mod_cast hk
  have hmax := two_pow_62_le_posMaxFinite
  obtain ⟨hsa, hsr⟩ := Agree.sub hka hs (by nlinarith [abs_nonneg (breal startB)])
  obtain ⟨haa, har⟩ := Agree.absFloat hsa
  refine ⟨haa, ?_⟩
  rw [har, abs_abs, hsr]
  have hle : |breal (intToBinary64 k.toInt) - breal startB| ≤ ((2 ^ 31 - 1 : ℤ) : ℝ) := by
    have := abs_sub (breal (intToBinary64 k.toInt)) (breal startB)
    push_cast
    linarith
  have := abs_roundAt_le _ (2 ^ 31 - 1) (by norm_num) (by rw [hmain]) hle
  push_cast at this
  norm_num
  exact this

/-- One iteration of the compiled loop computes the float model's step. -/
theorem nativeStep_refines {A : Point32} {dxB dyB : Binary64} {stepXI stepYI : ℤ}
    {sx sy absDxN absDyN : Float} {stepXN stepYN : Int32}
    (ctx : MarchCtx A dxB dyB stepXI stepYI sx sy absDxN absDyN stepXN stepYN)
    (c : Cell) (curX curY : Int32) (hcx : curX.toInt = c.x) (hcy : curY.toInt = c.y)
    (hbx : |c.x| ≤ 2 ^ 30 + 2 ^ 29) (hby : |c.y| ≤ 2 ^ 30 + 2 ^ 29) :
    match nativeStep sx sy absDxN absDyN stepXN stepYN curX curY with
    | none => (rayMarchStepFloat A dxB dyB stepXI stepYI c).2 = true
    | some (nx, ny) => (rayMarchStepFloat A dxB dyB stepXI stepYI c).2 = false ∧
        (rayMarchStepFloat A dxB dyB stepXI stepYI c).1 = ⟨nx.toInt, ny.toInt⟩ := by
  obtain ⟨hbx1, hbx2⟩ := abs_le.mp hbx
  obtain ⟨hby1, hby2⟩ := abs_le.mp hby
  -- the cell boundaries in the step direction
  set kx : Int32 := if stepXN > 0 then curX + 1 else curX with hkx
  set ky : Int32 := if stepYN > 0 then curY + 1 else curY with hky
  have hgtX : (stepXN > 0) ↔ (stepXI > 0) := by
    rw [← ctx.hstepX]; simp [Int32.lt_iff_toInt_lt]
  have hgtY : (stepYN > 0) ↔ (stepYI > 0) := by
    rw [← ctx.hstepY]; simp [Int32.lt_iff_toInt_lt]
  have hkxI : kx.toInt = (if stepXI > 0 then c.x + 1 else c.x) := by
    rw [hkx]
    by_cases h : stepXI > 0
    · simp only [hgtX.mpr h, h, ↓reduceIte]
      rw [int32_toInt_add _ _ (by simp; omega) (by simp; omega), hcx]; rfl
    · have h' : ¬ stepXN > 0 := fun h' => h (hgtX.mp h')
      simp only [h', h, ↓reduceIte, hcx]
  have hkyI : ky.toInt = (if stepYI > 0 then c.y + 1 else c.y) := by
    rw [hky]
    by_cases h : stepYI > 0
    · simp only [hgtY.mpr h, h, ↓reduceIte]
      rw [int32_toInt_add _ _ (by simp; omega) (by simp; omega), hcy]; rfl
    · have h' : ¬ stepYN > 0 := fun h' => h (hgtY.mp h')
      simp only [h', h, ↓reduceIte, hcy]
  have hxb : (if stepXN > 0 then (curX + 1).toFloat else curX.toFloat) = kx.toFloat := by
    rw [hkx]; split <;> rfl
  have hyb : (if stepYN > 0 then (curY + 1).toFloat else curY.toFloat) = ky.toFloat := by
    rw [hky]; split <;> rfl
  have hkxb : |kx.toInt| ≤ 2 ^ 30 + 2 ^ 29 + 1 := by
    rw [hkxI]; split <;> exact abs_le.mpr ⟨by omega, by omega⟩
  have hkyb : |ky.toInt| ≤ 2 ^ 30 + 2 ^ 29 + 1 := by
    rw [hkyI]; split <;> exact abs_le.mpr ⟨by omega, by omega⟩
  obtain ⟨hremX, hremXb⟩ := rem_agree kx sx _ ctx.hsx ctx.hAx hkxb
  obtain ⟨hremY, hremYb⟩ := rem_agree ky sy _ ctx.hsy ctx.hAy hkyb
  have hX0 : (stepXN == 0) = (stepXI == 0) := by
    rw [← ctx.hstepX, Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, ← Int32.toInt_inj, Int32.toInt_zero]
  have hY0 : (stepYN == 0) = (stepYI == 0) := by
    rw [← ctx.hstepY, Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, ← Int32.toInt_inj, Int32.toInt_zero]
  have hstepXb : -1 ≤ stepXN.toInt ∧ stepXN.toInt ≤ 1 := by rw [ctx.hstepX]; rcases ctx.hsX with h | h | h <;> omega
  have hstepYb : -1 ≤ stepYN.toInt ∧ stepYN.toInt ≤ 1 := by rw [ctx.hstepY]; rcases ctx.hsY with h | h | h <;> omega
  have haddX : (curX + stepXN).toInt = c.x + stepXI := by
    rw [int32_toInt_add _ _ (by omega) (by omega), hcx, ctx.hstepX]
  have haddY : (curY + stepYN).toInt = c.y + stepYI := by
    rw [int32_toInt_add _ _ (by omega) (by omega), hcy, ctx.hstepY]
  unfold nativeStep rayMarchStepFloat
  simp only [hxb, hyb, ← hkxI, ← hkyI, hX0, hY0]
  by_cases hx0 : (stepXI == 0) = true
  · -- vertical march
    have hc := Agree.le_iff ctx.hady hremY
    simp only [hx0, ↓reduceIte]
    by_cases hge : absFloat (ky.toFloat - sy) ≥ absDyN
    · have hge' : ExecFloat.Binary.abs (intToBinary64 ky.toInt - widen32To64 A.y) ≥
          ExecFloat.Binary.abs dyB := hc.mp hge
      simp only [hge, hge', ↓reduceIte]
    · have hge' : ¬ ExecFloat.Binary.abs (intToBinary64 ky.toInt - widen32To64 A.y) ≥
          ExecFloat.Binary.abs dyB := fun h => hge (hc.mpr h)
      simp only [hge, hge', ↓reduceIte]
      exact ⟨trivial, by rw [hcx, haddY]⟩
  · by_cases hy0 : (stepYI == 0) = true
    · -- horizontal march
      have hc := Agree.le_iff ctx.hadx hremX
      simp only [hx0, hy0, Bool.false_eq_true, ↓reduceIte]
      by_cases hge : absFloat (kx.toFloat - sx) ≥ absDxN
      · have hge' : ExecFloat.Binary.abs (intToBinary64 kx.toInt - widen32To64 A.x) ≥
            ExecFloat.Binary.abs dxB := hc.mp hge
        simp only [hge, hge', ↓reduceIte]
      · have hge' : ¬ ExecFloat.Binary.abs (intToBinary64 kx.toInt - widen32To64 A.x) ≥
            ExecFloat.Binary.abs dxB := fun h => hge (hc.mpr h)
        simp only [hge, hge', ↓reduceIte]
        exact ⟨trivial, by rw [hcy, haddX]⟩
    · -- diagonal march
      simp only [hx0, hy0, Bool.false_eq_true, ↓reduceIte]
      have hmax := two_pow_62_le_posMaxFinite
      have hb31 : (2 : ℝ) ^ 31 - 1 ≤ 2 ^ 31 := by norm_num
      have hdx := ctx.hdx
      have hdy := ctx.hdy
      have bX : |breal (ExecFloat.Binary.abs (intToBinary64 kx.toInt - widen32To64 A.x))| *
          |breal (ExecFloat.Binary.abs dyB)| ≤ Model.toReal (Model.posMaxFinite FloatFormat.binary64) := by
        calc _ ≤ (2 ^ 31 : ℝ) * 2 ^ 30 :=
              mul_le_mul (le_trans hremXb hb31) hdy (abs_nonneg _) (by positivity)
          _ ≤ _ := by norm_num at hmax ⊢; linarith
      have bY : |breal (ExecFloat.Binary.abs (intToBinary64 ky.toInt - widen32To64 A.y))| *
          |breal (ExecFloat.Binary.abs dxB)| ≤ Model.toReal (Model.posMaxFinite FloatFormat.binary64) := by
        calc _ ≤ (2 ^ 31 : ℝ) * 2 ^ 30 :=
              mul_le_mul (le_trans hremYb hb31) hdx (abs_nonneg _) (by positivity)
          _ ≤ _ := by norm_num at hmax ⊢; linarith
      have bL : |breal (ExecFloat.Binary.abs dxB)| * |breal (ExecFloat.Binary.abs dyB)| ≤
          Model.toReal (Model.posMaxFinite FloatFormat.binary64) := by
        calc _ ≤ (2 ^ 30 : ℝ) * 2 ^ 30 := mul_le_mul hdx hdy (abs_nonneg _) (by positivity)
          _ ≤ _ := by norm_num at hmax ⊢; linarith
      obtain ⟨hcX, -⟩ := Agree.mul hremX ctx.hady bX
      obtain ⟨hcY, -⟩ := Agree.mul hremY ctx.hadx bY
      obtain ⟨hL, -⟩ := Agree.mul ctx.hadx ctx.hady bL
      -- every comparison of the step, on both sides, as a comparison of real values
      have e1 := Agree.lt_iff hcX hcY
      have e2 := Agree.lt_iff hcY hcX
      have e3 := Agree.le_iff hcX hcY
      have e4 := Agree.le_iff hcY hcX
      have e5 := Agree.le_iff hL hcX
      have e6 := Agree.le_iff hL hcY
      rw [binary_lt_iff_real _ _ hcX.bfin hcY.bfin] at e1
      rw [binary_lt_iff_real _ _ hcY.bfin hcX.bfin] at e2
      rw [binary_le_iff_real _ _ hcX.bfin hcY.bfin] at e3
      rw [binary_le_iff_real _ _ hcY.bfin hcX.bfin] at e4
      rw [binary_le_iff_real _ _ hL.bfin hcX.bfin] at e5
      rw [binary_le_iff_real _ _ hL.bfin hcY.bfin] at e6
      have m1 := binary_lt_iff_real _ _ hcX.bfin hcY.bfin
      have m2 := binary_lt_iff_real _ _ hcY.bfin hcX.bfin
      have m3 := min_ge_iff_of_isFinite_binary64 _ _ _ hcX.bfin hcY.bfin hL.bfin
      simp only [ge_iff_le] at m3 ⊢
      rw [binary_le_iff_real _ _ hL.bfin hcX.bfin, binary_le_iff_real _ _ hL.bfin hcY.bfin] at m3
      simp only [m3, m1, m2]
      rcases lt_trichotomy
          (breal (ExecFloat.Binary.abs (intToBinary64 kx.toInt - widen32To64 A.x) * ExecFloat.Binary.abs dyB))
          (breal (ExecFloat.Binary.abs (intToBinary64 ky.toInt - widen32To64 A.y) * ExecFloat.Binary.abs dxB))
        with hxy | hxy | hxy
      · simp only [e1.mpr hxy, ↓reduceIte]
        by_cases hl : breal (ExecFloat.Binary.abs dxB * ExecFloat.Binary.abs dyB) ≤
            breal (ExecFloat.Binary.abs (intToBinary64 kx.toInt - widen32To64 A.x) * ExecFloat.Binary.abs dyB)
        · simp only [e5.mpr hl, ↓reduceIte, hl, le_of_lt (lt_of_le_of_lt hl hxy), and_self]
        · have hn : ¬ (absDxN * absDyN ≤ absFloat (kx.toFloat - sx) * absDyN) := fun h => hl (e5.mp h)
          have hle1 : absFloat (kx.toFloat - sx) * absDyN ≤ absFloat (ky.toFloat - sy) * absDxN :=
            e3.mpr (le_of_lt hxy)
          have hle2 : ¬ (absFloat (ky.toFloat - sy) * absDxN ≤ absFloat (kx.toFloat - sx) * absDyN) :=
            fun h => (not_le.mpr hxy) (e4.mp h)
          simp only [hn, ↓reduceIte, hl, false_and, hxy, hle1, hle2]
          exact ⟨trivial, by rw [haddX, hcy]⟩
      · have hnlt : ¬ (absFloat (kx.toFloat - sx) * absDyN < absFloat (ky.toFloat - sy) * absDxN) :=
          fun h => by have h' := e1.mp h; rw [hxy] at h'; exact lt_irrefl _ h'
        simp only [hnlt, ↓reduceIte]
        by_cases hl : breal (ExecFloat.Binary.abs dxB * ExecFloat.Binary.abs dyB) ≤
            breal (ExecFloat.Binary.abs (intToBinary64 ky.toInt - widen32To64 A.y) * ExecFloat.Binary.abs dxB)
        · have hl' : breal (ExecFloat.Binary.abs dxB * ExecFloat.Binary.abs dyB) ≤
              breal (ExecFloat.Binary.abs (intToBinary64 kx.toInt - widen32To64 A.x) *
                ExecFloat.Binary.abs dyB) := by rw [hxy]; exact hl
          simp only [e6.mpr hl, ↓reduceIte, hl, hl', and_self]
        · have hn : ¬ (absDxN * absDyN ≤ absFloat (ky.toFloat - sy) * absDxN) := fun h => hl (e6.mp h)
          have hle1 : absFloat (kx.toFloat - sx) * absDyN ≤ absFloat (ky.toFloat - sy) * absDxN :=
            e3.mpr (le_of_eq hxy)
          have hle2 : absFloat (ky.toFloat - sy) * absDxN ≤ absFloat (kx.toFloat - sx) * absDyN :=
            e4.mpr (le_of_eq hxy.symm)
          simp only [hn, ↓reduceIte, hl, and_false, hxy, lt_irrefl, hle1, hle2]
          exact ⟨trivial, by rw [haddX, haddY]⟩
      · have hnlt : ¬ (absFloat (kx.toFloat - sx) * absDyN < absFloat (ky.toFloat - sy) * absDxN) :=
          fun h => (lt_asymm hxy) (e1.mp h)
        simp only [hnlt, ↓reduceIte]
        by_cases hl : breal (ExecFloat.Binary.abs dxB * ExecFloat.Binary.abs dyB) ≤
            breal (ExecFloat.Binary.abs (intToBinary64 ky.toInt - widen32To64 A.y) * ExecFloat.Binary.abs dxB)
        · simp only [e6.mpr hl, ↓reduceIte, hl, le_of_lt (lt_of_le_of_lt hl hxy), and_self]
        · have hn : ¬ (absDxN * absDyN ≤ absFloat (ky.toFloat - sy) * absDxN) := fun h => hl (e6.mp h)
          have hle1 : ¬ (absFloat (kx.toFloat - sx) * absDyN ≤ absFloat (ky.toFloat - sy) * absDxN) :=
            fun h => (not_le.mpr hxy) (e3.mp h)
          have hle2 : absFloat (ky.toFloat - sy) * absDxN ≤ absFloat (kx.toFloat - sx) * absDyN :=
            e4.mpr (le_of_lt hxy)
          simp only [hn, ↓reduceIte, hl, and_false, not_lt.mpr (le_of_lt hxy), hxy, hle1, hle2]
          exact ⟨trivial, by rw [hcx, haddY]⟩
theorem toCells_push (acc : Array (Int32 × Int32)) (p : Int32 × Int32) :
    toCells (acc.push p) = toCells acc ++ [⟨p.1.toInt, p.2.toInt⟩] := by
  simp [toCells]

theorem int32_beq_toInt (a b : Int32) : (a == b) = (a.toInt == b.toInt) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, Int32.toInt_inj]

theorem end_beq (curX curY endX endY : Int32) (c endCell : Cell) (hcx : curX.toInt = c.x)
    (hcy : curY.toInt = c.y) (hex : endX.toInt = endCell.x) (hey : endY.toInt = endCell.y) :
    (curX == endX && curY == endY) = (c == endCell) := by
  rw [cell_beq_def, ← hcx, ← hcy, ← hex, ← hey, int32_beq_toInt, int32_beq_toInt]

/-- The compiled loop computes the float model's march, cell by cell. -/
theorem rayMarchLoop_refines {A : Point32} {dxB dyB : Binary64} {stepXI stepYI : ℤ}
    {sx sy dxN dyN absDxN absDyN : Float} {stepXN stepYN endX endY : Int32} {endCell : Cell}
    (ctx : MarchCtx A dxB dyB stepXI stepYI sx sy absDxN absDyN stepXN stepYN)
    (hex : endX.toInt = endCell.x) (hey : endY.toInt = endCell.y) :
    ∀ (n : ℕ) (c : Cell) (curX curY : Int32) (acc : Array (Int32 × Int32)),
      n < 2 ^ 32 → curX.toInt = c.x → curY.toInt = c.y →
      c.x.natAbs + n ≤ 2 ^ 30 + 2 ^ 29 → c.y.natAbs + n ≤ 2 ^ 30 + 2 ^ 29 →
      toCells (rayMarchLoop (UInt32.ofNat n) sx sy dxN dyN absDxN absDyN stepXN stepYN endX endY
          curX curY acc) =
        rayMarchFloat n A dxB dyB stepXI stepYI endCell c (toCells acc) := by
  intro n
  induction n with
  | zero =>
    intro c curX curY acc _ _ _ _ _
    rw [show UInt32.ofNat 0 = 0 from rfl, rayMarchLoop_zero]
    rfl
  | succ n ih =>
    intro c curX curY acc hn hcx hcy hbx hby
    have hsz : UInt32.size = 2 ^ 32 := rfl
    have hne : UInt32.ofNat (n + 1) ≠ 0 := by
      intro h
      have := congrArg UInt32.toNat h
      rw [UInt32.toNat_ofNat_of_lt' (by rw [hsz]; exact hn)] at this
      simp at this
    have hpred : UInt32.ofNat (n + 1) - 1 = UInt32.ofNat n := by
      apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_sub_of_le _ _ (by
        rw [UInt32.le_iff_toNat_le, UInt32.toNat_ofNat_of_lt' (by rw [hsz]; exact hn)]; simp),
        UInt32.toNat_ofNat_of_lt' (by rw [hsz]; exact hn), UInt32.toNat_ofNat_of_lt' (by rw [hsz]; omega)]
      simp
    rw [rayMarchLoop_succ _ hne, end_beq curX curY endX endY c endCell hcx hcy hex hey]
    unfold rayMarchFloat
    by_cases hend : (c == endCell) = true
    · simp only [hend, ↓reduceIte]
    · simp only [hend, Bool.false_eq_true, ↓reduceIte]
      have hstep := nativeStep_refines ctx c curX curY hcx hcy
        (abs_le.mpr ⟨by omega, by omega⟩) (abs_le.mpr ⟨by omega, by omega⟩)
      have hcheb := chebyshevDistance_stepFloat_le_one A dxB dyB stepXI stepYI ctx.hsX ctx.hsY c
      revert hstep
      cases nativeStep sx sy absDxN absDyN stepXN stepYN curX curY with
      | none =>
        intro hstep
        simp only [hstep, ↓reduceIte]
      | some p =>
        obtain ⟨nx, ny⟩ := p
        intro ⟨hdone, hnext⟩
        simp only [hdone, Bool.false_eq_true, ↓reduceIte]
        rw [hpred, ih ⟨nx.toInt, ny.toInt⟩ nx ny _ (by omega) rfl rfl, toCells_push, hnext]
        · rw [hnext] at hcheb
          simp only [chebyshevDistance] at hcheb
          have h1 : (c.x - nx.toInt).natAbs ≤ 1 := le_trans (le_max_left _ _) hcheb
          show nx.toInt.natAbs + n ≤ _
          omega
        · rw [hnext] at hcheb
          simp only [chebyshevDistance] at hcheb
          have h1 : (c.y - ny.toInt).natAbs ≤ 1 := le_trans (le_max_right _ _) hcheb
          show ny.toInt.natAbs + n ≤ _
          omega

theorem coord_agree (f : Float) (b : Binary32) (hw : ExecFloat.Binary.ofFloat f = widen32To64 b)
    (hb : binary32IsFinite b = true) :
    Agree f (widen32To64 b) ∧ breal (widen32To64 b) = ((binary32ToRat b : ℚ) : ℝ) := by
  have hfin := widen32To64_isFinite b hb
  refine ⟨⟨?_, hfin, by unfold nreal; rw [hw]; rfl⟩, ?_⟩
  · rw [← ofFloat_isFinite, hw]; exact hfin
  · unfold breal; rw [widen32To64_toReal_eq b hb, toReal_eq_cast_toRat b hb]

theorem floor_natAbs_le (q : ℚ) (hq : |q| ≤ 2 ^ 28) : (toInt q).natAbs ≤ 2 ^ 28 := by
  obtain ⟨h1, h2⟩ := abs_le.mp hq
  have hlo : (-(2 : ℤ) ^ 28) ≤ toInt q := le_floor_of_le _ q (by push_cast; linarith)
  have hhi : toInt q ≤ 2 ^ 28 := by
    have := Rat.floor_le q
    have : ((toInt q : ℤ) : ℚ) ≤ 2 ^ 28 := by unfold toInt; linarith
    exact_mod_cast this
  omega

theorem absInt_toNat (x : Int32) (hx : -2 ^ 31 < x.toInt) : (absInt x).toNat = x.toInt.natAbs := by
  have hlt := Int32.toInt_lt x
  unfold absInt
  split
  · rename_i hneg
    have hneg' : x.toInt < 0 := by simpa [Int32.lt_iff_toInt_lt] using hneg
    have hn : (-x).toInt = -x.toInt := by
      rw [Int32.toInt_neg]; exact Int.bmod_eq_of_le (by omega) (by omega)
    have h0 : (0 : Int32) ≤ -x := by rw [Int32.le_iff_toInt_le, hn]; simp; omega
    rw [Int32.toNat_toUInt32_of_le h0, ← Int32.toNat_toInt, hn]
    omega
  · rename_i hnn
    have hnn' : (0 : Int32) ≤ x := by
      rw [Int32.le_iff_toInt_le]; simp [Int32.lt_iff_toInt_lt] at hnn; simpa using hnn
    rw [Int32.toNat_toUInt32_of_le hnn', ← Int32.toNat_toInt]
    have : 0 ≤ x.toInt := by simpa [Int32.le_iff_toInt_le] using hnn'
    omega

/--
The compiled ray march returns exactly the cells of the float model, up to duplicates.
-/
theorem rayMarchSegmentCoords_refines_Impl (A B : Point32) (sx sy ex ey : Float)
    (cx cy ex' ey' : Int32) (hPre : InRange A B sx sy ex ey cx cy ex' ey') :
    dedupCells (toCells (rayMarchSegmentCoords sx sy ex ey cx cy ex' ey')) =
      cellIntersectionsSegmentFloat A B := by
  obtain ⟨⟨hfA, hfB⟩, ⟨hAx, hAy, hBx, hBy⟩, ⟨hwsx, hwsy, hwex, hwey⟩, hstart, hend⟩ := hPre
  have hcb : compiledCoordBound = 2 ^ 28 := rfl
  rw [hcb] at hAx hAy hBx hBy
  obtain ⟨asx, rsx⟩ := coord_agree sx A.x hwsx hfA.1
  obtain ⟨asy, rsy⟩ := coord_agree sy A.y hwsy hfA.2
  obtain ⟨aex, rex⟩ := coord_agree ex B.x hwex hfB.1
  obtain ⟨aey, rey⟩ := coord_agree ey B.y hwey hfB.2
  have bAx : |breal (widen32To64 A.x)| ≤ 2 ^ 28 := by rw [rsx]; exact_mod_cast hAx
  have bAy : |breal (widen32To64 A.y)| ≤ 2 ^ 28 := by rw [rsy]; exact_mod_cast hAy
  have bBx : |breal (widen32To64 B.x)| ≤ 2 ^ 28 := by rw [rex]; exact_mod_cast hBx
  have bBy : |breal (widen32To64 B.y)| ≤ 2 ^ 28 := by rw [rey]; exact_mod_cast hBy
  have hmax := two_pow_62_le_posMaxFinite
  have hsum : (2 : ℝ) ^ 28 + 2 ^ 28 ≤ Model.toReal (Model.posMaxFinite FloatFormat.binary64) := by
    norm_num at hmax ⊢; linarith
  obtain ⟨adx, rdx⟩ := Agree.sub aex asx (by linarith)
  obtain ⟨ady, rdy⟩ := Agree.sub aey asy (by linarith)
  obtain ⟨aadx, radx⟩ := Agree.absFloat adx
  obtain ⟨aady, rady⟩ := Agree.absFloat ady
  have hmain : (mainCoordBoundNat : ℤ) + 2 = 2 ^ 31 - 1 := by decide
  have bdx : |breal (ExecFloat.Binary.abs (widen32To64 B.x - widen32To64 A.x))| ≤ 2 ^ 30 := by
    rw [radx, abs_abs, rdx]
    have h := abs_roundAt_le (breal (widen32To64 B.x) - breal (widen32To64 A.x)) (2 ^ 29)
      (by norm_num) (by rw [hmain]; norm_num)
      (by push_cast; linarith [abs_sub (breal (widen32To64 B.x)) (breal (widen32To64 A.x))])
    push_cast at h
    linarith
  have bdy : |breal (ExecFloat.Binary.abs (widen32To64 B.y - widen32To64 A.y))| ≤ 2 ^ 30 := by
    rw [rady, abs_abs, rdy]
    have h := abs_roundAt_le (breal (widen32To64 B.y) - breal (widen32To64 A.y)) (2 ^ 29)
      (by norm_num) (by rw [hmain]; norm_num)
      (by push_cast; linarith [abs_sub (breal (widen32To64 B.y)) (breal (widen32To64 A.y))])
    push_cast at h
    linarith
  -- the step directions agree
  have hstep (dN : Float) (dB : Binary64) (h : Agree dN dB) :
      (if dN > 0.0 then (1 : Int32) else if dN < 0.0 then -1 else 0).toInt =
        (if dB > 0.0 then (1 : ℤ) else if dB < 0.0 then -1 else 0) := by
    have hgt : dN > 0.0 ↔ dB > 0.0 := Agree.lt_iff Agree.zero h
    have hlt : dN < 0.0 ↔ dB < 0.0 := Agree.lt_iff h Agree.zero
    by_cases h1 : dB > 0.0
    · simp only [hgt.mpr h1, h1, ↓reduceIte]; rfl
    · have h1' : ¬ dN > 0.0 := fun h' => h1 (hgt.mp h')
      by_cases h2 : dB < 0.0
      · simp only [h1', h1, hlt.mpr h2, h2, ↓reduceIte]; rfl
      · have h2' : ¬ dN < 0.0 := fun h' => h2 (hlt.mp h')
        simp only [h1', h1, h2', h2, ↓reduceIte]; rfl
  have hsrange (dB : Binary64) :
      (if dB > 0.0 then (1 : ℤ) else if dB < 0.0 then -1 else 0) = -1 ∨
      (if dB > 0.0 then (1 : ℤ) else if dB < 0.0 then -1 else 0) = 0 ∨
      (if dB > 0.0 then (1 : ℤ) else if dB < 0.0 then -1 else 0) = 1 := by
    split_ifs <;> simp
  have ctx : MarchCtx A (deltaX A B) (deltaY A B)
      (if deltaX A B > 0.0 then 1 else if deltaX A B < 0.0 then -1 else 0)
      (if deltaY A B > 0.0 then 1 else if deltaY A B < 0.0 then -1 else 0)
      sx sy (absFloat (ex - sx)) (absFloat (ey - sy))
      (if ex - sx > 0.0 then 1 else if ex - sx < 0.0 then -1 else 0)
      (if ey - sy > 0.0 then 1 else if ey - sy < 0.0 then -1 else 0) :=
    { hsx := asx, hsy := asy, hadx := aadx, hady := aady
      hstepX := hstep _ _ adx, hstepY := hstep _ _ ady
      hsX := hsrange _, hsY := hsrange _
      hAx := bAx, hAy := bAy, hdx := bdx, hdy := bdy }
  -- the endpoint cells
  have hfloorA := floorPoint32_eq_floorPoint A hfA
  have hfloorB := floorPoint32_eq_floorPoint B hfB
  have hcxb : cx.toInt.natAbs ≤ 2 ^ 28 := by
    have := congrArg Cell.x hstart; rw [hfloorA] at this; simp only at this
    rw [this]; exact floor_natAbs_le _ hAx
  have hcyb : cy.toInt.natAbs ≤ 2 ^ 28 := by
    have := congrArg Cell.y hstart; rw [hfloorA] at this; simp only at this
    rw [this]; exact floor_natAbs_le _ hAy
  have hexb : ex'.toInt.natAbs ≤ 2 ^ 28 := by
    have := congrArg Cell.x hend; rw [hfloorB] at this; simp only at this
    rw [this]; exact floor_natAbs_le _ hBx
  have heyb : ey'.toInt.natAbs ≤ 2 ^ 28 := by
    have := congrArg Cell.y hend; rw [hfloorB] at this; simp only at this
    rw [this]; exact floor_natAbs_le _ hBy
  unfold rayMarchSegmentCoords cellIntersectionsSegmentFloat
  rw [end_beq cx cy ex' ey' (floorPoint32 A) (floorPoint32 B)
    (by rw [← hstart]) (by rw [← hstart]) (by rw [← hend]) (by rw [← hend])]
  by_cases hsame : (floorPoint32 A == floorPoint32 B) = true
  · simp only [hsame, ↓reduceIte]
    rw [← hstart]
    rfl
  · simp only [hsame, Bool.false_eq_true, ↓reduceIte]
    have hAcx : (floorPoint32 A).x = cx.toInt := by rw [← hstart]
    have hAcy : (floorPoint32 A).y = cy.toInt := by rw [← hstart]
    have hBex : (floorPoint32 B).x = ex'.toInt := by rw [← hend]
    have hBey : (floorPoint32 B).y = ey'.toInt := by rw [← hend]
    have hsubX : (ex' - cx).toInt = ex'.toInt - cx.toInt := by
      rw [Int32.toInt_sub]; exact Int.bmod_eq_of_le (by omega) (by omega)
    have hsubY : (ey' - cy).toInt = ey'.toInt - cy.toInt := by
      rw [Int32.toInt_sub]; exact Int.bmod_eq_of_le (by omega) (by omega)
    have hsz : UInt32.size = 2 ^ 32 := rfl
    have hNlt : ((floorPoint32 B).x - (floorPoint32 A).x).natAbs +
        ((floorPoint32 B).y - (floorPoint32 A).y).natAbs + 2 < 2 ^ 32 := by
      rw [hAcx, hAcy, hBex, hBey]; omega
    have hN : absInt (ex' - cx) + absInt (ey' - cy) + 2 =
        UInt32.ofNat (((floorPoint32 B).x - (floorPoint32 A).x).natAbs +
          ((floorPoint32 B).y - (floorPoint32 A).y).natAbs + 2) := by
      apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_ofNat_of_lt' (by rw [hsz]; exact hNlt), UInt32.toNat_add, UInt32.toNat_add,
        absInt_toNat _ (by rw [hsubX]; omega), absInt_toNat _ (by rw [hsubY]; omega), hsubX, hsubY,
        hAcx, hAcy, hBex, hBey]
      simp only [UInt32.toNat_ofNat]
      omega
    rw [hN, rayMarchLoop_refines ctx hBex.symm hBey.symm _ (floorPoint32 A) cx cy _ hNlt
      hAcx.symm hAcy.symm (by rw [hAcx, hAcy, hBex, hBey]; omega) (by rw [hAcx, hAcy, hBex, hBey]; omega),
      rayMarchFloat_acc]
    have hacc : toCells #[(cx, cy), (ex', ey')] = [floorPoint32 A, floorPoint32 B] := by
      rw [← hstart, ← hend]; rfl
    rw [hacc]

end Geometry
