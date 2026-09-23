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
import Geometry.LineSegment
import Geometry.Interval
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Geometry

/-!
# Part 3: Abstract rayMarch reachability induction
-/

lemma rayMarch_reaches_target (fuel : Nat) (start ptEnd : Point) (dx dy : Rat) (stepX stepY : Int)
    (endCell : Cell) (x : Cell) (D : Cell → Nat)
    (h_step : ∀ c, D c > 0 →
      (c == endCell) = false ∧
      (rayMarchStep start ptEnd dx dy stepX stepY c).2 = false ∧
      ( (rayMarchStep start ptEnd dx dy stepX stepY c).1 = x ∨
        (D (rayMarchStep start ptEnd dx dy stepX stepY c).1 < D c ∧ D (rayMarchStep start ptEnd dx dy stepX stepY c).1 > 0) )) :
    ∀ current, D current > 0 → D current ≤ fuel →
      x ∈ rayMarch fuel start ptEnd dx dy stepX stepY endCell current [] := by
  induction fuel with
  | zero =>
    intro current h_pos h_le
    omega
  | succ fuel ih =>
    intro current h_pos h_le
    rcases h_step current h_pos with ⟨h_not_end, h_not_done, h_next⟩
    rw [rayMarch_succ]
    rw [h_not_end]
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases h_done : (rayMarchStep start ptEnd dx dy stepX stepY current).2
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [List.mem_cons]
      rcases h_next with rfl | ⟨h_lt, h_next_pos⟩
      · exact Or.inl rfl
      · refine Or.inr ?_
        have h_next_le : D (rayMarchStep start ptEnd dx dy stepX stepY current).1 ≤ fuel := by omega
        exact ih (rayMarchStep start ptEnd dx dy stepX stepY current).1 h_next_pos h_next_le
    · rw [h_done] at h_not_done
      contradiction



/-!
# Part 4: rayMarchStep possible outputs
-/

theorem rayMarchStep_mem (start ptEnd : Point) (dx dy : Rat) (stepX stepY : Int) (c : Cell) :
    let S : List (Cell × Bool) :=
      [(c, true), (⟨c.x + stepX, c.y⟩, false), (⟨c.x, c.y + stepY⟩, false), (⟨c.x + stepX, c.y + stepY⟩, false)]
    rayMarchStep start ptEnd dx dy stepX stepY c ∈ S := by
  intro S
  unfold rayMarchStep
  dsimp only []
  have h_in1 : (c, true) ∈ S := by simp [S]
  have h_in2 : (⟨c.x + stepX, c.y⟩, false) ∈ S := by simp [S]
  have h_in3 : (⟨c.x, c.y + stepY⟩, false) ∈ S := by simp [S]
  have h_in4 : (⟨c.x + stepX, c.y + stepY⟩, false) ∈ S := by simp [S]
  by_cases hx0 : stepX == 0
  · simp only [hx0, ite_true]
    by_cases hremY : (if (if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ start.y then
        (if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) - start.y
      else start.y - if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ (if dy ≥ 0 then dy else -dy)
    · simp only [hremY, ite_true]; exact h_in1
    · simp only [hremY, ite_false]; exact h_in3
  · simp only [hx0]
    by_cases hy0 : stepY == 0
    · simp only [hy0, ite_true]
      by_cases hremX : (if (if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ start.x then
          (if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) - start.x
        else start.x - if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ (if dx ≥ 0 then dx else -dx)
      · simp only [hremX, ite_true]; exact h_in1
      · simp only [hremX, ite_false]; exact h_in2
    · simp only [hy0]
      by_cases hlim : min
            ((if (if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ start.x then
                (if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) - start.x
              else start.x - if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) *
              if dy ≥ 0 then dy else -dy)
            ((if (if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ start.y then
                (if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) - start.y
              else start.y - if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) *
              if dx ≥ 0 then dx else -dx) ≥
          (if dx ≥ 0 then dx else -dx) * if dy ≥ 0 then dy else -dy
      · simp only [hlim, ite_true]; exact h_in1
      · simp only [hlim, ite_false]
        by_cases hxy : ((if (if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ start.x then
                (if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) - start.x
              else start.x - if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) *
              if dy ≥ 0 then dy else -dy) <
            (if (if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ start.y then
                (if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) - start.y
              else start.y - if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) *
              if dx ≥ 0 then dx else -dx
        · simp only [hxy, ite_true]; exact h_in2
        · simp only [hxy, ite_false]
          by_cases hyx : ((if (if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ start.y then
                  (if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) - start.y
                else start.y - if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) *
                if dx ≥ 0 then dx else -dx) <
              (if (if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ start.x then
                  (if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) - start.x
                else start.x - if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) *
                if dy ≥ 0 then dy else -dy
          · simp only [hyx, ite_true]; exact h_in3
          · simp only [hyx, ite_false]; exact h_in4

theorem rayMarchStep_fst_cases (start ptEnd : Point) (dx dy : Rat) (stepX stepY : Int) (c : Cell)
    (h_not_done : (rayMarchStep start ptEnd dx dy stepX stepY c).2 = false) :
    (rayMarchStep start ptEnd dx dy stepX stepY c).1 = ⟨c.x + stepX, c.y⟩ ∨
    (rayMarchStep start ptEnd dx dy stepX stepY c).1 = ⟨c.x, c.y + stepY⟩ ∨
    (rayMarchStep start ptEnd dx dy stepX stepY c).1 = ⟨c.x + stepX, c.y + stepY⟩ := by
  have h_mem := rayMarchStep_mem start ptEnd dx dy stepX stepY c
  dsimp only [] at h_mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h_mem
  rcases h_mem with h1 | h2 | h3 | h4
  · have : (rayMarchStep start ptEnd dx dy stepX stepY c).2 = true := by rw [h1]
    rw [this] at h_not_done
    contradiction
  · left
    exact congrArg Prod.fst h2
  · right; left
    exact congrArg Prod.fst h3
  · right; right
    exact congrArg Prod.fst h4




/-! # 1. crossY < crossX when cx = xx -/

theorem cross_pos_pos (cx cy xx xy : Int) (Ax Ay dx dy tEnter tExit : Rat)
    (hdx : 0 < dx) (hdy : 0 < dy)
    (h_enter_lt_exit : tEnter < tExit)
    (h_tx : (ofInt xx - Ax) / dx ≤ tEnter ∧ tExit ≤ (ofInt (xx + 1) - Ax) / dx)
    (h_ty : (ofInt xy - Ay) / dy ≤ tEnter ∧ tExit ≤ (ofInt (xy + 1) - Ay) / dy)
    (hcx : cx = xx) (hcy : cy + 1 ≤ xy) :
    let remX := ofInt (cx + 1) - Ax
    let remY := ofInt (cy + 1) - Ay
    remY * dx < remX * dy := by
  intro remX remY
  have h_remY_le : remY ≤ ofInt xy - Ay := by
    dsimp [remY, ofInt]
    have : ((cy + 1 : Int) : Rat) ≤ ((xy : Int) : Rat) := Int.cast_le.mpr hcy
    linarith
  have h_remX_ge : ofInt (xx + 1) - Ax ≤ remX := by
    dsimp [remX, ofInt]
    have : ((xx + 1 : Int) : Rat) = ((cx + 1 : Int) : Rat) := by rw [hcx]
    linarith
  have h1 : remY / dy ≤ (ofInt xy - Ay) / dy := div_le_div_of_nonneg_right h_remY_le (le_of_lt hdy)
  have h2 : (ofInt xy - Ay) / dy ≤ tEnter := h_ty.1
  have h3 : tEnter < tExit := h_enter_lt_exit
  have h4 : tExit ≤ (ofInt (xx + 1) - Ax) / dx := h_tx.2
  have h5 : (ofInt (xx + 1) - Ax) / dx ≤ remX / dx := div_le_div_of_nonneg_right h_remX_ge (le_of_lt hdx)
  have h_lt : remY / dy < remX / dx := by linarith
  have h_cross := (cross_lt_cross_iff_div_lt_div remY remX dy dx hdy hdx).mpr h_lt
  linarith

theorem cross_pos_neg (cx cy xx xy : Int) (Ax Ay dx dy tEnter tExit : Rat)
    (hdx : 0 < dx) (hdy : dy < 0)
    (h_enter_lt_exit : tEnter < tExit)
    (h_tx : (ofInt xx - Ax) / dx ≤ tEnter ∧ tExit ≤ (ofInt (xx + 1) - Ax) / dx)
    (h_ty : (ofInt (xy + 1) - Ay) / dy ≤ tEnter ∧ tExit ≤ (ofInt xy - Ay) / dy)
    (hcx : cx = xx) (hcy : xy + 1 ≤ cy) :
    let remX := ofInt (cx + 1) - Ax
    let remY := Ay - ofInt cy
    let absDy := -dy
    remY * dx < remX * absDy := by
  intro remX remY absDy
  have habsDy : 0 < absDy := by dsimp [absDy]; linarith
  have h_remY_le : remY ≤ Ay - ofInt (xy + 1) := by
    dsimp [remY, ofInt]
    have : ((xy + 1 : Int) : Rat) ≤ ((cy : Int) : Rat) := Int.cast_le.mpr hcy
    linarith
  have h1 : remY / absDy ≤ (Ay - ofInt (xy + 1)) / absDy :=
    div_le_div_of_nonneg_right h_remY_le (le_of_lt habsDy)
  have h_eq : (Ay - ofInt (xy + 1)) / absDy = (ofInt (xy + 1) - Ay) / dy := by
    dsimp [absDy]
    have : Ay - ofInt (xy + 1) = -(ofInt (xy + 1) - Ay) := by ring
    rw [this, neg_div, div_neg, neg_neg]
  have h2 : (Ay - ofInt (xy + 1)) / absDy ≤ tEnter := by rw [h_eq]; exact h_ty.1
  have h3 : tEnter < tExit := h_enter_lt_exit
  have h4 : tExit ≤ (ofInt (xx + 1) - Ax) / dx := h_tx.2
  have h_remX_ge : ofInt (xx + 1) - Ax ≤ remX := by
    dsimp [remX, ofInt]
    have : ((xx + 1 : Int) : Rat) = ((cx + 1 : Int) : Rat) := by rw [hcx]
    linarith
  have h5 : (ofInt (xx + 1) - Ax) / dx ≤ remX / dx := div_le_div_of_nonneg_right h_remX_ge (le_of_lt hdx)
  have h_lt : remY / absDy < remX / dx := by linarith
  have h_cross := (cross_lt_cross_iff_div_lt_div remY remX absDy dx habsDy hdx).mpr h_lt
  linarith

theorem cross_neg_pos (cx cy xx xy : Int) (Ax Ay dx dy tEnter tExit : Rat)
    (hdx : dx < 0) (hdy : 0 < dy)
    (h_enter_lt_exit : tEnter < tExit)
    (h_tx : (ofInt (xx + 1) - Ax) / dx ≤ tEnter ∧ tExit ≤ (ofInt xx - Ax) / dx)
    (h_ty : (ofInt xy - Ay) / dy ≤ tEnter ∧ tExit ≤ (ofInt (xy + 1) - Ay) / dy)
    (hcx : cx = xx) (hcy : cy + 1 ≤ xy) :
    let remX := Ax - ofInt cx
    let remY := ofInt (cy + 1) - Ay
    let absDx := -dx
    remY * absDx < remX * dy := by
  intro remX remY absDx
  have habsDx : 0 < absDx := by dsimp [absDx]; linarith
  have h_remY_le : remY ≤ ofInt xy - Ay := by
    dsimp [remY, ofInt]
    have : ((cy + 1 : Int) : Rat) ≤ ((xy : Int) : Rat) := Int.cast_le.mpr hcy
    linarith
  have h1 : remY / dy ≤ (ofInt xy - Ay) / dy :=
    div_le_div_of_nonneg_right h_remY_le (le_of_lt hdy)
  have h2 : (ofInt xy - Ay) / dy ≤ tEnter := h_ty.1
  have h3 : tEnter < tExit := h_enter_lt_exit
  have h4 : tExit ≤ (ofInt xx - Ax) / dx := h_tx.2
  have h_remX_eq : remX / absDx = (ofInt xx - Ax) / dx := by
    dsimp [remX, absDx]
    rw [hcx]
    have : Ax - ofInt xx = -(ofInt xx - Ax) := by ring
    rw [this, neg_div, div_neg, neg_neg]
  have h5 : tExit ≤ remX / absDx := by rw [h_remX_eq]; exact h4
  have h_lt : remY / dy < remX / absDx := by linarith
  have h_cross := (cross_lt_cross_iff_div_lt_div remY remX dy absDx hdy habsDx).mpr h_lt
  linarith

theorem cross_neg_neg (cx cy xx xy : Int) (Ax Ay dx dy tEnter tExit : Rat)
    (hdx : dx < 0) (hdy : dy < 0)
    (h_enter_lt_exit : tEnter < tExit)
    (h_tx : (ofInt (xx + 1) - Ax) / dx ≤ tEnter ∧ tExit ≤ (ofInt xx - Ax) / dx)
    (h_ty : (ofInt (xy + 1) - Ay) / dy ≤ tEnter ∧ tExit ≤ (ofInt xy - Ay) / dy)
    (hcx : cx = xx) (hcy : xy + 1 ≤ cy) :
    let remX := Ax - ofInt cx
    let remY := Ay - ofInt cy
    let absDx := -dx
    let absDy := -dy
    remY * absDx < remX * absDy := by
  intro remX remY absDx absDy
  have habsDx : 0 < absDx := by dsimp [absDx]; linarith
  have habsDy : 0 < absDy := by dsimp [absDy]; linarith
  have h_remY_le : remY ≤ Ay - ofInt (xy + 1) := by
    dsimp [remY, ofInt]
    have : ((xy + 1 : Int) : Rat) ≤ ((cy : Int) : Rat) := Int.cast_le.mpr hcy
    linarith
  have h1 : remY / absDy ≤ (Ay - ofInt (xy + 1)) / absDy :=
    div_le_div_of_nonneg_right h_remY_le (le_of_lt habsDy)
  have h_eqY : (Ay - ofInt (xy + 1)) / absDy = (ofInt (xy + 1) - Ay) / dy := by
    dsimp [absDy]
    have : Ay - ofInt (xy + 1) = -(ofInt (xy + 1) - Ay) := by ring
    rw [this, neg_div, div_neg, neg_neg]
  have h2 : (Ay - ofInt (xy + 1)) / absDy ≤ tEnter := by rw [h_eqY]; exact h_ty.1
  have h3 : tEnter < tExit := h_enter_lt_exit
  have h4 : tExit ≤ (ofInt xx - Ax) / dx := h_tx.2
  have h_eqX : remX / absDx = (ofInt xx - Ax) / dx := by
    dsimp [remX, absDx]
    rw [hcx]
    have : Ax - ofInt xx = -(ofInt xx - Ax) := by ring
    rw [this, neg_div, div_neg, neg_neg]
  have h5 : tExit ≤ remX / absDx := by rw [h_eqX]; exact h4
  have h_lt : remY / absDy < remX / absDx := by linarith
  have h_cross := (cross_lt_cross_iff_div_lt_div remY remX absDy absDx habsDy habsDx).mpr h_lt
  linarith

/-! # 2. crossX < crossY when cy = xy -/

theorem cross_ge_pos_pos (cx cy xx xy : Int) (Ax Ay dx dy tEnter tExit : Rat)
    (hdx : 0 < dx) (hdy : 0 < dy)
    (h_enter_lt_exit : tEnter < tExit)
    (h_tx : (ofInt xx - Ax) / dx ≤ tEnter ∧ tExit ≤ (ofInt (xx + 1) - Ax) / dx)
    (h_ty : (ofInt xy - Ay) / dy ≤ tEnter ∧ tExit ≤ (ofInt (xy + 1) - Ay) / dy)
    (hcy : cy = xy) (hcx : cx + 1 ≤ xx) :
    let remX := ofInt (cx + 1) - Ax
    let remY := ofInt (cy + 1) - Ay
    remX * dy < remY * dx := by
  intro remX remY
  have h_remX_le : remX ≤ ofInt xx - Ax := by
    dsimp [remX, ofInt]
    have : ((cx + 1 : Int) : Rat) ≤ ((xx : Int) : Rat) := Int.cast_le.mpr hcx
    linarith
  have h_remY_ge : ofInt (xy + 1) - Ay ≤ remY := by
    dsimp [remY, ofInt]
    have : ((xy + 1 : Int) : Rat) = ((cy + 1 : Int) : Rat) := by rw [hcy]
    linarith
  have h1 : remX / dx ≤ (ofInt xx - Ax) / dx := div_le_div_of_nonneg_right h_remX_le (le_of_lt hdx)
  have h2 : (ofInt xx - Ax) / dx ≤ tEnter := h_tx.1
  have h3 : tEnter < tExit := h_enter_lt_exit
  have h4 : tExit ≤ (ofInt (xy + 1) - Ay) / dy := h_ty.2
  have h5 : (ofInt (xy + 1) - Ay) / dy ≤ remY / dy := div_le_div_of_nonneg_right h_remY_ge (le_of_lt hdy)
  have h_lt : remX / dx < remY / dy := by linarith
  have h_cross := (cross_lt_cross_iff_div_lt_div remX remY dx dy hdx hdy).mpr h_lt
  linarith

theorem cross_ge_pos_neg (cx cy xx xy : Int) (Ax Ay dx dy tEnter tExit : Rat)
    (hdx : 0 < dx) (hdy : dy < 0)
    (h_enter_lt_exit : tEnter < tExit)
    (h_tx : (ofInt xx - Ax) / dx ≤ tEnter ∧ tExit ≤ (ofInt (xx + 1) - Ax) / dx)
    (h_ty : (ofInt (xy + 1) - Ay) / dy ≤ tEnter ∧ tExit ≤ (ofInt xy - Ay) / dy)
    (hcy : cy = xy) (hcx : cx + 1 ≤ xx) :
    let remX := ofInt (cx + 1) - Ax
    let remY := Ay - ofInt cy
    let absDy := -dy
    remX * absDy < remY * dx := by
  intro remX remY absDy
  have habsDy : 0 < absDy := by dsimp [absDy]; linarith
  have h_remX_le : remX ≤ ofInt xx - Ax := by
    dsimp [remX, ofInt]
    have : ((cx + 1 : Int) : Rat) ≤ ((xx : Int) : Rat) := Int.cast_le.mpr hcx
    linarith
  have h1 : remX / dx ≤ (ofInt xx - Ax) / dx := div_le_div_of_nonneg_right h_remX_le (le_of_lt hdx)
  have h2 : (ofInt xx - Ax) / dx ≤ tEnter := h_tx.1
  have h3 : tEnter < tExit := h_enter_lt_exit
  have h4 : tExit ≤ (ofInt xy - Ay) / dy := h_ty.2
  have h_eqY : remY / absDy = (ofInt xy - Ay) / dy := by
    dsimp [remY, absDy]
    rw [hcy]
    have : Ay - ofInt xy = -(ofInt xy - Ay) := by ring
    rw [this, neg_div, div_neg, neg_neg]
  have h5 : tExit ≤ remY / absDy := by rw [h_eqY]; exact h4
  have h_lt : remX / dx < remY / absDy := by linarith
  have h_cross := (cross_lt_cross_iff_div_lt_div remX remY dx absDy hdx habsDy).mpr h_lt
  linarith

theorem cross_ge_neg_pos (cx cy xx xy : Int) (Ax Ay dx dy tEnter tExit : Rat)
    (hdx : dx < 0) (hdy : 0 < dy)
    (h_enter_lt_exit : tEnter < tExit)
    (h_tx : (ofInt (xx + 1) - Ax) / dx ≤ tEnter ∧ tExit ≤ (ofInt xx - Ax) / dx)
    (h_ty : (ofInt xy - Ay) / dy ≤ tEnter ∧ tExit ≤ (ofInt (xy + 1) - Ay) / dy)
    (hcy : cy = xy) (hcx : xx + 1 ≤ cx) :
    let remX := Ax - ofInt cx
    let remY := ofInt (cy + 1) - Ay
    let absDx := -dx
    remX * dy < remY * absDx := by
  intro remX remY absDx
  have habsDx : 0 < absDx := by dsimp [absDx]; linarith
  have h_remX_le : remX ≤ Ax - ofInt (xx + 1) := by
    dsimp [remX, ofInt]
    have : ((xx + 1 : Int) : Rat) ≤ ((cx : Int) : Rat) := Int.cast_le.mpr hcx
    linarith
  have h1 : remX / absDx ≤ (Ax - ofInt (xx + 1)) / absDx :=
    div_le_div_of_nonneg_right h_remX_le (le_of_lt habsDx)
  have h_eqX : (Ax - ofInt (xx + 1)) / absDx = (ofInt (xx + 1) - Ax) / dx := by
    dsimp [absDx]
    have : Ax - ofInt (xx + 1) = -(ofInt (xx + 1) - Ax) := by ring
    rw [this, neg_div, div_neg, neg_neg]
  have h2 : (Ax - ofInt (xx + 1)) / absDx ≤ tEnter := by rw [h_eqX]; exact h_tx.1
  have h3 : tEnter < tExit := h_enter_lt_exit
  have h4 : tExit ≤ (ofInt (xy + 1) - Ay) / dy := h_ty.2
  have h_remY_ge : ofInt (xy + 1) - Ay ≤ remY := by
    dsimp [remY, ofInt]
    have : ((xy + 1 : Int) : Rat) = ((cy + 1 : Int) : Rat) := by rw [hcy]
    linarith
  have h5 : (ofInt (xy + 1) - Ay) / dy ≤ remY / dy := div_le_div_of_nonneg_right h_remY_ge (le_of_lt hdy)
  have h_lt : remX / absDx < remY / dy := by linarith
  have h_cross := (cross_lt_cross_iff_div_lt_div remX remY absDx dy habsDx hdy).mpr h_lt
  linarith

theorem cross_ge_neg_neg (cx cy xx xy : Int) (Ax Ay dx dy tEnter tExit : Rat)
    (hdx : dx < 0) (hdy : dy < 0)
    (h_enter_lt_exit : tEnter < tExit)
    (h_tx : (ofInt (xx + 1) - Ax) / dx ≤ tEnter ∧ tExit ≤ (ofInt xx - Ax) / dx)
    (h_ty : (ofInt (xy + 1) - Ay) / dy ≤ tEnter ∧ tExit ≤ (ofInt xy - Ay) / dy)
    (hcy : cy = xy) (hcx : xx + 1 ≤ cx) :
    let remX := Ax - ofInt cx
    let remY := Ay - ofInt cy
    let absDx := -dx
    let absDy := -dy
    remX * absDy < remY * absDx := by
  intro remX remY absDx absDy
  have habsDx : 0 < absDx := by dsimp [absDx]; linarith
  have habsDy : 0 < absDy := by dsimp [absDy]; linarith
  have h_remX_le : remX ≤ Ax - ofInt (xx + 1) := by
    dsimp [remX, ofInt]
    have : ((xx + 1 : Int) : Rat) ≤ ((cx : Int) : Rat) := Int.cast_le.mpr hcx
    linarith
  have h1 : remX / absDx ≤ (Ax - ofInt (xx + 1)) / absDx :=
    div_le_div_of_nonneg_right h_remX_le (le_of_lt habsDx)
  have h_eqX : (Ax - ofInt (xx + 1)) / absDx = (ofInt (xx + 1) - Ax) / dx := by
    dsimp [absDx]
    have : Ax - ofInt (xx + 1) = -(ofInt (xx + 1) - Ax) := by ring
    rw [this, neg_div, div_neg, neg_neg]
  have h2 : (Ax - ofInt (xx + 1)) / absDx ≤ tEnter := by rw [h_eqX]; exact h_tx.1
  have h3 : tEnter < tExit := h_enter_lt_exit
  have h4 : tExit ≤ (ofInt xy - Ay) / dy := h_ty.2
  have h_eqY : remY / absDy = (ofInt xy - Ay) / dy := by
    dsimp [remY, absDy]
    rw [hcy]
    have : Ay - ofInt xy = -(ofInt xy - Ay) := by ring
    rw [this, neg_div, div_neg, neg_neg]
  have h5 : tExit ≤ remY / absDy := by rw [h_eqY]; exact h4
  have h_lt : remX / absDx < remY / absDy := by linarith
  have h_cross := (cross_lt_cross_iff_div_lt_div remX remY absDx absDy habsDx habsDy).mpr h_lt
  linarith


/-! # 3. min crossX crossY < limitCross when cx not reached or cy not reached -/

theorem min_cross_lt_limit_pos_pos (cx cy xx xy : Int) (Ax Ay dx dy tEnter tExit : Rat)
    (hdx : 0 < dx) (hdy : 0 < dy)
    (h_enter_lt_exit : tEnter < tExit)
    (h_exit_le_one : tExit ≤ 1)
    (h_tx : (ofInt xx - Ax) / dx ≤ tEnter ∧ tExit ≤ (ofInt (xx + 1) - Ax) / dx)
    (h_ty : (ofInt xy - Ay) / dy ≤ tEnter ∧ tExit ≤ (ofInt (xy + 1) - Ay) / dy)
    (h_cases : cx + 1 ≤ xx ∨ cy + 1 ≤ xy) :
    let remX := ofInt (cx + 1) - Ax
    let remY := ofInt (cy + 1) - Ay
    min (remX * dy) (remY * dx) < dx * dy := by
  intro remX remY
  rw [min_cross_lt_limit_iff remX remY dx dy hdx hdy]
  rcases h_cases with hcx | hcy
  · left
    have h_remX_le : remX ≤ ofInt xx - Ax := by
      dsimp [remX, ofInt]
      have : ((cx + 1 : Int) : Rat) ≤ ((xx : Int) : Rat) := Int.cast_le.mpr hcx
      linarith
    have h1 : remX / dx ≤ (ofInt xx - Ax) / dx := div_le_div_of_nonneg_right h_remX_le (le_of_lt hdx)
    have h2 : (ofInt xx - Ax) / dx ≤ tEnter := h_tx.1
    have h3 : tEnter < 1 := by linarith
    have : remX / dx < 1 := by linarith
    exact (div_lt_one hdx).mp this
  · right
    have h_remY_le : remY ≤ ofInt xy - Ay := by
      dsimp [remY, ofInt]
      have : ((cy + 1 : Int) : Rat) ≤ ((xy : Int) : Rat) := Int.cast_le.mpr hcy
      linarith
    have h1 : remY / dy ≤ (ofInt xy - Ay) / dy := div_le_div_of_nonneg_right h_remY_le (le_of_lt hdy)
    have h2 : (ofInt xy - Ay) / dy ≤ tEnter := h_ty.1
    have h3 : tEnter < 1 := by linarith
    have : remY / dy < 1 := by linarith
    exact (div_lt_one hdy).mp this

theorem min_cross_lt_limit_pos_neg (cx cy xx xy : Int) (Ax Ay dx dy tEnter tExit : Rat)
    (hdx : 0 < dx) (hdy : dy < 0)
    (h_enter_lt_exit : tEnter < tExit)
    (h_exit_le_one : tExit ≤ 1)
    (h_tx : (ofInt xx - Ax) / dx ≤ tEnter ∧ tExit ≤ (ofInt (xx + 1) - Ax) / dx)
    (h_ty : (ofInt (xy + 1) - Ay) / dy ≤ tEnter ∧ tExit ≤ (ofInt xy - Ay) / dy)
    (h_cases : cx + 1 ≤ xx ∨ xy + 1 ≤ cy) :
    let remX := ofInt (cx + 1) - Ax
    let remY := Ay - ofInt cy
    let absDy := -dy
    min (remX * absDy) (remY * dx) < dx * absDy := by
  intro remX remY absDy
  have habsDy : 0 < absDy := by dsimp [absDy]; linarith
  rw [min_cross_lt_limit_iff remX remY dx absDy hdx habsDy]
  rcases h_cases with hcx | hcy
  · left
    have h_remX_le : remX ≤ ofInt xx - Ax := by
      dsimp [remX, ofInt]
      have : ((cx + 1 : Int) : Rat) ≤ ((xx : Int) : Rat) := Int.cast_le.mpr hcx
      linarith
    have h1 : remX / dx ≤ (ofInt xx - Ax) / dx := div_le_div_of_nonneg_right h_remX_le (le_of_lt hdx)
    have h2 : (ofInt xx - Ax) / dx ≤ tEnter := h_tx.1
    have h3 : tEnter < 1 := by linarith
    have : remX / dx < 1 := by linarith
    exact (div_lt_one hdx).mp this
  · right
    have h_remY_le : remY ≤ Ay - ofInt (xy + 1) := by
      dsimp [remY, ofInt]
      have : ((xy + 1 : Int) : Rat) ≤ ((cy : Int) : Rat) := Int.cast_le.mpr hcy
      linarith
    have h1 : remY / absDy ≤ (Ay - ofInt (xy + 1)) / absDy :=
      div_le_div_of_nonneg_right h_remY_le (le_of_lt habsDy)
    have h_eq : (Ay - ofInt (xy + 1)) / absDy = (ofInt (xy + 1) - Ay) / dy := by
      dsimp [absDy]
      have : Ay - ofInt (xy + 1) = -(ofInt (xy + 1) - Ay) := by ring
      rw [this, neg_div, div_neg, neg_neg]
    have h2 : (Ay - ofInt (xy + 1)) / absDy ≤ tEnter := by rw [h_eq]; exact h_ty.1
    have h3 : tEnter < 1 := by linarith
    have : remY / absDy < 1 := by linarith
    exact (div_lt_one habsDy).mp this

theorem min_cross_lt_limit_neg_pos (cx cy xx xy : Int) (Ax Ay dx dy tEnter tExit : Rat)
    (hdx : dx < 0) (hdy : 0 < dy)
    (h_enter_lt_exit : tEnter < tExit)
    (h_exit_le_one : tExit ≤ 1)
    (h_tx : (ofInt (xx + 1) - Ax) / dx ≤ tEnter ∧ tExit ≤ (ofInt xx - Ax) / dx)
    (h_ty : (ofInt xy - Ay) / dy ≤ tEnter ∧ tExit ≤ (ofInt (xy + 1) - Ay) / dy)
    (h_cases : xx + 1 ≤ cx ∨ cy + 1 ≤ xy) :
    let remX := Ax - ofInt cx
    let remY := ofInt (cy + 1) - Ay
    let absDx := -dx
    min (remX * dy) (remY * absDx) < absDx * dy := by
  intro remX remY absDx
  have habsDx : 0 < absDx := by dsimp [absDx]; linarith
  rw [min_cross_lt_limit_iff remX remY absDx dy habsDx hdy]
  rcases h_cases with hcx | hcy
  · left
    have h_remX_le : remX ≤ Ax - ofInt (xx + 1) := by
      dsimp [remX, ofInt]
      have : ((xx + 1 : Int) : Rat) ≤ ((cx : Int) : Rat) := Int.cast_le.mpr hcx
      linarith
    have h1 : remX / absDx ≤ (Ax - ofInt (xx + 1)) / absDx :=
      div_le_div_of_nonneg_right h_remX_le (le_of_lt habsDx)
    have h_eq : (Ax - ofInt (xx + 1)) / absDx = (ofInt (xx + 1) - Ax) / dx := by
      dsimp [absDx]
      have : Ax - ofInt (xx + 1) = -(ofInt (xx + 1) - Ax) := by ring
      rw [this, neg_div, div_neg, neg_neg]
    have h2 : (Ax - ofInt (xx + 1)) / absDx ≤ tEnter := by rw [h_eq]; exact h_tx.1
    have h3 : tEnter < 1 := by linarith
    have : remX / absDx < 1 := by linarith
    exact (div_lt_one habsDx).mp this
  · right
    have h_remY_le : remY ≤ ofInt xy - Ay := by
      dsimp [remY, ofInt]
      have : ((cy + 1 : Int) : Rat) ≤ ((xy : Int) : Rat) := Int.cast_le.mpr hcy
      linarith
    have h1 : remY / dy ≤ (ofInt xy - Ay) / dy := div_le_div_of_nonneg_right h_remY_le (le_of_lt hdy)
    have h2 : (ofInt xy - Ay) / dy ≤ tEnter := h_ty.1
    have h3 : tEnter < 1 := by linarith
    have : remY / dy < 1 := by linarith
    exact (div_lt_one hdy).mp this

theorem min_cross_lt_limit_neg_neg (cx cy xx xy : Int) (Ax Ay dx dy tEnter tExit : Rat)
    (hdx : dx < 0) (hdy : dy < 0)
    (h_enter_lt_exit : tEnter < tExit)
    (h_exit_le_one : tExit ≤ 1)
    (h_tx : (ofInt (xx + 1) - Ax) / dx ≤ tEnter ∧ tExit ≤ (ofInt xx - Ax) / dx)
    (h_ty : (ofInt (xy + 1) - Ay) / dy ≤ tEnter ∧ tExit ≤ (ofInt xy - Ay) / dy)
    (h_cases : xx + 1 ≤ cx ∨ xy + 1 ≤ cy) :
    let remX := Ax - ofInt cx
    let remY := Ay - ofInt cy
    let absDx := -dx
    let absDy := -dy
    min (remX * absDy) (remY * absDx) < absDx * absDy := by
  intro remX remY absDx absDy
  have habsDx : 0 < absDx := by dsimp [absDx]; linarith
  have habsDy : 0 < absDy := by dsimp [absDy]; linarith
  rw [min_cross_lt_limit_iff remX remY absDx absDy habsDx habsDy]
  rcases h_cases with hcx | hcy
  · left
    have h_remX_le : remX ≤ Ax - ofInt (xx + 1) := by
      dsimp [remX, ofInt]
      have : ((xx + 1 : Int) : Rat) ≤ ((cx : Int) : Rat) := Int.cast_le.mpr hcx
      linarith
    have h1 : remX / absDx ≤ (Ax - ofInt (xx + 1)) / absDx :=
      div_le_div_of_nonneg_right h_remX_le (le_of_lt habsDx)
    have h_eq : (Ax - ofInt (xx + 1)) / absDx = (ofInt (xx + 1) - Ax) / dx := by
      dsimp [absDx]
      have : Ax - ofInt (xx + 1) = -(ofInt (xx + 1) - Ax) := by ring
      rw [this, neg_div, div_neg, neg_neg]
    have h2 : (Ax - ofInt (xx + 1)) / absDx ≤ tEnter := by rw [h_eq]; exact h_tx.1
    have h3 : tEnter < 1 := by linarith
    have : remX / absDx < 1 := by linarith
    exact (div_lt_one habsDx).mp this
  · right
    have h_remY_le : remY ≤ Ay - ofInt (xy + 1) := by
      dsimp [remY, ofInt]
      have : ((xy + 1 : Int) : Rat) ≤ ((cy : Int) : Rat) := Int.cast_le.mpr hcy
      linarith
    have h1 : remY / absDy ≤ (Ay - ofInt (xy + 1)) / absDy :=
      div_le_div_of_nonneg_right h_remY_le (le_of_lt habsDy)
    have h_eq : (Ay - ofInt (xy + 1)) / absDy = (ofInt (xy + 1) - Ay) / dy := by
      dsimp [absDy]
      have : Ay - ofInt (xy + 1) = -(ofInt (xy + 1) - Ay) := by ring
      rw [this, neg_div, div_neg, neg_neg]
    have h2 : (Ay - ofInt (xy + 1)) / absDy ≤ tEnter := by rw [h_eq]; exact h_ty.1
    have h3 : tEnter < 1 := by linarith
    have : remY / absDy < 1 := by linarith
    exact (div_lt_one habsDy).mp this


theorem rayMarchStep_sx_zero (A B : Point) (c : Cell)
    (dy : Rat) (stepY : Int) :
    let stepX : Int := 0
    let yb : Rat := if stepY > 0 then ofInt (c.y + 1) else ofInt c.y
    let absDy := if dy >= 0 then dy else -dy
    let remY := if yb >= A.y then yb - A.y else A.y - yb
    rayMarchStep A B 0 dy stepX stepY c =
      if remY >= absDy then (c, true)
      else (⟨c.x, c.y + stepY⟩, false) := by
  intro stepX yb absDy remY
  unfold rayMarchStep
  dsimp only []
  rfl

theorem step_sx_zero (A B : Point) (x c : Cell) (tEnter tExit : Rat)
    (hdx : B.x - A.x = 0) (hdy_ne : B.y - A.y ≠ 0)
    (h_enter_lt_exit : tEnter < tExit)
    (h_inter : cellIntersectionInterval x A B = some (tEnter, tExit))
    (h_cy_le : 0 ≤ (x.y - c.y) * if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0)
    (h_cy_ne : c.y ≠ x.y)
    (h_cA_y : 0 ≤ (c.y - (floorPoint A).y) * if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0) :
    let stepY : Int := if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0
    (rayMarchStep A B (B.x - A.x) (B.y - A.y) 0 stepY c) = (⟨c.x, c.y + stepY⟩, false) ∧
    (x.y - (c.y + stepY)) * stepY < (x.y - c.y) * stepY ∧
    0 ≤ (x.y - (c.y + stepY)) * stepY ∧
    0 ≤ (c.y + stepY - (floorPoint A).y) * stepY := by
  intro stepY
  have h_step := rayMarchStep_sx_zero A B c (B.y - A.y) stepY
  rw [hdx]
  dsimp only [] at h_step
  rw [h_step]
  have h_exit_le_one := (interval_enter_exit_le_one x A B tEnter tExit h_inter).2
  by_cases hdy_pos : B.y - A.y > 0
  · have hsy : stepY = 1 := by dsimp [stepY]; simp [hdy_pos]
    have h_absDy : (if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)) = B.y - A.y := by
      split_ifs with h <;> [rfl; linarith]
    have h_yb : (if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) = ofInt (c.y + 1) := by
      rw [hsy]; rfl
    have h_cA : (floorPoint A).y ≤ c.y := by
      have : 0 ≤ (c.y - (floorPoint A).y) * 1 := by rw [← hsy]; exact h_cA_y
      omega
    have h_cx_le : c.y + 1 ≤ x.y := by
      have : 0 ≤ (x.y - c.y) * 1 := by rw [← hsy]; exact h_cy_le
      omega
    have h_fl : (floorPoint A).y = toInt A.y := rfl
    have h_lt : A.y < ((floorPoint A).y : Rat) + 1 := by
      have := Rat.lt_floor_add_one A.y
      unfold toInt at h_fl
      rw [← h_fl] at this
      push_cast at this
      exact this
    have h_cast_cA : ((floorPoint A).y : Rat) ≤ (c.y : Rat) := Int.cast_le.mpr h_cA
    have h_ge : A.y < ofInt (c.y + 1) := by
      dsimp [ofInt]
      push_cast
      linarith
    have h_remY : (if (if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
        (if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
      else A.y - if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) = ofInt (c.y + 1) - A.y := by
      rw [h_yb]
      split_ifs with h <;> [rfl; linarith]
    have h_ty := interval_dy_pos x A B tEnter tExit h_inter hdy_pos
    have h_remY_le : ofInt (c.y + 1) - A.y ≤ ofInt x.y - A.y := by
      dsimp [ofInt]
      have : ((c.y + 1 : Int) : Rat) ≤ ((x.y : Int) : Rat) := Int.cast_le.mpr h_cx_le
      linarith
    have h1 : (ofInt (c.y + 1) - A.y) / (B.y - A.y) ≤ (ofInt x.y - A.y) / (B.y - A.y) :=
      div_le_div_of_nonneg_right h_remY_le (le_of_lt hdy_pos)
    have h2 : (ofInt (c.y + 1) - A.y) / (B.y - A.y) < 1 := by linarith [h1, h_ty.1, h_enter_lt_exit, h_exit_le_one]
    have h_remY_lt : ofInt (c.y + 1) - A.y < B.y - A.y := (div_lt_one hdy_pos).mp h2
    have h_not_ge : ¬(ofInt (c.y + 1) - A.y ≥ B.y - A.y) := by linarith
    rw [h_absDy, h_remY]
    simp only [ge_iff_le, h_not_ge, ↓reduceIte]
    refine ⟨trivial, ?_, ?_, ?_⟩
    · rw [hsy]; omega
    · rw [hsy]; omega
    · rw [hsy]; omega
  · have hdy_neg : B.y - A.y < 0 := by
      rcases lt_or_gt_of_ne hdy_ne with h | h
      · exact h
      · contradiction
    have hsy : stepY = -1 := by
      dsimp [stepY]
      have : ¬(B.y - A.y > 0) := by linarith
      simp [this, hdy_neg]
    have h_absDy : (if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)) = -(B.y - A.y) := by
      split_ifs with h <;> [linarith; rfl]
    have habsDy : 0 < -(B.y - A.y) := by linarith
    have h_yb : (if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) = ofInt c.y := by
      rw [hsy]; rfl
    have h_cA : c.y ≤ (floorPoint A).y := by
      have : 0 ≤ (c.y - (floorPoint A).y) * (-1) := by rw [← hsy]; exact h_cA_y
      omega
    have h_cx_le : x.y + 1 ≤ c.y := by
      have : 0 ≤ (x.y - c.y) * (-1) := by rw [← hsy]; exact h_cy_le
      omega
    have h_fl : (floorPoint A).y = toInt A.y := rfl
    have h_le : ((floorPoint A).y : Rat) ≤ A.y := by
      have := Rat.floor_le A.y
      unfold toInt at h_fl
      rw [← h_fl] at this
      exact this
    have h_le_A : ofInt c.y ≤ A.y := by
      have : (c.y : Rat) ≤ ((floorPoint A).y : Rat) := Int.cast_le.mpr h_cA
      dsimp [ofInt]
      linarith
    have h_remY : (if (if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
        (if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
      else A.y - if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) = A.y - ofInt c.y := by
      rw [h_yb]
      split_ifs with h
      · have : ofInt c.y = A.y := by linarith
        linarith
      · rfl
    have h_ty := interval_dy_neg x A B tEnter tExit h_inter hdy_neg
    have h_remY_le : A.y - ofInt c.y ≤ A.y - ofInt (x.y + 1) := by
      dsimp [ofInt]
      have : ((x.y + 1 : Int) : Rat) ≤ ((c.y : Int) : Rat) := Int.cast_le.mpr h_cx_le
      linarith
    have h1 : (A.y - ofInt c.y) / -(B.y - A.y) ≤ (A.y - ofInt (x.y + 1)) / -(B.y - A.y) :=
      div_le_div_of_nonneg_right h_remY_le (le_of_lt habsDy)
    have h_eq : (A.y - ofInt (x.y + 1)) / -(B.y - A.y) = (ofInt (x.y + 1) - A.y) / (B.y - A.y) := by
      have : A.y - ofInt (x.y + 1) = -(ofInt (x.y + 1) - A.y) := by ring
      rw [this, neg_div, div_neg, neg_neg]
    have h2 : (A.y - ofInt c.y) / -(B.y - A.y) < 1 := by linarith [h1, h_eq, h_ty.1, h_enter_lt_exit, h_exit_le_one]
    have h_remY_lt : A.y - ofInt c.y < -(B.y - A.y) := (div_lt_one habsDy).mp h2
    have h_not_ge : ¬(A.y - ofInt c.y ≥ -(B.y - A.y)) := by linarith
    rw [h_absDy, h_remY]
    simp only [ge_iff_le, h_not_ge, ↓reduceIte]
    refine ⟨trivial, ?_, ?_, ?_⟩
    · rw [hsy]; omega
    · rw [hsy]; omega
    · rw [hsy]; omega


theorem rayMarchStep_sy_zero (A B : Point) (c : Cell)
    (dx : Rat) (stepX : Int) (hx : (stepX == 0) = false) :
    let stepY : Int := 0
    let xb : Rat := if stepX > 0 then ofInt (c.x + 1) else ofInt c.x
    let absDx := if dx >= 0 then dx else -dx
    let remX := if xb >= A.x then xb - A.x else A.x - xb
    rayMarchStep A B dx 0 stepX stepY c =
      if remX >= absDx then (c, true)
      else (⟨c.x + stepX, c.y⟩, false) := by
  intro stepY xb absDx remX
  unfold rayMarchStep
  dsimp only []
  simp only [hx, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem step_sy_zero (A B : Point) (x c : Cell) (tEnter tExit : Rat)
    (hdy : B.y - A.y = 0) (hdx_ne : B.x - A.x ≠ 0)
    (h_enter_lt_exit : tEnter < tExit)
    (h_inter : cellIntersectionInterval x A B = some (tEnter, tExit))
    (h_cx_le : 0 ≤ (x.x - c.x) * if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0)
    (h_cx_ne : c.x ≠ x.x)
    (h_cA_x : 0 ≤ (c.x - (floorPoint A).x) * if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0) :
    let stepX : Int := if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0
    (rayMarchStep A B (B.x - A.x) (B.y - A.y) stepX 0 c) = (⟨c.x + stepX, c.y⟩, false) ∧
    (x.x - (c.x + stepX)) * stepX < (x.x - c.x) * stepX ∧
    0 ≤ (x.x - (c.x + stepX)) * stepX ∧
    0 ≤ (c.x + stepX - (floorPoint A).x) * stepX := by
  intro stepX
  have hsx_ne : (stepX == 0) = false := by
    dsimp [stepX]
    rcases lt_or_gt_of_ne hdx_ne with h | h
    · have : ¬(B.x - A.x > 0) := by linarith
      simp [this, h]
    · simp [h]
  have h_step := rayMarchStep_sy_zero A B c (B.x - A.x) stepX hsx_ne
  rw [hdy]
  dsimp only [] at h_step
  rw [h_step]
  have h_exit_le_one := (interval_enter_exit_le_one x A B tEnter tExit h_inter).2
  by_cases hdx_pos : B.x - A.x > 0
  · have hsx : stepX = 1 := by dsimp [stepX]; simp [hdx_pos]
    have h_absDx : (if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) = B.x - A.x := by
      split_ifs with h <;> [rfl; linarith]
    have h_xb : (if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) = ofInt (c.x + 1) := by
      rw [hsx]; rfl
    have h_cA : (floorPoint A).x ≤ c.x := by
      have : 0 ≤ (c.x - (floorPoint A).x) * 1 := by rw [← hsx]; exact h_cA_x
      omega
    have h_cx_le' : c.x + 1 ≤ x.x := by
      have : 0 ≤ (x.x - c.x) * 1 := by rw [← hsx]; exact h_cx_le
      omega
    have h_fl : (floorPoint A).x = toInt A.x := rfl
    have h_lt : A.x < ((floorPoint A).x : Rat) + 1 := by
      have := Rat.lt_floor_add_one A.x
      unfold toInt at h_fl
      rw [← h_fl] at this
      push_cast at this
      exact this
    have h_cast_cA : ((floorPoint A).x : Rat) ≤ (c.x : Rat) := Int.cast_le.mpr h_cA
    have h_ge : A.x < ofInt (c.x + 1) := by
      dsimp [ofInt]
      push_cast
      linarith
    have h_remX : (if (if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
        (if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
      else A.x - if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) = ofInt (c.x + 1) - A.x := by
      rw [h_xb]
      split_ifs with h <;> [rfl; linarith]
    have h_tx := interval_dx_pos x A B tEnter tExit h_inter hdx_pos
    have h_remX_le : ofInt (c.x + 1) - A.x ≤ ofInt x.x - A.x := by
      dsimp [ofInt]
      have : ((c.x + 1 : Int) : Rat) ≤ ((x.x : Int) : Rat) := Int.cast_le.mpr h_cx_le'
      linarith
    have h1 : (ofInt (c.x + 1) - A.x) / (B.x - A.x) ≤ (ofInt x.x - A.x) / (B.x - A.x) :=
      div_le_div_of_nonneg_right h_remX_le (le_of_lt hdx_pos)
    have h2 : (ofInt (c.x + 1) - A.x) / (B.x - A.x) < 1 := by linarith [h1, h_tx.1, h_enter_lt_exit, h_exit_le_one]
    have h_remX_lt : ofInt (c.x + 1) - A.x < B.x - A.x := (div_lt_one hdx_pos).mp h2
    have h_not_ge : ¬(ofInt (c.x + 1) - A.x ≥ B.x - A.x) := by linarith
    rw [h_absDx, h_remX]
    simp only [ge_iff_le, h_not_ge, ↓reduceIte]
    refine ⟨trivial, ?_, ?_, ?_⟩
    · rw [hsx]; omega
    · rw [hsx]; omega
    · rw [hsx]; omega
  · have hdx_neg : B.x - A.x < 0 := by
      rcases lt_or_gt_of_ne hdx_ne with h | h
      · exact h
      · contradiction
    have hsx : stepX = -1 := by
      dsimp [stepX]
      have : ¬(B.x - A.x > 0) := by linarith
      simp [this, hdx_neg]
    have h_absDx : (if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) = -(B.x - A.x) := by
      split_ifs with h <;> [linarith; rfl]
    have habsDx : 0 < -(B.x - A.x) := by linarith
    have h_xb : (if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) = ofInt c.x := by
      rw [hsx]; rfl
    have h_cA : c.x ≤ (floorPoint A).x := by
      have : 0 ≤ (c.x - (floorPoint A).x) * (-1) := by rw [← hsx]; exact h_cA_x
      omega
    have h_cx_le' : x.x + 1 ≤ c.x := by
      have : 0 ≤ (x.x - c.x) * (-1) := by rw [← hsx]; exact h_cx_le
      omega
    have h_fl : (floorPoint A).x = toInt A.x := rfl
    have h_le : ((floorPoint A).x : Rat) ≤ A.x := by
      have := Rat.floor_le A.x
      unfold toInt at h_fl
      rw [← h_fl] at this
      exact this
    have h_le_A : ofInt c.x ≤ A.x := by
      have : (c.x : Rat) ≤ ((floorPoint A).x : Rat) := Int.cast_le.mpr h_cA
      dsimp [ofInt]
      linarith
    have h_remX : (if (if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
        (if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
      else A.x - if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) = A.x - ofInt c.x := by
      rw [h_xb]
      split_ifs with h
      · have : ofInt c.x = A.x := by linarith
        linarith
      · rfl
    have h_tx := interval_dx_neg x A B tEnter tExit h_inter hdx_neg
    have h_remX_le : A.x - ofInt c.x ≤ A.x - ofInt (x.x + 1) := by
      dsimp [ofInt]
      have : ((x.x + 1 : Int) : Rat) ≤ ((c.x : Int) : Rat) := Int.cast_le.mpr h_cx_le'
      linarith
    have h1 : (A.x - ofInt c.x) / -(B.x - A.x) ≤ (A.x - ofInt (x.x + 1)) / -(B.x - A.x) :=
      div_le_div_of_nonneg_right h_remX_le (le_of_lt habsDx)
    have h_eq : (A.x - ofInt (x.x + 1)) / -(B.x - A.x) = (ofInt (x.x + 1) - A.x) / (B.x - A.x) := by
      have : A.x - ofInt (x.x + 1) = -(ofInt (x.x + 1) - A.x) := by ring
      rw [this, neg_div, div_neg, neg_neg]
    have h2 : (A.x - ofInt c.x) / -(B.x - A.x) < 1 := by linarith [h1, h_eq, h_tx.1, h_enter_lt_exit, h_exit_le_one]
    have h_remX_lt : A.x - ofInt c.x < -(B.x - A.x) := (div_lt_one habsDx).mp h2
    have h_not_ge : ¬(A.x - ofInt c.x ≥ -(B.x - A.x)) := by linarith
    rw [h_absDx, h_remX]
    simp only [ge_iff_le, h_not_ge, ↓reduceIte]
    refine ⟨trivial, ?_, ?_, ?_⟩
    · rw [hsx]; omega
    · rw [hsx]; omega
    · rw [hsx]; omega




theorem rayMarchStep_diag (A B : Point) (c : Cell)
    (dx dy : Rat) (stepX stepY : Int) (hx : (stepX == 0) = false) (hy : (stepY == 0) = false) :
    let xb : Rat := if stepX > 0 then ofInt (c.x + 1) else ofInt c.x
    let yb : Rat := if stepY > 0 then ofInt (c.y + 1) else ofInt c.y
    let absDx := if dx >= 0 then dx else -dx
    let absDy := if dy >= 0 then dy else -dy
    let remX := if xb >= A.x then xb - A.x else A.x - xb
    let remY := if yb >= A.y then yb - A.y else A.y - yb
    let crossX := remX * absDy
    let crossY := remY * absDx
    let limitCross := absDx * absDy
    rayMarchStep A B dx dy stepX stepY c =
      if min crossX crossY >= limitCross then (c, true)
      else if crossX < crossY then (⟨c.x + stepX, c.y⟩, false)
      else if crossY < crossX then (⟨c.x, c.y + stepY⟩, false)
      else (⟨c.x + stepX, c.y + stepY⟩, false) := by
  intro xb yb absDx absDy remX remY crossX crossY limitCross
  unfold rayMarchStep
  dsimp only []
  simp only [hx, hy, Bool.false_eq_true, ↓reduceIte]
  rfl



def absVal (r : Rat) : Rat := if r ≥ 0 then r else -r


def remX_val (start : Point) (stepX : Int) (c : Cell) : Rat :=
  let xb := if stepX > 0 then ofInt (c.x + 1) else ofInt c.x
  if xb ≥ start.x then xb - start.x else start.x - xb


def remY_val (start : Point) (stepY : Int) (c : Cell) : Rat :=
  let yb := if stepY > 0 then ofInt (c.y + 1) else ofInt c.y
  if yb ≥ start.y then yb - start.y else start.y - yb



theorem rayMarchStep_cases (start ptEnd : Point) (dx dy : Rat) (stepX stepY : Int) (c : Cell) :
    rayMarchStep start ptEnd dx dy stepX stepY c = (c, true) ∨
    rayMarchStep start ptEnd dx dy stepX stepY c = (⟨c.x + stepX, c.y⟩, false) ∨
    rayMarchStep start ptEnd dx dy stepX stepY c = (⟨c.x, c.y + stepY⟩, false) ∨
    rayMarchStep start ptEnd dx dy stepX stepY c = (⟨c.x + stepX, c.y + stepY⟩, false) := by
  have h_mem := rayMarchStep_mem start ptEnd dx dy stepX stepY c
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h_mem
  exact h_mem


theorem rayMarchStep_not_done_cases (start ptEnd : Point) (dx dy : Rat) (stepX stepY : Int) (c : Cell)
    (h_not_done : (rayMarchStep start ptEnd dx dy stepX stepY c).2 = false) :
    let next := (rayMarchStep start ptEnd dx dy stepX stepY c).1
    next = ⟨c.x + stepX, c.y⟩ ∨ next = ⟨c.x, c.y + stepY⟩ ∨ next = ⟨c.x + stepX, c.y + stepY⟩ := by
  have h := rayMarchStep_cases start ptEnd dx dy stepX stepY c
  rcases h with h1 | h2 | h3 | h4
  · rw [h1] at h_not_done
    contradiction
  · rw [h2]
    exact Or.inl rfl
  · rw [h3]
    exact Or.inr (Or.inl rfl)
  · rw [h4]
    exact Or.inr (Or.inr rfl)


theorem rayMarch_same_endpoints (fuel : Nat) (A B : Point) (dx dy : Rat) (stepX stepY : Int)
    (h : floorPoint A = floorPoint B) :
    rayMarch (fuel + 1) A B dx dy stepX stepY (floorPoint B) (floorPoint A) [] = [] := by
  rw [rayMarch_succ]
  dsimp only []
  have : (floorPoint A == floorPoint B) = true := by rw [h]; exact beq_self_eq_true _
  simp [this]


theorem floor_mono {x y : Rat} (h : x ≤ y) : Rat.floor x ≤ Rat.floor y := by
  have h1 : ((Rat.floor x : Int) : Rat) ≤ x := Rat.floor_le x
  have h2 : ((Rat.floor x : Int) : Rat) ≤ y := le_trans h1 h
  by_contra! h_lt
  have : Rat.floor y + 1 ≤ Rat.floor x := h_lt
  have h_le : ((Rat.floor y + 1 : Int) : Rat) ≤ ((Rat.floor x : Int) : Rat) := Int.cast_le.mpr this
  have h_lt_cast : y < ((Rat.floor y + 1 : Int) : Rat) := Rat.lt_floor_add_one y
  linarith


theorem floor_le_sub_one_of_lt (y : Rat) (cy : Int) (h : y < ofInt cy) :
    Rat.floor y ≤ cy - 1 := by
  have h1 : ((Rat.floor y : Int) : Rat) ≤ y := Rat.floor_le y
  have h2 : ((Rat.floor y : Int) : Rat) < ofInt cy := lt_of_le_of_lt h1 h
  unfold ofInt at h2
  change ((Rat.floor y : Int) : Rat) < ((cy : Int) : Rat) at h2
  have h3 : Rat.floor y < cy := Int.cast_lt.mp h2
  omega


theorem stepX_pos_next_le_end (cx : Int) (Ax : Rat) (B : Point)
    (_hdx : 0 < B.x - Ax)
    (h_bnd : ofInt cx - Ax < B.x - Ax) :
    cx ≤ (floorPoint B).x := by
  have h_lt : ((cx : Int) : Rat) ≤ B.x := by
    change ((cx : Int) : Rat) - Ax < B.x - Ax at h_bnd
    linarith
  unfold floorPoint toInt; dsimp
  exact le_floor_of_le cx B.x h_lt


theorem stepY_pos_next_le_end (cy : Int) (Ay : Rat) (B : Point)
    (_hdy : 0 < B.y - Ay)
    (h_bnd : ofInt cy - Ay < B.y - Ay) :
    cy ≤ (floorPoint B).y := by
  have h_lt : ((cy : Int) : Rat) ≤ B.y := by
    change ((cy : Int) : Rat) - Ay < B.y - Ay at h_bnd
    linarith
  unfold floorPoint toInt; dsimp
  exact le_floor_of_le cy B.y h_lt


theorem stepX_neg_next_ge_end (cx : Int) (Ax : Rat) (B : Point)
    (hdx : B.x - Ax < 0)
    (h_bnd : (ofInt cx - Ax) / (B.x - Ax) < 1) :
    (floorPoint B).x ≤ cx - 1 := by
  have h_gt : B.x < ofInt cx := by
    have := (div_lt_one_of_neg hdx).mp h_bnd
    linarith
  unfold floorPoint toInt; dsimp
  exact floor_le_sub_one_of_lt B.x cx h_gt


theorem stepY_neg_next_ge_end (cy : Int) (Ay : Rat) (B : Point)
    (hdy : B.y - Ay < 0)
    (h_bnd : (ofInt cy - Ay) / (B.y - Ay) < 1) :
    (floorPoint B).y ≤ cy - 1 := by
  have h_gt : B.y < ofInt cy := by
    have := (div_lt_one_of_neg hdy).mp h_bnd
    linarith
  unfold floorPoint toInt; dsimp
  exact floor_le_sub_one_of_lt B.y cy h_gt


theorem inBoundingBox_stepX_forward (c : Cell) (A B : Point)
    (hdx : 0 < B.x - A.x)
    (h_bbox : inBoundingBox c A B = true)
    (h_next : c.x + 1 ≤ (floorPoint B).x) :
    inBoundingBox ⟨c.x + 1, c.y⟩ A B = true := by
  unfold inBoundingBox at h_bbox ⊢
  dsimp only [] at h_bbox ⊢
  have h_floorA : (floorPoint A).x ≤ (floorPoint B).x := floor_mono (by linarith)
  have h_min : min (floorPoint A).x (floorPoint B).x = (floorPoint A).x := min_eq_left h_floorA
  have h_max : max (floorPoint A).x (floorPoint B).x = (floorPoint B).x := max_eq_right h_floorA
  rw [h_min, h_max] at h_bbox ⊢
  simp only [Bool.and_eq_true, decide_eq_true_iff] at h_bbox ⊢
  rcases h_bbox with ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
  exact ⟨⟨⟨by omega, h_next⟩, h3⟩, h4⟩


theorem inBoundingBox_stepX_backward (c : Cell) (A B : Point)
    (hdx : B.x - A.x < 0)
    (h_bbox : inBoundingBox c A B = true)
    (h_next : (floorPoint B).x ≤ c.x - 1) :
    inBoundingBox ⟨c.x - 1, c.y⟩ A B = true := by
  unfold inBoundingBox at h_bbox ⊢
  dsimp only [] at h_bbox ⊢
  have h_floorB : (floorPoint B).x ≤ (floorPoint A).x := floor_mono (by linarith)
  have h_min : min (floorPoint A).x (floorPoint B).x = (floorPoint B).x := min_eq_right h_floorB
  have h_max : max (floorPoint A).x (floorPoint B).x = (floorPoint A).x := max_eq_left h_floorB
  rw [h_min, h_max] at h_bbox ⊢
  simp only [Bool.and_eq_true, decide_eq_true_iff] at h_bbox ⊢
  rcases h_bbox with ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
  exact ⟨⟨⟨h_next, by omega⟩, h3⟩, h4⟩


theorem inBoundingBox_stepY_forward (c : Cell) (A B : Point)
    (hdy : 0 < B.y - A.y)
    (h_bbox : inBoundingBox c A B = true)
    (h_next : c.y + 1 ≤ (floorPoint B).y) :
    inBoundingBox ⟨c.x, c.y + 1⟩ A B = true := by
  unfold inBoundingBox at h_bbox ⊢
  dsimp only [] at h_bbox ⊢
  have h_floorA : (floorPoint A).y ≤ (floorPoint B).y := floor_mono (by linarith)
  have h_min : min (floorPoint A).y (floorPoint B).y = (floorPoint A).y := min_eq_left h_floorA
  have h_max : max (floorPoint A).y (floorPoint B).y = (floorPoint B).y := max_eq_right h_floorA
  rw [h_min, h_max] at h_bbox ⊢
  simp only [Bool.and_eq_true, decide_eq_true_iff] at h_bbox ⊢
  rcases h_bbox with ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
  exact ⟨⟨⟨h1, h2⟩, by omega⟩, h_next⟩


theorem inBoundingBox_stepY_backward (c : Cell) (A B : Point)
    (hdy : B.y - A.y < 0)
    (h_bbox : inBoundingBox c A B = true)
    (h_next : (floorPoint B).y ≤ c.y - 1) :
    inBoundingBox ⟨c.x, c.y - 1⟩ A B = true := by
  unfold inBoundingBox at h_bbox ⊢
  dsimp only [] at h_bbox ⊢
  have h_floorB : (floorPoint B).y ≤ (floorPoint A).y := floor_mono (by linarith)
  have h_min : min (floorPoint A).y (floorPoint B).y = (floorPoint B).y := min_eq_right h_floorB
  have h_max : max (floorPoint A).y (floorPoint B).y = (floorPoint A).y := max_eq_left h_floorB
  rw [h_min, h_max] at h_bbox ⊢
  simp only [Bool.and_eq_true, decide_eq_true_iff] at h_bbox ⊢
  rcases h_bbox with ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
  exact ⟨⟨⟨h1, h2⟩, h_next⟩, by omega⟩


theorem stepX_interval_lt_neg (tx1 ty0 ty1 dx : Rat) (dx_neg : dx < 0)
    (h_cross : tx1 < ty1)
    (h_lim : tx1 < 1)
    (h_pos : 0 ≤ tx1)
    (h_ty0 : ty0 ≤ tx1) :
    max 0 (max tx1 ty0) < min 1 (min (tx1 - 1 / dx) ty1) := by
  have h_enter : max 0 (max tx1 ty0) = tx1 := by
    rw [max_eq_left h_ty0]
    exact max_eq_right h_pos
  rw [h_enter]
  have h1 : tx1 < 1 := h_lim
  have h2 : tx1 < tx1 - 1 / dx := by
    have h_neg_dx : 0 < -dx := by linarith
    have h_inv : 0 < 1 / -dx := one_div_pos.mpr h_neg_dx
    have h_eq : -1 / dx = 1 / -dx := by ring
    linarith
  have h3 : tx1 < ty1 := h_cross
  rw [lt_min_iff]
  refine ⟨h1, ?_⟩
  rw [lt_min_iff]
  exact ⟨h2, h3⟩


theorem stepY_interval_lt_neg (ty1 tx0 tx1 dy : Rat) (dy_neg : dy < 0)
    (h_cross : ty1 < tx1)
    (h_lim : ty1 < 1)
    (h_pos : 0 ≤ ty1)
    (h_tx0 : tx0 ≤ ty1) :
    max 0 (max tx0 ty1) < min 1 (min tx1 (ty1 - 1 / dy)) := by
  have h_enter : max 0 (max tx0 ty1) = ty1 := by
    rw [max_eq_right h_tx0]
    exact max_eq_right h_pos
  rw [h_enter]
  have h1 : ty1 < 1 := h_lim
  have h2 : ty1 < tx1 := h_cross
  have h3 : ty1 < ty1 - 1 / dy := by
    have h_neg_dy : 0 < -dy := by linarith
    have h_inv : 0 < 1 / -dy := one_div_pos.mpr h_neg_dy
    have h_eq : -1 / dy = 1 / -dy := by ring
    linarith
  rw [lt_min_iff]
  refine ⟨h1, ?_⟩
  rw [lt_min_iff]
  exact ⟨h2, h3⟩



end Geometry
