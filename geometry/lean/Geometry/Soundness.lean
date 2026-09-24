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
import Geometry.RayMarchStep
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Geometry

/- =========================================================================
   Quadrant 1: dx > 0, dy > 0
   ========================================================================= -/

theorem inBoundingBox_diag (c : Cell) (A B : Point) (stepX stepY : ℤ)
    (hX : inBoundingBox ⟨c.x + stepX, c.y⟩ A B = true)
    (hY : inBoundingBox ⟨c.x, c.y + stepY⟩ A B = true) :
    inBoundingBox ⟨c.x + stepX, c.y + stepY⟩ A B = true := by
  unfold inBoundingBox at hX hY ⊢
  dsimp only [] at hX hY ⊢
  simp only [Bool.and_eq_true] at hX hY ⊢
  exact ⟨⟨⟨hX.1.1.1, hX.1.1.2⟩, hY.1.2⟩, hY.2⟩


theorem cellIntersectionInterval_stepX_pos (A B : Point) (c : Cell)
    (hdx : 0 < B.x - A.x) (hdy : 0 < B.y - A.y) :
    let dx := B.x - A.x
    let dy := B.y - A.y
    let tx1 := (ofInt (c.x + 1) - A.x) / dx
    let ty0 := (ofInt c.y - A.y) / dy
    let ty1 := (ofInt (c.y + 1) - A.y) / dy
    let tEnter := max 0 (max tx1 ty0)
    let tExit := min 1 (min (tx1 + 1 / dx) ty1)
    tEnter < tExit →
    cellIntersectionInterval ⟨c.x + 1, c.y⟩ A B = some (tEnter, tExit) := by
  intro dx dy tx1 ty0 ty1 tEnter tExit h_lt
  unfold cellIntersectionInterval
  dsimp only []
  have h_dx_ne : (B.x - A.x == 0) = false := by
    cases h : (B.x - A.x == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_dy_ne : (B.y - A.y == 0) = false := by
    cases h : (B.y - A.y == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  simp only [h_dx_ne, h_dy_ne, hdx, hdy, ↓reduceIte]
  have h_cx1 : ofInt (c.x + 1 + 1) = ofInt (c.x + 1) + 1 := by
    unfold ofInt
    change ((c.x + 1 + 1 : ℤ) : ℚ) = ((c.x + 1 : ℤ) : ℚ) + 1
    push_cast
    ring
  rw [h_cx1]
  have h_divx : (ofInt (c.x + 1) + 1 - A.x) / (B.x - A.x) = tx1 + 1 / dx := by
    dsimp [tx1, dx]
    ring
  rw [h_divx]
  simp only [Bool.false_eq_true, ↓reduceIte]
  change (if tEnter ≤ tExit then some (tEnter, tExit) else none) = some (tEnter, tExit)
  have h_le : tEnter ≤ tExit := le_of_lt h_lt
  simp only [h_le, ↓reduceIte]


theorem cellIntersectionInterval_stepY_pos (A B : Point) (c : Cell)
    (hdx : 0 < B.x - A.x) (hdy : 0 < B.y - A.y) :
    let dx := B.x - A.x
    let dy := B.y - A.y
    let tx0 := (ofInt c.x - A.x) / dx
    let tx1 := (ofInt (c.x + 1) - A.x) / dx
    let ty1 := (ofInt (c.y + 1) - A.y) / dy
    let tEnter := max 0 (max tx0 ty1)
    let tExit := min 1 (min tx1 (ty1 + 1 / dy))
    tEnter < tExit →
    cellIntersectionInterval ⟨c.x, c.y + 1⟩ A B = some (tEnter, tExit) := by
  intro dx dy tx0 tx1 ty1 tEnter tExit h_lt
  unfold cellIntersectionInterval
  dsimp only []
  have h_dx_ne : (B.x - A.x == 0) = false := by
    cases h : (B.x - A.x == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_dy_ne : (B.y - A.y == 0) = false := by
    cases h : (B.y - A.y == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  simp only [h_dx_ne, h_dy_ne, hdx, hdy, ↓reduceIte]
  have h_cy1 : ofInt (c.y + 1 + 1) = ofInt (c.y + 1) + 1 := by
    unfold ofInt
    change ((c.y + 1 + 1 : ℤ) : ℚ) = ((c.y + 1 : ℤ) : ℚ) + 1
    push_cast
    ring
  rw [h_cy1]
  have h_divy : (ofInt (c.y + 1) + 1 - A.y) / (B.y - A.y) = ty1 + 1 / dy := by
    dsimp [ty1, dy]
    ring
  rw [h_divy]
  simp only [Bool.false_eq_true, ↓reduceIte]
  change (if tEnter ≤ tExit then some (tEnter, tExit) else none) = some (tEnter, tExit)
  have h_le : tEnter ≤ tExit := le_of_lt h_lt
  simp only [h_le, ↓reduceIte]


theorem cellIntersectionInterval_diag_pos (A B : Point) (c : Cell) (hdx : 0 < B.x - A.x) (hdy : 0 < B.y - A.y) :
    let dx := B.x - A.x
    let dy := B.y - A.y
    let t := (ofInt (c.x + 1) - A.x) / dx
    let tEnter := max 0 (max t t)
    let tExit := min 1 (min (t + 1 / dx) (t + 1 / dy))
    t = (ofInt (c.y + 1) - A.y) / dy →
    tEnter < tExit →
    cellIntersectionInterval ⟨c.x + 1, c.y + 1⟩ A B = some (tEnter, tExit) := by
  intro dx dy t tEnter tExit h_eq h_lt
  unfold cellIntersectionInterval
  dsimp only []
  have h_dx_ne : (B.x - A.x == 0) = false := by
    cases h : (B.x - A.x == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_dy_ne : (B.y - A.y == 0) = false := by
    cases h : (B.y - A.y == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  simp only [h_dx_ne, h_dy_ne, hdx, hdy, ↓reduceIte]
  have h_cx1 : ofInt (c.x + 1 + 1) = ofInt (c.x + 1) + 1 := by
    unfold ofInt
    change ((c.x + 1 + 1 : ℤ) : ℚ) = ((c.x + 1 : ℤ) : ℚ) + 1
    push_cast
    ring
  have h_cy1 : ofInt (c.y + 1 + 1) = ofInt (c.y + 1) + 1 := by
    unfold ofInt
    change ((c.y + 1 + 1 : ℤ) : ℚ) = ((c.y + 1 : ℤ) : ℚ) + 1
    push_cast
    ring
  rw [h_cx1, h_cy1]
  have h_divx : (ofInt (c.x + 1) + 1 - A.x) / (B.x - A.x) = t + 1 / dx := by
    dsimp [t, dx]
    ring
  have h_divy : (ofInt (c.y + 1) + 1 - A.y) / (B.y - A.y) = t + 1 / dy := by
    have h_split : (ofInt (c.y + 1) + 1 - A.y) / (B.y - A.y) =
        (ofInt (c.y + 1) - A.y) / (B.y - A.y) + 1 / (B.y - A.y) := by ring
    rw [h_split]
    dsimp [dy]
    rw [← h_eq]
  rw [h_divx, h_divy]
  have h_ty : (ofInt (c.y + 1) - A.y) / (B.y - A.y) = t := by
    dsimp [dy] at h_eq
    exact h_eq.symm
  rw [h_ty]
  simp only [Bool.false_eq_true, ↓reduceIte]
  change (if tEnter ≤ tExit then some (tEnter, tExit) else none) = some (tEnter, tExit)
  have h_le : tEnter ≤ tExit := le_of_lt h_lt
  simp only [h_le, ↓reduceIte]


theorem extract_stepX_pos_pos (A B : Point) (c : Cell)
    (_hdx : 0 < B.x - A.x) (_hdy : 0 < B.y - A.y)
    (h_step : rayMarchStep A B (B.x - A.x) (B.y - A.y) 1 1 c = (⟨c.x + 1, c.y⟩, false)) :
    remX_val A 1 c * absVal (B.y - A.y) < remY_val A 1 c * absVal (B.x - A.x) ∧
    min (remX_val A 1 c * absVal (B.y - A.y)) (remY_val A 1 c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y) := by
  unfold rayMarchStep at h_step
  dsimp only [] at h_step
  simp only [show ((1 : ℤ) == 0) = false by decide, Bool.false_eq_true, ↓reduceIte] at h_step
  by_cases hlim : min
        ((if (if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y))
        ((if (if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) ≥
      (if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) *
        if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
  · simp only [hlim, ↓reduceIte] at h_step
    injection h_step with _ h_bool; contradiction
  · simp only [hlim, ↓reduceIte] at h_step
    by_cases hxy : ((if (if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)) <
        (if (if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)
    · unfold remX_val remY_val absVal
      dsimp only []
      simp only [show (1 : ℤ) > 0 by decide, ↓reduceIte]
      refine ⟨hxy, not_le.mp hlim⟩
    · simp only [hxy, ↓reduceIte] at h_step
      by_cases hyx : ((if (if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
              (if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
            else A.y - if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) *
            if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) <
          (if (if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
              (if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
            else A.x - if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) *
            if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
      · simp only [hyx, ↓reduceIte] at h_step
        injection h_step with h_cell _
        injection h_cell with hx _
        omega
      · simp only [hyx, ↓reduceIte] at h_step
        injection h_step with h_cell _
        injection h_cell with _ hy
        omega


theorem extract_stepY_pos_pos (A B : Point) (c : Cell)
    (_hdx : 0 < B.x - A.x) (_hdy : 0 < B.y - A.y)
    (h_step : rayMarchStep A B (B.x - A.x) (B.y - A.y) 1 1 c = (⟨c.x, c.y + 1⟩, false)) :
    remY_val A 1 c * absVal (B.x - A.x) < remX_val A 1 c * absVal (B.y - A.y) ∧
    min (remX_val A 1 c * absVal (B.y - A.y)) (remY_val A 1 c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y) := by
  unfold rayMarchStep at h_step
  dsimp only [] at h_step
  simp only [show ((1 : ℤ) == 0) = false by decide, Bool.false_eq_true, ↓reduceIte] at h_step
  by_cases hlim : min
        ((if (if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y))
        ((if (if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) ≥
      (if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) *
        if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
  · simp only [hlim, ↓reduceIte] at h_step
    injection h_step with _ h_bool; contradiction
  · simp only [hlim, ↓reduceIte] at h_step
    by_cases hxy : ((if (if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)) <
        (if (if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)
    · simp only [hxy, ↓reduceIte] at h_step
      injection h_step with h_cell _
      injection h_cell with hx _
      omega
    · simp only [hxy, ↓reduceIte] at h_step
      by_cases hyx : ((if (if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
              (if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
            else A.y - if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) *
            if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) <
          (if (if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
              (if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
            else A.x - if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) *
            if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
      · unfold remX_val remY_val absVal
        dsimp only []
        simp only [show (1 : ℤ) > 0 by decide, ↓reduceIte]
        refine ⟨hyx, not_le.mp hlim⟩
      · simp only [hyx, ↓reduceIte] at h_step
        injection h_step with h_cell _
        injection h_cell with hx _
        omega


theorem extract_stepDiag_pos_pos (A B : Point) (c : Cell)
    (_hdx : 0 < B.x - A.x) (_hdy : 0 < B.y - A.y)
    (h_step : rayMarchStep A B (B.x - A.x) (B.y - A.y) 1 1 c = (⟨c.x + 1, c.y + 1⟩, false)) :
    remX_val A 1 c * absVal (B.y - A.y) = remY_val A 1 c * absVal (B.x - A.x) ∧
    min (remX_val A 1 c * absVal (B.y - A.y)) (remY_val A 1 c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y) := by
  unfold rayMarchStep at h_step
  dsimp only [] at h_step
  simp only [show ((1 : ℤ) == 0) = false by decide, Bool.false_eq_true, ↓reduceIte] at h_step
  by_cases hlim : min
        ((if (if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y))
        ((if (if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) ≥
      (if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) *
        if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
  · simp only [hlim, ↓reduceIte] at h_step
    injection h_step with _ h_bool; contradiction
  · simp only [hlim, ↓reduceIte] at h_step
    by_cases hxy : ((if (if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)) <
        (if (if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)
    · simp only [hxy, ↓reduceIte] at h_step
      injection h_step with h_cell _
      injection h_cell with _ hy
      omega
    · simp only [hxy, ↓reduceIte] at h_step
      by_cases hyx : ((if (if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
              (if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
            else A.y - if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) *
            if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) <
          (if (if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
              (if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
            else A.x - if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) *
            if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
      · simp only [hyx, ↓reduceIte] at h_step
        injection h_step with h_cell _
        injection h_cell with hx _
        omega
      · unfold remX_val remY_val absVal
        dsimp only []
        simp only [show (1 : ℤ) > 0 by decide, ↓reduceIte]
        simp only [show (1 : ℤ) > 0 by decide, ↓reduceIte] at hxy hyx hlim
        have h_eq : ((if ofInt (c.x + 1) ≥ A.x then ofInt (c.x + 1) - A.x else A.x - ofInt (c.x + 1)) *
              if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)) =
            ((if ofInt (c.y + 1) ≥ A.y then ofInt (c.y + 1) - A.y else A.y - ofInt (c.y + 1)) *
              if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) := le_antisymm (not_lt.mp hyx) (not_lt.mp hxy)
        refine ⟨h_eq, not_le.mp hlim⟩


theorem rayMarchStep_X_pos_pos_sound (A B : Point) (c : Cell)
    (hdx : 0 < B.x - A.x) (hdy : 0 < B.y - A.y)
    (hc_bbox : inBoundingBox c A B = true)
    (hc_int : ∃ tEnter tExit, cellIntersectionInterval c A B = some (tEnter, tExit) ∧ tEnter < tExit)
    (h_step : remX_val A 1 c * absVal (B.y - A.y) < remY_val A 1 c * absVal (B.x - A.x))
    (h_not_done : min (remX_val A 1 c * absVal (B.y - A.y)) (remY_val A 1 c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y)) :
    inBoundingBox ⟨c.x + 1, c.y⟩ A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval ⟨c.x + 1, c.y⟩ A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  have h_absDy : 0 < absVal (B.y - A.y) := by
    unfold absVal
    simp [le_of_lt hdy, hdy]
  have h_bnd := stepX_bounded (remX_val A 1 c) (absVal (B.x - A.x)) (absVal (B.y - A.y))
    (remY_val A 1 c * absVal (B.x - A.x)) h_absDy h_step h_not_done
  unfold absVal at h_bnd
  simp [le_of_lt hdx] at h_bnd
  unfold remX_val at h_bnd
  simp only [show (1 : ℤ) > 0 by decide, ↓reduceIte] at h_bnd
  have hc_prop := hc_bbox
  unfold inBoundingBox at hc_prop
  dsimp only [] at hc_prop
  simp only [Bool.and_eq_true, decide_eq_true_iff] at hc_prop
  have h_flA : (floorPoint A).x ≤ c.x := by
    have h_min := hc_prop.1.1.1
    have h_le : (floorPoint A).x ≤ (floorPoint B).x := by
      unfold floorPoint toInt; dsimp
      have : A.x ≤ B.x := by linarith
      exact floor_mono this
    rw [min_eq_left h_le] at h_min
    exact h_min
  have h_flAy : (floorPoint A).y ≤ c.y := by
    have h_min := hc_prop.1.2
    have h_le : (floorPoint A).y ≤ (floorPoint B).y := by
      unfold floorPoint toInt; dsimp
      have : A.y ≤ B.y := by linarith
      exact floor_mono this
    rw [min_eq_left h_le] at h_min
    exact h_min
  have h_ge : ofInt (c.x + 1) ≥ A.x := by
    unfold floorPoint toInt at h_flA; dsimp at h_flA
    have h_lt := Rat.lt_floor_add_one A.x
    push_cast at h_lt
    have h_flA_rat : ((A.x.floor : ℤ) : ℚ) ≤ (c.x : ℚ) := Int.cast_le.mpr h_flA
    have h_ofInt : ofInt (c.x + 1) = (c.x : ℚ) + 1 := by
      unfold ofInt; change ((c.x + 1 : ℤ) : ℚ) = (c.x : ℚ) + 1; push_cast; ring
    rw [h_ofInt]
    linarith
  have h_remY_ge : ofInt (c.y + 1) ≥ A.y := by
    unfold floorPoint toInt at h_flAy; dsimp at h_flAy
    have h_lt := Rat.lt_floor_add_one A.y
    push_cast at h_lt
    have h_flAy_rat : ((A.y.floor : ℤ) : ℚ) ≤ (c.y : ℚ) := Int.cast_le.mpr h_flAy
    have h_ofInt : ofInt (c.y + 1) = (c.y : ℚ) + 1 := by
      unfold ofInt; change ((c.y + 1 : ℤ) : ℚ) = (c.y : ℚ) + 1; push_cast; ring
    rw [h_ofInt]
    linarith
  simp only [h_ge, ↓reduceIte] at h_bnd
  have h_le := stepX_next_le_end c.x A.x B.x h_bnd
  have h_bbox_next := inBoundingBox_stepX_forward c A B hdx hc_bbox h_le
  refine ⟨h_bbox_next, ?_⟩
  rcases hc_int with ⟨tEnter_c, tExit_c, hc_inter, _⟩
  have h_dx_prop := interval_dx_pos c A B tEnter_c tExit_c hc_inter hdx
  have h_dy_prop := interval_dy_pos c A B tEnter_c tExit_c hc_inter hdy
  unfold remY_val absVal at h_step
  simp only [show (1 : ℤ) > 0 by decide, ↓reduceIte, le_of_lt hdy, le_of_lt hdx, h_remY_ge] at h_step
  unfold remX_val at h_step
  simp only [show (1 : ℤ) > 0 by decide, ↓reduceIte, h_ge] at h_step
  let tx1 := (ofInt (c.x + 1) - A.x) / (B.x - A.x)
  let ty0 := (ofInt c.y - A.y) / (B.y - A.y)
  let ty1 := (ofInt (c.y + 1) - A.y) / (B.y - A.y)
  have h_cross : tx1 < ty1 := by
    dsimp [tx1, ty1]
    exact (cross_lt_cross_iff_div_lt_div (ofInt (c.x + 1) - A.x) (ofInt (c.y + 1) - A.y) (B.x - A.x) (B.y - A.y) hdx hdy).mp h_step
  have h_lim : tx1 < 1 := by
    dsimp [tx1]
    exact (div_lt_one hdx).mpr h_bnd
  have h_pos' : 0 ≤ tx1 := by
    dsimp [tx1]
    exact div_nonneg (by linarith) (le_of_lt hdx)
  have h_ty0 : ty0 ≤ tx1 := by
    dsimp [tx1, ty0]
    linarith [h_dy_prop.1, h_dx_prop.2]
  have h_lt := stepX_interval_lt tx1 ty0 ty1 (B.x - A.x) hdx h_cross h_lim h_pos' h_ty0
  let tEnter := max 0 (max tx1 ty0)
  let tExit := min 1 (min (tx1 + 1 / (B.x - A.x)) ty1)
  have h_eval := cellIntersectionInterval_stepX_pos A B c hdx hdy h_lt
  exact ⟨tEnter, tExit, h_eval, h_lt⟩


theorem rayMarchStep_Y_pos_pos_sound (A B : Point) (c : Cell)
    (hdx : 0 < B.x - A.x) (hdy : 0 < B.y - A.y)
    (hc_bbox : inBoundingBox c A B = true)
    (hc_int : ∃ tEnter tExit, cellIntersectionInterval c A B = some (tEnter, tExit) ∧ tEnter < tExit)
    (h_step : remY_val A 1 c * absVal (B.x - A.x) < remX_val A 1 c * absVal (B.y - A.y))
    (h_not_done : min (remX_val A 1 c * absVal (B.y - A.y)) (remY_val A 1 c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y)) :
    inBoundingBox ⟨c.x, c.y + 1⟩ A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval ⟨c.x, c.y + 1⟩ A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  have h_absDx : 0 < absVal (B.x - A.x) := by
    unfold absVal
    simp [le_of_lt hdx, hdx]
  have h_bnd := stepY_bounded (remY_val A 1 c) (absVal (B.x - A.x)) (absVal (B.y - A.y))
    (remX_val A 1 c * absVal (B.y - A.y)) h_absDx h_step h_not_done
  unfold absVal at h_bnd
  simp [le_of_lt hdy] at h_bnd
  unfold remY_val at h_bnd
  simp only [show (1 : ℤ) > 0 by decide, ↓reduceIte] at h_bnd
  have hc_prop := hc_bbox
  unfold inBoundingBox at hc_prop
  dsimp only [] at hc_prop
  simp only [Bool.and_eq_true, decide_eq_true_iff] at hc_prop
  have h_flA : (floorPoint A).x ≤ c.x := by
    have h_min := hc_prop.1.1.1
    have h_le : (floorPoint A).x ≤ (floorPoint B).x := by
      unfold floorPoint toInt; dsimp
      have : A.x ≤ B.x := by linarith
      exact floor_mono this
    rw [min_eq_left h_le] at h_min
    exact h_min
  have h_flAy : (floorPoint A).y ≤ c.y := by
    have h_min := hc_prop.1.2
    have h_le : (floorPoint A).y ≤ (floorPoint B).y := by
      unfold floorPoint toInt; dsimp
      have : A.y ≤ B.y := by linarith
      exact floor_mono this
    rw [min_eq_left h_le] at h_min
    exact h_min
  have h_ge : ofInt (c.x + 1) ≥ A.x := by
    unfold floorPoint toInt at h_flA; dsimp at h_flA
    have h_lt := Rat.lt_floor_add_one A.x
    push_cast at h_lt
    have h_flA_rat : ((A.x.floor : ℤ) : ℚ) ≤ (c.x : ℚ) := Int.cast_le.mpr h_flA
    have h_ofInt : ofInt (c.x + 1) = (c.x : ℚ) + 1 := by
      unfold ofInt; change ((c.x + 1 : ℤ) : ℚ) = (c.x : ℚ) + 1; push_cast; ring
    rw [h_ofInt]
    linarith
  have h_remY_ge : ofInt (c.y + 1) ≥ A.y := by
    unfold floorPoint toInt at h_flAy; dsimp at h_flAy
    have h_lt := Rat.lt_floor_add_one A.y
    push_cast at h_lt
    have h_flAy_rat : ((A.y.floor : ℤ) : ℚ) ≤ (c.y : ℚ) := Int.cast_le.mpr h_flAy
    have h_ofInt : ofInt (c.y + 1) = (c.y : ℚ) + 1 := by
      unfold ofInt; change ((c.y + 1 : ℤ) : ℚ) = (c.y : ℚ) + 1; push_cast; ring
    rw [h_ofInt]
    linarith
  simp only [h_remY_ge, ↓reduceIte] at h_bnd
  have h_le := stepY_next_le_end c.y A.y B.y h_bnd
  have h_bbox_next := inBoundingBox_stepY_forward c A B hdy hc_bbox h_le
  refine ⟨h_bbox_next, ?_⟩
  rcases hc_int with ⟨tEnter_c, tExit_c, hc_inter, _⟩
  have h_dx_prop := interval_dx_pos c A B tEnter_c tExit_c hc_inter hdx
  have h_dy_prop := interval_dy_pos c A B tEnter_c tExit_c hc_inter hdy
  unfold remY_val absVal at h_step
  simp only [show (1 : ℤ) > 0 by decide, ↓reduceIte, le_of_lt hdy, le_of_lt hdx, h_remY_ge] at h_step
  unfold remX_val at h_step
  simp only [show (1 : ℤ) > 0 by decide, ↓reduceIte, h_ge] at h_step
  let tx0 := (ofInt c.x - A.x) / (B.x - A.x)
  let tx1 := (ofInt (c.x + 1) - A.x) / (B.x - A.x)
  let ty1 := (ofInt (c.y + 1) - A.y) / (B.y - A.y)
  have h_cross : ty1 < tx1 := by
    dsimp [tx1, ty1]
    exact (cross_lt_cross_iff_div_lt_div (ofInt (c.y + 1) - A.y) (ofInt (c.x + 1) - A.x) (B.y - A.y) (B.x - A.x) hdy hdx).mp h_step
  have h_lim : ty1 < 1 := by
    dsimp [ty1]
    exact (div_lt_one hdy).mpr h_bnd
  have h_pos' : 0 ≤ ty1 := by
    dsimp [ty1]
    exact div_nonneg (by linarith) (le_of_lt hdy)
  have h_tx0 : tx0 ≤ ty1 := by
    dsimp [tx0, ty1]
    linarith [h_dx_prop.1, h_dy_prop.2]
  have h_lt := stepY_interval_lt ty1 tx0 tx1 (B.y - A.y) hdy h_cross h_lim h_pos' h_tx0
  let tEnter := max 0 (max tx0 ty1)
  let tExit := min 1 (min tx1 (ty1 + 1 / (B.y - A.y)))
  have h_eval := cellIntersectionInterval_stepY_pos A B c hdx hdy h_lt
  exact ⟨tEnter, tExit, h_eval, h_lt⟩


theorem rayMarchStep_Diag_pos_pos_sound (A B : Point) (c : Cell)
    (hdx : 0 < B.x - A.x) (hdy : 0 < B.y - A.y)
    (hc_bbox : inBoundingBox c A B = true)
    (_hc_int : ∃ tEnter tExit, cellIntersectionInterval c A B = some (tEnter, tExit) ∧ tEnter < tExit)
    (h_step : remX_val A 1 c * absVal (B.y - A.y) = remY_val A 1 c * absVal (B.x - A.x))
    (h_not_done : min (remX_val A 1 c * absVal (B.y - A.y)) (remY_val A 1 c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y)) :
    inBoundingBox ⟨c.x + 1, c.y + 1⟩ A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval ⟨c.x + 1, c.y + 1⟩ A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  have h_absDx : 0 < absVal (B.x - A.x) := by
    unfold absVal
    simp [le_of_lt hdx, hdx]
  have h_absDy : 0 < absVal (B.y - A.y) := by
    unfold absVal
    simp [le_of_lt hdy, hdy]
  have ⟨h_bndX, h_bndY⟩ := stepDiag_bounded (remX_val A 1 c) (remY_val A 1 c) (absVal (B.x - A.x)) (absVal (B.y - A.y))
    h_absDx h_absDy h_step h_not_done
  unfold absVal at h_bndX h_bndY
  simp [le_of_lt hdx] at h_bndX
  simp [le_of_lt hdy] at h_bndY
  unfold remX_val at h_bndX
  unfold remY_val at h_bndY
  simp only [show (1 : ℤ) > 0 by decide, ↓reduceIte] at h_bndX h_bndY
  have hc_prop := hc_bbox
  unfold inBoundingBox at hc_prop
  dsimp only [] at hc_prop
  simp only [Bool.and_eq_true, decide_eq_true_iff] at hc_prop
  have h_flA : (floorPoint A).x ≤ c.x := by
    have h_min := hc_prop.1.1.1
    have h_le : (floorPoint A).x ≤ (floorPoint B).x := by
      unfold floorPoint toInt; dsimp
      have : A.x ≤ B.x := by linarith
      exact floor_mono this
    rw [min_eq_left h_le] at h_min
    exact h_min
  have h_flAy : (floorPoint A).y ≤ c.y := by
    have h_min := hc_prop.1.2
    have h_le : (floorPoint A).y ≤ (floorPoint B).y := by
      unfold floorPoint toInt; dsimp
      have : A.y ≤ B.y := by linarith
      exact floor_mono this
    rw [min_eq_left h_le] at h_min
    exact h_min
  have h_ge : ofInt (c.x + 1) ≥ A.x := by
    unfold floorPoint toInt at h_flA; dsimp at h_flA
    have h_lt := Rat.lt_floor_add_one A.x
    push_cast at h_lt
    have h_flA_rat : ((A.x.floor : ℤ) : ℚ) ≤ (c.x : ℚ) := Int.cast_le.mpr h_flA
    have h_ofInt : ofInt (c.x + 1) = (c.x : ℚ) + 1 := by
      unfold ofInt; change ((c.x + 1 : ℤ) : ℚ) = (c.x : ℚ) + 1; push_cast; ring
    rw [h_ofInt]
    linarith
  have h_remY_ge : ofInt (c.y + 1) ≥ A.y := by
    unfold floorPoint toInt at h_flAy; dsimp at h_flAy
    have h_lt := Rat.lt_floor_add_one A.y
    push_cast at h_lt
    have h_flAy_rat : ((A.y.floor : ℤ) : ℚ) ≤ (c.y : ℚ) := Int.cast_le.mpr h_flAy
    have h_ofInt : ofInt (c.y + 1) = (c.y : ℚ) + 1 := by
      unfold ofInt; change ((c.y + 1 : ℤ) : ℚ) = (c.y : ℚ) + 1; push_cast; ring
    rw [h_ofInt]
    linarith
  simp only [h_ge, ↓reduceIte] at h_bndX
  simp only [h_remY_ge, ↓reduceIte] at h_bndY
  have h_leX := stepX_next_le_end c.x A.x B.x h_bndX
  have h_leY := stepY_next_le_end c.y A.y B.y h_bndY
  have h_bboxX := inBoundingBox_stepX_forward c A B hdx hc_bbox h_leX
  have h_bboxY := inBoundingBox_stepY_forward c A B hdy hc_bbox h_leY
  have h_bbox_next := inBoundingBox_diag c A B 1 1 h_bboxX h_bboxY
  refine ⟨h_bbox_next, ?_⟩
  unfold remX_val remY_val absVal at h_step
  simp only [show (1 : ℤ) > 0 by decide, ↓reduceIte, le_of_lt hdy, le_of_lt hdx, h_ge, h_remY_ge] at h_step
  let t := (ofInt (c.x + 1) - A.x) / (B.x - A.x)
  have h_cross : t = (ofInt (c.y + 1) - A.y) / (B.y - A.y) := by
    dsimp [t]
    exact (cross_eq_cross_iff_div_eq_div (ofInt (c.x + 1) - A.x) (ofInt (c.y + 1) - A.y) (B.x - A.x) (B.y - A.y) hdx hdy).mp h_step
  have h_lim : t < 1 := by
    dsimp [t]
    exact (div_lt_one hdx).mpr h_bndX
  have h_pos : 0 ≤ t := by
    dsimp [t]
    exact div_nonneg (by linarith) (le_of_lt hdx)
  have h_lt := stepDiag_interval_lt t (B.x - A.x) (B.y - A.y) hdx hdy h_lim h_pos
  let tEnter := max 0 (max t t)
  let tExit := min 1 (min (t + 1 / (B.x - A.x)) (t + 1 / (B.y - A.y)))
  have h_eval := cellIntersectionInterval_diag_pos A B c hdx hdy h_cross h_lt
  exact ⟨tEnter, tExit, h_eval, h_lt⟩


theorem cellIntersectionInterval_startCell_pos_pos (A B : Point)
    (hdx : 0 < B.x - A.x) (hdy : 0 < B.y - A.y) :
    ∃ tEnter tExit, cellIntersectionInterval (floorPoint A) A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  unfold cellIntersectionInterval
  dsimp only []
  have h_dx_ne : (B.x - A.x == 0) = false := by
    cases h : (B.x - A.x == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_dy_ne : (B.y - A.y == 0) = false := by
    cases h : (B.y - A.y == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  simp only [h_dx_ne, h_dy_ne, hdx, hdy, Bool.false_eq_true, ↓reduceIte]
  have h_flA : ((floorPoint A).x : ℚ) ≤ A.x := by
    unfold floorPoint toInt; dsimp
    exact Rat.floor_le A.x
  have h_flAy : ((floorPoint A).y : ℚ) ≤ A.y := by
    unfold floorPoint toInt; dsimp
    exact Rat.floor_le A.y
  have h_ltX : A.x < ((floorPoint A).x : ℚ) + 1 := by
    unfold floorPoint toInt; dsimp
    have := Rat.lt_floor_add_one A.x
    push_cast at this
    exact this
  have h_ltY : A.y < ((floorPoint A).y : ℚ) + 1 := by
    unfold floorPoint toInt; dsimp
    have := Rat.lt_floor_add_one A.y
    push_cast at this
    exact this
  have h_ofIntX0 : ofInt (floorPoint A).x = ((floorPoint A).x : ℚ) := rfl
  have h_ofIntX1 : ofInt ((floorPoint A).x + 1) = ((floorPoint A).x : ℚ) + 1 := by
    unfold ofInt; change (((floorPoint A).x + 1 : ℤ) : ℚ) = ((floorPoint A).x : ℚ) + 1; push_cast; ring
  have h_ofIntY0 : ofInt (floorPoint A).y = ((floorPoint A).y : ℚ) := rfl
  have h_ofIntY1 : ofInt ((floorPoint A).y + 1) = ((floorPoint A).y : ℚ) + 1 := by
    unfold ofInt; change (((floorPoint A).y + 1 : ℤ) : ℚ) = ((floorPoint A).y : ℚ) + 1; push_cast; ring
  rw [h_ofIntX0, h_ofIntX1, h_ofIntY0, h_ofIntY1]
  let tx0 := (((floorPoint A).x : ℚ) - A.x) / (B.x - A.x)
  let tx1 := (((floorPoint A).x : ℚ) + 1 - A.x) / (B.x - A.x)
  let ty0 := (((floorPoint A).y : ℚ) - A.y) / (B.y - A.y)
  let ty1 := (((floorPoint A).y : ℚ) + 1 - A.y) / (B.y - A.y)
  have h_tx0_nonpos : tx0 ≤ 0 := by
    dsimp [tx0]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hdx)
  have h_ty0_nonpos : ty0 ≤ 0 := by
    dsimp [ty0]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hdy)
  have h_tx1_pos : 0 < tx1 := by
    dsimp [tx1]
    exact div_pos (by linarith) hdx
  have h_ty1_pos : 0 < ty1 := by
    dsimp [ty1]
    exact div_pos (by linarith) hdy
  have h_enter : max 0 (max tx0 ty0) = 0 := by
    have : max tx0 ty0 ≤ 0 := max_le h_tx0_nonpos h_ty0_nonpos
    exact max_eq_left this
  have h_exit_pos : 0 < min 1 (min tx1 ty1) := by
    rw [lt_min_iff]
    refine ⟨by linarith, ?_⟩
    rw [lt_min_iff]
    exact ⟨h_tx1_pos, h_ty1_pos⟩
  have h_le : max 0 (max tx0 ty0) ≤ min 1 (min tx1 ty1) := by
    rw [h_enter]
    exact le_of_lt h_exit_pos
  change ∃ tEnter tExit, (if max 0 (max tx0 ty0) ≤ min 1 (min tx1 ty1) then some (max 0 (max tx0 ty0), min 1 (min tx1 ty1)) else none) = some (tEnter, tExit) ∧ tEnter < tExit
  simp only [h_le, ↓reduceIte]
  refine ⟨max 0 (max tx0 ty0), min 1 (min tx1 ty1), rfl, ?_⟩
  rw [h_enter]
  exact h_exit_pos


theorem rayMarchStep_sound_step_pos_pos (A B : Point) (dx dy : ℚ) (stepX stepY : ℤ) (c : Cell)
    (hdx : dx = B.x - A.x) (hdy : dy = B.y - A.y)
    (hstepX : stepX = if dx > 0 then 1 else if dx < 0 then -1 else 0)
    (hstepY : stepY = if dy > 0 then 1 else if dy < 0 then -1 else 0)
    (h_pos : 0 < dx ∧ 0 < dy)
    (hc : inBoundingBox c A B = true ∧ ∃ tEnter tExit, cellIntersectionInterval c A B = some (tEnter, tExit) ∧ tEnter < tExit)
    (h_not_done : (rayMarchStep A B dx dy stepX stepY c).2 = false) :
    inBoundingBox (rayMarchStep A B dx dy stepX stepY c).1 A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval (rayMarchStep A B dx dy stepX stepY c).1 A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  have hsx : stepX = 1 := by rw [hstepX]; simp [h_pos.1]
  have hsy : stepY = 1 := by rw [hstepY]; simp [h_pos.2]
  have h_cases := rayMarchStep_cases A B dx dy stepX stepY c
  rcases h_cases with h1 | h2 | h3 | h4
  · rw [h1] at h_not_done
    contradiction
  · rw [h2]
    dsimp only []
    have h_step_eq : rayMarchStep A B (B.x - A.x) (B.y - A.y) 1 1 c = (⟨c.x + 1, c.y⟩, false) := by
      subst hdx; subst hdy; subst hsx; subst hsy; exact h2
    have ⟨h_step, h_lim⟩ := extract_stepX_pos_pos A B c (by linarith) (by linarith) h_step_eq
    rw [hsx]
    exact rayMarchStep_X_pos_pos_sound A B c (by linarith) (by linarith) hc.1 hc.2 h_step h_lim
  · rw [h3]
    dsimp only []
    have h_step_eq : rayMarchStep A B (B.x - A.x) (B.y - A.y) 1 1 c = (⟨c.x, c.y + 1⟩, false) := by
      subst hdx; subst hdy; subst hsx; subst hsy; exact h3
    have ⟨h_step, h_lim⟩ := extract_stepY_pos_pos A B c (by linarith) (by linarith) h_step_eq
    rw [hsy]
    exact rayMarchStep_Y_pos_pos_sound A B c (by linarith) (by linarith) hc.1 hc.2 h_step h_lim
  · rw [h4]
    dsimp only []
    have h_step_eq : rayMarchStep A B (B.x - A.x) (B.y - A.y) 1 1 c = (⟨c.x + 1, c.y + 1⟩, false) := by
      subst hdx; subst hdy; subst hsx; subst hsy; exact h4
    have ⟨h_step, h_lim⟩ := extract_stepDiag_pos_pos A B c (by linarith) (by linarith) h_step_eq
    rw [hsx, hsy]
    exact rayMarchStep_Diag_pos_pos_sound A B c (by linarith) (by linarith) hc.1 hc.2 h_step h_lim


theorem rayMarchStep_sound_base_pos_pos (A B : Point) (dx dy : ℚ) (stepX stepY : ℤ)
    (hdx : dx = B.x - A.x) (hdy : dy = B.y - A.y)
    (hstepX : stepX = if dx > 0 then 1 else if dx < 0 then -1 else 0)
    (hstepY : stepY = if dy > 0 then 1 else if dy < 0 then -1 else 0)
    (h_pos : 0 < dx ∧ 0 < dy)
    (h_not_done : (rayMarchStep A B dx dy stepX stepY (floorPoint A)).2 = false) :
    inBoundingBox (rayMarchStep A B dx dy stepX stepY (floorPoint A)).1 A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval (rayMarchStep A B dx dy stepX stepY (floorPoint A)).1 A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  have h_bbox := inBoundingBox_startCell A B
  have h_inter := cellIntersectionInterval_startCell_pos_pos A B (by linarith) (by linarith)
  exact rayMarchStep_sound_step_pos_pos A B dx dy stepX stepY (floorPoint A) hdx hdy hstepX hstepY h_pos ⟨h_bbox, h_inter⟩ h_not_done



theorem rayMarch_soundness_pos_pos (A B : Point) (x : Cell)
    (hdx : 0 < B.x - A.x) (hdy : 0 < B.y - A.y)
    (hx : x ∈ rayMarch (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 2)
      A B (B.x - A.x) (B.y - A.y)
      (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0)
      (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0)
      (floorPoint B) (floorPoint A) []) :
    inBoundingBox x A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval x A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  have hsx : (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else (0 : ℤ)) = 1 := by simp [hdx]
  have hsy : (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else (0 : ℤ)) = 1 := by simp [hdy]
  rw [hsx, hsy] at hx
  have h_fuel : (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 2) =
    (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 1) + 1 := by omega
  rw [h_fuel] at hx
  apply sound_from_first_step _ _ _ _ _ _ _ (floorPoint B) (fun cell =>
    inBoundingBox cell A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval cell A B = some (tEnter, tExit) ∧ tEnter < tExit)
    _ _ x hx
  · intro c hc h_not_done
    have h_res := rayMarchStep_sound_step_pos_pos A B (B.x - A.x) (B.y - A.y) 1 1 c rfl rfl (by simp [hdx]) (by simp [hdy]) ⟨hdx, hdy⟩ hc h_not_done
    exact h_res
  · intro h_not_done
    have h_res := rayMarchStep_sound_base_pos_pos A B (B.x - A.x) (B.y - A.y) 1 1 rfl rfl (by simp [hdx]) (by simp [hdy]) ⟨hdx, hdy⟩ h_not_done
    exact h_res


/- =========================================================================
   Quadrant 2: dx > 0, dy < 0
   ========================================================================= -/

theorem inBoundingBox_diag_pos_neg (c : Cell) (A B : Point)
    (hdx : 0 < B.x - A.x) (hdy : B.y - A.y < 0)
    (h_bbox : inBoundingBox c A B = true)
    (h_next_x : c.x + 1 ≤ (floorPoint B).x)
    (h_next_y : (floorPoint B).y ≤ c.y - 1) :
    inBoundingBox ⟨c.x + 1, c.y - 1⟩ A B = true := by
  have h1 := inBoundingBox_stepX_forward c A B hdx h_bbox h_next_x
  exact inBoundingBox_stepY_backward ⟨c.x + 1, c.y⟩ A B hdy h1 h_next_y


theorem stepDiag_interval_lt_pos_neg (t dx dy : ℚ) (dx_pos : 0 < dx) (dy_neg : dy < 0)
    (h_lim : t < 1)
    (h_pos : 0 ≤ t) :
    max 0 (max t t) < min 1 (min (t + 1 / dx) (t - 1 / dy)) := by
  have h_enter : max 0 (max t t) = t := by
    rw [max_self]
    exact max_eq_right h_pos
  rw [h_enter]
  have h1 : t < 1 := h_lim
  have h2 : t < t + 1 / dx := by
    have : 0 < 1 / dx := one_div_pos.mpr dx_pos
    linarith
  have h3 : t < t - 1 / dy := by
    have h_neg_dy : 0 < -dy := by linarith
    have h_inv : 0 < 1 / -dy := one_div_pos.mpr h_neg_dy
    have h_eq : -1 / dy = 1 / -dy := by ring
    linarith
  rw [lt_min_iff]
  refine ⟨h1, ?_⟩
  rw [lt_min_iff]
  exact ⟨h2, h3⟩


theorem cellIntersectionInterval_stepX_pos_neg (A B : Point) (c : Cell)
    (hdx : 0 < B.x - A.x) (hdy : B.y - A.y < 0) :
    let dx := B.x - A.x
    let dy := B.y - A.y
    let tx1 := (ofInt (c.x + 1) - A.x) / dx
    let ty0 := (ofInt (c.y + 1) - A.y) / dy
    let ty1 := (ofInt c.y - A.y) / dy
    let tEnter := max 0 (max tx1 ty0)
    let tExit := min 1 (min (tx1 + 1 / dx) ty1)
    tEnter < tExit →
    cellIntersectionInterval ⟨c.x + 1, c.y⟩ A B = some (tEnter, tExit) := by
  intro dx dy tx1 ty0 ty1 tEnter tExit h_lt
  unfold cellIntersectionInterval
  dsimp only []
  have h_dx_ne : (B.x - A.x == 0) = false := by
    cases h : (B.x - A.x == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_dy_ne : (B.y - A.y == 0) = false := by
    cases h : (B.y - A.y == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_not_dy_pos : ¬(B.y - A.y > 0) := by linarith
  simp only [h_dx_ne, h_dy_ne, hdx, h_not_dy_pos, ↓reduceIte]
  have h_cx1 : ofInt (c.x + 1 + 1) = ofInt (c.x + 1) + 1 := by
    unfold ofInt
    change ((c.x + 1 + 1 : ℤ) : ℚ) = ((c.x + 1 : ℤ) : ℚ) + 1
    push_cast
    ring
  rw [h_cx1]
  have h_divx : (ofInt (c.x + 1) + 1 - A.x) / (B.x - A.x) = tx1 + 1 / dx := by
    dsimp [tx1, dx]
    ring
  rw [h_divx]
  simp only [Bool.false_eq_true, ↓reduceIte]
  change (if tEnter ≤ tExit then some (tEnter, tExit) else none) = some (tEnter, tExit)
  have h_le : tEnter ≤ tExit := le_of_lt h_lt
  simp only [h_le, ↓reduceIte]


theorem cellIntersectionInterval_stepY_pos_neg (A B : Point) (c : Cell)
    (hdx : 0 < B.x - A.x) (hdy : B.y - A.y < 0) :
    let dx := B.x - A.x
    let dy := B.y - A.y
    let tx0 := (ofInt c.x - A.x) / dx
    let tx1 := (ofInt (c.x + 1) - A.x) / dx
    let ty1 := (ofInt c.y - A.y) / dy
    let tEnter := max 0 (max tx0 ty1)
    let tExit := min 1 (min tx1 (ty1 - 1 / dy))
    tEnter < tExit →
    cellIntersectionInterval ⟨c.x, c.y - 1⟩ A B = some (tEnter, tExit) := by
  intro dx dy tx0 tx1 ty1 tEnter tExit h_lt
  unfold cellIntersectionInterval
  dsimp only []
  have h_dx_ne : (B.x - A.x == 0) = false := by
    cases h : (B.x - A.x == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_dy_ne : (B.y - A.y == 0) = false := by
    cases h : (B.y - A.y == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_not_dy_pos : ¬(B.y - A.y > 0) := by linarith
  simp only [h_dx_ne, h_dy_ne, hdx, h_not_dy_pos, ↓reduceIte]
  have h_cy1 : ofInt (c.y - 1 + 1) = ofInt c.y := by
    unfold ofInt
    congr 1
    omega
  have h_cy0 : ofInt (c.y - 1) = ofInt c.y - 1 := by
    unfold ofInt
    change ((c.y - 1 : ℤ) : ℚ) = ((c.y : ℤ) : ℚ) - 1
    push_cast
    ring
  rw [h_cy1, h_cy0]
  have h_divy : (ofInt c.y - 1 - A.y) / (B.y - A.y) = ty1 - 1 / dy := by
    dsimp [ty1, dy]
    ring
  rw [h_divy]
  simp only [Bool.false_eq_true, ↓reduceIte]
  change (if tEnter ≤ tExit then some (tEnter, tExit) else none) = some (tEnter, tExit)
  have h_le : tEnter ≤ tExit := le_of_lt h_lt
  simp only [h_le, ↓reduceIte]


theorem cellIntersectionInterval_diag_pos_neg (A B : Point) (c : Cell)
    (hdx : 0 < B.x - A.x) (hdy : B.y - A.y < 0) :
    let dx := B.x - A.x
    let dy := B.y - A.y
    let t := (ofInt (c.x + 1) - A.x) / dx
    let tEnter := max 0 (max t t)
    let tExit := min 1 (min (t + 1 / dx) (t - 1 / dy))
    t = (ofInt c.y - A.y) / dy →
    tEnter < tExit →
    cellIntersectionInterval ⟨c.x + 1, c.y - 1⟩ A B = some (tEnter, tExit) := by
  intro dx dy t tEnter tExit h_eq h_lt
  unfold cellIntersectionInterval
  dsimp only []
  have h_dx_ne : (B.x - A.x == 0) = false := by
    cases h : (B.x - A.x == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_dy_ne : (B.y - A.y == 0) = false := by
    cases h : (B.y - A.y == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_not_dy_pos : ¬(B.y - A.y > 0) := by linarith
  simp only [h_dx_ne, h_dy_ne, hdx, h_not_dy_pos, ↓reduceIte]
  have h_cx1 : ofInt (c.x + 1 + 1) = ofInt (c.x + 1) + 1 := by
    unfold ofInt
    change ((c.x + 1 + 1 : ℤ) : ℚ) = ((c.x + 1 : ℤ) : ℚ) + 1
    push_cast
    ring
  have h_cy1 : ofInt (c.y - 1 + 1) = ofInt c.y := by
    unfold ofInt
    congr 1
    omega
  have h_cy0 : ofInt (c.y - 1) = ofInt c.y - 1 := by
    unfold ofInt
    change ((c.y - 1 : ℤ) : ℚ) = ((c.y : ℤ) : ℚ) - 1
    push_cast
    ring
  rw [h_cx1, h_cy1, h_cy0]
  have h_divx : (ofInt (c.x + 1) + 1 - A.x) / (B.x - A.x) = t + 1 / dx := by
    dsimp [t, dx]
    ring
  have h_divy : (ofInt c.y - 1 - A.y) / (B.y - A.y) = t - 1 / dy := by
    have h_split : (ofInt c.y - 1 - A.y) / (B.y - A.y) =
        (ofInt c.y - A.y) / (B.y - A.y) - 1 / (B.y - A.y) := by ring
    rw [h_split]
    dsimp [dy]
    rw [← h_eq]
  rw [h_divx, h_divy]
  have h_ty : (ofInt c.y - A.y) / (B.y - A.y) = t := by
    dsimp [dy] at h_eq
    exact h_eq.symm
  rw [h_ty]
  simp only [Bool.false_eq_true, ↓reduceIte]
  change (if tEnter ≤ tExit then some (tEnter, tExit) else none) = some (tEnter, tExit)
  have h_le : tEnter ≤ tExit := le_of_lt h_lt
  simp only [h_le, ↓reduceIte]


theorem extract_stepX_pos_neg (A B : Point) (c : Cell)
    (_hdx : 0 < B.x - A.x) (_hdy : B.y - A.y < 0)
    (h_step : rayMarchStep A B (B.x - A.x) (B.y - A.y) 1 (-1) c = (⟨c.x + 1, c.y⟩, false)) :
    remX_val A 1 c * absVal (B.y - A.y) < remY_val A (-1) c * absVal (B.x - A.x) ∧
    min (remX_val A 1 c * absVal (B.y - A.y)) (remY_val A (-1) c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y) := by
  unfold rayMarchStep at h_step; dsimp only [] at h_step
  simp only [show ((1 : ℤ) == 0) = false by decide, Bool.false_eq_true, ↓reduceIte] at h_step
  by_cases hlim : min
        ((if (if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y))
        ((if (if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) ≥
      (if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) * if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
  · simp only [hlim, ↓reduceIte] at h_step; injection h_step with _ h_bool; contradiction
  · simp only [hlim, ↓reduceIte] at h_step
    by_cases hxy : ((if (if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)) <
        (if (if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)
    · unfold remX_val remY_val absVal; dsimp only []
      simp only [show (1 : ℤ) > 0 by decide, show ¬((-1 : ℤ) > 0) by decide, ↓reduceIte]
      refine ⟨hxy, not_le.mp hlim⟩
    · simp only [hxy, ↓reduceIte] at h_step
      by_cases hyx : ((if (if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
              (if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
            else A.y - if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) *
            if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) <
          (if (if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
              (if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
            else A.x - if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) *
            if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
      · simp only [hyx, ↓reduceIte] at h_step; injection h_step with h_cell _; injection h_cell with hx _; omega
      · simp only [hyx, ↓reduceIte] at h_step; injection h_step with h_cell _; injection h_cell with _ hy; omega


theorem extract_stepY_pos_neg (A B : Point) (c : Cell)
    (_hdx : 0 < B.x - A.x) (_hdy : B.y - A.y < 0)
    (h_step : rayMarchStep A B (B.x - A.x) (B.y - A.y) 1 (-1) c = (⟨c.x, c.y - 1⟩, false)) :
    remY_val A (-1) c * absVal (B.x - A.x) < remX_val A 1 c * absVal (B.y - A.y) ∧
    min (remX_val A 1 c * absVal (B.y - A.y)) (remY_val A (-1) c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y) := by
  unfold rayMarchStep at h_step; dsimp only [] at h_step
  simp only [show ((1 : ℤ) == 0) = false by decide, Bool.false_eq_true, ↓reduceIte] at h_step
  by_cases hlim : min
        ((if (if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y))
        ((if (if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) ≥
      (if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) * if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
  · simp only [hlim, ↓reduceIte] at h_step; injection h_step with _ h_bool; contradiction
  · simp only [hlim, ↓reduceIte] at h_step
    by_cases hxy : ((if (if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)) <
        (if (if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)
    · simp only [hxy, ↓reduceIte] at h_step; injection h_step with h_cell _; injection h_cell with _ hy; omega
    · simp only [hxy, ↓reduceIte] at h_step
      by_cases hyx : ((if (if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
              (if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
            else A.y - if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) *
            if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) <
          (if (if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
              (if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
            else A.x - if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) *
            if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
      · unfold remX_val remY_val absVal; dsimp only []
        simp only [show (1 : ℤ) > 0 by decide, show ¬((-1 : ℤ) > 0) by decide, ↓reduceIte]
        refine ⟨hyx, not_le.mp hlim⟩
      · simp only [hyx, ↓reduceIte] at h_step; injection h_step with h_cell _; injection h_cell with hx _; omega


theorem extract_stepDiag_pos_neg (A B : Point) (c : Cell)
    (_hdx : 0 < B.x - A.x) (_hdy : B.y - A.y < 0)
    (h_step : rayMarchStep A B (B.x - A.x) (B.y - A.y) 1 (-1) c = (⟨c.x + 1, c.y - 1⟩, false)) :
    remX_val A 1 c * absVal (B.y - A.y) = remY_val A (-1) c * absVal (B.x - A.x) ∧
    min (remX_val A 1 c * absVal (B.y - A.y)) (remY_val A (-1) c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y) := by
  unfold rayMarchStep at h_step; dsimp only [] at h_step
  simp only [show ((1 : ℤ) == 0) = false by decide, Bool.false_eq_true, ↓reduceIte] at h_step
  by_cases hlim : min
        ((if (if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y))
        ((if (if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) ≥
      (if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) * if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
  · simp only [hlim, ↓reduceIte] at h_step; injection h_step with _ h_bool; contradiction
  · simp only [hlim, ↓reduceIte] at h_step
    by_cases hxy : ((if (if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)) <
        (if (if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)
    · simp only [hxy, ↓reduceIte] at h_step; injection h_step with h_cell _; injection h_cell with _ hy; omega
    · simp only [hxy, ↓reduceIte] at h_step
      by_cases hyx : ((if (if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
              (if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
            else A.y - if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) *
            if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) <
          (if (if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
              (if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
            else A.x - if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) *
            if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
      · simp only [hyx, ↓reduceIte] at h_step; injection h_step with h_cell _; injection h_cell with hx _; omega
      · unfold remX_val remY_val absVal; dsimp only []
        simp only [show (1 : ℤ) > 0 by decide, show ¬((-1 : ℤ) > 0) by decide, ↓reduceIte] at *
        refine ⟨by linarith, not_le.mp hlim⟩


theorem rayMarchStep_X_pos_neg_sound (A B : Point) (c : Cell)
    (hdx : 0 < B.x - A.x) (hdy : B.y - A.y < 0)
    (hc_bbox : inBoundingBox c A B = true)
    (hc_valid : c = floorPoint A ∨ ∃ tEnter tExit, cellIntersectionInterval c A B = some (tEnter, tExit) ∧ tEnter < tExit)
    (h_step : remX_val A 1 c * absVal (B.y - A.y) < remY_val A (-1) c * absVal (B.x - A.x))
    (h_not_done : min (remX_val A 1 c * absVal (B.y - A.y)) (remY_val A (-1) c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y)) :
    inBoundingBox ⟨c.x + 1, c.y⟩ A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval ⟨c.x + 1, c.y⟩ A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  have h_absDy : 0 < absVal (B.y - A.y) := by
    unfold absVal; split_ifs <;> linarith
  have h_bnd := stepX_bounded (remX_val A 1 c) (absVal (B.x - A.x)) (absVal (B.y - A.y))
    (remY_val A (-1) c * absVal (B.x - A.x)) h_absDy h_step h_not_done
  unfold absVal at h_bnd; simp [le_of_lt hdx] at h_bnd
  unfold remX_val at h_bnd; simp only [show (1 : ℤ) > 0 by decide, ↓reduceIte] at h_bnd
  have hc_prop := hc_bbox; unfold inBoundingBox at hc_prop; dsimp only [] at hc_prop
  simp only [Bool.and_eq_true, decide_eq_true_iff] at hc_prop
  have h_flA : (floorPoint A).x ≤ c.x := by
    have h_min := hc_prop.1.1.1
    have h_le : (floorPoint A).x ≤ (floorPoint B).x := floor_mono (by linarith)
    rw [min_eq_left h_le] at h_min; exact h_min
  have h_flAy : c.y ≤ (floorPoint A).y := by
    have h_max := hc_prop.2
    have h_le : (floorPoint B).y ≤ (floorPoint A).y := floor_mono (by linarith)
    have h_max_eq : max (floorPoint A).y (floorPoint B).y = (floorPoint A).y := max_eq_left h_le
    rw [h_max_eq] at h_max; exact h_max
  have h_ge : ofInt (c.x + 1) ≥ A.x := by
    unfold floorPoint toInt at h_flA; dsimp at h_flA
    have h_lt := Rat.lt_floor_add_one A.x; push_cast at h_lt
    have h_flA_rat : ((A.x.floor : ℤ) : ℚ) ≤ (c.x : ℚ) := Int.cast_le.mpr h_flA
    have h_ofInt : ofInt (c.x + 1) = (c.x : ℚ) + 1 := by
      unfold ofInt; change ((c.x + 1 : ℤ) : ℚ) = (c.x : ℚ) + 1; push_cast; ring
    rw [h_ofInt]; linarith
  have h_remY_ge : ofInt c.y ≤ A.y := by
    unfold floorPoint toInt at h_flAy; dsimp at h_flAy
    have h_le := Rat.floor_le A.y
    have h_flAy_rat : (c.y : ℚ) ≤ ((A.y.floor : ℤ) : ℚ) := Int.cast_le.mpr h_flAy
    have h_ofInt : ofInt c.y = (c.y : ℚ) := rfl
    rw [h_ofInt]; linarith
  simp only [h_ge, ↓reduceIte] at h_bnd
  have h_le := stepX_next_le_end c.x A.x B.x h_bnd
  have h_bbox_next := inBoundingBox_stepX_forward c A B hdx hc_bbox h_le
  refine ⟨h_bbox_next, ?_⟩
  unfold remY_val absVal at h_step
  simp only [show ¬((-1 : ℤ) > 0) by decide, ↓reduceIte, show ¬(B.y - A.y ≥ 0) by linarith, le_of_lt hdx] at h_step
  unfold remX_val at h_step
  simp only [show (1 : ℤ) > 0 by decide, ↓reduceIte, h_ge] at h_step
  have h_remY_split : (if ofInt c.y ≥ A.y then ofInt c.y - A.y else A.y - ofInt c.y) = A.y - ofInt c.y := by
    split_ifs with h <;> [linarith; rfl]
  rw [h_remY_split] at h_step
  let tx1 := (ofInt (c.x + 1) - A.x) / (B.x - A.x)
  let ty0 := (ofInt (c.y + 1) - A.y) / (B.y - A.y)
  let ty1 := (ofInt c.y - A.y) / (B.y - A.y)
  have h_ty1_eq : (A.y - ofInt c.y) / -(B.y - A.y) = ty1 := by
    dsimp [ty1]
    have h_num : A.y - ofInt c.y = -(ofInt c.y - A.y) := by ring
    rw [h_num, neg_div_neg_eq]
  have h_cross : tx1 < ty1 := by
    dsimp [tx1]
    rw [← h_ty1_eq]
    have h_pos_neg_dy : 0 < -(B.y - A.y) := by linarith
    exact (cross_lt_cross_iff_div_lt_div (ofInt (c.x + 1) - A.x) (A.y - ofInt c.y) (B.x - A.x) (-(B.y - A.y)) hdx h_pos_neg_dy).mp h_step
  have h_lim : tx1 < 1 := (div_lt_one hdx).mpr h_bnd
  have h_pos_val : 0 ≤ tx1 := div_nonneg (by linarith) (le_of_lt hdx)
  have h_ty0 : ty0 ≤ tx1 := by
    cases hc_valid with
    | inl h_cA =>
      subst h_cA; dsimp [tx1, ty0]
      have h1 : (ofInt ((floorPoint A).y + 1) - A.y) / (B.y - A.y) ≤ 0 := by
        unfold floorPoint toInt; dsimp
        have h_lt := Rat.lt_floor_add_one A.y; push_cast at h_lt
        have h_num : 0 < ofInt (A.y.floor + 1) - A.y := by
          unfold ofInt; change 0 < ((A.y.floor + 1 : ℤ) : ℚ) - A.y; push_cast; linarith
        exact div_nonpos_of_nonneg_of_nonpos (le_of_lt h_num) (le_of_lt hdy)
      linarith
    | inr h_int =>
      rcases h_int with ⟨tEnter_c, tExit_c, hc_inter, _⟩
      have h_dx_prop := interval_dx_pos c A B tEnter_c tExit_c hc_inter hdx
      have h_dy_prop := interval_dy_neg c A B tEnter_c tExit_c hc_inter hdy
      dsimp [tx1, ty0]; linarith [h_dy_prop.1, h_dx_prop.2]
  have h_lt := stepX_interval_lt tx1 ty0 ty1 (B.x - A.x) hdx h_cross h_lim h_pos_val h_ty0
  let tEnter := max 0 (max tx1 ty0)
  let tExit := min 1 (min (tx1 + 1 / (B.x - A.x)) ty1)
  have h_eval := cellIntersectionInterval_stepX_pos_neg A B c hdx hdy h_lt
  exact ⟨tEnter, tExit, h_eval, h_lt⟩


theorem rayMarchStep_Y_pos_neg_sound (A B : Point) (c : Cell)
    (hdx : 0 < B.x - A.x) (hdy : B.y - A.y < 0)
    (hc_bbox : inBoundingBox c A B = true)
    (hc_valid : c = floorPoint A ∨ ∃ tEnter tExit, cellIntersectionInterval c A B = some (tEnter, tExit) ∧ tEnter < tExit)
    (h_step : remY_val A (-1) c * absVal (B.x - A.x) < remX_val A 1 c * absVal (B.y - A.y))
    (h_not_done : min (remX_val A 1 c * absVal (B.y - A.y)) (remY_val A (-1) c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y)) :
    inBoundingBox ⟨c.x, c.y - 1⟩ A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval ⟨c.x, c.y - 1⟩ A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  have h_absDx : 0 < absVal (B.x - A.x) := by
    unfold absVal; split_ifs <;> linarith
  have h_bnd := stepY_bounded (remY_val A (-1) c) (absVal (B.x - A.x)) (absVal (B.y - A.y))
    (remX_val A 1 c * absVal (B.y - A.y)) h_absDx h_step h_not_done
  unfold absVal at h_bnd; simp [show ¬(B.y - A.y ≥ 0) by linarith] at h_bnd
  unfold remY_val at h_bnd; simp only [show ¬((-1 : ℤ) > 0) by decide, ↓reduceIte] at h_bnd
  have hc_prop := hc_bbox; unfold inBoundingBox at hc_prop; dsimp only [] at hc_prop
  simp only [Bool.and_eq_true, decide_eq_true_iff] at hc_prop
  have h_flA : (floorPoint A).x ≤ c.x := by
    have h_min := hc_prop.1.1.1
    have h_le : (floorPoint A).x ≤ (floorPoint B).x := floor_mono (by linarith)
    rw [min_eq_left h_le] at h_min; exact h_min
  have h_flAy : c.y ≤ (floorPoint A).y := by
    have h_max := hc_prop.2
    have h_le : (floorPoint B).y ≤ (floorPoint A).y := floor_mono (by linarith)
    have h_max_eq : max (floorPoint A).y (floorPoint B).y = (floorPoint A).y := max_eq_left h_le
    rw [h_max_eq] at h_max; exact h_max
  have h_ge : ofInt (c.x + 1) ≥ A.x := by
    unfold floorPoint toInt at h_flA; dsimp at h_flA
    have h_lt := Rat.lt_floor_add_one A.x; push_cast at h_lt
    have h_flA_rat : ((A.x.floor : ℤ) : ℚ) ≤ (c.x : ℚ) := Int.cast_le.mpr h_flA
    have h_ofInt : ofInt (c.x + 1) = (c.x : ℚ) + 1 := by
      unfold ofInt; change ((c.x + 1 : ℤ) : ℚ) = (c.x : ℚ) + 1; push_cast; ring
    rw [h_ofInt]; linarith
  have h_remY_ge : ofInt c.y ≤ A.y := by
    unfold floorPoint toInt at h_flAy; dsimp at h_flAy
    have h_le := Rat.floor_le A.y
    have h_flAy_rat : (c.y : ℚ) ≤ ((A.y.floor : ℤ) : ℚ) := Int.cast_le.mpr h_flAy
    have h_ofInt : ofInt c.y = (c.y : ℚ) := rfl
    rw [h_ofInt]; linarith
  have h_remY_split : (if ofInt c.y ≥ A.y then ofInt c.y - A.y else A.y - ofInt c.y) = A.y - ofInt c.y := by
    split_ifs with h <;> [linarith; rfl]
  rw [h_remY_split] at h_bnd
  have h_div_bnd : (ofInt c.y - A.y) / (B.y - A.y) < 1 := by
    have h_lt_neg : A.y - ofInt c.y < -(B.y - A.y) := by linarith [h_bnd]
    have : (A.y - ofInt c.y) / -(B.y - A.y) < 1 := (div_lt_one (by linarith)).mpr h_lt_neg
    have h_num : A.y - ofInt c.y = -(ofInt c.y - A.y) := by ring
    rw [h_num, neg_div_neg_eq] at this; exact this
  have h_le := stepY_neg_next_ge_end c.y A.y B hdy h_div_bnd
  have h_bbox_next := inBoundingBox_stepY_backward c A B hdy hc_bbox h_le
  refine ⟨h_bbox_next, ?_⟩
  unfold remX_val absVal at h_step
  simp only [show (1 : ℤ) > 0 by decide, ↓reduceIte, le_of_lt hdx, show ¬(B.y - A.y ≥ 0) by linarith, h_ge] at h_step
  unfold remY_val at h_step
  simp only [show ¬((-1 : ℤ) > 0) by decide, ↓reduceIte] at h_step
  rw [h_remY_split] at h_step
  let tx0 := (ofInt c.x - A.x) / (B.x - A.x)
  let tx1 := (ofInt (c.x + 1) - A.x) / (B.x - A.x)
  let ty1 := (ofInt c.y - A.y) / (B.y - A.y)
  have h_ty1_eq : (A.y - ofInt c.y) / -(B.y - A.y) = ty1 := by
    dsimp [ty1]
    have h_num : A.y - ofInt c.y = -(ofInt c.y - A.y) := by ring
    rw [h_num, neg_div_neg_eq]
  have h_cross : ty1 < tx1 := by
    dsimp [tx1]; rw [← h_ty1_eq]
    have h_pos_neg_dy : 0 < -(B.y - A.y) := by linarith
    exact (cross_lt_cross_iff_div_lt_div (A.y - ofInt c.y) (ofInt (c.x + 1) - A.x) (-(B.y - A.y)) (B.x - A.x) h_pos_neg_dy hdx).mp h_step
  have h_lim : ty1 < 1 := h_div_bnd
  have h_pos_val : 0 ≤ ty1 := by rw [← h_ty1_eq]; exact div_nonneg (by linarith) (by linarith)
  have h_tx0 : tx0 ≤ ty1 := by
    cases hc_valid with
    | inl h_cA =>
      subst h_cA; dsimp [tx0, ty1]
      have h1 : (ofInt (floorPoint A).x - A.x) / (B.x - A.x) ≤ 0 := by
        unfold floorPoint toInt ofInt; dsimp
        have h_le := Rat.floor_le A.x
        exact div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hdx)
      linarith
    | inr h_int =>
      rcases h_int with ⟨tEnter_c, tExit_c, hc_inter, _⟩
      have h_dx_prop := interval_dx_pos c A B tEnter_c tExit_c hc_inter hdx
      have h_dy_prop := interval_dy_neg c A B tEnter_c tExit_c hc_inter hdy
      dsimp [tx0, ty1]; linarith [h_dx_prop.1, h_dy_prop.2]
  have h_lt := stepY_interval_lt_neg ty1 tx0 tx1 (B.y - A.y) hdy h_cross h_lim h_pos_val h_tx0
  let tEnter := max 0 (max tx0 ty1)
  let tExit := min 1 (min tx1 (ty1 - 1 / (B.y - A.y)))
  have h_eval := cellIntersectionInterval_stepY_pos_neg A B c hdx hdy h_lt
  exact ⟨tEnter, tExit, h_eval, h_lt⟩


theorem rayMarchStep_Diag_pos_neg_sound (A B : Point) (c : Cell)
    (hdx : 0 < B.x - A.x) (hdy : B.y - A.y < 0)
    (hc_bbox : inBoundingBox c A B = true)
    (_hc_valid : c = floorPoint A ∨ ∃ tEnter tExit, cellIntersectionInterval c A B = some (tEnter, tExit) ∧ tEnter < tExit)
    (h_step : remX_val A 1 c * absVal (B.y - A.y) = remY_val A (-1) c * absVal (B.x - A.x))
    (h_not_done : min (remX_val A 1 c * absVal (B.y - A.y)) (remY_val A (-1) c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y)) :
    inBoundingBox ⟨c.x + 1, c.y - 1⟩ A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval ⟨c.x + 1, c.y - 1⟩ A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  have h_absDx : 0 < absVal (B.x - A.x) := by
    unfold absVal; split_ifs <;> linarith
  have h_absDy : 0 < absVal (B.y - A.y) := by
    unfold absVal; split_ifs <;> linarith
  have ⟨h_bndX, h_bndY⟩ := stepDiag_bounded (remX_val A 1 c) (remY_val A (-1) c)
    (absVal (B.x - A.x)) (absVal (B.y - A.y)) h_absDx h_absDy h_step h_not_done
  unfold absVal at h_bndX h_bndY
  simp [le_of_lt hdx, show ¬(B.y - A.y ≥ 0) by linarith] at h_bndX h_bndY
  unfold remX_val at h_bndX
  unfold remY_val at h_bndY
  simp only [show (1 : ℤ) > 0 by decide, ↓reduceIte] at h_bndX
  simp only [show ¬((-1 : ℤ) > 0) by decide, ↓reduceIte] at h_bndY
  have hc_prop := hc_bbox; unfold inBoundingBox at hc_prop; dsimp only [] at hc_prop
  simp only [Bool.and_eq_true, decide_eq_true_iff] at hc_prop
  have h_flA : (floorPoint A).x ≤ c.x := by
    have h_min := hc_prop.1.1.1
    have h_le : (floorPoint A).x ≤ (floorPoint B).x := floor_mono (by linarith)
    rw [min_eq_left h_le] at h_min; exact h_min
  have h_flAy : c.y ≤ (floorPoint A).y := by
    have h_max := hc_prop.2
    have h_le : (floorPoint B).y ≤ (floorPoint A).y := floor_mono (by linarith)
    have h_max_eq : max (floorPoint A).y (floorPoint B).y = (floorPoint A).y := max_eq_left h_le
    rw [h_max_eq] at h_max; exact h_max
  have h_ge : ofInt (c.x + 1) ≥ A.x := by
    unfold floorPoint toInt at h_flA; dsimp at h_flA; have h_lt := Rat.lt_floor_add_one A.x; push_cast at h_lt
    have h_flA_rat : ((A.x.floor : ℤ) : ℚ) ≤ (c.x : ℚ) := Int.cast_le.mpr h_flA
    have h_ofInt : ofInt (c.x + 1) = (c.x : ℚ) + 1 := by
      unfold ofInt; change ((c.x + 1 : ℤ) : ℚ) = (c.x : ℚ) + 1; push_cast; ring
    rw [h_ofInt]; linarith
  have h_remY_ge : ofInt c.y ≤ A.y := by
    unfold floorPoint toInt at h_flAy; dsimp at h_flAy; have h_le := Rat.floor_le A.y
    have h_flAy_rat : (c.y : ℚ) ≤ ((A.y.floor : ℤ) : ℚ) := Int.cast_le.mpr h_flAy
    have h_ofInt : ofInt c.y = (c.y : ℚ) := rfl
    rw [h_ofInt]; linarith
  have h_remY_split : (if ofInt c.y ≥ A.y then ofInt c.y - A.y else A.y - ofInt c.y) = A.y - ofInt c.y := by
    split_ifs with h <;> [linarith; rfl]
  simp only [h_ge, ↓reduceIte] at h_bndX
  rw [h_remY_split] at h_bndY
  have h_le_x := stepX_next_le_end c.x A.x B.x h_bndX
  have h_div_bnd : (ofInt c.y - A.y) / (B.y - A.y) < 1 := by
    have h_lt_neg : A.y - ofInt c.y < -(B.y - A.y) := by linarith [h_bndY]
    have : (A.y - ofInt c.y) / -(B.y - A.y) < 1 := (div_lt_one (by linarith)).mpr h_lt_neg
    have h_num : A.y - ofInt c.y = -(ofInt c.y - A.y) := by ring
    rw [h_num, neg_div_neg_eq] at this; exact this
  have h_le_y := stepY_neg_next_ge_end c.y A.y B hdy h_div_bnd
  have h_bbox_next := inBoundingBox_diag_pos_neg c A B hdx hdy hc_bbox h_le_x h_le_y
  refine ⟨h_bbox_next, ?_⟩
  unfold remX_val remY_val absVal at h_step
  simp only [show (1 : ℤ) > 0 by decide, show ¬((-1 : ℤ) > 0) by decide, ↓reduceIte,
    le_of_lt hdx, show ¬(B.y - A.y ≥ 0) by linarith, h_ge] at h_step
  rw [h_remY_split] at h_step
  let t := (ofInt (c.x + 1) - A.x) / (B.x - A.x)
  have h_t_eq : t = (ofInt c.y - A.y) / (B.y - A.y) := by
    dsimp [t]
    have h_cross := (cross_eq_cross_iff_div_eq_div (ofInt (c.x + 1) - A.x) (A.y - ofInt c.y) (B.x - A.x) (-(B.y - A.y)) hdx (by linarith)).mp h_step
    rw [h_cross]
    have h_num : A.y - ofInt c.y = -(ofInt c.y - A.y) := by ring
    rw [h_num, neg_div_neg_eq]
  have h_lim : t < 1 := (div_lt_one hdx).mpr h_bndX
  have h_pos : 0 ≤ t := div_nonneg (by linarith) (le_of_lt hdx)
  have h_lt := stepDiag_interval_lt_pos_neg t (B.x - A.x) (B.y - A.y) hdx hdy h_lim h_pos
  let tEnter := max 0 (max t t)
  let tExit := min 1 (min (t + 1 / (B.x - A.x)) (t - 1 / (B.y - A.y)))
  have h_eval := cellIntersectionInterval_diag_pos_neg A B c hdx hdy h_t_eq h_lt
  exact ⟨tEnter, tExit, h_eval, h_lt⟩


theorem rayMarchStep_sound_step_pos_neg (A B : Point) (dx dy : ℚ) (stepX stepY : ℤ) (c : Cell)
    (hdx : dx = B.x - A.x) (hdy : dy = B.y - A.y)
    (hstepX : stepX = if dx > 0 then 1 else if dx < 0 then -1 else 0)
    (hstepY : stepY = if dy > 0 then 1 else if dy < 0 then -1 else 0)
    (h_pos_neg : 0 < dx ∧ dy < 0)
    (hc_bbox : inBoundingBox c A B = true)
    (hc_valid : c = floorPoint A ∨ ∃ tEnter tExit, cellIntersectionInterval c A B = some (tEnter, tExit) ∧ tEnter < tExit)
    (h_not_done : (rayMarchStep A B dx dy stepX stepY c).2 = false) :
    inBoundingBox (rayMarchStep A B dx dy stepX stepY c).1 A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval (rayMarchStep A B dx dy stepX stepY c).1 A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  have hsx : stepX = 1 := by rw [hstepX]; simp [h_pos_neg.1]
  have hsy : stepY = -1 := by rw [hstepY]; simp [show ¬(dy > 0) by linarith [h_pos_neg.2], h_pos_neg.2]
  have h_cases := rayMarchStep_cases A B dx dy stepX stepY c
  rcases h_cases with h1 | h2 | h3 | h4
  · rw [h1] at h_not_done; contradiction
  · rw [h2]; dsimp only []
    have h_step_eq : rayMarchStep A B (B.x - A.x) (B.y - A.y) 1 (-1) c = (⟨c.x + 1, c.y⟩, false) := by
      subst hdx; subst hdy; subst hsx; subst hsy; exact h2
    have ⟨h_step, h_lim⟩ := extract_stepX_pos_neg A B c (by linarith [h_pos_neg.1, hdx]) (by linarith [h_pos_neg.2, hdy]) h_step_eq
    rw [hsx]
    exact rayMarchStep_X_pos_neg_sound A B c (by linarith [h_pos_neg.1, hdx]) (by linarith [h_pos_neg.2, hdy]) hc_bbox hc_valid h_step h_lim
  · rw [h3]; dsimp only []
    have h_step_eq : rayMarchStep A B (B.x - A.x) (B.y - A.y) 1 (-1) c = (⟨c.x, c.y - 1⟩, false) := by
      subst hdx; subst hdy; subst hsx; subst hsy; exact h3
    have ⟨h_step, h_lim⟩ := extract_stepY_pos_neg A B c (by linarith [h_pos_neg.1, hdx]) (by linarith [h_pos_neg.2, hdy]) h_step_eq
    rw [hsy]
    exact rayMarchStep_Y_pos_neg_sound A B c (by linarith [h_pos_neg.1, hdx]) (by linarith [h_pos_neg.2, hdy]) hc_bbox hc_valid h_step h_lim
  · rw [h4]; dsimp only []
    have h_step_eq : rayMarchStep A B (B.x - A.x) (B.y - A.y) 1 (-1) c = (⟨c.x + 1, c.y - 1⟩, false) := by
      subst hdx; subst hdy; subst hsx; subst hsy; exact h4
    have ⟨h_step, h_lim⟩ := extract_stepDiag_pos_neg A B c (by linarith [h_pos_neg.1, hdx]) (by linarith [h_pos_neg.2, hdy]) h_step_eq
    rw [hsx, hsy]
    exact rayMarchStep_Diag_pos_neg_sound A B c (by linarith [h_pos_neg.1, hdx]) (by linarith [h_pos_neg.2, hdy]) hc_bbox hc_valid h_step h_lim


theorem rayMarch_soundness_pos_neg (A B : Point) (x : Cell)
    (hdx : 0 < B.x - A.x) (hdy : B.y - A.y < 0)
    (hx : x ∈ rayMarch (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 2)
      A B (B.x - A.x) (B.y - A.y)
      (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0)
      (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0)
      (floorPoint B) (floorPoint A) []) :
    inBoundingBox x A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval x A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  have hsx : (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else (0 : ℤ)) = 1 := by simp [hdx]
  have hsy : (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else (0 : ℤ)) = -1 := by
    simp [show ¬(B.y - A.y > 0) by linarith, hdy]
  rw [hsx, hsy] at hx
  have h_fuel : (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 2) =
    (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 1) + 1 := by omega
  rw [h_fuel] at hx
  apply sound_from_first_step _ _ _ _ _ _ _ (floorPoint B) (fun cell =>
    inBoundingBox cell A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval cell A B = some (tEnter, tExit) ∧ tEnter < tExit)
    _ _ x hx
  · intro c hc h_not_done
    exact rayMarchStep_sound_step_pos_neg A B (B.x - A.x) (B.y - A.y) 1 (-1) c rfl rfl (by simp [hdx]) (by simp [show ¬(B.y - A.y > 0) by linarith, hdy]) ⟨hdx, hdy⟩ hc.1 (Or.inr hc.2) h_not_done
  · intro h_not_done
    exact rayMarchStep_sound_step_pos_neg A B (B.x - A.x) (B.y - A.y) 1 (-1) (floorPoint A) rfl rfl (by simp [hdx]) (by simp [show ¬(B.y - A.y > 0) by linarith, hdy]) ⟨hdx, hdy⟩ (inBoundingBox_startCell A B) (Or.inl rfl) h_not_done


/- =========================================================================
   Quadrant 3: dx < 0, dy > 0
   ========================================================================= -/

theorem inBoundingBox_diag_neg_pos (c : Cell) (A B : Point)
    (hdx : B.x - A.x < 0) (hdy : 0 < B.y - A.y)
    (h_bbox : inBoundingBox c A B = true)
    (h_next_x : (floorPoint B).x ≤ c.x - 1)
    (h_next_y : c.y + 1 ≤ (floorPoint B).y) :
    inBoundingBox ⟨c.x - 1, c.y + 1⟩ A B = true := by
  have h1 := inBoundingBox_stepX_backward c A B hdx h_bbox h_next_x
  exact inBoundingBox_stepY_forward ⟨c.x - 1, c.y⟩ A B hdy h1 h_next_y


theorem stepDiag_interval_lt_neg_pos (t dx dy : ℚ) (dx_neg : dx < 0) (dy_pos : 0 < dy)
    (h_lim : t < 1)
    (h_pos : 0 ≤ t) :
    max 0 (max t t) < min 1 (min (t - 1 / dx) (t + 1 / dy)) := by
  have h_enter : max 0 (max t t) = t := by
    rw [max_self]
    exact max_eq_right h_pos
  rw [h_enter]
  have h1 : t < 1 := h_lim
  have h2 : t < t - 1 / dx := by
    have h_neg_dx : 0 < -dx := by linarith
    have h_inv : 0 < 1 / -dx := one_div_pos.mpr h_neg_dx
    have h_eq : -1 / dx = 1 / -dx := by ring
    linarith
  have h3 : t < t + 1 / dy := by
    have : 0 < 1 / dy := one_div_pos.mpr dy_pos
    linarith
  rw [lt_min_iff]
  refine ⟨h1, ?_⟩
  rw [lt_min_iff]
  exact ⟨h2, h3⟩


theorem cellIntersectionInterval_stepX_neg_pos (A B : Point) (c : Cell)
    (hdx : B.x - A.x < 0) (hdy : 0 < B.y - A.y) :
    let dx := B.x - A.x
    let dy := B.y - A.y
    let tx1 := (ofInt c.x - A.x) / dx
    let ty0 := (ofInt c.y - A.y) / dy
    let ty1 := (ofInt (c.y + 1) - A.y) / dy
    let tEnter := max 0 (max tx1 ty0)
    let tExit := min 1 (min (tx1 - 1 / dx) ty1)
    tEnter < tExit →
    cellIntersectionInterval ⟨c.x - 1, c.y⟩ A B = some (tEnter, tExit) := by
  intro dx dy tx1 ty0 ty1 tEnter tExit h_lt
  unfold cellIntersectionInterval; dsimp only []
  have h_dx_ne : (B.x - A.x == 0) = false := by
    cases h : (B.x - A.x == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_dy_ne : (B.y - A.y == 0) = false := by
    cases h : (B.y - A.y == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_not_dx_pos : ¬(B.x - A.x > 0) := by linarith
  simp only [h_dx_ne, h_dy_ne, h_not_dx_pos, hdy, ↓reduceIte]
  have h_cx1 : ofInt (c.x - 1 + 1) = ofInt c.x := by
    unfold ofInt; congr 1; omega
  have h_cx0 : ofInt (c.x - 1) = ofInt c.x - 1 := by
    unfold ofInt; change ((c.x - 1 : ℤ) : ℚ) = ((c.x : ℤ) : ℚ) - 1; push_cast; ring
  rw [h_cx1, h_cx0]
  have h_divx : (ofInt c.x - 1 - A.x) / (B.x - A.x) = tx1 - 1 / dx := by
    dsimp [tx1, dx]; ring
  rw [h_divx]
  simp only [Bool.false_eq_true, ↓reduceIte]
  change (if tEnter ≤ tExit then some (tEnter, tExit) else none) = some (tEnter, tExit)
  have h_le : tEnter ≤ tExit := le_of_lt h_lt
  simp only [h_le, ↓reduceIte]


theorem cellIntersectionInterval_stepY_neg_pos (A B : Point) (c : Cell)
    (hdx : B.x - A.x < 0) (hdy : 0 < B.y - A.y) :
    let dx := B.x - A.x
    let dy := B.y - A.y
    let tx0 := (ofInt (c.x + 1) - A.x) / dx
    let tx1 := (ofInt c.x - A.x) / dx
    let ty1 := (ofInt (c.y + 1) - A.y) / dy
    let tEnter := max 0 (max tx0 ty1)
    let tExit := min 1 (min tx1 (ty1 + 1 / dy))
    tEnter < tExit →
    cellIntersectionInterval ⟨c.x, c.y + 1⟩ A B = some (tEnter, tExit) := by
  intro dx dy tx0 tx1 ty1 tEnter tExit h_lt
  unfold cellIntersectionInterval; dsimp only []
  have h_dx_ne : (B.x - A.x == 0) = false := by
    cases h : (B.x - A.x == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_dy_ne : (B.y - A.y == 0) = false := by
    cases h : (B.y - A.y == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_not_dx_pos : ¬(B.x - A.x > 0) := by linarith
  simp only [h_dx_ne, h_dy_ne, h_not_dx_pos, hdy, ↓reduceIte]
  have h_cy1 : ofInt (c.y + 1 + 1) = ofInt (c.y + 1) + 1 := by
    unfold ofInt; change ((c.y + 1 + 1 : ℤ) : ℚ) = ((c.y + 1 : ℤ) : ℚ) + 1; push_cast; ring
  rw [h_cy1]
  have h_divy : (ofInt (c.y + 1) + 1 - A.y) / (B.y - A.y) = ty1 + 1 / dy := by
    dsimp [ty1, dy]; ring
  rw [h_divy]
  simp only [Bool.false_eq_true, ↓reduceIte]
  change (if tEnter ≤ tExit then some (tEnter, tExit) else none) = some (tEnter, tExit)
  have h_le : tEnter ≤ tExit := le_of_lt h_lt
  simp only [h_le, ↓reduceIte]


theorem cellIntersectionInterval_diag_neg_pos (A B : Point) (c : Cell)
    (hdx : B.x - A.x < 0) (hdy : 0 < B.y - A.y) :
    let dx := B.x - A.x
    let dy := B.y - A.y
    let t := (ofInt c.x - A.x) / dx
    let tEnter := max 0 (max t t)
    let tExit := min 1 (min (t - 1 / dx) (t + 1 / dy))
    t = (ofInt (c.y + 1) - A.y) / dy →
    tEnter < tExit →
    cellIntersectionInterval ⟨c.x - 1, c.y + 1⟩ A B = some (tEnter, tExit) := by
  intro dx dy t tEnter tExit h_eq h_lt
  unfold cellIntersectionInterval; dsimp only []
  have h_dx_ne : (B.x - A.x == 0) = false := by
    cases h : (B.x - A.x == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_dy_ne : (B.y - A.y == 0) = false := by
    cases h : (B.y - A.y == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_not_dx_pos : ¬(B.x - A.x > 0) := by linarith
  simp only [h_dx_ne, h_dy_ne, h_not_dx_pos, hdy, ↓reduceIte]
  have h_cx1 : ofInt (c.x - 1 + 1) = ofInt c.x := by
    unfold ofInt; congr 1; omega
  have h_cx0 : ofInt (c.x - 1) = ofInt c.x - 1 := by
    unfold ofInt; change ((c.x - 1 : ℤ) : ℚ) = ((c.x : ℤ) : ℚ) - 1; push_cast; ring
  have h_cy1 : ofInt (c.y + 1 + 1) = ofInt (c.y + 1) + 1 := by
    unfold ofInt; change ((c.y + 1 + 1 : ℤ) : ℚ) = ((c.y + 1 : ℤ) : ℚ) + 1; push_cast; ring
  rw [h_cx1, h_cx0, h_cy1]
  have h_divx : (ofInt c.x - 1 - A.x) / (B.x - A.x) = t - 1 / dx := by
    dsimp [t, dx]; ring
  have h_divy : (ofInt (c.y + 1) + 1 - A.y) / (B.y - A.y) = t + 1 / dy := by
    rw [h_eq]; dsimp [dy]; ring
  rw [h_divx, h_divy]
  have h_ty : (ofInt (c.y + 1) - A.y) / (B.y - A.y) = t := by
    dsimp [dy] at h_eq; exact h_eq.symm
  rw [h_ty]
  simp only [Bool.false_eq_true, ↓reduceIte]
  change (if tEnter ≤ tExit then some (tEnter, tExit) else none) = some (tEnter, tExit)
  have h_le : tEnter ≤ tExit := le_of_lt h_lt
  simp only [h_le, ↓reduceIte]


theorem extract_stepX_neg_pos (A B : Point) (c : Cell)
    (_hdx : B.x - A.x < 0) (_hdy : 0 < B.y - A.y)
    (h_step : rayMarchStep A B (B.x - A.x) (B.y - A.y) (-1) 1 c = (⟨c.x - 1, c.y⟩, false)) :
    remX_val A (-1) c * absVal (B.y - A.y) < remY_val A 1 c * absVal (B.x - A.x) ∧
    min (remX_val A (-1) c * absVal (B.y - A.y)) (remY_val A 1 c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y) := by
  unfold rayMarchStep at h_step; dsimp only [] at h_step
  simp only [show ((-1 : ℤ) == 0) = false by decide, Bool.false_eq_true, ↓reduceIte] at h_step
  by_cases hlim : min
        ((if (if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y))
        ((if (if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) ≥
      (if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) * if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
  · simp only [hlim, ↓reduceIte] at h_step; injection h_step with _ h_bool; contradiction
  · simp only [hlim, ↓reduceIte] at h_step
    by_cases hxy : ((if (if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)) <
        (if (if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)
    · unfold remX_val remY_val absVal; dsimp only []
      simp only [show ¬((-1 : ℤ) > 0) by decide, show (1 : ℤ) > 0 by decide, ↓reduceIte]
      refine ⟨hxy, not_le.mp hlim⟩
    · simp only [hxy, ↓reduceIte] at h_step
      by_cases hyx : ((if (if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
              (if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
            else A.y - if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) *
            if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) <
          (if (if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
              (if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
            else A.x - if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) *
            if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
      · simp only [hyx, ↓reduceIte] at h_step; injection h_step with h_cell _; injection h_cell with _ hy; omega
      · simp only [hyx, ↓reduceIte] at h_step; injection h_step with h_cell _; injection h_cell with hx _; omega


theorem extract_stepY_neg_pos (A B : Point) (c : Cell)
    (_hdx : B.x - A.x < 0) (_hdy : 0 < B.y - A.y)
    (h_step : rayMarchStep A B (B.x - A.x) (B.y - A.y) (-1) 1 c = (⟨c.x, c.y + 1⟩, false)) :
    remY_val A 1 c * absVal (B.x - A.x) < remX_val A (-1) c * absVal (B.y - A.y) ∧
    min (remX_val A (-1) c * absVal (B.y - A.y)) (remY_val A 1 c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y) := by
  unfold rayMarchStep at h_step; dsimp only [] at h_step
  simp only [show ((-1 : ℤ) == 0) = false by decide, Bool.false_eq_true, ↓reduceIte] at h_step
  by_cases hlim : min
        ((if (if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y))
        ((if (if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) ≥
      (if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) * if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
  · simp only [hlim, ↓reduceIte] at h_step; injection h_step with _ h_bool; contradiction
  · simp only [hlim, ↓reduceIte] at h_step
    by_cases hxy : ((if (if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)) <
        (if (if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)
    · simp only [hxy, ↓reduceIte] at h_step; injection h_step with h_cell _; injection h_cell with hx _; omega
    · simp only [hxy, ↓reduceIte] at h_step
      by_cases hyx : ((if (if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
              (if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
            else A.y - if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) *
            if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) <
          (if (if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
              (if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
            else A.x - if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) *
            if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
      · unfold remX_val remY_val absVal; dsimp only []
        simp only [show ¬((-1 : ℤ) > 0) by decide, show (1 : ℤ) > 0 by decide, ↓reduceIte]
        refine ⟨hyx, not_le.mp hlim⟩
      · simp only [hyx, ↓reduceIte] at h_step; injection h_step with h_cell _; injection h_cell with _ hy; omega


theorem extract_stepDiag_neg_pos (A B : Point) (c : Cell)
    (_hdx : B.x - A.x < 0) (_hdy : 0 < B.y - A.y)
    (h_step : rayMarchStep A B (B.x - A.x) (B.y - A.y) (-1) 1 c = (⟨c.x - 1, c.y + 1⟩, false)) :
    remX_val A (-1) c * absVal (B.y - A.y) = remY_val A 1 c * absVal (B.x - A.x) ∧
    min (remX_val A (-1) c * absVal (B.y - A.y)) (remY_val A 1 c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y) := by
  unfold rayMarchStep at h_step; dsimp only [] at h_step
  simp only [show ((-1 : ℤ) == 0) = false by decide, Bool.false_eq_true, ↓reduceIte] at h_step
  by_cases hlim : min
        ((if (if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y))
        ((if (if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) ≥
      (if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) * if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
  · simp only [hlim, ↓reduceIte] at h_step; injection h_step with _ h_bool; contradiction
  · simp only [hlim, ↓reduceIte] at h_step
    by_cases hxy : ((if (if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)) <
        (if (if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)
    · simp only [hxy, ↓reduceIte] at h_step; injection h_step with h_cell _; injection h_cell with hx _; omega
    · simp only [hxy, ↓reduceIte] at h_step
      by_cases hyx : ((if (if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
              (if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
            else A.y - if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) *
            if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) <
          (if (if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
              (if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
            else A.x - if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) *
            if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
      · simp only [hyx, ↓reduceIte] at h_step; injection h_step with h_cell _; injection h_cell with _ hy; omega
      · unfold remX_val remY_val absVal; dsimp only []
        simp only [show ¬((-1 : ℤ) > 0) by decide, show (1 : ℤ) > 0 by decide, ↓reduceIte] at *
        refine ⟨by linarith, not_le.mp hlim⟩


theorem rayMarchStep_X_neg_pos_sound (A B : Point) (c : Cell)
    (hdx : B.x - A.x < 0) (hdy : 0 < B.y - A.y)
    (hc_bbox : inBoundingBox c A B = true)
    (hc_valid : c = floorPoint A ∨ ∃ tEnter tExit, cellIntersectionInterval c A B = some (tEnter, tExit) ∧ tEnter < tExit)
    (h_step : remX_val A (-1) c * absVal (B.y - A.y) < remY_val A 1 c * absVal (B.x - A.x))
    (h_not_done : min (remX_val A (-1) c * absVal (B.y - A.y)) (remY_val A 1 c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y)) :
    inBoundingBox ⟨c.x - 1, c.y⟩ A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval ⟨c.x - 1, c.y⟩ A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  have h_absDy : 0 < absVal (B.y - A.y) := by unfold absVal; split_ifs <;> linarith
  have h_bnd := stepX_bounded (remX_val A (-1) c) (absVal (B.x - A.x)) (absVal (B.y - A.y))
    (remY_val A 1 c * absVal (B.x - A.x)) h_absDy h_step h_not_done
  unfold absVal at h_bnd; simp [show ¬(B.x - A.x ≥ 0) by linarith] at h_bnd
  unfold remX_val at h_bnd; simp only [show ¬((-1 : ℤ) > 0) by decide, ↓reduceIte] at h_bnd
  have hc_prop := hc_bbox; unfold inBoundingBox at hc_prop; dsimp only [] at hc_prop
  simp only [Bool.and_eq_true, decide_eq_true_iff] at hc_prop
  have h_flAx : c.x ≤ (floorPoint A).x := by
    have h_max := hc_prop.1.1.2
    have h_le : (floorPoint B).x ≤ (floorPoint A).x := floor_mono (by linarith)
    have h_max_eq : max (floorPoint A).x (floorPoint B).x = (floorPoint A).x := max_eq_left h_le
    rw [h_max_eq] at h_max; exact h_max
  have h_flAy : (floorPoint A).y ≤ c.y := by
    have h_min := hc_prop.1.2
    have h_le : (floorPoint A).y ≤ (floorPoint B).y := floor_mono (by linarith)
    rw [min_eq_left h_le] at h_min; exact h_min
  have h_remX_ge : ofInt c.x ≤ A.x := by
    unfold floorPoint toInt at h_flAx; dsimp at h_flAx
    have h_le := Rat.floor_le A.x
    have h_flAx_rat : (c.x : ℚ) ≤ ((A.x.floor : ℤ) : ℚ) := Int.cast_le.mpr h_flAx
    have h_ofInt : ofInt c.x = (c.x : ℚ) := rfl
    rw [h_ofInt]; linarith
  have h_remY_ge : ofInt (c.y + 1) ≥ A.y := by
    unfold floorPoint toInt at h_flAy; dsimp at h_flAy
    have h_lt := Rat.lt_floor_add_one A.y; push_cast at h_lt
    have h_flAy_rat : ((A.y.floor : ℤ) : ℚ) ≤ (c.y : ℚ) := Int.cast_le.mpr h_flAy
    have h_ofInt : ofInt (c.y + 1) = (c.y : ℚ) + 1 := by
      unfold ofInt; change ((c.y + 1 : ℤ) : ℚ) = (c.y : ℚ) + 1; push_cast; ring
    rw [h_ofInt]; linarith
  have h_remX_split : (if ofInt c.x ≥ A.x then ofInt c.x - A.x else A.x - ofInt c.x) = A.x - ofInt c.x := by
    split_ifs with h <;> [linarith; rfl]
  rw [h_remX_split] at h_bnd
  have h_div_bnd : (ofInt c.x - A.x) / (B.x - A.x) < 1 := by
    have h_lt_neg : A.x - ofInt c.x < -(B.x - A.x) := by linarith [h_bnd]
    have : (A.x - ofInt c.x) / -(B.x - A.x) < 1 := (div_lt_one (by linarith)).mpr h_lt_neg
    have h_num : A.x - ofInt c.x = -(ofInt c.x - A.x) := by ring
    rw [h_num, neg_div_neg_eq] at this; exact this
  have h_le := stepX_neg_next_ge_end c.x A.x B hdx h_div_bnd
  have h_bbox_next := inBoundingBox_stepX_backward c A B hdx hc_bbox h_le
  refine ⟨h_bbox_next, ?_⟩
  unfold remY_val absVal at h_step
  simp only [show (1 : ℤ) > 0 by decide, ↓reduceIte, le_of_lt hdy, show ¬(B.x - A.x ≥ 0) by linarith, h_remY_ge] at h_step
  unfold remX_val at h_step
  simp only [show ¬((-1 : ℤ) > 0) by decide, ↓reduceIte] at h_step
  rw [h_remX_split] at h_step
  let tx1 := (ofInt c.x - A.x) / (B.x - A.x)
  let ty0 := (ofInt c.y - A.y) / (B.y - A.y)
  let ty1 := (ofInt (c.y + 1) - A.y) / (B.y - A.y)
  have h_tx1_eq : (A.x - ofInt c.x) / -(B.x - A.x) = tx1 := by
    dsimp [tx1]; have h_num : A.x - ofInt c.x = -(ofInt c.x - A.x) := by ring
    rw [h_num, neg_div_neg_eq]
  have h_cross : tx1 < ty1 := by
    have h_cross_div := (cross_lt_cross_iff_div_lt_div (A.x - ofInt c.x) (ofInt (c.y + 1) - A.y) (-(B.x - A.x)) (B.y - A.y) (by linarith) hdy).mp h_step
    rw [h_tx1_eq] at h_cross_div
    exact h_cross_div
  have h_lim : tx1 < 1 := h_div_bnd
  have h_pos_val : 0 ≤ tx1 := by rw [← h_tx1_eq]; exact div_nonneg (by linarith) (by linarith)
  have h_ty0 : ty0 ≤ tx1 := by
    cases hc_valid with
    | inl h_cA =>
      subst h_cA; dsimp [tx1, ty0]
      have h1 : (ofInt (floorPoint A).y - A.y) / (B.y - A.y) ≤ 0 := by
        unfold floorPoint toInt ofInt; dsimp
        have h_le := Rat.floor_le A.y
        exact div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hdy)
      linarith
    | inr h_int =>
      rcases h_int with ⟨tEnter_c, tExit_c, hc_inter, _⟩
      have h_dx_prop := interval_dx_neg c A B tEnter_c tExit_c hc_inter hdx
      have h_dy_prop := interval_dy_pos c A B tEnter_c tExit_c hc_inter hdy
      dsimp [tx1, ty0]; linarith [h_dy_prop.1, h_dx_prop.2]
  have h_lt := stepX_interval_lt_neg tx1 ty0 ty1 (B.x - A.x) hdx h_cross h_lim h_pos_val h_ty0
  let tEnter := max 0 (max tx1 ty0)
  let tExit := min 1 (min (tx1 - 1 / (B.x - A.x)) ty1)
  have h_eval := cellIntersectionInterval_stepX_neg_pos A B c hdx hdy h_lt
  exact ⟨tEnter, tExit, h_eval, h_lt⟩


theorem rayMarchStep_Y_neg_pos_sound (A B : Point) (c : Cell)
    (hdx : B.x - A.x < 0) (hdy : 0 < B.y - A.y)
    (hc_bbox : inBoundingBox c A B = true)
    (hc_valid : c = floorPoint A ∨ ∃ tEnter tExit, cellIntersectionInterval c A B = some (tEnter, tExit) ∧ tEnter < tExit)
    (h_step : remY_val A 1 c * absVal (B.x - A.x) < remX_val A (-1) c * absVal (B.y - A.y))
    (h_not_done : min (remX_val A (-1) c * absVal (B.y - A.y)) (remY_val A 1 c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y)) :
    inBoundingBox ⟨c.x, c.y + 1⟩ A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval ⟨c.x, c.y + 1⟩ A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  have h_absDx : 0 < absVal (B.x - A.x) := by unfold absVal; split_ifs <;> linarith
  have h_bnd := stepY_bounded (remY_val A 1 c) (absVal (B.x - A.x)) (absVal (B.y - A.y))
    (remX_val A (-1) c * absVal (B.y - A.y)) h_absDx h_step h_not_done
  unfold absVal at h_bnd; simp [le_of_lt hdy] at h_bnd
  unfold remY_val at h_bnd; simp only [show (1 : ℤ) > 0 by decide, ↓reduceIte] at h_bnd
  have hc_prop := hc_bbox; unfold inBoundingBox at hc_prop; dsimp only [] at hc_prop
  simp only [Bool.and_eq_true, decide_eq_true_iff] at hc_prop
  have h_flAx : c.x ≤ (floorPoint A).x := by
    have h_max := hc_prop.1.1.2
    have h_le : (floorPoint B).x ≤ (floorPoint A).x := floor_mono (by linarith)
    have h_max_eq : max (floorPoint A).x (floorPoint B).x = (floorPoint A).x := max_eq_left h_le
    rw [h_max_eq] at h_max; exact h_max
  have h_flAy : (floorPoint A).y ≤ c.y := by
    have h_min := hc_prop.1.2
    have h_le : (floorPoint A).y ≤ (floorPoint B).y := floor_mono (by linarith)
    rw [min_eq_left h_le] at h_min; exact h_min
  have h_remX_ge : ofInt c.x ≤ A.x := by
    unfold floorPoint toInt at h_flAx; dsimp at h_flAx
    have h_le := Rat.floor_le A.x
    have h_flAx_rat : (c.x : ℚ) ≤ ((A.x.floor : ℤ) : ℚ) := Int.cast_le.mpr h_flAx
    have h_ofInt : ofInt c.x = (c.x : ℚ) := rfl
    rw [h_ofInt]; linarith
  have h_remY_ge : ofInt (c.y + 1) ≥ A.y := by
    unfold floorPoint toInt at h_flAy; dsimp at h_flAy
    have h_lt := Rat.lt_floor_add_one A.y; push_cast at h_lt
    have h_flAy_rat : ((A.y.floor : ℤ) : ℚ) ≤ (c.y : ℚ) := Int.cast_le.mpr h_flAy
    have h_ofInt : ofInt (c.y + 1) = (c.y : ℚ) + 1 := by
      unfold ofInt; change ((c.y + 1 : ℤ) : ℚ) = (c.y : ℚ) + 1; push_cast; ring
    rw [h_ofInt]; linarith
  simp only [h_remY_ge, ↓reduceIte] at h_bnd
  have h_le := stepY_next_le_end c.y A.y B.y h_bnd
  have h_bbox_next := inBoundingBox_stepY_forward c A B hdy hc_bbox h_le
  refine ⟨h_bbox_next, ?_⟩
  unfold remX_val absVal at h_step
  simp only [show ¬((-1 : ℤ) > 0) by decide, ↓reduceIte, le_of_lt hdy, show ¬(B.x - A.x ≥ 0) by linarith] at h_step
  unfold remY_val at h_step
  simp only [show (1 : ℤ) > 0 by decide, ↓reduceIte, h_remY_ge] at h_step
  have h_remX_split : (if ofInt c.x ≥ A.x then ofInt c.x - A.x else A.x - ofInt c.x) = A.x - ofInt c.x := by
    split_ifs with h <;> [linarith; rfl]
  rw [h_remX_split] at h_step
  let tx0 := (ofInt (c.x + 1) - A.x) / (B.x - A.x)
  let tx1 := (ofInt c.x - A.x) / (B.x - A.x)
  let ty1 := (ofInt (c.y + 1) - A.y) / (B.y - A.y)
  have h_tx1_eq : (A.x - ofInt c.x) / -(B.x - A.x) = tx1 := by
    dsimp [tx1]; have h_num : A.x - ofInt c.x = -(ofInt c.x - A.x) := by ring
    rw [h_num, neg_div_neg_eq]
  have h_cross : ty1 < tx1 := by
    have h_cross_div := (cross_lt_cross_iff_div_lt_div (ofInt (c.y + 1) - A.y) (A.x - ofInt c.x) (B.y - A.y) (-(B.x - A.x)) hdy (by linarith)).mp h_step
    rw [h_tx1_eq] at h_cross_div
    exact h_cross_div
  have h_lim : ty1 < 1 := (div_lt_one hdy).mpr h_bnd
  have h_pos_val : 0 ≤ ty1 := div_nonneg (by linarith) (le_of_lt hdy)
  have h_tx0 : tx0 ≤ ty1 := by
    cases hc_valid with
    | inl h_cA =>
      subst h_cA; dsimp [tx0, ty1]
      have h1 : (ofInt ((floorPoint A).x + 1) - A.x) / (B.x - A.x) ≤ 0 := by
        unfold floorPoint toInt; dsimp
        have h_lt := Rat.lt_floor_add_one A.x; push_cast at h_lt
        have h_num : 0 < ofInt (A.x.floor + 1) - A.x := by
          unfold ofInt; change 0 < ((A.x.floor + 1 : ℤ) : ℚ) - A.x; push_cast; linarith
        exact div_nonpos_of_nonneg_of_nonpos (le_of_lt h_num) (le_of_lt hdx)
      linarith
    | inr h_int =>
      rcases h_int with ⟨tEnter_c, tExit_c, hc_inter, _⟩
      have h_dx_prop := interval_dx_neg c A B tEnter_c tExit_c hc_inter hdx
      have h_dy_prop := interval_dy_pos c A B tEnter_c tExit_c hc_inter hdy
      dsimp [tx0, ty1]; linarith [h_dx_prop.1, h_dy_prop.2]
  have h_lt := stepY_interval_lt ty1 tx0 tx1 (B.y - A.y) hdy h_cross h_lim h_pos_val h_tx0
  let tEnter := max 0 (max tx0 ty1)
  let tExit := min 1 (min tx1 (ty1 + 1 / (B.y - A.y)))
  have h_eval := cellIntersectionInterval_stepY_neg_pos A B c hdx hdy h_lt
  exact ⟨tEnter, tExit, h_eval, h_lt⟩


theorem rayMarchStep_Diag_neg_pos_sound (A B : Point) (c : Cell)
    (hdx : B.x - A.x < 0) (hdy : 0 < B.y - A.y)
    (hc_bbox : inBoundingBox c A B = true)
    (_hc_valid : c = floorPoint A ∨ ∃ tEnter tExit, cellIntersectionInterval c A B = some (tEnter, tExit) ∧ tEnter < tExit)
    (h_step : remX_val A (-1) c * absVal (B.y - A.y) = remY_val A 1 c * absVal (B.x - A.x))
    (h_not_done : min (remX_val A (-1) c * absVal (B.y - A.y)) (remY_val A 1 c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y)) :
    inBoundingBox ⟨c.x - 1, c.y + 1⟩ A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval ⟨c.x - 1, c.y + 1⟩ A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  have h_absDx : 0 < absVal (B.x - A.x) := by unfold absVal; split_ifs <;> linarith
  have h_absDy : 0 < absVal (B.y - A.y) := by unfold absVal; split_ifs <;> linarith
  have ⟨h_bndX, h_bndY⟩ := stepDiag_bounded (remX_val A (-1) c) (remY_val A 1 c)
    (absVal (B.x - A.x)) (absVal (B.y - A.y)) h_absDx h_absDy h_step h_not_done
  unfold absVal at h_bndX h_bndY
  simp [show ¬(B.x - A.x ≥ 0) by linarith, le_of_lt hdy] at h_bndX h_bndY
  unfold remX_val at h_bndX
  unfold remY_val at h_bndY
  simp only [show ¬((-1 : ℤ) > 0) by decide, ↓reduceIte] at h_bndX
  simp only [show (1 : ℤ) > 0 by decide, ↓reduceIte] at h_bndY
  have hc_prop := hc_bbox; unfold inBoundingBox at hc_prop; dsimp only [] at hc_prop
  simp only [Bool.and_eq_true, decide_eq_true_iff] at hc_prop
  have h_flAx : c.x ≤ (floorPoint A).x := by
    have h_max := hc_prop.1.1.2
    have h_le : (floorPoint B).x ≤ (floorPoint A).x := floor_mono (by linarith)
    have h_max_eq : max (floorPoint A).x (floorPoint B).x = (floorPoint A).x := max_eq_left h_le
    rw [h_max_eq] at h_max; exact h_max
  have h_flAy : (floorPoint A).y ≤ c.y := by
    have h_min := hc_prop.1.2
    have h_le : (floorPoint A).y ≤ (floorPoint B).y := floor_mono (by linarith)
    rw [min_eq_left h_le] at h_min; exact h_min
  have h_remX_ge : ofInt c.x ≤ A.x := by
    unfold floorPoint toInt at h_flAx; dsimp at h_flAx
    have h_le := Rat.floor_le A.x
    have h_flAx_rat : (c.x : ℚ) ≤ ((A.x.floor : ℤ) : ℚ) := Int.cast_le.mpr h_flAx
    have h_ofInt : ofInt c.x = (c.x : ℚ) := rfl
    rw [h_ofInt]; linarith
  have h_remY_ge : ofInt (c.y + 1) ≥ A.y := by
    unfold floorPoint toInt at h_flAy; dsimp at h_flAy
    have h_lt := Rat.lt_floor_add_one A.y; push_cast at h_lt
    have h_flAy_rat : ((A.y.floor : ℤ) : ℚ) ≤ (c.y : ℚ) := Int.cast_le.mpr h_flAy
    have h_ofInt : ofInt (c.y + 1) = (c.y : ℚ) + 1 := by
      unfold ofInt; change ((c.y + 1 : ℤ) : ℚ) = (c.y : ℚ) + 1; push_cast; ring
    rw [h_ofInt]; linarith
  have h_remX_split : (if ofInt c.x ≥ A.x then ofInt c.x - A.x else A.x - ofInt c.x) = A.x - ofInt c.x := by
    split_ifs with h <;> [linarith; rfl]
  rw [h_remX_split] at h_bndX
  simp only [h_remY_ge, ↓reduceIte] at h_bndY
  have h_div_bnd : (ofInt c.x - A.x) / (B.x - A.x) < 1 := by
    have h_lt_neg : A.x - ofInt c.x < -(B.x - A.x) := by linarith [h_bndX]
    have : (A.x - ofInt c.x) / -(B.x - A.x) < 1 := (div_lt_one (by linarith)).mpr h_lt_neg
    have h_num : A.x - ofInt c.x = -(ofInt c.x - A.x) := by ring
    rw [h_num, neg_div_neg_eq] at this; exact this
  have h_le_x := stepX_neg_next_ge_end c.x A.x B hdx h_div_bnd
  have h_le_y := stepY_next_le_end c.y A.y B.y h_bndY
  have h_bbox_next := inBoundingBox_diag_neg_pos c A B hdx hdy hc_bbox h_le_x h_le_y
  refine ⟨h_bbox_next, ?_⟩
  unfold remX_val remY_val absVal at h_step
  simp only [show ¬((-1 : ℤ) > 0) by decide, show (1 : ℤ) > 0 by decide, ↓reduceIte,
    le_of_lt hdy, show ¬(B.x - A.x ≥ 0) by linarith, h_remY_ge] at h_step
  rw [h_remX_split] at h_step
  let t := (ofInt c.x - A.x) / (B.x - A.x)
  have h_t_eq : t = (ofInt (c.y + 1) - A.y) / (B.y - A.y) := by
    dsimp [t]
    have h_cross := (cross_eq_cross_iff_div_eq_div (A.x - ofInt c.x) (ofInt (c.y + 1) - A.y) (-(B.x - A.x)) (B.y - A.y) (by linarith) hdy).mp h_step
    have h_num : A.x - ofInt c.x = -(ofInt c.x - A.x) := by ring
    rw [← h_cross, h_num, neg_div_neg_eq]
  have h_lim : t < 1 := h_div_bnd
  have h_pos : 0 ≤ t := by
    have h_num : A.x - ofInt c.x = -(ofInt c.x - A.x) := by ring
    have h_tx1_eq : (A.x - ofInt c.x) / -(B.x - A.x) = t := by dsimp [t]; rw [h_num, neg_div_neg_eq]
    rw [← h_tx1_eq]; exact div_nonneg (by linarith) (by linarith)
  have h_lt := stepDiag_interval_lt_neg_pos t (B.x - A.x) (B.y - A.y) hdx hdy h_lim h_pos
  let tEnter := max 0 (max t t)
  let tExit := min 1 (min (t - 1 / (B.x - A.x)) (t + 1 / (B.y - A.y)))
  have h_eval := cellIntersectionInterval_diag_neg_pos A B c hdx hdy h_t_eq h_lt
  exact ⟨tEnter, tExit, h_eval, h_lt⟩


theorem rayMarchStep_sound_step_neg_pos (A B : Point) (dx dy : ℚ) (stepX stepY : ℤ) (c : Cell)
    (hdx : dx = B.x - A.x) (hdy : dy = B.y - A.y)
    (hstepX : stepX = if dx > 0 then 1 else if dx < 0 then -1 else 0)
    (hstepY : stepY = if dy > 0 then 1 else if dy < 0 then -1 else 0)
    (h_neg_pos : dx < 0 ∧ 0 < dy)
    (hc_bbox : inBoundingBox c A B = true)
    (hc_valid : c = floorPoint A ∨ ∃ tEnter tExit, cellIntersectionInterval c A B = some (tEnter, tExit) ∧ tEnter < tExit)
    (h_not_done : (rayMarchStep A B dx dy stepX stepY c).2 = false) :
    inBoundingBox (rayMarchStep A B dx dy stepX stepY c).1 A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval (rayMarchStep A B dx dy stepX stepY c).1 A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  have hsx : stepX = -1 := by rw [hstepX]; simp [show ¬(dx > 0) by linarith [h_neg_pos.1], h_neg_pos.1]
  have hsy : stepY = 1 := by rw [hstepY]; simp [h_neg_pos.2]
  have h_cases := rayMarchStep_cases A B dx dy stepX stepY c
  rcases h_cases with h1 | h2 | h3 | h4
  · rw [h1] at h_not_done; contradiction
  · rw [h2]; dsimp only []
    have h_step_eq : rayMarchStep A B (B.x - A.x) (B.y - A.y) (-1) 1 c = (⟨c.x - 1, c.y⟩, false) := by
      subst hdx; subst hdy; subst hsx; subst hsy; exact h2
    have ⟨h_step, h_lim⟩ := extract_stepX_neg_pos A B c (by linarith [h_neg_pos.1, hdx]) (by linarith [h_neg_pos.2, hdy]) h_step_eq
    rw [hsx]
    exact rayMarchStep_X_neg_pos_sound A B c (by linarith [h_neg_pos.1, hdx]) (by linarith [h_neg_pos.2, hdy]) hc_bbox hc_valid h_step h_lim
  · rw [h3]; dsimp only []
    have h_step_eq : rayMarchStep A B (B.x - A.x) (B.y - A.y) (-1) 1 c = (⟨c.x, c.y + 1⟩, false) := by
      subst hdx; subst hdy; subst hsx; subst hsy; exact h3
    have ⟨h_step, h_lim⟩ := extract_stepY_neg_pos A B c (by linarith [h_neg_pos.1, hdx]) (by linarith [h_neg_pos.2, hdy]) h_step_eq
    rw [hsy]
    exact rayMarchStep_Y_neg_pos_sound A B c (by linarith [h_neg_pos.1, hdx]) (by linarith [h_neg_pos.2, hdy]) hc_bbox hc_valid h_step h_lim
  · rw [h4]; dsimp only []
    have h_step_eq : rayMarchStep A B (B.x - A.x) (B.y - A.y) (-1) 1 c = (⟨c.x - 1, c.y + 1⟩, false) := by
      subst hdx; subst hdy; subst hsx; subst hsy; exact h4
    have ⟨h_step, h_lim⟩ := extract_stepDiag_neg_pos A B c (by linarith [h_neg_pos.1, hdx]) (by linarith [h_neg_pos.2, hdy]) h_step_eq
    rw [hsx, hsy]
    exact rayMarchStep_Diag_neg_pos_sound A B c (by linarith [h_neg_pos.1, hdx]) (by linarith [h_neg_pos.2, hdy]) hc_bbox hc_valid h_step h_lim


theorem rayMarch_soundness_neg_pos (A B : Point) (x : Cell)
    (hdx : B.x - A.x < 0) (hdy : 0 < B.y - A.y)
    (hx : x ∈ rayMarch (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 2)
      A B (B.x - A.x) (B.y - A.y)
      (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0)
      (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0)
      (floorPoint B) (floorPoint A) []) :
    inBoundingBox x A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval x A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  have hsx : (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else (0 : ℤ)) = -1 := by
    simp [show ¬(B.x - A.x > 0) by linarith, hdx]
  have hsy : (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else (0 : ℤ)) = 1 := by simp [hdy]
  rw [hsx, hsy] at hx
  have h_fuel : (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 2) =
    (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 1) + 1 := by omega
  rw [h_fuel] at hx
  apply sound_from_first_step _ _ _ _ _ _ _ (floorPoint B) (fun cell =>
    inBoundingBox cell A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval cell A B = some (tEnter, tExit) ∧ tEnter < tExit)
    _ _ x hx
  · intro c hc h_not_done
    exact rayMarchStep_sound_step_neg_pos A B (B.x - A.x) (B.y - A.y) (-1) 1 c rfl rfl (by simp [show ¬(B.x - A.x > 0) by linarith, hdx]) (by simp [hdy]) ⟨hdx, hdy⟩ hc.1 (Or.inr hc.2) h_not_done
  · intro h_not_done
    exact rayMarchStep_sound_step_neg_pos A B (B.x - A.x) (B.y - A.y) (-1) 1 (floorPoint A) rfl rfl (by simp [show ¬(B.x - A.x > 0) by linarith, hdx]) (by simp [hdy]) ⟨hdx, hdy⟩ (inBoundingBox_startCell A B) (Or.inl rfl) h_not_done


/- =========================================================================
   Quadrant 4: dx < 0, dy < 0
   ========================================================================= -/

theorem inBoundingBox_diag_neg_neg (c : Cell) (A B : Point)
    (hdx : B.x - A.x < 0) (hdy : B.y - A.y < 0)
    (h_bbox : inBoundingBox c A B = true)
    (h_next_x : (floorPoint B).x ≤ c.x - 1)
    (h_next_y : (floorPoint B).y ≤ c.y - 1) :
    inBoundingBox ⟨c.x - 1, c.y - 1⟩ A B = true := by
  have h1 := inBoundingBox_stepX_backward c A B hdx h_bbox h_next_x
  exact inBoundingBox_stepY_backward ⟨c.x - 1, c.y⟩ A B hdy h1 h_next_y


theorem stepDiag_interval_lt_neg_neg (t dx dy : ℚ) (dx_neg : dx < 0) (dy_neg : dy < 0)
    (h_lim : t < 1)
    (h_pos : 0 ≤ t) :
    max 0 (max t t) < min 1 (min (t - 1 / dx) (t - 1 / dy)) := by
  have h_enter : max 0 (max t t) = t := by
    rw [max_self]
    exact max_eq_right h_pos
  rw [h_enter]
  have h1 : t < 1 := h_lim
  have h2 : t < t - 1 / dx := by
    have h_neg_dx : 0 < -dx := by linarith
    have h_inv : 0 < 1 / -dx := one_div_pos.mpr h_neg_dx
    have h_eq : -1 / dx = 1 / -dx := by ring
    linarith
  have h3 : t < t - 1 / dy := by
    have h_neg_dy : 0 < -dy := by linarith
    have h_inv : 0 < 1 / -dy := one_div_pos.mpr h_neg_dy
    have h_eq : -1 / dy = 1 / -dy := by ring
    linarith
  rw [lt_min_iff]
  refine ⟨h1, ?_⟩
  rw [lt_min_iff]
  exact ⟨h2, h3⟩


theorem cellIntersectionInterval_stepX_neg_neg (A B : Point) (c : Cell)
    (hdx : B.x - A.x < 0) (hdy : B.y - A.y < 0) :
    let dx := B.x - A.x
    let dy := B.y - A.y
    let tx1 := (ofInt c.x - A.x) / dx
    let ty0 := (ofInt (c.y + 1) - A.y) / dy
    let ty1 := (ofInt c.y - A.y) / dy
    let tEnter := max 0 (max tx1 ty0)
    let tExit := min 1 (min (tx1 - 1 / dx) ty1)
    tEnter < tExit →
    cellIntersectionInterval ⟨c.x - 1, c.y⟩ A B = some (tEnter, tExit) := by
  intro dx dy tx1 ty0 ty1 tEnter tExit h_lt
  unfold cellIntersectionInterval; dsimp only []
  have h_dx_ne : (B.x - A.x == 0) = false := by
    cases h : (B.x - A.x == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_dy_ne : (B.y - A.y == 0) = false := by
    cases h : (B.y - A.y == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_not_dx_pos : ¬(B.x - A.x > 0) := by linarith
  have h_not_dy_pos : ¬(B.y - A.y > 0) := by linarith
  simp only [h_dx_ne, h_dy_ne, h_not_dx_pos, h_not_dy_pos, ↓reduceIte]
  have h_cx1 : ofInt (c.x - 1 + 1) = ofInt c.x := by
    unfold ofInt; congr 1; omega
  have h_cx0 : ofInt (c.x - 1) = ofInt c.x - 1 := by
    unfold ofInt; change ((c.x - 1 : ℤ) : ℚ) = ((c.x : ℤ) : ℚ) - 1; push_cast; ring
  rw [h_cx1, h_cx0]
  have h_divx : (ofInt c.x - 1 - A.x) / (B.x - A.x) = tx1 - 1 / dx := by
    dsimp [tx1, dx]; ring
  rw [h_divx]
  simp only [Bool.false_eq_true, ↓reduceIte]
  change (if tEnter ≤ tExit then some (tEnter, tExit) else none) = some (tEnter, tExit)
  have h_le : tEnter ≤ tExit := le_of_lt h_lt
  simp only [h_le, ↓reduceIte]


theorem cellIntersectionInterval_stepY_neg_neg (A B : Point) (c : Cell)
    (hdx : B.x - A.x < 0) (hdy : B.y - A.y < 0) :
    let dx := B.x - A.x
    let dy := B.y - A.y
    let tx0 := (ofInt (c.x + 1) - A.x) / dx
    let tx1 := (ofInt c.x - A.x) / dx
    let ty1 := (ofInt c.y - A.y) / dy
    let tEnter := max 0 (max tx0 ty1)
    let tExit := min 1 (min tx1 (ty1 - 1 / dy))
    tEnter < tExit →
    cellIntersectionInterval ⟨c.x, c.y - 1⟩ A B = some (tEnter, tExit) := by
  intro dx dy tx0 tx1 ty1 tEnter tExit h_lt
  unfold cellIntersectionInterval; dsimp only []
  have h_dx_ne : (B.x - A.x == 0) = false := by
    cases h : (B.x - A.x == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_dy_ne : (B.y - A.y == 0) = false := by
    cases h : (B.y - A.y == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_not_dx_pos : ¬(B.x - A.x > 0) := by linarith
  have h_not_dy_pos : ¬(B.y - A.y > 0) := by linarith
  simp only [h_dx_ne, h_dy_ne, h_not_dx_pos, h_not_dy_pos, ↓reduceIte]
  have h_cy1 : ofInt (c.y - 1 + 1) = ofInt c.y := by
    unfold ofInt; congr 1; omega
  have h_cy0 : ofInt (c.y - 1) = ofInt c.y - 1 := by
    unfold ofInt; change ((c.y - 1 : ℤ) : ℚ) = ((c.y : ℤ) : ℚ) - 1; push_cast; ring
  rw [h_cy1, h_cy0]
  have h_divy : (ofInt c.y - 1 - A.y) / (B.y - A.y) = ty1 - 1 / dy := by
    dsimp [ty1, dy]; ring
  rw [h_divy]
  simp only [Bool.false_eq_true, ↓reduceIte]
  change (if tEnter ≤ tExit then some (tEnter, tExit) else none) = some (tEnter, tExit)
  have h_le : tEnter ≤ tExit := le_of_lt h_lt
  simp only [h_le, ↓reduceIte]


theorem cellIntersectionInterval_diag_neg_neg (A B : Point) (c : Cell)
    (hdx : B.x - A.x < 0) (hdy : B.y - A.y < 0) :
    let dx := B.x - A.x
    let dy := B.y - A.y
    let t := (ofInt c.x - A.x) / dx
    let tEnter := max 0 (max t t)
    let tExit := min 1 (min (t - 1 / dx) (t - 1 / dy))
    t = (ofInt c.y - A.y) / dy →
    tEnter < tExit →
    cellIntersectionInterval ⟨c.x - 1, c.y - 1⟩ A B = some (tEnter, tExit) := by
  intro dx dy t tEnter tExit h_eq h_lt
  unfold cellIntersectionInterval; dsimp only []
  have h_dx_ne : (B.x - A.x == 0) = false := by
    cases h : (B.x - A.x == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_dy_ne : (B.y - A.y == 0) = false := by
    cases h : (B.y - A.y == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_not_dx_pos : ¬(B.x - A.x > 0) := by linarith
  have h_not_dy_pos : ¬(B.y - A.y > 0) := by linarith
  simp only [h_dx_ne, h_dy_ne, h_not_dx_pos, h_not_dy_pos, ↓reduceIte]
  have h_cx1 : ofInt (c.x - 1 + 1) = ofInt c.x := by
    unfold ofInt; congr 1; omega
  have h_cx0 : ofInt (c.x - 1) = ofInt c.x - 1 := by
    unfold ofInt; change ((c.x - 1 : ℤ) : ℚ) = ((c.x : ℤ) : ℚ) - 1; push_cast; ring
  have h_cy1 : ofInt (c.y - 1 + 1) = ofInt c.y := by
    unfold ofInt; congr 1; omega
  have h_cy0 : ofInt (c.y - 1) = ofInt c.y - 1 := by
    unfold ofInt; change ((c.y - 1 : ℤ) : ℚ) = ((c.y : ℤ) : ℚ) - 1; push_cast; ring
  rw [h_cx1, h_cx0, h_cy1, h_cy0]
  have h_divx : (ofInt c.x - 1 - A.x) / (B.x - A.x) = t - 1 / dx := by
    dsimp [t, dx]; ring
  have h_divy : (ofInt c.y - 1 - A.y) / (B.y - A.y) = t - 1 / dy := by
    rw [h_eq]; dsimp [dy]; ring
  rw [h_divx, h_divy]
  have h_ty : (ofInt c.y - A.y) / (B.y - A.y) = t := by
    dsimp [dy] at h_eq; exact h_eq.symm
  rw [h_ty]
  simp only [Bool.false_eq_true, ↓reduceIte]
  change (if tEnter ≤ tExit then some (tEnter, tExit) else none) = some (tEnter, tExit)
  have h_le : tEnter ≤ tExit := le_of_lt h_lt
  simp only [h_le, ↓reduceIte]


theorem extract_stepX_neg_neg (A B : Point) (c : Cell)
    (_hdx : B.x - A.x < 0) (_hdy : B.y - A.y < 0)
    (h_step : rayMarchStep A B (B.x - A.x) (B.y - A.y) (-1) (-1) c = (⟨c.x - 1, c.y⟩, false)) :
    remX_val A (-1) c * absVal (B.y - A.y) < remY_val A (-1) c * absVal (B.x - A.x) ∧
    min (remX_val A (-1) c * absVal (B.y - A.y)) (remY_val A (-1) c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y) := by
  unfold rayMarchStep at h_step; dsimp only [] at h_step
  simp only [show ((-1 : ℤ) == 0) = false by decide, Bool.false_eq_true, ↓reduceIte] at h_step
  by_cases hlim : min
        ((if (if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y))
        ((if (if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) ≥
      (if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) * if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
  · simp only [hlim, ↓reduceIte] at h_step; injection h_step with _ h_bool; contradiction
  · simp only [hlim, ↓reduceIte] at h_step
    by_cases hxy : ((if (if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)) <
        (if (if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)
    · unfold remX_val remY_val absVal; dsimp only []
      simp only [show ¬((-1 : ℤ) > 0) by decide, ↓reduceIte]
      refine ⟨hxy, not_le.mp hlim⟩
    · simp only [hxy, ↓reduceIte] at h_step
      by_cases hyx : ((if (if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
              (if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
            else A.y - if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) *
            if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) <
          (if (if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
              (if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
            else A.x - if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) *
            if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
      · simp only [hyx, ↓reduceIte] at h_step; injection h_step with h_cell _; injection h_cell with _ hy; omega
      · simp only [hyx, ↓reduceIte] at h_step; injection h_step with h_cell _; injection h_cell with hx _; omega


theorem extract_stepY_neg_neg (A B : Point) (c : Cell)
    (_hdx : B.x - A.x < 0) (_hdy : B.y - A.y < 0)
    (h_step : rayMarchStep A B (B.x - A.x) (B.y - A.y) (-1) (-1) c = (⟨c.x, c.y - 1⟩, false)) :
    remY_val A (-1) c * absVal (B.x - A.x) < remX_val A (-1) c * absVal (B.y - A.y) ∧
    min (remX_val A (-1) c * absVal (B.y - A.y)) (remY_val A (-1) c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y) := by
  unfold rayMarchStep at h_step; dsimp only [] at h_step
  simp only [show ((-1 : ℤ) == 0) = false by decide, Bool.false_eq_true, ↓reduceIte] at h_step
  by_cases hlim : min
        ((if (if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y))
        ((if (if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) ≥
      (if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) * if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
  · simp only [hlim, ↓reduceIte] at h_step; injection h_step with _ h_bool; contradiction
  · simp only [hlim, ↓reduceIte] at h_step
    by_cases hxy : ((if (if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)) <
        (if (if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)
    · simp only [hxy, ↓reduceIte] at h_step; injection h_step with h_cell _; injection h_cell with _ hy; omega
    · simp only [hxy, ↓reduceIte] at h_step
      by_cases hyx : ((if (if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
              (if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
            else A.y - if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) *
            if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) <
          (if (if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
              (if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
            else A.x - if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) *
            if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
      · unfold remX_val remY_val absVal; dsimp only []
        simp only [show ¬((-1 : ℤ) > 0) by decide, ↓reduceIte]
        refine ⟨hyx, not_le.mp hlim⟩
      · simp only [hyx, ↓reduceIte] at h_step; injection h_step with h_cell _; injection h_cell with hx _; omega


theorem extract_stepDiag_neg_neg (A B : Point) (c : Cell)
    (_hdx : B.x - A.x < 0) (_hdy : B.y - A.y < 0)
    (h_step : rayMarchStep A B (B.x - A.x) (B.y - A.y) (-1) (-1) c = (⟨c.x - 1, c.y - 1⟩, false)) :
    remX_val A (-1) c * absVal (B.y - A.y) = remY_val A (-1) c * absVal (B.x - A.x) ∧
    min (remX_val A (-1) c * absVal (B.y - A.y)) (remY_val A (-1) c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y) := by
  unfold rayMarchStep at h_step; dsimp only [] at h_step
  simp only [show ((-1 : ℤ) == 0) = false by decide, Bool.false_eq_true, ↓reduceIte] at h_step
  by_cases hlim : min
        ((if (if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y))
        ((if (if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) ≥
      (if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) * if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
  · simp only [hlim, ↓reduceIte] at h_step; injection h_step with _ h_bool; contradiction
  · simp only [hlim, ↓reduceIte] at h_step
    by_cases hxy : ((if (if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
            (if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
          else A.x - if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) *
          if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)) <
        (if (if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
            (if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
          else A.y - if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) *
          if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)
    · simp only [hxy, ↓reduceIte] at h_step; injection h_step with h_cell _; injection h_cell with _ hy; omega
    · simp only [hxy, ↓reduceIte] at h_step
      by_cases hyx : ((if (if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
              (if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
            else A.y - if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) *
            if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) <
          (if (if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
              (if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
            else A.x - if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) *
            if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)
      · simp only [hyx, ↓reduceIte] at h_step; injection h_step with h_cell _; injection h_cell with hx _; omega
      · unfold remX_val remY_val absVal; dsimp only []
        simp only [show ¬((-1 : ℤ) > 0) by decide, ↓reduceIte] at *
        refine ⟨by linarith, not_le.mp hlim⟩


theorem rayMarchStep_X_neg_neg_sound (A B : Point) (c : Cell)
    (hdx : B.x - A.x < 0) (hdy : B.y - A.y < 0)
    (hc_bbox : inBoundingBox c A B = true)
    (hc_valid : c = floorPoint A ∨ ∃ tEnter tExit, cellIntersectionInterval c A B = some (tEnter, tExit) ∧ tEnter < tExit)
    (h_step : remX_val A (-1) c * absVal (B.y - A.y) < remY_val A (-1) c * absVal (B.x - A.x))
    (h_not_done : min (remX_val A (-1) c * absVal (B.y - A.y)) (remY_val A (-1) c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y)) :
    inBoundingBox ⟨c.x - 1, c.y⟩ A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval ⟨c.x - 1, c.y⟩ A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  have h_absDy : 0 < absVal (B.y - A.y) := by unfold absVal; split_ifs <;> linarith
  have h_bnd := stepX_bounded (remX_val A (-1) c) (absVal (B.x - A.x)) (absVal (B.y - A.y))
    (remY_val A (-1) c * absVal (B.x - A.x)) h_absDy h_step h_not_done
  unfold absVal at h_bnd; simp [show ¬(B.x - A.x ≥ 0) by linarith] at h_bnd
  unfold remX_val at h_bnd; simp only [show ¬((-1 : ℤ) > 0) by decide, ↓reduceIte] at h_bnd
  have hc_prop := hc_bbox; unfold inBoundingBox at hc_prop; dsimp only [] at hc_prop
  simp only [Bool.and_eq_true, decide_eq_true_iff] at hc_prop
  have h_flAx : c.x ≤ (floorPoint A).x := by
    have h_max := hc_prop.1.1.2
    have h_le : (floorPoint B).x ≤ (floorPoint A).x := floor_mono (by linarith)
    have h_max_eq : max (floorPoint A).x (floorPoint B).x = (floorPoint A).x := max_eq_left h_le
    rw [h_max_eq] at h_max; exact h_max
  have h_flAy : c.y ≤ (floorPoint A).y := by
    have h_max := hc_prop.2
    have h_le : (floorPoint B).y ≤ (floorPoint A).y := floor_mono (by linarith)
    have h_max_eq : max (floorPoint A).y (floorPoint B).y = (floorPoint A).y := max_eq_left h_le
    rw [h_max_eq] at h_max; exact h_max
  have h_remX_ge : ofInt c.x ≤ A.x := by
    unfold floorPoint toInt at h_flAx; dsimp at h_flAx
    have h_le := Rat.floor_le A.x
    have h_flAx_rat : (c.x : ℚ) ≤ ((A.x.floor : ℤ) : ℚ) := Int.cast_le.mpr h_flAx
    have h_ofInt : ofInt c.x = (c.x : ℚ) := rfl
    rw [h_ofInt]; linarith
  have h_remY_ge : ofInt c.y ≤ A.y := by
    unfold floorPoint toInt at h_flAy; dsimp at h_flAy
    have h_le := Rat.floor_le A.y
    have h_flAy_rat : (c.y : ℚ) ≤ ((A.y.floor : ℤ) : ℚ) := Int.cast_le.mpr h_flAy
    have h_ofInt : ofInt c.y = (c.y : ℚ) := rfl
    rw [h_ofInt]; linarith
  have h_remX_split : (if ofInt c.x ≥ A.x then ofInt c.x - A.x else A.x - ofInt c.x) = A.x - ofInt c.x := by
    split_ifs with h <;> [linarith; rfl]
  rw [h_remX_split] at h_bnd
  have h_div_bnd : (ofInt c.x - A.x) / (B.x - A.x) < 1 := by
    have h_lt_neg : A.x - ofInt c.x < -(B.x - A.x) := by linarith [h_bnd]
    have : (A.x - ofInt c.x) / -(B.x - A.x) < 1 := (div_lt_one (by linarith)).mpr h_lt_neg
    have h_num : A.x - ofInt c.x = -(ofInt c.x - A.x) := by ring
    rw [h_num, neg_div_neg_eq] at this; exact this
  have h_le := stepX_neg_next_ge_end c.x A.x B hdx h_div_bnd
  have h_bbox_next := inBoundingBox_stepX_backward c A B hdx hc_bbox h_le
  refine ⟨h_bbox_next, ?_⟩
  unfold remY_val absVal at h_step
  simp only [show ¬((-1 : ℤ) > 0) by decide, ↓reduceIte, show ¬(B.y - A.y ≥ 0) by linarith, show ¬(B.x - A.x ≥ 0) by linarith] at h_step
  unfold remX_val at h_step
  simp only [show ¬((-1 : ℤ) > 0) by decide, ↓reduceIte] at h_step
  rw [h_remX_split] at h_step
  have h_remY_split : (if ofInt c.y ≥ A.y then ofInt c.y - A.y else A.y - ofInt c.y) = A.y - ofInt c.y := by
    split_ifs with h <;> [linarith; rfl]
  rw [h_remY_split] at h_step
  let tx1 := (ofInt c.x - A.x) / (B.x - A.x)
  let ty0 := (ofInt (c.y + 1) - A.y) / (B.y - A.y)
  let ty1 := (ofInt c.y - A.y) / (B.y - A.y)
  have h_tx1_eq : (A.x - ofInt c.x) / -(B.x - A.x) = tx1 := by
    dsimp [tx1]; have h_num : A.x - ofInt c.x = -(ofInt c.x - A.x) := by ring
    rw [h_num, neg_div_neg_eq]
  have h_ty1_eq : (A.y - ofInt c.y) / -(B.y - A.y) = ty1 := by
    dsimp [ty1]; have h_num : A.y - ofInt c.y = -(ofInt c.y - A.y) := by ring
    rw [h_num, neg_div_neg_eq]
  have h_cross : tx1 < ty1 := by
    have h_cross_div := (cross_lt_cross_iff_div_lt_div (A.x - ofInt c.x) (A.y - ofInt c.y) (-(B.x - A.x)) (-(B.y - A.y)) (by linarith) (by linarith)).mp h_step
    rw [h_tx1_eq, h_ty1_eq] at h_cross_div
    exact h_cross_div
  have h_lim : tx1 < 1 := h_div_bnd
  have h_pos_val : 0 ≤ tx1 := by rw [← h_tx1_eq]; exact div_nonneg (by linarith) (by linarith)
  have h_ty0 : ty0 ≤ tx1 := by
    cases hc_valid with
    | inl h_cA =>
      subst h_cA; dsimp [tx1, ty0]
      have h1 : (ofInt ((floorPoint A).y + 1) - A.y) / (B.y - A.y) ≤ 0 := by
        unfold floorPoint toInt; dsimp
        have h_lt := Rat.lt_floor_add_one A.y; push_cast at h_lt
        have h_num : 0 < ofInt (A.y.floor + 1) - A.y := by
          unfold ofInt; change 0 < ((A.y.floor + 1 : ℤ) : ℚ) - A.y; push_cast; linarith
        exact div_nonpos_of_nonneg_of_nonpos (le_of_lt h_num) (le_of_lt hdy)
      linarith
    | inr h_int =>
      rcases h_int with ⟨tEnter_c, tExit_c, hc_inter, _⟩
      have h_dx_prop := interval_dx_neg c A B tEnter_c tExit_c hc_inter hdx
      have h_dy_prop := interval_dy_neg c A B tEnter_c tExit_c hc_inter hdy
      dsimp [tx1, ty0]; linarith [h_dy_prop.1, h_dx_prop.2]
  have h_lt := stepX_interval_lt_neg tx1 ty0 ty1 (B.x - A.x) hdx h_cross h_lim h_pos_val h_ty0
  let tEnter := max 0 (max tx1 ty0)
  let tExit := min 1 (min (tx1 - 1 / (B.x - A.x)) ty1)
  have h_eval := cellIntersectionInterval_stepX_neg_neg A B c hdx hdy h_lt
  exact ⟨tEnter, tExit, h_eval, h_lt⟩


theorem rayMarchStep_Y_neg_neg_sound (A B : Point) (c : Cell)
    (hdx : B.x - A.x < 0) (hdy : B.y - A.y < 0)
    (hc_bbox : inBoundingBox c A B = true)
    (hc_valid : c = floorPoint A ∨ ∃ tEnter tExit, cellIntersectionInterval c A B = some (tEnter, tExit) ∧ tEnter < tExit)
    (h_step : remY_val A (-1) c * absVal (B.x - A.x) < remX_val A (-1) c * absVal (B.y - A.y))
    (h_not_done : min (remX_val A (-1) c * absVal (B.y - A.y)) (remY_val A (-1) c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y)) :
    inBoundingBox ⟨c.x, c.y - 1⟩ A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval ⟨c.x, c.y - 1⟩ A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  have h_absDx : 0 < absVal (B.x - A.x) := by unfold absVal; split_ifs <;> linarith
  have h_bnd := stepY_bounded (remY_val A (-1) c) (absVal (B.x - A.x)) (absVal (B.y - A.y))
    (remX_val A (-1) c * absVal (B.y - A.y)) h_absDx h_step h_not_done
  unfold absVal at h_bnd; simp [show ¬(B.y - A.y ≥ 0) by linarith] at h_bnd
  unfold remY_val at h_bnd; simp only [show ¬((-1 : ℤ) > 0) by decide, ↓reduceIte] at h_bnd
  have hc_prop := hc_bbox; unfold inBoundingBox at hc_prop; dsimp only [] at hc_prop
  simp only [Bool.and_eq_true, decide_eq_true_iff] at hc_prop
  have h_flAx : c.x ≤ (floorPoint A).x := by
    have h_max := hc_prop.1.1.2
    have h_le : (floorPoint B).x ≤ (floorPoint A).x := floor_mono (by linarith)
    have h_max_eq : max (floorPoint A).x (floorPoint B).x = (floorPoint A).x := max_eq_left h_le
    rw [h_max_eq] at h_max; exact h_max
  have h_flAy : c.y ≤ (floorPoint A).y := by
    have h_max := hc_prop.2
    have h_le : (floorPoint B).y ≤ (floorPoint A).y := floor_mono (by linarith)
    have h_max_eq : max (floorPoint A).y (floorPoint B).y = (floorPoint A).y := max_eq_left h_le
    rw [h_max_eq] at h_max; exact h_max
  have h_remX_ge : ofInt c.x ≤ A.x := by
    unfold floorPoint toInt at h_flAx; dsimp at h_flAx
    have h_le := Rat.floor_le A.x
    have h_flAx_rat : (c.x : ℚ) ≤ ((A.x.floor : ℤ) : ℚ) := Int.cast_le.mpr h_flAx
    have h_ofInt : ofInt c.x = (c.x : ℚ) := rfl
    rw [h_ofInt]; linarith
  have h_remY_ge : ofInt c.y ≤ A.y := by
    unfold floorPoint toInt at h_flAy; dsimp at h_flAy
    have h_le := Rat.floor_le A.y
    have h_flAy_rat : (c.y : ℚ) ≤ ((A.y.floor : ℤ) : ℚ) := Int.cast_le.mpr h_flAy
    have h_ofInt : ofInt c.y = (c.y : ℚ) := rfl
    rw [h_ofInt]; linarith
  have h_remY_split : (if ofInt c.y ≥ A.y then ofInt c.y - A.y else A.y - ofInt c.y) = A.y - ofInt c.y := by
    split_ifs with h <;> [linarith; rfl]
  rw [h_remY_split] at h_bnd
  have h_div_bnd : (ofInt c.y - A.y) / (B.y - A.y) < 1 := by
    have h_lt_neg : A.y - ofInt c.y < -(B.y - A.y) := by linarith [h_bnd]
    have : (A.y - ofInt c.y) / -(B.y - A.y) < 1 := (div_lt_one (by linarith)).mpr h_lt_neg
    have h_num : A.y - ofInt c.y = -(ofInt c.y - A.y) := by ring
    rw [h_num, neg_div_neg_eq] at this; exact this
  have h_le := stepY_neg_next_ge_end c.y A.y B hdy h_div_bnd
  have h_bbox_next := inBoundingBox_stepY_backward c A B hdy hc_bbox h_le
  refine ⟨h_bbox_next, ?_⟩
  unfold remX_val absVal at h_step
  simp only [show ¬((-1 : ℤ) > 0) by decide, ↓reduceIte, show ¬(B.x - A.x ≥ 0) by linarith, show ¬(B.y - A.y ≥ 0) by linarith] at h_step
  unfold remY_val at h_step
  simp only [show ¬((-1 : ℤ) > 0) by decide, ↓reduceIte] at h_step
  rw [h_remY_split] at h_step
  have h_remX_split : (if ofInt c.x ≥ A.x then ofInt c.x - A.x else A.x - ofInt c.x) = A.x - ofInt c.x := by
    split_ifs with h <;> [linarith; rfl]
  rw [h_remX_split] at h_step
  let tx0 := (ofInt (c.x + 1) - A.x) / (B.x - A.x)
  let tx1 := (ofInt c.x - A.x) / (B.x - A.x)
  let ty1 := (ofInt c.y - A.y) / (B.y - A.y)
  have h_tx1_eq : (A.x - ofInt c.x) / -(B.x - A.x) = tx1 := by
    dsimp [tx1]; have h_num : A.x - ofInt c.x = -(ofInt c.x - A.x) := by ring
    rw [h_num, neg_div_neg_eq]
  have h_ty1_eq : (A.y - ofInt c.y) / -(B.y - A.y) = ty1 := by
    dsimp [ty1]; have h_num : A.y - ofInt c.y = -(ofInt c.y - A.y) := by ring
    rw [h_num, neg_div_neg_eq]
  have h_cross : ty1 < tx1 := by
    have h_cross_div := (cross_lt_cross_iff_div_lt_div (A.y - ofInt c.y) (A.x - ofInt c.x) (-(B.y - A.y)) (-(B.x - A.x)) (by linarith) (by linarith)).mp h_step
    rw [h_tx1_eq, h_ty1_eq] at h_cross_div
    exact h_cross_div
  have h_lim : ty1 < 1 := h_div_bnd
  have h_pos_val : 0 ≤ ty1 := by rw [← h_ty1_eq]; exact div_nonneg (by linarith) (by linarith)
  have h_tx0 : tx0 ≤ ty1 := by
    cases hc_valid with
    | inl h_cA =>
      subst h_cA; dsimp [tx0, ty1]
      have h1 : (ofInt ((floorPoint A).x + 1) - A.x) / (B.x - A.x) ≤ 0 := by
        unfold floorPoint toInt; dsimp
        have h_lt := Rat.lt_floor_add_one A.x; push_cast at h_lt
        have h_num : 0 < ofInt (A.x.floor + 1) - A.x := by
          unfold ofInt; change 0 < ((A.x.floor + 1 : ℤ) : ℚ) - A.x; push_cast; linarith
        exact div_nonpos_of_nonneg_of_nonpos (le_of_lt h_num) (le_of_lt hdx)
      linarith
    | inr h_int =>
      rcases h_int with ⟨tEnter_c, tExit_c, hc_inter, _⟩
      have h_dx_prop := interval_dx_neg c A B tEnter_c tExit_c hc_inter hdx
      have h_dy_prop := interval_dy_neg c A B tEnter_c tExit_c hc_inter hdy
      dsimp [tx0, ty1]; linarith [h_dx_prop.1, h_dy_prop.2]
  have h_lt := stepY_interval_lt_neg ty1 tx0 tx1 (B.y - A.y) hdy h_cross h_lim h_pos_val h_tx0
  let tEnter := max 0 (max tx0 ty1)
  let tExit := min 1 (min tx1 (ty1 - 1 / (B.y - A.y)))
  have h_eval := cellIntersectionInterval_stepY_neg_neg A B c hdx hdy h_lt
  exact ⟨tEnter, tExit, h_eval, h_lt⟩


theorem rayMarchStep_Diag_neg_neg_sound (A B : Point) (c : Cell)
    (hdx : B.x - A.x < 0) (hdy : B.y - A.y < 0)
    (hc_bbox : inBoundingBox c A B = true)
    (_hc_valid : c = floorPoint A ∨ ∃ tEnter tExit, cellIntersectionInterval c A B = some (tEnter, tExit) ∧ tEnter < tExit)
    (h_step : remX_val A (-1) c * absVal (B.y - A.y) = remY_val A (-1) c * absVal (B.x - A.x))
    (h_not_done : min (remX_val A (-1) c * absVal (B.y - A.y)) (remY_val A (-1) c * absVal (B.x - A.x)) < absVal (B.x - A.x) * absVal (B.y - A.y)) :
    inBoundingBox ⟨c.x - 1, c.y - 1⟩ A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval ⟨c.x - 1, c.y - 1⟩ A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  have h_absDx : 0 < absVal (B.x - A.x) := by unfold absVal; split_ifs <;> linarith
  have h_absDy : 0 < absVal (B.y - A.y) := by unfold absVal; split_ifs <;> linarith
  have ⟨h_bndX, h_bndY⟩ := stepDiag_bounded (remX_val A (-1) c) (remY_val A (-1) c)
    (absVal (B.x - A.x)) (absVal (B.y - A.y)) h_absDx h_absDy h_step h_not_done
  unfold absVal at h_bndX h_bndY
  simp [show ¬(B.x - A.x ≥ 0) by linarith, show ¬(B.y - A.y ≥ 0) by linarith] at h_bndX h_bndY
  unfold remX_val at h_bndX
  unfold remY_val at h_bndY
  simp only [show ¬((-1 : ℤ) > 0) by decide, ↓reduceIte] at h_bndX
  simp only [show ¬((-1 : ℤ) > 0) by decide, ↓reduceIte] at h_bndY
  have hc_prop := hc_bbox; unfold inBoundingBox at hc_prop; dsimp only [] at hc_prop
  simp only [Bool.and_eq_true, decide_eq_true_iff] at hc_prop
  have h_flAx : c.x ≤ (floorPoint A).x := by
    have h_max := hc_prop.1.1.2
    have h_le : (floorPoint B).x ≤ (floorPoint A).x := floor_mono (by linarith)
    have h_max_eq : max (floorPoint A).x (floorPoint B).x = (floorPoint A).x := max_eq_left h_le
    rw [h_max_eq] at h_max; exact h_max
  have h_flAy : c.y ≤ (floorPoint A).y := by
    have h_max := hc_prop.2
    have h_le : (floorPoint B).y ≤ (floorPoint A).y := floor_mono (by linarith)
    have h_max_eq : max (floorPoint A).y (floorPoint B).y = (floorPoint A).y := max_eq_left h_le
    rw [h_max_eq] at h_max; exact h_max
  have h_remX_ge : ofInt c.x ≤ A.x := by
    unfold floorPoint toInt at h_flAx; dsimp at h_flAx
    have h_le := Rat.floor_le A.x
    have h_flAx_rat : (c.x : ℚ) ≤ ((A.x.floor : ℤ) : ℚ) := Int.cast_le.mpr h_flAx
    have h_ofInt : ofInt c.x = (c.x : ℚ) := rfl
    rw [h_ofInt]; linarith
  have h_remY_ge : ofInt c.y ≤ A.y := by
    unfold floorPoint toInt at h_flAy; dsimp at h_flAy
    have h_le := Rat.floor_le A.y
    have h_flAy_rat : (c.y : ℚ) ≤ ((A.y.floor : ℤ) : ℚ) := Int.cast_le.mpr h_flAy
    have h_ofInt : ofInt c.y = (c.y : ℚ) := rfl
    rw [h_ofInt]; linarith
  have h_remX_split : (if ofInt c.x ≥ A.x then ofInt c.x - A.x else A.x - ofInt c.x) = A.x - ofInt c.x := by
    split_ifs with h <;> [linarith; rfl]
  have h_remY_split : (if ofInt c.y ≥ A.y then ofInt c.y - A.y else A.y - ofInt c.y) = A.y - ofInt c.y := by
    split_ifs with h <;> [linarith; rfl]
  rw [h_remX_split] at h_bndX
  rw [h_remY_split] at h_bndY
  have h_div_bndX : (ofInt c.x - A.x) / (B.x - A.x) < 1 := by
    have h_lt_neg : A.x - ofInt c.x < -(B.x - A.x) := by linarith [h_bndX]
    have : (A.x - ofInt c.x) / -(B.x - A.x) < 1 := (div_lt_one (by linarith)).mpr h_lt_neg
    have h_num : A.x - ofInt c.x = -(ofInt c.x - A.x) := by ring
    rw [h_num, neg_div_neg_eq] at this; exact this
  have h_div_bndY : (ofInt c.y - A.y) / (B.y - A.y) < 1 := by
    have h_lt_neg : A.y - ofInt c.y < -(B.y - A.y) := by linarith [h_bndY]
    have : (A.y - ofInt c.y) / -(B.y - A.y) < 1 := (div_lt_one (by linarith)).mpr h_lt_neg
    have h_num : A.y - ofInt c.y = -(ofInt c.y - A.y) := by ring
    rw [h_num, neg_div_neg_eq] at this; exact this
  have h_le_x := stepX_neg_next_ge_end c.x A.x B hdx h_div_bndX
  have h_le_y := stepY_neg_next_ge_end c.y A.y B hdy h_div_bndY
  have h_bbox_next := inBoundingBox_diag_neg_neg c A B hdx hdy hc_bbox h_le_x h_le_y
  refine ⟨h_bbox_next, ?_⟩
  unfold remX_val remY_val absVal at h_step
  simp only [show ¬((-1 : ℤ) > 0) by decide, ↓reduceIte,
    show ¬(B.y - A.y ≥ 0) by linarith, show ¬(B.x - A.x ≥ 0) by linarith] at h_step
  rw [h_remX_split, h_remY_split] at h_step
  let t := (ofInt c.x - A.x) / (B.x - A.x)
  have h_t_eq : t = (ofInt c.y - A.y) / (B.y - A.y) := by
    dsimp [t]
    have h_cross := (cross_eq_cross_iff_div_eq_div (A.x - ofInt c.x) (A.y - ofInt c.y) (-(B.x - A.x)) (-(B.y - A.y)) (by linarith) (by linarith)).mp h_step
    have h_numX : A.x - ofInt c.x = -(ofInt c.x - A.x) := by ring
    have h_numY : A.y - ofInt c.y = -(ofInt c.y - A.y) := by ring
    have h_LHS : (A.x - ofInt c.x) / -(B.x - A.x) = (ofInt c.x - A.x) / (B.x - A.x) := by rw [h_numX, neg_div_neg_eq]
    have h_RHS : (A.y - ofInt c.y) / -(B.y - A.y) = (ofInt c.y - A.y) / (B.y - A.y) := by rw [h_numY, neg_div_neg_eq]
    rw [h_LHS, h_RHS] at h_cross
    exact h_cross
  have h_lim : t < 1 := h_div_bndX
  have h_pos : 0 ≤ t := by
    have h_num : A.x - ofInt c.x = -(ofInt c.x - A.x) := by ring
    have h_tx1_eq : (A.x - ofInt c.x) / -(B.x - A.x) = t := by dsimp [t]; rw [h_num, neg_div_neg_eq]
    rw [← h_tx1_eq]; exact div_nonneg (by linarith) (by linarith)
  have h_lt := stepDiag_interval_lt_neg_neg t (B.x - A.x) (B.y - A.y) hdx hdy h_lim h_pos
  let tEnter := max 0 (max t t)
  let tExit := min 1 (min (t - 1 / (B.x - A.x)) (t - 1 / (B.y - A.y)))
  have h_eval := cellIntersectionInterval_diag_neg_neg A B c hdx hdy h_t_eq h_lt
  exact ⟨tEnter, tExit, h_eval, h_lt⟩


theorem rayMarchStep_sound_step_neg_neg (A B : Point) (dx dy : ℚ) (stepX stepY : ℤ) (c : Cell)
    (hdx : dx = B.x - A.x) (hdy : dy = B.y - A.y)
    (hstepX : stepX = if dx > 0 then 1 else if dx < 0 then -1 else 0)
    (hstepY : stepY = if dy > 0 then 1 else if dy < 0 then -1 else 0)
    (h_neg_neg : dx < 0 ∧ dy < 0)
    (hc_bbox : inBoundingBox c A B = true)
    (hc_valid : c = floorPoint A ∨ ∃ tEnter tExit, cellIntersectionInterval c A B = some (tEnter, tExit) ∧ tEnter < tExit)
    (h_not_done : (rayMarchStep A B dx dy stepX stepY c).2 = false) :
    inBoundingBox (rayMarchStep A B dx dy stepX stepY c).1 A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval (rayMarchStep A B dx dy stepX stepY c).1 A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  have hsx : stepX = -1 := by rw [hstepX]; simp [show ¬(dx > 0) by linarith [h_neg_neg.1], h_neg_neg.1]
  have hsy : stepY = -1 := by rw [hstepY]; simp [show ¬(dy > 0) by linarith [h_neg_neg.2], h_neg_neg.2]
  have h_cases := rayMarchStep_cases A B dx dy stepX stepY c
  rcases h_cases with h1 | h2 | h3 | h4
  · rw [h1] at h_not_done; contradiction
  · rw [h2]; dsimp only []
    have h_step_eq : rayMarchStep A B (B.x - A.x) (B.y - A.y) (-1) (-1) c = (⟨c.x - 1, c.y⟩, false) := by
      subst hdx; subst hdy; subst hsx; subst hsy; exact h2
    have ⟨h_step, h_lim⟩ := extract_stepX_neg_neg A B c (by linarith [h_neg_neg.1, hdx]) (by linarith [h_neg_neg.2, hdy]) h_step_eq
    rw [hsx]
    exact rayMarchStep_X_neg_neg_sound A B c (by linarith [h_neg_neg.1, hdx]) (by linarith [h_neg_neg.2, hdy]) hc_bbox hc_valid h_step h_lim
  · rw [h3]; dsimp only []
    have h_step_eq : rayMarchStep A B (B.x - A.x) (B.y - A.y) (-1) (-1) c = (⟨c.x, c.y - 1⟩, false) := by
      subst hdx; subst hdy; subst hsx; subst hsy; exact h3
    have ⟨h_step, h_lim⟩ := extract_stepY_neg_neg A B c (by linarith [h_neg_neg.1, hdx]) (by linarith [h_neg_neg.2, hdy]) h_step_eq
    rw [hsy]
    exact rayMarchStep_Y_neg_neg_sound A B c (by linarith [h_neg_neg.1, hdx]) (by linarith [h_neg_neg.2, hdy]) hc_bbox hc_valid h_step h_lim
  · rw [h4]; dsimp only []
    have h_step_eq : rayMarchStep A B (B.x - A.x) (B.y - A.y) (-1) (-1) c = (⟨c.x - 1, c.y - 1⟩, false) := by
      subst hdx; subst hdy; subst hsx; subst hsy; exact h4
    have ⟨h_step, h_lim⟩ := extract_stepDiag_neg_neg A B c (by linarith [h_neg_neg.1, hdx]) (by linarith [h_neg_neg.2, hdy]) h_step_eq
    rw [hsx, hsy]
    exact rayMarchStep_Diag_neg_neg_sound A B c (by linarith [h_neg_neg.1, hdx]) (by linarith [h_neg_neg.2, hdy]) hc_bbox hc_valid h_step h_lim


theorem rayMarch_soundness_neg_neg (A B : Point) (x : Cell)
    (hdx : B.x - A.x < 0) (hdy : B.y - A.y < 0)
    (hx : x ∈ rayMarch (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 2)
      A B (B.x - A.x) (B.y - A.y)
      (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0)
      (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0)
      (floorPoint B) (floorPoint A) []) :
    inBoundingBox x A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval x A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  have hsx : (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else (0 : ℤ)) = -1 := by
    simp [show ¬(B.x - A.x > 0) by linarith, hdx]
  have hsy : (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else (0 : ℤ)) = -1 := by
    simp [show ¬(B.y - A.y > 0) by linarith, hdy]
  rw [hsx, hsy] at hx
  have h_fuel : (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 2) =
    (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 1) + 1 := by omega
  rw [h_fuel] at hx
  apply sound_from_first_step _ _ _ _ _ _ _ (floorPoint B) (fun cell =>
    inBoundingBox cell A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval cell A B = some (tEnter, tExit) ∧ tEnter < tExit)
    _ _ x hx
  · intro c hc h_not_done
    exact rayMarchStep_sound_step_neg_neg A B (B.x - A.x) (B.y - A.y) (-1) (-1) c rfl rfl (by simp [show ¬(B.x - A.x > 0) by linarith, hdx]) (by simp [show ¬(B.y - A.y > 0) by linarith, hdy]) ⟨hdx, hdy⟩ hc.1 (Or.inr hc.2) h_not_done
  · intro h_not_done
    exact rayMarchStep_sound_step_neg_neg A B (B.x - A.x) (B.y - A.y) (-1) (-1) (floorPoint A) rfl rfl (by simp [show ¬(B.x - A.x > 0) by linarith, hdx]) (by simp [show ¬(B.y - A.y > 0) by linarith, hdy]) ⟨hdx, hdy⟩ (inBoundingBox_startCell A B) (Or.inl rfl) h_not_done


/- =========================================================================
   Axis-parallel: dx = 0 or dy = 0
   ========================================================================= -/

theorem cellIntersectionInterval_sx_zero_pos (A B : Point) (c : Cell)
    (hdx : B.x - A.x = 0) (hdy : 0 < B.y - A.y)
    (hcx : c.x = (floorPoint A).x)
    (hcy : (floorPoint A).y ≤ c.y)
    (h_bnd : ofInt (c.y + 1) - A.y < B.y - A.y) :
    let ty0 := (ofInt (c.y + 1) - A.y) / (B.y - A.y)
    let ty1 := (ofInt (c.y + 1 + 1) - A.y) / (B.y - A.y)
    let tEnter := max 0 ty0
    let tExit := min 1 ty1
    tEnter < tExit ∧ cellIntersectionInterval ⟨c.x, c.y + 1⟩ A B = some (tEnter, tExit) := by
  intro ty0 ty1 tEnter tExit
  have h_dx_eq : (B.x - A.x == 0) = true := beq_iff_eq.mpr hdx
  have h_dy_ne : (B.y - A.y == 0) = false := by
    cases h : (B.y - A.y == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_flA_x : ofInt (floorPoint A).x ≤ A.x := by
    unfold floorPoint toInt ofInt; exact Rat.floor_le A.x
  have h_flA_x_lt : A.x < ofInt ((floorPoint A).x + 1) := by
    unfold ofInt floorPoint toInt; exact Rat.lt_floor_add_one A.x
  have hcx_le : ofInt c.x ≤ A.x := by rw [hcx]; exact h_flA_x
  have hcx_lt : A.x < ofInt (c.x + 1) := by rw [hcx]; exact h_flA_x_lt
  have h_pos : 0 < ofInt (c.y + 1) - A.y := by
    have h_flAy : A.y < ofInt ((floorPoint A).y + 1) := by
      unfold ofInt floorPoint toInt; exact Rat.lt_floor_add_one A.y
    have h_int_le : (floorPoint A).y + 1 ≤ c.y + 1 := by omega
    have h_le_cy : ofInt ((floorPoint A).y + 1) ≤ ofInt (c.y + 1) := by
      unfold ofInt; exact Int.cast_le.mpr h_int_le
    linarith
  have h_ty0_pos : 0 < ty0 := div_pos h_pos hdy
  have h_enter : tEnter = ty0 := max_eq_right (le_of_lt h_ty0_pos)
  have h1 : ty0 < 1 := (div_lt_one hdy).mpr h_bnd
  have h2 : ty0 < ty1 := by
    dsimp [ty0, ty1]
    have h_lt_num : ofInt (c.y + 1) - A.y < ofInt (c.y + 1 + 1) - A.y := by
      unfold ofInt; change ((c.y + 1 : ℤ) : ℚ) - A.y < ((c.y + 1 + 1 : ℤ) : ℚ) - A.y
      push_cast; linarith
    exact div_lt_div_of_pos_right h_lt_num hdy
  have h_lt : tEnter < tExit := by
    rw [h_enter]; dsimp [tExit]; rw [lt_min_iff]; exact ⟨h1, h2⟩
  refine ⟨h_lt, ?_⟩
  unfold cellIntersectionInterval; dsimp only []
  simp only [h_dx_eq, h_dy_ne, hdy, ↓reduceIte, Bool.false_eq_true]
  have h_not_lt_cx : ¬(A.x < ofInt c.x) := by linarith
  have h_not_gt_cx1 : ¬(A.x > ofInt (c.x + 1)) := by linarith
  have h_cx_eval : (if (A.x < ofInt c.x || A.x > ofInt (c.x + 1)) then (1, 0) else (0, 1) : ℚ × ℚ) = (0, 1) := by
    simp [h_not_lt_cx, h_not_gt_cx1]
  rw [h_cx_eval]
  dsimp only []
  rw [← max_assoc, max_self, ← min_assoc, min_self]
  have h_eval_le : tEnter ≤ tExit := le_of_lt h_lt
  change (if tEnter ≤ tExit then some (tEnter, tExit) else none) = some (tEnter, tExit)
  simp only [h_eval_le, ↓reduceIte]


theorem cellIntersectionInterval_sx_zero_neg (A B : Point) (c : Cell)
    (hdx : B.x - A.x = 0) (hdy : B.y - A.y < 0)
    (hcx : c.x = (floorPoint A).x)
    (hcy : c.y ≤ (floorPoint A).y)
    (h_bnd : (ofInt c.y - A.y) / (B.y - A.y) < 1) :
    let ty0 := (ofInt c.y - A.y) / (B.y - A.y)
    let ty1 := ty0 - 1 / (B.y - A.y)
    let tEnter := max 0 ty0
    let tExit := min 1 ty1
    tEnter < tExit ∧ cellIntersectionInterval ⟨c.x, c.y - 1⟩ A B = some (tEnter, tExit) := by
  intro ty0 ty1 tEnter tExit
  have h_dx_eq : (B.x - A.x == 0) = true := beq_iff_eq.mpr hdx
  have h_dy_ne : (B.y - A.y == 0) = false := by
    cases h : (B.y - A.y == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_flA_x : ofInt (floorPoint A).x ≤ A.x := by
    unfold floorPoint toInt ofInt; exact Rat.floor_le A.x
  have h_flA_x_lt : A.x < ofInt ((floorPoint A).x + 1) := by
    unfold ofInt floorPoint toInt; exact Rat.lt_floor_add_one A.x
  have hcx_le : ofInt c.x ≤ A.x := by rw [hcx]; exact h_flA_x
  have hcx_lt : A.x < ofInt (c.x + 1) := by rw [hcx]; exact h_flA_x_lt
  have h_nonpos : ofInt c.y - A.y ≤ 0 := by
    have h_flAy : ofInt (floorPoint A).y ≤ A.y := by
      unfold floorPoint toInt ofInt; exact Rat.floor_le A.y
    have h_cy_le : ofInt c.y ≤ ofInt (floorPoint A).y := by
      unfold ofInt; exact Int.cast_le.mpr hcy
    linarith
  have h_num : ofInt c.y - A.y = -(A.y - ofInt c.y) := by ring
  have h_den : B.y - A.y = -(A.y - B.y) := by ring
  have h_ty0_eq : ty0 = (A.y - ofInt c.y) / (A.y - B.y) := by
    dsimp [ty0]; rw [h_num, h_den, neg_div_neg_eq]
  have h_ty0_pos : 0 ≤ ty0 := by
    rw [h_ty0_eq]; exact div_nonneg (by linarith) (by linarith)
  have h_enter : tEnter = ty0 := max_eq_right h_ty0_pos
  have h1 : ty0 < 1 := h_bnd
  have h2 : ty0 < ty1 := by
    dsimp [ty1]
    have : 0 < -(B.y - A.y) := by linarith
    have h := one_div_pos.mpr this
    rw [div_neg] at h
    linarith
  have h_lt : tEnter < tExit := by
    rw [h_enter]; dsimp [tExit]; rw [lt_min_iff]; exact ⟨h1, h2⟩
  refine ⟨h_lt, ?_⟩
  unfold cellIntersectionInterval; dsimp only []
  have h_not_dy_pos : ¬(B.y - A.y > 0) := by linarith
  simp only [h_dx_eq, h_dy_ne, h_not_dy_pos, ↓reduceIte, Bool.false_eq_true]
  have h_not_lt_cx : ¬(A.x < ofInt c.x) := by linarith
  have h_not_gt_cx1 : ¬(A.x > ofInt (c.x + 1)) := by linarith
  have h_cx_eval : (if (A.x < ofInt c.x || A.x > ofInt (c.x + 1)) then (1, 0) else (0, 1) : ℚ × ℚ) = (0, 1) := by
    simp [h_not_lt_cx, h_not_gt_cx1]
  rw [h_cx_eval]
  have h_cy1 : ofInt (c.y - 1 + 1) = ofInt c.y := by
    unfold ofInt; congr 1; omega
  have h_cy0 : ofInt (c.y - 1) = ofInt c.y - 1 := by
    unfold ofInt; change ((c.y - 1 : ℤ) : ℚ) = ((c.y : ℤ) : ℚ) - 1; push_cast; ring
  rw [h_cy1, h_cy0]
  have h_divy : (ofInt c.y - 1 - A.y) / (B.y - A.y) = ty1 := by
    dsimp [ty1, ty0]; ring
  rw [h_divy]
  dsimp only []
  rw [← max_assoc, max_self, ← min_assoc, min_self]
  have h_eval_le : tEnter ≤ tExit := le_of_lt h_lt
  change (if tEnter ≤ tExit then some (tEnter, tExit) else none) = some (tEnter, tExit)
  simp only [h_eval_le, ↓reduceIte]


theorem cellIntersectionInterval_sy_zero_pos (A B : Point) (c : Cell)
    (hdx : 0 < B.x - A.x) (hdy : B.y - A.y = 0)
    (hcy : c.y = (floorPoint A).y)
    (hcx : (floorPoint A).x ≤ c.x)
    (h_bnd : ofInt (c.x + 1) - A.x < B.x - A.x) :
    let tx0 := (ofInt (c.x + 1) - A.x) / (B.x - A.x)
    let tx1 := (ofInt (c.x + 1 + 1) - A.x) / (B.x - A.x)
    let tEnter := max 0 tx0
    let tExit := min 1 tx1
    tEnter < tExit ∧ cellIntersectionInterval ⟨c.x + 1, c.y⟩ A B = some (tEnter, tExit) := by
  intro tx0 tx1 tEnter tExit
  have h_dy_eq : (B.y - A.y == 0) = true := beq_iff_eq.mpr hdy
  have h_dx_ne : (B.x - A.x == 0) = false := by
    cases h : (B.x - A.x == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_flA_y : ofInt (floorPoint A).y ≤ A.y := by
    unfold floorPoint toInt ofInt; exact Rat.floor_le A.y
  have h_flA_y_lt : A.y < ofInt ((floorPoint A).y + 1) := by
    unfold ofInt floorPoint toInt; exact Rat.lt_floor_add_one A.y
  have hcy_le : ofInt c.y ≤ A.y := by rw [hcy]; exact h_flA_y
  have hcy_lt : A.y < ofInt (c.y + 1) := by rw [hcy]; exact h_flA_y_lt
  have h_pos : 0 < ofInt (c.x + 1) - A.x := by
    have h_flAx : A.x < ofInt ((floorPoint A).x + 1) := by
      unfold ofInt floorPoint toInt; exact Rat.lt_floor_add_one A.x
    have h_int_le : (floorPoint A).x + 1 ≤ c.x + 1 := by omega
    have h_le_cx : ofInt ((floorPoint A).x + 1) ≤ ofInt (c.x + 1) := by
      unfold ofInt; exact Int.cast_le.mpr h_int_le
    linarith
  have h_tx0_pos : 0 < tx0 := div_pos h_pos hdx
  have h_enter : tEnter = tx0 := max_eq_right (le_of_lt h_tx0_pos)
  have h1 : tx0 < 1 := (div_lt_one hdx).mpr h_bnd
  have h2 : tx0 < tx1 := by
    dsimp [tx0, tx1]
    have h_lt_num : ofInt (c.x + 1) - A.x < ofInt (c.x + 1 + 1) - A.x := by
      unfold ofInt; change ((c.x + 1 : ℤ) : ℚ) - A.x < ((c.x + 1 + 1 : ℤ) : ℚ) - A.x
      push_cast; linarith
    exact div_lt_div_of_pos_right h_lt_num hdx
  have h_lt : tEnter < tExit := by
    rw [h_enter]; dsimp [tExit]; rw [lt_min_iff]; exact ⟨h1, h2⟩
  refine ⟨h_lt, ?_⟩
  unfold cellIntersectionInterval; dsimp only []
  simp only [h_dy_eq, h_dx_ne, hdx, ↓reduceIte, Bool.false_eq_true]
  have h_not_lt_cy : ¬(A.y < ofInt c.y) := by linarith
  have h_not_gt_cy1 : ¬(A.y > ofInt (c.y + 1)) := by linarith
  have h_cy_eval : (if (A.y < ofInt c.y || A.y > ofInt (c.y + 1)) then (1, 0) else (0, 1) : ℚ × ℚ) = (0, 1) := by
    simp [h_not_lt_cy, h_not_gt_cy1]
  rw [h_cy_eval]
  dsimp only []
  rw [max_comm tx0 0, ← max_assoc, max_self]
  rw [min_comm tx1 1, ← min_assoc, min_self]
  have h_eval_le : tEnter ≤ tExit := le_of_lt h_lt
  change (if tEnter ≤ tExit then some (tEnter, tExit) else none) = some (tEnter, tExit)
  simp only [h_eval_le, ↓reduceIte]


theorem cellIntersectionInterval_sy_zero_neg (A B : Point) (c : Cell)
    (hdx : B.x - A.x < 0) (hdy : B.y - A.y = 0)
    (hcy : c.y = (floorPoint A).y)
    (hcx : c.x ≤ (floorPoint A).x)
    (h_bnd : (ofInt c.x - A.x) / (B.x - A.x) < 1) :
    let tx0 := (ofInt c.x - A.x) / (B.x - A.x)
    let tx1 := tx0 - 1 / (B.x - A.x)
    let tEnter := max 0 tx0
    let tExit := min 1 tx1
    tEnter < tExit ∧ cellIntersectionInterval ⟨c.x - 1, c.y⟩ A B = some (tEnter, tExit) := by
  intro tx0 tx1 tEnter tExit
  have h_dy_eq : (B.y - A.y == 0) = true := beq_iff_eq.mpr hdy
  have h_dx_ne : (B.x - A.x == 0) = false := by
    cases h : (B.x - A.x == 0)
    · rfl
    · exfalso; have := eq_of_beq h; linarith
  have h_flA_y : ofInt (floorPoint A).y ≤ A.y := by
    unfold floorPoint toInt ofInt; exact Rat.floor_le A.y
  have h_flA_y_lt : A.y < ofInt ((floorPoint A).y + 1) := by
    unfold ofInt floorPoint toInt; exact Rat.lt_floor_add_one A.y
  have hcy_le : ofInt c.y ≤ A.y := by rw [hcy]; exact h_flA_y
  have hcy_lt : A.y < ofInt (c.y + 1) := by rw [hcy]; exact h_flA_y_lt
  have h_nonpos : ofInt c.x - A.x ≤ 0 := by
    have h_flAx : ofInt (floorPoint A).x ≤ A.x := by
      unfold floorPoint toInt ofInt; exact Rat.floor_le A.x
    have h_cx_le : ofInt c.x ≤ ofInt (floorPoint A).x := by
      unfold ofInt; exact Int.cast_le.mpr hcx
    linarith
  have h_num : ofInt c.x - A.x = -(A.x - ofInt c.x) := by ring
  have h_den : B.x - A.x = -(A.x - B.x) := by ring
  have h_tx0_eq : tx0 = (A.x - ofInt c.x) / (A.x - B.x) := by
    dsimp [tx0]; rw [h_num, h_den, neg_div_neg_eq]
  have h_tx0_pos : 0 ≤ tx0 := by
    rw [h_tx0_eq]; exact div_nonneg (by linarith) (by linarith)
  have h_enter : tEnter = tx0 := max_eq_right h_tx0_pos
  have h1 : tx0 < 1 := h_bnd
  have h2 : tx0 < tx1 := by
    dsimp [tx1]
    have : 0 < -(B.x - A.x) := by linarith
    have h := one_div_pos.mpr this
    rw [div_neg] at h
    linarith
  have h_lt : tEnter < tExit := by
    rw [h_enter]; dsimp [tExit]; rw [lt_min_iff]; exact ⟨h1, h2⟩
  refine ⟨h_lt, ?_⟩
  unfold cellIntersectionInterval; dsimp only []
  have h_not_dx_pos : ¬(B.x - A.x > 0) := by linarith
  simp only [h_dy_eq, h_dx_ne, h_not_dx_pos, ↓reduceIte, Bool.false_eq_true]
  have h_not_lt_cy : ¬(A.y < ofInt c.y) := by linarith
  have h_not_gt_cy1 : ¬(A.y > ofInt (c.y + 1)) := by linarith
  have h_cy_eval : (if (A.y < ofInt c.y || A.y > ofInt (c.y + 1)) then (1, 0) else (0, 1) : ℚ × ℚ) = (0, 1) := by
    simp [h_not_lt_cy, h_not_gt_cy1]
  rw [h_cy_eval]
  have h_cx1 : ofInt (c.x - 1 + 1) = ofInt c.x := by
    unfold ofInt; congr 1; omega
  have h_cx0 : ofInt (c.x - 1) = ofInt c.x - 1 := by
    unfold ofInt; change ((c.x - 1 : ℤ) : ℚ) = ((c.x : ℤ) : ℚ) - 1; push_cast; ring
  rw [h_cx1, h_cx0]
  have h_divx : (ofInt c.x - 1 - A.x) / (B.x - A.x) = tx1 := by
    dsimp [tx1, tx0]; ring
  rw [h_divx]
  dsimp only []
  rw [max_comm tx0 0, ← max_assoc, max_self]
  rw [min_comm tx1 1, ← min_assoc, min_self]
  have h_eval_le : tEnter ≤ tExit := le_of_lt h_lt
  change (if tEnter ≤ tExit then some (tEnter, tExit) else none) = some (tEnter, tExit)
  simp only [h_eval_le, ↓reduceIte]


theorem rayMarchStep_sx_zero_step (A B : Point) (c : Cell)
    (dy : ℚ) (stepY : ℤ)
    (h_not_done : (rayMarchStep A B 0 dy 0 stepY c).2 = false) :
    let yb : ℚ := if stepY > 0 then ofInt (c.y + 1) else ofInt c.y
    let absDy := if dy >= 0 then dy else -dy
    let remY := if yb >= A.y then yb - A.y else A.y - yb
    (rayMarchStep A B 0 dy 0 stepY c) = (⟨c.x, c.y + stepY⟩, false) ∧ remY < absDy := by
  intro yb absDy remY
  have h_step := rayMarchStep_sx_zero A B c dy stepY
  dsimp only [] at h_step
  rw [h_step] at h_not_done ⊢
  by_cases h : (if (if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
        (if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
      else A.y - if stepY > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ if dy ≥ 0 then dy else -dy
  · simp only [h, ↓reduceIte] at h_not_done
    contradiction
  · simp only [h, ↓reduceIte]
    exact ⟨trivial, not_le.mp h⟩


theorem rayMarchStep_sy_zero_step (A B : Point) (c : Cell)
    (dx : ℚ) (stepX : ℤ)
    (hsx_ne : (stepX == 0) = false)
    (h_not_done : (rayMarchStep A B dx 0 stepX 0 c).2 = false) :
    let xb : ℚ := if stepX > 0 then ofInt (c.x + 1) else ofInt c.x
    let absDx := if dx >= 0 then dx else -dx
    let remX := if xb >= A.x then xb - A.x else A.x - xb
    (rayMarchStep A B dx 0 stepX 0 c) = (⟨c.x + stepX, c.y⟩, false) ∧ remX < absDx := by
  intro xb absDx remX
  have h_step := rayMarchStep_sy_zero A B c dx stepX hsx_ne
  dsimp only [] at h_step
  rw [h_step] at h_not_done ⊢
  by_cases h : (if (if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
        (if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
      else A.x - if stepX > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ if dx >= 0 then dx else -dx
  · simp only [h, ↓reduceIte] at h_not_done
    contradiction
  · simp only [h, ↓reduceIte]
    exact ⟨trivial, not_le.mp h⟩


theorem rayMarchStep_sound_step_sx_zero (A B : Point) (stepY : ℤ) (c : Cell)
    (hdx : B.x - A.x = 0)
    (hstepY : stepY = if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0)
    (hc_bbox : inBoundingBox c A B = true)
    (hc_x : c.x = (floorPoint A).x)
    (hc_y : (0 < B.y - A.y ∧ (floorPoint A).y ≤ c.y) ∨ (B.y - A.y < 0 ∧ c.y ≤ (floorPoint A).y))
    (h_not_done : (rayMarchStep A B 0 (B.y - A.y) 0 stepY c).2 = false) :
    let next := (rayMarchStep A B 0 (B.y - A.y) 0 stepY c).1
    inBoundingBox next A B = true ∧
    next.x = (floorPoint A).x ∧
    ((0 < B.y - A.y ∧ (floorPoint A).y ≤ next.y) ∨ (B.y - A.y < 0 ∧ next.y ≤ (floorPoint A).y)) ∧
    ∃ tEnter tExit, cellIntersectionInterval next A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  intro next
  have h_step := rayMarchStep_sx_zero_step A B c (B.y - A.y) stepY h_not_done
  rcases h_step with ⟨h_step_eq, h_rem⟩
  dsimp [next]
  rw [h_step_eq]
  rcases hc_y with ⟨hdy_pos, hcy_le⟩ | ⟨hdy_neg, hcy_ge⟩
  · have hsy : stepY = 1 := by rw [hstepY]; simp [hdy_pos]
    rw [hsy] at h_step_eq h_rem ⊢
    have h_yb : (if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) = ofInt (c.y + 1) := by rfl
    have h_abs : (if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)) = B.y - A.y := by
      simp [show B.y - A.y ≥ 0 by linarith]
    rw [h_yb, h_abs] at h_rem
    have h_yb_ge : ofInt (c.y + 1) ≥ A.y := by
      have h_flAy : A.y < ofInt ((floorPoint A).y + 1) := by
        unfold ofInt floorPoint toInt; exact Rat.lt_floor_add_one A.y
      have h_int_le : (floorPoint A).y + 1 ≤ c.y + 1 := by omega
      have h_le_cy : ofInt ((floorPoint A).y + 1) ≤ ofInt (c.y + 1) := by
        unfold ofInt; exact Int.cast_le.mpr h_int_le
      linarith
    have h_case : (if ofInt (c.y + 1) ≥ A.y then ofInt (c.y + 1) - A.y else A.y - ofInt (c.y + 1)) = ofInt (c.y + 1) - A.y := by
      simp [h_yb_ge]
    rw [h_case] at h_rem
    have h_bnd_y : c.y + 1 ≤ (floorPoint B).y := stepY_pos_next_le_end (c.y + 1) A.y B hdy_pos h_rem
    have h_bbox_next : inBoundingBox ⟨c.x, c.y + 1⟩ A B = true :=
      inBoundingBox_stepY_forward c A B hdy_pos hc_bbox h_bnd_y
    have h_inter := cellIntersectionInterval_sx_zero_pos A B c hdx hdy_pos hc_x hcy_le h_rem
    dsimp only []
    refine ⟨h_bbox_next, hc_x, Or.inl ⟨hdy_pos, by omega⟩, ?_⟩
    exact ⟨_, _, h_inter.2, h_inter.1⟩
  · have hsy : stepY = -1 := by
      rw [hstepY]
      simp [show ¬(B.y - A.y > 0) by linarith, hdy_neg]
    rw [hsy] at h_step_eq h_rem ⊢
    have h_yb : (if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) = ofInt c.y := by rfl
    have h_abs : (if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)) = -(B.y - A.y) := by
      simp [show ¬(B.y - A.y ≥ 0) by linarith]
    rw [h_yb, h_abs] at h_rem
    have h_yb_le : ofInt c.y ≤ A.y := by
      have h_flAy : ofInt (floorPoint A).y ≤ A.y := by
        unfold floorPoint toInt ofInt; exact Rat.floor_le A.y
      have h_cy_le : ofInt c.y ≤ ofInt (floorPoint A).y := by
        unfold ofInt; exact Int.cast_le.mpr hcy_ge
      linarith
    have h_case : (if ofInt c.y ≥ A.y then ofInt c.y - A.y else A.y - ofInt c.y) = A.y - ofInt c.y := by
      by_cases h_eq : ofInt c.y ≥ A.y
      · have : ofInt c.y = A.y := le_antisymm h_yb_le h_eq
        simp [this]
      · simp [h_eq]
    rw [h_case] at h_rem
    have h_div_lt : (ofInt c.y - A.y) / (B.y - A.y) < 1 := by
      have h_eq : (ofInt c.y - A.y) / (B.y - A.y) = (A.y - ofInt c.y) / (A.y - B.y) := by
        have h1 : ofInt c.y - A.y = -(A.y - ofInt c.y) := by ring
        have h2 : B.y - A.y = -(A.y - B.y) := by ring
        rw [h1, h2, neg_div_neg_eq]
      rw [h_eq]
      have h_pos_den : 0 < A.y - B.y := by linarith
      have h_rem' : A.y - ofInt c.y < A.y - B.y := by linarith
      exact (div_lt_one h_pos_den).mpr h_rem'
    have h_bnd_y : (floorPoint B).y ≤ c.y - 1 := stepY_neg_next_ge_end c.y A.y B hdy_neg h_div_lt
    have h_bbox_next : inBoundingBox ⟨c.x, c.y - 1⟩ A B = true :=
      inBoundingBox_stepY_backward c A B hdy_neg hc_bbox h_bnd_y
    have h_inter := cellIntersectionInterval_sx_zero_neg A B c hdx hdy_neg hc_x hcy_ge h_div_lt
    dsimp only []
    refine ⟨h_bbox_next, hc_x, Or.inr ⟨hdy_neg, by omega⟩, ?_⟩
    exact ⟨_, _, h_inter.2, h_inter.1⟩


theorem rayMarchStep_sound_step_sy_zero (A B : Point) (stepX : ℤ) (c : Cell)
    (hdy : B.y - A.y = 0)
    (hsx_ne : (stepX == 0) = false)
    (hstepX : stepX = if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0)
    (hc_bbox : inBoundingBox c A B = true)
    (hc_y : c.y = (floorPoint A).y)
    (hc_x : (0 < B.x - A.x ∧ (floorPoint A).x ≤ c.x) ∨ (B.x - A.x < 0 ∧ c.x ≤ (floorPoint A).x))
    (h_not_done : (rayMarchStep A B (B.x - A.x) 0 stepX 0 c).2 = false) :
    let next := (rayMarchStep A B (B.x - A.x) 0 stepX 0 c).1
    inBoundingBox next A B = true ∧
    next.y = (floorPoint A).y ∧
    ((0 < B.x - A.x ∧ (floorPoint A).x ≤ next.x) ∨ (B.x - A.x < 0 ∧ next.x ≤ (floorPoint A).x)) ∧
    ∃ tEnter tExit, cellIntersectionInterval next A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  intro next
  have h_step := rayMarchStep_sy_zero_step A B c (B.x - A.x) stepX hsx_ne h_not_done
  rcases h_step with ⟨h_step_eq, h_rem⟩
  dsimp [next]
  rw [h_step_eq]
  rcases hc_x with ⟨hdx_pos, hcx_le⟩ | ⟨hdx_neg, hcx_ge⟩
  · have hsx : stepX = 1 := by rw [hstepX]; simp [hdx_pos]
    rw [hsx] at h_step_eq h_rem ⊢
    have h_xb : (if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) = ofInt (c.x + 1) := by rfl
    have h_abs : (if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) = B.x - A.x := by
      simp [show B.x - A.x ≥ 0 by linarith]
    rw [h_xb, h_abs] at h_rem
    have h_xb_ge : ofInt (c.x + 1) ≥ A.x := by
      have h_flAx : A.x < ofInt ((floorPoint A).x + 1) := by
        unfold ofInt floorPoint toInt; exact Rat.lt_floor_add_one A.x
      have h_int_le : (floorPoint A).x + 1 ≤ c.x + 1 := by omega
      have h_le_cx : ofInt ((floorPoint A).x + 1) ≤ ofInt (c.x + 1) := by
        unfold ofInt; exact Int.cast_le.mpr h_int_le
      linarith
    have h_case : (if ofInt (c.x + 1) ≥ A.x then ofInt (c.x + 1) - A.x else A.x - ofInt (c.x + 1)) = ofInt (c.x + 1) - A.x := by
      simp [h_xb_ge]
    rw [h_case] at h_rem
    have h_bnd_x : c.x + 1 ≤ (floorPoint B).x := stepX_pos_next_le_end (c.x + 1) A.x B hdx_pos h_rem
    have h_bbox_next : inBoundingBox ⟨c.x + 1, c.y⟩ A B = true :=
      inBoundingBox_stepX_forward c A B hdx_pos hc_bbox h_bnd_x
    have h_inter := cellIntersectionInterval_sy_zero_pos A B c hdx_pos hdy hc_y hcx_le h_rem
    dsimp only []
    refine ⟨h_bbox_next, hc_y, Or.inl ⟨hdx_pos, by omega⟩, ?_⟩
    exact ⟨_, _, h_inter.2, h_inter.1⟩
  · have hsx : stepX = -1 := by
      rw [hstepX]
      simp [show ¬(B.x - A.x > 0) by linarith, hdx_neg]
    rw [hsx] at h_step_eq h_rem ⊢
    have h_xb : (if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) = ofInt c.x := by rfl
    have h_abs : (if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) = -(B.x - A.x) := by
      simp [show ¬(B.x - A.x ≥ 0) by linarith]
    rw [h_xb, h_abs] at h_rem
    have h_xb_le : ofInt c.x ≤ A.x := by
      have h_flAx : ofInt (floorPoint A).x ≤ A.x := by
        unfold floorPoint toInt ofInt; exact Rat.floor_le A.x
      have h_cx_le : ofInt c.x ≤ ofInt (floorPoint A).x := by
        unfold ofInt; exact Int.cast_le.mpr hcx_ge
      linarith
    have h_case : (if ofInt c.x ≥ A.x then ofInt c.x - A.x else A.x - ofInt c.x) = A.x - ofInt c.x := by
      by_cases h_eq : ofInt c.x ≥ A.x
      · have : ofInt c.x = A.x := le_antisymm h_xb_le h_eq
        simp [this]
      · simp [h_eq]
    rw [h_case] at h_rem
    have h_div_lt : (ofInt c.x - A.x) / (B.x - A.x) < 1 := by
      have h_eq : (ofInt c.x - A.x) / (B.x - A.x) = (A.x - ofInt c.x) / (A.x - B.x) := by
        have h1 : ofInt c.x - A.x = -(A.x - ofInt c.x) := by ring
        have h2 : B.x - A.x = -(A.x - B.x) := by ring
        rw [h1, h2, neg_div_neg_eq]
      rw [h_eq]
      have h_pos_den : 0 < A.x - B.x := by linarith
      have h_rem' : A.x - ofInt c.x < A.x - B.x := by linarith
      exact (div_lt_one h_pos_den).mpr h_rem'
    have h_bnd_x : (floorPoint B).x ≤ c.x - 1 := stepX_neg_next_ge_end c.x A.x B hdx_neg h_div_lt
    have h_bbox_next : inBoundingBox ⟨c.x - 1, c.y⟩ A B = true :=
      inBoundingBox_stepX_backward c A B hdx_neg hc_bbox h_bnd_x
    have h_inter := cellIntersectionInterval_sy_zero_neg A B c hdx_neg hdy hc_y hcx_ge h_div_lt
    dsimp only []
    refine ⟨h_bbox_next, hc_y, Or.inr ⟨hdx_neg, by omega⟩, ?_⟩
    exact ⟨_, _, h_inter.2, h_inter.1⟩


theorem rayMarch_soundness_sx_zero (A B : Point) (x : Cell)
    (hdx : B.x - A.x = 0)
    (hA_eq_B : ¬(floorPoint A = floorPoint B))
    (hx : x ∈ rayMarch (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 2)
      A B (B.x - A.x) (B.y - A.y)
      (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0)
      (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0)
      (floorPoint B) (floorPoint A) []) :
    inBoundingBox x A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval x A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  have hsx : (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else (0 : ℤ)) = 0 := by simp [hdx]
  have hdy_ne : ¬(B.y - A.y = 0) := by
    intro h_dy0
    have : A = B := by
      rcases A with ⟨Ax, Ay⟩
      rcases B with ⟨Bx, By⟩
      dsimp at hdx h_dy0
      have : Ax = Bx := by linarith
      have : Ay = By := by linarith
      congr
    rw [this] at hA_eq_B
    exact hA_eq_B rfl
  let stepY : ℤ := if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0
  rw [hsx, hdx] at hx
  have h_fuel : (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 2) =
    (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 1) + 1 := by omega
  rw [h_fuel] at hx
  let P : Cell → Prop := fun cell =>
    inBoundingBox cell A B = true ∧
    cell.x = (floorPoint A).x ∧
    ((0 < B.y - A.y ∧ (floorPoint A).y ≤ cell.y) ∨ (B.y - A.y < 0 ∧ cell.y ≤ (floorPoint A).y)) ∧
    ∃ tEnter tExit, cellIntersectionInterval cell A B = some (tEnter, tExit) ∧ tEnter < tExit
  have h_sound := sound_from_first_step _ _ _ 0 (B.y - A.y) 0 stepY (floorPoint B) P
    (by
      intro c hc h_not_done
      exact rayMarchStep_sound_step_sx_zero A B stepY c hdx rfl hc.1 hc.2.1 hc.2.2.1 h_not_done)
    (by
      intro h_not_done
      have hc_bbox : inBoundingBox (floorPoint A) A B = true := inBoundingBox_startCell A B
      have hc_x : (floorPoint A).x = (floorPoint A).x := rfl
      have hc_y : (0 < B.y - A.y ∧ (floorPoint A).y ≤ (floorPoint A).y) ∨ (B.y - A.y < 0 ∧ (floorPoint A).y ≤ (floorPoint A).y) := by
        by_cases hdy_pos : 0 < B.y - A.y
        · exact Or.inl ⟨hdy_pos, le_rfl⟩
        · have hdy_neg : B.y - A.y < 0 := lt_of_le_of_ne (not_lt.mp hdy_pos) hdy_ne
          exact Or.inr ⟨hdy_neg, le_rfl⟩
      exact rayMarchStep_sound_step_sx_zero A B stepY (floorPoint A) hdx rfl hc_bbox hc_x hc_y h_not_done)
    x hx
  exact ⟨h_sound.1, h_sound.2.2.2⟩


theorem rayMarch_soundness_sy_zero (A B : Point) (x : Cell)
    (hdy : B.y - A.y = 0)
    (hA_eq_B : ¬(floorPoint A = floorPoint B))
    (hx : x ∈ rayMarch (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 2)
      A B (B.x - A.x) (B.y - A.y)
      (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0)
      (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0)
      (floorPoint B) (floorPoint A) []) :
    inBoundingBox x A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval x A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  have hsy : (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else (0 : ℤ)) = 0 := by simp [hdy]
  have hdx_ne : ¬(B.x - A.x = 0) := by
    intro h_dx0
    have : A = B := by
      rcases A with ⟨Ax, Ay⟩
      rcases B with ⟨Bx, By⟩
      dsimp at hdy h_dx0
      have : Ax = Bx := by linarith
      have : Ay = By := by linarith
      congr
    rw [this] at hA_eq_B
    exact hA_eq_B rfl
  let stepX : ℤ := if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0
  have hsx_ne : (stepX == 0) = false := by
    cases h : (stepX == 0)
    · rfl
    · exfalso
      have := eq_of_beq h
      dsimp [stepX] at this
      by_cases h1 : B.x - A.x > 0
      · simp [h1] at this
      · by_cases h2 : B.x - A.x < 0
        · simp [h1, h2] at this
        · simp [h1, h2] at this
          exact hdx_ne (by linarith)
  rw [hsy, hdy] at hx
  have h_fuel : (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 2) =
    (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 1) + 1 := by omega
  rw [h_fuel] at hx
  let P : Cell → Prop := fun cell =>
    inBoundingBox cell A B = true ∧
    cell.y = (floorPoint A).y ∧
    ((0 < B.x - A.x ∧ (floorPoint A).x ≤ cell.x) ∨ (B.x - A.x < 0 ∧ cell.x ≤ (floorPoint A).x)) ∧
    ∃ tEnter tExit, cellIntersectionInterval cell A B = some (tEnter, tExit) ∧ tEnter < tExit
  have h_sound := sound_from_first_step _ _ _ (B.x - A.x) 0 stepX 0 (floorPoint B) P
    (by
      intro c hc h_not_done
      exact rayMarchStep_sound_step_sy_zero A B stepX c hdy hsx_ne rfl hc.1 hc.2.1 hc.2.2.1 h_not_done)
    (by
      intro h_not_done
      have hc_bbox : inBoundingBox (floorPoint A) A B = true := inBoundingBox_startCell A B
      have hc_y : (floorPoint A).y = (floorPoint A).y := rfl
      have hc_x : (0 < B.x - A.x ∧ (floorPoint A).x ≤ (floorPoint A).x) ∨ (B.x - A.x < 0 ∧ (floorPoint A).x ≤ (floorPoint A).x) := by
        by_cases hdx_pos : 0 < B.x - A.x
        · exact Or.inl ⟨hdx_pos, le_rfl⟩
        · have hdx_neg : B.x - A.x < 0 := lt_of_le_of_ne (not_lt.mp hdx_pos) hdx_ne
          exact Or.inr ⟨hdx_neg, le_rfl⟩
      exact rayMarchStep_sound_step_sy_zero A B stepX (floorPoint A) hdy hsx_ne rfl hc_bbox hc_y hc_x h_not_done)
    x hx
  exact ⟨h_sound.1, h_sound.2.2.2⟩


/- =========================================================================
   Top-level Soundness Theorem
   ========================================================================= -/

theorem rayMarch_soundness (A B : Point) (x : Cell)
    (hx : x ∈ rayMarch (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 2)
      A B (B.x - A.x) (B.y - A.y)
      (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0)
      (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0)
      (floorPoint B) (floorPoint A) []) :
    inBoundingBox x A B = true ∧
    ∃ tEnter tExit, cellIntersectionInterval x A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  by_cases hA_eq_B : floorPoint A = floorPoint B
  · have := rayMarch_same_endpoints
      (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 1)
      A B (B.x - A.x) (B.y - A.y)
      (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0)
      (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0)
      hA_eq_B
    have h_fuel : (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 2) =
      (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 1) + 1 := by omega
    rw [h_fuel, this] at hx
    contradiction
  · by_cases hdx0 : B.x - A.x = 0
    · exact rayMarch_soundness_sx_zero A B x hdx0 hA_eq_B hx
    · by_cases hdy0 : B.y - A.y = 0
      · exact rayMarch_soundness_sy_zero A B x hdy0 hA_eq_B hx
      · by_cases hdx : 0 < B.x - A.x
        · by_cases hdy : 0 < B.y - A.y
          · exact rayMarch_soundness_pos_pos A B x hdx hdy hx
          · have hdy_neg : B.y - A.y < 0 := lt_of_le_of_ne (not_lt.mp hdy) hdy0
            exact rayMarch_soundness_pos_neg A B x hdx hdy_neg hx
        · have hdx_neg : B.x - A.x < 0 := lt_of_le_of_ne (not_lt.mp hdx) hdx0
          by_cases hdy : 0 < B.y - A.y
          · exact rayMarch_soundness_neg_pos A B x hdx_neg hdy hx
          · have hdy_neg : B.y - A.y < 0 := lt_of_le_of_ne (not_lt.mp hdy) hdy0
            exact rayMarch_soundness_neg_neg A B x hdx_neg hdy_neg hx



end Geometry
