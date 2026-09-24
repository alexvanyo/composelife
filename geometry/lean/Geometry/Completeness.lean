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

def targetDist (sx sy : ℤ) (x c A : Cell) : ℕ :=
  let dx := (x.x - c.x) * sx
  let dy := (x.y - c.y) * sy
  if 0 ≤ (c.x - A.x) * sx ∧ 0 ≤ (c.y - A.y) * sy ∧
     0 ≤ dx ∧ 0 ≤ dy ∧
     (c.x = A.x ∨ sx ≠ 0) ∧ (c.y = A.y ∨ sy ≠ 0) ∧
     c ≠ x then
    (dx + dy).toNat
  else
    0

theorem eq_of_mul_sign_zero (x_val a_val : ℤ) (dx : ℚ)
    (e : (x_val - a_val) * (if dx > 0 then 1 else if dx < 0 then -1 else (0 : ℤ)) = 0)
    (h_zero : dx = 0 → x_val = a_val) :
    x_val = a_val := by
  split_ifs at e with h1 h2
  · linarith
  · linarith
  · exact h_zero (by linarith)

theorem targetDist_start_pos (A B : Point) (x : Cell)
    (h_bbox : inBoundingBox x A B = true)
    (hxA : x ≠ floorPoint A) :
    let sx : ℤ := if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0
    let sy : ℤ := if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0
    0 < targetDist sx sy x (floorPoint A) (floorPoint A) := by
  intro sx sy
  unfold targetDist
  dsimp only []
  have h_signs := bbox_signs x A B h_bbox
  have h_ne : floorPoint A ≠ x := hxA.symm
  have h_sum_pos : 0 < (x.x - (floorPoint A).x) * sx + (x.y - (floorPoint A).y) * sy := by
    by_contra! h_le
    have h1 := h_signs.1
    have h2 := h_signs.2.2.1
    have e1 : (x.x - (floorPoint A).x) * sx = 0 := by linarith
    have e2 : (x.y - (floorPoint A).y) * sy = 0 := by linarith
    have hx_eq : x.x = (floorPoint A).x :=
      eq_of_mul_sign_zero x.x (floorPoint A).x (B.x - A.x) e1 (fun h => (bbox_sx_zero x A B h_bbox (by simp [h])).1)
    have hy_eq : x.y = (floorPoint A).y :=
      eq_of_mul_sign_zero x.y (floorPoint A).y (B.y - A.y) e2 (fun h => (bbox_sy_zero x A B h_bbox (by simp [h])).1)
    have : x = floorPoint A := by
      cases x
      dsimp at hx_eq hy_eq
      rw [hx_eq, hy_eq]
    contradiction
  have h_all : 0 ≤ ((floorPoint A).x - (floorPoint A).x) * sx ∧
    0 ≤ ((floorPoint A).y - (floorPoint A).y) * sy ∧
    0 ≤ (x.x - (floorPoint A).x) * sx ∧
    0 ≤ (x.y - (floorPoint A).y) * sy ∧
    ((floorPoint A).x = (floorPoint A).x ∨ sx ≠ 0) ∧
    ((floorPoint A).y = (floorPoint A).y ∨ sy ≠ 0) ∧
    floorPoint A ≠ x := ⟨by simp, by simp, h_signs.1, h_signs.2.2.1, Or.inl rfl, Or.inl rfl, h_ne⟩
  split_ifs
  omega

theorem mul_sign_le_natAbs (z : ℤ) (s : ℤ) (hs : s = 1 ∨ s = -1 ∨ s = 0) :
    z * s ≤ (z.natAbs : ℤ) := by
  rcases hs with rfl | rfl | rfl
  · simp
    exact le_max_left z (-z)
  · simp
    exact le_max_right z (-z)
  · simp

theorem sign_cases (v : ℚ) :
    (if v > 0 then 1 else if v < 0 then -1 else (0 : ℤ)) = 1 ∨
    (if v > 0 then 1 else if v < 0 then -1 else (0 : ℤ)) = -1 ∨
    (if v > 0 then 1 else if v < 0 then -1 else (0 : ℤ)) = 0 := by
  split_ifs <;> simp

theorem targetDist_start_le (A B : Point) (x : Cell)
    (h_bbox : inBoundingBox x A B = true) :
    let sx : ℤ := if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0
    let sy : ℤ := if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0
    let fuel := (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 2)
    targetDist sx sy x (floorPoint A) (floorPoint A) ≤ fuel := by
  intro sx sy fuel
  unfold targetDist
  dsimp only []
  have h_signs := bbox_signs x A B h_bbox
  have h_le_x : (x.x - (floorPoint A).x) * sx ≤ ((floorPoint B).x - (floorPoint A).x) * sx := by
    have h1 := h_signs.2.1
    have : ((floorPoint B).x - (floorPoint A).x) * sx =
      (x.x - (floorPoint A).x) * sx + ((floorPoint B).x - x.x) * sx := by ring
    linarith
  have h_le_y : (x.y - (floorPoint A).y) * sy ≤ ((floorPoint B).y - (floorPoint A).y) * sy := by
    have h2 := h_signs.2.2.2
    have : ((floorPoint B).y - (floorPoint A).y) * sy =
      (x.y - (floorPoint A).y) * sy + ((floorPoint B).y - x.y) * sy := by ring
    linarith
  have hsx : sx = 1 ∨ sx = -1 ∨ sx = 0 := sign_cases (B.x - A.x)
  have hsy : sy = 1 ∨ sy = -1 ∨ sy = 0 := sign_cases (B.y - A.y)
  have h_abs_x := mul_sign_le_natAbs ((floorPoint B).x - (floorPoint A).x) sx hsx
  have h_abs_y := mul_sign_le_natAbs ((floorPoint B).y - (floorPoint A).y) sy hsy
  have h_sum : (x.x - (floorPoint A).x) * sx + (x.y - (floorPoint A).y) * sy ≤
    (((floorPoint B).x - (floorPoint A).x).natAbs : ℤ) + (((floorPoint B).y - (floorPoint A).y).natAbs : ℤ) := by
    linarith
  have h_fuel : (x.x - (floorPoint A).x) * sx + (x.y - (floorPoint A).y) * sy ≤ (fuel : ℤ) := by
    dsimp [fuel]
    omega
  split_ifs <;> omega



theorem targetDist_step_sx_zero (A B : Point) (x c : Cell) (tEnter tExit : ℚ)
    (h_bbox : inBoundingBox x A B = true) (hxA : x ≠ floorPoint A)
    (h_int : cellIntersectionInterval x A B = some (tEnter, tExit))
    (h_enter_lt_exit : tEnter < tExit)
    (hsx : (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else (0 : ℤ)) = 0)
    (h_cA_y : 0 ≤ (c.y - (floorPoint A).y) * if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0)
    (h_cy : 0 ≤ (x.y - c.y) * if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0)
    (hc_x : c.x = (floorPoint A).x)
    (h_ne : c ≠ x) :
    let sy : ℤ := if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0
    (rayMarchStep A B (B.x - A.x) (B.y - A.y) 0 sy c).2 = false ∧
    ( (rayMarchStep A B (B.x - A.x) (B.y - A.y) 0 sy c).1 = x ∨
      (targetDist 0 sy x (rayMarchStep A B (B.x - A.x) (B.y - A.y) 0 sy c).1 (floorPoint A) < targetDist 0 sy x c (floorPoint A) ∧
       0 < targetDist 0 sy x (rayMarchStep A B (B.x - A.x) (B.y - A.y) 0 sy c).1 (floorPoint A)) ) := by
  intro sy
  have hdx : B.x - A.x = 0 := by
    revert hsx; split_ifs with h1 h2 <;> intro h <;> [contradiction; contradiction; linarith]
  have hdy_ne : B.y - A.y ≠ 0 := by
    intro hdy0
    have hx_eq := (bbox_sx_zero x A B h_bbox (by simp [hdx])).1
    have hy_eq := (bbox_sy_zero x A B h_bbox (by simp [hdy0])).1
    have : x = floorPoint A := by cases x; dsimp at hx_eq hy_eq; rw [hx_eq, hy_eq]
    exact hxA this
  have h_cy_ne : c.y ≠ x.y := by
    intro hcy_eq
    have hx_eq : c.x = x.x := by
      have := (bbox_sx_zero x A B h_bbox (by simp [hdx])).1
      rw [hc_x, this]
    have : c = x := by cases c; dsimp at hx_eq hcy_eq; rw [hx_eq, hcy_eq]
    exact h_ne this
  have h_step := step_sx_zero A B x c tEnter tExit hdx hdy_ne h_enter_lt_exit h_int h_cy h_cy_ne h_cA_y
  rw [h_step.1]
  dsimp only []
  refine ⟨rfl, ?_⟩
  by_cases h_next_eq : ({ x := c.x, y := c.y + sy } : Cell) = x
  · left; exact h_next_eq
  · right
    have h_Dc : targetDist 0 sy x c (floorPoint A) = ((x.y - c.y) * sy).toNat := by
      unfold targetDist; dsimp only []
      have h_cond : 0 ≤ (c.x - (floorPoint A).x) * 0 ∧
        0 ≤ (c.y - (floorPoint A).y) * sy ∧
        0 ≤ (x.x - c.x) * 0 ∧
        0 ≤ (x.y - c.y) * sy ∧
        (c.x = (floorPoint A).x ∨ (0 : ℤ) ≠ 0) ∧
        (c.y = (floorPoint A).y ∨ sy ≠ 0) ∧
        c ≠ x := ⟨by simp, h_cA_y, by simp, h_cy, Or.inl hc_x, Or.inr (by
          dsimp [sy]
          rcases lt_or_gt_of_ne hdy_ne with h | h
          · have : ¬(B.y - A.y > 0) := by linarith
            simp [this, h]
          · simp [h]), h_ne⟩
      split_ifs; simp
    have h_Dnext : targetDist 0 sy x { x := c.x, y := c.y + sy } (floorPoint A) =
        ((x.y - (c.y + sy)) * sy).toNat := by
      unfold targetDist; dsimp only []
      have h_cond : 0 ≤ (c.x - (floorPoint A).x) * 0 ∧
        0 ≤ (c.y + sy - (floorPoint A).y) * sy ∧
        0 ≤ (x.x - c.x) * 0 ∧
        0 ≤ (x.y - (c.y + sy)) * sy ∧
        (c.x = (floorPoint A).x ∨ (0 : ℤ) ≠ 0) ∧
        (c.y + sy = (floorPoint A).y ∨ sy ≠ 0) ∧
        ({ x := c.x, y := c.y + sy } : Cell) ≠ x := ⟨by simp, h_step.2.2.2, by simp, h_step.2.2.1, Or.inl hc_x, Or.inr (by
          dsimp [sy]
          rcases lt_or_gt_of_ne hdy_ne with h | h
          · have : ¬(B.y - A.y > 0) := by linarith
            simp [this, h]
          · simp [h]), h_next_eq⟩
      split_ifs; simp
    rw [h_Dc, h_Dnext]
    have h_lt := h_step.2.1
    have h_ge := h_step.2.2.1
    have h_sy_ne : sy ≠ 0 := by
      dsimp [sy]
      rcases lt_or_gt_of_ne hdy_ne with h | h
      · have : ¬(B.y - A.y > 0) := by linarith
        simp [this, h]
      · simp [h]
    have h_next_y_ne : c.y + sy ≠ x.y := by
      intro h_eq
      apply h_next_eq
      have h_x_eq : c.x = x.x := by
        have := (bbox_sx_zero x A B h_bbox (by simp [hdx])).1
        rw [hc_x, this]
      cases c
      cases x
      dsimp at h_x_eq h_eq
      rw [h_x_eq, h_eq]
    dsimp [sy] at *
    have h_pos : 0 < (x.y - (c.y + if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0)) *
        (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0) := by
      have : (x.y - (c.y + if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0)) *
          (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0) ≠ 0 := by
        intro h0
        rcases mul_eq_zero.mp h0 with h1 | h2
        · apply h_next_y_ne; linarith
        · contradiction
      omega
    refine ⟨by omega, by omega⟩


theorem targetDist_step_sy_zero (A B : Point) (x c : Cell) (tEnter tExit : ℚ)
    (h_bbox : inBoundingBox x A B = true) (hxA : x ≠ floorPoint A)
    (h_int : cellIntersectionInterval x A B = some (tEnter, tExit))
    (h_enter_lt_exit : tEnter < tExit)
    (hsy : (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else (0 : ℤ)) = 0)
    (h_cA_x : 0 ≤ (c.x - (floorPoint A).x) * if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0)
    (h_cx : 0 ≤ (x.x - c.x) * if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0)
    (hc_y : c.y = (floorPoint A).y)
    (h_ne : c ≠ x) :
    let sx : ℤ := if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0
    (rayMarchStep A B (B.x - A.x) (B.y - A.y) sx 0 c).2 = false ∧
    ( (rayMarchStep A B (B.x - A.x) (B.y - A.y) sx 0 c).1 = x ∨
      (targetDist sx 0 x (rayMarchStep A B (B.x - A.x) (B.y - A.y) sx 0 c).1 (floorPoint A) < targetDist sx 0 x c (floorPoint A) ∧
       0 < targetDist sx 0 x (rayMarchStep A B (B.x - A.x) (B.y - A.y) sx 0 c).1 (floorPoint A)) ) := by
  intro sx
  have hdy : B.y - A.y = 0 := by
    revert hsy; split_ifs with h1 h2 <;> intro h <;> [contradiction; contradiction; linarith]
  have hdx_ne : B.x - A.x ≠ 0 := by
    intro hdx0
    have hx_eq := (bbox_sx_zero x A B h_bbox (by simp [hdx0])).1
    have hy_eq := (bbox_sy_zero x A B h_bbox (by simp [hdy])).1
    have : x = floorPoint A := by cases x; dsimp at hx_eq hy_eq; rw [hx_eq, hy_eq]
    exact hxA this
  have h_cx_ne : c.x ≠ x.x := by
    intro hcx_eq
    have hy_eq : c.y = x.y := by
      have := (bbox_sy_zero x A B h_bbox (by simp [hdy])).1
      rw [hc_y, this]
    have : c = x := by cases c; dsimp at hcx_eq hy_eq; rw [hcx_eq, hy_eq]
    exact h_ne this
  have h_step := step_sy_zero A B x c tEnter tExit hdy hdx_ne h_enter_lt_exit h_int h_cx h_cx_ne h_cA_x
  rw [h_step.1]
  dsimp only []
  refine ⟨rfl, ?_⟩
  by_cases h_next_eq : ({ x := c.x + sx, y := c.y } : Cell) = x
  · left; exact h_next_eq
  · right
    have h_Dc : targetDist sx 0 x c (floorPoint A) = ((x.x - c.x) * sx).toNat := by
      unfold targetDist; dsimp only []
      have h_cond : 0 ≤ (c.x - (floorPoint A).x) * sx ∧
        0 ≤ (c.y - (floorPoint A).y) * 0 ∧
        0 ≤ (x.x - c.x) * sx ∧
        0 ≤ (x.y - c.y) * 0 ∧
        (c.x = (floorPoint A).x ∨ sx ≠ 0) ∧
        (c.y = (floorPoint A).y ∨ (0 : ℤ) ≠ 0) ∧
        c ≠ x := ⟨h_cA_x, by simp, h_cx, by simp, Or.inr (by
          dsimp [sx]
          rcases lt_or_gt_of_ne hdx_ne with h | h
          · have : ¬(B.x - A.x > 0) := by linarith
            simp [this, h]
          · simp [h]), Or.inl hc_y, h_ne⟩
      split_ifs; simp
    have h_Dnext : targetDist sx 0 x { x := c.x + sx, y := c.y } (floorPoint A) =
        ((x.x - (c.x + sx)) * sx).toNat := by
      unfold targetDist; dsimp only []
      have h_cond : 0 ≤ (c.x + sx - (floorPoint A).x) * sx ∧
        0 ≤ (c.y - (floorPoint A).y) * 0 ∧
        0 ≤ (x.x - (c.x + sx)) * sx ∧
        0 ≤ (x.y - c.y) * 0 ∧
        (c.x + sx = (floorPoint A).x ∨ sx ≠ 0) ∧
        (c.y = (floorPoint A).y ∨ (0 : ℤ) ≠ 0) ∧
        ({ x := c.x + sx, y := c.y } : Cell) ≠ x := ⟨h_step.2.2.2, by simp, h_step.2.2.1, by simp, Or.inr (by
          dsimp [sx]
          rcases lt_or_gt_of_ne hdx_ne with h | h
          · have : ¬(B.x - A.x > 0) := by linarith
            simp [this, h]
          · simp [h]), Or.inl hc_y, h_next_eq⟩
      split_ifs; simp
    rw [h_Dc, h_Dnext]
    have h_lt := h_step.2.1
    have h_ge := h_step.2.2.1
    have h_sx_ne : sx ≠ 0 := by
      dsimp [sx]
      rcases lt_or_gt_of_ne hdx_ne with h | h
      · have : ¬(B.x - A.x > 0) := by linarith
        simp [this, h]
      · simp [h]
    have h_next_x_ne : c.x + sx ≠ x.x := by
      intro h_eq
      apply h_next_eq
      have h_y_eq : c.y = x.y := by
        have := (bbox_sy_zero x A B h_bbox (by simp [hdy])).1
        rw [hc_y, this]
      cases c
      cases x
      dsimp at h_eq h_y_eq
      rw [h_eq, h_y_eq]
    dsimp [sx] at *
    have h_pos : 0 < (x.x - (c.x + if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0)) *
        (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0) := by
      have : (x.x - (c.x + if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0)) *
          (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0) ≠ 0 := by
        intro h0
        rcases mul_eq_zero.mp h0 with h1 | h2
        · apply h_next_x_ne; linarith
        · contradiction
      omega
    refine ⟨by omega, by omega⟩


theorem targetDist_step_pos_pos (A B : Point) (x c : Cell) (tEnter tExit : ℚ)
    (h_bbox : inBoundingBox x A B = true) (hxA : x ≠ floorPoint A)
    (h_int : cellIntersectionInterval x A B = some (tEnter, tExit))
    (h_enter_lt_exit : tEnter < tExit)
    (hdx : 0 < B.x - A.x) (hdy : 0 < B.y - A.y)
    (h_cA_x : 0 ≤ (c.x - (floorPoint A).x) * 1)
    (h_cA_y : 0 ≤ (c.y - (floorPoint A).y) * 1)
    (h_cx : 0 ≤ (x.x - c.x) * 1)
    (h_cy : 0 ≤ (x.y - c.y) * 1)
    (h_ne : c ≠ x) :
    (rayMarchStep A B (B.x - A.x) (B.y - A.y) 1 1 c).2 = false ∧
    ( (rayMarchStep A B (B.x - A.x) (B.y - A.y) 1 1 c).1 = x ∨
      (targetDist 1 1 x (rayMarchStep A B (B.x - A.x) (B.y - A.y) 1 1 c).1 (floorPoint A) < targetDist 1 1 x c (floorPoint A) ∧
       0 < targetDist 1 1 x (rayMarchStep A B (B.x - A.x) (B.y - A.y) 1 1 c).1 (floorPoint A)) ) := by
  have hsx_ne : ((1 : ℤ) == 0) = false := rfl
  have hsy_ne : ((1 : ℤ) == 0) = false := rfl
  have h_diag := rayMarchStep_diag A B c (B.x - A.x) (B.y - A.y) 1 1 hsx_ne hsy_ne
  dsimp only [] at h_diag
  have h_tx := interval_dx_pos x A B tEnter tExit h_int hdx
  have h_ty := interval_dy_pos x A B tEnter tExit h_int hdy
  have h_exit_le_one := (interval_enter_exit_le_one x A B tEnter tExit h_int).2
  have h_absDx : (if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) = B.x - A.x := by
    split_ifs with h <;> [rfl; linarith]
  have h_absDy : (if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)) = B.y - A.y := by
    split_ifs with h <;> [rfl; linarith]
  have h_flA_x : (floorPoint A).x = toInt A.x := rfl
  have h_lt_x : A.x < ((floorPoint A).x : ℚ) + 1 := by
    have := Rat.lt_floor_add_one A.x
    unfold toInt at h_flA_x; rw [← h_flA_x] at this; push_cast at this; exact this
  have h_cast_cA_x : ((floorPoint A).x : ℚ) ≤ (c.x : ℚ) := Int.cast_le.mpr (by omega)
  have h_ge_x : A.x < ofInt (c.x + 1) := by dsimp [ofInt]; push_cast; linarith
  have h_flA_y : (floorPoint A).y = toInt A.y := rfl
  have h_lt_y : A.y < ((floorPoint A).y : ℚ) + 1 := by
    have := Rat.lt_floor_add_one A.y
    unfold toInt at h_flA_y; rw [← h_flA_y] at this; push_cast at this; exact this
  have h_cast_cA_y : ((floorPoint A).y : ℚ) ≤ (c.y : ℚ) := Int.cast_le.mpr (by omega)
  have h_ge_y : A.y < ofInt (c.y + 1) := by dsimp [ofInt]; push_cast; linarith
  have h_one_pos : (1 : ℤ) > 0 := by decide
  have h_remX : (if (if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
      (if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
    else A.x - if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) = ofInt (c.x + 1) - A.x := by
    simp only [h_one_pos, ↓reduceIte]
    split_ifs with h <;> [rfl; linarith]
  have h_remY : (if (if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
      (if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
    else A.y - if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) = ofInt (c.y + 1) - A.y := by
    simp only [h_one_pos, ↓reduceIte]
    split_ifs with h <;> [rfl; linarith]
  have h_cases : c.x + 1 ≤ x.x ∨ c.y + 1 ≤ x.y := by
    rcases lt_or_eq_of_le (show c.x ≤ x.x by omega) with h1 | h1
    · left; omega
    · rcases lt_or_eq_of_le (show c.y ≤ x.y by omega) with h2 | h2
      · right; omega
      · exfalso; apply h_ne; cases c; cases x; dsimp at h1 h2; rw [h1, h2]
  have h_lim := min_cross_lt_limit_pos_pos c.x c.y x.x x.y A.x A.y (B.x - A.x) (B.y - A.y) tEnter tExit
    hdx hdy h_enter_lt_exit h_exit_le_one h_tx h_ty h_cases
  dsimp only [] at h_lim
  rw [h_absDx, h_absDy, h_remX, h_remY] at h_diag
  have h_not_done : ¬(min ((ofInt (c.x + 1) - A.x) * (B.y - A.y)) ((ofInt (c.y + 1) - A.y) * (B.x - A.x)) ≥
      (B.x - A.x) * (B.y - A.y)) := by linarith
  rw [h_diag]
  simp only [ge_iff_le, h_not_done, ↓reduceIte]
  have h_step_not_done : (if (ofInt (c.x + 1) - A.x) * (B.y - A.y) < (ofInt (c.y + 1) - A.y) * (B.x - A.x) then
      (({ x := c.x + 1, y := c.y } : Cell), false)
    else if (ofInt (c.y + 1) - A.y) * (B.x - A.x) < (ofInt (c.x + 1) - A.x) * (B.y - A.y) then
      (({ x := c.x, y := c.y + 1 } : Cell), false)
    else (({ x := c.x + 1, y := c.y + 1 } : Cell), false)).2 = false := by
    split_ifs <;> rfl
  refine ⟨h_step_not_done, ?_⟩
  have h_eval_targetDist : ∀ (px py : ℤ), (floorPoint A).x ≤ px → (floorPoint A).y ≤ py →
      px ≤ x.x → py ≤ x.y → ({ x := px, y := py } : Cell) ≠ x →
      targetDist 1 1 x { x := px, y := py } (floorPoint A) = ((x.x - px) + (x.y - py)).toNat := by
    intro px py hpAx hpAy hpx hpy hpne
    unfold targetDist; dsimp only []
    have h_cond : 0 ≤ (px - (floorPoint A).x) * 1 ∧
      0 ≤ (py - (floorPoint A).y) * 1 ∧
      0 ≤ (x.x - px) * 1 ∧
      0 ≤ (x.y - py) * 1 ∧
      (px = (floorPoint A).x ∨ (1 : ℤ) ≠ 0) ∧
      (py = (floorPoint A).y ∨ (1 : ℤ) ≠ 0) ∧
      ({ x := px, y := py } : Cell) ≠ x := ⟨by omega, by omega, by omega, by omega, Or.inr (by decide), Or.inr (by decide), hpne⟩
    split_ifs; simp
  have hc_cell : c = { x := c.x, y := c.y } := by cases c; rfl
  have h_ne_pair : ({ x := c.x, y := c.y } : Cell) ≠ x := by rw [← hc_cell]; exact h_ne
  have h_Dc : targetDist 1 1 x c (floorPoint A) = ((x.x - c.x) + (x.y - c.y)).toNat := by
    rw [hc_cell]
    exact h_eval_targetDist c.x c.y (by omega) (by omega) (by omega) (by omega) h_ne_pair
  have h_cell_ne : ∀ nx ny : ℤ, ({ x := nx, y := ny } : Cell) ≠ x → nx ≠ x.x ∨ ny ≠ x.y := by
    intro nx ny hne
    contrapose! hne
    cases x
    dsimp at hne
    rw [hne.1, hne.2]
  rcases eq_or_lt_of_le (show c.x ≤ x.x by omega) with hcx_eq | hcx_lt
  · -- cx = xx, so cy + 1 ≤ xy
    have hcy_le : c.y + 1 ≤ x.y := by
      rcases h_cases with h | h
      · omega
      · exact h
    have h_cross := cross_pos_pos c.x c.y x.x x.y A.x A.y (B.x - A.x) (B.y - A.y) tEnter tExit
      hdx hdy h_enter_lt_exit h_tx h_ty hcx_eq hcy_le
    dsimp only [] at h_cross
    have h_not_xy : ¬((ofInt (c.x + 1) - A.x) * (B.y - A.y) < (ofInt (c.y + 1) - A.y) * (B.x - A.x)) := by linarith
    simp only [h_not_xy, ↓reduceIte, h_cross]
    by_cases h_next_eq : ({ x := c.x, y := c.y + 1 } : Cell) = x
    · left; exact h_next_eq
    · right
      have h_Dnext := h_eval_targetDist c.x (c.y + 1) (by omega) (by omega) (by omega) (by omega) h_next_eq
      have h_ne_coords := h_cell_ne c.x (c.y + 1) h_next_eq
      rw [h_Dc, h_Dnext]
      refine ⟨by omega, by omega⟩
  · rcases eq_or_lt_of_le (show c.y ≤ x.y by omega) with hcy_eq | hcy_lt
    · -- cy = xy, so cx + 1 ≤ xx
      have hcx_le : c.x + 1 ≤ x.x := by
        rcases h_cases with h | h
        · exact h
        · omega
      have h_cross := cross_ge_pos_pos c.x c.y x.x x.y A.x A.y (B.x - A.x) (B.y - A.y) tEnter tExit
        hdx hdy h_enter_lt_exit h_tx h_ty hcy_eq hcx_le
      dsimp only [] at h_cross
      simp only [h_cross, ↓reduceIte]
      by_cases h_next_eq : ({ x := c.x + 1, y := c.y } : Cell) = x
      · left; exact h_next_eq
      · right
        have h_Dnext := h_eval_targetDist (c.x + 1) c.y (by omega) (by omega) (by omega) (by omega) h_next_eq
        have h_ne_coords := h_cell_ne (c.x + 1) c.y h_next_eq
        rw [h_Dc, h_Dnext]
        refine ⟨by omega, by omega⟩
    · -- both <
      have hcx_le : c.x + 1 ≤ x.x := hcx_lt
      have hcy_le : c.y + 1 ≤ x.y := hcy_lt
      split_ifs with h1 h2
      · by_cases h_next_eq : ({ x := c.x + 1, y := c.y } : Cell) = x
        · left; exact h_next_eq
        · right
          have h_Dnext := h_eval_targetDist (c.x + 1) c.y (by omega) (by omega) (by omega) (by omega) h_next_eq
          have h_ne_coords := h_cell_ne (c.x + 1) c.y h_next_eq
          rw [h_Dc, h_Dnext]
          refine ⟨by omega, by omega⟩
      · by_cases h_next_eq : ({ x := c.x, y := c.y + 1 } : Cell) = x
        · left; exact h_next_eq
        · right
          have h_Dnext := h_eval_targetDist c.x (c.y + 1) (by omega) (by omega) (by omega) (by omega) h_next_eq
          have h_ne_coords := h_cell_ne c.x (c.y + 1) h_next_eq
          rw [h_Dc, h_Dnext]
          refine ⟨by omega, by omega⟩
      · by_cases h_next_eq : ({ x := c.x + 1, y := c.y + 1 } : Cell) = x
        · left; exact h_next_eq
        · right
          have h_Dnext := h_eval_targetDist (c.x + 1) (c.y + 1) (by omega) (by omega) (by omega) (by omega) h_next_eq
          have h_ne_coords := h_cell_ne (c.x + 1) (c.y + 1) h_next_eq
          rw [h_Dc, h_Dnext]
          refine ⟨by omega, by omega⟩


theorem targetDist_step_pos_neg (A B : Point) (x c : Cell) (tEnter tExit : ℚ)
    (h_bbox : inBoundingBox x A B = true) (hxA : x ≠ floorPoint A)
    (h_int : cellIntersectionInterval x A B = some (tEnter, tExit))
    (h_enter_lt_exit : tEnter < tExit)
    (hdx : 0 < B.x - A.x) (hdy : B.y - A.y < 0)
    (h_cA_x : 0 ≤ (c.x - (floorPoint A).x) * 1)
    (h_cA_y : 0 ≤ (c.y - (floorPoint A).y) * (-1))
    (h_cx : 0 ≤ (x.x - c.x) * 1)
    (h_cy : 0 ≤ (x.y - c.y) * (-1))
    (h_ne : c ≠ x) :
    (rayMarchStep A B (B.x - A.x) (B.y - A.y) 1 (-1) c).2 = false ∧
    ( (rayMarchStep A B (B.x - A.x) (B.y - A.y) 1 (-1) c).1 = x ∨
      (targetDist 1 (-1) x (rayMarchStep A B (B.x - A.x) (B.y - A.y) 1 (-1) c).1 (floorPoint A) < targetDist 1 (-1) x c (floorPoint A) ∧
       0 < targetDist 1 (-1) x (rayMarchStep A B (B.x - A.x) (B.y - A.y) 1 (-1) c).1 (floorPoint A)) ) := by
  have hsx_ne : ((1 : ℤ) == 0) = false := rfl
  have hsy_ne : ((-1 : ℤ) == 0) = false := rfl
  have h_diag := rayMarchStep_diag A B c (B.x - A.x) (B.y - A.y) 1 (-1) hsx_ne hsy_ne
  dsimp only [] at h_diag
  have h_tx := interval_dx_pos x A B tEnter tExit h_int hdx
  have h_ty := interval_dy_neg x A B tEnter tExit h_int hdy
  have h_exit_le_one := (interval_enter_exit_le_one x A B tEnter tExit h_int).2
  have h_absDx : (if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) = B.x - A.x := by
    split_ifs with h <;> [rfl; linarith]
  have h_absDy : (if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)) = -(B.y - A.y) := by
    split_ifs with h <;> [linarith; rfl]
  have h_flA_x : (floorPoint A).x = toInt A.x := rfl
  have h_lt_x : A.x < ((floorPoint A).x : ℚ) + 1 := by
    have := Rat.lt_floor_add_one A.x
    unfold toInt at h_flA_x; rw [← h_flA_x] at this; push_cast at this; exact this
  have h_cast_cA_x : ((floorPoint A).x : ℚ) ≤ (c.x : ℚ) := Int.cast_le.mpr (by omega)
  have h_ge_x : A.x < ofInt (c.x + 1) := by dsimp [ofInt]; push_cast; linarith
  have h_flA_y : (floorPoint A).y = toInt A.y := rfl
  have h_le_y : ((floorPoint A).y : ℚ) ≤ A.y := by
    have := Rat.floor_le A.y
    unfold toInt at h_flA_y; rw [← h_flA_y] at this; exact this
  have h_cast_cA_y : (c.y : ℚ) ≤ ((floorPoint A).y : ℚ) := Int.cast_le.mpr (by omega)
  have h_le_cA_y : ofInt c.y ≤ A.y := by dsimp [ofInt]; linarith
  have h_one_pos : (1 : ℤ) > 0 := by decide
  have h_neg_one_not_pos : ¬((-1 : ℤ) > 0) := by decide
  have h_remX : (if (if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
      (if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
    else A.x - if (1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) = ofInt (c.x + 1) - A.x := by
    simp only [h_one_pos, ↓reduceIte]
    split_ifs with h <;> [rfl; linarith]
  have h_remY : (if (if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
      (if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
    else A.y - if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) = A.y - ofInt c.y := by
    simp only [h_neg_one_not_pos, ↓reduceIte]
    split_ifs with h <;> [linarith; rfl]
  have h_cases : c.x + 1 ≤ x.x ∨ x.y + 1 ≤ c.y := by
    rcases lt_or_eq_of_le (show c.x ≤ x.x by omega) with h1 | h1
    · left; omega
    · rcases lt_or_eq_of_le (show x.y ≤ c.y by omega) with h2 | h2
      · right; omega
      · exfalso; apply h_ne; cases c; cases x; dsimp at h1 h2; rw [h1, h2]
  have h_lim := min_cross_lt_limit_pos_neg c.x c.y x.x x.y A.x A.y (B.x - A.x) (B.y - A.y) tEnter tExit
    hdx hdy h_enter_lt_exit h_exit_le_one h_tx h_ty h_cases
  dsimp only [] at h_lim
  rw [h_absDx, h_absDy, h_remX, h_remY] at h_diag
  have h_not_done : ¬(min ((ofInt (c.x + 1) - A.x) * -(B.y - A.y)) ((A.y - ofInt c.y) * (B.x - A.x)) ≥
      (B.x - A.x) * -(B.y - A.y)) := by linarith
  rw [h_diag]
  simp only [ge_iff_le, h_not_done, ↓reduceIte]
  have h_step_not_done : (if (ofInt (c.x + 1) - A.x) * -(B.y - A.y) < (A.y - ofInt c.y) * (B.x - A.x) then
      (({ x := c.x + 1, y := c.y } : Cell), false)
    else if (A.y - ofInt c.y) * (B.x - A.x) < (ofInt (c.x + 1) - A.x) * -(B.y - A.y) then
      (({ x := c.x, y := c.y + -1 } : Cell), false)
    else (({ x := c.x + 1, y := c.y + -1 } : Cell), false)).2 = false := by
    split_ifs <;> rfl
  refine ⟨h_step_not_done, ?_⟩
  have h_eval_targetDist : ∀ (px py : ℤ), (floorPoint A).x ≤ px → py ≤ (floorPoint A).y →
      px ≤ x.x → x.y ≤ py → ({ x := px, y := py } : Cell) ≠ x →
      targetDist 1 (-1) x { x := px, y := py } (floorPoint A) = ((x.x - px) + (py - x.y)).toNat := by
    intro px py hpAx hpAy hpx hpy hpne
    unfold targetDist; dsimp only []
    have h_cond : 0 ≤ (px - (floorPoint A).x) * 1 ∧
      0 ≤ (py - (floorPoint A).y) * (-1) ∧
      0 ≤ (x.x - px) * 1 ∧
      0 ≤ (x.y - py) * (-1) ∧
      (px = (floorPoint A).x ∨ (1 : ℤ) ≠ 0) ∧
      (py = (floorPoint A).y ∨ (-1 : ℤ) ≠ 0) ∧
      ({ x := px, y := py } : Cell) ≠ x := ⟨by omega, by omega, by omega, by omega, Or.inr (by decide), Or.inr (by decide), hpne⟩
    split_ifs; congr 1; ring
  have hc_cell : c = { x := c.x, y := c.y } := by cases c; rfl
  have h_ne_pair : ({ x := c.x, y := c.y } : Cell) ≠ x := by rw [← hc_cell]; exact h_ne
  have h_Dc : targetDist 1 (-1) x c (floorPoint A) = ((x.x - c.x) + (c.y - x.y)).toNat := by
    rw [hc_cell]
    exact h_eval_targetDist c.x c.y (by omega) (by omega) (by omega) (by omega) h_ne_pair
  have h_cell_ne : ∀ nx ny : ℤ, ({ x := nx, y := ny } : Cell) ≠ x → nx ≠ x.x ∨ ny ≠ x.y := by
    intro nx ny hne
    contrapose! hne
    cases x
    dsimp at hne
    rw [hne.1, hne.2]
  rcases eq_or_lt_of_le (show c.x ≤ x.x by omega) with hcx_eq | hcx_lt
  · -- cx = xx, so xy + 1 ≤ cy
    have hcy_le : x.y + 1 ≤ c.y := by
      rcases h_cases with h | h
      · omega
      · exact h
    have h_cross := cross_pos_neg c.x c.y x.x x.y A.x A.y (B.x - A.x) (B.y - A.y) tEnter tExit
      hdx hdy h_enter_lt_exit h_tx h_ty hcx_eq hcy_le
    dsimp only [] at h_cross
    have h_not_xy : ¬((ofInt (c.x + 1) - A.x) * -(B.y - A.y) < (A.y - ofInt c.y) * (B.x - A.x)) := by linarith
    simp only [h_not_xy, ↓reduceIte, h_cross]
    by_cases h_next_eq : ({ x := c.x, y := c.y + -1 } : Cell) = x
    · left; exact h_next_eq
    · right
      have h_Dnext := h_eval_targetDist c.x (c.y + -1) (by omega) (by omega) (by omega) (by omega) h_next_eq
      have h_ne_coords := h_cell_ne c.x (c.y + -1) h_next_eq
      rw [h_Dc, h_Dnext]
      refine ⟨by omega, by omega⟩
  · rcases eq_or_lt_of_le (show x.y ≤ c.y by omega) with hcy_eq | hcy_lt
    · -- cy = xy, so cx + 1 ≤ xx
      have hcx_le : c.x + 1 ≤ x.x := by
        rcases h_cases with h | h
        · exact h
        · omega
      have h_cross := cross_ge_pos_neg c.x c.y x.x x.y A.x A.y (B.x - A.x) (B.y - A.y) tEnter tExit
        hdx hdy h_enter_lt_exit h_tx h_ty hcy_eq.symm hcx_le
      dsimp only [] at h_cross
      simp only [h_cross, ↓reduceIte]
      by_cases h_next_eq : ({ x := c.x + 1, y := c.y } : Cell) = x
      · left; exact h_next_eq
      · right
        have h_Dnext := h_eval_targetDist (c.x + 1) c.y (by omega) (by omega) (by omega) (by omega) h_next_eq
        have h_ne_coords := h_cell_ne (c.x + 1) c.y h_next_eq
        rw [h_Dc, h_Dnext]
        refine ⟨by omega, by omega⟩
    · -- both <
      have hcx_le : c.x + 1 ≤ x.x := hcx_lt
      have hcy_le : x.y + 1 ≤ c.y := hcy_lt
      split_ifs with h1 h2
      · by_cases h_next_eq : ({ x := c.x + 1, y := c.y } : Cell) = x
        · left; exact h_next_eq
        · right
          have h_Dnext := h_eval_targetDist (c.x + 1) c.y (by omega) (by omega) (by omega) (by omega) h_next_eq
          have h_ne_coords := h_cell_ne (c.x + 1) c.y h_next_eq
          rw [h_Dc, h_Dnext]
          refine ⟨by omega, by omega⟩
      · by_cases h_next_eq : ({ x := c.x, y := c.y + -1 } : Cell) = x
        · left; exact h_next_eq
        · right
          have h_Dnext := h_eval_targetDist c.x (c.y + -1) (by omega) (by omega) (by omega) (by omega) h_next_eq
          have h_ne_coords := h_cell_ne c.x (c.y + -1) h_next_eq
          rw [h_Dc, h_Dnext]
          refine ⟨by omega, by omega⟩
      · by_cases h_next_eq : ({ x := c.x + 1, y := c.y + -1 } : Cell) = x
        · left; exact h_next_eq
        · right
          have h_Dnext := h_eval_targetDist (c.x + 1) (c.y + -1) (by omega) (by omega) (by omega) (by omega) h_next_eq
          have h_ne_coords := h_cell_ne (c.x + 1) (c.y + -1) h_next_eq
          rw [h_Dc, h_Dnext]
          refine ⟨by omega, by omega⟩


theorem targetDist_step_neg_pos (A B : Point) (x c : Cell) (tEnter tExit : ℚ)
    (h_bbox : inBoundingBox x A B = true) (hxA : x ≠ floorPoint A)
    (h_int : cellIntersectionInterval x A B = some (tEnter, tExit))
    (h_enter_lt_exit : tEnter < tExit)
    (hdx : B.x - A.x < 0) (hdy : 0 < B.y - A.y)
    (h_cA_x : 0 ≤ (c.x - (floorPoint A).x) * (-1))
    (h_cA_y : 0 ≤ (c.y - (floorPoint A).y) * 1)
    (h_cx : 0 ≤ (x.x - c.x) * (-1))
    (h_cy : 0 ≤ (x.y - c.y) * 1)
    (h_ne : c ≠ x) :
    (rayMarchStep A B (B.x - A.x) (B.y - A.y) (-1) 1 c).2 = false ∧
    ( (rayMarchStep A B (B.x - A.x) (B.y - A.y) (-1) 1 c).1 = x ∨
      (targetDist (-1) 1 x (rayMarchStep A B (B.x - A.x) (B.y - A.y) (-1) 1 c).1 (floorPoint A) < targetDist (-1) 1 x c (floorPoint A) ∧
       0 < targetDist (-1) 1 x (rayMarchStep A B (B.x - A.x) (B.y - A.y) (-1) 1 c).1 (floorPoint A)) ) := by
  have hsx_ne : (((-1 : ℤ) == 0) = false) := rfl
  have hsy_ne : ((1 : ℤ) == 0) = false := rfl
  have h_diag := rayMarchStep_diag A B c (B.x - A.x) (B.y - A.y) (-1) 1 hsx_ne hsy_ne
  dsimp only [] at h_diag
  have h_tx := interval_dx_neg x A B tEnter tExit h_int hdx
  have h_ty := interval_dy_pos x A B tEnter tExit h_int hdy
  have h_exit_le_one := (interval_enter_exit_le_one x A B tEnter tExit h_int).2
  have h_absDx : (if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) = -(B.x - A.x) := by
    split_ifs with h <;> [linarith; rfl]
  have h_absDy : (if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)) = B.y - A.y := by
    split_ifs with h <;> [rfl; linarith]
  have h_flA_x : (floorPoint A).x = toInt A.x := rfl
  have h_le_x : ((floorPoint A).x : ℚ) ≤ A.x := by
    have := Rat.floor_le A.x
    unfold toInt at h_flA_x; rw [← h_flA_x] at this; exact this
  have h_cast_cA_x : (c.x : ℚ) ≤ ((floorPoint A).x : ℚ) := Int.cast_le.mpr (by omega)
  have h_le_cA_x : ofInt c.x ≤ A.x := by dsimp [ofInt]; linarith
  have h_flA_y : (floorPoint A).y = toInt A.y := rfl
  have h_lt_y : A.y < ((floorPoint A).y : ℚ) + 1 := by
    have := Rat.lt_floor_add_one A.y
    unfold toInt at h_flA_y; rw [← h_flA_y] at this; push_cast at this; exact this
  have h_cast_cA_y : ((floorPoint A).y : ℚ) ≤ (c.y : ℚ) := Int.cast_le.mpr (by omega)
  have h_ge_y : A.y < ofInt (c.y + 1) := by dsimp [ofInt]; push_cast; linarith
  have h_one_pos : (1 : ℤ) > 0 := by decide
  have h_neg_one_not_pos : ¬((-1 : ℤ) > 0) := by decide
  have h_remX : (if (if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
      (if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
    else A.x - if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) = A.x - ofInt c.x := by
    simp only [h_neg_one_not_pos, ↓reduceIte]
    split_ifs with h <;> [linarith; rfl]
  have h_remY : (if (if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
      (if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
    else A.y - if (1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) = ofInt (c.y + 1) - A.y := by
    simp only [h_one_pos, ↓reduceIte]
    split_ifs with h <;> [rfl; linarith]
  have h_cases : x.x + 1 ≤ c.x ∨ c.y + 1 ≤ x.y := by
    rcases lt_or_eq_of_le (show x.x ≤ c.x by omega) with h1 | h1
    · left; omega
    · rcases lt_or_eq_of_le (show c.y ≤ x.y by omega) with h2 | h2
      · right; omega
      · exfalso; apply h_ne; cases c; cases x; dsimp at h1 h2; rw [h1, h2]
  have h_lim := min_cross_lt_limit_neg_pos c.x c.y x.x x.y A.x A.y (B.x - A.x) (B.y - A.y) tEnter tExit
    hdx hdy h_enter_lt_exit h_exit_le_one h_tx h_ty h_cases
  dsimp only [] at h_lim
  rw [h_absDx, h_absDy, h_remX, h_remY] at h_diag
  have h_not_done : ¬(min ((A.x - ofInt c.x) * (B.y - A.y)) ((ofInt (c.y + 1) - A.y) * -(B.x - A.x)) ≥
      -(B.x - A.x) * (B.y - A.y)) := by linarith
  rw [h_diag]
  simp only [ge_iff_le, h_not_done, ↓reduceIte]
  have h_step_not_done : (if (A.x - ofInt c.x) * (B.y - A.y) < (ofInt (c.y + 1) - A.y) * -(B.x - A.x) then
      (({ x := c.x + -1, y := c.y } : Cell), false)
    else if (ofInt (c.y + 1) - A.y) * -(B.x - A.x) < (A.x - ofInt c.x) * (B.y - A.y) then
      (({ x := c.x, y := c.y + 1 } : Cell), false)
    else (({ x := c.x + -1, y := c.y + 1 } : Cell), false)).2 = false := by
    split_ifs <;> rfl
  refine ⟨h_step_not_done, ?_⟩
  have h_eval_targetDist : ∀ (px py : ℤ), px ≤ (floorPoint A).x → (floorPoint A).y ≤ py →
      x.x ≤ px → py ≤ x.y → ({ x := px, y := py } : Cell) ≠ x →
      targetDist (-1) 1 x { x := px, y := py } (floorPoint A) = ((px - x.x) + (x.y - py)).toNat := by
    intro px py hpAx hpAy hpx hpy hpne
    unfold targetDist; dsimp only []
    have h_cond : 0 ≤ (px - (floorPoint A).x) * (-1) ∧
      0 ≤ (py - (floorPoint A).y) * 1 ∧
      0 ≤ (x.x - px) * (-1) ∧
      0 ≤ (x.y - py) * 1 ∧
      (px = (floorPoint A).x ∨ (-1 : ℤ) ≠ 0) ∧
      (py = (floorPoint A).y ∨ (1 : ℤ) ≠ 0) ∧
      ({ x := px, y := py } : Cell) ≠ x := ⟨by omega, by omega, by omega, by omega, Or.inr (by decide), Or.inr (by decide), hpne⟩
    split_ifs; congr 1; ring
  have hc_cell : c = { x := c.x, y := c.y } := by cases c; rfl
  have h_ne_pair : ({ x := c.x, y := c.y } : Cell) ≠ x := by rw [← hc_cell]; exact h_ne
  have h_Dc : targetDist (-1) 1 x c (floorPoint A) = ((c.x - x.x) + (x.y - c.y)).toNat := by
    rw [hc_cell]
    exact h_eval_targetDist c.x c.y (by omega) (by omega) (by omega) (by omega) h_ne_pair
  have h_cell_ne : ∀ nx ny : ℤ, ({ x := nx, y := ny } : Cell) ≠ x → nx ≠ x.x ∨ ny ≠ x.y := by
    intro nx ny hne
    contrapose! hne
    cases x
    dsimp at hne
    rw [hne.1, hne.2]
  rcases eq_or_lt_of_le (show x.x ≤ c.x by omega) with hcx_eq | hcx_lt
  · -- cx = xx, so cy + 1 ≤ xy
    have hcy_le : c.y + 1 ≤ x.y := by
      rcases h_cases with h | h
      · omega
      · exact h
    have h_cross := cross_neg_pos c.x c.y x.x x.y A.x A.y (B.x - A.x) (B.y - A.y) tEnter tExit
      hdx hdy h_enter_lt_exit h_tx h_ty hcx_eq.symm hcy_le
    dsimp only [] at h_cross
    have h_not_xy : ¬((A.x - ofInt c.x) * (B.y - A.y) < (ofInt (c.y + 1) - A.y) * -(B.x - A.x)) := by linarith
    simp only [h_not_xy, ↓reduceIte, h_cross]
    by_cases h_next_eq : ({ x := c.x, y := c.y + 1 } : Cell) = x
    · left; exact h_next_eq
    · right
      have h_Dnext := h_eval_targetDist c.x (c.y + 1) (by omega) (by omega) (by omega) (by omega) h_next_eq
      have h_ne_coords := h_cell_ne c.x (c.y + 1) h_next_eq
      rw [h_Dc, h_Dnext]
      refine ⟨by omega, by omega⟩
  · rcases eq_or_lt_of_le (show c.y ≤ x.y by omega) with hcy_eq | hcy_lt
    · -- cy = xy, so xx + 1 ≤ cx
      have hcx_le : x.x + 1 ≤ c.x := by
        rcases h_cases with h | h
        · exact h
        · omega
      have h_cross := cross_ge_neg_pos c.x c.y x.x x.y A.x A.y (B.x - A.x) (B.y - A.y) tEnter tExit
        hdx hdy h_enter_lt_exit h_tx h_ty hcy_eq hcx_le
      dsimp only [] at h_cross
      simp only [h_cross, ↓reduceIte]
      by_cases h_next_eq : ({ x := c.x + -1, y := c.y } : Cell) = x
      · left; exact h_next_eq
      · right
        have h_Dnext := h_eval_targetDist (c.x + -1) c.y (by omega) (by omega) (by omega) (by omega) h_next_eq
        have h_ne_coords := h_cell_ne (c.x + -1) c.y h_next_eq
        rw [h_Dc, h_Dnext]
        refine ⟨by omega, by omega⟩
    · -- both <
      have hcx_le : x.x + 1 ≤ c.x := hcx_lt
      have hcy_le : c.y + 1 ≤ x.y := hcy_lt
      split_ifs with h1 h2
      · by_cases h_next_eq : ({ x := c.x + -1, y := c.y } : Cell) = x
        · left; exact h_next_eq
        · right
          have h_Dnext := h_eval_targetDist (c.x + -1) c.y (by omega) (by omega) (by omega) (by omega) h_next_eq
          have h_ne_coords := h_cell_ne (c.x + -1) c.y h_next_eq
          rw [h_Dc, h_Dnext]
          refine ⟨by omega, by omega⟩
      · by_cases h_next_eq : ({ x := c.x, y := c.y + 1 } : Cell) = x
        · left; exact h_next_eq
        · right
          have h_Dnext := h_eval_targetDist c.x (c.y + 1) (by omega) (by omega) (by omega) (by omega) h_next_eq
          have h_ne_coords := h_cell_ne c.x (c.y + 1) h_next_eq
          rw [h_Dc, h_Dnext]
          refine ⟨by omega, by omega⟩
      · by_cases h_next_eq : ({ x := c.x + -1, y := c.y + 1 } : Cell) = x
        · left; exact h_next_eq
        · right
          have h_Dnext := h_eval_targetDist (c.x + -1) (c.y + 1) (by omega) (by omega) (by omega) (by omega) h_next_eq
          have h_ne_coords := h_cell_ne (c.x + -1) (c.y + 1) h_next_eq
          rw [h_Dc, h_Dnext]
          refine ⟨by omega, by omega⟩


theorem targetDist_step_neg_neg (A B : Point) (x c : Cell) (tEnter tExit : ℚ)
    (h_bbox : inBoundingBox x A B = true) (hxA : x ≠ floorPoint A)
    (h_int : cellIntersectionInterval x A B = some (tEnter, tExit))
    (h_enter_lt_exit : tEnter < tExit)
    (hdx : B.x - A.x < 0) (hdy : B.y - A.y < 0)
    (h_cA_x : 0 ≤ (c.x - (floorPoint A).x) * (-1))
    (h_cA_y : 0 ≤ (c.y - (floorPoint A).y) * (-1))
    (h_cx : 0 ≤ (x.x - c.x) * (-1))
    (h_cy : 0 ≤ (x.y - c.y) * (-1))
    (h_ne : c ≠ x) :
    (rayMarchStep A B (B.x - A.x) (B.y - A.y) (-1) (-1) c).2 = false ∧
    ( (rayMarchStep A B (B.x - A.x) (B.y - A.y) (-1) (-1) c).1 = x ∨
      (targetDist (-1) (-1) x (rayMarchStep A B (B.x - A.x) (B.y - A.y) (-1) (-1) c).1 (floorPoint A) < targetDist (-1) (-1) x c (floorPoint A) ∧
       0 < targetDist (-1) (-1) x (rayMarchStep A B (B.x - A.x) (B.y - A.y) (-1) (-1) c).1 (floorPoint A)) ) := by
  have hsx_ne : (((-1 : ℤ) == 0) = false) := rfl
  have hsy_ne : (((-1 : ℤ) == 0) = false) := rfl
  have h_diag := rayMarchStep_diag A B c (B.x - A.x) (B.y - A.y) (-1) (-1) hsx_ne hsy_ne
  dsimp only [] at h_diag
  have h_tx := interval_dx_neg x A B tEnter tExit h_int hdx
  have h_ty := interval_dy_neg x A B tEnter tExit h_int hdy
  have h_exit_le_one := (interval_enter_exit_le_one x A B tEnter tExit h_int).2
  have h_absDx : (if B.x - A.x ≥ 0 then B.x - A.x else -(B.x - A.x)) = -(B.x - A.x) := by
    split_ifs with h <;> [linarith; rfl]
  have h_absDy : (if B.y - A.y ≥ 0 then B.y - A.y else -(B.y - A.y)) = -(B.y - A.y) := by
    split_ifs with h <;> [linarith; rfl]
  have h_flA_x : (floorPoint A).x = toInt A.x := rfl
  have h_le_x : ((floorPoint A).x : ℚ) ≤ A.x := by
    have := Rat.floor_le A.x
    unfold toInt at h_flA_x; rw [← h_flA_x] at this; exact this
  have h_cast_cA_x : (c.x : ℚ) ≤ ((floorPoint A).x : ℚ) := Int.cast_le.mpr (by omega)
  have h_le_cA_x : ofInt c.x ≤ A.x := by dsimp [ofInt]; linarith
  have h_flA_y : (floorPoint A).y = toInt A.y := rfl
  have h_le_y : ((floorPoint A).y : ℚ) ≤ A.y := by
    have := Rat.floor_le A.y
    unfold toInt at h_flA_y; rw [← h_flA_y] at this; exact this
  have h_cast_cA_y : (c.y : ℚ) ≤ ((floorPoint A).y : ℚ) := Int.cast_le.mpr (by omega)
  have h_le_cA_y : ofInt c.y ≤ A.y := by dsimp [ofInt]; linarith
  have h_neg_one_not_pos : ¬((-1 : ℤ) > 0) := by decide
  have h_remX : (if (if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) ≥ A.x then
      (if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) - A.x
    else A.x - if (-1 : ℤ) > 0 then ofInt (c.x + 1) else ofInt c.x) = A.x - ofInt c.x := by
    simp only [h_neg_one_not_pos, ↓reduceIte]
    split_ifs with h <;> [linarith; rfl]
  have h_remY : (if (if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) ≥ A.y then
      (if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) - A.y
    else A.y - if (-1 : ℤ) > 0 then ofInt (c.y + 1) else ofInt c.y) = A.y - ofInt c.y := by
    simp only [h_neg_one_not_pos, ↓reduceIte]
    split_ifs with h <;> [linarith; rfl]
  have h_cases : x.x + 1 ≤ c.x ∨ x.y + 1 ≤ c.y := by
    rcases lt_or_eq_of_le (show x.x ≤ c.x by omega) with h1 | h1
    · left; omega
    · rcases lt_or_eq_of_le (show x.y ≤ c.y by omega) with h2 | h2
      · right; omega
      · exfalso; apply h_ne; cases c; cases x; dsimp at h1 h2; rw [h1, h2]
  have h_lim := min_cross_lt_limit_neg_neg c.x c.y x.x x.y A.x A.y (B.x - A.x) (B.y - A.y) tEnter tExit
    hdx hdy h_enter_lt_exit h_exit_le_one h_tx h_ty h_cases
  dsimp only [] at h_lim
  rw [h_absDx, h_absDy, h_remX, h_remY] at h_diag
  have h_not_done : ¬(min ((A.x - ofInt c.x) * -(B.y - A.y)) ((A.y - ofInt c.y) * -(B.x - A.x)) ≥
      -(B.x - A.x) * -(B.y - A.y)) := by linarith
  rw [h_diag]
  simp only [ge_iff_le, h_not_done, ↓reduceIte]
  have h_step_not_done : (if (A.x - ofInt c.x) * -(B.y - A.y) < (A.y - ofInt c.y) * -(B.x - A.x) then
      (({ x := c.x + -1, y := c.y } : Cell), false)
    else if (A.y - ofInt c.y) * -(B.x - A.x) < (A.x - ofInt c.x) * -(B.y - A.y) then
      (({ x := c.x, y := c.y + -1 } : Cell), false)
    else (({ x := c.x + -1, y := c.y + -1 } : Cell), false)).2 = false := by
    split_ifs <;> rfl
  refine ⟨h_step_not_done, ?_⟩
  have h_eval_targetDist : ∀ (px py : ℤ), px ≤ (floorPoint A).x → py ≤ (floorPoint A).y →
      x.x ≤ px → x.y ≤ py → ({ x := px, y := py } : Cell) ≠ x →
      targetDist (-1) (-1) x { x := px, y := py } (floorPoint A) = ((px - x.x) + (py - x.y)).toNat := by
    intro px py hpAx hpAy hpx hpy hpne
    unfold targetDist; dsimp only []
    have h_cond : 0 ≤ (px - (floorPoint A).x) * (-1) ∧
      0 ≤ (py - (floorPoint A).y) * (-1) ∧
      0 ≤ (x.x - px) * (-1) ∧
      0 ≤ (x.y - py) * (-1) ∧
      (px = (floorPoint A).x ∨ (-1 : ℤ) ≠ 0) ∧
      (py = (floorPoint A).y ∨ (-1 : ℤ) ≠ 0) ∧
      ({ x := px, y := py } : Cell) ≠ x := ⟨by omega, by omega, by omega, by omega, Or.inr (by decide), Or.inr (by decide), hpne⟩
    split_ifs; congr 1; ring
  have hc_cell : c = { x := c.x, y := c.y } := by cases c; rfl
  have h_ne_pair : ({ x := c.x, y := c.y } : Cell) ≠ x := by rw [← hc_cell]; exact h_ne
  have h_Dc : targetDist (-1) (-1) x c (floorPoint A) = ((c.x - x.x) + (c.y - x.y)).toNat := by
    rw [hc_cell]
    exact h_eval_targetDist c.x c.y (by omega) (by omega) (by omega) (by omega) h_ne_pair
  have h_cell_ne : ∀ nx ny : ℤ, ({ x := nx, y := ny } : Cell) ≠ x → nx ≠ x.x ∨ ny ≠ x.y := by
    intro nx ny hne
    contrapose! hne
    cases x
    dsimp at hne
    rw [hne.1, hne.2]
  rcases eq_or_lt_of_le (show x.x ≤ c.x by omega) with hcx_eq | hcx_lt
  · -- cx = xx, so xy + 1 ≤ cy
    have hcy_le : x.y + 1 ≤ c.y := by
      rcases h_cases with h | h
      · omega
      · exact h
    have h_cross := cross_neg_neg c.x c.y x.x x.y A.x A.y (B.x - A.x) (B.y - A.y) tEnter tExit
      hdx hdy h_enter_lt_exit h_tx h_ty hcx_eq.symm hcy_le
    dsimp only [] at h_cross
    have h_not_xy : ¬((A.x - ofInt c.x) * -(B.y - A.y) < (A.y - ofInt c.y) * -(B.x - A.x)) := by linarith
    simp only [h_not_xy, ↓reduceIte, h_cross]
    by_cases h_next_eq : ({ x := c.x, y := c.y + -1 } : Cell) = x
    · left; exact h_next_eq
    · right
      have h_Dnext := h_eval_targetDist c.x (c.y + -1) (by omega) (by omega) (by omega) (by omega) h_next_eq
      have h_ne_coords := h_cell_ne c.x (c.y + -1) h_next_eq
      rw [h_Dc, h_Dnext]
      refine ⟨by omega, by omega⟩
  · rcases eq_or_lt_of_le (show x.y ≤ c.y by omega) with hcy_eq | hcy_lt
    · -- cy = xy, so xx + 1 ≤ cx
      have hcx_le : x.x + 1 ≤ c.x := by
        rcases h_cases with h | h
        · exact h
        · omega
      have h_cross := cross_ge_neg_neg c.x c.y x.x x.y A.x A.y (B.x - A.x) (B.y - A.y) tEnter tExit
        hdx hdy h_enter_lt_exit h_tx h_ty hcy_eq.symm hcx_le
      dsimp only [] at h_cross
      simp only [h_cross, ↓reduceIte]
      by_cases h_next_eq : ({ x := c.x + -1, y := c.y } : Cell) = x
      · left; exact h_next_eq
      · right
        have h_Dnext := h_eval_targetDist (c.x + -1) c.y (by omega) (by omega) (by omega) (by omega) h_next_eq
        have h_ne_coords := h_cell_ne (c.x + -1) c.y h_next_eq
        rw [h_Dc, h_Dnext]
        refine ⟨by omega, by omega⟩
    · -- both <
      have hcx_le : x.x + 1 ≤ c.x := hcx_lt
      have hcy_le : x.y + 1 ≤ c.y := hcy_lt
      split_ifs with h1 h2
      · by_cases h_next_eq : ({ x := c.x + -1, y := c.y } : Cell) = x
        · left; exact h_next_eq
        · right
          have h_Dnext := h_eval_targetDist (c.x + -1) c.y (by omega) (by omega) (by omega) (by omega) h_next_eq
          have h_ne_coords := h_cell_ne (c.x + -1) c.y h_next_eq
          rw [h_Dc, h_Dnext]
          refine ⟨by omega, by omega⟩
      · by_cases h_next_eq : ({ x := c.x, y := c.y + -1 } : Cell) = x
        · left; exact h_next_eq
        · right
          have h_Dnext := h_eval_targetDist c.x (c.y + -1) (by omega) (by omega) (by omega) (by omega) h_next_eq
          have h_ne_coords := h_cell_ne c.x (c.y + -1) h_next_eq
          rw [h_Dc, h_Dnext]
          refine ⟨by omega, by omega⟩
      · by_cases h_next_eq : ({ x := c.x + -1, y := c.y + -1 } : Cell) = x
        · left; exact h_next_eq
        · right
          have h_Dnext := h_eval_targetDist (c.x + -1) (c.y + -1) (by omega) (by omega) (by omega) (by omega) h_next_eq
          have h_ne_coords := h_cell_ne (c.x + -1) (c.y + -1) h_next_eq
          rw [h_Dc, h_Dnext]
          refine ⟨by omega, by omega⟩


theorem not_endCell_of_dist_pos (A B : Point) (x c : Cell)
    (h_bbox : inBoundingBox x A B = true) :
    let sx : ℤ := if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0
    let sy : ℤ := if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0
    targetDist sx sy x c (floorPoint A) > 0 → (c == floorPoint B) = false := by
  intro sx sy hD
  have h_signs := bbox_signs x A B h_bbox
  unfold targetDist at hD
  dsimp only [] at hD
  split_ifs at hD with hcond
  · cases h_eq : (c == floorPoint B)
    · rfl
    · exfalso
      have hcB : c = floorPoint B := eq_of_beq h_eq
      have hBx : ((floorPoint B).x - x.x) * sx ≥ 0 := h_signs.2.1
      have hBy : ((floorPoint B).y - x.y) * sy ≥ 0 := h_signs.2.2.2
      have h1 : (x.x - c.x) * sx ≤ 0 := by
        rw [hcB]
        have : (x.x - (floorPoint B).x) * sx = -(((floorPoint B).x - x.x) * sx) := by ring
        linarith
      have h2 : (x.y - c.y) * sy ≤ 0 := by
        rw [hcB]
        have : (x.y - (floorPoint B).y) * sy = -(((floorPoint B).y - x.y) * sy) := by ring
        linarith
      have hdx0 : (x.x - c.x) * sx = 0 := by linarith [hcond.2.2.1]
      have hdy0 : (x.y - c.y) * sy = 0 := by linarith [hcond.2.2.2.1]
      rw [hdx0, hdy0] at hD
      revert hD; decide
  · contradiction



theorem targetDist_step_combined (A B : Point) (x c : Cell) (tEnter tExit : ℚ)
    (h_bbox : inBoundingBox x A B = true) (hxA : x ≠ floorPoint A)
    (h_int : cellIntersectionInterval x A B = some (tEnter, tExit))
    (h_enter_lt_exit : tEnter < tExit) :
    let sx : ℤ := if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0
    let sy : ℤ := if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0
    targetDist sx sy x c (floorPoint A) > 0 →
    (rayMarchStep A B (B.x - A.x) (B.y - A.y) sx sy c).2 = false ∧
    ( (rayMarchStep A B (B.x - A.x) (B.y - A.y) sx sy c).1 = x ∨
      (targetDist sx sy x (rayMarchStep A B (B.x - A.x) (B.y - A.y) sx sy c).1 (floorPoint A) < targetDist sx sy x c (floorPoint A) ∧
       0 < targetDist sx sy x (rayMarchStep A B (B.x - A.x) (B.y - A.y) sx sy c).1 (floorPoint A)) ) := by
  intro sx sy hD
  have hD_copy := hD
  unfold targetDist at hD
  dsimp only [] at hD
  split_ifs at hD with hcond
  swap
  · contradiction
  rcases hcond with ⟨h_cA_x, h_cA_y, h_cx, h_cy, hc_x_or, hc_y_or, h_ne⟩
  by_cases hsx : sx = 0
  · have hc_x : c.x = (floorPoint A).x := by
      cases hc_x_or with
      | inl h => exact h
      | inr h => contradiction
    rw [hsx]
    exact targetDist_step_sx_zero A B x c tEnter tExit h_bbox hxA h_int h_enter_lt_exit hsx h_cA_y h_cy hc_x h_ne
  · by_cases hsy : sy = 0
    · have hc_y : c.y = (floorPoint A).y := by
        cases hc_y_or with
        | inl h => exact h
        | inr h => contradiction
      rw [hsy]
      exact targetDist_step_sy_zero A B x c tEnter tExit h_bbox hxA h_int h_enter_lt_exit hsy h_cA_x h_cx hc_y h_ne
    · -- both non-zero
      have hsx_cases : (B.x - A.x > 0 ∧ sx = 1) ∨ (B.x - A.x < 0 ∧ sx = -1) := by
        dsimp [sx] at hsx ⊢
        split_ifs with h1 h2
        · left; exact ⟨h1, rfl⟩
        · right; exact ⟨h2, rfl⟩
        · exfalso; apply hsx; simp only [h1, h2, ↓reduceIte]
      have hsy_cases : (B.y - A.y > 0 ∧ sy = 1) ∨ (B.y - A.y < 0 ∧ sy = -1) := by
        dsimp [sy] at hsy ⊢
        split_ifs with h1 h2
        · left; exact ⟨h1, rfl⟩
        · right; exact ⟨h2, rfl⟩
        · exfalso; apply hsy; simp only [h1, h2, ↓reduceIte]
      rcases hsx_cases with ⟨hdx_pos, hsx1⟩ | ⟨hdx_neg, hsx_neg1⟩
      · rcases hsy_cases with ⟨hdy_pos, hsy1⟩ | ⟨hdy_neg, hsy_neg1⟩
        · -- pos_pos
          rw [hsx1, hsy1]
          rw [hsx1] at h_cA_x h_cx
          rw [hsy1] at h_cA_y h_cy
          exact targetDist_step_pos_pos A B x c tEnter tExit h_bbox hxA h_int h_enter_lt_exit hdx_pos hdy_pos h_cA_x h_cA_y h_cx h_cy h_ne
        · -- pos_neg
          rw [hsx1, hsy_neg1]
          rw [hsx1] at h_cA_x h_cx
          rw [hsy_neg1] at h_cA_y h_cy
          exact targetDist_step_pos_neg A B x c tEnter tExit h_bbox hxA h_int h_enter_lt_exit hdx_pos hdy_neg h_cA_x h_cA_y h_cx h_cy h_ne
      · rcases hsy_cases with ⟨hdy_pos, hsy1⟩ | ⟨hdy_neg, hsy_neg1⟩
        · -- neg_pos
          rw [hsx_neg1, hsy1]
          rw [hsx_neg1] at h_cA_x h_cx
          rw [hsy1] at h_cA_y h_cy
          exact targetDist_step_neg_pos A B x c tEnter tExit h_bbox hxA h_int h_enter_lt_exit hdx_neg hdy_pos h_cA_x h_cA_y h_cx h_cy h_ne
        · -- neg_neg
          rw [hsx_neg1, hsy_neg1]
          rw [hsx_neg1] at h_cA_x h_cx
          rw [hsy_neg1] at h_cA_y h_cy
          exact targetDist_step_neg_neg A B x c tEnter tExit h_bbox hxA h_int h_enter_lt_exit hdx_neg hdy_neg h_cA_x h_cA_y h_cx h_cy h_ne

theorem rayMarch_completeness (A B : Point) (x : Cell)
    (hxA : x ≠ floorPoint A) (_hxB : x ≠ floorPoint B)
    (h_bbox : inBoundingBox x A B = true)
    (h_int : ∃ tEnter tExit, cellIntersectionInterval x A B = some (tEnter, tExit) ∧ tEnter < tExit) :
    x ∈ rayMarch (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 2)
      A B (B.x - A.x) (B.y - A.y)
      (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0)
      (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0)
      (floorPoint B) (floorPoint A) [] := by
  rcases h_int with ⟨tEnter, tExit, h_inter, h_enter_lt_exit⟩
  let sx : ℤ := if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0
  let sy : ℤ := if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0
  let fuel : ℕ := ((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 2
  let D := fun c => targetDist sx sy x c (floorPoint A)
  have h_step : ∀ c, D c > 0 →
      (c == floorPoint B) = false ∧
      (rayMarchStep A B (B.x - A.x) (B.y - A.y) sx sy c).2 = false ∧
      ( (rayMarchStep A B (B.x - A.x) (B.y - A.y) sx sy c).1 = x ∨
        (D (rayMarchStep A B (B.x - A.x) (B.y - A.y) sx sy c).1 < D c ∧
         D (rayMarchStep A B (B.x - A.x) (B.y - A.y) sx sy c).1 > 0) ) := by
    intro c hcD
    refine ⟨not_endCell_of_dist_pos A B x c h_bbox hcD, ?_⟩
    exact targetDist_step_combined A B x c tEnter tExit h_bbox hxA h_inter h_enter_lt_exit hcD
  have h_start_pos : D (floorPoint A) > 0 := targetDist_start_pos A B x h_bbox hxA
  have h_start_le : D (floorPoint A) ≤ fuel := targetDist_start_le A B x h_bbox
  exact rayMarch_reaches_target fuel A B (B.x - A.x) (B.y - A.y) sx sy (floorPoint B) x D h_step (floorPoint A) h_start_pos h_start_le




end Geometry
