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
import Geometry.LineSegment
import GeometryDefs
import proofs.Interval
import proofs.Soundness
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith

namespace Geometry

/--
Floored start point of a segment lies within the closed starting cell.
-/
theorem floorPoint_touches (A B : Point) : CellTouchesSegment (floorPoint A) A B := by
  refine ⟨A, PointOnSegment.start rfl, ?_, ?_, ?_, ?_⟩
  · exact Rat.floor_le A.x
  · exact le_of_lt (Rat.lt_floor_add_one A.x)
  · exact Rat.floor_le A.y
  · exact le_of_lt (Rat.lt_floor_add_one A.y)

/--
Floored end point of a segment lies within the closed ending cell.
-/
theorem floorPoint_end_touches (A B : Point) : CellTouchesSegment (floorPoint B) A B := by
  refine ⟨B, PointOnSegment.ptEnd rfl, ?_, ?_, ?_, ?_⟩
  · exact Rat.floor_le B.x
  · exact le_of_lt (Rat.lt_floor_add_one B.x)
  · exact Rat.floor_le B.y
  · exact le_of_lt (Rat.lt_floor_add_one B.y)

/--
A cell whose open interior the segment crosses touches the segment.
-/
theorem cellCrossedBySegment_touches_segment (c : Cell) (A B : Point)
    (h_cross : CellCrossedBySegment c A B) : CellTouchesSegment c A B := by
  rcases h_cross with ⟨p, h_seg, hx0, hx1, hy0, hy1⟩
  exact ⟨p, h_seg, le_of_lt hx0, le_of_lt hx1, le_of_lt hy0, le_of_lt hy1⟩

theorem cellIntersectionInterval_eq_none_of_dx_zero_out
    (c : Cell) (A B : Point) (hdx : B.x - A.x = 0)
    (h_out : A.x < ofInt c.x ∨ ofInt (c.x + 1) < A.x) :
    cellIntersectionInterval c A B = none := by
  unfold cellIntersectionInterval
  dsimp only []
  have h_eq : ((B.x - A.x) == 0) = true := by rw [beq_iff_eq, hdx]
  simp only [h_eq, ↓reduceIte]
  have h_or : (A.x < ofInt c.x || ofInt (c.x + 1) < A.x) = true := by
    rw [Bool.or_eq_true, decide_eq_true_iff, decide_eq_true_iff]
    exact h_out
  simp only [h_or, ↓reduceIte]
  have h_not : ¬ (max 0 (max 1 (if B.y - A.y == 0 then if A.y < ofInt c.y || A.y > ofInt (c.y + 1) then (1, 0) else (0, 1) else if B.y - A.y > 0 then ((ofInt c.y - A.y) / (B.y - A.y), (ofInt (c.y + 1) - A.y) / (B.y - A.y)) else ((ofInt (c.y + 1) - A.y) / (B.y - A.y), (ofInt c.y - A.y) / (B.y - A.y))).1) ≤
    min 1 (min 0 (if B.y - A.y == 0 then if A.y < ofInt c.y || A.y > ofInt (c.y + 1) then (1, 0) else (0, 1) else if B.y - A.y > 0 then ((ofInt c.y - A.y) / (B.y - A.y), (ofInt (c.y + 1) - A.y) / (B.y - A.y)) else ((ofInt (c.y + 1) - A.y) / (B.y - A.y), (ofInt c.y - A.y) / (B.y - A.y))).2)) := by
    intro h_le
    generalize (if B.y - A.y == 0 then if A.y < ofInt c.y || A.y > ofInt (c.y + 1) then (1, 0) else (0, 1) else if B.y - A.y > 0 then ((ofInt c.y - A.y) / (B.y - A.y), (ofInt (c.y + 1) - A.y) / (B.y - A.y)) else ((ofInt (c.y + 1) - A.y) / (B.y - A.y), (ofInt c.y - A.y) / (B.y - A.y))) = ty at h_le
    have h1 : (1 : ℚ) ≤ max 0 (max 1 ty.1) := le_trans (le_max_left 1 ty.1) (le_max_right 0 (max 1 ty.1))
    have h2 : min 1 (min 0 ty.2) ≤ (0 : ℚ) := le_trans (min_le_right 1 (min 0 ty.2)) (min_le_left 0 ty.2)
    linarith
  exact ite_eq_right h_not

theorem interval_dx_zero (c : Cell) (A B : Point) (tEnter tExit : ℚ)
    (h : cellIntersectionInterval c A B = some (tEnter, tExit))
    (_h_le : tEnter ≤ tExit)
    (hdx : B.x - A.x = 0) :
    ofInt c.x ≤ A.x ∧ A.x ≤ ofInt (c.x + 1) := by
  by_contra h_contra
  have h_out : A.x < ofInt c.x ∨ ofInt (c.x + 1) < A.x := by
    by_cases h1 : A.x < ofInt c.x
    · exact Or.inl h1
    · have h1' : ofInt c.x ≤ A.x := by linarith
      have h2 : ofInt (c.x + 1) < A.x := by
        by_contra h2'
        have h2'' : A.x ≤ ofInt (c.x + 1) := by linarith
        exact h_contra ⟨h1', h2''⟩
      exact Or.inr h2
  have h_none := cellIntersectionInterval_eq_none_of_dx_zero_out c A B hdx h_out
  rw [h_none] at h
  contradiction

theorem cellIntersectionInterval_eq_none_of_dy_zero_out
    (c : Cell) (A B : Point) (hdy : B.y - A.y = 0)
    (h_out : A.y < ofInt c.y ∨ ofInt (c.y + 1) < A.y) :
    cellIntersectionInterval c A B = none := by
  unfold cellIntersectionInterval
  dsimp only []
  have h_eq : ((B.y - A.y) == 0) = true := by rw [beq_iff_eq, hdy]
  simp only [h_eq, ↓reduceIte]
  have h_or : (A.y < ofInt c.y || ofInt (c.y + 1) < A.y) = true := by
    rw [Bool.or_eq_true, decide_eq_true_iff, decide_eq_true_iff]
    exact h_out
  simp only [h_or, ↓reduceIte]
  have h_not : ¬ (max 0 (max (if B.x - A.x == 0 then if A.x < ofInt c.x || A.x > ofInt (c.x + 1) then (1, 0) else (0, 1) else if B.x - A.x > 0 then ((ofInt c.x - A.x) / (B.x - A.x), (ofInt (c.x + 1) - A.x) / (B.x - A.x)) else ((ofInt (c.x + 1) - A.x) / (B.x - A.x), (ofInt c.x - A.x) / (B.x - A.x))).1 1) ≤
    min 1 (min (if B.x - A.x == 0 then if A.x < ofInt c.x || A.x > ofInt (c.x + 1) then (1, 0) else (0, 1) else if B.x - A.x > 0 then ((ofInt c.x - A.x) / (B.x - A.x), (ofInt (c.x + 1) - A.x) / (B.x - A.x)) else ((ofInt (c.x + 1) - A.x) / (B.x - A.x), (ofInt c.x - A.x) / (B.x - A.x))).2 0)) := by
    intro h_le
    generalize (if B.x - A.x == 0 then if A.x < ofInt c.x || A.x > ofInt (c.x + 1) then (1, 0) else (0, 1) else if B.x - A.x > 0 then ((ofInt c.x - A.x) / (B.x - A.x), (ofInt (c.x + 1) - A.x) / (B.x - A.x)) else ((ofInt (c.x + 1) - A.x) / (B.x - A.x), (ofInt c.x - A.x) / (B.x - A.x))) = tx at h_le
    have h1 : (1 : ℚ) ≤ max 0 (max tx.1 1) := le_trans (le_max_right tx.1 1) (le_max_right 0 (max tx.1 1))
    have h2 : min 1 (min tx.2 0) ≤ (0 : ℚ) := le_trans (min_le_right 1 (min tx.2 0)) (min_le_right tx.2 0)
    linarith
  exact ite_eq_right h_not

theorem interval_dy_zero (c : Cell) (A B : Point) (tEnter tExit : ℚ)
    (h : cellIntersectionInterval c A B = some (tEnter, tExit))
    (_h_le : tEnter ≤ tExit)
    (hdy : B.y - A.y = 0) :
    ofInt c.y ≤ A.y ∧ A.y ≤ ofInt (c.y + 1) := by
  by_contra h_contra
  have h_out : A.y < ofInt c.y ∨ ofInt (c.y + 1) < A.y := by
    by_cases h1 : A.y < ofInt c.y
    · exact Or.inl h1
    · have h1' : ofInt c.y ≤ A.y := by linarith
      have h2 : ofInt (c.y + 1) < A.y := by
        by_contra h2'
        have h2'' : A.y ≤ ofInt (c.y + 1) := by linarith
        exact h_contra ⟨h1', h2''⟩
      exact Or.inr h2
  have h_none := cellIntersectionInterval_eq_none_of_dy_zero_out c A B hdy h_out
  rw [h_none] at h
  contradiction

/--
Continuous Soundness: Every discrete cell in the idealized intersection output touches
the continuous closed line segment in [c.x, c.x + 1] × [c.y, c.y + 1].
-/
theorem cellIntersectionsSegment_touches_segment_Impl (A B : Point) (c : Cell)
    (hc : c ∈ cellIntersectionsSegment A B) : CellTouchesSegment c A B := by
  have h_cases : c = floorPoint A ∨ c = floorPoint B ∨
      ∃ tEnter tExit, cellIntersectionInterval c A B = some (tEnter, tExit) := by
    by_cases h_same : floorPoint A = floorPoint B
    · rw [cellIntersectionsSegment_of_same A B h_same] at hc
      simp only [List.mem_singleton] at hc
      left; exact hc
    · rw [mem_cellIntersectionsSegment_of_ne A B c h_same] at hc
      rcases hc with hc1 | hc2 | hc3
      · left; exact hc1
      · right; left; exact hc2
      · right; right
        have ⟨_, tEnter, tExit, h_int, _⟩ := rayMarch_soundness A B c hc3
        exact ⟨tEnter, tExit, h_int⟩
  rcases h_cases with hcA | hcB | ⟨tEnter, tExit, h_int⟩
  · rw [hcA]; exact floorPoint_touches A B
  · rw [hcB]; exact floorPoint_end_touches A B
  · have h_le := cellIntersectionInterval_le c A B tEnter tExit h_int
    have h_bnd := interval_enter_exit_le_one c A B tEnter tExit h_int
    have ht0 : 0 ≤ tEnter := h_bnd.1
    have ht1 : tEnter ≤ 1 := le_trans h_le h_bnd.2
    let p : Point := ⟨A.x + tEnter * (B.x - A.x), A.y + tEnter * (B.y - A.y)⟩
    refine ⟨p, PointOnSegment.interior tEnter ht0 ht1 rfl rfl, ?_, ?_, ?_, ?_⟩
    · -- ofInt c.x ≤ p.x
      by_cases hdx_pos : 0 < B.x - A.x
      · have hdx_prop := interval_dx_pos c A B tEnter tExit h_int hdx_pos
        have h_mul : ofInt c.x - A.x ≤ tEnter * (B.x - A.x) := by
          have h_div := hdx_prop.1
          rwa [div_le_iff₀ hdx_pos] at h_div
        dsimp [p]; linarith
      · by_cases hdx_neg : B.x - A.x < 0
        · have hdx_prop := interval_dx_neg c A B tEnter tExit h_int hdx_neg
          have h_mul : ofInt c.x - A.x ≤ tEnter * (B.x - A.x) := by
            have h_div := le_trans h_le hdx_prop.2
            rwa [le_div_iff_of_neg hdx_neg] at h_div
          dsimp [p]; linarith
        · have hdx_zero : B.x - A.x = 0 := by linarith
          have ⟨hx1, _⟩ := interval_dx_zero c A B tEnter tExit h_int h_le hdx_zero
          dsimp [p]; rw [hdx_zero, mul_zero, add_zero]; exact hx1
    · -- p.x ≤ ofInt (c.x + 1)
      by_cases hdx_pos : 0 < B.x - A.x
      · have hdx_prop := interval_dx_pos c A B tEnter tExit h_int hdx_pos
        have h_mul : tEnter * (B.x - A.x) ≤ ofInt (c.x + 1) - A.x := by
          have h_div := le_trans h_le hdx_prop.2
          rwa [le_div_iff₀ hdx_pos] at h_div
        dsimp [p]; linarith
      · by_cases hdx_neg : B.x - A.x < 0
        · have hdx_prop := interval_dx_neg c A B tEnter tExit h_int hdx_neg
          have h_mul : tEnter * (B.x - A.x) ≤ ofInt (c.x + 1) - A.x := by
            have h_div := hdx_prop.1
            rwa [div_le_iff_of_neg hdx_neg] at h_div
          dsimp [p]; linarith
        · have hdx_zero : B.x - A.x = 0 := by linarith
          have ⟨_, hx2⟩ := interval_dx_zero c A B tEnter tExit h_int h_le hdx_zero
          dsimp [p]; rw [hdx_zero, mul_zero, add_zero]; exact hx2
    · -- ofInt c.y ≤ p.y
      by_cases hdy_pos : 0 < B.y - A.y
      · have hdy_prop := interval_dy_pos c A B tEnter tExit h_int hdy_pos
        have h_mul : ofInt c.y - A.y ≤ tEnter * (B.y - A.y) := by
          have h_div := hdy_prop.1
          rwa [div_le_iff₀ hdy_pos] at h_div
        dsimp [p]; linarith
      · by_cases hdy_neg : B.y - A.y < 0
        · have hdy_prop := interval_dy_neg c A B tEnter tExit h_int hdy_neg
          have h_mul : ofInt c.y - A.y ≤ tEnter * (B.y - A.y) := by
            have h_div := le_trans h_le hdy_prop.2
            rwa [le_div_iff_of_neg hdy_neg] at h_div
          dsimp [p]; linarith
        · have hdy_zero : B.y - A.y = 0 := by linarith
          have ⟨hy1, _⟩ := interval_dy_zero c A B tEnter tExit h_int h_le hdy_zero
          dsimp [p]; rw [hdy_zero, mul_zero, add_zero]; exact hy1
    · -- p.y ≤ ofInt (c.y + 1)
      by_cases hdy_pos : 0 < B.y - A.y
      · have hdy_prop := interval_dy_pos c A B tEnter tExit h_int hdy_pos
        have h_mul : tEnter * (B.y - A.y) ≤ ofInt (c.y + 1) - A.y := by
          have h_div := le_trans h_le hdy_prop.2
          rwa [le_div_iff₀ hdy_pos] at h_div
        dsimp [p]; linarith
      · by_cases hdy_neg : B.y - A.y < 0
        · have hdy_prop := interval_dy_neg c A B tEnter tExit h_int hdy_neg
          have h_mul : tEnter * (B.y - A.y) ≤ ofInt (c.y + 1) - A.y := by
            have h_div := hdy_prop.1
            rwa [div_le_iff_of_neg hdy_neg] at h_div
          dsimp [p]; linarith
        · have hdy_zero : B.y - A.y = 0 := by linarith
          have ⟨_, hy2⟩ := interval_dy_zero c A B tEnter tExit h_int h_le hdy_zero
          dsimp [p]; rw [hdy_zero, mul_zero, add_zero]; exact hy2

/--
Endpoints inclusion: Endpoint cells are active intersected cells and belong to the intersection list.
-/
theorem cellIntersectionsSegment_contains_endpoints_Impl (A B : Point) :
    floorPoint A ∈ cellIntersectionsSegment A B ∧ floorPoint B ∈ cellIntersectionsSegment A B := by
  constructor
  · by_cases h : floorPoint A = floorPoint B
    · rw [cellIntersectionsSegment_of_same A B h]
      simp
    · rw [mem_cellIntersectionsSegment_of_ne A B _ h]
      left; rfl
  · by_cases h : floorPoint A = floorPoint B
    · rw [cellIntersectionsSegment_of_same A B h]
      simp [h]
    · rw [mem_cellIntersectionsSegment_of_ne A B _ h]
      right; left; rfl

/-- The parameter interval of one axis in `cellIntersectionInterval`. -/
def axisInterval (a d lo hi : ℚ) : ℚ × ℚ :=
  if d == 0 then (if a < lo || a > hi then (1, 0) else (0, 1))
  else if d > 0 then ((lo - a) / d, (hi - a) / d) else ((hi - a) / d, (lo - a) / d)

theorem cellIntersectionInterval_eq_axes (c : Cell) (A B : Point) :
    cellIntersectionInterval c A B =
      let px := axisInterval A.x (B.x - A.x) (ofInt c.x) (ofInt (c.x + 1))
      let py := axisInterval A.y (B.y - A.y) (ofInt c.y) (ofInt (c.y + 1))
      if max 0 (max px.1 py.1) ≤ min 1 (min px.2 py.2) then
        some (max 0 (max px.1 py.1), min 1 (min px.2 py.2))
      else none := by
  rfl

theorem axisInterval_bounds (a d lo hi t : ℚ) (ht0 : 0 < t) (ht1 : t < 1)
    (hlo : lo < a + t * d) (hhi : a + t * d < hi) :
    (axisInterval a d lo hi).1 < t ∧ t < (axisInterval a d lo hi).2 := by
  unfold axisInterval
  by_cases hd : d = 0
  · subst hd
    have h1 : ¬ (a < lo) := by simp at hlo; linarith
    have h2 : ¬ (a > hi) := by simp at hhi; linarith
    simp [h1, h2, ht0, ht1]
  · have hd' : (d == 0) = false := by simpa using hd
    rcases lt_or_gt_of_ne hd with hneg | hpos
    · have hng : ¬ d > 0 := by linarith
      simp only [hd', hng, Bool.false_eq_true, ↓reduceIte]
      constructor
      · rw [div_lt_iff_of_neg hneg]; linarith
      · rw [lt_div_iff_of_neg hneg]; linarith
    · simp only [hd', hpos, Bool.false_eq_true, ↓reduceIte]
      constructor
      · rw [div_lt_iff₀ hpos]; linarith
      · rw [lt_div_iff₀ hpos]; linarith

theorem interval_lt_of_interior (c : Cell) (A B : Point) (t : ℚ) (ht0 : 0 < t) (ht1 : t < 1)
    (hint : InInteriorCell c ⟨A.x + t * (B.x - A.x), A.y + t * (B.y - A.y)⟩) :
    ∃ tEnter tExit, cellIntersectionInterval c A B = some (tEnter, tExit) ∧ tEnter < tExit := by
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hint
  obtain ⟨hX0, hX1⟩ := axisInterval_bounds A.x (B.x - A.x) (ofInt c.x) (ofInt (c.x + 1)) t ht0 ht1 hx0 hx1
  obtain ⟨hY0, hY1⟩ := axisInterval_bounds A.y (B.y - A.y) (ofInt c.y) (ofInt (c.y + 1)) t ht0 ht1 hy0 hy1
  rw [cellIntersectionInterval_eq_axes]
  have hlt : max 0 (max (axisInterval A.x (B.x - A.x) (ofInt c.x) (ofInt (c.x + 1))).1
      (axisInterval A.y (B.y - A.y) (ofInt c.y) (ofInt (c.y + 1))).1) <
      min 1 (min (axisInterval A.x (B.x - A.x) (ofInt c.x) (ofInt (c.x + 1))).2
      (axisInterval A.y (B.y - A.y) (ofInt c.y) (ofInt (c.y + 1))).2) :=
    lt_trans (max_lt ht0 (max_lt hX0 hY0)) (lt_min ht1 (lt_min hX1 hY1))
  exact ⟨_, _, by simp only [le_of_lt hlt, ↓reduceIte], hlt⟩

/-- A point strictly inside cell `c` floors to `c`. -/
theorem floorPoint_of_interior {c : Cell} {p : Point} (h : InInteriorCell c p) : floorPoint p = c := by
  obtain ⟨hx0, hx1, hy0, hy1⟩ := h
  have hx : Rat.floor p.x = c.x :=
    le_antisymm (Int.lt_add_one_iff.mp (floor_lt_of_lt (c.x + 1) p.x hx1))
      (int_le_floor_of_lt c.x p.x hx0)
  have hy : Rat.floor p.y = c.y :=
    le_antisymm (Int.lt_add_one_iff.mp (floor_lt_of_lt (c.y + 1) p.y hy1))
      (int_le_floor_of_lt c.y p.y hy0)
  exact cell_ext hx hy

/-- A point of the segment lies between the endpoints, so its floor lies in the bounding box. -/
theorem floor_between (a b t : ℚ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    min (Rat.floor a) (Rat.floor b) ≤ Rat.floor (a + t * (b - a)) ∧
      Rat.floor (a + t * (b - a)) ≤ max (Rat.floor a) (Rat.floor b) := by
  rcases le_total a b with hab | hba
  · have h1 : a ≤ a + t * (b - a) := by nlinarith
    have h2 : a + t * (b - a) ≤ b := by nlinarith
    have := rat_floor_mono h1
    have := rat_floor_mono h2
    omega
  · have h1 : b ≤ a + t * (b - a) := by nlinarith
    have h2 : a + t * (b - a) ≤ a := by nlinarith
    have := rat_floor_mono h1
    have := rat_floor_mono h2
    omega

end Geometry
