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
import Geometry.FloatSemantics
import Geometry.LineSegment
import Geometry.Interval
import Geometry.RayMarchStep
import Mathlib.Tactic.Linarith

namespace Geometry

/--
The next cell produced by `rayMarchStepFloat` is always one of the 4 candidate transitions:
current cell, stepX neighbor, stepY neighbor, or diagonal step.
-/
theorem rayMarchStepFloat_candidates (start : Point32) (dx dy : Binary32) (stepX stepY : Int) (c : Cell) :
    (rayMarchStepFloat start dx dy stepX stepY c).1 ∈ [
      c,
      ⟨c.x + stepX, c.y⟩,
      ⟨c.x, c.y + stepY⟩,
      ⟨c.x + stepX, c.y + stepY⟩
    ] := by
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

/--
Every step taken in floating-point raymarching changes coordinates by at most 1 in Chebyshev distance
relative to the current cell, ensuring path continuity.
-/
theorem chebyshevDistance_stepFloat_le_one (start : Point32) (dx dy : Binary32) (stepX stepY : Int)
    (hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1) (hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1) (c : Cell) :
    chebyshevDistance c (rayMarchStepFloat start dx dy stepX stepY c).1 ≤ 1 := by
  have hc := rayMarchStepFloat_candidates start dx dy stepX stepY c
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with h | h | h | h
  · rw [h]
    unfold chebyshevDistance
    simp
  · rw [h]
    unfold chebyshevDistance
    simp only [sub_self, Int.natAbs_zero]
    rcases hX with rfl | rfl | rfl <;> omega
  · rw [h]
    unfold chebyshevDistance
    simp only [sub_self, Int.natAbs_zero]
    rcases hY with rfl | rfl | rfl <;> omega
  · rw [h]
    have hx : c.x - (⟨c.x + stepX, c.y + stepY⟩ : Cell).x = -stepX := by simp
    have hy : c.y - (⟨c.x + stepX, c.y + stepY⟩ : Cell).y = -stepY := by simp
    unfold chebyshevDistance
    rw [hx, hy]
    rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl <;> omega

/--
Helper lemma bounding Chebyshev distance between any two candidate cell displacements.
-/
theorem chebyshevDistance_candidate_cells_le_one (c : Cell) (stepX stepY : Int)
    (hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1) (hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1)
    (dx1 dy1 dx2 dy2 : Int)
    (hx1 : dx1 = 0 ∨ dx1 = stepX) (hy1 : dy1 = 0 ∨ dy1 = stepY)
    (hx2 : dx2 = 0 ∨ dx2 = stepX) (hy2 : dy2 = 0 ∨ dy2 = stepY) :
    chebyshevDistance ⟨c.x + dx1, c.y + dy1⟩ ⟨c.x + dx2, c.y + dy2⟩ ≤ 1 := by
  have hx : (⟨c.x + dx1, c.y + dy1⟩ : Cell).x - (⟨c.x + dx2, c.y + dy2⟩ : Cell).x = dx1 - dx2 := by simp
  have hy : (⟨c.x + dx1, c.y + dy1⟩ : Cell).y - (⟨c.x + dx2, c.y + dy2⟩ : Cell).y = dy1 - dy2 := by simp
  unfold chebyshevDistance
  rw [hx, hy]
  rcases hx1 with rfl | rfl <;>
    rcases hx2 with rfl | rfl <;>
    rcases hy1 with rfl | rfl <;>
    rcases hy2 with rfl | rfl <;>
    rcases hX with rfl | rfl | rfl <;>
    rcases hY with rfl | rfl | rfl <;>
    omega

/--
Symmetry of discrete Chebyshev distance.
-/
theorem chebyshevDistance_symm (c1 c2 : Cell) :
    chebyshevDistance c1 c2 = chebyshevDistance c2 c1 := by
  unfold chebyshevDistance
  rw [show (c1.x - c2.x).natAbs = (c2.x - c1.x).natAbs by omega,
      show (c1.y - c2.y).natAbs = (c2.y - c1.y).natAbs by omega]

/--
The next cell produced by idealized rational `rayMarchStep` is always one of the 4 candidate transitions.
-/
theorem rayMarchStep_candidates (start ptEnd : Point) (dx dy : ℚ) (stepX stepY : ℤ) (c : Cell) :
    (rayMarchStep start ptEnd dx dy stepX stepY c).1 ∈ [
      c,
      ⟨c.x + stepX, c.y⟩,
      ⟨c.x, c.y + stepY⟩,
      ⟨c.x + stepX, c.y + stepY⟩
    ] := by
  have h := rayMarchStep_mem start ptEnd dx dy stepX stepY c
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  rcases h with h | h | h | h
  · left; rw [h]
  · right; left; rw [h]
  · right; right; left; rw [h]
  · right; right; right; rw [h]

/--
Every step taken in idealized rational raymarching changes coordinates by at most 1 in Chebyshev distance.
-/
theorem chebyshevDistance_step_le_one (start ptEnd : Point) (dx dy : ℚ) (stepX stepY : ℤ)
    (hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1) (hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1) (c : Cell) :
    chebyshevDistance c (rayMarchStep start ptEnd dx dy stepX stepY c).1 ≤ 1 := by
  have hc := rayMarchStep_candidates start ptEnd dx dy stepX stepY c
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with h | h | h | h
  · rw [h]
    unfold chebyshevDistance
    simp
  · rw [h]
    unfold chebyshevDistance
    simp only [sub_self, Int.natAbs_zero]
    rcases hX with rfl | rfl | rfl <;> omega
  · rw [h]
    unfold chebyshevDistance
    simp only [sub_self, Int.natAbs_zero]
    rcases hY with rfl | rfl | rfl <;> omega
  · rw [h]
    have hx : c.x - (⟨c.x + stepX, c.y + stepY⟩ : Cell).x = -stepX := by simp
    have hy : c.y - (⟨c.x + stepX, c.y + stepY⟩ : Cell).y = -stepY := by simp
    unfold chebyshevDistance
    rw [hx, hy]
    rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl <;> omega

/--
Chebyshev distance between the next cell chosen by floating-point raymarching
and idealized rational raymarching from the same cell is always at most 1.
-/
theorem rayMarchStepFloat_near_rayMarchStep (start : Point32) (ptEnd : Point)
    (dx dy : Binary32) (dxQ dyQ : ℚ) (stepX stepY : ℤ)
    (hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1) (hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1) (c : Cell) :
    chebyshevDistance
      (rayMarchStepFloat start dx dy stepX stepY c).1
      (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 ≤ 1 := by
  have hf := rayMarchStepFloat_candidates start dx dy stepX stepY c
  have hi := rayMarchStep_candidates start.toPoint ptEnd dxQ dyQ stepX stepY c
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf hi
  rcases hf with hf | hf | hf | hf <;>
  rcases hi with hi | hi | hi | hi <;>
  rw [hf, hi]
  · rw [chebyshevDistance_self]; omega
  · unfold chebyshevDistance; dsimp only []
    rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl <;> omega
  · unfold chebyshevDistance; dsimp only []
    rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl <;> omega
  · unfold chebyshevDistance; dsimp only []
    rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl <;> omega
  · unfold chebyshevDistance; dsimp only []
    rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl <;> omega
  · rw [chebyshevDistance_self]; omega
  · unfold chebyshevDistance; dsimp only []
    rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl <;> omega
  · unfold chebyshevDistance; dsimp only []
    rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl <;> omega
  · unfold chebyshevDistance; dsimp only []
    rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl <;> omega
  · unfold chebyshevDistance; dsimp only []
    rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl <;> omega
  · rw [chebyshevDistance_self]; omega
  · unfold chebyshevDistance; dsimp only []
    rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl <;> omega
  · unfold chebyshevDistance; dsimp only []
    rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl <;> omega
  · unfold chebyshevDistance; dsimp only []
    rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl <;> omega
  · unfold chebyshevDistance; dsimp only []
    rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl <;> omega
  · rw [chebyshevDistance_self]; omega

/--
Accumulator append property for rayMarchFloat.
-/
theorem rayMarchFloat_acc (fuel : ℕ) (start : Point32) (dx dy : Binary32) (stepX stepY : ℤ)
    (endCell current : Cell) (acc : List Cell) :
    rayMarchFloat fuel start dx dy stepX stepY endCell current acc =
      acc ++ rayMarchFloat fuel start dx dy stepX stepY endCell current [] := by
  induction fuel generalizing current acc with
  | zero =>
    unfold rayMarchFloat
    simp
  | succ fuel ih =>
    unfold rayMarchFloat
    dsimp
    cases hc : (current == endCell)
    · dsimp
      cases hd : (rayMarchStepFloat start dx dy stepX stepY current).snd
      · dsimp
        rw [ih _ (acc ++ [(rayMarchStepFloat start dx dy stepX stepY current).fst])]
        rw [ih _ [(rayMarchStepFloat start dx dy stepX stepY current).fst]]
        simp [List.append_assoc]
      · simp
    · simp

/--
Membership in rayMarchFloat with accumulator splits into accumulator or empty accumulator.
-/
theorem mem_rayMarchFloat (fuel : ℕ) (start : Point32) (dx dy : Binary32) (stepX stepY : ℤ)
    (endCell current : Cell) (acc : List Cell) (c : Cell) :
    c ∈ rayMarchFloat fuel start dx dy stepX stepY endCell current acc ↔
      c ∈ acc ∨ c ∈ rayMarchFloat fuel start dx dy stepX stepY endCell current [] := by
  rw [rayMarchFloat_acc]
  simp

/--
Unfolding step equation for rayMarchFloat with empty accumulator.
-/
theorem rayMarchFloat_succ (fuel : ℕ) (start : Point32) (dx dy : Binary32) (stepX stepY : ℤ)
    (endCell current : Cell) :
    rayMarchFloat (fuel + 1) start dx dy stepX stepY endCell current [] =
      if current == endCell then []
      else
        let (nextCell, done) := rayMarchStepFloat start dx dy stepX stepY current
        if done then []
        else nextCell :: rayMarchFloat fuel start dx dy stepX stepY endCell nextCell [] := by
  conv =>
    lhs
    rw [rayMarchFloat]
  dsimp
  cases hc : (current == endCell)
  · dsimp
    cases hd : (rayMarchStepFloat start dx dy stepX stepY current).snd
    · dsimp
      rw [rayMarchFloat_acc]
      rfl
    · rfl
  · rfl

/--
Proves that every cell visited by floating-point raymarching is within Chebyshev distance at most 1
of some cell in the deduplicated ideal raymarching output (including endpoints) when step transitions agree.
-/
theorem rayMarchFloat_near_rayMarch_endpoints (fuel : ℕ) (start : Point32) (ptEnd : Point)
    (dx dy : Binary32) (dxQ dyQ : ℚ) (stepX stepY : ℤ) (endCell current : Cell)
    (hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1) (hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1)
    (h_step : ∀ c, (rayMarchStepFloat start dx dy stepX stepY c).1 =
      (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1)
    (h_done : ∀ c, (rayMarchStepFloat start dx dy stepX stepY c).2 =
      (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).2) :
    ∀ c1 ∈ rayMarchFloat fuel start dx dy stepX stepY endCell current [],
      ∃ c2 ∈ dedupCells ([current, endCell] ++
        rayMarch fuel start.toPoint ptEnd dxQ dyQ stepX stepY endCell current []),
        chebyshevDistance c1 c2 ≤ 1 := by
  induction fuel generalizing current with
  | zero =>
    intro c1 hc1
    unfold rayMarchFloat at hc1
    cases hc1
  | succ fuel ih =>
    intro c1 hc1
    rw [rayMarchFloat_succ] at hc1
    dsimp only [] at hc1
    rw [rayMarch_succ]
    dsimp only []
    split_ifs at hc1 with hc hd
    · cases hc1
    · cases hc1
    · have h_not_end : (current == endCell) = false := by
        cases h : (current == endCell)
        · rfl
        · exfalso; apply hc; exact h
      rw [h_not_end]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hd_ideal : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY current).2 = false := by
        rw [← h_done]
        cases h : (rayMarchStepFloat start dx dy stepX stepY current).2
        · rfl
        · exfalso; apply hd; exact h
      rw [hd_ideal]
      simp only [Bool.false_eq_true, ↓reduceIte]
      simp only [List.mem_cons] at hc1
      have h_eq_step := h_step current
      rcases hc1 with rfl | htail
      · refine ⟨current, ?_, ?_⟩
        · rw [mem_dedupCells]
          simp only [List.mem_append, List.mem_cons, true_or]
        · rw [chebyshevDistance_symm]
          exact chebyshevDistance_stepFloat_le_one start dx dy stepX stepY hX hY current
      · have h_rec := ih (rayMarchStepFloat start dx dy stepX stepY current).1 c1 htail
        rcases h_rec with ⟨c2, hc2, hd2⟩
        refine ⟨c2, ?_, hd2⟩
        rw [mem_dedupCells] at hc2 ⊢
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc2 ⊢
        rcases hc2 with (rfl | rfl) | hmem
        · exact Or.inr (Or.inl (by rw [← h_eq_step]))
        · exact Or.inl (Or.inr rfl)
        · exact Or.inr (Or.inr (by rw [← h_eq_step]; exact hmem))

/--
Proves that every cell visited by ideal rational raymarching is within Chebyshev distance at most 1
of some cell in the deduplicated floating-point raymarching output (including endpoints) when step transitions agree.
-/
theorem rayMarch_near_rayMarchFloat_endpoints (fuel : ℕ) (start : Point32) (ptEnd : Point)
    (dx dy : Binary32) (dxQ dyQ : ℚ) (stepX stepY : ℤ) (endCell current : Cell)
    (hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1) (hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1)
    (h_step : ∀ c, (rayMarchStepFloat start dx dy stepX stepY c).1 =
      (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1)
    (h_done : ∀ c, (rayMarchStepFloat start dx dy stepX stepY c).2 =
      (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).2) :
    ∀ c2 ∈ rayMarch fuel start.toPoint ptEnd dxQ dyQ stepX stepY endCell current [],
      ∃ c1 ∈ dedupCells ([current, endCell] ++
        rayMarchFloat fuel start dx dy stepX stepY endCell current []),
        chebyshevDistance c1 c2 ≤ 1 := by
  induction fuel generalizing current with
  | zero =>
    intro c2 hc2
    unfold rayMarch at hc2
    cases hc2
  | succ fuel ih =>
    intro c2 hc2
    rw [rayMarchFloat_succ]
    dsimp only []
    rw [rayMarch_succ] at hc2
    dsimp only [] at hc2
    split_ifs at hc2 with hc hd
    · cases hc2
    · cases hc2
    · have h_not_end : (current == endCell) = false := by
        cases h : (current == endCell)
        · rfl
        · exfalso; apply hc; exact h
      rw [h_not_end]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hd_float : (rayMarchStepFloat start dx dy stepX stepY current).2 = false := by
        rw [h_done]
        cases h : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY current).2
        · rfl
        · exfalso; apply hd; exact h
      rw [hd_float]
      simp only [Bool.false_eq_true, ↓reduceIte]
      simp only [List.mem_cons] at hc2
      have h_eq_step := h_step current
      rcases hc2 with rfl | htail
      · refine ⟨current, ?_, ?_⟩
        · rw [mem_dedupCells]
          simp only [List.mem_append, List.mem_cons, true_or]
        · exact chebyshevDistance_step_le_one start.toPoint ptEnd dxQ dyQ stepX stepY hX hY current
      · have h_rec := ih (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY current).1 c2 htail
        rcases h_rec with ⟨c1, hc1, hd1⟩
        refine ⟨c1, ?_, hd1⟩
        rw [mem_dedupCells] at hc1 ⊢
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc1 ⊢
        rcases hc1 with (rfl | rfl) | hmem
        · exact Or.inr (Or.inl h_eq_step.symm)
        · exact Or.inl (Or.inr rfl)
        · exact Or.inr (Or.inr (by rw [h_eq_step]; exact hmem))

/--
Inductive invariant relation on cell pairs during raymarching across corner grazes:
the cells are either identical, or they are diagonally adjacent corner neighbors
separated by one step in X and one step in Y.
-/
def CellStepRel (stepX stepY : ℤ) (c1 c2 : Cell) : Prop :=
  c1 = c2 ∨
  c1 = ⟨c2.x + stepX, c2.y - stepY⟩ ∨
  c1 = ⟨c2.x - stepX, c2.y + stepY⟩

/--
Any pair of cells satisfying `CellStepRel` has discrete Chebyshev distance at most 1.
-/
theorem chebyshevDistance_of_CellStepRel (stepX stepY : ℤ)
    (hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1) (hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1)
    (c1 c2 : Cell) (h : CellStepRel stepX stepY c1 c2) :
    chebyshevDistance c1 c2 ≤ 1 := by
  unfold CellStepRel chebyshevDistance at *
  rcases h with rfl | rfl | rfl
  · simp
  · dsimp only []
    have hx : (c2.x + stepX - c2.x).natAbs ≤ 1 := by
      have : c2.x + stepX - c2.x = stepX := by ring
      rw [this]
      rcases hX with rfl | rfl | rfl <;> omega
    have hy : (c2.y - stepY - c2.y).natAbs ≤ 1 := by
      have : c2.y - stepY - c2.y = -stepY := by ring
      rw [this]
      rcases hY with rfl | rfl | rfl <;> omega
    exact max_le hx hy
  · dsimp only []
    have hx : (c2.x - stepX - c2.x).natAbs ≤ 1 := by
      have : c2.x - stepX - c2.x = -stepX := by ring
      rw [this]
      rcases hX with rfl | rfl | rfl <;> omega
    have hy : (c2.y + stepY - c2.y).natAbs ≤ 1 := by
      have : c2.y + stepY - c2.y = stepY := by ring
      rw [this]
      rcases hY with rfl | rfl | rfl <;> omega
    exact max_le hx hy

end Geometry
