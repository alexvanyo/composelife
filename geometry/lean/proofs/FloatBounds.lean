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
import Geometry.LineSegment
import proofs.Interval
import proofs.RayMarchStep
import Mathlib.Tactic.Linarith

namespace Geometry

/--
The next cell produced by `rayMarchStepFloat` is always one of the 4 candidate transitions:
current cell, stepX neighbor, stepY neighbor, or diagonal step.
-/
theorem rayMarchStepFloat_candidates (start : Point32) (dx dy : Binary64) (stepX stepY : Int) (c : Cell) :
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
theorem chebyshevDistance_stepFloat_le_one (start : Point32) (dx dy : Binary64) (stepX stepY : Int)
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
Accumulator append property for rayMarchFloat.
-/
theorem rayMarchFloat_acc (fuel : ℕ) (start : Point32) (dx dy : Binary64) (stepX stepY : ℤ)
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
Unfolding step equation for rayMarchFloat with empty accumulator.
-/
theorem rayMarchFloat_succ (fuel : ℕ) (start : Point32) (dx dy : Binary64) (stepX stepY : ℤ)
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
Discrete Chebyshev distance between horizontal and vertical corner neighbors is at most 1.
-/
theorem chebyshevDistance_diamond_X_Y (c : Cell) (stepX stepY : ℤ)
    (hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1) (hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1) :
    chebyshevDistance ⟨c.x + stepX, c.y⟩ ⟨c.x, c.y + stepY⟩ ≤ 1 := by
  unfold chebyshevDistance; dsimp only []
  have hx : (c.x + stepX - c.x).natAbs ≤ 1 := by
    have : c.x + stepX - c.x = stepX := by ring
    rw [this]; rcases hX with rfl | rfl | rfl <;> omega
  have hy : (c.y - (c.y + stepY)).natAbs ≤ 1 := by
    have : c.y - (c.y + stepY) = -stepY := by ring
    rw [this]; rcases hY with rfl | rfl | rfl <;> omega
  exact max_le hx hy

/--
Discrete Chebyshev distance between diagonal corner neighbor and horizontal neighbor is at most 1.
-/
theorem chebyshevDistance_diamond_diag_X (c : Cell) (stepX stepY : ℤ)
    (_hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1) (hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1) :
    chebyshevDistance ⟨c.x + stepX, c.y + stepY⟩ ⟨c.x + stepX, c.y⟩ ≤ 1 := by
  unfold chebyshevDistance; dsimp only []
  have hx : (c.x + stepX - (c.x + stepX)).natAbs ≤ 1 := by simp
  have hy : (c.y + stepY - c.y).natAbs ≤ 1 := by
    have : c.y + stepY - c.y = stepY := by ring
    rw [this]; rcases hY with rfl | rfl | rfl <;> omega
  exact max_le hx hy

/--
Discrete Chebyshev distance between diagonal corner neighbor and vertical neighbor is at most 1.
-/
theorem chebyshevDistance_diamond_diag_Y (c : Cell) (stepX stepY : ℤ)
    (hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1) (_hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1) :
    chebyshevDistance ⟨c.x + stepX, c.y + stepY⟩ ⟨c.x, c.y + stepY⟩ ≤ 1 := by
  unfold chebyshevDistance; dsimp only []
  have hx : (c.x + stepX - c.x).natAbs ≤ 1 := by
    have : c.x + stepX - c.x = stepX := by ring
    rw [this]; rcases hX with rfl | rfl | rfl <;> omega
  have hy : (c.y + stepY - (c.y + stepY)).natAbs ≤ 1 := by simp
  exact max_le hx hy

/--
Diamond step synchronizing proximity:
For any base cell c and step directions stepX, stepY ∈ {-1, 0, 1},
all cells involved in the corner diamond transition
(the base cell c, the horizontal neighbor, the vertical neighbor, and the diagonal synchronizing cell)
are mutually within Chebyshev distance at most 1.
-/
theorem cell_diamond_sync_proximity (c : Cell) (stepX stepY : ℤ)
    (hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1) (hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1) :
    chebyshevDistance ⟨c.x + stepX, c.y⟩ ⟨c.x, c.y + stepY⟩ ≤ 1 ∧
    chebyshevDistance ⟨c.x + stepX, c.y + stepY⟩ ⟨c.x, c.y + stepY⟩ ≤ 1 ∧
    chebyshevDistance ⟨c.x + stepX, c.y + stepY⟩ ⟨c.x + stepX, c.y⟩ ≤ 1 ∧
    chebyshevDistance ⟨c.x + stepX, c.y⟩ c ≤ 1 ∧
    chebyshevDistance ⟨c.x, c.y + stepY⟩ c ≤ 1 := by
  refine ⟨chebyshevDistance_diamond_X_Y c stepX stepY hX hY,
          chebyshevDistance_diamond_diag_Y c stepX stepY hX hY,
          chebyshevDistance_diamond_diag_X c stepX stepY hX hY,
          ?_, ?_⟩
  · unfold chebyshevDistance; dsimp only []
    have hx : (c.x + stepX - c.x).natAbs ≤ 1 := by
      have : c.x + stepX - c.x = stepX := by ring
      rw [this]; rcases hX with rfl | rfl | rfl <;> omega
    have hy : (c.y - c.y).natAbs ≤ 1 := by simp
    exact max_le hx hy
  · unfold chebyshevDistance; dsimp only []
    have hx : (c.x - c.x).natAbs ≤ 1 := by simp
    have hy : (c.y + stepY - c.y).natAbs ≤ 1 := by
      have : c.y + stepY - c.y = stepY := by ring
      rw [this]; rcases hY with rfl | rfl | rfl <;> omega
    exact max_le hx hy

/--
Two-step unfolding for rayMarchFloat across a corner diamond transition:
When the float algorithm steps from `c` to `⟨c.x + stepX, c.y⟩` and then to `⟨c.x + stepX, c.y + stepY⟩`,
the visited cells are precisely `⟨c.x + stepX, c.y⟩ :: ⟨c.x + stepX, c.y + stepY⟩ :: tail`.
-/
theorem rayMarchFloat_succ_succ (fuel : ℕ) (start : Point32) (dx dy : Binary64) (stepX stepY : ℤ)
    (endCell c : Cell)
    (h_not_end : (c == endCell) = false)
    (h_not_done1 : (rayMarchStepFloat start dx dy stepX stepY c).2 = false)
    (h_step1 : (rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x + stepX, c.y⟩)
    (h_not_end1 : (⟨c.x + stepX, c.y⟩ == endCell) = false)
    (h_not_done2 : (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y⟩).2 = false)
    (h_step2 : (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y⟩).1 = ⟨c.x + stepX, c.y + stepY⟩) :
    rayMarchFloat (fuel + 2) start dx dy stepX stepY endCell c [] =
      ⟨c.x + stepX, c.y⟩ :: ⟨c.x + stepX, c.y + stepY⟩ ::
        rayMarchFloat fuel start dx dy stepX stepY endCell ⟨c.x + stepX, c.y + stepY⟩ [] := by
  have h1 := rayMarchFloat_succ (fuel + 1) start dx dy stepX stepY endCell c
  rw [h1]
  rw [h_not_end]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [show (rayMarchStepFloat start dx dy stepX stepY c) = (⟨c.x + stepX, c.y⟩, false) from
    Prod.ext h_step1 h_not_done1]
  dsimp only []
  have h2 := rayMarchFloat_succ fuel start dx dy stepX stepY endCell ⟨c.x + stepX, c.y⟩
  rw [h2]
  rw [h_not_end1]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [show (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y⟩) = (⟨c.x + stepX, c.y + stepY⟩, false) from
    Prod.ext h_step2 h_not_done2]
  dsimp only []
  simp only [Bool.false_eq_true, ↓reduceIte]

/--
Two-step unfolding for rational rayMarch across a corner diamond transition:
When the ideal algorithm steps from `c` to `⟨c.x, c.y + stepY⟩` and then to `⟨c.x + stepX, c.y + stepY⟩`,
the visited cells are precisely `⟨c.x, c.y + stepY⟩ :: ⟨c.x + stepX, c.y + stepY⟩ :: tail`.
-/
theorem rayMarch_succ_succ (fuel : ℕ) (start ptEnd : Point) (dx dy : ℚ) (stepX stepY : ℤ)
    (endCell c : Cell)
    (h_not_end : (c == endCell) = false)
    (h_not_done1 : (rayMarchStep start ptEnd dx dy stepX stepY c).2 = false)
    (h_step1 : (rayMarchStep start ptEnd dx dy stepX stepY c).1 = ⟨c.x, c.y + stepY⟩)
    (h_not_end1 : (⟨c.x, c.y + stepY⟩ == endCell) = false)
    (h_not_done2 : (rayMarchStep start ptEnd dx dy stepX stepY ⟨c.x, c.y + stepY⟩).2 = false)
    (h_step2 : (rayMarchStep start ptEnd dx dy stepX stepY ⟨c.x, c.y + stepY⟩).1 = ⟨c.x + stepX, c.y + stepY⟩) :
    rayMarch (fuel + 2) start ptEnd dx dy stepX stepY endCell c [] =
      ⟨c.x, c.y + stepY⟩ :: ⟨c.x + stepX, c.y + stepY⟩ ::
        rayMarch fuel start ptEnd dx dy stepX stepY endCell ⟨c.x + stepX, c.y + stepY⟩ [] := by
  have h1 := rayMarch_succ (fuel + 1) start ptEnd dx dy stepX stepY endCell c
  rw [h1]
  rw [h_not_end]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [show (rayMarchStep start ptEnd dx dy stepX stepY c) = (⟨c.x, c.y + stepY⟩, false) from
    Prod.ext h_step1 h_not_done1]
  dsimp only []
  have h2 := rayMarch_succ fuel start ptEnd dx dy stepX stepY endCell ⟨c.x, c.y + stepY⟩
  rw [h2]
  rw [h_not_end1]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [show (rayMarchStep start ptEnd dx dy stepX stepY ⟨c.x, c.y + stepY⟩) = (⟨c.x + stepX, c.y + stepY⟩, false) from
    Prod.ext h_step2 h_not_done2]
  dsimp only []
  simp only [Bool.false_eq_true, ↓reduceIte]

/--
Direction 1 proximity for a 2-step corner diamond transition:
Every cell visited by the float path during the diamond transition (or in its tail)
is within Chebyshev distance at most 1 of some cell in the deduplicated ideal output.
-/
theorem rayMarchFloat_diamond_near_rayMarch_endpoints
    (fuel : ℕ) (start : Point32) (ptEnd : Point)
    (dx dy : Binary64) (dxQ dyQ : ℚ) (stepX stepY : ℤ)
    (endCell c : Cell)
    (hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1) (hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1)
    (h_not_end : (c == endCell) = false)
    (h_not_doneF1 : (rayMarchStepFloat start dx dy stepX stepY c).2 = false)
    (h_stepF1 : (rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x + stepX, c.y⟩)
    (h_not_endF1 : (⟨c.x + stepX, c.y⟩ == endCell) = false)
    (h_not_doneF2 : (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y⟩).2 = false)
    (h_stepF2 : (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y⟩).1 = ⟨c.x + stepX, c.y + stepY⟩)
    (h_not_doneI1 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).2 = false)
    (h_stepI1 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 = ⟨c.x, c.y + stepY⟩)
    (h_not_endI1 : (⟨c.x, c.y + stepY⟩ == endCell) = false)
    (h_not_doneI2 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x, c.y + stepY⟩).2 = false)
    (h_stepI2 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x, c.y + stepY⟩).1 = ⟨c.x + stepX, c.y + stepY⟩)
    (ih : ∀ c1 ∈ rayMarchFloat fuel start dx dy stepX stepY endCell ⟨c.x + stepX, c.y + stepY⟩ [],
      ∃ c2 ∈ dedupCells ([⟨c.x + stepX, c.y + stepY⟩, endCell] ++
        rayMarch fuel start.toPoint ptEnd dxQ dyQ stepX stepY endCell ⟨c.x + stepX, c.y + stepY⟩ []),
        chebyshevDistance c1 c2 ≤ 1) :
    ∀ c1 ∈ rayMarchFloat (fuel + 2) start dx dy stepX stepY endCell c [],
      ∃ c2 ∈ dedupCells ([c, endCell] ++
        rayMarch (fuel + 2) start.toPoint ptEnd dxQ dyQ stepX stepY endCell c []),
        chebyshevDistance c1 c2 ≤ 1 := by
  intro c1 hc1
  rw [rayMarchFloat_succ_succ fuel start dx dy stepX stepY endCell c
    h_not_end h_not_doneF1 h_stepF1 h_not_endF1 h_not_doneF2 h_stepF2] at hc1
  rw [rayMarch_succ_succ fuel start.toPoint ptEnd dxQ dyQ stepX stepY endCell c
    h_not_end h_not_doneI1 h_stepI1 h_not_endI1 h_not_doneI2 h_stepI2]
  have h_sync := cell_diamond_sync_proximity c stepX stepY hX hY
  simp only [List.mem_cons] at hc1
  rcases hc1 with rfl | rfl | htail
  · refine ⟨⟨c.x, c.y + stepY⟩, ?_, h_sync.1⟩
    rw [mem_dedupCells]
    simp only [List.mem_append, List.mem_cons, true_or, or_true]
  · refine ⟨⟨c.x + stepX, c.y + stepY⟩, ?_, ?_⟩
    · rw [mem_dedupCells]
      simp only [List.mem_append, List.mem_cons, true_or, or_true]
    · rw [chebyshevDistance_self]; omega
  · rcases ih c1 htail with ⟨c2, hc2, hd2⟩
    refine ⟨c2, ?_, hd2⟩
    rw [mem_dedupCells] at hc2 ⊢
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc2 ⊢
    rcases hc2 with (rfl | rfl) | hmem
    · right; right; left; rfl
    · left; right; rfl
    · right; right; right; exact hmem

/--
Direction 2 proximity for a 2-step corner diamond transition:
Every cell visited by the ideal rational path during the diamond transition (or in its tail)
is within Chebyshev distance at most 1 of some cell in the deduplicated float output.
-/
theorem rayMarch_diamond_near_rayMarchFloat_endpoints
    (fuel : ℕ) (start : Point32) (ptEnd : Point)
    (dx dy : Binary64) (dxQ dyQ : ℚ) (stepX stepY : ℤ)
    (endCell c : Cell)
    (hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1) (hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1)
    (h_not_end : (c == endCell) = false)
    (h_not_doneF1 : (rayMarchStepFloat start dx dy stepX stepY c).2 = false)
    (h_stepF1 : (rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x + stepX, c.y⟩)
    (h_not_endF1 : (⟨c.x + stepX, c.y⟩ == endCell) = false)
    (h_not_doneF2 : (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y⟩).2 = false)
    (h_stepF2 : (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y⟩).1 = ⟨c.x + stepX, c.y + stepY⟩)
    (h_not_doneI1 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).2 = false)
    (h_stepI1 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 = ⟨c.x, c.y + stepY⟩)
    (h_not_endI1 : (⟨c.x, c.y + stepY⟩ == endCell) = false)
    (h_not_doneI2 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x, c.y + stepY⟩).2 = false)
    (h_stepI2 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x, c.y + stepY⟩).1 = ⟨c.x + stepX, c.y + stepY⟩)
    (ih : ∀ c2 ∈ rayMarch fuel start.toPoint ptEnd dxQ dyQ stepX stepY endCell ⟨c.x + stepX, c.y + stepY⟩ [],
      ∃ c1 ∈ dedupCells ([⟨c.x + stepX, c.y + stepY⟩, endCell] ++
        rayMarchFloat fuel start dx dy stepX stepY endCell ⟨c.x + stepX, c.y + stepY⟩ []),
        chebyshevDistance c1 c2 ≤ 1) :
    ∀ c2 ∈ rayMarch (fuel + 2) start.toPoint ptEnd dxQ dyQ stepX stepY endCell c [],
      ∃ c1 ∈ dedupCells ([c, endCell] ++
        rayMarchFloat (fuel + 2) start dx dy stepX stepY endCell c []),
        chebyshevDistance c1 c2 ≤ 1 := by
  intro c2 hc2
  rw [rayMarchFloat_succ_succ fuel start dx dy stepX stepY endCell c
    h_not_end h_not_doneF1 h_stepF1 h_not_endF1 h_not_doneF2 h_stepF2]
  rw [rayMarch_succ_succ fuel start.toPoint ptEnd dxQ dyQ stepX stepY endCell c
    h_not_end h_not_doneI1 h_stepI1 h_not_endI1 h_not_doneI2 h_stepI2] at hc2
  have h_sync := cell_diamond_sync_proximity c stepX stepY hX hY
  simp only [List.mem_cons] at hc2
  rcases hc2 with rfl | rfl | htail
  · refine ⟨⟨c.x + stepX, c.y⟩, ?_, ?_⟩
    · rw [mem_dedupCells]
      simp only [List.mem_append, List.mem_cons, true_or, or_true]
    · exact h_sync.1
  · refine ⟨⟨c.x + stepX, c.y + stepY⟩, ?_, ?_⟩
    · rw [mem_dedupCells]
      simp only [List.mem_append, List.mem_cons, true_or, or_true]
    · rw [chebyshevDistance_self]; omega
  · rcases ih c2 htail with ⟨c1, hc1, hd1⟩
    refine ⟨c1, ?_, hd1⟩
    rw [mem_dedupCells] at hc1 ⊢
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc1 ⊢
    rcases hc1 with (rfl | rfl) | hmem
    · right; right; left; rfl
    · left; right; rfl
    · right; right; right; exact hmem

/--
Direction 1 proximity inductive descent under single-step agreement:
If the floating-point and ideal step transitions agree at `current`,
then any cell in the floating-point raymarch of fuel `fuel + 1` is within Chebyshev distance at most 1
of some cell in the deduplicated ideal raymarch (including endpoints),
assuming the induction hypothesis holds for the remaining fuel from the next cell.
-/
theorem rayMarchFloat_step_agree_near_rayMarch_endpoints
    (fuel : ℕ) (start : Point32) (ptEnd : Point)
    (dx dy : Binary64) (dxQ dyQ : ℚ) (stepX stepY : ℤ) (endCell current : Cell)
    (hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1) (hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1)
    (h_step : (rayMarchStepFloat start dx dy stepX stepY current).1 =
      (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY current).1)
    (h_done : (rayMarchStepFloat start dx dy stepX stepY current).2 =
      (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY current).2)
    (ih : ∀ c1 ∈ rayMarchFloat fuel start dx dy stepX stepY endCell
        (rayMarchStepFloat start dx dy stepX stepY current).1 [],
      ∃ c2 ∈ dedupCells ([(rayMarchStepFloat start dx dy stepX stepY current).1, endCell] ++
        rayMarch fuel start.toPoint ptEnd dxQ dyQ stepX stepY endCell
          (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY current).1 []),
        chebyshevDistance c1 c2 ≤ 1) :
    ∀ c1 ∈ rayMarchFloat (fuel + 1) start dx dy stepX stepY endCell current [],
      ∃ c2 ∈ dedupCells ([current, endCell] ++
        rayMarch (fuel + 1) start.toPoint ptEnd dxQ dyQ stepX stepY endCell current []),
        chebyshevDistance c1 c2 ≤ 1 := by
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
    rcases hc1 with rfl | htail
    · refine ⟨current, ?_, ?_⟩
      · rw [mem_dedupCells]
        simp only [List.mem_append, List.mem_cons, true_or]
      · rw [chebyshevDistance_symm]
        exact chebyshevDistance_stepFloat_le_one start dx dy stepX stepY hX hY current
    · have h_rec := ih c1 htail
      rcases h_rec with ⟨c2, hc2, hd2⟩
      refine ⟨c2, ?_, hd2⟩
      rw [mem_dedupCells] at hc2 ⊢
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc2 ⊢
      rcases hc2 with (rfl | rfl) | hmem
      · right; left; rw [h_step]
      · left; right; rfl
      · right; right; exact hmem

/--
Direction 2 proximity inductive descent under single-step agreement:
If the floating-point and ideal step transitions agree at `current`,
then any cell in the ideal raymarch of fuel `fuel + 1` is within Chebyshev distance at most 1
of some cell in the deduplicated floating-point raymarch (including endpoints),
assuming the induction hypothesis holds for the remaining fuel from the next cell.
-/
theorem rayMarch_step_agree_near_rayMarchFloat_endpoints
    (fuel : ℕ) (start : Point32) (ptEnd : Point)
    (dx dy : Binary64) (dxQ dyQ : ℚ) (stepX stepY : ℤ) (endCell current : Cell)
    (hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1) (hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1)
    (h_step : (rayMarchStepFloat start dx dy stepX stepY current).1 =
      (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY current).1)
    (h_done : (rayMarchStepFloat start dx dy stepX stepY current).2 =
      (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY current).2)
    (ih : ∀ c2 ∈ rayMarch fuel start.toPoint ptEnd dxQ dyQ stepX stepY endCell
        (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY current).1 [],
      ∃ c1 ∈ dedupCells ([(rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY current).1, endCell] ++
        rayMarchFloat fuel start dx dy stepX stepY endCell
          (rayMarchStepFloat start dx dy stepX stepY current).1 []),
        chebyshevDistance c1 c2 ≤ 1) :
    ∀ c2 ∈ rayMarch (fuel + 1) start.toPoint ptEnd dxQ dyQ stepX stepY endCell current [],
      ∃ c1 ∈ dedupCells ([current, endCell] ++
        rayMarchFloat (fuel + 1) start dx dy stepX stepY endCell current []),
        chebyshevDistance c1 c2 ≤ 1 := by
  intro c2 hc2
  rw [rayMarch_succ] at hc2
  dsimp only [] at hc2
  rw [rayMarchFloat_succ]
  dsimp only []
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
    rcases hc2 with rfl | htail
    · refine ⟨current, ?_, ?_⟩
      · rw [mem_dedupCells]
        simp only [List.mem_append, List.mem_cons, true_or]
      · exact chebyshevDistance_step_le_one start.toPoint ptEnd dxQ dyQ stepX stepY hX hY current
    · have h_rec := ih c2 htail
      rcases h_rec with ⟨c1, hc1, hd1⟩
      refine ⟨c1, ?_, hd1⟩
      rw [mem_dedupCells] at hc1 ⊢
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc1 ⊢
      rcases hc1 with (rfl | rfl) | hmem
      · right; left; rw [h_step]
      · left; right; rfl
      · right; right; exact hmem

/--
Two-step unfolding for rayMarchFloat across a symmetric corner diamond transition:
When the float algorithm steps from `c` to `⟨c.x, c.y + stepY⟩` and then to `⟨c.x + stepX, c.y + stepY⟩`.
-/
theorem rayMarchFloat_succ_succ_symm (fuel : ℕ) (start : Point32) (dx dy : Binary64) (stepX stepY : ℤ)
    (endCell c : Cell)
    (h_not_end : (c == endCell) = false)
    (h_not_doneF1 : (rayMarchStepFloat start dx dy stepX stepY c).2 = false)
    (h_stepF1 : (rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x, c.y + stepY⟩)
    (h_not_endF1 : (⟨c.x, c.y + stepY⟩ == endCell) = false)
    (h_not_doneF2 : (rayMarchStepFloat start dx dy stepX stepY ⟨c.x, c.y + stepY⟩).2 = false)
    (h_stepF2 : (rayMarchStepFloat start dx dy stepX stepY ⟨c.x, c.y + stepY⟩).1 = ⟨c.x + stepX, c.y + stepY⟩) :
    rayMarchFloat (fuel + 2) start dx dy stepX stepY endCell c [] =
      ⟨c.x, c.y + stepY⟩ :: ⟨c.x + stepX, c.y + stepY⟩ ::
        rayMarchFloat fuel start dx dy stepX stepY endCell ⟨c.x + stepX, c.y + stepY⟩ [] := by
  have h1 := rayMarchFloat_succ (fuel + 1) start dx dy stepX stepY endCell c
  rw [h1]
  rw [h_not_end]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [show (rayMarchStepFloat start dx dy stepX stepY c) = (⟨c.x, c.y + stepY⟩, false) from
    Prod.ext h_stepF1 h_not_doneF1]
  dsimp only []
  have h2 := rayMarchFloat_succ fuel start dx dy stepX stepY endCell ⟨c.x, c.y + stepY⟩
  rw [h2]
  rw [h_not_endF1]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [show (rayMarchStepFloat start dx dy stepX stepY ⟨c.x, c.y + stepY⟩) = (⟨c.x + stepX, c.y + stepY⟩, false) from
    Prod.ext h_stepF2 h_not_doneF2]
  dsimp only []
  simp only [Bool.false_eq_true, ↓reduceIte]

/--
Two-step unfolding for rational rayMarch across a symmetric corner diamond transition:
When the ideal algorithm steps from `c` to `⟨c.x + stepX, c.y⟩` and then to `⟨c.x + stepX, c.y + stepY⟩`.
-/
theorem rayMarch_succ_succ_symm (fuel : ℕ) (start ptEnd : Point) (dx dy : ℚ) (stepX stepY : ℤ)
    (endCell c : Cell)
    (h_not_end : (c == endCell) = false)
    (h_not_done1 : (rayMarchStep start ptEnd dx dy stepX stepY c).2 = false)
    (h_step1 : (rayMarchStep start ptEnd dx dy stepX stepY c).1 = ⟨c.x + stepX, c.y⟩)
    (h_not_end1 : (⟨c.x + stepX, c.y⟩ == endCell) = false)
    (h_not_done2 : (rayMarchStep start ptEnd dx dy stepX stepY ⟨c.x + stepX, c.y⟩).2 = false)
    (h_step2 : (rayMarchStep start ptEnd dx dy stepX stepY ⟨c.x + stepX, c.y⟩).1 = ⟨c.x + stepX, c.y + stepY⟩) :
    rayMarch (fuel + 2) start ptEnd dx dy stepX stepY endCell c [] =
      ⟨c.x + stepX, c.y⟩ :: ⟨c.x + stepX, c.y + stepY⟩ ::
        rayMarch fuel start ptEnd dx dy stepX stepY endCell ⟨c.x + stepX, c.y + stepY⟩ [] := by
  have h1 := rayMarch_succ (fuel + 1) start ptEnd dx dy stepX stepY endCell c
  rw [h1]
  rw [h_not_end]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [show (rayMarchStep start ptEnd dx dy stepX stepY c) = (⟨c.x + stepX, c.y⟩, false) from
    Prod.ext h_step1 h_not_done1]
  dsimp only []
  have h2 := rayMarch_succ fuel start ptEnd dx dy stepX stepY endCell ⟨c.x + stepX, c.y⟩
  rw [h2]
  rw [h_not_end1]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [show (rayMarchStep start ptEnd dx dy stepX stepY ⟨c.x + stepX, c.y⟩) = (⟨c.x + stepX, c.y + stepY⟩, false) from
    Prod.ext h_step2 h_not_done2]
  dsimp only []
  simp only [Bool.false_eq_true, ↓reduceIte]

/--
Direction 1 proximity inductive descent across a symmetric corner diamond transition (Float Y-then-X, Ideal X-then-Y):
If floating-point steps Y then X while ideal rational steps X then Y,
reaching the common diagonal cell `⟨c.x + stepX, c.y + stepY⟩` in 2 steps,
then any cell visited by floating-point raymarching is within Chebyshev distance at most 1
of some cell in the deduplicated ideal raymarching output (including endpoints).
-/
theorem rayMarchFloat_diamond_symm_near_rayMarch_endpoints
    (fuel : ℕ) (start : Point32) (ptEnd : Point)
    (dx dy : Binary64) (dxQ dyQ : ℚ) (stepX stepY : ℤ)
    (endCell c : Cell)
    (hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1) (hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1)
    (h_not_end : (c == endCell) = false)
    (h_not_doneF1 : (rayMarchStepFloat start dx dy stepX stepY c).2 = false)
    (h_stepF1 : (rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x, c.y + stepY⟩)
    (h_not_endF1 : (⟨c.x, c.y + stepY⟩ == endCell) = false)
    (h_not_doneF2 : (rayMarchStepFloat start dx dy stepX stepY ⟨c.x, c.y + stepY⟩).2 = false)
    (h_stepF2 : (rayMarchStepFloat start dx dy stepX stepY ⟨c.x, c.y + stepY⟩).1 = ⟨c.x + stepX, c.y + stepY⟩)
    (h_not_doneI1 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).2 = false)
    (h_stepI1 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 = ⟨c.x + stepX, c.y⟩)
    (h_not_endI1 : (⟨c.x + stepX, c.y⟩ == endCell) = false)
    (h_not_doneI2 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y⟩).2 = false)
    (h_stepI2 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y⟩).1 = ⟨c.x + stepX, c.y + stepY⟩)
    (ih : ∀ c1 ∈ rayMarchFloat fuel start dx dy stepX stepY endCell ⟨c.x + stepX, c.y + stepY⟩ [],
      ∃ c2 ∈ dedupCells ([⟨c.x + stepX, c.y + stepY⟩, endCell] ++
        rayMarch fuel start.toPoint ptEnd dxQ dyQ stepX stepY endCell ⟨c.x + stepX, c.y + stepY⟩ []),
        chebyshevDistance c1 c2 ≤ 1) :
    ∀ c1 ∈ rayMarchFloat (fuel + 2) start dx dy stepX stepY endCell c [],
      ∃ c2 ∈ dedupCells ([c, endCell] ++
        rayMarch (fuel + 2) start.toPoint ptEnd dxQ dyQ stepX stepY endCell c []),
        chebyshevDistance c1 c2 ≤ 1 := by
  intro c1 hc1
  rw [rayMarchFloat_succ_succ_symm fuel start dx dy stepX stepY endCell c
    h_not_end h_not_doneF1 h_stepF1 h_not_endF1 h_not_doneF2 h_stepF2] at hc1
  rw [rayMarch_succ_succ_symm fuel start.toPoint ptEnd dxQ dyQ stepX stepY endCell c
    h_not_end h_not_doneI1 h_stepI1 h_not_endI1 h_not_doneI2 h_stepI2]
  have h_sync := cell_diamond_sync_proximity c stepX stepY hX hY
  simp only [List.mem_cons] at hc1
  rcases hc1 with rfl | rfl | htail
  · refine ⟨⟨c.x + stepX, c.y⟩, ?_, ?_⟩
    · rw [mem_dedupCells]
      simp only [List.mem_append, List.mem_cons, true_or, or_true]
    · rw [chebyshevDistance_symm]; exact h_sync.1
  · refine ⟨⟨c.x + stepX, c.y + stepY⟩, ?_, ?_⟩
    · rw [mem_dedupCells]
      simp only [List.mem_append, List.mem_cons, true_or, or_true]
    · rw [chebyshevDistance_self]; omega
  · rcases ih c1 htail with ⟨c2, hc2, hd2⟩
    refine ⟨c2, ?_, hd2⟩
    rw [mem_dedupCells] at hc2 ⊢
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc2 ⊢
    rcases hc2 with (rfl | rfl) | hmem
    · right; right; left; rfl
    · left; right; rfl
    · right; right; right; exact hmem

/--
Direction 2 proximity inductive descent across a symmetric corner diamond transition (Float Y-then-X, Ideal X-then-Y):
If floating-point steps Y then X while ideal rational steps X then Y,
reaching the common diagonal cell `⟨c.x + stepX, c.y + stepY⟩` in 2 steps,
then any cell visited by ideal rational raymarching is within Chebyshev distance at most 1
of some cell in the deduplicated floating-point raymarching output (including endpoints).
-/
theorem rayMarch_diamond_symm_near_rayMarchFloat_endpoints
    (fuel : ℕ) (start : Point32) (ptEnd : Point)
    (dx dy : Binary64) (dxQ dyQ : ℚ) (stepX stepY : ℤ)
    (endCell c : Cell)
    (hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1) (hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1)
    (h_not_end : (c == endCell) = false)
    (h_not_doneF1 : (rayMarchStepFloat start dx dy stepX stepY c).2 = false)
    (h_stepF1 : (rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x, c.y + stepY⟩)
    (h_not_endF1 : (⟨c.x, c.y + stepY⟩ == endCell) = false)
    (h_not_doneF2 : (rayMarchStepFloat start dx dy stepX stepY ⟨c.x, c.y + stepY⟩).2 = false)
    (h_stepF2 : (rayMarchStepFloat start dx dy stepX stepY ⟨c.x, c.y + stepY⟩).1 = ⟨c.x + stepX, c.y + stepY⟩)
    (h_not_doneI1 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).2 = false)
    (h_stepI1 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 = ⟨c.x + stepX, c.y⟩)
    (h_not_endI1 : (⟨c.x + stepX, c.y⟩ == endCell) = false)
    (h_not_doneI2 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y⟩).2 = false)
    (h_stepI2 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y⟩).1 = ⟨c.x + stepX, c.y + stepY⟩)
    (ih : ∀ c2 ∈ rayMarch fuel start.toPoint ptEnd dxQ dyQ stepX stepY endCell ⟨c.x + stepX, c.y + stepY⟩ [],
      ∃ c1 ∈ dedupCells ([⟨c.x + stepX, c.y + stepY⟩, endCell] ++
        rayMarchFloat fuel start dx dy stepX stepY endCell ⟨c.x + stepX, c.y + stepY⟩ []),
        chebyshevDistance c1 c2 ≤ 1) :
    ∀ c2 ∈ rayMarch (fuel + 2) start.toPoint ptEnd dxQ dyQ stepX stepY endCell c [],
      ∃ c1 ∈ dedupCells ([c, endCell] ++
        rayMarchFloat (fuel + 2) start dx dy stepX stepY endCell c []),
        chebyshevDistance c1 c2 ≤ 1 := by
  intro c2 hc2
  rw [rayMarchFloat_succ_succ_symm fuel start dx dy stepX stepY endCell c
    h_not_end h_not_doneF1 h_stepF1 h_not_endF1 h_not_doneF2 h_stepF2]
  rw [rayMarch_succ_succ_symm fuel start.toPoint ptEnd dxQ dyQ stepX stepY endCell c
    h_not_end h_not_doneI1 h_stepI1 h_not_endI1 h_not_doneI2 h_stepI2] at hc2
  have h_sync := cell_diamond_sync_proximity c stepX stepY hX hY
  simp only [List.mem_cons] at hc2
  rcases hc2 with rfl | rfl | htail
  · refine ⟨⟨c.x, c.y + stepY⟩, ?_, ?_⟩
    · rw [mem_dedupCells]
      simp only [List.mem_append, List.mem_cons, true_or, or_true]
    · rw [chebyshevDistance_symm]; exact h_sync.1
  · refine ⟨⟨c.x + stepX, c.y + stepY⟩, ?_, ?_⟩
    · rw [mem_dedupCells]
      simp only [List.mem_append, List.mem_cons, true_or, or_true]
    · rw [chebyshevDistance_self]; omega
  · rcases ih c2 htail with ⟨c1, hc1, hd1⟩
    refine ⟨c1, ?_, hd1⟩
    rw [mem_dedupCells] at hc1 ⊢
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc1 ⊢
    rcases hc1 with (rfl | rfl) | hmem
    · right; right; left; rfl
    · left; right; rfl
    · right; right; right; exact hmem

theorem rayMarchFloat_endCell (fuel : ℕ) (start : Point32) (dx dy : Binary64) (stepX stepY : ℤ)
    (endCell : Cell) :
    rayMarchFloat fuel start dx dy stepX stepY endCell endCell [] = [] := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    rw [rayMarchFloat_succ]
    simp only [beq_self_eq_true, ite_true]

theorem rayMarch_endCell (fuel : ℕ) (start ptEnd : Point) (dx dy : ℚ) (stepX stepY : ℤ)
    (endCell : Cell) :
    rayMarch fuel start ptEnd dx dy stepX stepY endCell endCell [] = [] := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    rw [rayMarch_succ]
    simp only [beq_self_eq_true, ite_true]

theorem rayMarchFloat_terminal_near_rayMarch_endpoints
    (fuel : ℕ) (start : Point32) (ptEnd : Point)
    (dx dy : Binary64) (dxQ dyQ : ℚ) (stepX stepY : ℤ)
    (endCell current : Cell)
    (h_termF : (current == endCell) = true ∨
               (rayMarchStepFloat start dx dy stepX stepY current).2 = true ∨
               (rayMarchStepFloat start dx dy stepX stepY current).1 = endCell)
    (c1 : Cell)
    (hc1 : c1 ∈ rayMarchFloat fuel start dx dy stepX stepY endCell current []) :
    ∃ c2 ∈ dedupCells ([current, endCell] ++
      rayMarch fuel start.toPoint ptEnd dxQ dyQ stepX stepY endCell current []),
      chebyshevDistance c1 c2 ≤ 1 := by
  cases fuel with
  | zero =>
    unfold rayMarchFloat at hc1
    cases hc1
  | succ fuel =>
    rw [rayMarchFloat_succ] at hc1
    dsimp only [] at hc1
    split_ifs at hc1 with hc hd
    · cases hc1
    · cases hc1
    · rcases h_termF with h_end | h_done_true | h_next_end
      · exfalso
        apply hc
        exact h_end
      · exfalso
        apply hd
        exact h_done_true
      · rw [h_next_end, rayMarchFloat_endCell] at hc1
        simp only [List.mem_singleton] at hc1
        subst c1
        refine ⟨endCell, ?_, by rw [chebyshevDistance_self]; omega⟩
        rw [mem_dedupCells]
        simp

theorem rayMarch_terminal_near_rayMarchFloat_endpoints
    (fuel : ℕ) (start : Point32) (ptEnd : Point)
    (dx dy : Binary64) (dxQ dyQ : ℚ) (stepX stepY : ℤ)
    (endCell current : Cell)
    (h_termI : (current == endCell) = true ∨
               (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY current).2 = true ∨
               (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY current).1 = endCell)
    (c2 : Cell)
    (hc2 : c2 ∈ rayMarch fuel start.toPoint ptEnd dxQ dyQ stepX stepY endCell current []) :
    ∃ c1 ∈ dedupCells ([current, endCell] ++
      rayMarchFloat fuel start dx dy stepX stepY endCell current []),
      chebyshevDistance c1 c2 ≤ 1 := by
  cases fuel with
  | zero =>
    unfold rayMarch at hc2
    cases hc2
  | succ fuel =>
    rw [rayMarch_succ] at hc2
    dsimp only [] at hc2
    split_ifs at hc2 with hc hd
    · cases hc2
    · cases hc2
    · rcases h_termI with h_end | h_done_true | h_next_end
      · exfalso
        apply hc
        exact h_end
      · exfalso
        apply hd
        exact h_done_true
      · rw [h_next_end, rayMarch_endCell] at hc2
        simp only [List.mem_singleton] at hc2
        subst c2
        refine ⟨endCell, ?_, by rw [chebyshevDistance_self]; omega⟩
        rw [mem_dedupCells]
        simp

end Geometry
