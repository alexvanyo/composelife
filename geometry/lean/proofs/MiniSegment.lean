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
import proofs.FloatSemantics
import proofs.FloatBounds
import proofs.FloatProperties
import proofs.FloatAnalysis
import proofs.Interval
import proofs.Soundness
import proofs.Waypoints
import proofs.PointBound
import proofs.RayMarchLimits
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Instances

namespace Geometry

/--
General combinatorial lemma: if two cell collections S₁ and S₂ share an anchor cell,
and every cell in both S₁ and S₂ is within Chebyshev distance 1 of that anchor,
then the discrete Chebyshev Hausdorff distance between S₁ and S₂ is at most 1.
-/
theorem cellHausdorffDistanceLe_of_subset_near_anchor
    (S₁ S₂ : List Cell) (anchor : Cell)
    (h_anchor1 : anchor ∈ S₁)
    (h_anchor2 : anchor ∈ S₂)
    (h_bound1 : ∀ c ∈ S₁, chebyshevDistance c anchor ≤ 1)
    (h_bound2 : ∀ c ∈ S₂, chebyshevDistance c anchor ≤ 1) :
    cellHausdorffDistanceLe S₁ S₂ 1 := by
  constructor
  · intro c1 hc1
    exact ⟨anchor, h_anchor2, h_bound1 c1 hc1⟩
  · intro c2 hc2
    refine ⟨anchor, h_anchor1, ?_⟩
    rw [chebyshevDistance_symm]
    exact h_bound2 c2 hc2

/--
Any cell in the bounding box between two cells at Chebyshev distance at most 1
is also within Chebyshev distance at most 1 from the start cell.
-/
theorem chebyshevDistance_le_one_of_inBoundingBox (x : Cell) (A B : Point)
    (h_bbox : inBoundingBox x A B = true)
    (h_dist : chebyshevDistance (floorPoint A) (floorPoint B) ≤ 1) :
    chebyshevDistance x (floorPoint A) ≤ 1 := by
  unfold inBoundingBox at h_bbox
  unfold chebyshevDistance at h_dist ⊢
  dsimp only [] at h_bbox h_dist ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h_bbox
  rcases h_bbox with ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
  have hx : (x.x - (floorPoint A).x).natAbs ≤ 1 := by
    have h_max : ((floorPoint A).x - (floorPoint B).x).natAbs ≤ 1 := by
      apply le_trans _ h_dist
      exact le_max_left _ _
    omega
  have hy : (x.y - (floorPoint A).y).natAbs ≤ 1 := by
    have h_max : ((floorPoint A).y - (floorPoint B).y).natAbs ≤ 1 := by
      apply le_trans _ h_dist
      exact le_max_right _ _
    omega
  exact max_le hx hy

/--
Every cell in the rational intersection list of a short segment (endpoints with Chebyshev distance ≤ 1)
is within Chebyshev distance at most 1 from the start cell.
-/
theorem cellIntersectionsSegment_cells_near_start (A B : Point)
    (h_dist : chebyshevDistance (floorPoint A) (floorPoint B) ≤ 1) :
    ∀ c ∈ cellIntersectionsSegment A B, chebyshevDistance c (floorPoint A) ≤ 1 := by
  intro c hc
  unfold cellIntersectionsSegment at hc
  dsimp only [] at hc
  cases h_same : (floorPoint A == floorPoint B)
  · rw [h_same] at hc
    simp only [Bool.false_eq_true, ↓reduceIte] at hc
    rw [mem_dedupCells] at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl) | hray
    · rw [chebyshevDistance_self]; omega
    · exact chebyshevDistance_symm (floorPoint B) (floorPoint A) ▸ h_dist
    · have h_snd := (rayMarch_soundness A B c hray).1
      exact chebyshevDistance_le_one_of_inBoundingBox c A B h_snd h_dist
  · rw [h_same] at hc
    simp only [ite_true, List.mem_singleton] at hc
    subst hc
    rw [chebyshevDistance_self]; omega

/--
When two floating-point points reside in the same discrete grid cell,
the floating-point and idealized rational segment intersection lists are strictly identical.
-/
theorem cellIntersectionsSegmentFloat_eq_ideal_of_same_cell
    (A B : Point32) (h_finA : A.isFinite) (h_finB : B.isFinite)
    (h_same : floorPoint32 A = floorPoint32 B) :
    cellIntersectionsSegmentFloat A B = cellIntersectionsSegment A.toPoint B.toPoint := by
  have h_floorA := floorPoint32_eq_floorPoint A h_finA
  have h_floorB := floorPoint32_eq_floorPoint B h_finB
  unfold cellIntersectionsSegmentFloat cellIntersectionsSegment
  dsimp only []
  have h_same_bool : (floorPoint32 A == floorPoint32 B) = true := by
    rw [h_same, beq_self_eq_true]
  have h_ideal : floorPoint A.toPoint = floorPoint B.toPoint := by
    rw [← h_floorA, ← h_floorB, h_same]
  have h_ideal_bool : (floorPoint A.toPoint == floorPoint B.toPoint) = true := by
    rw [h_ideal, beq_self_eq_true]
  rw [h_same_bool, h_ideal_bool]
  simp only [ite_true]
  rw [h_floorA]

/--
When two floating-point points reside in the same discrete grid cell,
the discrete Chebyshev Hausdorff distance between float and rational outputs is 0.
-/
theorem cellIntersectionsSegmentFloat_sub_hausdorff_same_cell
    (A B : Point32) (h_finA : A.isFinite) (h_finB : B.isFinite)
    (h_same : floorPoint32 A = floorPoint32 B) :
    cellHausdorffDistanceLe
      (cellIntersectionsSegmentFloat A B)
      (cellIntersectionsSegment A.toPoint B.toPoint) 0 := by
  have h_eq := cellIntersectionsSegmentFloat_eq_ideal_of_same_cell A B h_finA h_finB h_same
  rw [h_eq]
  exact cellHausdorffDistanceLe_refl _

/--
When two points reside in the same cell, the Hausdorff distance is also at most 1.
-/
theorem cellIntersectionsSegmentFloat_sub_hausdorff_one_of_same_cell
    (A B : Point32) (h_finA : A.isFinite) (h_finB : B.isFinite)
    (h_same : floorPoint32 A = floorPoint32 B) :
    cellHausdorffDistanceLe
      (cellIntersectionsSegmentFloat A B)
      (cellIntersectionsSegment A.toPoint B.toPoint) 1 := by
  have h0 := cellIntersectionsSegmentFloat_sub_hausdorff_same_cell A B h_finA h_finB h_same
  rcases h0 with ⟨h1, h2⟩
  constructor
  · intro c hc
    rcases h1 c hc with ⟨c', hc', hd⟩
    exact ⟨c', hc', by omega⟩
  · intro c hc
    rcases h2 c hc with ⟨c', hc', hd⟩
    exact ⟨c', hc', by omega⟩

/--
Mini-segment agreement at waypoints:
When two points reside in the same cell, the float and rational outputs agree identically.
-/
theorem cellIntersectionsSegment_float_eq_rational_at_waypoints
    (Pi Pi1 : Point32) (h_finPi : Pi.isFinite) (h_finPi1 : Pi1.isFinite)
    (h_same : floorPoint32 Pi = floorPoint32 Pi1) :
    cellIntersectionsSegmentFloat Pi Pi1 =
    cellIntersectionsSegment Pi.toPoint Pi1.toPoint :=
  cellIntersectionsSegmentFloat_eq_ideal_of_same_cell Pi Pi1 h_finPi h_finPi1 h_same

/--
Mini-segment discrete Hausdorff bound:
When two points reside in the same cell, their discrete Chebyshev Hausdorff distance is at most 1.
-/
theorem cellIntersectionsSegmentFloat_sub_hausdorff_one_at_waypoints
    (Pi Pi1 : Point32) (h_finPi : Pi.isFinite) (h_finPi1 : Pi1.isFinite)
    (h_same : floorPoint32 Pi = floorPoint32 Pi1) :
    cellHausdorffDistanceLe
      (cellIntersectionsSegmentFloat Pi Pi1)
      (cellIntersectionsSegment Pi.toPoint Pi1.toPoint) 1 :=
  cellIntersectionsSegmentFloat_sub_hausdorff_one_of_same_cell Pi Pi1 h_finPi h_finPi1 h_same

/--
The endpoint of a segment is always included in the rational intersection output.
-/
theorem cellIntersectionsSegment_contains_end (A B : Point) :
    floorPoint B ∈ cellIntersectionsSegment A B := by
  unfold cellIntersectionsSegment
  dsimp only []
  cases h : (floorPoint A == floorPoint B)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [mem_dedupCells]
    simp only [List.mem_append, List.mem_cons, true_or, or_true]
  · simp only [ite_true]
    have h_eq : floorPoint A = floorPoint B := eq_of_beq h
    simp [h_eq]

theorem rayMarch_fuel_bound_le_four_of_adjacent (startCell endCell : Cell)
    (h_dist : chebyshevDistance startCell endCell ≤ 1) :
    (endCell.x - startCell.x).natAbs + (endCell.y - startCell.y).natAbs + 2 ≤ 4 := by
  unfold chebyshevDistance at h_dist
  have hx : (startCell.x - endCell.x).natAbs ≤ 1 := by
    have := le_max_left (startCell.x - endCell.x).natAbs (startCell.y - endCell.y).natAbs
    omega
  have hy : (startCell.y - endCell.y).natAbs ≤ 1 := by
    have := le_max_right (startCell.x - endCell.x).natAbs (startCell.y - endCell.y).natAbs
    omega
  have hx' : (endCell.x - startCell.x).natAbs = (startCell.x - endCell.x).natAbs := by
    rw [← Int.natAbs_neg, neg_sub]
  have hy' : (endCell.y - startCell.y).natAbs = (startCell.y - endCell.y).natAbs := by
    rw [← Int.natAbs_neg, neg_sub]
  omega

theorem chebyshevDistance_step1_diag_le_one (startCell : Cell) (stepX stepY : ℤ)
    (hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1) (hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1) :
    chebyshevDistance ⟨startCell.x + stepX, startCell.y + stepY⟩ startCell ≤ 1 := by
  unfold chebyshevDistance; dsimp only []
  rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl <;> omega

theorem chebyshevDistance_2x_end_le_one (startCell : Cell) (stepX stepY : ℤ)
    (hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1) (hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1)
    (hend : endCell = ⟨startCell.x + stepX, startCell.y + stepY⟩) :
    chebyshevDistance ⟨startCell.x + 2 * stepX, startCell.y⟩ endCell ≤ 1 ∧
    chebyshevDistance ⟨startCell.x + 2 * stepX, startCell.y + stepY⟩ endCell ≤ 1 ∧
    chebyshevDistance ⟨startCell.x, startCell.y + 2 * stepY⟩ endCell ≤ 1 ∧
    chebyshevDistance ⟨startCell.x + stepX, startCell.y + 2 * stepY⟩ endCell ≤ 1 := by
  rw [hend]
  unfold chebyshevDistance; dsimp only []
  rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl <;> omega

theorem chebyshevDistance_2x_stepY_endCell_le_one (c0 : Cell) (stepX stepY : ℤ)
    (hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1) (hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1)
    (endCell : Cell) (he3 : endCell = ⟨c0.x + stepX, c0.y + stepY⟩) :
    chebyshevDistance ⟨c0.x + 2 * stepX, c0.y + stepY⟩ endCell ≤ 1 := by
  rw [he3]; unfold chebyshevDistance; cases c0
  rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl <;> dsimp <;> omega

theorem chebyshevDistance_stepX_2y_endCell_le_one (c0 : Cell) (stepX stepY : ℤ)
    (hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1) (hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1)
    (endCell : Cell) (he3 : endCell = ⟨c0.x + stepX, c0.y + stepY⟩) :
    chebyshevDistance ⟨c0.x + stepX, c0.y + 2 * stepY⟩ endCell ≤ 1 := by
  rw [he3]; unfold chebyshevDistance; cases c0
  rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl <;> dsimp <;> omega

theorem chebyshevDistance_candidates_diag_endCell_le_one (startCell : Cell) (stepX stepY : ℤ)
    (hX : stepX = -1 ∨ stepX = 1) (hY : stepY = -1 ∨ stepY = 1)
    (endCell : Cell) (hend : endCell = ⟨startCell.x + stepX, startCell.y + stepY⟩)
    (c : Cell)
    (hc : c = ⟨startCell.x + 2 * stepX, startCell.y⟩ ∨
          c = ⟨startCell.x + 2 * stepX, startCell.y + stepY⟩ ∨
          c = ⟨startCell.x + 2 * stepX, startCell.y + 2 * stepY⟩ ∨
          c = ⟨startCell.x, startCell.y + 2 * stepY⟩ ∨
          c = ⟨startCell.x + stepX, startCell.y + 2 * stepY⟩) :
    chebyshevDistance c endCell ≤ 1 := by
  rw [hend]; unfold chebyshevDistance; cases startCell
  rcases hc with rfl | rfl | rfl | rfl | rfl <;>
  rcases hX with rfl | rfl <;> rcases hY with rfl | rfl <;>
  dsimp <;> omega

theorem axial_X_s2_s3_candidates (startCell endCell : Cell) (stepX stepY : ℤ)
    (hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1) (hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1)
    (he1 : endCell = ⟨startCell.x + stepX, startCell.y⟩)
    (c : Cell)
    (hc : c = ⟨startCell.x + stepX, startCell.y + stepY⟩ ∨
          c = ⟨startCell.x + 2 * stepX, startCell.y + stepY⟩) :
    chebyshevDistance c endCell ≤ 1 := by
  rw [he1]; unfold chebyshevDistance; cases startCell
  rcases hc with rfl | rfl <;>
  rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl <;>
  dsimp <;> omega

theorem axial_Y_s2_s3_candidates (startCell endCell : Cell) (stepX stepY : ℤ)
    (hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1) (hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1)
    (he2 : endCell = ⟨startCell.x, startCell.y + stepY⟩)
    (c : Cell)
    (hc : c = ⟨startCell.x + stepX, startCell.y + stepY⟩ ∨
          c = ⟨startCell.x + stepX, startCell.y + 2 * stepY⟩) :
    chebyshevDistance c endCell ≤ 1 := by
  rw [he2]; unfold chebyshevDistance; cases startCell
  rcases hc with rfl | rfl <;>
  rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl <;>
  dsimp <;> omega

theorem fuel_le_3_of_axial_X (startCell endCell : Cell) (stepX : ℤ)
    (hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1)
    (he1 : endCell = ⟨startCell.x + stepX, startCell.y⟩) :
    (endCell.x - startCell.x).natAbs + (endCell.y - startCell.y).natAbs + 2 ≤ 3 := by
  rw [he1]; dsimp only []
  have hx : (startCell.x + stepX - startCell.x).natAbs ≤ 1 := by
    rcases hX with rfl | rfl | rfl <;> omega
  have hy : (startCell.y - startCell.y).natAbs = 0 := by simp
  omega

theorem fuel_le_3_of_axial_Y (startCell endCell : Cell) (stepY : ℤ)
    (hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1)
    (he2 : endCell = ⟨startCell.x, startCell.y + stepY⟩) :
    (endCell.x - startCell.x).natAbs + (endCell.y - startCell.y).natAbs + 2 ≤ 3 := by
  rw [he2]; dsimp only []
  have hx : (startCell.x - startCell.x).natAbs = 0 := by simp
  have hy : (startCell.y + stepY - startCell.y).natAbs ≤ 1 := by
    rcases hY with rfl | rfl | rfl <;> omega
  omega

theorem rayMarchStepFloat_step_cases_stepY_zero (start : Point32) (dx dy : Binary32) (stepX : Int) (c : Cell)
    (hx : stepX ≠ 0) :
    (rayMarchStepFloat start dx dy stepX 0 c).2 = true ∨
    (rayMarchStepFloat start dx dy stepX 0 c).1 = ⟨c.x + stepX, c.y⟩ := by
  unfold rayMarchStepFloat; dsimp only []
  have hx_b : (stepX == 0) = false := by
    cases h : (stepX == 0)
    · rfl
    · exfalso; apply hx; exact eq_of_beq h
  have hy_b : ((0 : Int) == 0) = true := rfl
  rw [hx_b, hy_b]
  simp only [Bool.false_eq_true, ite_false, ite_true]
  split_ifs <;> simp

theorem rayMarchStepFloat_step_cases_stepX_zero (start : Point32) (dx dy : Binary32) (stepY : Int) (c : Cell)
    (_hy : stepY ≠ 0) :
    (rayMarchStepFloat start dx dy 0 stepY c).2 = true ∨
    (rayMarchStepFloat start dx dy 0 stepY c).1 = ⟨c.x, c.y + stepY⟩ := by
  unfold rayMarchStepFloat; dsimp only []
  have hx_b : ((0 : Int) == 0) = true := rfl
  rw [hx_b]
  simp only [ite_true]
  split_ifs <;> simp

theorem rayMarchStepFloat_step_cases (start : Point32) (dx dy : Binary32) (stepX stepY : Int) (c : Cell)
    (hx : stepX ≠ 0) (hy : stepY ≠ 0) :
    (rayMarchStepFloat start dx dy stepX stepY c).2 = true ∨
    ((rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x + stepX, c.y⟩ ∧ (rayMarchStepFloat start dx dy stepX stepY c).2 = false) ∨
    ((rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x, c.y + stepY⟩ ∧ (rayMarchStepFloat start dx dy stepX stepY c).2 = false) ∨
    ((rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x + stepX, c.y + stepY⟩ ∧ (rayMarchStepFloat start dx dy stepX stepY c).2 = false) := by
  unfold rayMarchStepFloat; dsimp only []
  have hx_b : (stepX == 0) = false := by
    cases h : (stepX == 0)
    · rfl
    · exfalso; apply hx; exact eq_of_beq h
  have hy_b : (stepY == 0) = false := by
    cases h : (stepY == 0)
    · rfl
    · exfalso; apply hy; exact eq_of_beq h
  rw [hx_b, hy_b]
  simp only [Bool.false_eq_true, ite_false]
  split_ifs <;> simp

theorem rat_floor_step_cases (a b : ℚ) (h_dist : (b.floor - a.floor).natAbs ≤ 1) :
    b.floor = a.floor ∨ b.floor = a.floor + (if b - a > 0 then 1 else if b - a < 0 then -1 else 0) := by
  by_cases h : b.floor = a.floor
  · exact Or.inl h
  · right
    have h_diff : (b.floor - a.floor).natAbs = 1 := by omega
    have h_cases : b.floor - a.floor = 1 ∨ b.floor - a.floor = -1 := by omega
    rcases h_cases with h1 | h2
    · have h1Q : (b.floor : ℚ) - (a.floor : ℚ) = 1 := by exact_mod_cast h1
      have ha := Rat.lt_floor_add_one a
      have hb := Rat.floor_le b
      push_cast at ha hb
      have h_pos : b - a > 0 := by linarith
      simp only [h_pos, ite_true]
      omega
    · have h2Q : (b.floor : ℚ) - (a.floor : ℚ) = -1 := by exact_mod_cast h2
      have hb := Rat.lt_floor_add_one b
      have ha := Rat.floor_le a
      push_cast at ha hb
      have h_neg : b - a < 0 := by linarith
      have h_not_pos : ¬ (b - a > 0) := by linarith
      simp only [h_not_pos, h_neg, ↓reduceIte]
      omega

theorem endCell_step_cases (A B : Point32)
    (h_finA : A.isFinite) (h_finB : B.isFinite) (h_bound : inCoordBounds mainCoordBound A.toPoint B.toPoint)
    (h_dist : chebyshevDistance (floorPoint32 A) (floorPoint32 B) ≤ 1) :
    let stepX := if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0
    let stepY := if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0
    floorPoint32 B = floorPoint32 A ∨
    floorPoint32 B = ⟨(floorPoint32 A).x + stepX, (floorPoint32 A).y⟩ ∨
    floorPoint32 B = ⟨(floorPoint32 A).x, (floorPoint32 A).y + stepY⟩ ∨
    floorPoint32 B = ⟨(floorPoint32 A).x + stepX, (floorPoint32 A).y + stepY⟩ := by
  intro stepX stepY
  have h_floorA := floorPoint32_eq_floorPoint A h_finA
  have h_floorB := floorPoint32_eq_floorPoint B h_finB
  have h_stepX := step_signs_agree_X A B h_finA h_finB h_bound
  have h_stepY := step_signs_agree_Y A B h_finA h_finB h_bound
  have h_dist_ideal : chebyshevDistance (floorPoint A.toPoint) (floorPoint B.toPoint) ≤ 1 := by
    rw [← h_floorA, ← h_floorB]; exact h_dist
  unfold chebyshevDistance at h_dist_ideal
  have hx_le : ((floorPoint B.toPoint).x - (floorPoint A.toPoint).x).natAbs ≤ 1 := by
    have h1 := le_max_left ((floorPoint A.toPoint).x - (floorPoint B.toPoint).x).natAbs
                           ((floorPoint A.toPoint).y - (floorPoint B.toPoint).y).natAbs
    have h2 : ((floorPoint A.toPoint).x - (floorPoint B.toPoint).x).natAbs =
              ((floorPoint B.toPoint).x - (floorPoint A.toPoint).x).natAbs := by
      rw [← Int.natAbs_neg, neg_sub]
    omega
  have hy_le : ((floorPoint B.toPoint).y - (floorPoint A.toPoint).y).natAbs ≤ 1 := by
    have h1 := le_max_right ((floorPoint A.toPoint).x - (floorPoint B.toPoint).x).natAbs
                            ((floorPoint A.toPoint).y - (floorPoint B.toPoint).y).natAbs
    have h2 : ((floorPoint A.toPoint).y - (floorPoint B.toPoint).y).natAbs =
              ((floorPoint B.toPoint).y - (floorPoint A.toPoint).y).natAbs := by
      rw [← Int.natAbs_neg, neg_sub]
    omega
  have h_cases_x := rat_floor_step_cases A.toPoint.x B.toPoint.x hx_le
  have heq_x : (floorPoint32 B).x = (floorPoint32 A).x ∨ (floorPoint32 B).x = (floorPoint32 A).x + stepX := by
    rw [h_floorA, h_floorB]
    dsimp only [stepX]
    rw [h_stepX]
    unfold floorPoint toInt; dsimp only []
    exact h_cases_x
  have h_cases_y := rat_floor_step_cases A.toPoint.y B.toPoint.y hy_le
  have heq_y : (floorPoint32 B).y = (floorPoint32 A).y ∨ (floorPoint32 B).y = (floorPoint32 A).y + stepY := by
    rw [h_floorA, h_floorB]
    dsimp only [stepY]
    rw [h_stepY]
    unfold floorPoint toInt; dsimp only []
    exact h_cases_y
  have h_cell_B : floorPoint32 B = ⟨(floorPoint32 B).x, (floorPoint32 B).y⟩ := by cases (floorPoint32 B); rfl
  have h_cell_A : floorPoint32 A = ⟨(floorPoint32 A).x, (floorPoint32 A).y⟩ := by cases (floorPoint32 A); rfl
  rcases heq_x with hx1 | hx2 <;> rcases heq_y with hy1 | hy2
  · left; rw [h_cell_B, h_cell_A, hx1, hy1]
  · right; right; left; rw [h_cell_B, hx1, hy2]
  · right; left; rw [h_cell_B, hx2, hy1]
  · right; right; right; rw [h_cell_B, hx2, hy2]

theorem adjacent_cells_h_term_full (A B : Point32)
    (h_finA : A.isFinite) (h_finB : B.isFinite)
    (h_bound : inCoordBounds mainCoordBound A.toPoint B.toPoint)
    (h_dist : chebyshevDistance (floorPoint32 A) (floorPoint32 B) ≤ 1) :
    let startCell := floorPoint32 A
    let endCell := floorPoint32 B
    let dx := B.x - A.x
    let dy := B.y - A.y
    let stepX := if dx > 0.0 then 1 else if dx < 0.0 then -1 else 0
    let stepY := if dy > 0.0 then 1 else if dy < 0.0 then -1 else 0
    (startCell == endCell) = true ∨
    (rayMarchStepFloat A dx dy stepX stepY startCell).2 = true ∨
    (rayMarchStepFloat A dx dy stepX stepY startCell).1 = endCell ∨
    (rayMarchStepFloat A dx dy stepX stepY startCell).1 = ⟨startCell.x + stepX, startCell.y + stepY⟩ ∨
    (rayMarchStepFloat A dx dy stepX stepY (rayMarchStepFloat A dx dy stepX stepY startCell).1).2 = true ∨
    (rayMarchStepFloat A dx dy stepX stepY (rayMarchStepFloat A dx dy stepX stepY startCell).1).1 = endCell ∨
    (rayMarchStepFloat A dx dy stepX stepY (rayMarchStepFloat A dx dy stepX stepY startCell).1).1 = ⟨startCell.x + stepX, startCell.y + stepY⟩ ∨
    (rayMarchStepFloat A dx dy stepX stepY (rayMarchStepFloat A dx dy stepX stepY startCell).1).1 = ⟨startCell.x + 2 * stepX, startCell.y⟩ ∨
    (rayMarchStepFloat A dx dy stepX stepY (rayMarchStepFloat A dx dy stepX stepY startCell).1).1 = ⟨startCell.x + 2 * stepX, startCell.y + stepY⟩ ∨
    (rayMarchStepFloat A dx dy stepX stepY (rayMarchStepFloat A dx dy stepX stepY startCell).1).1 = ⟨startCell.x, startCell.y + 2 * stepY⟩ ∨
    (rayMarchStepFloat A dx dy stepX stepY (rayMarchStepFloat A dx dy stepX stepY startCell).1).1 = ⟨startCell.x + stepX, startCell.y + 2 * stepY⟩ := by
  intro startCell endCell dx dy stepX stepY
  by_cases h_same : startCell = endCell
  · left; rw [h_same]; exact beq_self_eq_true _
  · have hend_cases := endCell_step_cases A B h_finA h_finB h_bound h_dist
    have hend : endCell = ⟨startCell.x + stepX, startCell.y⟩ ∨
                endCell = ⟨startCell.x, startCell.y + stepY⟩ ∨
                endCell = ⟨startCell.x + stepX, startCell.y + stepY⟩ := by
      rcases hend_cases with h1 | h2 | h3 | h4
      · exact False.elim (h_same h1.symm)
      · left; exact h2
      · right; left; exact h3
      · right; right; exact h4
    by_cases hx0 : stepX = 0
    · have hendY : endCell = ⟨startCell.x, startCell.y + stepY⟩ := by
        rcases hend with h1 | h2 | h3
        · rw [hx0] at h1; simp only [add_zero] at h1
          have heq : endCell = startCell := by rw [h1]
          exact False.elim (h_same heq.symm)
        · exact h2
        · rw [hx0] at h3; simp only [add_zero] at h3; exact h3
      have hy0 : stepY ≠ 0 := by
        intro hy; rw [hy] at hendY; simp only [add_zero] at hendY
        have heq : endCell = startCell := by rw [hendY]
        exact h_same heq.symm
      have hstep := rayMarchStepFloat_step_cases_stepX_zero A dx dy stepY startCell hy0
      change (startCell == endCell) = true ∨ _
      rw [hx0]
      rcases hstep with h_done | h_c1
      · right; left; exact h_done
      · right; right; left; rw [hendY, h_c1]
    · by_cases hy0 : stepY = 0
      · have hendX : endCell = ⟨startCell.x + stepX, startCell.y⟩ := by
          rcases hend with h1 | h2 | h3
          · exact h1
          · rw [hy0] at h2; simp only [add_zero] at h2
            have heq : endCell = startCell := by rw [h2]
            exact False.elim (h_same heq.symm)
          · rw [hy0] at h3; simp only [add_zero] at h3; exact h3
        have hstep := rayMarchStepFloat_step_cases_stepY_zero A dx dy stepX startCell hx0
        change (startCell == endCell) = true ∨ _
        rw [hy0]
        rcases hstep with h_done | h_c1
        · right; left; exact h_done
        · right; right; left; rw [hendX, h_c1]
      · let s1 := rayMarchStepFloat A dx dy stepX stepY startCell
        have hs1 := rayMarchStepFloat_step_cases A dx dy stepX stepY startCell hx0 hy0
        rcases hs1 with h1_done | ⟨h1_x, h1_nf⟩ | ⟨h1_y, h1_nf⟩ | ⟨h1_diag, h1_nf⟩
        · right; left; exact h1_done
        · by_cases hc1_end : s1.1 = endCell
          · right; right; left; exact hc1_end
          · let s2 := rayMarchStepFloat A dx dy stepX stepY s1.1
            have hs2 := rayMarchStepFloat_step_cases A dx dy stepX stepY s1.1 hx0 hy0
            rcases hs2 with h2_done | ⟨h2_x, _⟩ | ⟨h2_y, _⟩ | ⟨h2_diag, _⟩
            · right; right; right; right; left; exact h2_done
            · right; right; right; right; right; right; right; left
              rw [h2_x, h1_x]; (apply cell_ext <;> dsimp <;> ring)
            · right; right; right; right; right; right; left
              rw [h2_y, h1_x]
            · right; right; right; right; right; right; right; right; left
              rw [h2_diag, h1_x]; (apply cell_ext <;> dsimp <;> ring)
        · by_cases hc1_end : s1.1 = endCell
          · right; right; left; exact hc1_end
          · let s2 := rayMarchStepFloat A dx dy stepX stepY s1.1
            have hs2 := rayMarchStepFloat_step_cases A dx dy stepX stepY s1.1 hx0 hy0
            rcases hs2 with h2_done | ⟨h2_x, _⟩ | ⟨h2_y, _⟩ | ⟨h2_diag, _⟩
            · right; right; right; right; left; exact h2_done
            · right; right; right; right; right; right; left
              rw [h2_x, h1_y]
            · right; right; right; right; right; right; right; right; right; left
              rw [h2_y, h1_y]; (apply cell_ext; dsimp; ring)
            · right; right; right; right; right; right; right; right; right; right
              rw [h2_diag, h1_y]; (apply cell_ext; dsimp; ring)
        · by_cases hc1_end : s1.1 = endCell
          · right; right; left; exact hc1_end
          · right; right; right; left; exact h1_diag

theorem rayMarchFloat_cases_1_to_7
    (fuel : ℕ)
    (start : Point32) (dx dy : Binary32) (stepX stepY : ℤ)
    (endCell startCell : Cell)
    (hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1) (hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1)
    (hendDiag : endCell = ⟨startCell.x + stepX, startCell.y + stepY⟩)
    (h_term : (startCell == endCell) = true ∨
              (rayMarchStepFloat start dx dy stepX stepY startCell).2 = true ∨
              (rayMarchStepFloat start dx dy stepX stepY startCell).1 = endCell ∨
              (rayMarchStepFloat start dx dy stepX stepY (rayMarchStepFloat start dx dy stepX stepY startCell).1).2 = true ∨
              (rayMarchStepFloat start dx dy stepX stepY (rayMarchStepFloat start dx dy stepX stepY startCell).1).1 = endCell ∨
              (rayMarchStepFloat start dx dy stepX stepY (rayMarchStepFloat start dx dy stepX stepY startCell).1).1 = ⟨startCell.x + stepX, startCell.y + stepY⟩)
    (c : Cell)
    (hc : c ∈ rayMarchFloat fuel start dx dy stepX stepY endCell startCell []) :
    chebyshevDistance c startCell ≤ 1 ∨ chebyshevDistance c endCell ≤ 1 := by
  cases fuel with
  | zero => unfold rayMarchFloat at hc; cases hc
  | succ fuel =>
    rw [rayMarchFloat_succ] at hc; dsimp only [] at hc
    split_ifs at hc with h_end1 h_done1
    · cases hc
    · cases hc
    · rcases h_term with h_end | h_done_true | h_next_end | h_next2_done | h_next2_end | h_next2_diag
      · exfalso; apply h_end1; exact h_end
      · exfalso; apply h_done1; exact h_done_true
      · rw [h_next_end, rayMarchFloat_endCell] at hc
        simp only [List.mem_singleton] at hc
        subst c
        right; rw [chebyshevDistance_self]; omega
      · simp only [List.mem_cons] at hc
        rcases hc with rfl | htail
        · have h_step := chebyshevDistance_stepFloat_le_one start dx dy stepX stepY hX hY startCell
          left; rw [chebyshevDistance_symm]; exact h_step
        · cases fuel with
          | zero => unfold rayMarchFloat at htail; cases htail
          | succ fuel =>
            rw [rayMarchFloat_succ] at htail; dsimp only [] at htail
            rw [h_next2_done] at htail
            split_ifs at htail with h_end2 h_done2
            · cases htail
            · cases htail
            · exfalso; apply h_done2; rfl
      · simp only [List.mem_cons] at hc
        rcases hc with rfl | htail
        · have h_step := chebyshevDistance_stepFloat_le_one start dx dy stepX stepY hX hY startCell
          left; rw [chebyshevDistance_symm]; exact h_step
        · cases fuel with
          | zero => unfold rayMarchFloat at htail; cases htail
          | succ fuel =>
            rw [rayMarchFloat_succ] at htail; dsimp only [] at htail
            split_ifs at htail with h_end2 h_done2
            · cases htail
            · cases htail
            · simp only [List.mem_cons] at htail
              rcases htail with rfl | htail2
              · right; rw [h_next2_end, chebyshevDistance_self]; omega
              · rw [h_next2_end, rayMarchFloat_endCell] at htail2
                cases htail2
      · simp only [List.mem_cons] at hc
        rcases hc with rfl | htail
        · have h_step := chebyshevDistance_stepFloat_le_one start dx dy stepX stepY hX hY startCell
          left; rw [chebyshevDistance_symm]; exact h_step
        · cases fuel with
          | zero => unfold rayMarchFloat at htail; cases htail
          | succ fuel =>
            rw [rayMarchFloat_succ] at htail; dsimp only [] at htail
            split_ifs at htail with h_end2 h_done2
            · cases htail
            · cases htail
            · simp only [List.mem_cons] at htail
              rcases htail with rfl | htail2
              · right; rw [h_next2_diag, hendDiag, chebyshevDistance_self]; omega
              · rw [h_next2_diag, hendDiag, rayMarchFloat_endCell] at htail2
                cases htail2

theorem rayMarchFloat_cells_near_endpoints_stepY_zero
    (fuel : ℕ)
    (start : Point32) (dx dy : Binary32) (stepX : ℤ)
    (endCell startCell : Cell)
    (hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1)
    (he1 : endCell = ⟨startCell.x + stepX, startCell.y⟩)
    (hx0 : stepX ≠ 0)
    (c : Cell)
    (hc : c ∈ rayMarchFloat fuel start dx dy stepX 0 endCell startCell []) :
    chebyshevDistance c startCell ≤ 1 ∨ chebyshevDistance c endCell ≤ 1 := by
  have hstep := rayMarchStepFloat_step_cases_stepY_zero start dx dy stepX startCell hx0
  cases fuel with
  | zero => unfold rayMarchFloat at hc; cases hc
  | succ fuel =>
    rw [rayMarchFloat_succ] at hc; dsimp only [] at hc
    split_ifs at hc with h_end1 h_done1
    · cases hc
    · cases hc
    · simp only [List.mem_cons] at hc
      rcases hc with rfl | htail
      · have h_step_one := chebyshevDistance_stepFloat_le_one start dx dy stepX 0 hX (by simp) startCell
        left; rw [chebyshevDistance_symm]; exact h_step_one
      · rcases hstep with h_done | h_end
        · exfalso; apply h_done1; exact h_done
        · rw [h_end, ← he1] at htail
          rw [rayMarchFloat_endCell] at htail
          cases htail

theorem rayMarchFloat_cells_near_endpoints_stepX_zero
    (fuel : ℕ)
    (start : Point32) (dx dy : Binary32) (stepY : ℤ)
    (endCell startCell : Cell)
    (hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1)
    (he2 : endCell = ⟨startCell.x, startCell.y + stepY⟩)
    (hy0 : stepY ≠ 0)
    (c : Cell)
    (hc : c ∈ rayMarchFloat fuel start dx dy 0 stepY endCell startCell []) :
    chebyshevDistance c startCell ≤ 1 ∨ chebyshevDistance c endCell ≤ 1 := by
  have hstep := rayMarchStepFloat_step_cases_stepX_zero start dx dy stepY startCell hy0
  cases fuel with
  | zero => unfold rayMarchFloat at hc; cases hc
  | succ fuel =>
    rw [rayMarchFloat_succ] at hc; dsimp only [] at hc
    split_ifs at hc with h_end1 h_done1
    · cases hc
    · cases hc
    · simp only [List.mem_cons] at hc
      rcases hc with rfl | htail
      · have h_step_one := chebyshevDistance_stepFloat_le_one start dx dy 0 stepY (by simp) hY startCell
        left; rw [chebyshevDistance_symm]; exact h_step_one
      · rcases hstep with h_done | h_end
        · exfalso; apply h_done1; exact h_done
        · rw [h_end, ← he2] at htail
          rw [rayMarchFloat_endCell] at htail
          cases htail

theorem cellHausdorffDistanceLe_of_subset_near_endpoints
    (l1 l2 : List Cell) (anchorA anchorB : Cell)
    (h1A : anchorA ∈ l1) (h2A : anchorA ∈ l2) (h2B : anchorB ∈ l2)
    (b1 : ∀ c ∈ l1, chebyshevDistance c anchorA ≤ 1 ∨ chebyshevDistance c anchorB ≤ 1)
    (b2 : ∀ c ∈ l2, chebyshevDistance c anchorA ≤ 1) :
    cellHausdorffDistanceLe l1 l2 1 := by
  constructor
  · intro c1 hc1
    rcases b1 c1 hc1 with hdA | hdB
    · exact ⟨anchorA, h2A, hdA⟩
    · exact ⟨anchorB, h2B, hdB⟩
  · intro c2 hc2
    exact ⟨anchorA, h1A, by rw [chebyshevDistance_symm]; exact b2 c2 hc2⟩

theorem cellIntersectionsSegmentFloat_contains_start (A B : Point32) :
    floorPoint32 A ∈ cellIntersectionsSegmentFloat A B := by
  unfold cellIntersectionsSegmentFloat; dsimp only []
  cases h : (floorPoint32 A == floorPoint32 B)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [mem_dedupCells]
    simp only [List.mem_append, List.mem_cons, true_or]
  · simp only [ite_true, List.mem_singleton]

theorem cellIntersectionsSegment_contains_start (A B : Point) :
    floorPoint A ∈ cellIntersectionsSegment A B := by
  unfold cellIntersectionsSegment; dsimp only []
  cases h : (floorPoint A == floorPoint B)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [mem_dedupCells]
    simp only [List.mem_append, List.mem_cons, true_or]
  · simp only [ite_true, List.mem_singleton]

theorem rayMarchFloat_cells_near_endpoints_2stepX_stepY
    (fuel : ℕ) (h_fuel : fuel ≤ 4)
    (A : Point32) (dx dy : Binary32) (stepX stepY : ℤ)
    (endCell startCell : Cell)
    (hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1) (hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1)
    (hX_diag : stepX = -1 ∨ stepX = 1) (hY_diag : stepY = -1 ∨ stepY = 1)
    (he3 : endCell = ⟨startCell.x + stepX, startCell.y + stepY⟩)
    (h8 : (rayMarchStepFloat A dx dy stepX stepY (rayMarchStepFloat A dx dy stepX stepY startCell).1).1 =
           ⟨startCell.x + 2 * stepX, startCell.y⟩)
    (hs2_done_or_step :
      (rayMarchStepFloat A dx dy stepX stepY (rayMarchStepFloat A dx dy stepX stepY startCell).1).2 = true ∨
      (rayMarchStepFloat A dx dy stepX stepY ⟨startCell.x + 2 * stepX, startCell.y⟩).2 = true ∨
      (rayMarchStepFloat A dx dy stepX stepY ⟨startCell.x + 2 * stepX, startCell.y⟩).1 =
        ⟨startCell.x + 2 * stepX, startCell.y + stepY⟩)
    (hs3_step :
      (rayMarchStepFloat A dx dy stepX stepY ⟨startCell.x + 2 * stepX, startCell.y + stepY⟩).1 =
        ⟨startCell.x + 2 * stepX, startCell.y + stepY⟩ ∨
      (rayMarchStepFloat A dx dy stepX stepY ⟨startCell.x + 2 * stepX, startCell.y + stepY⟩).1 =
        ⟨startCell.x + 2 * stepX, startCell.y + 2 * stepY⟩)
    (c : Cell)
    (hc : c ∈ rayMarchFloat fuel A dx dy stepX stepY endCell startCell []) :
    chebyshevDistance c startCell ≤ 1 ∨ chebyshevDistance c endCell ≤ 1 := by
  cases h_f0 : fuel with
  | zero => rw [h_f0] at hc; unfold rayMarchFloat at hc; cases hc
  | succ f1 =>
    rw [h_f0, rayMarchFloat_succ] at hc; dsimp only [] at hc
    split_ifs at hc with h_end1 h_done1
    · cases hc
    · cases hc
    · simp only [List.mem_cons] at hc
      rcases hc with rfl | htail
      · have h_step := chebyshevDistance_stepFloat_le_one A dx dy stepX stepY hX hY startCell
        left; rw [chebyshevDistance_symm]; exact h_step
      · cases h_f1 : f1 with
        | zero => rw [h_f1] at htail; unfold rayMarchFloat at htail; cases htail
        | succ f2 =>
          rw [h_f1, rayMarchFloat_succ] at htail; dsimp only [] at htail
          rcases hs2_done_or_step with hs2_done | hs3_done_imm | hs2_step_eq
          · rw [hs2_done] at htail
            split_ifs at htail with h_end2 h_done2
            · cases htail
            · cases htail
            · exfalso; apply h_done2; rfl
          · split_ifs at htail with h_end2 h_done2
            · cases htail
            · cases htail
            · simp only [List.mem_cons] at htail
              rcases htail with rfl | htail2
              · right; rw [h8]
                exact chebyshevDistance_candidates_diag_endCell_le_one startCell stepX stepY hX_diag hY_diag endCell he3 _ (Or.inl rfl)
              · cases h_f2 : f2 with
                | zero => rw [h_f2] at htail2; unfold rayMarchFloat at htail2; cases htail2
                | succ f3 =>
                  rw [h_f2, rayMarchFloat_succ] at htail2; dsimp only [] at htail2
                  rw [h8, hs3_done_imm] at htail2
                  split_ifs at htail2 with h_end3 h_done3
                  · cases htail2
                  · cases htail2
                  · exfalso; apply h_done3; rfl
          · split_ifs at htail with h_end2 h_done2
            · cases htail
            · cases htail
            · simp only [List.mem_cons] at htail
              rcases htail with rfl | htail2
              · right; rw [h8]
                exact chebyshevDistance_candidates_diag_endCell_le_one startCell stepX stepY hX_diag hY_diag endCell he3 _ (Or.inl rfl)
              · cases h_f2 : f2 with
                | zero => rw [h_f2] at htail2; unfold rayMarchFloat at htail2; cases htail2
                | succ f3 =>
                  rw [h_f2, rayMarchFloat_succ] at htail2; dsimp only [] at htail2
                  rw [h8, hs2_step_eq] at htail2
                  split_ifs at htail2 with h_end3 h_done3
                  · cases htail2
                  · cases htail2
                  · simp only [List.mem_cons] at htail2
                    rcases htail2 with rfl | htail3
                    · right
                      exact chebyshevDistance_candidates_diag_endCell_le_one startCell stepX stepY hX_diag hY_diag endCell he3 _ (Or.inr (Or.inl rfl))
                    · cases h_f3 : f3 with
                      | zero => rw [h_f3] at htail3; unfold rayMarchFloat at htail3; cases htail3
                      | succ f4 =>
                        rw [h_f3, rayMarchFloat_succ] at htail3; dsimp only [] at htail3
                        rcases hs3_step with hs3_eq1 | hs3_eq2
                        · rw [hs3_eq1] at htail3
                          split_ifs at htail3 with h_end4 h_done4
                          · cases htail3
                          · cases htail3
                          · simp only [List.mem_cons] at htail3
                            rcases htail3 with rfl | htail4
                            · right; exact chebyshevDistance_candidates_diag_endCell_le_one startCell stepX stepY hX_diag hY_diag endCell he3 _ (Or.inr (Or.inl rfl))
                            · cases f4 with
                              | zero =>
                                subst h_f0 h_f1 h_f2 h_f3
                                unfold rayMarchFloat at htail4; cases htail4
                              | succ f5 => exfalso; omega
                        · rw [hs3_eq2] at htail3
                          split_ifs at htail3 with h_end4 h_done4
                          · cases htail3
                          · cases htail3
                          · simp only [List.mem_cons] at htail3
                            rcases htail3 with rfl | htail4
                            · right; exact chebyshevDistance_candidates_diag_endCell_le_one startCell stepX stepY hX_diag hY_diag endCell he3 _ (Or.inr (Or.inr (Or.inl rfl)))
                            · cases f4 with
                              | zero =>
                                subst h_f0 h_f1 h_f2 h_f3
                                unfold rayMarchFloat at htail4; cases htail4
                              | succ f5 => exfalso; omega

theorem rayMarchFloat_cells_near_endpoints_2stepX_term
    (fuel : ℕ) (h_fuel : fuel ≤ 4)
    (start : Point32) (dx dy : Binary32) (stepX stepY : ℤ)
    (endCell startCell : Cell)
    (hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1) (hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1)
    (he3 : endCell = ⟨startCell.x + stepX, startCell.y + stepY⟩)
    (h8 : (rayMarchStepFloat start dx dy stepX stepY (rayMarchStepFloat start dx dy stepX stepY startCell).1).1 =
           ⟨startCell.x + 2 * stepX, startCell.y⟩)
    (hs2_done_or_step :
      (rayMarchStepFloat start dx dy stepX stepY (rayMarchStepFloat start dx dy stepX stepY startCell).1).2 = true ∨
      (rayMarchStepFloat start dx dy stepX stepY ⟨startCell.x + 2 * stepX, startCell.y⟩).2 = true ∨
      (rayMarchStepFloat start dx dy stepX stepY ⟨startCell.x + 2 * stepX, startCell.y⟩).1 =
        ⟨startCell.x + 2 * stepX, startCell.y + stepY⟩)
    (hs3_done : (rayMarchStepFloat start dx dy stepX stepY ⟨startCell.x + 2 * stepX, startCell.y + stepY⟩).2 = true)
    (c : Cell)
    (hc : c ∈ rayMarchFloat fuel start dx dy stepX stepY endCell startCell []) :
    chebyshevDistance c startCell ≤ 1 ∨ chebyshevDistance c endCell ≤ 1 := by
  cases h_f0 : fuel with
  | zero => rw [h_f0] at hc; unfold rayMarchFloat at hc; cases hc
  | succ f1 =>
    rw [h_f0, rayMarchFloat_succ] at hc; dsimp only [] at hc
    split_ifs at hc with h_end1 h_done1
    · cases hc
    · cases hc
    · simp only [List.mem_cons] at hc
      rcases hc with rfl | htail
      · have h_step := chebyshevDistance_stepFloat_le_one start dx dy stepX stepY hX hY startCell
        left; rw [chebyshevDistance_symm]; exact h_step
      · cases h_f1 : f1 with
        | zero => rw [h_f1] at htail; unfold rayMarchFloat at htail; cases htail
        | succ f2 =>
          rw [h_f1, rayMarchFloat_succ] at htail; dsimp only [] at htail
          rcases hs2_done_or_step with hs2_done | hs3_done_imm | hs3_step
          · rw [hs2_done] at htail
            split_ifs at htail with h_end2 h_done2
            · cases htail
            · cases htail
            · exfalso; apply h_done2; rfl
          · split_ifs at htail with h_end2 h_done2
            · cases htail
            · cases htail
            · simp only [List.mem_cons] at htail
              rcases htail with rfl | htail2
              · right; rw [h8]
                exact (chebyshevDistance_2x_end_le_one startCell stepX stepY hX hY he3).1
              · cases h_f2 : f2 with
                | zero => rw [h_f2] at htail2; unfold rayMarchFloat at htail2; cases htail2
                | succ f3 =>
                  rw [h_f2, rayMarchFloat_succ] at htail2; dsimp only [] at htail2
                  rw [h8, hs3_done_imm] at htail2
                  split_ifs at htail2 with h_end3 h_done3
                  · cases htail2
                  · cases htail2
                  · exfalso; apply h_done3; rfl
          · split_ifs at htail with h_end2 h_done2
            · cases htail
            · cases htail
            · simp only [List.mem_cons] at htail
              rcases htail with rfl | htail2
              · right; rw [h8]
                exact (chebyshevDistance_2x_end_le_one startCell stepX stepY hX hY he3).1
              · cases h_f2 : f2 with
                | zero => rw [h_f2] at htail2; unfold rayMarchFloat at htail2; cases htail2
                | succ f3 =>
                  rw [h_f2, rayMarchFloat_succ] at htail2; dsimp only [] at htail2
                  rw [h8, hs3_step] at htail2
                  split_ifs at htail2 with h_end3 h_done3
                  · cases htail2
                  · cases htail2
                  · simp only [List.mem_cons] at htail2
                    rcases htail2 with rfl | htail3
                    · right; exact chebyshevDistance_2x_stepY_endCell_le_one startCell stepX stepY hX hY endCell he3
                    · cases h_f3 : f3 with
                      | zero => rw [h_f3] at htail3; unfold rayMarchFloat at htail3; cases htail3
                      | succ f4 =>
                        rw [h_f3, rayMarchFloat_succ] at htail3; dsimp only [] at htail3
                        rw [hs3_done] at htail3
                        split_ifs at htail3 with h_end4 h_done4
                        · cases htail3
                        · cases htail3
                        · exfalso; apply h_done4; rfl

theorem rayMarchFloat_cells_near_endpoints_2stepX_stepY_term
    (fuel : ℕ)
    (A : Point32) (dx dy : Binary32) (stepX stepY : ℤ)
    (endCell startCell : Cell)
    (hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1) (hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1)
    (he3 : endCell = ⟨startCell.x + stepX, startCell.y + stepY⟩)
    (h9 : (rayMarchStepFloat A dx dy stepX stepY (rayMarchStepFloat A dx dy stepX stepY startCell).1).1 =
           ⟨startCell.x + 2 * stepX, startCell.y + stepY⟩)
    (hs2_done :
      (rayMarchStepFloat A dx dy stepX stepY (rayMarchStepFloat A dx dy stepX stepY startCell).1).2 = true ∨
      (rayMarchStepFloat A dx dy stepX stepY ⟨startCell.x + 2 * stepX, startCell.y + stepY⟩).2 = true)
    (c : Cell)
    (hc : c ∈ rayMarchFloat fuel A dx dy stepX stepY endCell startCell []) :
    chebyshevDistance c startCell ≤ 1 ∨ chebyshevDistance c endCell ≤ 1 := by
  cases fuel with
  | zero => unfold rayMarchFloat at hc; cases hc
  | succ f1 =>
    rw [rayMarchFloat_succ] at hc; dsimp only [] at hc
    split_ifs at hc with h_end1 h_done1
    · cases hc
    · cases hc
    · simp only [List.mem_cons] at hc
      rcases hc with rfl | htail
      · have h_step := chebyshevDistance_stepFloat_le_one A dx dy stepX stepY hX hY startCell
        left; rw [chebyshevDistance_symm]; exact h_step
      · cases f1 with
        | zero => unfold rayMarchFloat at htail; cases htail
        | succ f2 =>
          rw [rayMarchFloat_succ] at htail; dsimp only [] at htail
          rcases hs2_done with hs2_done1 | hs2_done2
          · rw [hs2_done1] at htail
            split_ifs at htail with h_end2 h_done2
            · cases htail
            · cases htail
            · exfalso; apply h_done2; rfl
          · split_ifs at htail with h_end2 h_done2
            · cases htail
            · cases htail
            · simp only [List.mem_cons] at htail
              rcases htail with rfl | htail2
              · right; rw [h9]
                exact (chebyshevDistance_2x_end_le_one startCell stepX stepY hX hY he3).2.1
              · cases f2 with
                | zero => unfold rayMarchFloat at htail2; cases htail2
                | succ f3 =>
                  rw [rayMarchFloat_succ] at htail2; dsimp only [] at htail2
                  rw [h9, hs2_done2] at htail2
                  split_ifs at htail2 with h_end3 h_done3
                  · cases htail2
                  · cases htail2
                  · exfalso; apply h_done3; rfl

abbrev rayMarchFloat_cells_near_endpoints_2stepX_stepY_term_fuel4 := @rayMarchFloat_cells_near_endpoints_2stepX_stepY_term

theorem rayMarchFloat_cells_near_endpoints_2stepY_stepX
    (fuel : ℕ)
    (A : Point32) (dx dy : Binary32) (stepX stepY : ℤ)
    (endCell startCell : Cell)
    (hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1) (hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1)
    (hendDiag : endCell = ⟨startCell.x + stepX, startCell.y + stepY⟩)
    (h10 : (rayMarchStepFloat A dx dy stepX stepY (rayMarchStepFloat A dx dy stepX stepY startCell).1).1 =
           ⟨startCell.x, startCell.y + 2 * stepY⟩)
    (hs2_done :
      (rayMarchStepFloat A dx dy stepX stepY (rayMarchStepFloat A dx dy stepX stepY startCell).1).2 = true ∨
      (rayMarchStepFloat A dx dy stepX stepY ⟨startCell.x, startCell.y + 2 * stepY⟩).2 = true ∨
      (rayMarchStepFloat A dx dy stepX stepY ⟨startCell.x, startCell.y + 2 * stepY⟩).1 =
        ⟨startCell.x + stepX, startCell.y + 2 * stepY⟩)
    (hs3_done : (rayMarchStepFloat A dx dy stepX stepY ⟨startCell.x + stepX, startCell.y + 2 * stepY⟩).2 = true)
    (c : Cell)
    (hc : c ∈ rayMarchFloat fuel A dx dy stepX stepY endCell startCell []) :
    chebyshevDistance c startCell ≤ 1 ∨ chebyshevDistance c endCell ≤ 1 := by
  cases fuel with
  | zero => unfold rayMarchFloat at hc; cases hc
  | succ f1 =>
    rw [rayMarchFloat_succ] at hc; dsimp only [] at hc
    split_ifs at hc with h_end1 h_done1
    · cases hc
    · cases hc
    · simp only [List.mem_cons] at hc
      rcases hc with rfl | htail
      · have h_step := chebyshevDistance_stepFloat_le_one A dx dy stepX stepY hX hY startCell
        left; rw [chebyshevDistance_symm]; exact h_step
      · cases f1 with
        | zero => unfold rayMarchFloat at htail; cases htail
        | succ f2 =>
          rw [rayMarchFloat_succ] at htail; dsimp only [] at htail
          split_ifs at htail with h_end2 h_done2
          · cases htail
          · cases htail
          · simp only [List.mem_cons] at htail
            rcases htail with rfl | htail2
            · right; rw [h10]
              exact (chebyshevDistance_2x_end_le_one startCell stepX stepY hX hY hendDiag).2.2.1
            · rw [h10] at htail2
              rcases hs2_done with h_d2 | h_d3 | h_s3
              · exfalso; apply h_done2; exact h_d2
              · cases f2 with
                | zero => unfold rayMarchFloat at htail2; cases htail2
                | succ f3 =>
                  rw [rayMarchFloat_succ] at htail2; dsimp only [] at htail2
                  rw [h_d3] at htail2
                  split_ifs at htail2 with h_end3 h_done3
                  · cases htail2
                  · cases htail2
                  · exfalso; apply h_done3; rfl
              · cases f2 with
                | zero => unfold rayMarchFloat at htail2; cases htail2
                | succ f3 =>
                  rw [rayMarchFloat_succ] at htail2; dsimp only [] at htail2
                  rw [h_s3] at htail2
                  split_ifs at htail2 with h_end3 h_done3
                  · cases htail2
                  · cases htail2
                  · simp only [List.mem_cons] at htail2
                    rcases htail2 with rfl | htail3
                    · right
                      exact (chebyshevDistance_2x_end_le_one startCell stepX stepY hX hY hendDiag).2.2.2
                    · cases f3 with
                      | zero => unfold rayMarchFloat at htail3; cases htail3
                      | succ f4 =>
                        rw [rayMarchFloat_succ] at htail3; dsimp only [] at htail3
                        rw [hs3_done] at htail3
                        split_ifs at htail3 with h_end4 h_done4
                        · cases htail3
                        · cases htail3
                        · exfalso; apply h_done4; rfl

theorem rayMarchFloat_cells_near_endpoints_stepX_2stepY_term
    (fuel : ℕ)
    (A : Point32) (dx dy : Binary32) (stepX stepY : ℤ)
    (endCell startCell : Cell)
    (hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1) (hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1)
    (hendDiag : endCell = ⟨startCell.x + stepX, startCell.y + stepY⟩)
    (h11 : (rayMarchStepFloat A dx dy stepX stepY (rayMarchStepFloat A dx dy stepX stepY startCell).1).1 =
           ⟨startCell.x + stepX, startCell.y + 2 * stepY⟩)
    (hs2_done :
      (rayMarchStepFloat A dx dy stepX stepY (rayMarchStepFloat A dx dy stepX stepY startCell).1).2 = true ∨
      (rayMarchStepFloat A dx dy stepX stepY ⟨startCell.x + stepX, startCell.y + 2 * stepY⟩).2 = true)
    (c : Cell)
    (hc : c ∈ rayMarchFloat fuel A dx dy stepX stepY endCell startCell []) :
    chebyshevDistance c startCell ≤ 1 ∨ chebyshevDistance c endCell ≤ 1 := by
  cases fuel with
  | zero => unfold rayMarchFloat at hc; cases hc
  | succ f1 =>
    rw [rayMarchFloat_succ] at hc; dsimp only [] at hc
    split_ifs at hc with h_end1 h_done1
    · cases hc
    · cases hc
    · simp only [List.mem_cons] at hc
      rcases hc with rfl | htail
      · have h_step := chebyshevDistance_stepFloat_le_one A dx dy stepX stepY hX hY startCell
        left; rw [chebyshevDistance_symm]; exact h_step
      · cases f1 with
        | zero => unfold rayMarchFloat at htail; cases htail
        | succ f2 =>
          rw [rayMarchFloat_succ] at htail; dsimp only [] at htail
          rcases hs2_done with hs2_done1 | hs2_done2
          · rw [hs2_done1] at htail
            split_ifs at htail with h_end2 h_done2
            · cases htail
            · cases htail
            · exfalso; apply h_done2; rfl
          · split_ifs at htail with h_end2 h_done2
            · cases htail
            · cases htail
            · simp only [List.mem_cons] at htail
              rcases htail with rfl | htail2
              · right; rw [h11]
                exact (chebyshevDistance_2x_end_le_one startCell stepX stepY hX hY hendDiag).2.2.2
              · cases f2 with
                | zero => unfold rayMarchFloat at htail2; cases htail2
                | succ f3 =>
                  rw [rayMarchFloat_succ] at htail2; dsimp only [] at htail2
                  rw [h11, hs2_done2] at htail2
                  split_ifs at htail2 with h_end3 h_done3
                  · cases htail2
                  · cases htail2
                  · exfalso; apply h_done3; rfl

theorem rayMarchFloat_cells_near_endpoints_axial_X
    (fuel : ℕ)
    (A : Point32) (dx dy : Binary32) (stepX stepY : ℤ)
    (endCell startCell : Cell)
    (hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1) (hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1)
    (he1 : endCell = ⟨startCell.x + stepX, startCell.y⟩)
    (hs1_step :
      (rayMarchStepFloat A dx dy stepX stepY startCell).2 = true ∨
      (rayMarchStepFloat A dx dy stepX stepY startCell).1 = endCell)
    (c : Cell)
    (hc : c ∈ rayMarchFloat fuel A dx dy stepX stepY endCell startCell []) :
    chebyshevDistance c startCell ≤ 1 ∨ chebyshevDistance c endCell ≤ 1 := by
  cases fuel with
  | zero => unfold rayMarchFloat at hc; cases hc
  | succ f1 =>
    rw [rayMarchFloat_succ] at hc; dsimp only [] at hc
    split_ifs at hc with h_end1 h_done1
    · cases hc
    · cases hc
    · simp only [List.mem_cons] at hc
      rcases hc with rfl | htail
      · have h_step := chebyshevDistance_stepFloat_le_one A dx dy stepX stepY hX hY startCell
        left; rw [chebyshevDistance_symm]; exact h_step
      · rcases hs1_step with h_d1 | h_e1
        · exfalso; apply h_done1; exact h_d1
        · rw [h_e1, rayMarchFloat_endCell] at htail; cases htail

theorem rayMarchFloat_cells_near_endpoints_axial_Y
    (fuel : ℕ)
    (A : Point32) (dx dy : Binary32) (stepX stepY : ℤ)
    (endCell startCell : Cell)
    (hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1) (hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1)
    (he2 : endCell = ⟨startCell.x, startCell.y + stepY⟩)
    (hs1_step :
      (rayMarchStepFloat A dx dy stepX stepY startCell).2 = true ∨
      (rayMarchStepFloat A dx dy stepX stepY startCell).1 = endCell)
    (c : Cell)
    (hc : c ∈ rayMarchFloat fuel A dx dy stepX stepY endCell startCell []) :
    chebyshevDistance c startCell ≤ 1 ∨ chebyshevDistance c endCell ≤ 1 := by
  cases fuel with
  | zero => unfold rayMarchFloat at hc; cases hc
  | succ f1 =>
    rw [rayMarchFloat_succ] at hc; dsimp only [] at hc
    split_ifs at hc with h_end1 h_done1
    · cases hc
    · cases hc
    · simp only [List.mem_cons] at hc
      rcases hc with rfl | htail
      · have h_step := chebyshevDistance_stepFloat_le_one A dx dy stepX stepY hX hY startCell
        left; rw [chebyshevDistance_symm]; exact h_step
      · rcases hs1_step with h_d1 | h_e1
        · exfalso; apply h_done1; exact h_d1
        · rw [h_e1, rayMarchFloat_endCell] at htail; cases htail


theorem cellIntersectionsSegmentFloat_cells_near_endpoints_Impl
    (A B : Point32) (h_finA : A.isFinite) (h_finB : B.isFinite)
    (h_bound : inCoordBounds mainCoordBound A.toPoint B.toPoint)
    (h_dist : chebyshevDistance (floorPoint32 A) (floorPoint32 B) ≤ 1)
    (h_step_axial_X :
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y)
        (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0)
        (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0) (floorPoint32 A)).2 = true ∨
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y)
        (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0)
        (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0) (floorPoint32 A)).1 = floorPoint32 B)
    (h_step_axial_Y :
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y)
        (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0)
        (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0) (floorPoint32 A)).2 = true ∨
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y)
        (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0)
        (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0) (floorPoint32 A)).1 = floorPoint32 B)
    (h_case8_hs2 :
      let stepX := if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0
      let stepY := if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY
        (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY (floorPoint32 A)).1).2 = true ∨
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY ⟨(floorPoint32 A).x + 2 * stepX, (floorPoint32 A).y⟩).2 = true ∨
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY ⟨(floorPoint32 A).x + 2 * stepX, (floorPoint32 A).y⟩).1 =
        ⟨(floorPoint32 A).x + 2 * stepX, (floorPoint32 A).y + stepY⟩)
    (h_case8_hs3 :
      let stepX := if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0
      let stepY := if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY
        ⟨(floorPoint32 A).x + 2 * stepX, (floorPoint32 A).y + stepY⟩).2 = true)
    (h_case9_hs2 :
      let stepX := if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0
      let stepY := if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY
        (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY (floorPoint32 A)).1).2 = true ∨
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY ⟨(floorPoint32 A).x + 2 * stepX, (floorPoint32 A).y + stepY⟩).2 = true)
    (h_case10_hs2 :
      let stepX := if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0
      let stepY := if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY
        (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY (floorPoint32 A)).1).2 = true ∨
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY ⟨(floorPoint32 A).x, (floorPoint32 A).y + 2 * stepY⟩).2 = true ∨
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY ⟨(floorPoint32 A).x, (floorPoint32 A).y + 2 * stepY⟩).1 =
        ⟨(floorPoint32 A).x + stepX, (floorPoint32 A).y + 2 * stepY⟩)
    (h_case10_hs3 :
      let stepX := if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0
      let stepY := if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY
        ⟨(floorPoint32 A).x + stepX, (floorPoint32 A).y + 2 * stepY⟩).2 = true)
    (h_case11_hs2 :
      let stepX := if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0
      let stepY := if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY
        (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY (floorPoint32 A)).1).2 = true ∨
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY ⟨(floorPoint32 A).x + stepX, (floorPoint32 A).y + 2 * stepY⟩).2 = true) :
    ∀ c ∈ cellIntersectionsSegmentFloat A B,
      chebyshevDistance c (floorPoint32 A) ≤ 1 ∨ chebyshevDistance c (floorPoint32 B) ≤ 1 := by
  intro c hc
  unfold cellIntersectionsSegmentFloat at hc
  dsimp only [] at hc
  cases h_same : (floorPoint32 A == floorPoint32 B)
  · rw [h_same] at hc
    simp only [Bool.false_eq_true, ↓reduceIte] at hc
    rw [mem_dedupCells] at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl) | hray
    · left; rw [chebyshevDistance_self]; omega
    · right; rw [chebyshevDistance_self]; omega
    · let startCell := floorPoint32 A
      let endCell := floorPoint32 B
      let dx := B.x - A.x
      let dy := B.y - A.y
      let stepX := if dx > 0.0 then 1 else if dx < 0.0 then -1 else 0
      let stepY := if dy > 0.0 then 1 else if dy < 0.0 then -1 else 0
      have hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1 := by
        dsimp only [stepX]; split_ifs <;> simp
      have hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1 := by
        dsimp only [stepY]; split_ifs <;> simp
      let fuel := (endCell.x - startCell.x).natAbs + (endCell.y - startCell.y).natAbs + 2
      change chebyshevDistance c startCell ≤ 1 ∨ chebyshevDistance c endCell ≤ 1
      have h_fuel : fuel ≤ 4 := rayMarch_fuel_bound_le_four_of_adjacent startCell endCell h_dist
      have h_term := adjacent_cells_h_term_full A B h_finA h_finB h_bound h_dist
      have hend_cases := endCell_step_cases A B h_finA h_finB h_bound h_dist
      have h_ne : startCell ≠ endCell := by
        intro h
        have heq : (startCell == endCell) = (floorPoint32 A == floorPoint32 B) := rfl
        rw [← heq, h, beq_self_eq_true] at h_same
        contradiction
      have hend : endCell = ⟨startCell.x + stepX, startCell.y⟩ ∨
                  endCell = ⟨startCell.x, startCell.y + stepY⟩ ∨
                  endCell = ⟨startCell.x + stepX, startCell.y + stepY⟩ := by
        rcases hend_cases with h1 | h2 | h3 | h4
        · exact False.elim (h_ne h1.symm)
        · left; exact h2
        · right; left; exact h3
        · right; right; exact h4
      dsimp only [startCell, endCell, dx, dy, stepX, stepY] at h_term
      rcases hend with he1 | he2 | he3
      · -- he1 : endCell = ⟨startCell.x + stepX, startCell.y⟩
        by_cases hy0 : stepY = 0
        · have hx0 : stepX ≠ 0 := by
            intro hx; rw [hx] at he1
            have : endCell = startCell := by rw [he1]; apply cell_ext <;> dsimp <;> ring
            exact h_ne this.symm
          have hstepY_eq : (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0) = stepY := rfl
          have hstepX_eq : (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0) = stepX := rfl
          rw [hstepY_eq, hstepX_eq, hy0] at hray
          exact rayMarchFloat_cells_near_endpoints_stepY_zero fuel A dx dy stepX endCell startCell hX he1 hx0 c hray
        · have hstepX_eq : (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0) = stepX := rfl
          have hstepY_eq : (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0) = stepY := rfl
          rw [hstepX_eq, hstepY_eq] at hray
          exact rayMarchFloat_cells_near_endpoints_axial_X fuel A dx dy stepX stepY endCell startCell hX hY he1 h_step_axial_X c hray
      · -- he2 : endCell = ⟨startCell.x, startCell.y + stepY⟩
        by_cases hx0 : stepX = 0
        · have hy0 : stepY ≠ 0 := by
            intro hy; rw [hy] at he2
            have : endCell = startCell := by rw [he2]; apply cell_ext <;> dsimp <;> omega
            exact h_ne this.symm
          have hstepX_eq : (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0) = stepX := rfl
          have hstepY_eq : (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0) = stepY := rfl
          rw [hstepX_eq, hstepY_eq, hx0] at hray
          exact rayMarchFloat_cells_near_endpoints_stepX_zero fuel A dx dy stepY endCell startCell hY he2 hy0 c hray
        · have hstepX_eq : (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0) = stepX := rfl
          have hstepY_eq : (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0) = stepY := rfl
          rw [hstepX_eq, hstepY_eq] at hray
          exact rayMarchFloat_cells_near_endpoints_axial_Y fuel A dx dy stepX stepY endCell startCell hX hY he2 h_step_axial_Y c hray
      · -- he3 : endCell = ⟨startCell.x + stepX, startCell.y + stepY⟩
        have hstepX_eq : (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0) = stepX := rfl
        have hstepY_eq : (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0) = stepY := rfl
        rw [hstepX_eq, hstepY_eq] at hray
        rcases h_term with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11
        · exfalso; have heq : (startCell == endCell) = (floorPoint32 A == floorPoint32 B) := rfl
          rw [← heq, h1] at h_same; contradiction
        · exact rayMarchFloat_cases_1_to_7 fuel A dx dy stepX stepY endCell startCell hX hY he3 (Or.inr (Or.inl h2)) c hray
        · exact rayMarchFloat_cases_1_to_7 fuel A dx dy stepX stepY endCell startCell hX hY he3 (Or.inr (Or.inr (Or.inl h3))) c hray
        · have hs1_end : (rayMarchStepFloat A dx dy stepX stepY startCell).1 = endCell := by rw [he3, h4]
          exact rayMarchFloat_cases_1_to_7 fuel A dx dy stepX stepY endCell startCell hX hY he3 (Or.inr (Or.inr (Or.inl hs1_end))) c hray
        · exact rayMarchFloat_cases_1_to_7 fuel A dx dy stepX stepY endCell startCell hX hY he3 (Or.inr (Or.inr (Or.inr (Or.inl h5)))) c hray
        · exact rayMarchFloat_cases_1_to_7 fuel A dx dy stepX stepY endCell startCell hX hY he3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6))))) c hray
        · exact rayMarchFloat_cases_1_to_7 fuel A dx dy stepX stepY endCell startCell hX hY he3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h7))))) c hray
        · exact rayMarchFloat_cells_near_endpoints_2stepX_term fuel h_fuel A dx dy stepX stepY endCell startCell hX hY he3 h8 h_case8_hs2 h_case8_hs3 c hray
        · exact rayMarchFloat_cells_near_endpoints_2stepX_stepY_term fuel A dx dy stepX stepY endCell startCell hX hY he3 h9 h_case9_hs2 c hray
        · exact rayMarchFloat_cells_near_endpoints_2stepY_stepX fuel A dx dy stepX stepY endCell startCell hX hY he3 h10 h_case10_hs2 h_case10_hs3 c hray
        · exact rayMarchFloat_cells_near_endpoints_stepX_2stepY_term fuel A dx dy stepX stepY endCell startCell hX hY he3 h11 h_case11_hs2 c hray
  · rw [h_same] at hc
    simp only [ite_true, List.mem_singleton] at hc
    subst hc
    left; rw [chebyshevDistance_self]; omega

theorem cellIntersectionsSegmentFloat_cells_near_endpoints
    (A B : Point32) (h_finA : A.isFinite) (h_finB : B.isFinite)
    (h_bound : inCoordBounds mainCoordBound A.toPoint B.toPoint)
    (h_dist : chebyshevDistance (floorPoint32 A) (floorPoint32 B) ≤ 1)
    (h_step_axial_X :
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y)
        (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0)
        (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0) (floorPoint32 A)).2 = true ∨
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y)
        (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0)
        (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0) (floorPoint32 A)).1 = floorPoint32 B)
    (h_step_axial_Y :
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y)
        (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0)
        (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0) (floorPoint32 A)).2 = true ∨
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y)
        (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0)
        (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0) (floorPoint32 A)).1 = floorPoint32 B)
    (h_case8_hs2 :
      let stepX := if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0
      let stepY := if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY
        (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY (floorPoint32 A)).1).2 = true ∨
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY ⟨(floorPoint32 A).x + 2 * stepX, (floorPoint32 A).y⟩).2 = true ∨
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY ⟨(floorPoint32 A).x + 2 * stepX, (floorPoint32 A).y⟩).1 =
        ⟨(floorPoint32 A).x + 2 * stepX, (floorPoint32 A).y + stepY⟩)
    (h_case8_hs3 :
      let stepX := if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0
      let stepY := if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY
        ⟨(floorPoint32 A).x + 2 * stepX, (floorPoint32 A).y + stepY⟩).2 = true)
    (h_case9_hs2 :
      let stepX := if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0
      let stepY := if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY
        (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY (floorPoint32 A)).1).2 = true ∨
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY ⟨(floorPoint32 A).x + 2 * stepX, (floorPoint32 A).y + stepY⟩).2 = true)
    (h_case10_hs2 :
      let stepX := if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0
      let stepY := if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY
        (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY (floorPoint32 A)).1).2 = true ∨
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY ⟨(floorPoint32 A).x, (floorPoint32 A).y + 2 * stepY⟩).2 = true ∨
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY ⟨(floorPoint32 A).x, (floorPoint32 A).y + 2 * stepY⟩).1 =
        ⟨(floorPoint32 A).x + stepX, (floorPoint32 A).y + 2 * stepY⟩)
    (h_case10_hs3 :
      let stepX := if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0
      let stepY := if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY
        ⟨(floorPoint32 A).x + stepX, (floorPoint32 A).y + 2 * stepY⟩).2 = true)
    (h_case11_hs2 :
      let stepX := if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0
      let stepY := if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY
        (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY (floorPoint32 A)).1).2 = true ∨
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY ⟨(floorPoint32 A).x + stepX, (floorPoint32 A).y + 2 * stepY⟩).2 = true) :
    ∀ c ∈ cellIntersectionsSegmentFloat A B,
      chebyshevDistance c (floorPoint32 A) ≤ 1 ∨ chebyshevDistance c (floorPoint32 B) ≤ 1 :=
  cellIntersectionsSegmentFloat_cells_near_endpoints_Impl A B h_finA h_finB h_bound h_dist
    h_step_axial_X h_step_axial_Y h_case8_hs2 h_case8_hs3 h_case9_hs2 h_case10_hs2 h_case10_hs3 h_case11_hs2

theorem cellIntersectionsSegmentFloat_sub_hausdorff_one_of_adjacent_cells_Impl
    (A B : Point32) (h_finA : A.isFinite) (h_finB : B.isFinite)
    (_h_bound : inCoordBounds mainCoordBound A.toPoint B.toPoint)
    (h_dist : chebyshevDistance (floorPoint32 A) (floorPoint32 B) ≤ 1)
    (h_near : ∀ c ∈ cellIntersectionsSegmentFloat A B,
      chebyshevDistance c (floorPoint32 A) ≤ 1 ∨ chebyshevDistance c (floorPoint32 B) ≤ 1) :
    cellHausdorffDistanceLe
      (cellIntersectionsSegmentFloat A B)
      (cellIntersectionsSegment A.toPoint B.toPoint) 1 := by
  have h_floorA := floorPoint32_eq_floorPoint A h_finA
  have h_floorB := floorPoint32_eq_floorPoint B h_finB
  have h_dist_ideal : chebyshevDistance (floorPoint A.toPoint) (floorPoint B.toPoint) ≤ 1 := by
    rw [← h_floorA, ← h_floorB]
    exact h_dist
  have h_anchor1 : floorPoint32 A ∈ cellIntersectionsSegmentFloat A B :=
    cellIntersectionsSegmentFloat_contains_start A B
  have h_anchor2 : floorPoint32 A ∈ cellIntersectionsSegment A.toPoint B.toPoint := by
    rw [h_floorA]
    exact cellIntersectionsSegment_contains_start A.toPoint B.toPoint
  have h_anchor2B : floorPoint32 B ∈ cellIntersectionsSegment A.toPoint B.toPoint := by
    rw [h_floorB]
    exact cellIntersectionsSegment_contains_end A.toPoint B.toPoint
  have h_bound2 := cellIntersectionsSegment_cells_near_start A.toPoint B.toPoint h_dist_ideal
  exact cellHausdorffDistanceLe_of_subset_near_endpoints
    (cellIntersectionsSegmentFloat A B)
    (cellIntersectionsSegment A.toPoint B.toPoint)
    (floorPoint32 A)
    (floorPoint32 B)
    h_anchor1
    h_anchor2
    h_anchor2B
    h_near
    (by intro c hc; rw [h_floorA]; exact h_bound2 c hc)

theorem cellIntersectionsSegmentFloat_sub_hausdorff_one_of_adjacent_cells
    (A B : Point32) (h_finA : A.isFinite) (h_finB : B.isFinite)
    (h_bound : inCoordBounds mainCoordBound A.toPoint B.toPoint)
    (h_dist : chebyshevDistance (floorPoint32 A) (floorPoint32 B) ≤ 1)
    (h_near : ∀ c ∈ cellIntersectionsSegmentFloat A B,
      chebyshevDistance c (floorPoint32 A) ≤ 1 ∨ chebyshevDistance c (floorPoint32 B) ≤ 1) :
    cellHausdorffDistanceLe
      (cellIntersectionsSegmentFloat A B)
      (cellIntersectionsSegment A.toPoint B.toPoint) 1 :=
  cellIntersectionsSegmentFloat_sub_hausdorff_one_of_adjacent_cells_Impl A B h_finA h_finB h_bound h_dist h_near

theorem cellIntersectionsSegmentFloat_sub_hausdorff_one_of_adjacent_cells_of_cases
    (A B : Point32) (h_finA : A.isFinite) (h_finB : B.isFinite)
    (h_bound : inCoordBounds mainCoordBound A.toPoint B.toPoint)
    (h_dist : chebyshevDistance (floorPoint32 A) (floorPoint32 B) ≤ 1)
    (h_step_axial_X :
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y)
        (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0)
        (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0) (floorPoint32 A)).2 = true ∨
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y)
        (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0)
        (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0) (floorPoint32 A)).1 = floorPoint32 B)
    (h_step_axial_Y :
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y)
        (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0)
        (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0) (floorPoint32 A)).2 = true ∨
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y)
        (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0)
        (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0) (floorPoint32 A)).1 = floorPoint32 B)
    (h_case8_hs2 :
      let stepX := if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0
      let stepY := if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY
        (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY (floorPoint32 A)).1).2 = true ∨
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY ⟨(floorPoint32 A).x + 2 * stepX, (floorPoint32 A).y⟩).2 = true ∨
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY ⟨(floorPoint32 A).x + 2 * stepX, (floorPoint32 A).y⟩).1 =
        ⟨(floorPoint32 A).x + 2 * stepX, (floorPoint32 A).y + stepY⟩)
    (h_case8_hs3 :
      let stepX := if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0
      let stepY := if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY
        ⟨(floorPoint32 A).x + 2 * stepX, (floorPoint32 A).y + stepY⟩).2 = true)
    (h_case9_hs2 :
      let stepX := if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0
      let stepY := if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY
        (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY (floorPoint32 A)).1).2 = true ∨
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY ⟨(floorPoint32 A).x + 2 * stepX, (floorPoint32 A).y + stepY⟩).2 = true)
    (h_case10_hs2 :
      let stepX := if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0
      let stepY := if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY
        (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY (floorPoint32 A)).1).2 = true ∨
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY ⟨(floorPoint32 A).x, (floorPoint32 A).y + 2 * stepY⟩).2 = true ∨
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY ⟨(floorPoint32 A).x, (floorPoint32 A).y + 2 * stepY⟩).1 =
        ⟨(floorPoint32 A).x + stepX, (floorPoint32 A).y + 2 * stepY⟩)
    (h_case10_hs3 :
      let stepX := if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0
      let stepY := if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY
        ⟨(floorPoint32 A).x + stepX, (floorPoint32 A).y + 2 * stepY⟩).2 = true)
    (h_case11_hs2 :
      let stepX := if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0
      let stepY := if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY
        (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY (floorPoint32 A)).1).2 = true ∨
      (rayMarchStepFloat A (B.x - A.x) (B.y - A.y) stepX stepY ⟨(floorPoint32 A).x + stepX, (floorPoint32 A).y + 2 * stepY⟩).2 = true) :
    cellHausdorffDistanceLe
      (cellIntersectionsSegmentFloat A B)
      (cellIntersectionsSegment A.toPoint B.toPoint) 1 :=
  cellIntersectionsSegmentFloat_sub_hausdorff_one_of_adjacent_cells A B h_finA h_finB h_bound h_dist
    (cellIntersectionsSegmentFloat_cells_near_endpoints A B h_finA h_finB h_bound h_dist
      h_step_axial_X h_step_axial_Y h_case8_hs2 h_case8_hs3 h_case9_hs2 h_case10_hs2 h_case10_hs3 h_case11_hs2)

#print axioms cellIntersectionsSegmentFloat_cells_near_endpoints
#print axioms cellIntersectionsSegmentFloat_sub_hausdorff_one_of_adjacent_cells
#print axioms cellIntersectionsSegmentFloat_sub_hausdorff_one_of_adjacent_cells_of_cases

end Geometry

