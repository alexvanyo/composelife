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
import proofs.FloatProperties
import Geometry.LineSegment
import proofs.MiniSegment
import proofs.RayMarchLimits

namespace Geometry

/--
The endpoint of a segment is always included in the floating-point intersection output.
-/
theorem cellIntersectionsSegmentFloat_contains_end (A B : Point32) :
    floorPoint32 B ∈ cellIntersectionsSegmentFloat A B := by
  unfold cellIntersectionsSegmentFloat
  dsimp only []
  cases h : (floorPoint32 A == floorPoint32 B)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [mem_dedupCells]
    simp only [List.mem_append, List.mem_cons, true_or, or_true]
  · simp only [ite_true]
    have h_eq : floorPoint32 A = floorPoint32 B := eq_of_beq h
    simp [h_eq]

/--
Master Path Induction Theorem:
For any polyline waypoint sequence Ps with finite coordinates, if every constituent mini-segment
satisfies the discrete Chebyshev Hausdorff distance bound ≤ 1 relative to its rational counterpart,
then the full floating-point path output satisfies the discrete Chebyshev Hausdorff distance bound ≤ 1
relative to the full rational path output.
-/
theorem cellIntersectionsPathFloat_hausdorff_bound_of_segments_Impl :
    ∀ (Ps : List Point32), AllFinite Ps →
      (∀ (i : Nat) (hi : i + 1 < Ps.length),
        cellHausdorffDistanceLe
          (cellIntersectionsSegmentFloat (Ps.get ⟨i, by omega⟩) (Ps.get ⟨i + 1, hi⟩))
          (cellIntersectionsSegment (Ps.get ⟨i, by omega⟩).toPoint (Ps.get ⟨i + 1, hi⟩).toPoint) 1) →
      cellHausdorffDistanceLe
        (cellIntersectionsPathFloat Ps)
        (cellIntersectionsPath (pointsToRational Ps)) 1 := by
  intro Ps
  induction Ps with
  | nil =>
    intro _ _
    unfold cellIntersectionsPathFloat cellIntersectionsPath pointsToRational
    dsimp only []
    exact cellHausdorffDistanceLe_of_eq rfl
  | cons p1 rest1 ih1 =>
    cases rest1 with
    | nil =>
      intro h_fin _
      unfold cellIntersectionsPathFloat cellIntersectionsPath pointsToRational
      dsimp only []
      have hp1_fin : p1.isFinite := h_fin p1 (by simp)
      have h_fp := floorPoint32_eq_floorPoint p1 hp1_fin
      rw [h_fp]
      exact cellHausdorffDistanceLe_of_eq rfl
    | cons p2 rest2 =>
      intro h_fin h_seg
      unfold cellIntersectionsPathFloat cellIntersectionsPath pointsToRational
      dsimp only [cellIntersectionsPathFloat, cellIntersectionsPath, List.map]
      have h_fin_tail : AllFinite (p2 :: rest2) := by
        intro x hx
        exact h_fin x (List.mem_cons_of_mem p1 hx)
      have h_seg_tail : ∀ (i : Nat) (hi : i + 1 < (p2 :: rest2).length),
          cellHausdorffDistanceLe
            (cellIntersectionsSegmentFloat ((p2 :: rest2).get ⟨i, by omega⟩) ((p2 :: rest2).get ⟨i + 1, hi⟩))
            (cellIntersectionsSegment ((p2 :: rest2).get ⟨i, by omega⟩).toPoint ((p2 :: rest2).get ⟨i + 1, hi⟩).toPoint) 1 := by
        intro i hi
        have hi' : (i + 1) + 1 < (p1 :: p2 :: rest2).length := by
          change (i + 1) + 1 < rest2.length + 2
          change i + 1 < rest2.length + 1 at hi
          omega
        have h_step := h_seg (i + 1) hi'
        have h_get1 : (p2 :: rest2).get ⟨i, by omega⟩ = (p1 :: p2 :: rest2).get ⟨i + 1, by omega⟩ := rfl
        have h_get2 : (p2 :: rest2).get ⟨i + 1, hi⟩ = (p1 :: p2 :: rest2).get ⟨(i + 1) + 1, hi'⟩ := rfl
        rw [h_get1, h_get2]
        exact h_step
      have ih := ih1 h_fin_tail h_seg_tail
      have h0_lt : 0 + 1 < (p1 :: p2 :: rest2).length := by
        change 1 < rest2.length + 2
        omega
      have h_first := h_seg 0 h0_lt
      have h_get0 : (p1 :: p2 :: rest2).get ⟨0, by omega⟩ = p1 := rfl
      have h_get1 : (p1 :: p2 :: rest2).get ⟨0 + 1, h0_lt⟩ = p2 := rfl
      rw [h_get0, h_get1] at h_first
      apply cellHausdorffDistanceLe_dedupCells
      apply cellHausdorffDistanceLe_append
      · exact h_first
      · exact ih

/--
Master Theorem (Same-Cell Unconditional Formulation):
For any segment whose endpoints reside in the same discrete grid cell,
the discrete Chebyshev Hausdorff distance between float and rational outputs is at most 1.
-/
theorem cellIntersectionsSegmentFloat_hausdorff_bound_of_same_cell_Impl
    (A B : Point32) (h_finA : A.isFinite) (h_finB : B.isFinite)
    (h_same : floorPoint32 A = floorPoint32 B) :
    cellHausdorffDistanceLe
      (cellIntersectionsSegmentFloat A B)
      (cellIntersectionsSegment A.toPoint B.toPoint) 1 :=
  cellIntersectionsSegmentFloat_sub_hausdorff_one_of_same_cell A B h_finA h_finB h_same

theorem rayMarchStep_done_or_cases (start ptEnd : Point) (dx dy : ℚ) (stepX stepY : Int) (c : Cell) :
    ((rayMarchStep start ptEnd dx dy stepX stepY c).2 = true ∧
     (rayMarchStep start ptEnd dx dy stepX stepY c).1 = c) ∨
    ((rayMarchStep start ptEnd dx dy stepX stepY c).2 = false ∧
     ((rayMarchStep start ptEnd dx dy stepX stepY c).1 = ⟨c.x + stepX, c.y⟩ ∨
      (rayMarchStep start ptEnd dx dy stepX stepY c).1 = ⟨c.x, c.y + stepY⟩ ∨
      (rayMarchStep start ptEnd dx dy stepX stepY c).1 = ⟨c.x + stepX, c.y + stepY⟩)) := by
  have h := rayMarchStep_mem start ptEnd dx dy stepX stepY c
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h
  · left; exact ⟨congrArg Prod.snd h, congrArg Prod.fst h⟩
  · right; exact ⟨congrArg Prod.snd h, Or.inl (congrArg Prod.fst h)⟩
  · right; exact ⟨congrArg Prod.snd h, Or.inr (Or.inl (congrArg Prod.fst h))⟩
  · right; exact ⟨congrArg Prod.snd h, Or.inr (Or.inr (congrArg Prod.fst h))⟩

def RayMarchCasesFloatInd
    (start : Point32) (ptEnd : Point)
    (dx dy : Binary64) (dxQ dyQ : ℚ) (stepX stepY : ℤ) (endCell : Cell) (c : Cell) : Prop :=
  RayMarchCasesFloatExt3 start ptEnd dx dy dxQ dyQ stepX stepY endCell c ∨
  -- Residual 1: Float steps diagonal at c, Ideal does NOT step diagonal at c and does NOT resynchronize via HalfDiamondIdealTransition
  ((c == endCell) = false ∧
   (rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x + stepX, c.y + stepY⟩ ∧
   (rayMarchStepFloat start dx dy stepX stepY c).2 = false ∧
   (⟨c.x + stepX, c.y + stepY⟩ == endCell) = false ∧
   (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y + stepY⟩).2 = false ∧
   (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y + stepY⟩).1 ≠ endCell ∧
   ((rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).2 = true ∨
    ((rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).2 = false ∧
     (((rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 = ⟨c.x + stepX, c.y⟩ ∧
       ((⟨c.x + stepX, c.y⟩ == endCell) = true ∨
        (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y⟩).2 = true ∨
        (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y⟩).1 = ⟨c.x + 2 * stepX, c.y⟩ ∨
        (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y⟩).1 = ⟨c.x + 2 * stepX, c.y + stepY⟩)) ∨
      ((rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 = ⟨c.x, c.y + stepY⟩ ∧
       ((⟨c.x, c.y + stepY⟩ == endCell) = true ∨
        (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x, c.y + stepY⟩).2 = true ∨
        (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x, c.y + stepY⟩).1 = ⟨c.x, c.y + 2 * stepY⟩ ∨
        (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x, c.y + stepY⟩).1 = ⟨c.x + stepX, c.y + 2 * stepY⟩)))))) ∨
  -- Residual 2: Float steps X then Y (or Y then X) to (c.x+stepX, c.y+stepY), and Ideal is done or doesn't resynchronize
  ((c == endCell) = false ∧
   (rayMarchStepFloat start dx dy stepX stepY c).2 = false ∧
   (⟨c.x + stepX, c.y + stepY⟩ == endCell) = false ∧
   (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y + stepY⟩).2 = false ∧
   (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y + stepY⟩).1 ≠ endCell ∧
   (((rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x + stepX, c.y⟩ ∧
     (⟨c.x + stepX, c.y⟩ == endCell) = false ∧
     (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y⟩).2 = false ∧
     (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y⟩).1 = ⟨c.x + stepX, c.y + stepY⟩ ∧
     ((rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).2 = true ∨
      ((rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).2 = false ∧
       (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 = ⟨c.x, c.y + stepY⟩ ∧
       ((⟨c.x, c.y + stepY⟩ == endCell) = true ∨
        (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x, c.y + stepY⟩).2 = true ∨
        (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x, c.y + stepY⟩).1 = ⟨c.x, c.y + 2 * stepY⟩ ∨
        (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x, c.y + stepY⟩).1 = ⟨c.x + stepX, c.y + 2 * stepY⟩)))) ∨
    ((rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x, c.y + stepY⟩ ∧
     (⟨c.x, c.y + stepY⟩ == endCell) = false ∧
     (rayMarchStepFloat start dx dy stepX stepY ⟨c.x, c.y + stepY⟩).2 = false ∧
     (rayMarchStepFloat start dx dy stepX stepY ⟨c.x, c.y + stepY⟩).1 = ⟨c.x + stepX, c.y + stepY⟩ ∧
     ((rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).2 = true ∨
      ((rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).2 = false ∧
       (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 = ⟨c.x + stepX, c.y⟩ ∧
       ((⟨c.x + stepX, c.y⟩ == endCell) = true ∨
        (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y⟩).2 = true ∨
        (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y⟩).1 = ⟨c.x + 2 * stepX, c.y⟩ ∨
        (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y⟩).1 = ⟨c.x + 2 * stepX, c.y + stepY⟩)))))) ∨
  -- Residual 3: Float takes 2 steps in the same coordinate (2*stepX or 2*stepY) while disagreeing with Ideal at step 1
  ((c == endCell) = false ∧
   (rayMarchStepFloat start dx dy stepX stepY c).2 = false ∧
   (rayMarchStepFloat start dx dy stepX stepY (rayMarchStepFloat start dx dy stepX stepY c).1).2 = false ∧
   (rayMarchStepFloat start dx dy stepX stepY (rayMarchStepFloat start dx dy stepX stepY c).1).1 ≠ endCell ∧
   ((((rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x + stepX, c.y⟩ ∧
      (⟨c.x + stepX, c.y⟩ == endCell) = false ∧
      ((rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y⟩).1 = ⟨c.x + 2 * stepX, c.y⟩ ∨
       (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y⟩).1 = ⟨c.x + 2 * stepX, c.y + stepY⟩) ∧
      ((rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).2 = true ∨
       ((rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).2 = false ∧
        ((rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 = ⟨c.x, c.y + stepY⟩ ∨
         (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 = ⟨c.x + stepX, c.y + stepY⟩)))) ∨
     ((rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x, c.y + stepY⟩ ∧
      (⟨c.x, c.y + stepY⟩ == endCell) = false ∧
      ((rayMarchStepFloat start dx dy stepX stepY ⟨c.x, c.y + stepY⟩).1 = ⟨c.x, c.y + 2 * stepY⟩ ∨
       (rayMarchStepFloat start dx dy stepX stepY ⟨c.x, c.y + stepY⟩).1 = ⟨c.x + stepX, c.y + 2 * stepY⟩) ∧
      ((rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).2 = true ∨
       ((rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).2 = false ∧
        ((rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 = ⟨c.x + stepX, c.y⟩ ∨
         (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 = ⟨c.x + stepX, c.y + stepY⟩)))))))

theorem prove_cases_float_ind (start : Point32) (ptEnd : Point)
    (dx dy : Binary64) (dxQ dyQ : ℚ) (stepX stepY : Int) (endCell : Cell) (c : Cell) :
    RayMarchCasesFloatInd start ptEnd dx dy dxQ dyQ stepX stepY endCell c := by
  by_cases h_end : (c == endCell) = true
  · left; left; exact Or.inr (Or.inl (Or.inl h_end))
  · have h_end_b : (c == endCell) = false := by
      cases h : (c == endCell); rfl; exfalso; apply h_end; exact h
    have hF := rayMarchStepFloat_done_or_cases start dx dy stepX stepY c
    have hI := rayMarchStep_done_or_cases start.toPoint ptEnd dxQ dyQ stepX stepY c
    rcases hF with ⟨hdF, hcF⟩ | ⟨hdF, hcF | hcF | hcF⟩
    · left; left; exact Or.inr (Or.inl (Or.inr (Or.inl hdF)))
    · -- Float step 1 is X: ⟨c.x + stepX, c.y⟩
      by_cases h_endF1 : (⟨c.x + stepX, c.y⟩ == endCell) = true
      · left; left; exact Or.inr (Or.inl (Or.inr (Or.inr (by rw [hcF]; exact eq_of_beq h_endF1))))
      · have h_endF1_b : (⟨c.x + stepX, c.y⟩ == endCell) = false := by
          cases h : (⟨c.x + stepX, c.y⟩ == endCell); rfl; exfalso; apply h_endF1; exact h
        have hF2 := rayMarchStepFloat_done_or_cases start dx dy stepX stepY ⟨c.x + stepX, c.y⟩
        rcases hF2 with ⟨hdF2, hcF2⟩ | ⟨hdF2, hcF2 | hcF2 | hcF2⟩
        · left; left; exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (by rw [hcF]; exact hdF2)))))
        · -- Float step 2 is 2*X: ⟨c.x + 2*stepX, c.y⟩
          have heq : (⟨c.x + stepX + stepX, c.y⟩ : Cell) = ⟨c.x + 2 * stepX, c.y⟩ := by
            have : c.x + stepX + stepX = c.x + 2 * stepX := by omega
            rw [this]
          rw [heq] at hcF2
          by_cases h_endF2 : (rayMarchStepFloat start dx dy stepX stepY (rayMarchStepFloat start dx dy stepX stepY c).1).1 = endCell
          · left; left; exact Or.inr (Or.inr (Or.inl (Or.inl h_endF2)))
          · rcases hI with ⟨hdI, _⟩ | ⟨hdI, hcI | hcI | hcI⟩
            · right; right; right
              exact ⟨h_end_b, hdF, by rw [hcF]; exact hdF2, h_endF2, Or.inl ⟨hcF, h_endF1_b, Or.inl hcF2, Or.inl hdI⟩⟩
            · left; left; exact Or.inl ⟨by rw [hcF, hcI], by rw [hdF, hdI]⟩
            · right; right; right
              exact ⟨h_end_b, hdF, by rw [hcF]; exact hdF2, h_endF2, Or.inl ⟨hcF, h_endF1_b, Or.inl hcF2, Or.inr ⟨hdI, Or.inl hcI⟩⟩⟩
            · right; right; right
              exact ⟨h_end_b, hdF, by rw [hcF]; exact hdF2, h_endF2, Or.inl ⟨hcF, h_endF1_b, Or.inl hcF2, Or.inr ⟨hdI, Or.inr hcI⟩⟩⟩
        · -- Float step 2 is Y: ⟨c.x + stepX, c.y + stepY⟩
          by_cases h_endF2 : (⟨c.x + stepX, c.y + stepY⟩ == endCell) = true
          · left; left; exact Or.inr (Or.inr (Or.inl (Or.inl (by rw [hcF, hcF2]; exact eq_of_beq h_endF2))))
          · have h_endF2_b : (⟨c.x + stepX, c.y + stepY⟩ == endCell) = false := by
              cases h : (⟨c.x + stepX, c.y + stepY⟩ == endCell); rfl; exfalso; apply h_endF2; exact h
            by_cases hdF3 : (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y + stepY⟩).2 = true
            · left; left; exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl ⟨hcF, hcF2, hdF3⟩)))))
            · have hdF3_b : (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y + stepY⟩).2 = false := by
                cases h : (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y + stepY⟩).2; rfl; exfalso; apply hdF3; exact h
              by_cases heF3 : (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y + stepY⟩).1 = endCell
              · left; left; exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hcF, hcF2, heF3⟩)))))))
              · rcases hI with ⟨hdI, _⟩ | ⟨hdI, hcI | hcI | hcI⟩
                · right; right; left
                  exact ⟨h_end_b, hdF, h_endF2_b, hdF3_b, heF3, Or.inl ⟨hcF, h_endF1_b, hdF2, hcF2, Or.inl hdI⟩⟩
                · left; left; exact Or.inl ⟨by rw [hcF, hcI], by rw [hdF, hdI]⟩
                · by_cases h_endI1 : (⟨c.x, c.y + stepY⟩ == endCell) = true
                  · right; right; left
                    exact ⟨h_end_b, hdF, h_endF2_b, hdF3_b, heF3, Or.inl ⟨hcF, h_endF1_b, hdF2, hcF2, Or.inr ⟨hdI, hcI, Or.inl h_endI1⟩⟩⟩
                  · have h_endI1_b : (⟨c.x, c.y + stepY⟩ == endCell) = false := by
                      cases h : (⟨c.x, c.y + stepY⟩ == endCell); rfl; exfalso; apply h_endI1; exact h
                    have hI2 := rayMarchStep_done_or_cases start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x, c.y + stepY⟩
                    rcases hI2 with ⟨hdI2, _⟩ | ⟨hdI2, hcI2 | hcI2 | hcI2⟩
                    · right; right; left
                      exact ⟨h_end_b, hdF, h_endF2_b, hdF3_b, heF3, Or.inl ⟨hcF, h_endF1_b, hdF2, hcF2, Or.inr ⟨hdI, hcI, Or.inr (Or.inl hdI2)⟩⟩⟩
                    · left; left; right; right; right; left
                      exact ⟨h_end_b, hdF, hcF, h_endF1_b, hdF2, hcF2, hdI, hcI, h_endI1_b, hdI2, hcI2⟩
                    · have heqI : (⟨c.x, c.y + stepY + stepY⟩ : Cell) = ⟨c.x, c.y + 2 * stepY⟩ := by
                        have : c.y + stepY + stepY = c.y + 2 * stepY := by omega
                        rw [this]
                      rw [heqI] at hcI2
                      right; right; left
                      exact ⟨h_end_b, hdF, h_endF2_b, hdF3_b, heF3, Or.inl ⟨hcF, h_endF1_b, hdF2, hcF2, Or.inr ⟨hdI, hcI, Or.inr (Or.inr (Or.inl hcI2))⟩⟩⟩
                    · have heqI : (⟨c.x + stepX, c.y + stepY + stepY⟩ : Cell) = ⟨c.x + stepX, c.y + 2 * stepY⟩ := by
                        have : c.y + stepY + stepY = c.y + 2 * stepY := by omega
                        rw [this]
                      rw [heqI] at hcI2
                      right; right; left
                      exact ⟨h_end_b, hdF, h_endF2_b, hdF3_b, heF3, Or.inl ⟨hcF, h_endF1_b, hdF2, hcF2, Or.inr ⟨hdI, hcI, Or.inr (Or.inr (Or.inr hcI2))⟩⟩⟩
                · -- Ideal stepped diagonal at c! Half-diamond!
                  left; right; left; left
                  exact ⟨h_end_b, hdF, hcF, h_endF1_b, hdF2, hcF2, hdI, hcI⟩
        · -- Float step 2 is diagonal: ⟨c.x + 2*stepX, c.y + stepY⟩
          have heq : (⟨c.x + stepX + stepX, c.y + stepY⟩ : Cell) = ⟨c.x + 2 * stepX, c.y + stepY⟩ := by
            have : c.x + stepX + stepX = c.x + 2 * stepX := by omega
            rw [this]
          rw [heq] at hcF2
          by_cases h_endF2 : (rayMarchStepFloat start dx dy stepX stepY (rayMarchStepFloat start dx dy stepX stepY c).1).1 = endCell
          · left; left; exact Or.inr (Or.inr (Or.inl (Or.inl h_endF2)))
          · rcases hI with ⟨hdI, _⟩ | ⟨hdI, hcI | hcI | hcI⟩
            · right; right; right
              exact ⟨h_end_b, hdF, by rw [hcF]; exact hdF2, h_endF2, Or.inl ⟨hcF, h_endF1_b, Or.inr hcF2, Or.inl hdI⟩⟩
            · left; left; exact Or.inl ⟨by rw [hcF, hcI], by rw [hdF, hdI]⟩
            · right; right; right
              exact ⟨h_end_b, hdF, by rw [hcF]; exact hdF2, h_endF2, Or.inl ⟨hcF, h_endF1_b, Or.inr hcF2, Or.inr ⟨hdI, Or.inl hcI⟩⟩⟩
            · right; right; right
              exact ⟨h_end_b, hdF, by rw [hcF]; exact hdF2, h_endF2, Or.inl ⟨hcF, h_endF1_b, Or.inr hcF2, Or.inr ⟨hdI, Or.inr hcI⟩⟩⟩
    · -- Float step 1 is Y: ⟨c.x, c.y + stepY⟩
      by_cases h_endF1 : (⟨c.x, c.y + stepY⟩ == endCell) = true
      · left; left; exact Or.inr (Or.inl (Or.inr (Or.inr (by rw [hcF]; exact eq_of_beq h_endF1))))
      · have h_endF1_b : (⟨c.x, c.y + stepY⟩ == endCell) = false := by
          cases h : (⟨c.x, c.y + stepY⟩ == endCell); rfl; exfalso; apply h_endF1; exact h
        have hF2 := rayMarchStepFloat_done_or_cases start dx dy stepX stepY ⟨c.x, c.y + stepY⟩
        rcases hF2 with ⟨hdF2, hcF2⟩ | ⟨hdF2, hcF2 | hcF2 | hcF2⟩
        · left; left; exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (by rw [hcF]; exact hdF2)))))
        · -- Float step 2 is X: ⟨c.x + stepX, c.y + stepY⟩
          by_cases h_endF2 : (⟨c.x + stepX, c.y + stepY⟩ == endCell) = true
          · left; left; exact Or.inr (Or.inr (Or.inl (Or.inl (by rw [hcF, hcF2]; exact eq_of_beq h_endF2))))
          · have h_endF2_b : (⟨c.x + stepX, c.y + stepY⟩ == endCell) = false := by
              cases h : (⟨c.x + stepX, c.y + stepY⟩ == endCell); rfl; exfalso; apply h_endF2; exact h
            by_cases hdF3 : (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y + stepY⟩).2 = true
            · left; left; exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨hcF, hcF2, hdF3⟩))))))
            · have hdF3_b : (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y + stepY⟩).2 = false := by
                cases h : (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y + stepY⟩).2; rfl; exfalso; apply hdF3; exact h
              by_cases heF3 : (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y + stepY⟩).1 = endCell
              · left; left; exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hcF, hcF2, heF3⟩))))))))
              · rcases hI with ⟨hdI, _⟩ | ⟨hdI, hcI | hcI | hcI⟩
                · right; right; left
                  exact ⟨h_end_b, hdF, h_endF2_b, hdF3_b, heF3, Or.inr ⟨hcF, h_endF1_b, hdF2, hcF2, Or.inl hdI⟩⟩
                · by_cases h_endI1 : (⟨c.x + stepX, c.y⟩ == endCell) = true
                  · right; right; left
                    exact ⟨h_end_b, hdF, h_endF2_b, hdF3_b, heF3, Or.inr ⟨hcF, h_endF1_b, hdF2, hcF2, Or.inr ⟨hdI, hcI, Or.inl h_endI1⟩⟩⟩
                  · have h_endI1_b : (⟨c.x + stepX, c.y⟩ == endCell) = false := by
                      cases h : (⟨c.x + stepX, c.y⟩ == endCell); rfl; exfalso; apply h_endI1; exact h
                    have hI2 := rayMarchStep_done_or_cases start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y⟩
                    rcases hI2 with ⟨hdI2, _⟩ | ⟨hdI2, hcI2 | hcI2 | hcI2⟩
                    · right; right; left
                      exact ⟨h_end_b, hdF, h_endF2_b, hdF3_b, heF3, Or.inr ⟨hcF, h_endF1_b, hdF2, hcF2, Or.inr ⟨hdI, hcI, Or.inr (Or.inl hdI2)⟩⟩⟩
                    · have heqI : (⟨c.x + stepX + stepX, c.y⟩ : Cell) = ⟨c.x + 2 * stepX, c.y⟩ := by
                        have : c.x + stepX + stepX = c.x + 2 * stepX := by omega
                        rw [this]
                      rw [heqI] at hcI2
                      right; right; left
                      exact ⟨h_end_b, hdF, h_endF2_b, hdF3_b, heF3, Or.inr ⟨hcF, h_endF1_b, hdF2, hcF2, Or.inr ⟨hdI, hcI, Or.inr (Or.inr (Or.inl hcI2))⟩⟩⟩
                    · left; left; right; right; right; right
                      exact ⟨h_end_b, hdF, hcF, h_endF1_b, hdF2, hcF2, hdI, hcI, h_endI1_b, hdI2, hcI2⟩
                    · have heqI : (⟨c.x + stepX + stepX, c.y + stepY⟩ : Cell) = ⟨c.x + 2 * stepX, c.y + stepY⟩ := by
                        have : c.x + stepX + stepX = c.x + 2 * stepX := by omega
                        rw [this]
                      rw [heqI] at hcI2
                      right; right; left
                      exact ⟨h_end_b, hdF, h_endF2_b, hdF3_b, heF3, Or.inr ⟨hcF, h_endF1_b, hdF2, hcF2, Or.inr ⟨hdI, hcI, Or.inr (Or.inr (Or.inr hcI2))⟩⟩⟩
                · left; left; exact Or.inl ⟨by rw [hcF, hcI], by rw [hdF, hdI]⟩
                · -- Ideal stepped diagonal at c! Half-diamond!
                  left; right; left; right
                  exact ⟨h_end_b, hdF, hcF, h_endF1_b, hdF2, hcF2, hdI, hcI⟩
        · -- Float step 2 is 2*Y: ⟨c.x, c.y + 2*stepY⟩
          have heq : (⟨c.x, c.y + stepY + stepY⟩ : Cell) = ⟨c.x, c.y + 2 * stepY⟩ := by
            have : c.y + stepY + stepY = c.y + 2 * stepY := by omega
            rw [this]
          rw [heq] at hcF2
          by_cases h_endF2 : (rayMarchStepFloat start dx dy stepX stepY (rayMarchStepFloat start dx dy stepX stepY c).1).1 = endCell
          · left; left; exact Or.inr (Or.inr (Or.inl (Or.inl h_endF2)))
          · rcases hI with ⟨hdI, _⟩ | ⟨hdI, hcI | hcI | hcI⟩
            · right; right; right
              exact ⟨h_end_b, hdF, by rw [hcF]; exact hdF2, h_endF2, Or.inr ⟨hcF, h_endF1_b, Or.inl hcF2, Or.inl hdI⟩⟩
            · right; right; right
              exact ⟨h_end_b, hdF, by rw [hcF]; exact hdF2, h_endF2, Or.inr ⟨hcF, h_endF1_b, Or.inl hcF2, Or.inr ⟨hdI, Or.inl hcI⟩⟩⟩
            · left; left; exact Or.inl ⟨by rw [hcF, hcI], by rw [hdF, hdI]⟩
            · right; right; right
              exact ⟨h_end_b, hdF, by rw [hcF]; exact hdF2, h_endF2, Or.inr ⟨hcF, h_endF1_b, Or.inl hcF2, Or.inr ⟨hdI, Or.inr hcI⟩⟩⟩
        · -- Float step 2 is diagonal: ⟨c.x + stepX, c.y + 2*stepY⟩
          have heq : (⟨c.x + stepX, c.y + stepY + stepY⟩ : Cell) = ⟨c.x + stepX, c.y + 2 * stepY⟩ := by
            have : c.y + stepY + stepY = c.y + 2 * stepY := by omega
            rw [this]
          rw [heq] at hcF2
          by_cases h_endF2 : (rayMarchStepFloat start dx dy stepX stepY (rayMarchStepFloat start dx dy stepX stepY c).1).1 = endCell
          · left; left; exact Or.inr (Or.inr (Or.inl (Or.inl h_endF2)))
          · rcases hI with ⟨hdI, _⟩ | ⟨hdI, hcI | hcI | hcI⟩
            · right; right; right
              exact ⟨h_end_b, hdF, by rw [hcF]; exact hdF2, h_endF2, Or.inr ⟨hcF, h_endF1_b, Or.inr hcF2, Or.inl hdI⟩⟩
            · right; right; right
              exact ⟨h_end_b, hdF, by rw [hcF]; exact hdF2, h_endF2, Or.inr ⟨hcF, h_endF1_b, Or.inr hcF2, Or.inr ⟨hdI, Or.inl hcI⟩⟩⟩
            · left; left; exact Or.inl ⟨by rw [hcF, hcI], by rw [hdF, hdI]⟩
            · right; right; right
              exact ⟨h_end_b, hdF, by rw [hcF]; exact hdF2, h_endF2, Or.inr ⟨hcF, h_endF1_b, Or.inr hcF2, Or.inr ⟨hdI, Or.inr hcI⟩⟩⟩
    · -- Float step 1 is diagonal: ⟨c.x + stepX, c.y + stepY⟩
      by_cases h_endF1 : (⟨c.x + stepX, c.y + stepY⟩ == endCell) = true
      · left; left; exact Or.inr (Or.inl (Or.inr (Or.inr (by rw [hcF]; exact eq_of_beq h_endF1))))
      · by_cases hdF2 : (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y + stepY⟩).2 = true
        · left; left; exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hcF, hdF2⟩)))))))))
        · by_cases heF2 : (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y + stepY⟩).1 = endCell
          · left; left; exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hcF, heF2⟩)))))))))
          · have h_endF1_b : (⟨c.x + stepX, c.y + stepY⟩ == endCell) = false := by
              cases h : (⟨c.x + stepX, c.y + stepY⟩ == endCell); rfl; exfalso; apply h_endF1; exact h
            have hdF2_b : (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y + stepY⟩).2 = false := by
              cases h : (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y + stepY⟩).2; rfl; exfalso; apply hdF2; exact h
            rcases hI with ⟨hdI, _⟩ | ⟨hdI, hcI | hcI | hcI⟩
            · right; left; exact ⟨h_end_b, hcF, hdF, h_endF1_b, hdF2_b, heF2, Or.inl hdI⟩
            · by_cases h_endI1 : (⟨c.x + stepX, c.y⟩ == endCell) = true
              · right; left; exact ⟨h_end_b, hcF, hdF, h_endF1_b, hdF2_b, heF2, Or.inr ⟨hdI, Or.inl ⟨hcI, Or.inl h_endI1⟩⟩⟩
              · have h_endI1_b : (⟨c.x + stepX, c.y⟩ == endCell) = false := by
                  cases h : (⟨c.x + stepX, c.y⟩ == endCell); rfl; exfalso; apply h_endI1; exact h
                have hI2 := rayMarchStep_done_or_cases start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y⟩
                rcases hI2 with ⟨hdI2, _⟩ | ⟨hdI2, hcI2 | hcI2 | hcI2⟩
                · right; left; exact ⟨h_end_b, hcF, hdF, h_endF1_b, hdF2_b, heF2, Or.inr ⟨hdI, Or.inl ⟨hcI, Or.inr (Or.inl hdI2)⟩⟩⟩
                · have heqI : (⟨c.x + stepX + stepX, c.y⟩ : Cell) = ⟨c.x + 2 * stepX, c.y⟩ := by
                    have : c.x + stepX + stepX = c.x + 2 * stepX := by omega
                    rw [this]
                  rw [heqI] at hcI2
                  right; left; exact ⟨h_end_b, hcF, hdF, h_endF1_b, hdF2_b, heF2, Or.inr ⟨hdI, Or.inl ⟨hcI, Or.inr (Or.inr (Or.inl hcI2))⟩⟩⟩
                · left; right; right; left
                  exact ⟨h_end_b, hdF, hcF, hdI, hcI, h_endI1_b, hdI2, hcI2⟩
                · have heqI : (⟨c.x + stepX + stepX, c.y + stepY⟩ : Cell) = ⟨c.x + 2 * stepX, c.y + stepY⟩ := by
                    have : c.x + stepX + stepX = c.x + 2 * stepX := by omega
                    rw [this]
                  rw [heqI] at hcI2
                  right; left; exact ⟨h_end_b, hcF, hdF, h_endF1_b, hdF2_b, heF2, Or.inr ⟨hdI, Or.inl ⟨hcI, Or.inr (Or.inr (Or.inr hcI2))⟩⟩⟩
            · by_cases h_endI1 : (⟨c.x, c.y + stepY⟩ == endCell) = true
              · right; left; exact ⟨h_end_b, hcF, hdF, h_endF1_b, hdF2_b, heF2, Or.inr ⟨hdI, Or.inr ⟨hcI, Or.inl h_endI1⟩⟩⟩
              · have h_endI1_b : (⟨c.x, c.y + stepY⟩ == endCell) = false := by
                  cases h : (⟨c.x, c.y + stepY⟩ == endCell); rfl; exfalso; apply h_endI1; exact h
                have hI2 := rayMarchStep_done_or_cases start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x, c.y + stepY⟩
                rcases hI2 with ⟨hdI2, _⟩ | ⟨hdI2, hcI2 | hcI2 | hcI2⟩
                · right; left; exact ⟨h_end_b, hcF, hdF, h_endF1_b, hdF2_b, heF2, Or.inr ⟨hdI, Or.inr ⟨hcI, Or.inr (Or.inl hdI2)⟩⟩⟩
                · left; right; right; right
                  exact ⟨h_end_b, hdF, hcF, hdI, hcI, h_endI1_b, hdI2, hcI2⟩
                · have heqI : (⟨c.x, c.y + stepY + stepY⟩ : Cell) = ⟨c.x, c.y + 2 * stepY⟩ := by
                    have : c.y + stepY + stepY = c.y + 2 * stepY := by omega
                    rw [this]
                  rw [heqI] at hcI2
                  right; left; exact ⟨h_end_b, hcF, hdF, h_endF1_b, hdF2_b, heF2, Or.inr ⟨hdI, Or.inr ⟨hcI, Or.inr (Or.inr (Or.inl hcI2))⟩⟩⟩
                · have heqI : (⟨c.x + stepX, c.y + stepY + stepY⟩ : Cell) = ⟨c.x + stepX, c.y + 2 * stepY⟩ := by
                    have : c.y + stepY + stepY = c.y + 2 * stepY := by omega
                    rw [this]
                  rw [heqI] at hcI2
                  right; left; exact ⟨h_end_b, hcF, hdF, h_endF1_b, hdF2_b, heF2, Or.inr ⟨hdI, Or.inr ⟨hcI, Or.inr (Or.inr (Or.inr hcI2))⟩⟩⟩
            · left; left; exact Or.inl ⟨by rw [hcF, hcI], by rw [hdF, hdI]⟩

def RayMarchCasesIdealInd
    (start : Point32) (ptEnd : Point)
    (dx dy : Binary64) (dxQ dyQ : ℚ) (stepX stepY : Int) (endCell : Cell) (c : Cell) : Prop :=
  RayMarchCasesIdealExt3 start ptEnd dx dy dxQ dyQ stepX stepY endCell c ∨
  -- Residual 1: Ideal steps diagonal at c, Float does NOT step diagonal at c and does NOT resynchronize via HalfDiamondFloatTransition
  ((c == endCell) = false ∧
   (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 = ⟨c.x + stepX, c.y + stepY⟩ ∧
   (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).2 = false ∧
   (⟨c.x + stepX, c.y + stepY⟩ == endCell) = false ∧
   (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y + stepY⟩).2 = false ∧
   (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y + stepY⟩).1 ≠ endCell ∧
   ((rayMarchStepFloat start dx dy stepX stepY c).2 = true ∨
    ((rayMarchStepFloat start dx dy stepX stepY c).2 = false ∧
     (((rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x + stepX, c.y⟩ ∧
       ((⟨c.x + stepX, c.y⟩ == endCell) = true ∨
        (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y⟩).2 = true ∨
        (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y⟩).1 = ⟨c.x + 2 * stepX, c.y⟩ ∨
        (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y⟩).1 = ⟨c.x + 2 * stepX, c.y + stepY⟩)) ∨
      ((rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x, c.y + stepY⟩ ∧
       ((⟨c.x, c.y + stepY⟩ == endCell) = true ∨
        (rayMarchStepFloat start dx dy stepX stepY ⟨c.x, c.y + stepY⟩).2 = true ∨
        (rayMarchStepFloat start dx dy stepX stepY ⟨c.x, c.y + stepY⟩).1 = ⟨c.x, c.y + 2 * stepY⟩ ∨
        (rayMarchStepFloat start dx dy stepX stepY ⟨c.x, c.y + stepY⟩).1 = ⟨c.x + stepX, c.y + 2 * stepY⟩)))))) ∨
  -- Residual 2: Ideal steps X then Y (or Y then X) to (c.x+stepX, c.y+stepY), and Float is done or doesn't resynchronize
  ((c == endCell) = false ∧
   (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).2 = false ∧
   (⟨c.x + stepX, c.y + stepY⟩ == endCell) = false ∧
   (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y + stepY⟩).2 = false ∧
   (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y + stepY⟩).1 ≠ endCell ∧
   (((rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 = ⟨c.x + stepX, c.y⟩ ∧
     (⟨c.x + stepX, c.y⟩ == endCell) = false ∧
     (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y⟩).2 = false ∧
     (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y⟩).1 = ⟨c.x + stepX, c.y + stepY⟩ ∧
     ((rayMarchStepFloat start dx dy stepX stepY c).2 = true ∨
      ((rayMarchStepFloat start dx dy stepX stepY c).2 = false ∧
       (rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x, c.y + stepY⟩ ∧
       ((⟨c.x, c.y + stepY⟩ == endCell) = true ∨
        (rayMarchStepFloat start dx dy stepX stepY ⟨c.x, c.y + stepY⟩).2 = true ∨
        (rayMarchStepFloat start dx dy stepX stepY ⟨c.x, c.y + stepY⟩).1 = ⟨c.x, c.y + 2 * stepY⟩ ∨
        (rayMarchStepFloat start dx dy stepX stepY ⟨c.x, c.y + stepY⟩).1 = ⟨c.x + stepX, c.y + 2 * stepY⟩)))) ∨
    ((rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 = ⟨c.x, c.y + stepY⟩ ∧
     (⟨c.x, c.y + stepY⟩ == endCell) = false ∧
     (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x, c.y + stepY⟩).2 = false ∧
     (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x, c.y + stepY⟩).1 = ⟨c.x + stepX, c.y + stepY⟩ ∧
     ((rayMarchStepFloat start dx dy stepX stepY c).2 = true ∨
      ((rayMarchStepFloat start dx dy stepX stepY c).2 = false ∧
       (rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x + stepX, c.y⟩ ∧
       ((⟨c.x + stepX, c.y⟩ == endCell) = true ∨
        (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y⟩).2 = true ∨
        (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y⟩).1 = ⟨c.x + 2 * stepX, c.y⟩ ∨
        (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y⟩).1 = ⟨c.x + 2 * stepX, c.y + stepY⟩)))))) ∨
  -- Residual 3: Ideal takes 2 steps in the same coordinate (2*stepX or 2*stepY) while disagreeing with Float at step 1
  ((c == endCell) = false ∧
   (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).2 = false ∧
   (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1).2 = false ∧
   (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1).1 ≠ endCell ∧
   ((((rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 = ⟨c.x + stepX, c.y⟩ ∧
      (⟨c.x + stepX, c.y⟩ == endCell) = false ∧
      ((rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y⟩).1 = ⟨c.x + 2 * stepX, c.y⟩ ∨
       (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y⟩).1 = ⟨c.x + 2 * stepX, c.y + stepY⟩) ∧
      ((rayMarchStepFloat start dx dy stepX stepY c).2 = true ∨
       ((rayMarchStepFloat start dx dy stepX stepY c).2 = false ∧
        ((rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x, c.y + stepY⟩ ∨
         (rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x + stepX, c.y + stepY⟩)))) ∨
     ((rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 = ⟨c.x, c.y + stepY⟩ ∧
      (⟨c.x, c.y + stepY⟩ == endCell) = false ∧
      ((rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x, c.y + stepY⟩).1 = ⟨c.x, c.y + 2 * stepY⟩ ∨
       (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x, c.y + stepY⟩).1 = ⟨c.x + stepX, c.y + 2 * stepY⟩) ∧
      ((rayMarchStepFloat start dx dy stepX stepY c).2 = true ∨
       ((rayMarchStepFloat start dx dy stepX stepY c).2 = false ∧
        ((rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x + stepX, c.y⟩ ∨
         (rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x + stepX, c.y + stepY⟩)))))))

theorem prove_cases_ideal_ind (start : Point32) (ptEnd : Point)
    (dx dy : Binary64) (dxQ dyQ : ℚ) (stepX stepY : Int) (endCell : Cell) (c : Cell) :
    RayMarchCasesIdealInd start ptEnd dx dy dxQ dyQ stepX stepY endCell c := by
  by_cases h_end : (c == endCell) = true
  · left; left; exact Or.inr (Or.inl (Or.inl h_end))
  · have h_end_b : (c == endCell) = false := by
      cases h : (c == endCell); rfl; exfalso; apply h_end; exact h
    have hF := rayMarchStepFloat_done_or_cases start dx dy stepX stepY c
    have hI := rayMarchStep_done_or_cases start.toPoint ptEnd dxQ dyQ stepX stepY c
    rcases hI with ⟨hdI, hcI⟩ | ⟨hdI, hcI | hcI | hcI⟩
    · left; left; exact Or.inr (Or.inl (Or.inr (Or.inl hdI)))
    · -- Ideal step 1 is X: ⟨c.x + stepX, c.y⟩
      by_cases h_endI1 : (⟨c.x + stepX, c.y⟩ == endCell) = true
      · left; left; exact Or.inr (Or.inl (Or.inr (Or.inr (by rw [hcI]; exact eq_of_beq h_endI1))))
      · have h_endI1_b : (⟨c.x + stepX, c.y⟩ == endCell) = false := by
          cases h : (⟨c.x + stepX, c.y⟩ == endCell); rfl; exfalso; apply h_endI1; exact h
        have hI2 := rayMarchStep_done_or_cases start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y⟩
        rcases hI2 with ⟨hdI2, hcI2⟩ | ⟨hdI2, hcI2 | hcI2 | hcI2⟩
        · left; left; exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (by rw [hcI]; exact hdI2)))))
        · -- Ideal step 2 is 2*X: ⟨c.x + 2*stepX, c.y⟩
          have heq : (⟨c.x + stepX + stepX, c.y⟩ : Cell) = ⟨c.x + 2 * stepX, c.y⟩ := by
            have : c.x + stepX + stepX = c.x + 2 * stepX := by omega
            rw [this]
          rw [heq] at hcI2
          by_cases h_endI2 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1).1 = endCell
          · left; left; exact Or.inr (Or.inr (Or.inl (Or.inl h_endI2)))
          · rcases hF with ⟨hdF, _⟩ | ⟨hdF, hcF | hcF | hcF⟩
            · right; right; right
              exact ⟨h_end_b, hdI, by rw [hcI]; exact hdI2, h_endI2, Or.inl ⟨hcI, h_endI1_b, Or.inl hcI2, Or.inl hdF⟩⟩
            · left; left; exact Or.inl ⟨by rw [hcF, hcI], by rw [hdF, hdI]⟩
            · right; right; right
              exact ⟨h_end_b, hdI, by rw [hcI]; exact hdI2, h_endI2, Or.inl ⟨hcI, h_endI1_b, Or.inl hcI2, Or.inr ⟨hdF, Or.inl hcF⟩⟩⟩
            · right; right; right
              exact ⟨h_end_b, hdI, by rw [hcI]; exact hdI2, h_endI2, Or.inl ⟨hcI, h_endI1_b, Or.inl hcI2, Or.inr ⟨hdF, Or.inr hcF⟩⟩⟩
        · -- Ideal step 2 is Y: ⟨c.x + stepX, c.y + stepY⟩
          by_cases h_endI2 : (⟨c.x + stepX, c.y + stepY⟩ == endCell) = true
          · left; left; exact Or.inr (Or.inr (Or.inl (Or.inl (by rw [hcI, hcI2]; exact eq_of_beq h_endI2))))
          · have h_endI2_b : (⟨c.x + stepX, c.y + stepY⟩ == endCell) = false := by
              cases h : (⟨c.x + stepX, c.y + stepY⟩ == endCell); rfl; exfalso; apply h_endI2; exact h
            by_cases hdI3 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y + stepY⟩).2 = true
            · left; left; exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl ⟨hcI, hcI2, hdI3⟩)))))
            · have hdI3_b : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y + stepY⟩).2 = false := by
                cases h : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y + stepY⟩).2; rfl; exfalso; apply hdI3; exact h
              by_cases heI3 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y + stepY⟩).1 = endCell
              · left; left; exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hcI, hcI2, heI3⟩)))))))
              · rcases hF with ⟨hdF, _⟩ | ⟨hdF, hcF | hcF | hcF⟩
                · right; right; left
                  exact ⟨h_end_b, hdI, h_endI2_b, hdI3_b, heI3, Or.inl ⟨hcI, h_endI1_b, hdI2, hcI2, Or.inl hdF⟩⟩
                · left; left; exact Or.inl ⟨by rw [hcF, hcI], by rw [hdF, hdI]⟩
                · by_cases h_endF1 : (⟨c.x, c.y + stepY⟩ == endCell) = true
                  · right; right; left
                    exact ⟨h_end_b, hdI, h_endI2_b, hdI3_b, heI3, Or.inl ⟨hcI, h_endI1_b, hdI2, hcI2, Or.inr ⟨hdF, hcF, Or.inl h_endF1⟩⟩⟩
                  · have h_endF1_b : (⟨c.x, c.y + stepY⟩ == endCell) = false := by
                      cases h : (⟨c.x, c.y + stepY⟩ == endCell); rfl; exfalso; apply h_endF1; exact h
                    have hF2 := rayMarchStepFloat_done_or_cases start dx dy stepX stepY ⟨c.x, c.y + stepY⟩
                    rcases hF2 with ⟨hdF2, _⟩ | ⟨hdF2, hcF2 | hcF2 | hcF2⟩
                    · right; right; left
                      exact ⟨h_end_b, hdI, h_endI2_b, hdI3_b, heI3, Or.inl ⟨hcI, h_endI1_b, hdI2, hcI2, Or.inr ⟨hdF, hcF, Or.inr (Or.inl hdF2)⟩⟩⟩
                    · left; left; right; right; right; right
                      exact ⟨h_end_b, hdF, hcF, h_endF1_b, hdF2, hcF2, hdI, hcI, h_endI1_b, hdI2, hcI2⟩
                    · have heqF : (⟨c.x, c.y + stepY + stepY⟩ : Cell) = ⟨c.x, c.y + 2 * stepY⟩ := by
                        have : c.y + stepY + stepY = c.y + 2 * stepY := by omega
                        rw [this]
                      rw [heqF] at hcF2
                      right; right; left
                      exact ⟨h_end_b, hdI, h_endI2_b, hdI3_b, heI3, Or.inl ⟨hcI, h_endI1_b, hdI2, hcI2, Or.inr ⟨hdF, hcF, Or.inr (Or.inr (Or.inl hcF2))⟩⟩⟩
                    · have heqF : (⟨c.x + stepX, c.y + stepY + stepY⟩ : Cell) = ⟨c.x + stepX, c.y + 2 * stepY⟩ := by
                        have : c.y + stepY + stepY = c.y + 2 * stepY := by omega
                        rw [this]
                      rw [heqF] at hcF2
                      right; right; left
                      exact ⟨h_end_b, hdI, h_endI2_b, hdI3_b, heI3, Or.inl ⟨hcI, h_endI1_b, hdI2, hcI2, Or.inr ⟨hdF, hcF, Or.inr (Or.inr (Or.inr hcF2))⟩⟩⟩
                · -- Float stepped diagonal at c! Half-diamond!
                  left; right; left; left
                  exact ⟨h_end_b, hdF, hcF, hdI, hcI, h_endI1_b, hdI2, hcI2⟩
        · -- Ideal step 2 is diagonal: ⟨c.x + 2*stepX, c.y + stepY⟩
          have heq : (⟨c.x + stepX + stepX, c.y + stepY⟩ : Cell) = ⟨c.x + 2 * stepX, c.y + stepY⟩ := by
            have : c.x + stepX + stepX = c.x + 2 * stepX := by omega
            rw [this]
          rw [heq] at hcI2
          by_cases h_endI2 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1).1 = endCell
          · left; left; exact Or.inr (Or.inr (Or.inl (Or.inl h_endI2)))
          · rcases hF with ⟨hdF, _⟩ | ⟨hdF, hcF | hcF | hcF⟩
            · right; right; right
              exact ⟨h_end_b, hdI, by rw [hcI]; exact hdI2, h_endI2, Or.inl ⟨hcI, h_endI1_b, Or.inr hcI2, Or.inl hdF⟩⟩
            · left; left; exact Or.inl ⟨by rw [hcF, hcI], by rw [hdF, hdI]⟩
            · right; right; right
              exact ⟨h_end_b, hdI, by rw [hcI]; exact hdI2, h_endI2, Or.inl ⟨hcI, h_endI1_b, Or.inr hcI2, Or.inr ⟨hdF, Or.inl hcF⟩⟩⟩
            · right; right; right
              exact ⟨h_end_b, hdI, by rw [hcI]; exact hdI2, h_endI2, Or.inl ⟨hcI, h_endI1_b, Or.inr hcI2, Or.inr ⟨hdF, Or.inr hcF⟩⟩⟩
    · -- Ideal step 1 is Y: ⟨c.x, c.y + stepY⟩
      by_cases h_endI1 : (⟨c.x, c.y + stepY⟩ == endCell) = true
      · left; left; exact Or.inr (Or.inl (Or.inr (Or.inr (by rw [hcI]; exact eq_of_beq h_endI1))))
      · have h_endI1_b : (⟨c.x, c.y + stepY⟩ == endCell) = false := by
          cases h : (⟨c.x, c.y + stepY⟩ == endCell); rfl; exfalso; apply h_endI1; exact h
        have hI2 := rayMarchStep_done_or_cases start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x, c.y + stepY⟩
        rcases hI2 with ⟨hdI2, hcI2⟩ | ⟨hdI2, hcI2 | hcI2 | hcI2⟩
        · left; left; exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (by rw [hcI]; exact hdI2)))))
        · -- Ideal step 2 is X: ⟨c.x + stepX, c.y + stepY⟩
          by_cases h_endI2 : (⟨c.x + stepX, c.y + stepY⟩ == endCell) = true
          · left; left; exact Or.inr (Or.inr (Or.inl (Or.inl (by rw [hcI, hcI2]; exact eq_of_beq h_endI2))))
          · have h_endI2_b : (⟨c.x + stepX, c.y + stepY⟩ == endCell) = false := by
              cases h : (⟨c.x + stepX, c.y + stepY⟩ == endCell); rfl; exfalso; apply h_endI2; exact h
            by_cases hdI3 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y + stepY⟩).2 = true
            · left; left; exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨hcI, hcI2, hdI3⟩))))))
            · have hdI3_b : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y + stepY⟩).2 = false := by
                cases h : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y + stepY⟩).2; rfl; exfalso; apply hdI3; exact h
              by_cases heI3 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y + stepY⟩).1 = endCell
              · left; left; exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hcI, hcI2, heI3⟩))))))))
              · rcases hF with ⟨hdF, _⟩ | ⟨hdF, hcF | hcF | hcF⟩
                · right; right; left
                  exact ⟨h_end_b, hdI, h_endI2_b, hdI3_b, heI3, Or.inr ⟨hcI, h_endI1_b, hdI2, hcI2, Or.inl hdF⟩⟩
                · by_cases h_endF1 : (⟨c.x + stepX, c.y⟩ == endCell) = true
                  · right; right; left
                    exact ⟨h_end_b, hdI, h_endI2_b, hdI3_b, heI3, Or.inr ⟨hcI, h_endI1_b, hdI2, hcI2, Or.inr ⟨hdF, hcF, Or.inl h_endF1⟩⟩⟩
                  · have h_endF1_b : (⟨c.x + stepX, c.y⟩ == endCell) = false := by
                      cases h : (⟨c.x + stepX, c.y⟩ == endCell); rfl; exfalso; apply h_endF1; exact h
                    have hF2 := rayMarchStepFloat_done_or_cases start dx dy stepX stepY ⟨c.x + stepX, c.y⟩
                    rcases hF2 with ⟨hdF2, _⟩ | ⟨hdF2, hcF2 | hcF2 | hcF2⟩
                    · right; right; left
                      exact ⟨h_end_b, hdI, h_endI2_b, hdI3_b, heI3, Or.inr ⟨hcI, h_endI1_b, hdI2, hcI2, Or.inr ⟨hdF, hcF, Or.inr (Or.inl hdF2)⟩⟩⟩
                    · have heqF : (⟨c.x + stepX + stepX, c.y⟩ : Cell) = ⟨c.x + 2 * stepX, c.y⟩ := by
                        have : c.x + stepX + stepX = c.x + 2 * stepX := by omega
                        rw [this]
                      rw [heqF] at hcF2
                      right; right; left
                      exact ⟨h_end_b, hdI, h_endI2_b, hdI3_b, heI3, Or.inr ⟨hcI, h_endI1_b, hdI2, hcI2, Or.inr ⟨hdF, hcF, Or.inr (Or.inr (Or.inl hcF2))⟩⟩⟩
                    · left; left; right; right; right; left
                      exact ⟨h_end_b, hdF, hcF, h_endF1_b, hdF2, hcF2, hdI, hcI, h_endI1_b, hdI2, hcI2⟩
                    · have heqF : (⟨c.x + stepX + stepX, c.y + stepY⟩ : Cell) = ⟨c.x + 2 * stepX, c.y + stepY⟩ := by
                        have : c.x + stepX + stepX = c.x + 2 * stepX := by omega
                        rw [this]
                      rw [heqF] at hcF2
                      right; right; left
                      exact ⟨h_end_b, hdI, h_endI2_b, hdI3_b, heI3, Or.inr ⟨hcI, h_endI1_b, hdI2, hcI2, Or.inr ⟨hdF, hcF, Or.inr (Or.inr (Or.inr hcF2))⟩⟩⟩
                · left; left; exact Or.inl ⟨by rw [hcF, hcI], by rw [hdF, hdI]⟩
                · -- Float stepped diagonal at c! Half-diamond!
                  left; right; left; right
                  exact ⟨h_end_b, hdF, hcF, hdI, hcI, h_endI1_b, hdI2, hcI2⟩
        · -- Ideal step 2 is 2*Y: ⟨c.x, c.y + 2*stepY⟩
          have heq : (⟨c.x, c.y + stepY + stepY⟩ : Cell) = ⟨c.x, c.y + 2 * stepY⟩ := by
            have : c.y + stepY + stepY = c.y + 2 * stepY := by omega
            rw [this]
          rw [heq] at hcI2
          by_cases h_endI2 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1).1 = endCell
          · left; left; exact Or.inr (Or.inr (Or.inl (Or.inl h_endI2)))
          · rcases hF with ⟨hdF, _⟩ | ⟨hdF, hcF | hcF | hcF⟩
            · right; right; right
              exact ⟨h_end_b, hdI, by rw [hcI]; exact hdI2, h_endI2, Or.inr ⟨hcI, h_endI1_b, Or.inl hcI2, Or.inl hdF⟩⟩
            · right; right; right
              exact ⟨h_end_b, hdI, by rw [hcI]; exact hdI2, h_endI2, Or.inr ⟨hcI, h_endI1_b, Or.inl hcI2, Or.inr ⟨hdF, Or.inl hcF⟩⟩⟩
            · left; left; exact Or.inl ⟨by rw [hcF, hcI], by rw [hdF, hdI]⟩
            · right; right; right
              exact ⟨h_end_b, hdI, by rw [hcI]; exact hdI2, h_endI2, Or.inr ⟨hcI, h_endI1_b, Or.inl hcI2, Or.inr ⟨hdF, Or.inr hcF⟩⟩⟩
        · -- Ideal step 2 is diagonal: ⟨c.x + stepX, c.y + 2*stepY⟩
          have heq : (⟨c.x + stepX, c.y + stepY + stepY⟩ : Cell) = ⟨c.x + stepX, c.y + 2 * stepY⟩ := by
            have : c.y + stepY + stepY = c.y + 2 * stepY := by omega
            rw [this]
          rw [heq] at hcI2
          by_cases h_endI2 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1).1 = endCell
          · left; left; exact Or.inr (Or.inr (Or.inl (Or.inl h_endI2)))
          · rcases hF with ⟨hdF, _⟩ | ⟨hdF, hcF | hcF | hcF⟩
            · right; right; right
              exact ⟨h_end_b, hdI, by rw [hcI]; exact hdI2, h_endI2, Or.inr ⟨hcI, h_endI1_b, Or.inr hcI2, Or.inl hdF⟩⟩
            · right; right; right
              exact ⟨h_end_b, hdI, by rw [hcI]; exact hdI2, h_endI2, Or.inr ⟨hcI, h_endI1_b, Or.inr hcI2, Or.inr ⟨hdF, Or.inl hcF⟩⟩⟩
            · left; left; exact Or.inl ⟨by rw [hcF, hcI], by rw [hdF, hdI]⟩
            · right; right; right
              exact ⟨h_end_b, hdI, by rw [hcI]; exact hdI2, h_endI2, Or.inr ⟨hcI, h_endI1_b, Or.inr hcI2, Or.inr ⟨hdF, Or.inr hcF⟩⟩⟩
    · -- Ideal step 1 is diagonal: ⟨c.x + stepX, c.y + stepY⟩
      by_cases h_endI1 : (⟨c.x + stepX, c.y + stepY⟩ == endCell) = true
      · left; left; exact Or.inr (Or.inl (Or.inr (Or.inr (by rw [hcI]; exact eq_of_beq h_endI1))))
      · by_cases hdI2 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y + stepY⟩).2 = true
        · left; left; exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hcI, hdI2⟩)))))))))
        · by_cases heI2 : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y + stepY⟩).1 = endCell
          · left; left; exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hcI, heI2⟩)))))))))
          · have h_endI1_b : (⟨c.x + stepX, c.y + stepY⟩ == endCell) = false := by
              cases h : (⟨c.x + stepX, c.y + stepY⟩ == endCell); rfl; exfalso; apply h_endI1; exact h
            have hdI2_b : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y + stepY⟩).2 = false := by
              cases h : (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y + stepY⟩).2; rfl; exfalso; apply hdI2; exact h
            rcases hF with ⟨hdF, _⟩ | ⟨hdF, hcF | hcF | hcF⟩
            · right; left; exact ⟨h_end_b, hcI, hdI, h_endI1_b, hdI2_b, heI2, Or.inl hdF⟩
            · by_cases h_endF1 : (⟨c.x + stepX, c.y⟩ == endCell) = true
              · right; left; exact ⟨h_end_b, hcI, hdI, h_endI1_b, hdI2_b, heI2, Or.inr ⟨hdF, Or.inl ⟨hcF, Or.inl h_endF1⟩⟩⟩
              · have h_endF1_b : (⟨c.x + stepX, c.y⟩ == endCell) = false := by
                  cases h : (⟨c.x + stepX, c.y⟩ == endCell); rfl; exfalso; apply h_endF1; exact h
                have hF2 := rayMarchStepFloat_done_or_cases start dx dy stepX stepY ⟨c.x + stepX, c.y⟩
                rcases hF2 with ⟨hdF2, _⟩ | ⟨hdF2, hcF2 | hcF2 | hcF2⟩
                · right; left; exact ⟨h_end_b, hcI, hdI, h_endI1_b, hdI2_b, heI2, Or.inr ⟨hdF, Or.inl ⟨hcF, Or.inr (Or.inl hdF2)⟩⟩⟩
                · have heqF : (⟨c.x + stepX + stepX, c.y⟩ : Cell) = ⟨c.x + 2 * stepX, c.y⟩ := by
                    have : c.x + stepX + stepX = c.x + 2 * stepX := by omega
                    rw [this]
                  rw [heqF] at hcF2
                  right; left; exact ⟨h_end_b, hcI, hdI, h_endI1_b, hdI2_b, heI2, Or.inr ⟨hdF, Or.inl ⟨hcF, Or.inr (Or.inr (Or.inl hcF2))⟩⟩⟩
                · left; right; right; left
                  exact ⟨h_end_b, hdF, hcF, h_endF1_b, hdF2, hcF2, hdI, hcI⟩
                · have heqF : (⟨c.x + stepX + stepX, c.y + stepY⟩ : Cell) = ⟨c.x + 2 * stepX, c.y + stepY⟩ := by
                    have : c.x + stepX + stepX = c.x + 2 * stepX := by omega
                    rw [this]
                  rw [heqF] at hcF2
                  right; left; exact ⟨h_end_b, hcI, hdI, h_endI1_b, hdI2_b, heI2, Or.inr ⟨hdF, Or.inl ⟨hcF, Or.inr (Or.inr (Or.inr hcF2))⟩⟩⟩
            · by_cases h_endF1 : (⟨c.x, c.y + stepY⟩ == endCell) = true
              · right; left; exact ⟨h_end_b, hcI, hdI, h_endI1_b, hdI2_b, heI2, Or.inr ⟨hdF, Or.inr ⟨hcF, Or.inl h_endF1⟩⟩⟩
              · have h_endF1_b : (⟨c.x, c.y + stepY⟩ == endCell) = false := by
                  cases h : (⟨c.x, c.y + stepY⟩ == endCell); rfl; exfalso; apply h_endF1; exact h
                have hF2 := rayMarchStepFloat_done_or_cases start dx dy stepX stepY ⟨c.x, c.y + stepY⟩
                rcases hF2 with ⟨hdF2, _⟩ | ⟨hdF2, hcF2 | hcF2 | hcF2⟩
                · right; left; exact ⟨h_end_b, hcI, hdI, h_endI1_b, hdI2_b, heI2, Or.inr ⟨hdF, Or.inr ⟨hcF, Or.inr (Or.inl hdF2)⟩⟩⟩
                · left; right; right; right
                  exact ⟨h_end_b, hdF, hcF, h_endF1_b, hdF2, hcF2, hdI, hcI⟩
                · have heqF : (⟨c.x, c.y + stepY + stepY⟩ : Cell) = ⟨c.x, c.y + 2 * stepY⟩ := by
                    have : c.y + stepY + stepY = c.y + 2 * stepY := by omega
                    rw [this]
                  rw [heqF] at hcF2
                  right; left; exact ⟨h_end_b, hcI, hdI, h_endI1_b, hdI2_b, heI2, Or.inr ⟨hdF, Or.inr ⟨hcF, Or.inr (Or.inr (Or.inl hcF2))⟩⟩⟩
                · have heqF : (⟨c.x + stepX, c.y + stepY + stepY⟩ : Cell) = ⟨c.x + stepX, c.y + 2 * stepY⟩ := by
                    have : c.y + stepY + stepY = c.y + 2 * stepY := by omega
                    rw [this]
                  rw [heqF] at hcF2
                  right; left; exact ⟨h_end_b, hcI, hdI, h_endI1_b, hdI2_b, heI2, Or.inr ⟨hdF, Or.inr ⟨hcF, Or.inr (Or.inr (Or.inr hcF2))⟩⟩⟩
            · left; left; exact Or.inl ⟨by rw [hcF, hcI], by rw [hdF, hdI]⟩

theorem step_not_X_when_stepX_zero (start : Point32) (dx dy : Binary64) (stepY : ℤ) (c : Cell)
    (hd : (rayMarchStepFloat start dx dy 0 stepY c).2 = false) :
    (rayMarchStepFloat start dx dy 0 stepY c).1 = ⟨c.x, c.y + stepY⟩ := by
  unfold rayMarchStepFloat at hd ⊢
  dsimp only [] at hd ⊢
  have hx_b : ((0 : Int) == 0) = true := rfl
  rw [hx_b] at hd ⊢
  simp only [ite_true] at hd ⊢
  split_ifs at hd ⊢ <;> simp at hd ⊢

theorem step_not_Y_when_stepY_zero (start : Point32) (dx dy : Binary64) (stepX : ℤ) (c : Cell)
    (hx : stepX ≠ 0)
    (hd : (rayMarchStepFloat start dx dy stepX 0 c).2 = false) :
    (rayMarchStepFloat start dx dy stepX 0 c).1 = ⟨c.x + stepX, c.y⟩ := by
  unfold rayMarchStepFloat at hd ⊢
  dsimp only [] at hd ⊢
  have hx_b : (stepX == 0) = false := by
    cases h : (stepX == 0)
    · rfl
    · exfalso; apply hx; exact eq_of_beq h
  have hy_b : ((0 : Int) == 0) = true := rfl
  rw [hx_b, hy_b] at hd ⊢
  simp only [Bool.false_eq_true, ite_false, ite_true] at hd ⊢
  split_ifs at hd ⊢ <;> simp at hd ⊢

set_option maxHeartbeats 800000 in
private theorem prove_cases_float_ext3_of_cellInBox
    (A B : Point32) (stepX stepY : ℤ) (c : Cell)
    (h_finiteA : A.isFinite) (h_finiteB : B.isFinite)
    (h_bound : inCoordBounds mainCoordBound A.toPoint B.toPoint)
    (hx0 : (stepX == 0) = false) (hy0 : (stepY == 0) = false)
    (hc : CellInBox A B stepX stepY c) :
    RayMarchCasesFloatExt3 A B.toPoint (deltaX A B) (deltaY A B)
      (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y)
      stepX stepY (floorPoint B.toPoint) c := by
  have h_ind := prove_cases_float_ind A B.toPoint (deltaX A B) (deltaY A B)
    (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y)
    stepX stepY (floorPoint B.toPoint) c
  obtain ⟨⟨hcx_bnd, hcy_bnd, hcx1_bnd, hcy1_bnd⟩,
          ⟨hdx_pos, hdy_pos, hlim_pos, hcxR_ge, hcyR_ge⟩,
          ⟨hlim_dx, hlim_dy, hcx_le_dy, hcy_le_dx⟩,
          ⟨hcx_step1, hcx_step2, hcy_step1, hcy_step2⟩,
          ⟨hend_x0, hend_x1, hend_y0, hend_y1⟩⟩ :=
    cellInBox_real_facts A B stepX stepY c h_bound hc hx0 hy0
  have hF_c :=
    rayMarchStepFloat_real_bounds A B stepX stepY c
      h_finiteA h_finiteB h_bound hx0 hy0 hcx_bnd hcy_bnd
  have hF_x :=
    rayMarchStepFloat_real_bounds A B stepX stepY ⟨c.x + stepX, c.y⟩
      h_finiteA h_finiteB h_bound hx0 hy0 hcx1_bnd hcy_bnd
  have hF_y :=
    rayMarchStepFloat_real_bounds A B stepX stepY ⟨c.x, c.y + stepY⟩
      h_finiteA h_finiteB h_bound hx0 hy0 hcx_bnd hcy1_bnd
  have hF_xy :=
    rayMarchStepFloat_real_bounds A B stepX stepY ⟨c.x + stepX, c.y + stepY⟩
      h_finiteA h_finiteB h_bound hx0 hy0 hcx1_bnd hcy1_bnd
  have hI_c := rayMarchStep_real_bounds A B stepX stepY c hx0 hy0
  have hI_x := rayMarchStep_real_bounds A B stepX stepY ⟨c.x + stepX, c.y⟩ hx0 hy0
  have hI_y := rayMarchStep_real_bounds A B stepX stepY ⟨c.x, c.y + stepY⟩ hx0 hy0
  have hI_xy := rayMarchStep_real_bounds A B stepX stepY ⟨c.x + stepX, c.y + stepY⟩ hx0 hy0
  dsimp only [] at hF_c hF_x hF_y hF_xy hI_c hI_x hI_y hI_xy
  have heq_2x : c.x + stepX + stepX = c.x + 2 * stepX := by omega
  have heq_2y : c.y + stepY + stepY = c.y + 2 * stepY := by omega
  rw [hcx_step1, heq_2x] at hF_x hI_x
  rw [hcy_step1, heq_2y] at hF_y hI_y
  rw [maxCoordDelta_toReal_eval] at hlim_dx hlim_dy
  rw [maxCellBoundaryDistance_toReal_eval] at hcx_le_dy hcy_le_dx
  rw [epsRayMarch_toReal_eval] at hF_c hF_x hF_y hF_xy
  rcases h_ind with h_ext3 | h_res1 | h_res2 | h_res3
  · exact h_ext3
  · exfalso
    rcases h_res1 with ⟨_, hsF1, hdF1, _, hdF_xy, _, hdI1 | ⟨hdI1, ⟨hsI1, hI_sub⟩ | ⟨hsI1, hI_sub⟩⟩⟩
    · have := (hF_c.2 hdF1).2.2.2 hsF1; have := hI_c.1 hdI1
      rcases (hF_xy.2 hdF_xy).1 with h | h <;> linarith
    · have := (hF_c.2 hdF1).2.2.2 hsF1; have := (hI_c.2 hdI1).2.1 hsI1
      have hF_xy_min := (hF_xy.2 hdF_xy).1
      rcases hI_sub with hend | hdI2 | hsI2 | hsI2
      · have heq := eq_of_beq hend
        have hy_eq : c.y = (floorPoint B.toPoint).y := by simpa using congrArg Cell.y heq
        have := hend_y0 hy_eq
        rcases hF_xy_min with h | h <;> linarith
      · have := hI_x.1 hdI2; rcases hF_xy_min with h | h <;> linarith
      · have hdI2 : (rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y) stepX stepY ⟨c.x + stepX, c.y⟩).2 = false := by
          cases h : (rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y) stepX stepY ⟨c.x + stepX, c.y⟩).2
          · rfl
          · have := hI_x.1 h; rcases hF_xy_min with h' | h' <;> linarith
        have := (hI_x.2 hdI2).2.1 hsI2; linarith
      · have hdI2 : (rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y) stepX stepY ⟨c.x + stepX, c.y⟩).2 = false := by
          cases h : (rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y) stepX stepY ⟨c.x + stepX, c.y⟩).2
          · rfl
          · have := hI_x.1 h; rcases hF_xy_min with h' | h' <;> linarith
        have := (hI_x.2 hdI2).2.2.2 hsI2; linarith
    · have := (hF_c.2 hdF1).2.2.2 hsF1; have := (hI_c.2 hdI1).2.2.1 hsI1
      have hF_xy_min := (hF_xy.2 hdF_xy).1
      rcases hI_sub with hend | hdI2 | hsI2 | hsI2
      · have heq := eq_of_beq hend
        have hx_eq : c.x = (floorPoint B.toPoint).x := by simpa using congrArg Cell.x heq
        have := hend_x0 hx_eq
        rcases hF_xy_min with h | h <;> linarith
      · have := hI_y.1 hdI2; rcases hF_xy_min with h | h <;> linarith
      · have hdI2 : (rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y) stepX stepY ⟨c.x, c.y + stepY⟩).2 = false := by
          cases h : (rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y) stepX stepY ⟨c.x, c.y + stepY⟩).2
          · rfl
          · have := hI_y.1 h; rcases hF_xy_min with h' | h' <;> linarith
        have := (hI_y.2 hdI2).2.2.1 hsI2; linarith
      · have hdI2 : (rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y) stepX stepY ⟨c.x, c.y + stepY⟩).2 = false := by
          cases h : (rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y) stepX stepY ⟨c.x, c.y + stepY⟩).2
          · rfl
          · have := hI_y.1 h; rcases hF_xy_min with h' | h' <;> linarith
        have := (hI_y.2 hdI2).2.2.2 hsI2; linarith
  · exfalso
    rcases h_res2 with ⟨_, hdF1, _, hdF_xy, _, ⟨hsF1, _, hdF2, hsF2, hdI1 | ⟨hdI1, hsI1, hI_sub⟩⟩ | ⟨hsF1, _, hdF2, hsF2, hdI1 | ⟨hdI1, hsI1, hI_sub⟩⟩⟩
    · have := (hF_c.2 hdF1).2.1 hsF1; have := hI_c.1 hdI1
      rcases (hF_xy.2 hdF_xy).1 with h | h <;> linarith
    · have := (hF_c.2 hdF1).2.1 hsF1; have := (hF_x.2 hdF2).2.2.1 hsF2
      have := (hI_c.2 hdI1).2.2.1 hsI1; have hF_xy_min := (hF_xy.2 hdF_xy).1
      rcases hI_sub with hend | hdI2 | hsI2 | hsI2
      · have heq := eq_of_beq hend
        have hx_eq : c.x = (floorPoint B.toPoint).x := by simpa using congrArg Cell.x heq
        have := hend_x0 hx_eq
        rcases hF_xy_min with h | h <;> linarith
      · have := hI_y.1 hdI2; rcases hF_xy_min with h | h <;> linarith
      · have hdI2 : (rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y) stepX stepY ⟨c.x, c.y + stepY⟩).2 = false := by
          cases h : (rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y) stepX stepY ⟨c.x, c.y + stepY⟩).2
          · rfl
          · have := hI_y.1 h; rcases hF_xy_min with h' | h' <;> linarith
        have := (hI_y.2 hdI2).2.2.1 hsI2; linarith
      · have hdI2 : (rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y) stepX stepY ⟨c.x, c.y + stepY⟩).2 = false := by
          cases h : (rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y) stepX stepY ⟨c.x, c.y + stepY⟩).2
          · rfl
          · have := hI_y.1 h; rcases hF_xy_min with h' | h' <;> linarith
        have := (hI_y.2 hdI2).2.2.2 hsI2; linarith
    · have := (hF_c.2 hdF1).2.2.1 hsF1; have := hI_c.1 hdI1
      rcases (hF_xy.2 hdF_xy).1 with h | h <;> linarith
    · have := (hF_c.2 hdF1).2.2.1 hsF1; have := (hF_y.2 hdF2).2.1 hsF2
      have := (hI_c.2 hdI1).2.1 hsI1; have hF_xy_min := (hF_xy.2 hdF_xy).1
      rcases hI_sub with hend | hdI2 | hsI2 | hsI2
      · have heq := eq_of_beq hend
        have hy_eq : c.y = (floorPoint B.toPoint).y := by simpa using congrArg Cell.y heq
        have := hend_y0 hy_eq
        rcases hF_xy_min with h | h <;> linarith
      · have := hI_x.1 hdI2; rcases hF_xy_min with h | h <;> linarith
      · have hdI2 : (rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y) stepX stepY ⟨c.x + stepX, c.y⟩).2 = false := by
          cases h : (rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y) stepX stepY ⟨c.x + stepX, c.y⟩).2
          · rfl
          · have := hI_x.1 h; rcases hF_xy_min with h' | h' <;> linarith
        have := (hI_x.2 hdI2).2.1 hsI2; linarith
      · have hdI2 : (rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y) stepX stepY ⟨c.x + stepX, c.y⟩).2 = false := by
          cases h : (rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y) stepX stepY ⟨c.x + stepX, c.y⟩).2
          · rfl
          · have := hI_x.1 h; rcases hF_xy_min with h' | h' <;> linarith
        have := (hI_x.2 hdI2).2.2.2 hsI2; linarith
  · exfalso
    rcases h_res3 with ⟨_, hdF1, hdF2, _, ⟨hsF1, _, hsF2 | hsF2, hdI1 | ⟨hdI1, hsI1 | hsI1⟩⟩ | ⟨hsF1, _, hsF2 | hsF2, hdI1 | ⟨hdI1, hsI1 | hsI1⟩⟩⟩
    · rw [hsF1] at hdF2; have := (hF_c.2 hdF1).2.1 hsF1; have := (hF_x.2 hdF2).2.1 hsF2; have := hI_c.1 hdI1; linarith
    · rw [hsF1] at hdF2; have := (hF_c.2 hdF1).2.1 hsF1; have := (hF_x.2 hdF2).2.1 hsF2; have := (hI_c.2 hdI1).2.2.1 hsI1; linarith
    · rw [hsF1] at hdF2; have := (hF_c.2 hdF1).2.1 hsF1; have := (hF_x.2 hdF2).2.1 hsF2; have := (hI_c.2 hdI1).2.2.2 hsI1; linarith
    · rw [hsF1] at hdF2; have := (hF_c.2 hdF1).2.1 hsF1; have := (hF_x.2 hdF2).2.2.2 hsF2; have := hI_c.1 hdI1; linarith
    · rw [hsF1] at hdF2; have := (hF_c.2 hdF1).2.1 hsF1; have := (hF_x.2 hdF2).2.2.2 hsF2; have := (hI_c.2 hdI1).2.2.1 hsI1; linarith
    · rw [hsF1] at hdF2; have := (hF_c.2 hdF1).2.1 hsF1; have := (hF_x.2 hdF2).2.2.2 hsF2; have := (hI_c.2 hdI1).2.2.2 hsI1; linarith
    · rw [hsF1] at hdF2; have := (hF_c.2 hdF1).2.2.1 hsF1; have := (hF_y.2 hdF2).2.2.1 hsF2; have := hI_c.1 hdI1; linarith
    · rw [hsF1] at hdF2; have := (hF_c.2 hdF1).2.2.1 hsF1; have := (hF_y.2 hdF2).2.2.1 hsF2; have := (hI_c.2 hdI1).2.1 hsI1; linarith
    · rw [hsF1] at hdF2; have := (hF_c.2 hdF1).2.2.1 hsF1; have := (hF_y.2 hdF2).2.2.1 hsF2; have := (hI_c.2 hdI1).2.2.2 hsI1; linarith
    · rw [hsF1] at hdF2; have := (hF_c.2 hdF1).2.2.1 hsF1; have := (hF_y.2 hdF2).2.2.2 hsF2; have := hI_c.1 hdI1; linarith
    · rw [hsF1] at hdF2; have := (hF_c.2 hdF1).2.2.1 hsF1; have := (hF_y.2 hdF2).2.2.2 hsF2; have := (hI_c.2 hdI1).2.1 hsI1; linarith
    · rw [hsF1] at hdF2; have := (hF_c.2 hdF1).2.2.1 hsF1; have := (hF_y.2 hdF2).2.2.2 hsF2; have := (hI_c.2 hdI1).2.2.2 hsI1; linarith

set_option maxHeartbeats 800000 in
private theorem prove_cases_ideal_ext3_of_cellInBox
    (A B : Point32) (stepX stepY : ℤ) (c : Cell)
    (h_finiteA : A.isFinite) (h_finiteB : B.isFinite)
    (h_bound : inCoordBounds mainCoordBound A.toPoint B.toPoint)
    (hx0 : (stepX == 0) = false) (hy0 : (stepY == 0) = false)
    (hc : CellInBox A B stepX stepY c) :
    RayMarchCasesIdealExt3 A B.toPoint (deltaX A B) (deltaY A B)
      (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y)
      stepX stepY (floorPoint B.toPoint) c := by
  have h_ind := prove_cases_ideal_ind A B.toPoint (deltaX A B) (deltaY A B)
    (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y)
    stepX stepY (floorPoint B.toPoint) c
  obtain ⟨⟨hcx_bnd, hcy_bnd, hcx1_bnd, hcy1_bnd⟩,
          ⟨hdx_pos, hdy_pos, hlim_pos, hcxR_ge, hcyR_ge⟩,
          ⟨hlim_dx, hlim_dy, hcx_le_dy, hcy_le_dx⟩,
          ⟨hcx_step1, hcx_step2, hcy_step1, hcy_step2⟩,
          ⟨hend_x0, hend_x1, hend_y0, hend_y1⟩⟩ :=
    cellInBox_real_facts A B stepX stepY c h_bound hc hx0 hy0
  have hF_c :=
    rayMarchStepFloat_real_bounds A B stepX stepY c
      h_finiteA h_finiteB h_bound hx0 hy0 hcx_bnd hcy_bnd
  have hF_x :=
    rayMarchStepFloat_real_bounds A B stepX stepY ⟨c.x + stepX, c.y⟩
      h_finiteA h_finiteB h_bound hx0 hy0 hcx1_bnd hcy_bnd
  have hF_y :=
    rayMarchStepFloat_real_bounds A B stepX stepY ⟨c.x, c.y + stepY⟩
      h_finiteA h_finiteB h_bound hx0 hy0 hcx_bnd hcy1_bnd
  have hF_xy :=
    rayMarchStepFloat_real_bounds A B stepX stepY ⟨c.x + stepX, c.y + stepY⟩
      h_finiteA h_finiteB h_bound hx0 hy0 hcx1_bnd hcy1_bnd
  have hI_c := rayMarchStep_real_bounds A B stepX stepY c hx0 hy0
  have hI_x := rayMarchStep_real_bounds A B stepX stepY ⟨c.x + stepX, c.y⟩ hx0 hy0
  have hI_y := rayMarchStep_real_bounds A B stepX stepY ⟨c.x, c.y + stepY⟩ hx0 hy0
  have hI_xy := rayMarchStep_real_bounds A B stepX stepY ⟨c.x + stepX, c.y + stepY⟩ hx0 hy0
  dsimp only [] at hF_c hF_x hF_y hF_xy hI_c hI_x hI_y hI_xy
  have heq_2x : c.x + stepX + stepX = c.x + 2 * stepX := by omega
  have heq_2y : c.y + stepY + stepY = c.y + 2 * stepY := by omega
  rw [hcx_step1, heq_2x] at hF_x hI_x
  rw [hcy_step1, heq_2y] at hF_y hI_y
  rw [maxCoordDelta_toReal_eval] at hlim_dx hlim_dy
  rw [maxCellBoundaryDistance_toReal_eval] at hcx_le_dy hcy_le_dx
  rw [epsRayMarch_toReal_eval] at hF_c hF_x hF_y hF_xy
  rcases h_ind with h_ext3 | h_res1 | h_res2 | h_res3
  · exact h_ext3
  · exfalso
    rcases h_res1 with ⟨_, hsI1, hdI1, _, hdI_xy, _, hdF1 | ⟨hdF1, ⟨hsF1, hF_sub⟩ | ⟨hsF1, hF_sub⟩⟩⟩
    · have := (hI_c.2 hdI1).2.2.2 hsI1; have := hF_c.1 hdF1
      rcases (hI_xy.2 hdI_xy).1 with h | h <;> linarith
    · have := (hI_c.2 hdI1).2.2.2 hsI1; have := (hF_c.2 hdF1).2.1 hsF1
      have hI_xy_min := (hI_xy.2 hdI_xy).1
      rcases hF_sub with hend | hdF2 | hsF2 | hsF2
      · have heq := eq_of_beq hend
        have hy_eq : c.y = (floorPoint B.toPoint).y := by simpa using congrArg Cell.y heq
        have := hend_y0 hy_eq; linarith
      · have := hF_x.1 hdF2; rcases hI_xy_min with h | h <;> linarith
      · have hdF2 : (rayMarchStepFloat A (deltaX A B) (deltaY A B) stepX stepY ⟨c.x + stepX, c.y⟩).2 = false := by
          cases h : (rayMarchStepFloat A (deltaX A B) (deltaY A B) stepX stepY ⟨c.x + stepX, c.y⟩).2
          · rfl
          · have := hF_x.1 h; rcases hI_xy_min with h' | h' <;> linarith
        have := (hF_x.2 hdF2).2.1 hsF2; linarith
      · have hdF2 : (rayMarchStepFloat A (deltaX A B) (deltaY A B) stepX stepY ⟨c.x + stepX, c.y⟩).2 = false := by
          cases h : (rayMarchStepFloat A (deltaX A B) (deltaY A B) stepX stepY ⟨c.x + stepX, c.y⟩).2
          · rfl
          · have := hF_x.1 h; rcases hI_xy_min with h' | h' <;> linarith
        have := (hF_x.2 hdF2).2.2.2 hsF2; linarith
    · have := (hI_c.2 hdI1).2.2.2 hsI1; have := (hF_c.2 hdF1).2.2.1 hsF1
      have hI_xy_min := (hI_xy.2 hdI_xy).1
      rcases hF_sub with hend | hdF2 | hsF2 | hsF2
      · have heq := eq_of_beq hend
        have hx_eq : c.x = (floorPoint B.toPoint).x := by simpa using congrArg Cell.x heq
        have := hend_x0 hx_eq; linarith
      · have := hF_y.1 hdF2; rcases hI_xy_min with h | h <;> linarith
      · have hdF2 : (rayMarchStepFloat A (deltaX A B) (deltaY A B) stepX stepY ⟨c.x, c.y + stepY⟩).2 = false := by
          cases h : (rayMarchStepFloat A (deltaX A B) (deltaY A B) stepX stepY ⟨c.x, c.y + stepY⟩).2
          · rfl
          · have := hF_y.1 h; rcases hI_xy_min with h' | h' <;> linarith
        have := (hF_y.2 hdF2).2.2.1 hsF2; linarith
      · have hdF2 : (rayMarchStepFloat A (deltaX A B) (deltaY A B) stepX stepY ⟨c.x, c.y + stepY⟩).2 = false := by
          cases h : (rayMarchStepFloat A (deltaX A B) (deltaY A B) stepX stepY ⟨c.x, c.y + stepY⟩).2
          · rfl
          · have := hF_y.1 h; rcases hI_xy_min with h' | h' <;> linarith
        have := (hF_y.2 hdF2).2.2.2 hsF2; linarith
  · exfalso
    rcases h_res2 with ⟨_, hdI1, _, hdI_xy, _, ⟨hsI1, _, hdI2, hsI2, hdF1 | ⟨hdF1, hsF1, hF_sub⟩⟩ | ⟨hsI1, _, hdI2, hsI2, hdF1 | ⟨hdF1, hsF1, hF_sub⟩⟩⟩
    · have := (hI_c.2 hdI1).2.1 hsI1; have := hF_c.1 hdF1
      rcases (hI_xy.2 hdI_xy).1 with h | h <;> linarith
    · have := (hI_c.2 hdI1).2.1 hsI1; have := (hI_x.2 hdI2).2.2.1 hsI2
      have := (hF_c.2 hdF1).2.2.1 hsF1; have hI_xy_min := (hI_xy.2 hdI_xy).1
      rcases hF_sub with hend | hdF2 | hsF2 | hsF2
      · have heq := eq_of_beq hend
        have hx_eq : c.x = (floorPoint B.toPoint).x := by simpa using congrArg Cell.x heq
        have := hend_x0 hx_eq; linarith
      · have := hF_y.1 hdF2; rcases hI_xy_min with h | h <;> linarith
      · have hdF2 : (rayMarchStepFloat A (deltaX A B) (deltaY A B) stepX stepY ⟨c.x, c.y + stepY⟩).2 = false := by
          cases h : (rayMarchStepFloat A (deltaX A B) (deltaY A B) stepX stepY ⟨c.x, c.y + stepY⟩).2
          · rfl
          · have := hF_y.1 h; rcases hI_xy_min with h' | h' <;> linarith
        have := (hF_y.2 hdF2).2.2.1 hsF2; linarith
      · have hdF2 : (rayMarchStepFloat A (deltaX A B) (deltaY A B) stepX stepY ⟨c.x, c.y + stepY⟩).2 = false := by
          cases h : (rayMarchStepFloat A (deltaX A B) (deltaY A B) stepX stepY ⟨c.x, c.y + stepY⟩).2
          · rfl
          · have := hF_y.1 h; rcases hI_xy_min with h' | h' <;> linarith
        have := (hF_y.2 hdF2).2.2.2 hsF2; linarith
    · have := (hI_c.2 hdI1).2.2.1 hsI1; have := hF_c.1 hdF1
      rcases (hI_xy.2 hdI_xy).1 with h | h <;> linarith
    · have := (hI_c.2 hdI1).2.2.1 hsI1; have := (hI_y.2 hdI2).2.1 hsI2
      have := (hF_c.2 hdF1).2.1 hsF1; have hI_xy_min := (hI_xy.2 hdI_xy).1
      rcases hF_sub with hend | hdF2 | hsF2 | hsF2
      · have heq := eq_of_beq hend
        have hy_eq : c.y = (floorPoint B.toPoint).y := by simpa using congrArg Cell.y heq
        have := hend_y0 hy_eq; linarith
      · have := hF_x.1 hdF2; rcases hI_xy_min with h | h <;> linarith
      · have hdF2 : (rayMarchStepFloat A (deltaX A B) (deltaY A B) stepX stepY ⟨c.x + stepX, c.y⟩).2 = false := by
          cases h : (rayMarchStepFloat A (deltaX A B) (deltaY A B) stepX stepY ⟨c.x + stepX, c.y⟩).2
          · rfl
          · have := hF_x.1 h; rcases hI_xy_min with h' | h' <;> linarith
        have := (hF_x.2 hdF2).2.1 hsF2; linarith
      · have hdF2 : (rayMarchStepFloat A (deltaX A B) (deltaY A B) stepX stepY ⟨c.x + stepX, c.y⟩).2 = false := by
          cases h : (rayMarchStepFloat A (deltaX A B) (deltaY A B) stepX stepY ⟨c.x + stepX, c.y⟩).2
          · rfl
          · have := hF_x.1 h; rcases hI_xy_min with h' | h' <;> linarith
        have := (hF_x.2 hdF2).2.2.2 hsF2; linarith
  · exfalso
    rcases h_res3 with ⟨_, hdI1, hdI2, _, ⟨hsI1, _, hsI2 | hsI2, hdF1 | ⟨hdF1, hsF1 | hsF1⟩⟩ | ⟨hsI1, _, hsI2 | hsI2, hdF1 | ⟨hdF1, hsF1 | hsF1⟩⟩⟩
    · rw [hsI1] at hdI2; have := (hI_c.2 hdI1).2.1 hsI1; have := (hI_x.2 hdI2).2.1 hsI2; have := hF_c.1 hdF1; linarith
    · rw [hsI1] at hdI2; have := (hI_c.2 hdI1).2.1 hsI1; have := (hI_x.2 hdI2).2.1 hsI2; have := (hF_c.2 hdF1).2.2.1 hsF1; linarith
    · rw [hsI1] at hdI2; have := (hI_c.2 hdI1).2.1 hsI1; have := (hI_x.2 hdI2).2.1 hsI2; have := (hF_c.2 hdF1).2.2.2 hsF1; linarith
    · rw [hsI1] at hdI2; have := (hI_c.2 hdI1).2.1 hsI1; have := (hI_x.2 hdI2).2.2.2 hsI2; have := hF_c.1 hdF1; linarith
    · rw [hsI1] at hdI2; have := (hI_c.2 hdI1).2.1 hsI1; have := (hI_x.2 hdI2).2.2.2 hsI2; have := (hF_c.2 hdF1).2.2.1 hsF1; linarith
    · rw [hsI1] at hdI2; have := (hI_c.2 hdI1).2.1 hsI1; have := (hI_x.2 hdI2).2.2.2 hsI2; have := (hF_c.2 hdF1).2.2.2 hsF1; linarith
    · rw [hsI1] at hdI2; have := (hI_c.2 hdI1).2.2.1 hsI1; have := (hI_y.2 hdI2).2.2.1 hsI2; have := hF_c.1 hdF1; linarith
    · rw [hsI1] at hdI2; have := (hI_c.2 hdI1).2.2.1 hsI1; have := (hI_y.2 hdI2).2.2.1 hsI2; have := (hF_c.2 hdF1).2.1 hsF1; linarith
    · rw [hsI1] at hdI2; have := (hI_c.2 hdI1).2.2.1 hsI1; have := (hI_y.2 hdI2).2.2.1 hsI2; have := (hF_c.2 hdF1).2.2.2 hsF1; linarith
    · rw [hsI1] at hdI2; have := (hI_c.2 hdI1).2.2.1 hsI1; have := (hI_y.2 hdI2).2.2.2 hsI2; have := hF_c.1 hdF1; linarith
    · rw [hsI1] at hdI2; have := (hI_c.2 hdI1).2.2.1 hsI1; have := (hI_y.2 hdI2).2.2.2 hsI2; have := (hF_c.2 hdF1).2.1 hsF1; linarith
    · rw [hsI1] at hdI2; have := (hI_c.2 hdI1).2.2.1 hsI1; have := (hI_y.2 hdI2).2.2.2 hsI2; have := (hF_c.2 hdF1).2.2.2 hsF1; linarith

/--
Master Implementation:
For any input segment with coordinates bounded in magnitude by mainCoordBound and finite inputs,
the discrete Chebyshev Hausdorff distance between the 32-bit floating point output
`cellIntersectionsSegmentFloat A B` and the idealized rational output
`cellIntersectionsSegment A.toPoint B.toPoint` is at most 1.
-/
theorem cellIntersectionsSegmentFloat_hausdorff_bound_Impl
    (A B : Point32)
    (h_finiteA : A.isFinite)
    (h_finiteB : B.isFinite)
    (h_bound : inCoordBounds mainCoordBound A.toPoint B.toPoint) :
    cellHausdorffDistanceLe
      (cellIntersectionsSegmentFloat A B)
      (cellIntersectionsSegment A.toPoint B.toPoint) 1 := by
  have h_stepX := step_signs_agree_X A B h_finiteA h_finiteB h_bound
  have h_stepY := step_signs_agree_Y A B h_finiteA h_finiteB h_bound
  set stepX : ℤ := if deltaX A B > 0.0 then 1 else if deltaX A B < 0.0 then -1 else 0
  set stepY : ℤ := if deltaY A B > 0.0 then 1 else if deltaY A B < 0.0 then -1 else 0
  by_cases h_axis : (stepX == 0) = true ∨ (stepY == 0) = true
  · exact cellIntersectionsSegmentFloat_hausdorff_bound_axis_aligned A B h_finiteA h_finiteB h_bound h_stepX h_stepY h_axis
  · push Not at h_axis
    have hx0 : (stepX == 0) = false := Bool.eq_false_iff.mpr h_axis.1
    have hy0 : (stepY == 0) = false := Bool.eq_false_iff.mpr h_axis.2
    exact cellIntersectionsSegmentFloat_hausdorff_bound_of_cases_visited2 A B
      (CellInBox A B stepX stepY)
      h_finiteA h_finiteB h_stepX h_stepY
      (cellInBox_start A B h_stepX h_stepY)
      (fun c hc hne hnd => rayMarchStep_preserves_cellInBox_and_dist_2d A B stepX stepY c hx0 hy0 hc hne hnd)
      (fun c hc => prove_cases_float_ext3_of_cellInBox A B stepX stepY c h_finiteA h_finiteB h_bound hx0 hy0 hc)
      (fun c hc => prove_cases_ideal_ext3_of_cellInBox A B stepX stepY c h_finiteA h_finiteB h_bound hx0 hy0 hc)

/--
Master Polyline Theorem (Bounded Implementation):
For any polyline path Ps whose points are finite and whose consecutive segments
satisfy the coordinate magnitude bound of mainCoordBound, the discrete Chebyshev Hausdorff distance
between the floating-point path output and the rational path output is at most 1.
-/
theorem cellIntersectionsPathFloat_hausdorff_bound_Impl
    (Ps : List Point32) (h_fin : AllFinite Ps)
    (h_bounds : ∀ (i : Nat) (hi : i + 1 < Ps.length),
      inCoordBounds mainCoordBound (Ps.get ⟨i, by omega⟩).toPoint (Ps.get ⟨i + 1, hi⟩).toPoint) :
    cellHausdorffDistanceLe
      (cellIntersectionsPathFloat Ps)
      (cellIntersectionsPath (pointsToRational Ps)) 1 := by
  apply cellIntersectionsPathFloat_hausdorff_bound_of_segments_Impl Ps h_fin
  intro i hi
  have hP_fin1 : (Ps.get ⟨i, by omega⟩).isFinite := h_fin _ (List.get_mem Ps ⟨i, by omega⟩)
  have hP_fin2 : (Ps.get ⟨i + 1, hi⟩).isFinite := h_fin _ (List.get_mem Ps ⟨i + 1, hi⟩)
  exact cellIntersectionsSegmentFloat_hausdorff_bound_Impl _ _ hP_fin1 hP_fin2 (h_bounds i hi)

end Geometry

