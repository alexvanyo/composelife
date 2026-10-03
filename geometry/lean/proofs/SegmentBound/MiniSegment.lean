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
import proofs.FloatProperties
import proofs.Interval
import proofs.Soundness
import proofs.SegmentBound.Waypoints

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

end Geometry
