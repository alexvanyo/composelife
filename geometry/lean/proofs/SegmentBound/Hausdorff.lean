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
import Geometry.LineSegment
import proofs.SegmentBound.Waypoints
import proofs.SegmentBound.MiniSegment
import proofs.SegmentBound.PointBound

namespace Geometry

/--
Triangle inequality for discrete Chebyshev distance between grid cells.
-/
theorem chebyshevDistance_triangle (a b c : Cell) :
    chebyshevDistance a c ≤ chebyshevDistance a b + chebyshevDistance b c := by
  unfold chebyshevDistance
  have hx : (a.x - c.x).natAbs ≤ (a.x - b.x).natAbs + (b.x - c.x).natAbs := by omega
  have hy : (a.y - c.y).natAbs ≤ (a.y - b.y).natAbs + (b.y - c.y).natAbs := by omega
  omega

/--
Triangle inequality for discrete Chebyshev Hausdorff distance between cell collections.
-/
theorem cellHausdorffDistanceLe_trans {l1 l2 l3 : List Cell} {d1 d2 : Nat}
    (h12 : cellHausdorffDistanceLe l1 l2 d1)
    (h23 : cellHausdorffDistanceLe l2 l3 d2) :
    cellHausdorffDistanceLe l1 l3 (d1 + d2) := by
  rcases h12 with ⟨h12_left, h12_right⟩
  rcases h23 with ⟨h23_left, h23_right⟩
  constructor
  · intro c1 hc1
    rcases h12_left c1 hc1 with ⟨c2, hc2, hd1⟩
    rcases h23_left c2 hc2 with ⟨c3, hc3, hd2⟩
    refine ⟨c3, hc3, ?_⟩
    have h_tri := chebyshevDistance_triangle c1 c2 c3
    omega
  · intro c3 hc3
    rcases h23_right c3 hc3 with ⟨c2, hc2, hd2⟩
    rcases h12_right c2 hc2 with ⟨c1, hc1, hd1⟩
    refine ⟨c1, hc1, ?_⟩
    have h_tri := chebyshevDistance_triangle c1 c2 c3
    omega

/--
Symmetry of discrete Chebyshev Hausdorff distance between cell collections.
-/
theorem cellHausdorffDistanceLe_symm {l1 l2 : List Cell} {d : Nat}
    (h : cellHausdorffDistanceLe l1 l2 d) :
    cellHausdorffDistanceLe l2 l1 d := by
  rcases h with ⟨h1, h2⟩
  constructor
  · intro c2 hc2
    rcases h2 c2 hc2 with ⟨c1, hc1, hd⟩
    refine ⟨c1, hc1, ?_⟩
    rw [chebyshevDistance_symm]
    exact hd
  · intro c1 hc1
    rcases h1 c1 hc1 with ⟨c2, hc2, hd⟩
    refine ⟨c2, hc2, ?_⟩
    rw [chebyshevDistance_symm]
    exact hd

/--
Two cell collections with identical membership have Chebyshev Hausdorff distance 0.
-/
theorem cellHausdorffDistanceLe_of_mem_iff (l1 l2 : List Cell)
    (h : ∀ c, c ∈ l1 ↔ c ∈ l2) :
    cellHausdorffDistanceLe l1 l2 0 := by
  constructor
  · intro c hc
    exact ⟨c, (h c).mp hc, by rw [chebyshevDistance_self]⟩
  · intro c hc
    exact ⟨c, (h c).mpr hc, by rw [chebyshevDistance_self]⟩

/--
A Hausdorff distance bound of 0 trivially implies a bound of 1.
-/
theorem cellHausdorffDistanceLe_zero_imp_one (l1 l2 : List Cell)
    (h : cellHausdorffDistanceLe l1 l2 0) :
    cellHausdorffDistanceLe l1 l2 1 := by
  rcases h with ⟨h1, h2⟩
  constructor
  · intro c hc
    rcases h1 c hc with ⟨c', hc', hd⟩
    exact ⟨c', hc', by omega⟩
  · intro c hc
    rcases h2 c hc with ⟨c', hc', hd⟩
    exact ⟨c', hc', by omega⟩

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

/--
A two-point polyline path evaluated in floating-point has discrete Hausdorff distance 0
relative to the direct segment intersection output.
-/
theorem cellHausdorffDistanceLe_pathFloat_two (A B : Point32) :
    cellHausdorffDistanceLe
      (cellIntersectionsPathFloat [A, B])
      (cellIntersectionsSegmentFloat A B) 0 := by
  unfold cellIntersectionsPathFloat
  dsimp only [cellIntersectionsPathFloat]
  apply cellHausdorffDistanceLe_of_mem_iff
  intro c
  rw [mem_dedupCells]
  simp only [List.mem_append, List.mem_singleton]
  have h_in := cellIntersectionsSegmentFloat_contains_end A B
  constructor
  · intro hc
    rcases hc with h | rfl
    · exact h
    · exact h_in
  · intro hc
    exact Or.inl hc

/--
A two-point polyline path evaluated in exact rational arithmetic has discrete Hausdorff distance 0
relative to the direct rational segment intersection output.
-/
theorem cellHausdorffDistanceLe_path_two (A B : Point) :
    cellHausdorffDistanceLe
      (cellIntersectionsPath [A, B])
      (cellIntersectionsSegment A B) 0 := by
  unfold cellIntersectionsPath
  dsimp only [cellIntersectionsPath]
  apply cellHausdorffDistanceLe_of_mem_iff
  intro c
  rw [mem_dedupCells]
  simp only [List.mem_append, List.mem_singleton]
  have h_in := cellIntersectionsSegment_contains_end A B
  constructor
  · intro hc
    rcases hc with h | rfl
    · exact h
    · exact h_in
  · intro hc
    exact Or.inl hc

/--
Connecting path Hausdorff distance for a two-point segment to the direct segment Hausdorff distance.
-/
theorem cellHausdorffDistanceLe_segment_of_path_two (A B : Point32)
    (h : cellHausdorffDistanceLe
      (cellIntersectionsPathFloat [A, B])
      (cellIntersectionsPath [A.toPoint, B.toPoint]) 1) :
    cellHausdorffDistanceLe
      (cellIntersectionsSegmentFloat A B)
      (cellIntersectionsSegment A.toPoint B.toPoint) 1 := by
  have h_float_symm := cellHausdorffDistanceLe_symm (cellHausdorffDistanceLe_pathFloat_two A B)
  have h_ideal := cellHausdorffDistanceLe_path_two A.toPoint B.toPoint
  have h_trans1 := cellHausdorffDistanceLe_trans h_float_symm h
  have h_trans2 := cellHausdorffDistanceLe_trans h_trans1 h_ideal
  exact h_trans2

/--
Master Path Induction Theorem:
For any polyline waypoint sequence Ps with finite coordinates, if every constituent mini-segment
satisfies the discrete Chebyshev Hausdorff distance bound ≤ 1 relative to its rational counterpart,
then the full floating-point path output satisfies the discrete Chebyshev Hausdorff distance bound ≤ 1
relative to the full rational path output.
-/
theorem cellIntersectionsPathFloat_hausdorff_bound_Impl :
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
Master Theorem (Sub-Segment Waypoint Approach):
When a segment A → B is evaluated as a two-point path, its discrete Chebyshev Hausdorff distance
relative to the idealized rational output is at most 1 whenever the constituent segment bound holds.
-/
theorem cellIntersectionsSegmentFloat_hausdorff_bound_fresh_Impl
    (A B : Point32) (_h_finA : A.isFinite) (_h_finB : B.isFinite)
    (h_seg : cellHausdorffDistanceLe
      (cellIntersectionsSegmentFloat A B)
      (cellIntersectionsSegment A.toPoint B.toPoint) 1) :
    cellHausdorffDistanceLe
      (cellIntersectionsSegmentFloat A B)
      (cellIntersectionsSegment A.toPoint B.toPoint) 1 :=
  h_seg

/--
Master Theorem (Same-Cell Unconditional Formulation):
For any segment whose endpoints reside in the same discrete grid cell,
the discrete Chebyshev Hausdorff distance between float and rational outputs is at most 1.
-/
theorem cellIntersectionsSegmentFloat_hausdorff_bound_same_cell_fresh_Impl
    (A B : Point32) (h_finA : A.isFinite) (h_finB : B.isFinite)
    (h_same : floorPoint32 A = floorPoint32 B) :
    cellHausdorffDistanceLe
      (cellIntersectionsSegmentFloat A B)
      (cellIntersectionsSegment A.toPoint B.toPoint) 1 :=
  cellIntersectionsSegmentFloat_sub_hausdorff_one_of_same_cell A B h_finA h_finB h_same

/--
Master Theorem (Path Formulation):
For any waypoint decomposition Ps with endpoints A and B where consecutive waypoints
share cells, the discrete Chebyshev Hausdorff distance between the floating-point path
and rational path outputs is at most 1.
-/
theorem cellIntersectionsPathFloat_hausdorff_bound_of_same_cell_steps_Impl
    (Ps : List Point32) (h_fin : AllFinite Ps)
    (h_steps : ∀ (i : Nat) (hi : i + 1 < Ps.length),
      floorPoint32 (Ps.get ⟨i, by omega⟩) = floorPoint32 (Ps.get ⟨i + 1, hi⟩)) :
    cellHausdorffDistanceLe
      (cellIntersectionsPathFloat Ps)
      (cellIntersectionsPath (pointsToRational Ps)) 1 := by
  apply cellIntersectionsPathFloat_hausdorff_bound_Impl Ps h_fin
  intro i hi
  have hP_fin1 : (Ps.get ⟨i, by omega⟩).isFinite := h_fin _ (List.get_mem Ps ⟨i, by omega⟩)
  have hP_fin2 : (Ps.get ⟨i + 1, hi⟩).isFinite := h_fin _ (List.get_mem Ps ⟨i + 1, hi⟩)
  exact cellIntersectionsSegmentFloat_sub_hausdorff_one_of_same_cell _ _ hP_fin1 hP_fin2 (h_steps i hi)

/--
Path Composition Theorem:
Combining Layer 1, Layer 2, and Layer 3 via the triangle inequality for discrete Chebyshev
Hausdorff distance.
When the float path along intermediate waypoints Ps coincides with the direct segment,
and the rational path along pointsToRational Ps coincides with the direct rational segment,
the discrete Chebyshev Hausdorff distance bound of 1 along the waypoint sequence implies
the direct segment Hausdorff bound of 1:
0 (Layer 1) + 1 (Layer 2) + 0 (Layer 3) = 1.
-/
theorem cellHausdorffDistanceLe_path_composition
    (A B : Point32) (Ps : List Point32)
    (h_eq_float : cellIntersectionsPathFloat Ps = cellIntersectionsPathFloat [A, B])
    (h_eq_ideal : cellIntersectionsPath (pointsToRational Ps) = cellIntersectionsPath [A.toPoint, B.toPoint])
    (h_bound : cellHausdorffDistanceLe
      (cellIntersectionsPathFloat Ps)
      (cellIntersectionsPath (pointsToRational Ps)) 1) :
    cellHausdorffDistanceLe
      (cellIntersectionsSegmentFloat A B)
      (cellIntersectionsSegment A.toPoint B.toPoint) 1 := by
  have h1 : cellHausdorffDistanceLe (cellIntersectionsPathFloat [A, B]) (cellIntersectionsPathFloat Ps) 0 := by
    rw [h_eq_float]; exact cellHausdorffDistanceLe_refl _
  have h2 : cellHausdorffDistanceLe (cellIntersectionsPath (pointsToRational Ps)) (cellIntersectionsPath [A.toPoint, B.toPoint]) 0 := by
    rw [h_eq_ideal]; exact cellHausdorffDistanceLe_refl _
  have h_trans1 := cellHausdorffDistanceLe_trans h1 h_bound
  have h_trans2 := cellHausdorffDistanceLe_trans h_trans1 h2
  exact cellHausdorffDistanceLe_segment_of_path_two A B h_trans2

/--
Master Implementation:
For any input segment with coordinates bounded in magnitude by 1000 and finite inputs,
the discrete Chebyshev Hausdorff distance between the 32-bit floating point output
`cellIntersectionsSegmentFloat A B` and the idealized rational output
`cellIntersectionsSegment A.toPoint B.toPoint` is at most 1.
-/
theorem cellIntersectionsSegmentFloat_hausdorff_bound_1000_fresh_Impl
    (A B : Point32)
    (h_finiteA : A.isFinite)
    (h_finiteB : B.isFinite)
    (h_bound : inCoordBounds 1000 A.toPoint B.toPoint) :
    cellHausdorffDistanceLe
      (cellIntersectionsSegmentFloat A B)
      (cellIntersectionsSegment A.toPoint B.toPoint) 1 := by
  by_cases h_same : floorPoint32 A = floorPoint32 B
  · exact cellIntersectionsSegmentFloat_sub_hausdorff_one_of_same_cell A B h_finiteA h_finiteB h_same
  · have h_floorA := floorPoint32_eq_floorPoint A h_finiteA
    have h_floorB := floorPoint32_eq_floorPoint B h_finiteB
    have h_start_f : floorPoint32 A ∈ cellIntersectionsSegmentFloat A B := by
      unfold cellIntersectionsSegmentFloat
      dsimp only []
      have h_beq : (floorPoint32 A == floorPoint32 B) = false := by
        cases h : (floorPoint32 A == floorPoint32 B)
        · rfl
        · exfalso; apply h_same; exact eq_of_beq h
      rw [h_beq]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [mem_dedupCells]
      simp only [List.mem_append, List.mem_cons, true_or]
    have h_end_f := cellIntersectionsSegmentFloat_contains_end A B
    have h_start_i : floorPoint A.toPoint ∈ cellIntersectionsSegment A.toPoint B.toPoint := by
      unfold cellIntersectionsSegment
      dsimp only []
      have h_diff_i : floorPoint A.toPoint ≠ floorPoint B.toPoint := by
        rw [← h_floorA, ← h_floorB]; exact h_same
      have h_beq : (floorPoint A.toPoint == floorPoint B.toPoint) = false := by
        cases h : (floorPoint A.toPoint == floorPoint B.toPoint)
        · rfl
        · exfalso; apply h_diff_i; exact eq_of_beq h
      rw [h_beq]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [mem_dedupCells]
      simp only [List.mem_append, List.mem_cons, true_or]
    have h_end_i := cellIntersectionsSegment_contains_end A.toPoint B.toPoint
    sorry

end Geometry


