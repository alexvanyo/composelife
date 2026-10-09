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
import Geometry.FloatModel
import GeometryDefs
import GeometryProofs

namespace Geometry


/-- Rational Master Theorem: Complete and sound discrete cell characterization. -/
theorem cellIntersectionsSegment_exact_iff (A B : Point) (c : Cell) :
    c ∈ cellIntersectionsSegment A B ↔ ActiveIntersectedCell c A B :=
  cellIntersectionsSegment_exact_iff_Impl A B c

/-- Float Clearance Master Theorem: Exact equality between float and rational outputs under corner clearance. -/
theorem cellIntersectionsSegmentFloat_eq_ideal_of_clearance
    (A B : Point32) (M : ℚ) (h_finA : A.isFinite) (h_finB : B.isFinite)
    (h_bound : inCoordBounds M A.toPoint B.toPoint)
    (h_clear : HasCornerClearance A.toPoint B.toPoint M) :
    cellIntersectionsSegmentFloat A B = cellIntersectionsSegment A.toPoint B.toPoint :=
  cellIntersectionsSegmentFloat_eq_ideal_of_clearance_Impl A B M h_finA h_finB h_bound h_clear

/-- Sub-segment Path Master Theorem: Inductive Hausdorff bound along any waypoint sequence. -/
theorem cellIntersectionsPathFloat_hausdorff_bound_of_segments
    (Ps : List Point32) (h_fin : AllFinite Ps)
    (h_seg : ∀ (i : Nat) (hi : i + 1 < Ps.length),
      cellHausdorffDistanceLe
        (cellIntersectionsSegmentFloat (Ps.get ⟨i, by omega⟩) (Ps.get ⟨i + 1, hi⟩))
        (cellIntersectionsSegment (Ps.get ⟨i, by omega⟩).toPoint (Ps.get ⟨i + 1, hi⟩).toPoint) 1) :
    cellHausdorffDistanceLe
      (cellIntersectionsPathFloat Ps)
      (cellIntersectionsPath (pointsToRational Ps)) 1 :=
  cellIntersectionsPathFloat_hausdorff_bound_of_segments_Impl Ps h_fin h_seg

/-- Unconditional Hausdorff bound for segments whose endpoints lie in the same cell. -/
theorem cellIntersectionsSegmentFloat_hausdorff_bound_of_same_cell
    (A B : Point32) (h_finA : A.isFinite) (h_finB : B.isFinite)
    (h_same : floorPoint32 A = floorPoint32 B) :
    cellHausdorffDistanceLe
      (cellIntersectionsSegmentFloat A B)
      (cellIntersectionsSegment A.toPoint B.toPoint) 1 :=
  cellIntersectionsSegmentFloat_hausdorff_bound_of_same_cell_Impl A B h_finA h_finB h_same

/-- Path formulation along same-cell waypoint steps. -/
theorem cellIntersectionsPathFloat_hausdorff_bound_of_same_cell_steps
    (Ps : List Point32) (h_fin : AllFinite Ps)
    (h_steps : ∀ (i : Nat) (hi : i + 1 < Ps.length),
      floorPoint32 (Ps.get ⟨i, by omega⟩) = floorPoint32 (Ps.get ⟨i + 1, hi⟩)) :
    cellHausdorffDistanceLe
      (cellIntersectionsPathFloat Ps)
      (cellIntersectionsPath (pointsToRational Ps)) 1 :=
  cellIntersectionsPathFloat_hausdorff_bound_of_same_cell_steps_Impl Ps h_fin h_steps

/--
Master Segment Theorem: Global Hausdorff bound for any segment within `mainCoordBound` ([-2147483645, 2147483645]²).
-/
theorem cellIntersectionsSegmentFloat_hausdorff_bound
    (A B : Point32)
    (h_finiteA : A.isFinite)
    (h_finiteB : B.isFinite)
    (h_bound : inCoordBounds mainCoordBound A.toPoint B.toPoint) :
    cellHausdorffDistanceLe
      (cellIntersectionsSegmentFloat A B)
      (cellIntersectionsSegment A.toPoint B.toPoint) 1 :=
  cellIntersectionsSegmentFloat_hausdorff_bound_Impl A B h_finiteA h_finiteB h_bound

/--
Master Polyline Theorem: Global Hausdorff bound along any path within `mainCoordBound` ([-2147483645, 2147483645]²).
-/
theorem cellIntersectionsPathFloat_hausdorff_bound
    (Ps : List Point32) (h_fin : AllFinite Ps)
    (h_bounds : ∀ (i : Nat) (hi : i + 1 < Ps.length),
      inCoordBounds mainCoordBound (Ps.get ⟨i, by omega⟩).toPoint (Ps.get ⟨i + 1, hi⟩).toPoint) :
    cellHausdorffDistanceLe
      (cellIntersectionsPathFloat Ps)
      (cellIntersectionsPath (pointsToRational Ps)) 1 :=
  cellIntersectionsPathFloat_hausdorff_bound_Impl Ps h_fin h_bounds

/-- Same-cell Master Theorem for compiled ray march coordinates. -/
theorem rayMarchSegmentCoords_same_cell (x y : Float) (cx cy : Int32) :
    rayMarchSegmentCoords x y x y cx cy cx cy = #[(cx, cy)] :=
  rayMarchSegmentCoords_same_cell_Impl x y cx cy

end Geometry

#print axioms Geometry.cellIntersectionsSegmentFloat_eq_ideal_of_clearance
#print axioms Geometry.cellIntersectionsSegmentFloat_hausdorff_bound
#print axioms Geometry.cellIntersectionsPathFloat_hausdorff_bound
#print axioms Geometry.rayMarchSegmentCoords_same_cell

