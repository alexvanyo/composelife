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
import models.FloatModel
import GeometryDefs
import GeometryProofs

namespace Geometry


/-- Rational Master Theorem: Complete and sound discrete cell characterization. -/
theorem cellIntersectionsSegment_exact_iff (A B : Point) (c : Cell) :
    c ∈ cellIntersectionsSegment A B ↔ ActiveIntersectedCell c A B :=
  cellIntersectionsSegment_exact_iff_Impl A B c

/-- Continuous Soundness Master Theorem: Every discrete intersected cell touches the continuous line segment. -/
theorem cellIntersectionsSegment_touches_segment (A B : Point) (c : Cell) :
    c ∈ cellIntersectionsSegment A B → CellTouchesSegment c A B :=
  cellIntersectionsSegment_touches_segment_Impl A B c

/--
Continuous Completeness Master Theorem: Every cell whose open interior the segment passes through is
in the discrete output. Together with `cellIntersectionsSegment_touches_segment`, the output lies
between the cells the segment crosses (plus the endpoint cells) and the cells it touches.
-/
theorem cellIntersectionsSegment_complete (A B : Point) (c : Cell) :
    CellCrossedBySegment c A B → c ∈ cellIntersectionsSegment A B :=
  cellIntersectionsSegment_complete_Impl A B c

/-- Rational Endpoints Master Theorem: Endpoints are always contained in the discrete cell output. -/
theorem cellIntersectionsSegment_contains_endpoints (A B : Point) :
    floorPoint A ∈ cellIntersectionsSegment A B ∧ floorPoint B ∈ cellIntersectionsSegment A B :=
  cellIntersectionsSegment_contains_endpoints_Impl A B

/-- Float Step-Agreement Master Theorem: Exact equality between float and rational outputs under step agreement. -/
theorem cellIntersectionsSegmentFloat_eq_ideal_of_step_agreement
    (A B : Point32) (h_finA : A.isFinite) (h_finB : B.isFinite)
    (h_agree : StepAgreement A B) :
    cellIntersectionsSegmentFloat A B = cellIntersectionsSegment A.toPoint B.toPoint :=
  cellIntersectionsSegmentFloat_eq_ideal_of_step_agreement_Impl A B h_finA h_finB h_agree

/-- Float Endpoints Master Theorem: Endpoints are always contained in the floating-point cell output. -/
theorem cellIntersectionsSegmentFloat_contains_endpoints (A B : Point32) :
    floorPoint32 A ∈ cellIntersectionsSegmentFloat A B ∧ floorPoint32 B ∈ cellIntersectionsSegmentFloat A B :=
  cellIntersectionsSegmentFloat_contains_endpoints_Impl A B

/--
Float Connectivity Master Theorem: The float model's cells have no gaps. They can be listed as a
path of neighboring cells (king moves) from the start cell to the end cell.
-/
theorem cellIntersectionsSegmentFloat_connected (A B : Point32) (h_finA : A.isFinite)
    (h_finB : B.isFinite) (h_bound : inCoordBounds mainCoordBound A.toPoint B.toPoint) :
    ∃ path : List Cell, path.head? = some (floorPoint32 A) ∧ path.getLast? = some (floorPoint32 B) ∧
      CellPathConnected path ∧ ∀ c, c ∈ path ↔ c ∈ cellIntersectionsSegmentFloat A B :=
  cellIntersectionsSegmentFloat_connected_Impl A B h_finA h_finB h_bound

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

/--
Master Refinement Theorem (Pattern B): Within `InRange`, the compiled production ray march
`rayMarchSegmentCoords` returns exactly the cells of the float model `cellIntersectionsSegmentFloat`,
up to duplicates (the Kotlin caller collects the cells into a `Set`).
-/
theorem rayMarchSegmentCoords_refines (A B : Point32) (sx sy ex ey : Float) (cx cy ex' ey' : Int32)
    (hPre : InRange A B sx sy ex ey cx cy ex' ey') :
    dedupCells (toCells (rayMarchSegmentCoords sx sy ex ey cx cy ex' ey')) =
      cellIntersectionsSegmentFloat A B :=
  rayMarchSegmentCoords_refines_Impl A B sx sy ex ey cx cy ex' ey' hPre

/--
Compiled Hausdorff Master Theorem: Within `InRange`, the cells returned by the compiled ray march
are within Chebyshev Hausdorff distance 1 of the exact rational cell intersections of the segment.
-/
theorem rayMarchSegmentCoords_hausdorff_bound (A B : Point32) (sx sy ex ey : Float)
    (cx cy ex' ey' : Int32) (hPre : InRange A B sx sy ex ey cx cy ex' ey') :
    cellHausdorffDistanceLe
      (dedupCells (toCells (rayMarchSegmentCoords sx sy ex ey cx cy ex' ey')))
      (cellIntersectionsSegment A.toPoint B.toPoint) 1 :=
  rayMarchSegmentCoords_hausdorff_bound_Impl A B sx sy ex ey cx cy ex' ey' hPre

/--
Compiled Connectivity Master Theorem: Within `InRange`, the cells returned by the compiled ray march
have no gaps. They can be listed as a path of neighboring cells (king moves) from the start cell to
the end cell.
-/
theorem rayMarchSegmentCoords_connected (A B : Point32) (sx sy ex ey : Float) (cx cy ex' ey' : Int32)
    (hPre : InRange A B sx sy ex ey cx cy ex' ey') :
    ∃ path : List Cell, path.head? = some (floorPoint32 A) ∧ path.getLast? = some (floorPoint32 B) ∧
      CellPathConnected path ∧
      ∀ c, c ∈ path ↔ c ∈ toCells (rayMarchSegmentCoords sx sy ex ey cx cy ex' ey') :=
  rayMarchSegmentCoords_connected_Impl A B sx sy ex ey cx cy ex' ey' hPre

end Geometry


