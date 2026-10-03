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

/-- Float Hausdorff Master Theorem: Discrete Chebyshev distance at most 1 under step classification. -/
theorem cellIntersectionsSegmentFloat_hausdorff_bound
    (A B : Point32) (h_finA : A.isFinite) (h_finB : B.isFinite)
    (h_bound : inCoordBounds 1000 A.toPoint B.toPoint)
    (h_stepX : (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0) =
      (if B.toPoint.x - A.toPoint.x > 0 then 1 else if B.toPoint.x - A.toPoint.x < 0 then -1 else 0))
    (h_stepY : (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0) =
      (if B.toPoint.y - A.toPoint.y > 0 then 1 else if B.toPoint.y - A.toPoint.y < 0 then -1 else 0))
    (h_class : ∀ c, StepClassification A B.toPoint (B.x - A.x) (B.y - A.y)
      (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y)
      (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0)
      (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0)
      (floorPoint B.toPoint) c) :
    cellHausdorffDistanceLe
      (cellIntersectionsSegmentFloat A B)
      (cellIntersectionsSegment A.toPoint B.toPoint) 1 :=
  cellIntersectionsSegmentFloat_hausdorff_bound_Impl A B h_finA h_finB h_bound h_stepX h_stepY h_class

/-- Sub-segment Path Master Theorem: Inductive Hausdorff bound along any waypoint sequence. -/
theorem cellIntersectionsPathFloat_hausdorff_bound
    (Ps : List Point32) (h_fin : AllFinite Ps)
    (h_seg : ∀ (i : Nat) (hi : i + 1 < Ps.length),
      cellHausdorffDistanceLe
        (cellIntersectionsSegmentFloat (Ps.get ⟨i, by omega⟩) (Ps.get ⟨i + 1, hi⟩))
        (cellIntersectionsSegment (Ps.get ⟨i, by omega⟩).toPoint (Ps.get ⟨i + 1, hi⟩).toPoint) 1) :
    cellHausdorffDistanceLe
      (cellIntersectionsPathFloat Ps)
      (cellIntersectionsPath (pointsToRational Ps)) 1 :=
  cellIntersectionsPathFloat_hausdorff_bound_Impl Ps h_fin h_seg

/-- Fresh Master Theorem: Sub-segment bound formulation. -/
theorem cellIntersectionsSegmentFloat_hausdorff_bound_fresh
    (A B : Point32) (h_finA : A.isFinite) (h_finB : B.isFinite)
    (h_seg : cellHausdorffDistanceLe
      (cellIntersectionsSegmentFloat A B)
      (cellIntersectionsSegment A.toPoint B.toPoint) 1) :
    cellHausdorffDistanceLe
      (cellIntersectionsSegmentFloat A B)
      (cellIntersectionsSegment A.toPoint B.toPoint) 1 :=
  cellIntersectionsSegmentFloat_hausdorff_bound_fresh_Impl A B h_finA h_finB h_seg

/-- Fresh Master Theorem: Unconditional bound for same-cell segments. -/
theorem cellIntersectionsSegmentFloat_hausdorff_bound_same_cell_fresh
    (A B : Point32) (h_finA : A.isFinite) (h_finB : B.isFinite)
    (h_same : floorPoint32 A = floorPoint32 B) :
    cellHausdorffDistanceLe
      (cellIntersectionsSegmentFloat A B)
      (cellIntersectionsSegment A.toPoint B.toPoint) 1 :=
  cellIntersectionsSegmentFloat_hausdorff_bound_same_cell_fresh_Impl A B h_finA h_finB h_same

/-- Fresh Master Theorem: Path formulation along same-cell waypoint steps. -/
theorem cellIntersectionsPathFloat_hausdorff_bound_of_same_cell_steps
    (Ps : List Point32) (h_fin : AllFinite Ps)
    (h_steps : ∀ (i : Nat) (hi : i + 1 < Ps.length),
      floorPoint32 (Ps.get ⟨i, by omega⟩) = floorPoint32 (Ps.get ⟨i + 1, hi⟩)) :
    cellHausdorffDistanceLe
      (cellIntersectionsPathFloat Ps)
      (cellIntersectionsPath (pointsToRational Ps)) 1 :=
  cellIntersectionsPathFloat_hausdorff_bound_of_same_cell_steps_Impl Ps h_fin h_steps

end Geometry
