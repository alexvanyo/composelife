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
import proofs.FloatAnalysis
import Geometry.LineSegment

namespace Geometry

@[simp]
theorem pointsToRational_nil : pointsToRational [] = [] := rfl

@[simp]
theorem pointsToRational_cons (p : Point32) (ps : List Point32) :
    pointsToRational (p :: ps) = p.toPoint :: pointsToRational ps := rfl

@[simp]
theorem pointsToRational_length (pts : List Point32) :
    (pointsToRational pts).length = pts.length := by
  unfold pointsToRational
  simp

/--
When a point is finite, its discrete cell coordinates computed via floorPoint32
match the exact rational floorPoint of its rational lift.
-/
theorem floorPoint_pointsToRational_eq (p : Point32) (h_fin : p.isFinite) :
    floorPoint p.toPoint = floorPoint32 p := by
  rw [floorPoint32_eq_floorPoint p h_fin]

/--
For any finite point P, the Chebyshev distance between its floored float cell
and floored rational cell is 0.
-/
theorem chebyshevDistance_floor_float_rational_eq_zero (p : Point32) (h_fin : p.isFinite) :
    chebyshevDistance (floorPoint32 p) (floorPoint p.toPoint) = 0 := by
  rw [floorPoint_pointsToRational_eq p h_fin]
  exact chebyshevDistance_self (floorPoint32 p)

/--
Equivalence theorem: `rayMarchWithWaypointsFloat` generates the exact same sequence of discrete
grid cells as `rayMarchFloat`.
-/
theorem rayMarchFloat_eq_fst (fuel : Nat) (start : Point32) (dx dy : Binary64) (stepX stepY : Int)
    (endCell : Cell) (current : Cell) (acc : List Cell) (accW : List Point32) :
    (rayMarchWithWaypointsFloat fuel start dx dy stepX stepY endCell current acc accW).1 =
    rayMarchFloat fuel start dx dy stepX stepY endCell current acc := by
  induction fuel generalizing current acc accW with
  | zero => rfl
  | succ fuel ih =>
    unfold rayMarchWithWaypointsFloat rayMarchFloat
    dsimp only []
    split_ifs
    · rfl
    · rfl
    · exact ih _ _ _

/--
Equivalence between `cellIntersectionsSegmentFloat` defined via `rayMarchFloat` and
the waypoint-tracking formulation.
-/
theorem cellIntersectionsSegmentFloat_eq_with_waypoints (A B : Point32) :
    cellIntersectionsSegmentFloat A B =
    let startCell := floorPoint32 A
    let endCell := floorPoint32 B
    if startCell == endCell then
      [startCell]
    else
      let dx := deltaX A B
      let dy := deltaY A B
      let stepX : Int := if dx > 0.0 then 1 else if dx < 0.0 then -1 else 0
      let stepY : Int := if dy > 0.0 then 1 else if dy < 0.0 then -1 else 0
      let maxSteps := (endCell.x - startCell.x).natAbs + (endCell.y - startCell.y).natAbs + 2
      let (cells, _) := rayMarchWithWaypointsFloat maxSteps A dx dy stepX stepY endCell startCell [] []
      dedupCells ([startCell, endCell] ++ cells) := by
  unfold cellIntersectionsSegmentFloat
  cases h : (floorPoint32 A == floorPoint32 B)
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    rw [← rayMarchFloat_eq_fst]
  · simp only [h, ↓reduceIte]

end Geometry
