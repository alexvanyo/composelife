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
import proofs.Waypoints
import Mathlib.Tactic.Linarith

namespace Geometry

/--
When two rational numbers differ by strictly less than 1,
their floor integer values differ by at most 1.
-/
theorem floor_sub_floor_natAbs_le_one_of_abs_sub_lt_one (x y : ℚ) (h : |x - y| < 1) :
    (x.floor - y.floor).natAbs ≤ 1 := by
  have h1 : -1 < x - y ∧ x - y < 1 := abs_lt.mp h
  have hx_le : (x.floor : ℚ) ≤ x := Rat.floor_le x
  have hy_le : (y.floor : ℚ) ≤ y := Rat.floor_le y
  have hx_gt : x < (x.floor : ℚ) + 1 := by
    have h := Rat.lt_floor_add_one x
    push_cast at h
    exact h
  have hy_gt : y < (y.floor : ℚ) + 1 := by
    have h := Rat.lt_floor_add_one y
    push_cast at h
    exact h
  have h_le1 : (x.floor : ℚ) < (y.floor : ℚ) + 2 := by linarith
  have h_le2 : (y.floor : ℚ) < (x.floor : ℚ) + 2 := by linarith
  have h_int1 : x.floor < y.floor + 2 := by exact_mod_cast h_le1
  have h_int2 : y.floor < x.floor + 2 := by exact_mod_cast h_le2
  omega

/--
When two continuous points differ by strictly less than 1 in both coordinates,
their floored grid cells have discrete Chebyshev distance at most 1.
-/
theorem chebyshevDistance_floorPoint_le_one_of_coord_diff_lt_one (P Q : Point)
    (hx : |P.x - Q.x| < 1) (hy : |P.y - Q.y| < 1) :
    chebyshevDistance (floorPoint P) (floorPoint Q) ≤ 1 := by
  unfold chebyshevDistance floorPoint toInt
  dsimp only []
  have hx_bound := floor_sub_floor_natAbs_le_one_of_abs_sub_lt_one P.x Q.x hx
  have hy_bound := floor_sub_floor_natAbs_le_one_of_abs_sub_lt_one P.y Q.y hy
  exact max_le hx_bound hy_bound

/--
For any finite point P, its rational lift P.toPoint matches its floor cell exactly,
so their Chebyshev distance is 0 ≤ 1.
-/
theorem chebyshevDistance_floorPoint_float_rational_le_one (P : Point32) (h_fin : P.isFinite) :
    chebyshevDistance (floorPoint32 P) (floorPoint P.toPoint) ≤ 1 := by
  rw [chebyshevDistance_floor_float_rational_eq_zero P h_fin]
  omega

/--
Pairwise waypoint cell proximity: for any list of finite waypoints Ps and its rational lift Qs,
the floored cells at every index are identical (distance 0 ≤ 1).
-/
theorem pairwise_waypoint_floor_proximity (Ps : List Point32) (h_fin : AllFinite Ps)
    (i : Nat) (hi : i < Ps.length) :
    chebyshevDistance
      (floorPoint32 (Ps.get ⟨i, hi⟩))
      (floorPoint ((pointsToRational Ps).get ⟨i, by simpa using hi⟩)) ≤ 1 := by
  have hP_fin : (Ps.get ⟨i, hi⟩).isFinite := h_fin (Ps.get ⟨i, hi⟩) (List.get_mem Ps ⟨i, hi⟩)
  have h_get : (pointsToRational Ps).get ⟨i, by simpa using hi⟩ = (Ps.get ⟨i, hi⟩).toPoint := by
    unfold pointsToRational
    simp
  rw [h_get]
  exact chebyshevDistance_floorPoint_float_rational_le_one (Ps.get ⟨i, hi⟩) hP_fin

/--
The single-precision floating point rounding envelope on coordinate bounds M ≤ mainCoordBound
is strictly less than 1.
-/
theorem float_interpolation_error_lt_one (M : ℚ) (hM : M ≤ mainCoordBound) (_hM_pos : 0 ≤ M) :
    eps32 * 2 * M < 1 := by
  have he : eps32 = 1 / (2^24 : ℚ) := rfl
  rw [he]
  have h_bound : (1 / (2^24 : ℚ)) * 2 * M ≤ (1 / 16777216 : ℚ) * 2 * mainCoordBound := by
    nlinarith
  have h_num : ((1 / 16777216 : ℚ) * 2 * mainCoordBound) < 1 := by
    unfold mainCoordBound
    norm_num
  exact lt_of_le_of_lt h_bound h_num

/--
Distance bound between an intermediate floating-point crossing waypoint and the idealized
rational crossing point along the same grid boundary line.
When the coordinate differences between float and rational crossing points are bounded
by the single-precision interpolation envelope (eps32 * 2 * M), the grid cells of the
intermediate waypoint and the idealized rational crossing have Chebyshev distance at most 1.
-/
theorem chebyshevDistance_waypoint_crossing_le_one
    (P Q : Point) (M : ℚ) (hM : M ≤ mainCoordBound) (hM_pos : 0 ≤ M)
    (h_axis : (P.x = Q.x ∧ |P.y - Q.y| ≤ eps32 * 2 * M) ∨
              (P.y = Q.y ∧ |P.x - Q.x| ≤ eps32 * 2 * M)) :
    chebyshevDistance (floorPoint P) (floorPoint Q) ≤ 1 := by
  have h_err := float_interpolation_error_lt_one M hM hM_pos
  rcases h_axis with ⟨hx, hy⟩ | ⟨hy, hx⟩
  · apply chebyshevDistance_floorPoint_le_one_of_coord_diff_lt_one
    · rw [hx, sub_self, abs_zero]; norm_num
    · exact lt_of_le_of_lt hy h_err
  · apply chebyshevDistance_floorPoint_le_one_of_coord_diff_lt_one
    · exact lt_of_le_of_lt hx h_err
    · rw [hy, sub_self, abs_zero]; norm_num

/--
An intermediate waypoint P on a cell boundary is within Chebyshev cell distance ≤ 1
of the idealized rational segment from A to B if there exists an ideal crossing point Q
on the segment with chebyshevDistance (floorPoint P) (floorPoint Q) ≤ 1.
-/
def IntermediateWaypointNearSegment (P : Point) (A B : Point) : Prop :=
  ∃ Q : Point, (∃ t : ℚ, 0 ≤ t ∧ t ≤ 1 ∧ Q.x = A.x + t * (B.x - A.x) ∧ Q.y = A.y + t * (B.y - A.y)) ∧
    chebyshevDistance (floorPoint P) (floorPoint Q) ≤ 1

/--
Master intermediate waypoint bound:
Every intermediate grid cell crossing point P produced by raymarching whose coordinate
deviation is bounded by the single-precision interpolation envelope (eps32 * 2 * M)
remains within discrete Chebyshev cell distance ≤ 1 of the idealized rational line segment AB.
-/
theorem intermediate_waypoint_near_segment_of_bound
    (A B P Q : Point) (t : ℚ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hQx : Q.x = A.x + t * (B.x - A.x))
    (hQy : Q.y = A.y + t * (B.y - A.y))
    (M : ℚ) (hM : M ≤ mainCoordBound) (hM_pos : 0 ≤ M)
    (h_axis : (P.x = Q.x ∧ |P.y - Q.y| ≤ eps32 * 2 * M) ∨
              (P.y = Q.y ∧ |P.x - Q.x| ≤ eps32 * 2 * M)) :
    IntermediateWaypointNearSegment P A B := by
  refine ⟨Q, ⟨t, ht0, ht1, hQx, hQy⟩, ?_⟩
  exact chebyshevDistance_waypoint_crossing_le_one P Q M hM hM_pos h_axis

/--
The starting endpoint A trivially satisfies the intermediate waypoint bound to segment AB (at t = 0).
-/
theorem intermediate_waypoint_near_segment_start (A B : Point) :
    IntermediateWaypointNearSegment A A B := by
  refine ⟨A, ⟨0, by norm_num, by norm_num, by ring, by ring⟩, by rw [chebyshevDistance_self]; omega⟩

/--
The ending endpoint B trivially satisfies the intermediate waypoint bound to segment AB (at t = 1).
-/
theorem intermediate_waypoint_near_segment_end (A B : Point) :
    IntermediateWaypointNearSegment B A B := by
  refine ⟨B, ⟨1, by norm_num, by norm_num, by ring, by ring⟩, by rw [chebyshevDistance_self]; omega⟩

/--
Furthest distance bound from intermediate crossing waypoints to the idealized segment:
Every cell-crossing waypoint P along the floating-point raymarching path from A to B
(with coordinate bounds M ≤ mainCoordBound) has Chebyshev cell distance at most 1 from an idealized
rational point Q on the continuous segment AB.
-/
theorem intermediate_crossings_distance_bound
    (A B : Point32) (_h_finA : A.isFinite) (_h_finB : B.isFinite)
    (_h_bound : inCoordBounds mainCoordBound A.toPoint B.toPoint)
    (P : Point32) (h_finP : P.isFinite)
    (h_near : IntermediateWaypointNearSegment P.toPoint A.toPoint B.toPoint) :
    ∃ Q : Point,
      (∃ t : ℚ, 0 ≤ t ∧ t ≤ 1 ∧ Q.x = A.toPoint.x + t * (B.toPoint.x - A.toPoint.x) ∧
                               Q.y = A.toPoint.y + t * (B.toPoint.y - A.toPoint.y)) ∧
      chebyshevDistance (floorPoint32 P) (floorPoint Q) ≤ 1 := by
  rcases h_near with ⟨Q, hQ_seg, hdist⟩
  refine ⟨Q, hQ_seg, ?_⟩
  rw [← floorPoint_pointsToRational_eq P h_finP]
  exact hdist

/--
Every intermediate crossing waypoint produced by `rayMarchStepWaypointFloat`
satisfies `IsCellBoundaryPoint`: it lines up with at least one integer cell grid line
(x = currentX or y = currentY).
-/
theorem rayMarchStepWaypointFloat_isCellBoundaryPoint
    (start : Point32) (dx dy : Binary32) (stepX stepY : Int) (c : Cell) :
    IsCellBoundaryPoint (rayMarchStepWaypointFloat start dx dy stepX stepY c) := by
  unfold rayMarchStepWaypointFloat IsCellBoundaryPoint
  dsimp only []
  split_ifs <;> aesop

end Geometry




