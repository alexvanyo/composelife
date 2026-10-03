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
import proofs.FloatAnalysis
import proofs.SegmentBound.Waypoints
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

end Geometry
