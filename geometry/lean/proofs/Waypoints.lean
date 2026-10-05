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

end Geometry
