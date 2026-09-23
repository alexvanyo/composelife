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
import Geometry.Interval
import Geometry.RayMarchStep
import Geometry.Completeness
import Geometry.Soundness

namespace Geometry


/--
Master Theorem (Exact Characterization of LineSegment Cell Intersections):
For all line segments from A to B and all discrete grid cells c:
A cell c is in `cellIntersectionsSegment A B` IF AND ONLY IF:
c is an active intersected cell of the line segment (it intersects the line segment
and is not an off-axis corner).
-/
theorem cellIntersectionsSegment_exact_iff (A B : Point) (c : Cell) :
    c ∈ cellIntersectionsSegment A B ↔ ActiveIntersectedCell c A B := by
  apply cellIntersectionsSegment_exact_iff_reduction
  intro hne hcA hcB
  have h_sound : ∀ x, x ∈ rayMarch (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 2)
      A B (B.x - A.x) (B.y - A.y)
      (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0)
      (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0)
      (floorPoint B) (floorPoint A) [] →
      inBoundingBox x A B = true ∧
      ∃ tEnter tExit, cellIntersectionInterval x A B = some (tEnter, tExit) ∧ tEnter < tExit := by
    intro x hx
    exact rayMarch_soundness A B x hx
  apply rayMarch_iff_intermediate_of_mem_eq A B c hcA hcB
  · intro x hxA hxB
    apply rayMarchIntermediateCells_iff_intermediateCells A B x hxA hxB
    · exact h_sound x
    · intro h_bbox h_int
      exact rayMarch_completeness A B x hxA hxB h_bbox h_int
  · intro hray
    rcases h_sound c hray with ⟨h_bbox, tEnter, tExit, h_int, h_lt⟩
    exact not_off_axis_of_interval_lt c A B hcA hcB h_bbox tEnter tExit h_int h_lt

end Geometry
