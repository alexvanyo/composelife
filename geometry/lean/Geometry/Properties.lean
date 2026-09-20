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

namespace Geometry

/--
Theorem: Empty path produces an empty list of cells.
-/
theorem cellIntersectionsPath_nil :
    cellIntersectionsPath [] = [] := by
  rfl

/--
Theorem: A single point path produces exactly the floored cell of that point.
-/
theorem cellIntersectionsPath_singleton (p : Point) :
    cellIntersectionsPath [p] = [floorPoint p] := by
  rfl

/--
Theorem: Manhattan distance between identical cells is zero.
-/
theorem manhattanDistance_self (c : Cell) :
    manhattanDistance c c = 0 := by
  unfold manhattanDistance
  simp

/--
Theorem: Chebyshev distance between identical cells is zero.
-/
theorem chebyshevDistance_self (c : Cell) :
    chebyshevDistance c c = 0 := by
  unfold chebyshevDistance
  simp

/--
Theorem: Chebyshev distance is always bounded above by Manhattan distance.
-/
theorem chebyshev_le_manhattan (a b : Cell) :
    chebyshevDistance a b ≤ manhattanDistance a b := by
  unfold chebyshevDistance manhattanDistance
  omega

/--
Theorem: Stepping a degenerate segment from a point to itself yields exactly the floored cell.
-/
theorem cellIntersectionsSegment_self (p : Point) :
    cellIntersectionsSegment p p = [floorPoint p] := by
  unfold cellIntersectionsSegment
  have hman : manhattanDistance (floorPoint p) (floorPoint p) = 0 := manhattanDistance_self (floorPoint p)
  simp [hman]

/--
Theorem: When start and end points fall within the same discrete grid cell,
the intersection set is the singleton containing that cell.
-/
theorem cellIntersectionsSegment_same_cell {p1 p2 : Point} (h : floorPoint p1 = floorPoint p2) :
    cellIntersectionsSegment p1 p2 = [floorPoint p1] := by
  unfold cellIntersectionsSegment
  have hman : manhattanDistance (floorPoint p1) (floorPoint p2) = 0 := by
    rw [h]
    exact manhattanDistance_self (floorPoint p2)
  simp [hman]

/--
Theorem: When start and end points fall into adjacent cells with Manhattan distance 1,
the intersection set contains precisely those two endpoint cells.
-/
theorem cellIntersectionsSegment_manhattan_one {p1 p2 : Point}
    (h : manhattanDistance (floorPoint p1) (floorPoint p2) = 1) :
    cellIntersectionsSegment p1 p2 = [floorPoint p1, floorPoint p2] := by
  unfold cellIntersectionsSegment
  have hman0 : (manhattanDistance (floorPoint p1) (floorPoint p2) == 0) = false := by
    simp [h]
  have hman1 : (manhattanDistance (floorPoint p1) (floorPoint p2) == 1) = true := by
    simp [h]
  simp [hman0, hman1]

/--
Theorem: Manhattan distance is symmetric.
-/
theorem manhattanDistance_comm (a b : Cell) :
    manhattanDistance a b = manhattanDistance b a := by
  unfold manhattanDistance
  omega

/--
Theorem: Chebyshev distance is symmetric.
-/
theorem chebyshevDistance_comm (a b : Cell) :
    chebyshevDistance a b = chebyshevDistance b a := by
  unfold chebyshevDistance
  omega

/--
Theorem: Manhattan distance satisfies the triangle inequality.
-/
theorem manhattanDistance_triangle (a b c : Cell) :
    manhattanDistance a c ≤ manhattanDistance a b + manhattanDistance b c := by
  unfold manhattanDistance
  omega

/--
Theorem: Evaluating cellIntersectionsPath on a two-point segment reduces to the segment intersection.
-/
theorem cellIntersectionsPath_two (p1 p2 : Point) :
    cellIntersectionsPath [p1, p2] = dedupCells (cellIntersectionsSegment p1 p2 ++ [floorPoint p2]) := by
  rfl

end Geometry
