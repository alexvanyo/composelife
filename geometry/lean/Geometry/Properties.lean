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

/--
Theorem: Two cells are equal if and only if both their x and y coordinates are equal.
-/
theorem cell_ext {c1 c2 : Cell} (hx : c1.x = c2.x) (hy : c1.y = c2.y) : c1 = c2 := by
  cases c1; cases c2
  congr

/--
Theorem: Manhattan distance between two cells is zero if and only if the cells are identical.
-/
theorem manhattanDistance_eq_zero (a b : Cell) :
    manhattanDistance a b = 0 ↔ a = b := by
  constructor
  · intro h
    unfold manhattanDistance at h
    have hx : (a.x - b.x).natAbs = 0 := by omega
    have hy : (a.y - b.y).natAbs = 0 := by omega
    have hx2 : a.x = b.x := by
      have := Int.natAbs_eq_zero.mp hx
      omega
    have hy2 : a.y = b.y := by
      have := Int.natAbs_eq_zero.mp hy
      omega
    exact cell_ext hx2 hy2
  · intro h
    rw [h]
    exact manhattanDistance_self b

/--
Theorem: For any two points A and B, cellIntersectionsSegment contains the starting cell.
-/
theorem cellIntersectionsSegment_contains_start (A B : Point) :
    floorPoint A ∈ cellIntersectionsSegment A B := by
  dsimp [cellIntersectionsSegment]
  split
  · simp
  · split
    · simp
    · split
      · rw [mem_dedupCells]; simp
      · split
        · rw [mem_dedupCells]; simp
        · rw [mem_dedupCells]; simp

/--
Theorem: For any two points A and B, cellIntersectionsSegment contains the ending cell.
-/
theorem cellIntersectionsSegment_contains_end (A B : Point) :
    floorPoint B ∈ cellIntersectionsSegment A B := by
  dsimp [cellIntersectionsSegment]
  split
  · rename_i h
    have hman : manhattanDistance (floorPoint A) (floorPoint B) = 0 := by
      revert h
      cases manhattanDistance (floorPoint A) (floorPoint B) <;> simp
    have heq : floorPoint A = floorPoint B :=
      (manhattanDistance_eq_zero (floorPoint A) (floorPoint B)).mp hman
    simp [← heq]
  · split
    · simp
    · split
      · rw [mem_dedupCells]; simp
      · split
        · rw [mem_dedupCells]; simp
        · rw [mem_dedupCells]; simp

/--
Theorem: For any two points A and B, cellIntersectionsPath [A, B] contains the starting cell.
-/
theorem cellIntersectionsPath_two_contains_start (A B : Point) :
    floorPoint A ∈ cellIntersectionsPath [A, B] := by
  rw [cellIntersectionsPath_two, mem_dedupCells, List.mem_append]
  left
  exact cellIntersectionsSegment_contains_start A B

/--
Theorem: For any two points A and B, cellIntersectionsPath [A, B] contains the ending cell.
-/
theorem cellIntersectionsPath_two_contains_end (A B : Point) :
    floorPoint B ∈ cellIntersectionsPath [A, B] := by
  rw [cellIntersectionsPath_two, mem_dedupCells, List.mem_append]
  right
  simp

/--
Theorem: For any two points A and B, cellIntersectionsPath [A, B] gives cells connecting
those two points, containing both the start and end grid cells.
-/
theorem cellIntersectionsPath_connects_points (A B : Point) :
    floorPoint A ∈ cellIntersectionsPath [A, B] ∧
    floorPoint B ∈ cellIntersectionsPath [A, B] :=
  ⟨cellIntersectionsPath_two_contains_start A B, cellIntersectionsPath_two_contains_end A B⟩

/--
Theorem: For any two points A and B, cellIntersectionsPath [A, B] connects the two points
and produces a non-empty set of grid cells.
-/
theorem cellIntersectionsPath_two_connects_points (A B : Point) :
    floorPoint A ∈ cellIntersectionsPath [A, B] ∧
    floorPoint B ∈ cellIntersectionsPath [A, B] ∧
    cellIntersectionsPath [A, B] ≠ [] := by
  have hs := cellIntersectionsPath_two_contains_start A B
  have he := cellIntersectionsPath_two_contains_end A B
  refine ⟨hs, he, ?_⟩
  intro hnil
  rw [hnil] at hs
  contradiction

/--
Theorem: For any polyline path, cellIntersectionsPath contains the grid cell of every vertex along the path.
-/
theorem cellIntersectionsPath_contains_vertices : ∀ (pts : List Point) (p : Point),
    p ∈ pts → floorPoint p ∈ cellIntersectionsPath pts
  | [], p, hp => nomatch hp
  | [q], p, hp => by
    cases hp with
    | head =>
      simp [cellIntersectionsPath]
    | tail _ hp_rest =>
      nomatch hp_rest
  | p1 :: p2 :: rest, p, hp => by
    dsimp [cellIntersectionsPath]
    rw [mem_dedupCells, List.mem_append]
    cases hp with
    | head =>
      left
      exact cellIntersectionsSegment_contains_start p1 p2
    | tail _ hp_rest =>
      right
      exact cellIntersectionsPath_contains_vertices (p2 :: rest) p hp_rest


/--
Theorem: cellIntersectionsPath correctly connects any points A and B along a path.
-/
theorem cellIntersectionsPath_correct (A B : Point) :
    floorPoint A ∈ cellIntersectionsPath [A, B] ∧
    floorPoint B ∈ cellIntersectionsPath [A, B] :=
  cellIntersectionsPath_connects_points A B

/--
Theorem: For any non-empty path, cellIntersectionsPath is non-empty.
-/
theorem cellIntersectionsPath_nonempty (p : Point) (rest : List Point) :
    cellIntersectionsPath (p :: rest) ≠ [] := by
  have h := cellIntersectionsPath_contains_vertices (p :: rest) p (by simp)
  intro hnil
  rw [hnil] at h
  contradiction

end Geometry
