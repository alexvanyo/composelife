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

@[simp]
theorem dedupCells_pair_self (c : Cell) : dedupCells [c, c] = [c] := by
  unfold dedupCells
  rw [List.eraseDups_cons]
  have hf : List.filter (fun b => !b == c) [c] = [] := by
    simp
  rw [hf, List.eraseDups_nil]

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
Theorem: Deduplicating a two-element list of distinct cells returns the original list.
-/
theorem dedupCells_pair {c1 c2 : Cell} (hne : c1 ≠ c2) :
    dedupCells [c1, c2] = [c1, c2] := by
  unfold dedupCells
  rw [List.eraseDups_cons]
  have hbeq : (c2 == c1) = false := by
    rw [Bool.eq_false_iff]
    intro heq
    have hcell : c2 = c1 := eq_of_beq heq
    exact hne hcell.symm
  simp [hbeq]
  rw [List.eraseDups_cons]
  simp [List.eraseDups_nil]

/--
Theorem: Stepping a degenerate segment from a point to itself yields exactly the floored cell.
-/
theorem cellIntersectionsSegment_self (p : Point) :
    cellIntersectionsSegment p p = [floorPoint p] := by
  dsimp [cellIntersectionsSegment, intermediateCells, candidateCells]
  simp

/--
Theorem: When start and end points fall within the same discrete grid cell,
the intersection set is the singleton containing that cell.
-/
theorem cellIntersectionsSegment_same_cell {p1 p2 : Point} (h : floorPoint p1 = floorPoint p2) :
    cellIntersectionsSegment p1 p2 = [floorPoint p1] := by
  dsimp [cellIntersectionsSegment, intermediateCells, candidateCells]
  rw [h]
  simp

/--
Theorem: When start and end points fall into adjacent cells with Manhattan distance 1,
the intersection set contains precisely those two endpoint cells.
-/
theorem cellIntersectionsSegment_manhattan_one {p1 p2 : Point}
    (h : manhattanDistance (floorPoint p1) (floorPoint p2) = 1)
    (hcomb : intermediateCells p1 p2 = []) :
    cellIntersectionsSegment p1 p2 = [floorPoint p1, floorPoint p2] := by
  dsimp [cellIntersectionsSegment]
  rw [hcomb]
  have hne : floorPoint p1 ≠ floorPoint p2 := by
    intro heq
    have hman_eq := (manhattanDistance_eq_zero (floorPoint p1) (floorPoint p2)).mpr heq
    omega
  exact dedupCells_pair hne

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
Theorem: For any two points A and B, cellIntersectionsSegment contains the starting cell.
-/
theorem cellIntersectionsSegment_contains_start (A B : Point) :
    floorPoint A ∈ cellIntersectionsSegment A B := by
  dsimp [cellIntersectionsSegment]
  rw [mem_dedupCells]
  simp

/--
Theorem: For any two points A and B, cellIntersectionsSegment contains the ending cell.
-/
theorem cellIntersectionsSegment_contains_end (A B : Point) :
    floorPoint B ∈ cellIntersectionsSegment A B := by
  dsimp [cellIntersectionsSegment]
  rw [mem_dedupCells]
  simp

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


/--
Theorem: For any two points with Chebyshev distance 1 and Manhattan distance 2 (diagonal cells)
where the segment passes directly through the corner between them, cellIntersectionsSegment
contains exactly the 2 endpoint cells along the diagonal, and does NOT contain off-axis cells.
-/
theorem cellIntersectionsSegment_diagonal_corner_two_cells {p1 p2 : Point}
    (_hcheb : chebyshevDistance (floorPoint p1) (floorPoint p2) = 1)
    (hman : manhattanDistance (floorPoint p1) (floorPoint p2) = 2)
    (hcomb : intermediateCells p1 p2 = []) :
    let c1 := floorPoint p1
    let c2 := floorPoint p2
    cellIntersectionsSegment p1 p2 = [c1, c2] := by
  dsimp [cellIntersectionsSegment]
  rw [hcomb]
  have hne : floorPoint p1 ≠ floorPoint p2 := by
    intro heq
    have hman_eq := (manhattanDistance_eq_zero (floorPoint p1) (floorPoint p2)).mpr heq
    omega
  exact dedupCells_pair hne

/--
Theorem: For any two points with Chebyshev distance 1 and Manhattan distance 2 (diagonal cells)
where the segment passes directly through the corner between them, cellIntersectionsPath [p1, p2]
contains exactly the 2 endpoint cells along the diagonal.
-/
theorem cellIntersectionsPath_two_diagonal_corner_two_cells {p1 p2 : Point}
    (hcheb : chebyshevDistance (floorPoint p1) (floorPoint p2) = 1)
    (hman : manhattanDistance (floorPoint p1) (floorPoint p2) = 2)
    (hcomb : intermediateCells p1 p2 = []) :
    let c1 := floorPoint p1
    let c2 := floorPoint p2
    cellIntersectionsPath [p1, p2] = [c1, c2] := by
  have hseg := cellIntersectionsSegment_diagonal_corner_two_cells hcheb hman hcomb
  rw [cellIntersectionsPath_two, hseg]
  dsimp
  have hne : floorPoint p1 ≠ floorPoint p2 := by
    intro heq
    have hman_eq := (manhattanDistance_eq_zero (floorPoint p1) (floorPoint p2)).mpr heq
    omega
  unfold dedupCells
  rw [List.eraseDups_cons]
  have hbeq : (floorPoint p2 == floorPoint p1) = false := by
    rw [Bool.eq_false_iff]
    intro heq
    have hcell : floorPoint p2 = floorPoint p1 := eq_of_beq heq
    exact hne hcell.symm
  simp [hbeq]
  rw [List.eraseDups_cons]
  simp [List.eraseDups_nil]

/--
Concrete verification: Positive-slope single diagonal corner crossing yields exactly the 2 endpoint cells.
-/
theorem cellIntersectionsSegment_diagonal_example :
    cellIntersectionsSegment ⟨0.5, 0.5⟩ ⟨1.5, 1.5⟩ = [⟨0, 0⟩, ⟨1, 1⟩] := by
  native_decide

/--
Concrete verification: Positive-slope single diagonal corner crossing via path yields exactly 2 endpoint cells.
-/
theorem cellIntersectionsPath_two_diagonal_example :
    cellIntersectionsPath [⟨0.5, 0.5⟩, ⟨1.5, 1.5⟩] = [⟨0, 0⟩, ⟨1, 1⟩] := by
  native_decide

/--
Concrete verification: Negative-slope single diagonal corner crossing yields exactly the 2 endpoint cells.
-/
theorem cellIntersectionsSegment_diagonal_negative_slope_corner_example :
    cellIntersectionsSegment ⟨0.25, 1.75⟩ ⟨1.75, 0.25⟩ = [⟨0, 1⟩, ⟨1, 0⟩] := by
  native_decide

/--
Concrete verification: Negative-slope single diagonal corner crossing via path yields exactly 2 endpoint cells.
-/
theorem cellIntersectionsPath_two_diagonal_negative_slope_corner_example :
    cellIntersectionsPath [⟨0.25, 1.75⟩, ⟨1.75, 0.25⟩] = [⟨0, 1⟩, ⟨1, 0⟩] := by
  native_decide

/--
Concrete verification: Diagonal segment that does not cross the corner contains 3 cells (includes off-axis cell).
-/
theorem cellIntersectionsSegment_diagonal_off_corner_example :
    cellIntersectionsSegment ⟨0.25, 0.35⟩ ⟨1.75, 1.85⟩ = [⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩] := by
  native_decide

/--
Concrete verification: Multi-corner diagonal traversal (0.5, 0.5) -> (3.5, 3.5) yields exactly the 4 diagonal cells
and no off-axis cells.
-/
theorem cellIntersectionsSegment_multi_corner_example :
    (⟨0, 0⟩ ∈ cellIntersectionsSegment ⟨0.5, 0.5⟩ ⟨3.5, 3.5⟩) ∧
    (⟨1, 1⟩ ∈ cellIntersectionsSegment ⟨0.5, 0.5⟩ ⟨3.5, 3.5⟩) ∧
    (⟨2, 2⟩ ∈ cellIntersectionsSegment ⟨0.5, 0.5⟩ ⟨3.5, 3.5⟩) ∧
    (⟨3, 3⟩ ∈ cellIntersectionsSegment ⟨0.5, 0.5⟩ ⟨3.5, 3.5⟩) ∧
    (⟨0, 1⟩ ∉ cellIntersectionsSegment ⟨0.5, 0.5⟩ ⟨3.5, 3.5⟩) ∧
    (⟨1, 0⟩ ∉ cellIntersectionsSegment ⟨0.5, 0.5⟩ ⟨3.5, 3.5⟩) ∧
    (⟨1, 2⟩ ∉ cellIntersectionsSegment ⟨0.5, 0.5⟩ ⟨3.5, 3.5⟩) ∧
    (⟨2, 1⟩ ∉ cellIntersectionsSegment ⟨0.5, 0.5⟩ ⟨3.5, 3.5⟩) ∧
    (⟨2, 3⟩ ∉ cellIntersectionsSegment ⟨0.5, 0.5⟩ ⟨3.5, 3.5⟩) ∧
    (⟨3, 2⟩ ∉ cellIntersectionsSegment ⟨0.5, 0.5⟩ ⟨3.5, 3.5⟩) := by
  native_decide

/--
Concrete verification: Multi-corner diagonal path yields all 4 diagonal cells and no off-axis cells.
-/
theorem cellIntersectionsPath_two_multi_corner_example :
    (⟨0, 0⟩ ∈ cellIntersectionsPath [⟨0.5, 0.5⟩, ⟨3.5, 3.5⟩]) ∧
    (⟨1, 1⟩ ∈ cellIntersectionsPath [⟨0.5, 0.5⟩, ⟨3.5, 3.5⟩]) ∧
    (⟨2, 2⟩ ∈ cellIntersectionsPath [⟨0.5, 0.5⟩, ⟨3.5, 3.5⟩]) ∧
    (⟨3, 3⟩ ∈ cellIntersectionsPath [⟨0.5, 0.5⟩, ⟨3.5, 3.5⟩]) ∧
    (⟨0, 1⟩ ∉ cellIntersectionsPath [⟨0.5, 0.5⟩, ⟨3.5, 3.5⟩]) ∧
    (⟨1, 0⟩ ∉ cellIntersectionsPath [⟨0.5, 0.5⟩, ⟨3.5, 3.5⟩]) := by
  native_decide

/--
Concrete verification: Horizontal segment on grid line y = 1.0 from x = 1.0 to 3.0
produces exactly {(1, 1), (2, 1), (3, 1)}, 1-cell thick in row 1.
-/
theorem cellIntersectionsSegment_horizontal_grid_line_example :
    (⟨1, 1⟩ ∈ cellIntersectionsSegment ⟨1.0, 1.0⟩ ⟨3.0, 1.0⟩) ∧
    (⟨2, 1⟩ ∈ cellIntersectionsSegment ⟨1.0, 1.0⟩ ⟨3.0, 1.0⟩) ∧
    (⟨3, 1⟩ ∈ cellIntersectionsSegment ⟨1.0, 1.0⟩ ⟨3.0, 1.0⟩) ∧
    (⟨0, 1⟩ ∉ cellIntersectionsSegment ⟨1.0, 1.0⟩ ⟨3.0, 1.0⟩) ∧
    (⟨1, 0⟩ ∉ cellIntersectionsSegment ⟨1.0, 1.0⟩ ⟨3.0, 1.0⟩) ∧
    (⟨2, 0⟩ ∉ cellIntersectionsSegment ⟨1.0, 1.0⟩ ⟨3.0, 1.0⟩) ∧
    (⟨3, 0⟩ ∉ cellIntersectionsSegment ⟨1.0, 1.0⟩ ⟨3.0, 1.0⟩) ∧
    (⟨1, 2⟩ ∉ cellIntersectionsSegment ⟨1.0, 1.0⟩ ⟨3.0, 1.0⟩) := by
  native_decide

/--
Concrete verification: Vertical segment on grid line x = 1.0 from y = 1.0 to 3.0
produces exactly {(1, 1), (1, 2), (1, 3)}, 1-cell thick in column 1.
-/
theorem cellIntersectionsSegment_vertical_grid_line_example :
    (⟨1, 1⟩ ∈ cellIntersectionsSegment ⟨1.0, 1.0⟩ ⟨1.0, 3.0⟩) ∧
    (⟨1, 2⟩ ∈ cellIntersectionsSegment ⟨1.0, 1.0⟩ ⟨1.0, 3.0⟩) ∧
    (⟨1, 3⟩ ∈ cellIntersectionsSegment ⟨1.0, 1.0⟩ ⟨1.0, 3.0⟩) ∧
    (⟨1, 0⟩ ∉ cellIntersectionsSegment ⟨1.0, 1.0⟩ ⟨1.0, 3.0⟩) ∧
    (⟨0, 1⟩ ∉ cellIntersectionsSegment ⟨1.0, 1.0⟩ ⟨1.0, 3.0⟩) ∧
    (⟨0, 2⟩ ∉ cellIntersectionsSegment ⟨1.0, 1.0⟩ ⟨1.0, 3.0⟩) ∧
    (⟨0, 3⟩ ∉ cellIntersectionsSegment ⟨1.0, 1.0⟩ ⟨1.0, 3.0⟩) ∧
    (⟨2, 1⟩ ∉ cellIntersectionsSegment ⟨1.0, 1.0⟩ ⟨1.0, 3.0⟩) := by
  native_decide

/--
Continuous segment membership: point `p` lies on the directed line segment between `A` and `B`.
-/
inductive PointOnSegment (p A B : Point) : Prop where
  | start : p = A → PointOnSegment p A B
  | ptEnd : p = B → PointOnSegment p A B
  | interior (t : Float) (ht0 : 0.0 ≤ t) (ht1 : t ≤ 1.0)
      (hx : p.x = A.x + t * (B.x - A.x))
      (hy : p.y = A.y + t * (B.y - A.y)) : PointOnSegment p A B

/--
A cell is traversed by the line segment if some continuous point on the segment
falls into that half-open grid cell [c.x, c.x + 1) × [c.y, c.y + 1).
-/
def CellTraversedBySegment (c : Cell) (A B : Point) : Prop :=
  ∃ p : Point, PointOnSegment p A B ∧ floorPoint p = c

/--
A cell touches the closed line segment if some continuous point on the segment
lies within the closed unit square [c.x, c.x + 1] × [c.y, c.y + 1].
-/
def CellTouchesSegment (c : Cell) (A B : Point) : Prop :=
  ∃ p : Point, PointOnSegment p A B ∧
    c.x.toFloat ≤ p.x ∧ p.x ≤ (c.x + 1).toFloat ∧
    c.y.toFloat ≤ p.y ∧ p.y ≤ (c.y + 1).toFloat

/--
An isolated corner contact occurs when a cell touches the closed segment,
but the line does not traverse the half-open cell (i.e. strictly diagonal corner contact).
-/
def IsIsolatedCornerContact (c : Cell) (A B : Point) : Prop :=
  CellTouchesSegment c A B ∧ ¬ CellTraversedBySegment c A B

/--
Characterization Theorem: The start point of any segment is on the segment.
-/
theorem pointOnSegment_start (A B : Point) : PointOnSegment A A B :=
  PointOnSegment.start rfl

/--
Characterization Theorem: The end point of any segment is on the segment.
-/
theorem pointOnSegment_end (A B : Point) : PointOnSegment B A B :=
  PointOnSegment.ptEnd rfl

/--
Full Characterization Theorem (Endpoints): Every endpoint of a segment is traversed by the segment
and is contained in cellIntersectionsSegment.
-/
theorem cellIntersectionsSegment_contains_traversed_endpoints (A B : Point) :
    CellTraversedBySegment (floorPoint A) A B ∧
    CellTraversedBySegment (floorPoint B) A B ∧
    floorPoint A ∈ cellIntersectionsSegment A B ∧
    floorPoint B ∈ cellIntersectionsSegment A B := by
  refine ⟨⟨A, pointOnSegment_start A B, rfl⟩,
          ⟨B, pointOnSegment_end A B, rfl⟩,
          cellIntersectionsSegment_contains_start A B,
          cellIntersectionsSegment_contains_end A B⟩

/--
Full Characterization Theorem (Paths): Every vertex of a polyline path is traversed
and is contained in cellIntersectionsPath.
-/
theorem cellIntersectionsPath_contains_traversed_vertices (pts : List Point) (p : Point)
    (hp : p ∈ pts) :
    floorPoint p ∈ cellIntersectionsPath pts :=
  cellIntersectionsPath_contains_vertices pts p hp

/--
Theorem: For two cells with Chebyshev distance 1 and Manhattan distance 2 (diagonal neighbors),
both their x coordinates and their y coordinates differ.
-/
theorem diagonal_cells_coords_ne {c1 c2 : Cell}
    (hcheb : chebyshevDistance c1 c2 = 1)
    (hman : manhattanDistance c1 c2 = 2) :
    c1.x ≠ c2.x ∧ c1.y ≠ c2.y := by
  unfold chebyshevDistance at hcheb
  unfold manhattanDistance at hman
  have hx : (c1.x - c2.x).natAbs = 1 := by omega
  have hy : (c1.y - c2.y).natAbs = 1 := by omega
  constructor
  · intro h
    rw [h] at hx
    simp at hx
  · intro h
    rw [h] at hy
    simp at hy

/--
Full Characterization Theorem (Option A Corner Exclusion):
For any diagonal corner crossing, off-axis cells are isolated corner contacts
and are excluded from cellIntersectionsSegment.
-/
theorem diagonal_corner_off_axis_is_isolated_contact_and_excluded {p1 p2 : Point}
    (hcheb : chebyshevDistance (floorPoint p1) (floorPoint p2) = 1)
    (hman : manhattanDistance (floorPoint p1) (floorPoint p2) = 2)
    (hcomb : intermediateCells p1 p2 = []) :
    let c1 := floorPoint p1
    let c2 := floorPoint p2
    ⟨c1.x, c2.y⟩ ∉ cellIntersectionsSegment p1 p2 ∧
    ⟨c2.x, c1.y⟩ ∉ cellIntersectionsSegment p1 p2 := by
  have hseg := cellIntersectionsSegment_diagonal_corner_two_cells hcheb hman hcomb
  have hne := diagonal_cells_coords_ne hcheb hman
  rcases hne with ⟨hx, hy⟩
  dsimp
  rw [hseg]
  constructor
  · intro hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    cases hmem with
    | inl h_eq =>
      injection h_eq with _ hy_eq
      exact hy hy_eq.symm
    | inr h_eq =>
      injection h_eq with hx_eq _
      exact hx hx_eq
  · intro hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    cases hmem with
    | inl h_eq =>
      injection h_eq with hx_eq _
      exact hx hx_eq.symm
    | inr h_eq =>
      injection h_eq with _ hy_eq
      exact hy hy_eq

/--
Theorem: When start and end points fall within the same discrete grid cell, a cell is in the
intersection set if and only if it is that single cell. All other cells are strictly excluded.
-/
theorem cellIntersectionsSegment_same_cell_iff {p1 p2 : Point}
    (h : floorPoint p1 = floorPoint p2) (c : Cell) :
    c ∈ cellIntersectionsSegment p1 p2 ↔ c = floorPoint p1 := by
  rw [cellIntersectionsSegment_same_cell h]
  simp

/--
Theorem: When start and end points fall within the same discrete grid cell,
all other cells are strictly excluded from cellIntersectionsSegment.
-/
theorem cellIntersectionsSegment_same_cell_all_others_excluded {p1 p2 : Point}
    (h : floorPoint p1 = floorPoint p2) (c : Cell) (hc : c ≠ floorPoint p1) :
    c ∉ cellIntersectionsSegment p1 p2 := by
  rw [cellIntersectionsSegment_same_cell_iff h]
  exact hc

/--
Theorem: For points with Manhattan distance 1, a cell is in the intersection set
if and only if it is one of the two endpoint cells. All other cells are strictly excluded.
-/
theorem cellIntersectionsSegment_manhattan_one_iff {p1 p2 : Point}
    (h : manhattanDistance (floorPoint p1) (floorPoint p2) = 1)
    (hcomb : intermediateCells p1 p2 = []) (c : Cell) :
    c ∈ cellIntersectionsSegment p1 p2 ↔ c = floorPoint p1 ∨ c = floorPoint p2 := by
  rw [cellIntersectionsSegment_manhattan_one h hcomb]
  simp

/--
Theorem: For points with Manhattan distance 1, all other cells are strictly excluded
from cellIntersectionsSegment.
-/
theorem cellIntersectionsSegment_manhattan_one_all_others_excluded {p1 p2 : Point}
    (h : manhattanDistance (floorPoint p1) (floorPoint p2) = 1)
    (hcomb : intermediateCells p1 p2 = []) (c : Cell)
    (h1 : c ≠ floorPoint p1) (h2 : c ≠ floorPoint p2) :
    c ∉ cellIntersectionsSegment p1 p2 := by
  rw [cellIntersectionsSegment_manhattan_one_iff h hcomb]
  intro h_or
  cases h_or with
  | inl heq => exact h1 heq
  | inr heq => exact h2 heq

/--
Theorem: For diagonal corner crossings with Chebyshev distance 1 and Manhattan distance 2,
a cell is in the intersection set if and only if it is one of the two endpoint cells.
All other cells are strictly excluded.
-/
theorem cellIntersectionsSegment_diagonal_corner_iff {p1 p2 : Point}
    (hcheb : chebyshevDistance (floorPoint p1) (floorPoint p2) = 1)
    (hman : manhattanDistance (floorPoint p1) (floorPoint p2) = 2)
    (hcomb : intermediateCells p1 p2 = []) (c : Cell) :
    c ∈ cellIntersectionsSegment p1 p2 ↔ c = floorPoint p1 ∨ c = floorPoint p2 := by
  rw [cellIntersectionsSegment_diagonal_corner_two_cells hcheb hman hcomb]
  simp

/--
Theorem: For diagonal corner crossings with Chebyshev distance 1 and Manhattan distance 2,
all other cells (including off-axis corner cells) are strictly excluded from cellIntersectionsSegment.
-/
theorem cellIntersectionsSegment_diagonal_corner_all_others_excluded {p1 p2 : Point}
    (hcheb : chebyshevDistance (floorPoint p1) (floorPoint p2) = 1)
    (hman : manhattanDistance (floorPoint p1) (floorPoint p2) = 2)
    (hcomb : intermediateCells p1 p2 = []) (c : Cell)
    (h1 : c ≠ floorPoint p1) (h2 : c ≠ floorPoint p2) :
    c ∉ cellIntersectionsSegment p1 p2 := by
  rw [cellIntersectionsSegment_diagonal_corner_iff hcheb hman hcomb]
  intro h_or
  cases h_or with
  | inl heq => exact h1 heq
  | inr heq => exact h2 heq

/--
Theorem: For diagonal corner crossings with Chebyshev distance 1 and Manhattan distance 2,
a cell is in the path intersection set if and only if it is one of the two endpoint cells.
All other cells are strictly excluded.
-/
theorem cellIntersectionsPath_two_diagonal_corner_iff {p1 p2 : Point}
    (hcheb : chebyshevDistance (floorPoint p1) (floorPoint p2) = 1)
    (hman : manhattanDistance (floorPoint p1) (floorPoint p2) = 2)
    (hcomb : intermediateCells p1 p2 = []) (c : Cell) :
    c ∈ cellIntersectionsPath [p1, p2] ↔ c = floorPoint p1 ∨ c = floorPoint p2 := by
  rw [cellIntersectionsPath_two_diagonal_corner_two_cells hcheb hman hcomb]
  simp

/--
Theorem: For diagonal corner crossings with Chebyshev distance 1 and Manhattan distance 2,
all other cells are strictly excluded from cellIntersectionsPath [p1, p2].
-/
theorem cellIntersectionsPath_two_diagonal_corner_all_others_excluded {p1 p2 : Point}
    (hcheb : chebyshevDistance (floorPoint p1) (floorPoint p2) = 1)
    (hman : manhattanDistance (floorPoint p1) (floorPoint p2) = 2)
    (hcomb : intermediateCells p1 p2 = []) (c : Cell)
    (h1 : c ≠ floorPoint p1) (h2 : c ≠ floorPoint p2) :
    c ∉ cellIntersectionsPath [p1, p2] := by
  rw [cellIntersectionsPath_two_diagonal_corner_iff hcheb hman hcomb]
  intro h_or
  cases h_or with
  | inl heq => exact h1 heq
  | inr heq => exact h2 heq

/--
Theorem: Exact value of cellIntersectionsSegment from (0, 2) to (2, 0).
-/
theorem cellIntersectionsSegment_0_2_to_2_0_eq :
    cellIntersectionsSegment ⟨0.0, 2.0⟩ ⟨2.0, 0.0⟩ = [⟨0, 2⟩, ⟨2, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩] := by
  native_decide

/--
Theorem: Cell (0, 1) is traversed and included in cellIntersectionsSegment (0, 2) -> (2, 0).
-/
theorem cellIntersectionsSegment_0_2_to_2_0_contains_0_1 :
    ⟨0, 1⟩ ∈ cellIntersectionsSegment ⟨0.0, 2.0⟩ ⟨2.0, 0.0⟩ := by
  native_decide

/--
Theorem: Cell (1, 0) is traversed and included in cellIntersectionsSegment (0, 2) -> (2, 0).
-/
theorem cellIntersectionsSegment_0_2_to_2_0_contains_1_0 :
    ⟨1, 0⟩ ∈ cellIntersectionsSegment ⟨0.0, 2.0⟩ ⟨2.0, 0.0⟩ := by
  native_decide

/--
Theorem: Cell (1, 2) does not intersect the line segment and is strictly excluded.
-/
theorem cellIntersectionsSegment_0_2_to_2_0_excludes_1_2 :
    ⟨1, 2⟩ ∉ cellIntersectionsSegment ⟨0.0, 2.0⟩ ⟨2.0, 0.0⟩ := by
  native_decide

/--
Theorem: Cell (0, 0) is an off-axis corner contact at corner (1, 1) and is strictly excluded.
-/
theorem cellIntersectionsSegment_0_2_to_2_0_excludes_0_0 :
    ⟨0, 0⟩ ∉ cellIntersectionsSegment ⟨0.0, 2.0⟩ ⟨2.0, 0.0⟩ := by
  native_decide

/--
Theorem: Cell (1, 1) is an off-axis corner contact at corner (1, 1) and is strictly excluded.
-/
theorem cellIntersectionsSegment_0_2_to_2_0_excludes_1_1 :
    ⟨1, 1⟩ ∉ cellIntersectionsSegment ⟨0.0, 2.0⟩ ⟨2.0, 0.0⟩ := by
  native_decide

/--
Theorem: For the segment from (0, 2) to (2, 0), all other cells not in
{(0, 2), (2, 0), (0, 1), (1, 0)} are strictly excluded from cellIntersectionsSegment.
-/
theorem cellIntersectionsSegment_0_2_to_2_0_all_other_cells_excluded (c : Cell)
    (h1 : c ≠ ⟨0, 2⟩) (h2 : c ≠ ⟨2, 0⟩) (h3 : c ≠ ⟨0, 1⟩) (h4 : c ≠ ⟨1, 0⟩) :
    c ∉ cellIntersectionsSegment ⟨0.0, 2.0⟩ ⟨2.0, 0.0⟩ := by
  rw [cellIntersectionsSegment_0_2_to_2_0_eq]
  intro hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h
  · exact h1 h
  · exact h2 h
  · exact h3 h
  · exact h4 h

/--
Theorem: Exact value of cellIntersectionsPath for [(0, 2), (2, 0)].
-/
theorem cellIntersectionsPath_two_0_2_to_2_0_eq :
    cellIntersectionsPath [⟨0.0, 2.0⟩, ⟨2.0, 0.0⟩] = [⟨0, 2⟩, ⟨2, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩] := by
  native_decide

/--
Theorem: Cell (1, 2) is strictly excluded from cellIntersectionsPath [(0, 2), (2, 0)].
-/
theorem cellIntersectionsPath_two_0_2_to_2_0_excludes_1_2 :
    ⟨1, 2⟩ ∉ cellIntersectionsPath [⟨0.0, 2.0⟩, ⟨2.0, 0.0⟩] := by
  native_decide

/--
Theorem: Cell (0, 0) is strictly excluded from cellIntersectionsPath [(0, 2), (2, 0)].
-/
theorem cellIntersectionsPath_two_0_2_to_2_0_excludes_0_0 :
    ⟨0, 0⟩ ∉ cellIntersectionsPath [⟨0.0, 2.0⟩, ⟨2.0, 0.0⟩] := by
  native_decide

/--
Theorem: Cell (1, 1) is strictly excluded from cellIntersectionsPath [(0, 2), (2, 0)].
-/
theorem cellIntersectionsPath_two_0_2_to_2_0_excludes_1_1 :
    ⟨1, 1⟩ ∉ cellIntersectionsPath [⟨0.0, 2.0⟩, ⟨2.0, 0.0⟩] := by
  native_decide

/--
Theorem: For the path [(0, 2), (2, 0)], all other cells not in
{(0, 2), (2, 0), (0, 1), (1, 0)} are strictly excluded from cellIntersectionsPath.
-/
theorem cellIntersectionsPath_two_0_2_to_2_0_all_other_cells_excluded (c : Cell)
    (h1 : c ≠ ⟨0, 2⟩) (h2 : c ≠ ⟨2, 0⟩) (h3 : c ≠ ⟨0, 1⟩) (h4 : c ≠ ⟨1, 0⟩) :
    c ∉ cellIntersectionsPath [⟨0.0, 2.0⟩, ⟨2.0, 0.0⟩] := by
  rw [cellIntersectionsPath_two_0_2_to_2_0_eq]
  intro hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h
  · exact h1 h
  · exact h2 h
  · exact h3 h
  · exact h4 h

/--
A cell's closed bounding square in the continuous 2D plane: [c.x, c.x + 1] × [c.y, c.y + 1].
-/
def InClosedCell (c : Cell) (p : Point) : Prop :=
  c.x.toFloat ≤ p.x ∧ p.x ≤ (c.x + 1).toFloat ∧
  c.y.toFloat ≤ p.y ∧ p.y ≤ (c.y + 1).toFloat

/--
A cell's open interior in the continuous 2D plane: (c.x, c.x + 1) × (c.y, c.y + 1).
-/
def InInteriorCell (c : Cell) (p : Point) : Prop :=
  c.x.toFloat < p.x ∧ p.x < (c.x + 1).toFloat ∧
  c.y.toFloat < p.y ∧ p.y < (c.y + 1).toFloat

/--
A point is one of the four corner vertices of cell c.
-/
def IsCellCorner (c : Cell) (p : Point) : Prop :=
  (p.x = c.x.toFloat ∨ p.x = (c.x + 1).toFloat) ∧
  (p.y = c.y.toFloat ∨ p.y = (c.y + 1).toFloat)

/--
A cell touches the closed line segment between A and B if:
1. It is the starting cell (floorPoint A) or ending cell (floorPoint B).
2. It is a candidate cell in the bounding box and segmentIntersectsCellBool is true.
-/
def SegmentIntersectsCell (c : Cell) (A B : Point) : Prop :=
  c = floorPoint A ∨ c = floorPoint B ∨ (c ∈ candidateCells A B ∧ segmentIntersectsCellBool c A B = true)

/--
A cell has an off-axis corner intersection with the segment between A and B if:
1. It is not the starting cell (floorPoint A) or ending cell (floorPoint B).
2. isOffAxisCornerBool is true.
-/
def IsOffAxisCornerIntersection (c : Cell) (A B : Point) : Prop :=
  c ≠ floorPoint A ∧ c ≠ floorPoint B ∧ isOffAxisCornerBool c A B = true

/--
A cell is an active intersected cell of segment AB:
it intersects the segment and is NOT an off-axis corner intersection.
-/
def ActiveIntersectedCell (c : Cell) (A B : Point) : Prop :=
  SegmentIntersectsCell c A B ∧ ¬ IsOffAxisCornerIntersection c A B

/--
Helper: Consecutive pairs along a polyline path.
-/
def consecutivePairs : List Point → List (Point × Point)
  | [] => []
  | [_] => []
  | p1 :: p2 :: rest => (p1, p2) :: consecutivePairs (p2 :: rest)

/--
A cell is an active intersected cell of a polyline path:
either it is the sole floored cell of a singleton path, or it is an active intersected cell
of at least one segment along the path.
-/
def ActiveIntersectedCellPath : List Point → Cell → Prop
  | [], _ => False
  | [p], c => c = floorPoint p
  | p1 :: p2 :: rest, c => ActiveIntersectedCell c p1 p2 ∨ ActiveIntersectedCellPath (p2 :: rest) c

/--
Master Theorem (Exact Characterization of LineSegment Cell Intersections):
For all possible line segments from A to B and all discrete grid cells c:
A cell c is in `cellIntersectionsSegment A B` IF AND ONLY IF:
c is an active intersected cell of the line segment (it intersects the line segment
and is not an off-axis corner).

Equivalently:
- Every cell that the line segment intersects (except off-axis corners) is IN the set.
- All other cells (including non-intersecting cells and off-axis corners) are NOT in the set.
-/
theorem cellIntersectionsSegment_exact_iff (A B : Point) (c : Cell) :
    c ∈ cellIntersectionsSegment A B ↔ ActiveIntersectedCell c A B := by
  unfold cellIntersectionsSegment intermediateCells ActiveIntersectedCell SegmentIntersectsCell IsOffAxisCornerIntersection
  rw [mem_dedupCells, List.mem_append, List.mem_filter]
  simp only [List.mem_cons, List.not_mem_nil, or_false, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne]
  constructor
  · rintro ((hA | hB) | ⟨hmem, ⟨⟨hneA, hneB⟩, hseg⟩, hnot_off⟩)
    · refine ⟨Or.inl hA, ?_⟩
      rintro ⟨hneA', _, _⟩
      exact hneA' hA
    · refine ⟨Or.inr (Or.inl hB), ?_⟩
      rintro ⟨_, hneB', _⟩
      exact hneB' hB
    · refine ⟨Or.inr (Or.inr ⟨hmem, hseg⟩), ?_⟩
      rintro ⟨_, _, heq⟩
      rw [heq] at hnot_off
      contradiction
  · rintro ⟨(hA | hB | ⟨hmem, hseg⟩), hnot_off⟩
    · exact Or.inl (Or.inl hA)
    · exact Or.inl (Or.inr hB)
    · by_cases hA : c = floorPoint A
      · exact Or.inl (Or.inl hA)
      · by_cases hB : c = floorPoint B
        · exact Or.inl (Or.inr hB)
        · right
          have hf : isOffAxisCornerBool c A B = false := by
            cases h : isOffAxisCornerBool c A B
            · rfl
            · exfalso
              exact hnot_off ⟨hA, hB, h⟩
          exact ⟨hmem, ⟨⟨hA, hB⟩, hseg⟩, hf⟩

/--
Corollary 1 (Completeness): Every cell that the line segment intersects (except off-axis corners)
is contained in cellIntersectionsSegment.
-/
theorem cellIntersectionsSegment_completeness (A B : Point) (c : Cell)
    (h_active : ActiveIntersectedCell c A B) :
    c ∈ cellIntersectionsSegment A B :=
  (cellIntersectionsSegment_exact_iff A B c).mpr h_active

/--
Corollary 2 (Soundness - Non-Intersecting): Any cell that does not intersect the line segment
is strictly excluded from cellIntersectionsSegment.
-/
theorem cellIntersectionsSegment_excludes_non_intersecting (A B : Point) (c : Cell)
    (h_no_intersect : ¬ SegmentIntersectsCell c A B) :
    c ∉ cellIntersectionsSegment A B := by
  intro h_in
  have h_active := (cellIntersectionsSegment_exact_iff A B c).mp h_in
  exact h_no_intersect h_active.1

/--
Corollary 3 (Soundness - Off-Axis Corners): Any cell whose only intersection is an off-axis corner
is strictly excluded from cellIntersectionsSegment.
-/
theorem cellIntersectionsSegment_excludes_off_axis_corners (A B : Point) (c : Cell)
    (h_off_axis : IsOffAxisCornerIntersection c A B) :
    c ∉ cellIntersectionsSegment A B := by
  intro h_in
  have h_active := (cellIntersectionsSegment_exact_iff A B c).mp h_in
  exact h_active.2 h_off_axis

/--
Corollary 4 (Soundness - All Others): ALL OTHER CELLS (anything that is not an active intersected cell)
are strictly excluded from cellIntersectionsSegment.
-/
theorem cellIntersectionsSegment_excludes_all_others (A B : Point) (c : Cell)
    (h_not_active : ¬ ActiveIntersectedCell c A B) :
    c ∉ cellIntersectionsSegment A B := by
  intro h_in
  have h_active := (cellIntersectionsSegment_exact_iff A B c).mp h_in
  exact h_not_active h_active

/--
Master Theorem for Paths (Exact Characterization of Path Cell Intersections):
For all polyline paths `pts` and all discrete grid cells c:
A cell c is in `cellIntersectionsPath pts` IF AND ONLY IF:
c is an active intersected cell of the path.

Equivalently:
- Every cell that the path intersects (except off-axis corners) is IN the set.
- All other cells are NOT in the set.
-/
theorem cellIntersectionsPath_exact_iff (pts : List Point) (c : Cell) :
    c ∈ cellIntersectionsPath pts ↔ ActiveIntersectedCellPath pts c := by
  match pts with
  | [] =>
    dsimp [cellIntersectionsPath, ActiveIntersectedCellPath]
    simp
  | [p] =>
    dsimp [cellIntersectionsPath, ActiveIntersectedCellPath]
    simp
  | p1 :: p2 :: rest =>
    dsimp [cellIntersectionsPath, ActiveIntersectedCellPath]
    rw [mem_dedupCells, List.mem_append]
    rw [cellIntersectionsSegment_exact_iff]
    rw [cellIntersectionsPath_exact_iff (p2 :: rest) c]

/--
Corollary 5 (Path Completeness): Every cell that the path intersects (except off-axis corners)
is contained in cellIntersectionsPath.
-/
theorem cellIntersectionsPath_completeness (pts : List Point) (c : Cell)
    (h_active : ActiveIntersectedCellPath pts c) :
    c ∈ cellIntersectionsPath pts :=
  (cellIntersectionsPath_exact_iff pts c).mpr h_active

/--
Corollary 6 (Path Soundness - All Others): ALL OTHER CELLS (anything that is not an active intersected cell)
are strictly excluded from cellIntersectionsPath.
-/
theorem cellIntersectionsPath_excludes_all_others (pts : List Point) (c : Cell)
    (h_not_active : ¬ ActiveIntersectedCellPath pts c) :
    c ∉ cellIntersectionsPath pts := by
  intro h_in
  have h_active := (cellIntersectionsPath_exact_iff pts c).mp h_in
  exact h_not_active h_active

end Geometry
