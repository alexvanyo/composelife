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

/-!
# Definitions
-/

/--
Checks whether cell `c` is inside the bounding box formed by the floored endpoints `A` and `B`.
-/
def inBoundingBox (c : Cell) (A B : Point) : Bool :=
  let startCell := floorPoint A
  let endCell := floorPoint B
  let minX := min startCell.x endCell.x
  let maxX := max startCell.x endCell.x
  let minY := min startCell.y endCell.y
  let maxY := max startCell.y endCell.y
  minX <= c.x && c.x <= maxX && minY <= c.y && c.y <= maxY

/--
Computes the parameter interval [tEnter, tExit] ⊆ [0, 1] along the segment `A + t(B - A)`
that falls within the closed unit square [c.x, c.x + 1] × [c.y, c.y + 1].
Returns `none` if the segment does not intersect the cell's closed area.
-/
def cellIntersectionInterval (c : Cell) (A B : Point) : Option (Binary32 × Binary32) :=
  let dx := B.x - A.x
  let dy := B.y - A.y
  let cx0 := ofInt c.x
  let cx1 := ofInt (c.x + 1)
  let cy0 := ofInt c.y
  let cy1 := ofInt (c.y + 1)
  let (tx0, tx1) :=
    if dx == 0.0 then
      if A.x < cx0 || A.x > cx1 then (1.0, 0.0) else (0.0, 1.0)
    else if dx > 0.0 then
      ((cx0 - A.x) / dx, (cx1 - A.x) / dx)
    else
      ((cx1 - A.x) / dx, (cx0 - A.x) / dx)
  let (ty0, ty1) :=
    if dy == 0.0 then
      if A.y < cy0 || A.y > cy1 then (1.0, 0.0) else (0.0, 1.0)
    else if dy > 0.0 then
      ((cy0 - A.y) / dy, (cy1 - A.y) / dy)
    else
      ((cy1 - A.y) / dy, (cy0 - A.y) / dy)
  let tEnter := max 0.0 (max tx0 ty0)
  let tExit := min 1.0 (min tx1 ty1)
  if tEnter <= tExit then
    some (tEnter, tExit)
  else
    none

/--
Returns true if the line segment from `A` to `B` intersects cell `c`.
-/
def segmentIntersectsCellBool (c : Cell) (A B : Point) : Bool :=
  if c == floorPoint A || c == floorPoint B then
    true
  else if !inBoundingBox c A B then
    false
  else
    match cellIntersectionInterval c A B with
    | some _ => true
    | none => false

/--
Returns true if cell `c` has an off-axis corner contact with the segment:
it touches the segment at a single corner point, does not enter the interior,
and is not an endpoint cell (start or end).
-/
def isOffAxisCornerBool (c : Cell) (A B : Point) : Bool :=
  if c == floorPoint A || c == floorPoint B then
    false
  else if !inBoundingBox c A B then
    false
  else
    match cellIntersectionInterval c A B with
    | some (tEnter, tExit) => tEnter == tExit
    | none => false

/--
Generates all candidate grid cells within the bounding box of endpoints `A` and `B`.
-/
def candidateCells (A B : Point) : List Cell :=
  let startCell := floorPoint A
  let endCell := floorPoint B
  let minX := min startCell.x endCell.x
  let maxX := max startCell.x endCell.x
  let minY := min startCell.y endCell.y
  let maxY := max startCell.y endCell.y
  let xCount := (maxX - minX + 1).toNat
  let yCount := (maxY - minY + 1).toNat
  (List.range xCount).flatMap (fun dx =>
    (List.range yCount).map (fun dy =>
      ⟨minX + Int.ofNat dx, minY + Int.ofNat dy⟩))

/--
Candidate cells strictly between the endpoints that are actively intersected by the line segment.
-/
def intermediateCells (A B : Point) : List Cell :=
  let startCell := floorPoint A
  let endCell := floorPoint B
  (candidateCells A B).filter (fun c =>
    (c != startCell) && (c != endCell) && segmentIntersectsCellBool c A B && !isOffAxisCornerBool c A B)

/--
Intermediate cells traversed via ray-marching in O(W + H) time.
-/
def rayMarchIntermediateCells (A B : Point) : List Cell :=
  let startCell := floorPoint A
  let endCell := floorPoint B
  let dx := B.x - A.x
  let dy := B.y - A.y
  let stepX : Int := if dx > 0.0 then 1 else if dx < 0.0 then -1 else 0
  let stepY : Int := if dy > 0.0 then 1 else if dy < 0.0 then -1 else 0
  let maxSteps := (endCell.x - startCell.x).natAbs + (endCell.y - startCell.y).natAbs + 2
  (rayMarch maxSteps A B dx dy stepX stepY endCell startCell []).filter (fun c =>
    (c != startCell) && (c != endCell) && !isOffAxisCornerBool c A B)

/--
Continuous segment membership: point `p` lies on the directed line segment between `A` and `B`.
-/
inductive PointOnSegment (p A B : Point) : Prop where
  | start : p = A → PointOnSegment p A B
  | ptEnd : p = B → PointOnSegment p A B
  | interior (t : Binary32) (ht0 : 0.0 ≤ t) (ht1 : t ≤ 1.0)
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
    ofInt c.x ≤ p.x ∧ p.x ≤ ofInt (c.x + 1) ∧
    ofInt c.y ≤ p.y ∧ p.y ≤ ofInt (c.y + 1)

/--
An isolated corner contact occurs when a cell touches the closed segment,
but the line does not traverse the half-open cell (i.e. strictly diagonal corner contact).
-/
def IsIsolatedCornerContact (c : Cell) (A B : Point) : Prop :=
  CellTouchesSegment c A B ∧ ¬ CellTraversedBySegment c A B

/--
A cell's closed bounding square in the continuous 2D plane: [c.x, c.x + 1] × [c.y, c.y + 1].
-/
def InClosedCell (c : Cell) (p : Point) : Prop :=
  ofInt c.x ≤ p.x ∧ p.x ≤ ofInt (c.x + 1) ∧
  ofInt c.y ≤ p.y ∧ p.y ≤ ofInt (c.y + 1)

/--
A cell's open interior in the continuous 2D plane: (c.x, c.x + 1) × (c.y, c.y + 1).
-/
def InInteriorCell (c : Cell) (p : Point) : Prop :=
  ofInt c.x < p.x ∧ p.x < ofInt (c.x + 1) ∧
  ofInt c.y < p.y ∧ p.y < ofInt (c.y + 1)

/--
A point is one of the four corner vertices of cell c.
-/
def IsCellCorner (c : Cell) (p : Point) : Prop :=
  (p.x = ofInt c.x ∨ p.x = ofInt (c.x + 1)) ∧
  (p.y = ofInt c.y ∨ p.y = ofInt (c.y + 1))

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

/-!
# Foundational Lemmas: Cells and Deduplication
-/

/--
Theorem: Membership in dedupCells is equivalent to membership in the original list.
-/
@[simp]
theorem mem_dedupCells (c : Cell) (cells : List Cell) : c ∈ dedupCells cells ↔ c ∈ cells :=
  List.mem_eraseDups

/--
Theorem: Two cells are equal if and only if both their x and y coordinates are equal.
-/
theorem cell_ext {c1 c2 : Cell} (hx : c1.x = c2.x) (hy : c1.y = c2.y) : c1 = c2 := by
  cases c1; cases c2
  congr

/--
Theorem: Deduplicating a list of two identical cells yields the singleton cell.
-/
theorem dedupCells_same (c : Cell) : dedupCells [c, c] = [c] := by
  unfold dedupCells
  rw [List.eraseDups_cons]
  have _hbeq : (c == c) = true := beq_self_eq_true c
  simp [List.eraseDups_nil]

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

/-!
# Structural Ray-Marching Lemmas
-/

/--
Theorem: Ray-marching with zero fuel returns the accumulator unmodified.
-/
theorem rayMarch_zero (start ptEnd : Point) (dx dy : Binary32) (stepX stepY : Int)
    (endCell current : Cell) (acc : List Cell) :
    rayMarch 0 start ptEnd dx dy stepX stepY endCell current acc = acc :=
  rfl

/--
Theorem: Ray-marching halting condition when current cell reaches end cell.
-/
theorem rayMarch_self (fuel : Nat) (start ptEnd : Point) (dx dy : Binary32) (stepX stepY : Int)
    (endCell : Cell) (acc : List Cell) :
    rayMarch (fuel + 1) start ptEnd dx dy stepX stepY endCell endCell acc = acc := by
  dsimp [rayMarch]
  simp

/--
Theorem: Ray-marching halting condition when rayMarchStep indicates completion.
-/
theorem rayMarch_step_done (fuel : Nat) (start ptEnd : Point) (dx dy : Binary32) (stepX stepY : Int)
    (endCell current : Cell) (acc : List Cell) (h_not_end : (current == endCell) = false)
    (nextCell : Cell) (h_step : rayMarchStep start ptEnd dx dy stepX stepY current = (nextCell, true)) :
    rayMarch (fuel + 1) start ptEnd dx dy stepX stepY endCell current acc = acc := by
  change (if current == endCell then acc
          else
            let (nextCell', done) := rayMarchStep start ptEnd dx dy stepX stepY current
            if done then acc
            else rayMarch fuel start ptEnd dx dy stepX stepY endCell nextCell' (acc ++ [nextCell'])) = acc
  rw [h_not_end]
  dsimp only
  rw [h_step]
  rfl

/--
Theorem: Ray-marching recursive transition step.
-/
theorem rayMarch_step_continue (fuel : Nat) (start ptEnd : Point) (dx dy : Binary32) (stepX stepY : Int)
    (endCell current : Cell) (acc : List Cell) (h_not_end : (current == endCell) = false)
    (nextCell : Cell) (h_step : rayMarchStep start ptEnd dx dy stepX stepY current = (nextCell, false)) :
    rayMarch (fuel + 1) start ptEnd dx dy stepX stepY endCell current acc =
      rayMarch fuel start ptEnd dx dy stepX stepY endCell nextCell (acc ++ [nextCell]) := by
  change (if current == endCell then acc
          else
            let (nextCell', done) := rayMarchStep start ptEnd dx dy stepX stepY current
            if done then acc
            else rayMarch fuel start ptEnd dx dy stepX stepY endCell nextCell' (acc ++ [nextCell'])) =
      rayMarch fuel start ptEnd dx dy stepX stepY endCell nextCell (acc ++ [nextCell])
  rw [h_not_end]
  dsimp only
  rw [h_step]
  rfl

/--
Theorem: Accumulating in ray-marching distributes over appending.
-/
theorem rayMarch_acc (fuel : Nat) (start ptEnd : Point) (dx dy : Binary32) (stepX stepY : Int)
    (endCell current : Cell) (acc : List Cell) :
    rayMarch fuel start ptEnd dx dy stepX stepY endCell current acc =
      acc ++ rayMarch fuel start ptEnd dx dy stepX stepY endCell current [] := by
  induction fuel generalizing current acc with
  | zero =>
    dsimp [rayMarch]
    simp
  | succ fuel ih =>
    dsimp [rayMarch]
    split
    · simp
    · split
      · simp
      · rw [ih (acc := acc ++ [_])]
        rw [ih (acc := [_])]
        simp

/--
Theorem: Membership in a ray-marching run decomposes into membership in the accumulator
or in the remaining ray-marching traversal.
-/
theorem mem_rayMarch (fuel : Nat) (start ptEnd : Point) (dx dy : Binary32) (stepX stepY : Int)
    (endCell current : Cell) (acc : List Cell) (c : Cell) :
    c ∈ rayMarch fuel start ptEnd dx dy stepX stepY endCell current acc ↔
      c ∈ acc ∨ c ∈ rayMarch fuel start ptEnd dx dy stepX stepY endCell current [] := by
  rw [rayMarch_acc]
  rw [List.mem_append]

/--
Theorem: Unfolding a non-zero-fuel ray-marching step.
-/
theorem rayMarch_step_unfold (fuel : Nat) (start ptEnd : Point) (dx dy : Binary32) (stepX stepY : Int)
    (endCell current : Cell) :
    rayMarch (fuel + 1) start ptEnd dx dy stepX stepY endCell current [] =
      if current == endCell then []
      else
        let (nextCell, done) := rayMarchStep start ptEnd dx dy stepX stepY current
        if done then []
        else nextCell :: rayMarch fuel start ptEnd dx dy stepX stepY endCell nextCell [] := by
  dsimp [rayMarch]
  split
  · rfl
  · split
    · rfl
    · rw [rayMarch_acc]
      rfl

/-!
# Intermediate Cells Lemmas
-/

/--
Theorem: When endpoints coincide, intermediate candidate filtering yields no intermediate cells.
-/
theorem intermediateCells_self (p : Point) : intermediateCells p p = [] := by
  dsimp [intermediateCells, candidateCells]
  simp

/--
Theorem: When endpoints share the same floored cell, intermediate candidate filtering yields no intermediate cells.
-/
theorem intermediateCells_same_cell {p1 p2 : Point} (h : floorPoint p1 = floorPoint p2) :
    intermediateCells p1 p2 = [] := by
  dsimp [intermediateCells, candidateCells]
  rw [h]
  simp

/--
Theorem: When endpoints share the same floored cell, ray-marching yields no intermediate cells.
-/
theorem rayMarchIntermediateCells_same_cell {p1 p2 : Point} (h : floorPoint p1 = floorPoint p2) :
    rayMarchIntermediateCells p1 p2 = [] := by
  dsimp [rayMarchIntermediateCells]
  have hsteps : (floorPoint p2).x - (floorPoint p1).x = 0 := by rw [h]; ring
  have hstepsy : (floorPoint p2).y - (floorPoint p1).y = 0 := by rw [h]; ring
  rw [hsteps, hstepsy]
  dsimp
  rw [h]
  dsimp [rayMarch]
  simp

/--
Theorem: When endpoints coincide, ray-marching yields no intermediate cells.
-/
theorem rayMarchIntermediateCells_self (p : Point) :
    rayMarchIntermediateCells p p = [] :=
  rayMarchIntermediateCells_same_cell rfl

/--
Theorem: Membership in intermediateCells decomposed into its exact constituent predicates.
-/
theorem mem_intermediateCells_iff (A B : Point) (c : Cell) :
    c ∈ intermediateCells A B ↔
      c ∈ candidateCells A B ∧
      c ≠ floorPoint A ∧
      c ≠ floorPoint B ∧
      segmentIntersectsCellBool c A B = true ∧
      isOffAxisCornerBool c A B = false := by
  dsimp [intermediateCells]
  rw [List.mem_filter]
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne]
  tauto

/--
Theorem: Membership in rayMarchIntermediateCells decomposed into its exact constituent predicates.
-/
theorem mem_rayMarchIntermediateCells_iff (A B : Point) (c : Cell) :
    let startCell := floorPoint A
    let endCell := floorPoint B
    let dx := B.x - A.x
    let dy := B.y - A.y
    let stepX : Int := if dx > 0.0 then 1 else if dx < 0.0 then -1 else 0
    let stepY : Int := if dy > 0.0 then 1 else if dy < 0.0 then -1 else 0
    let maxSteps := (endCell.x - startCell.x).natAbs + (endCell.y - startCell.y).natAbs + 2
    c ∈ rayMarchIntermediateCells A B ↔
      c ∈ rayMarch maxSteps A B dx dy stepX stepY endCell startCell [] ∧
      c ≠ startCell ∧
      c ≠ endCell ∧
      isOffAxisCornerBool c A B = false := by
  dsimp [rayMarchIntermediateCells]
  rw [List.mem_filter]
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne]
  tauto

/-!
# Segment and Path Connection Properties
-/

/--
Theorem: Stepping a degenerate segment from a point to itself yields exactly the floored cell.
-/
theorem cellIntersectionsSegment_self (p : Point) :
    cellIntersectionsSegment p p = [floorPoint p] := by
  dsimp [cellIntersectionsSegment]
  simp

/--
Theorem: When start and end points fall within the same discrete grid cell,
the intersection set is the singleton containing that cell.
-/
theorem cellIntersectionsSegment_same_cell {p1 p2 : Point} (h : floorPoint p1 = floorPoint p2) :
    cellIntersectionsSegment p1 p2 = [floorPoint p1] := by
  dsimp [cellIntersectionsSegment]
  rw [h]
  simp

/--
Theorem: For any two points A and B, cellIntersectionsSegment contains the starting cell.
-/
theorem cellIntersectionsSegment_contains_start (A B : Point) :
    floorPoint A ∈ cellIntersectionsSegment A B := by
  dsimp [cellIntersectionsSegment]
  split
  · simp
  · rw [mem_dedupCells]
    simp

/--
Theorem: For any two points A and B, cellIntersectionsSegment contains the ending cell.
-/
theorem cellIntersectionsSegment_contains_end (A B : Point) :
    floorPoint B ∈ cellIntersectionsSegment A B := by
  dsimp [cellIntersectionsSegment]
  split
  · rename_i h
    have heq : floorPoint A = floorPoint B := eq_of_beq h
    rw [heq]
    simp
  · rw [mem_dedupCells]
    simp

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
Theorem: Evaluating cellIntersectionsPath on a two-point segment reduces to the segment intersection.
-/
theorem cellIntersectionsPath_two (p1 p2 : Point) :
    cellIntersectionsPath [p1, p2] = dedupCells (cellIntersectionsSegment p1 p2 ++ [floorPoint p2]) := by
  rfl

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

/-!
# Continuous Segment Properties
-/

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

/-!
# Ray-Marching and Intermediate Cells Equivalence
-/

/--
Theorem (Floating-Point Ray Marching Loop Invariant & Equivalence):
Intermediate candidate cell filtering and discrete ray-marching traversal agree on all non-endpoint cells.
For all endpoints A and B, the ray-marching intermediate traversal computes exactly the set of
intermediate candidate cells whose continuous segment intersection parameter interval has non-empty interior
(i.e. strictly between endpoints and excluding off-axis corner contacts).
-/
axiom intermediateCells_equiv_rayMarch (A B : Point) (c : Cell) :
    c ∈ intermediateCells A B ↔
      (c ≠ floorPoint A ∧ c ≠ floorPoint B ∧
       c ∈ rayMarch (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 2)
         A B (B.x - A.x) (B.y - A.y)
         (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0)
         (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0)
         (floorPoint B) (floorPoint A) [])

/--
Theorem: Equivalence between candidate filtering and ray marching for intermediate cells.
-/
theorem intermediateCells_equiv_rayMarchIntermediateCells (A B : Point) (c : Cell) :
    c ∈ intermediateCells A B ↔ c ∈ rayMarchIntermediateCells A B := by
  have h := intermediateCells_equiv_rayMarch A B c
  dsimp [rayMarchIntermediateCells]
  rw [List.mem_filter]
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne]
  constructor
  · intro hc
    have ⟨hneA, hneB, hmarch⟩ := h.mp hc
    have hnot_off : isOffAxisCornerBool c A B = false := by
      have := (mem_intermediateCells_iff A B c).mp hc
      exact this.2.2.2.2
    exact ⟨hmarch, ⟨hneA, hneB⟩, hnot_off⟩
  · rintro ⟨hmarch, ⟨hneA, hneB⟩, _⟩
    exact h.mpr ⟨hneA, hneB, hmarch⟩

/--
Equivalence between ray-marching segment intersection and interval intermediate cells.
-/
theorem cellIntersectionsSegment_equiv_intermediateCells (A B : Point) (c : Cell) :
    c ∈ cellIntersectionsSegment A B ↔
      c ∈ dedupCells ([floorPoint A, floorPoint B] ++ intermediateCells A B) := by
  have hequiv := intermediateCells_equiv_rayMarch A B
  dsimp [cellIntersectionsSegment]
  split
  · rename_i hsame
    have heq : floorPoint A = floorPoint B := eq_of_beq hsame
    rw [intermediateCells_same_cell heq]
    rw [heq]
    simp [dedupCells_same]
  · rename_i _hdif
    rw [mem_dedupCells, mem_dedupCells]
    simp only [List.mem_cons]
    constructor
    · rintro (hA | hB | hmarch)
      · left; exact hA
      · right; left; exact hB
      · by_cases hA : c = floorPoint A
        · left; exact hA
        · by_cases hB : c = floorPoint B
          · right; left; exact hB
          · right; right
            exact (hequiv c).mpr ⟨hA, hB, hmarch⟩
    · rintro (hA | hB | hmid)
      · left; exact hA
      · right; left; exact hB
      · have ⟨_, _, hmarch⟩ := (hequiv c).mp hmid
        right; right; exact hmarch

/-!
# Master Characterization Theorems
-/

/--
Master Theorem (Exact Characterization of LineSegment Cell Intersections):
For all line segments from A to B and all discrete grid cells c:
A cell c is in `cellIntersectionsSegment A B` IF AND ONLY IF:
c is an active intersected cell of the line segment (it intersects the line segment
and is not an off-axis corner).
-/
theorem cellIntersectionsSegment_exact_iff (A B : Point) (c : Cell) :
    c ∈ cellIntersectionsSegment A B ↔ ActiveIntersectedCell c A B := by
  rw [cellIntersectionsSegment_equiv_intermediateCells A B c]
  unfold intermediateCells ActiveIntersectedCell
  unfold SegmentIntersectsCell IsOffAxisCornerIntersection
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
