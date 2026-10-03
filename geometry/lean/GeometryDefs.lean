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


namespace Geometry

open FloatLib.Floats

-- =========================================================================
-- Continuous Intervals, Bounding Boxes, and Cell Intersections
-- =========================================================================

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
def cellIntersectionInterval (c : Cell) (A B : Point) : Option (ℚ × ℚ) :=
  let dx := B.x - A.x
  let dy := B.y - A.y
  let cx0 := ofInt c.x
  let cx1 := ofInt (c.x + 1)
  let cy0 := ofInt c.y
  let cy1 := ofInt (c.y + 1)
  let (tx0, tx1) :=
    if dx == 0 then
      if A.x < cx0 || A.x > cx1 then (1, 0) else (0, 1)
    else if dx > 0 then
      ((cx0 - A.x) / dx, (cx1 - A.x) / dx)
    else
      ((cx1 - A.x) / dx, (cx0 - A.x) / dx)
  let (ty0, ty1) :=
    if dy == 0 then
      if A.y < cy0 || A.y > cy1 then (1, 0) else (0, 1)
    else if dy > 0 then
      ((cy0 - A.y) / dy, (cy1 - A.y) / dy)
    else
      ((cy1 - A.y) / dy, (cy0 - A.y) / dy)
  let tEnter := max 0 (max tx0 ty0)
  let tExit := min 1 (min tx1 ty1)
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
  let stepX : ℤ := if dx > 0 then 1 else if dx < 0 then -1 else 0
  let stepY : ℤ := if dy > 0 then 1 else if dy < 0 then -1 else 0
  let maxSteps := (endCell.x - startCell.x).natAbs + (endCell.y - startCell.y).natAbs + 2
  (rayMarch maxSteps A B dx dy stepX stepY endCell startCell []).filter (fun c =>
    (c != startCell) && (c != endCell) && !isOffAxisCornerBool c A B)

/--
Continuous segment membership: point `p` lies on the directed line segment between `A` and `B`.
-/
inductive PointOnSegment (p A B : Point) : Prop where
  | start : p = A → PointOnSegment p A B
  | ptEnd : p = B → PointOnSegment p A B
  | interior (t : ℚ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
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
A cell touches the closed line segment between A and B.
-/
def SegmentIntersectsCell (c : Cell) (A B : Point) : Prop :=
  c = floorPoint A ∨ c = floorPoint B ∨ (c ∈ candidateCells A B ∧ segmentIntersectsCellBool c A B = true)

/--
A cell has an off-axis corner intersection with the segment between A and B.
-/
def IsOffAxisCornerIntersection (c : Cell) (A B : Point) : Prop :=
  c ≠ floorPoint A ∧ c ≠ floorPoint B ∧ isOffAxisCornerBool c A B = true

/--
A cell is an active intersected cell of segment AB:
it intersects the segment and is NOT an off-axis corner intersection.
-/
def ActiveIntersectedCell (c : Cell) (A B : Point) : Prop :=
  SegmentIntersectsCell c A B ∧ ¬ IsOffAxisCornerIntersection c A B

-- =========================================================================
-- Float Error Bounds, Coordinates, and Clearance
-- =========================================================================

def eps32 : ℚ := 1 / (2^24)

def eps64 : ℚ := 1 / (2^53)

def inCoordBounds (M : ℚ) (A B : Point) : Prop :=
  |A.x| ≤ M ∧ |A.y| ≤ M ∧ |B.x| ≤ M ∧ |B.y| ≤ M

def gammaBound (M : ℚ) : ℚ :=
  eps32 * (8 * M * M + 8 * M)

def idealCrossCorner (A B : Point) (xb yb : ℚ) : ℚ :=
  let dx := B.x - A.x
  let dy := B.y - A.y
  let absDx := if dx ≥ 0 then dx else -dx
  let absDy := if dy ≥ 0 then dy else -dy
  let remX := if xb ≥ A.x then xb - A.x else A.x - xb
  let remY := if yb ≥ A.y then yb - A.y else A.y - yb
  remX * absDy - remY * absDx

def HasCornerClearance (A B : Point) (M : ℚ) : Prop :=
  (∀ xb yb : ℤ,
    |idealCrossCorner A B (ofInt xb) (ofInt yb)| > gammaBound M ∨
    idealCrossCorner A B (ofInt xb) (ofInt yb) = 0) ∧
  (∀ (A' B' : Point32), A'.toPoint = A → B'.toPoint = B →
    (if B'.x - A'.x > 0.0 then 1 else if B'.x - A'.x < 0.0 then -1 else 0) =
      (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0) ∧
    (if B'.y - A'.y > 0.0 then 1 else if B'.y - A'.y < 0.0 then -1 else 0) =
      (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0) ∧
    (∀ c, rayMarchStepFloat A' (B'.x - A'.x) (B'.y - A'.y)
      (if B'.x - A'.x > 0.0 then 1 else if B'.x - A'.x < 0.0 then -1 else 0)
      (if B'.y - A'.y > 0.0 then 1 else if B'.y - A'.y < 0.0 then -1 else 0) c =
      rayMarchStep A B (B.x - A.x) (B.y - A.y)
        (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0)
        (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0) c))


-- =========================================================================
-- Hausdorff Metric and Step Classification
-- =========================================================================

def cellHausdorffDistanceLe (cells1 cells2 : List Cell) (d : Nat) : Prop :=
  (∀ c1 ∈ cells1, ∃ c2 ∈ cells2, chebyshevDistance c1 c2 ≤ d) ∧
  (∀ c2 ∈ cells2, ∃ c1 ∈ cells1, chebyshevDistance c1 c2 ≤ d)

def CellStepRel (stepX stepY : ℤ) (c1 c2 : Cell) : Prop :=
  c1 = c2 ∨
  c1 = ⟨c2.x + stepX, c2.y - stepY⟩ ∨
  c1 = ⟨c2.x - stepX, c2.y + stepY⟩

def StepClassification (start : Point32) (ptEnd : Point) (dx dy : Binary32) (dxQ dyQ : ℚ)
    (stepX stepY : ℤ) (endCell c : Cell) : Prop :=
  ( ( (rayMarchStepFloat start dx dy stepX stepY c).1 = (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 ∧
      (rayMarchStepFloat start dx dy stepX stepY c).2 = (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).2 ) ∨
    ( (c == endCell) = false ∧
      (⟨c.x + stepX, c.y⟩ == endCell) = false ∧
      (⟨c.x, c.y + stepY⟩ == endCell) = false ∧
      (rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x + stepX, c.y⟩ ∧
      (rayMarchStepFloat start dx dy stepX stepY c).2 = false ∧
      (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 = ⟨c.x, c.y + stepY⟩ ∧
      (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).2 = false ∧
      (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y⟩).1 = ⟨c.x + stepX, c.y + stepY⟩ ∧
      (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y⟩).2 = false ∧
      (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x, c.y + stepY⟩).1 = ⟨c.x + stepX, c.y + stepY⟩ ∧
      (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x, c.y + stepY⟩).2 = false ) ∨
    ( (c == endCell) = false ∧
      (⟨c.x, c.y + stepY⟩ == endCell) = false ∧
      (⟨c.x + stepX, c.y⟩ == endCell) = false ∧
      (rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x, c.y + stepY⟩ ∧
      (rayMarchStepFloat start dx dy stepX stepY c).2 = false ∧
      (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 = ⟨c.x + stepX, c.y⟩ ∧
      (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).2 = false ∧
      (rayMarchStepFloat start dx dy stepX stepY ⟨c.x, c.y + stepY⟩).1 = ⟨c.x + stepX, c.y + stepY⟩ ∧
      (rayMarchStepFloat start dx dy stepX stepY ⟨c.x, c.y + stepY⟩).2 = false ∧
      (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y⟩).1 = ⟨c.x + stepX, c.y + stepY⟩ ∧
      (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y⟩).2 = false ) ∨
    ( (c == endCell) = true ∨ (rayMarchStepFloat start dx dy stepX stepY c).2 = true ∨ (rayMarchStepFloat start dx dy stepX stepY c).1 = endCell ) ) ∧
  ( ( (rayMarchStepFloat start dx dy stepX stepY c).1 = (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 ∧
      (rayMarchStepFloat start dx dy stepX stepY c).2 = (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).2 ) ∨
    ( (c == endCell) = false ∧
      (⟨c.x + stepX, c.y⟩ == endCell) = false ∧
      (⟨c.x, c.y + stepY⟩ == endCell) = false ∧
      (rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x + stepX, c.y⟩ ∧
      (rayMarchStepFloat start dx dy stepX stepY c).2 = false ∧
      (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 = ⟨c.x, c.y + stepY⟩ ∧
      (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).2 = false ∧
      (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y⟩).1 = ⟨c.x + stepX, c.y + stepY⟩ ∧
      (rayMarchStepFloat start dx dy stepX stepY ⟨c.x + stepX, c.y⟩).2 = false ∧
      (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x, c.y + stepY⟩).1 = ⟨c.x + stepX, c.y + stepY⟩ ∧
      (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x, c.y + stepY⟩).2 = false ) ∨
    ( (c == endCell) = false ∧
      (⟨c.x, c.y + stepY⟩ == endCell) = false ∧
      (⟨c.x + stepX, c.y⟩ == endCell) = false ∧
      (rayMarchStepFloat start dx dy stepX stepY c).1 = ⟨c.x, c.y + stepY⟩ ∧
      (rayMarchStepFloat start dx dy stepX stepY c).2 = false ∧
      (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 = ⟨c.x + stepX, c.y⟩ ∧
      (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).2 = false ∧
      (rayMarchStepFloat start dx dy stepX stepY ⟨c.x, c.y + stepY⟩).1 = ⟨c.x + stepX, c.y + stepY⟩ ∧
      (rayMarchStepFloat start dx dy stepX stepY ⟨c.x, c.y + stepY⟩).2 = false ∧
      (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y⟩).1 = ⟨c.x + stepX, c.y + stepY⟩ ∧
      (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY ⟨c.x + stepX, c.y⟩).2 = false ) ∨
    ( (c == endCell) = true ∨ (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).2 = true ∨ (rayMarchStep start.toPoint ptEnd dxQ dyQ stepX stepY c).1 = endCell ) )


-- =========================================================================
-- Waypoints and Path Decompositions
-- =========================================================================

def Point32.isFinite (p : Point32) : Prop :=
  binary32IsFinite p.x = true ∧ binary32IsFinite p.y = true

def pointsToRational (pts : List Point32) : List Point :=
  pts.map Point32.toPoint

def AllFinite (pts : List Point32) : Prop :=
  ∀ p ∈ pts, p.isFinite

def ConsecutiveAdjacent (pts : List Point32) : Prop :=
  ∀ (i : Nat) (hi : i + 1 < pts.length),
    chebyshevDistance (floorPoint32 (pts.get ⟨i, by omega⟩))
                      (floorPoint32 (pts.get ⟨i + 1, hi⟩)) ≤ 1

def IsCellBoundaryPoint (p : Point32) : Prop :=
  (∃ k : ℤ, p.x = intToBinary32 k) ∨ (∃ k : ℤ, p.y = intToBinary32 k)

def PartitionValid (start ptEnd : Point32) (waypoints : List Point32) : Prop :=
  waypoints.head? = some start ∧
  waypoints.getLast? = some ptEnd ∧
  AllFinite waypoints ∧
  ConsecutiveAdjacent waypoints

end Geometry
