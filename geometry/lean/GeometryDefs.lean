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

import models.Basic
import Geometry.LineSegment
import models.FloatModel

namespace Geometry

open FloatLib.Floats

/--
Determines the next cell transition in ray-marching via exact coordinate crossings.
-/
def rayMarchStep (start _ptEnd : Point) (dx dy : ℚ) (stepX stepY : ℤ) (c : Cell) : Cell × Bool :=
  let xb : ℚ := if stepX > 0 then ofInt (c.x + 1) else ofInt c.x
  let yb : ℚ := if stepY > 0 then ofInt (c.y + 1) else ofInt c.y
  let absDx := if dx >= 0 then dx else -dx
  let absDy := if dy >= 0 then dy else -dy
  if stepX == 0 then
    let remY := if yb >= start.y then yb - start.y else start.y - yb
    if remY >= absDy then (c, true)
    else (⟨c.x, c.y + stepY⟩, false)
  else if stepY == 0 then
    let remX := if xb >= start.x then xb - start.x else start.x - xb
    if remX >= absDx then (c, true)
    else (⟨c.x + stepX, c.y⟩, false)
  else
    let remX := if xb >= start.x then xb - start.x else start.x - xb
    let remY := if yb >= start.y then yb - start.y else start.y - yb
    let crossX := remX * absDy
    let crossY := remY * absDx
    let limitCross := absDx * absDy
    if min crossX crossY >= limitCross then
      (c, true)
    else if crossX < crossY then
      (⟨c.x + stepX, c.y⟩, false)
    else if crossY < crossX then
      (⟨c.x, c.y + stepY⟩, false)
    else
      (⟨c.x + stepX, c.y + stepY⟩, false)

/--
Ray-marches from `startCell` towards `endCell`, stepping cell-by-cell in O(W + H) time.
-/
def rayMarch (fuel : ℕ) (start ptEnd : Point) (dx dy : ℚ) (stepX stepY : ℤ)
    (endCell : Cell) (current : Cell) (acc : List Cell) : List Cell :=
  match fuel with
  | 0 => acc
  | fuel + 1 =>
    if current == endCell then acc
    else
      let (nextCell, done) := rayMarchStep start ptEnd dx dy stepX stepY current
      if done then acc
      else rayMarch fuel start ptEnd dx dy stepX stepY endCell nextCell (acc ++ [nextCell])

/--
Computes the set of discrete grid cells intersected by the line segment from `A` to `B`.
Matches `cellIntersections(start, end)` in Kotlin's LineSegment.kt.
-/
def cellIntersectionsSegment (A B : Point) : List Cell :=
  let startCell := floorPoint A
  let endCell := floorPoint B
  if startCell == endCell then
    [startCell]
  else
    let dx := B.x - A.x
    let dy := B.y - A.y
    let stepX : ℤ := if dx > 0 then 1 else if dx < 0 then -1 else 0
    let stepY : ℤ := if dy > 0 then 1 else if dy < 0 then -1 else 0
    let maxSteps := (endCell.x - startCell.x).natAbs + (endCell.y - startCell.y).natAbs + 2
    dedupCells ([startCell, endCell] ++ rayMarch maxSteps A B dx dy stepX stepY endCell startCell [])

/--
Computes all grid cells intersected by a polyline path with at least one point.
Matches `cellIntersections(points)` in Kotlin's LineSegment.kt.
-/
def cellIntersectionsPath (points : List Point) : List Cell :=
  match points with
  | [] => []
  | [p] => [floorPoint p]
  | p1 :: p2 :: rest =>
    let firstSeg := cellIntersectionsSegment p1 p2
    let restSegs := cellIntersectionsPath (p2 :: rest)
    dedupCells (firstSeg ++ restSegs)

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
A cell touches the closed line segment if some continuous point on the segment
lies within the closed unit square [c.x, c.x + 1] × [c.y, c.y + 1].
-/
def CellTouchesSegment (c : Cell) (A B : Point) : Prop :=
  ∃ p : Point, PointOnSegment p A B ∧
    ofInt c.x ≤ p.x ∧ p.x ≤ ofInt (c.x + 1) ∧
    ofInt c.y ≤ p.y ∧ p.y ≤ ofInt (c.y + 1)

/--
A cell's open interior in the continuous 2D plane: (c.x, c.x + 1) × (c.y, c.y + 1).
-/
def InInteriorCell (c : Cell) (p : Point) : Prop :=
  ofInt c.x < p.x ∧ p.x < ofInt (c.x + 1) ∧
  ofInt c.y < p.y ∧ p.y < ofInt (c.y + 1)

/--
The segment crosses cell `c` if some point of the segment lies in the open interior of `c`.

This is the completeness criterion for cell intersections. Cells whose closed square the segment
only touches, along an edge or at a corner, may or may not be reported: a segment through a
lattice point touches up to four cells there, and an algorithm should report only the cells it
passes through.
-/
def CellCrossedBySegment (c : Cell) (A B : Point) : Prop :=
  ∃ p : Point, PointOnSegment p A B ∧ InInteriorCell c p

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
-- Float Error Bounds and Coordinate Bounds
-- =========================================================================

def eps64 : ℚ := 1 / (2^53)

/--
Cross-product relative error bound for ray marching.
Tightly bounds double-precision coordinate differences and cross products:
(1 + eps64)^3 - 1.
Numerically approximately 3.33067e-16, strictly derived from machine epsilon.
-/
def epsRayMarch : ℚ := (1 + eps64)^3 - 1

/--
Main coordinate magnitude bound as a natural number for global Hausdorff distance verification.
2147483645 (2^31 - 3) is the sharp theoretical integer upper bound where grid cell boundary
coordinates (up to M + 2) fit within the signed 32-bit integer range [-2^31, 2^31 - 1] in Kotlin and Lean.
-/
def mainCoordBoundNat : ℕ := 2147483645

/--
Main coordinate magnitude bound for geometry verification ([-2147483645, 2147483645]²).
-/
def mainCoordBound : ℚ := mainCoordBoundNat

/--
Maximum coordinate difference between two points bounded by `mainCoordBound` as a natural number.
-/
def maxCoordDeltaNat : ℕ := 2 * mainCoordBoundNat

/--
Maximum coordinate difference between two points bounded by `mainCoordBound`.
-/
def maxCoordDelta : ℚ := maxCoordDeltaNat

/--
Maximum distance from an endpoint to any evaluated cell boundary line as a natural number.
-/
def maxCellBoundaryDistanceNat : ℕ := 2 * mainCoordBoundNat + 2

/--
Maximum distance from an endpoint to any evaluated cell boundary line.
-/
def maxCellBoundaryDistance : ℚ := maxCellBoundaryDistanceNat

def inCoordBounds (M : ℚ) (A B : Point) : Prop :=
  |A.x| ≤ M ∧ |A.y| ≤ M ∧ |B.x| ≤ M ∧ |B.y| ≤ M

-- =========================================================================
-- Hausdorff Metric and Step Classification
-- =========================================================================

/--
A list of cells with no gaps: consecutive cells are equal or neighbors (king moves), so the cells
of a line drawn through the list form one connected stroke.
-/
def CellPathConnected : List Cell → Prop
  | a :: b :: rest => chebyshevDistance a b ≤ 1 ∧ CellPathConnected (b :: rest)
  | _ => True

def cellHausdorffDistanceLe (cells1 cells2 : List Cell) (d : Nat) : Prop :=
  (∀ c1 ∈ cells1, ∃ c2 ∈ cells2, chebyshevDistance c1 c2 ≤ d) ∧
  (∀ c2 ∈ cells2, ∃ c1 ∈ cells1, chebyshevDistance c1 c2 ≤ d)

-- =========================================================================
-- Finite Coordinates and Paths
-- =========================================================================

def Point32.isFinite (p : Point32) : Prop :=
  binary32IsFinite p.x = true ∧ binary32IsFinite p.y = true

def pointsToRational (pts : List Point32) : List Point :=
  pts.map Point32.toPoint

def AllFinite (pts : List Point32) : Prop :=
  ∀ p ∈ pts, p.isFinite

-- =========================================================================
-- Model Refinement Precondition (Pattern B)
-- =========================================================================

/--
Converts an Array of Int32 coordinates from rayMarchSegmentCoords to a List of discrete Cells.
-/
def toCells (arr : Array (Int32 × Int32)) : List Cell :=
  arr.toList.map (fun (x, y) => ⟨x.toInt, y.toInt⟩)

/--
Coordinate bound under which the compiled ray march is proven to refine the float model.

Within it, every cell the march can visit, its step budget, and every intermediate `Int32` and
`Float` value stay far from overflow. It covers any drawing on a screen by many orders of magnitude.
-/
def compiledCoordBound : ℚ := 2 ^ 28

/--
Precondition for the compiled ray march `rayMarchSegmentCoords` to refine the float model
`cellIntersectionsSegmentFloat A B`:
1. The endpoints `A` and `B` are finite and within `compiledCoordBound`.
2. The `Float` arguments are the binary64 widenings of the endpoint coordinates, which is what
   `cellIntersections` in `LineSegment.kt` passes (`Offset.x.toDouble()`, an exact widening).
3. `(cx, cy)` and `(ex', ey')` are the floored endpoint cells.
-/
structure InRange (A B : Point32) (sx sy ex ey : Float) (cx cy ex' ey' : Int32) : Prop where
  h_finite : A.isFinite ∧ B.isFinite
  h_bound : inCoordBounds compiledCoordBound A.toPoint B.toPoint
  h_widen : FloatLib.Floats.ExecFloat.Binary.ofFloat sx = widen32To64 A.x ∧
    FloatLib.Floats.ExecFloat.Binary.ofFloat sy = widen32To64 A.y ∧
    FloatLib.Floats.ExecFloat.Binary.ofFloat ex = widen32To64 B.x ∧
    FloatLib.Floats.ExecFloat.Binary.ofFloat ey = widen32To64 B.y
  h_start : ⟨cx.toInt, cy.toInt⟩ = floorPoint32 A
  h_end : ⟨ex'.toInt, ey'.toInt⟩ = floorPoint32 B

/--
The arguments of one call of the compiled ray march `rayMarchSegmentCoords`, as made by `cellIntersections` in
`LineSegment.kt` for one segment of a polyline.
-/
structure SegmentCall where
  sx : Float
  sy : Float
  ex : Float
  ey : Float
  cx : Int32
  cy : Int32
  ex' : Int32
  ey' : Int32

/--
The cells `cellIntersections(points)` in `LineSegment.kt` collects for a polyline of at least two points: the
cells returned by the compiled ray march for each consecutive segment.
-/
def compiledPathCells (calls : List SegmentCall) : List Cell :=
  calls.flatMap fun k => toCells (rayMarchSegmentCoords k.sx k.sy k.ex k.ey k.cx k.cy k.ex' k.ey')

/--
`calls` are the compiled ray march calls for the consecutive segments of the polyline `points`, one per
segment, each satisfying `InRange` for its segment.
-/
def PathInRange : List Point32 → List SegmentCall → Prop
  | [_], [] => True
  | p1 :: p2 :: rest, k :: ks =>
    InRange p1 p2 k.sx k.sy k.ex k.ey k.cx k.cy k.ex' k.ey' ∧ PathInRange (p2 :: rest) ks
  | _, _ => False

end Geometry

