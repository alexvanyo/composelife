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

namespace Geometry

/--
Deduplicates a list of cells while preserving first-occurrence order.
-/
def dedupCells (cells : List Cell) : List Cell :=
  cells.eraseDups

/--
Membership in dedupCells is equivalent to membership in the original list.
-/
@[simp]
theorem mem_dedupCells (c : Cell) (cells : List Cell) : c ∈ dedupCells cells ↔ c ∈ cells :=
  List.mem_eraseDups

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
Determines the next cell transition in ray-marching via exact coordinate crossings.
-/
def rayMarchStep (start _ptEnd : Point) (dx dy : Binary32) (stepX stepY : Int) (c : Cell) : Cell × Bool :=
  let xb : Binary32 := if stepX > 0 then ofInt (c.x + 1) else ofInt c.x
  let yb : Binary32 := if stepY > 0 then ofInt (c.y + 1) else ofInt c.y
  let tx : Binary32 := if stepX != 0 then (xb - start.x) / dx else 1.0 / 0.0
  let ty : Binary32 := if stepY != 0 then (yb - start.y) / dy else 1.0 / 0.0
  if tx <= 0.0 && ty <= 0.0 then
    (⟨c.x + stepX, c.y + stepY⟩, false)
  else if tx <= 0.0 then
    (⟨c.x + stepX, c.y⟩, false)
  else if ty <= 0.0 then
    (⟨c.x, c.y + stepY⟩, false)
  else if tx < ty then
    if tx >= 1.0 then (c, true)
    else (⟨c.x + stepX, c.y⟩, false)
  else if ty < tx then
    if ty >= 1.0 then (c, true)
    else (⟨c.x, c.y + stepY⟩, false)
  else
    if tx >= 1.0 then (c, true)
    else (⟨c.x + stepX, c.y + stepY⟩, false)

/--
Ray-marches from `startCell` towards `endCell`, stepping cell-by-cell in O(W + H) time.
-/
def rayMarch (fuel : Nat) (start ptEnd : Point) (dx dy : Binary32) (stepX stepY : Int)
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
Computes the set of discrete grid cells intersected by the line segment from `A` to `B`.
Contains endpoints followed by all actively intersected intermediate cells (excluding off-axis corners).
-/
def cellIntersectionsSegment (A B : Point) : List Cell :=
  dedupCells ([floorPoint A, floorPoint B] ++ intermediateCells A B)

/--
Computes all grid cells intersected by a polyline path with at least one point.
-/
def cellIntersectionsPath (points : List Point) : List Cell :=
  match points with
  | [] => []
  | [p] => [floorPoint p]
  | p1 :: p2 :: rest =>
    let firstSeg := cellIntersectionsSegment p1 p2
    let restSegs := cellIntersectionsPath (p2 :: rest)
    dedupCells (firstSeg ++ restSegs)

end Geometry
