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
Matches Kotlin's Set deduplication.
-/
def dedupCells (cells : List Cell) : List Cell :=
  cells.eraseDups

/--
Determines the next cell transition in ray-marching via exact coordinate crossings.
-/
def rayMarchStep (start _ptEnd : Point) (dx dy : Rat) (stepX stepY : Int) (c : Cell) : Cell × Bool :=
  let xb : Rat := if stepX > 0 then ofInt (c.x + 1) else ofInt c.x
  let yb : Rat := if stepY > 0 then ofInt (c.y + 1) else ofInt c.y
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
def rayMarch (fuel : Nat) (start ptEnd : Point) (dx dy : Rat) (stepX stepY : Int)
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
    let stepX : Int := if dx > 0 then 1 else if dx < 0 then -1 else 0
    let stepY : Int := if dy > 0 then 1 else if dy < 0 then -1 else 0
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

end Geometry
