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

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

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

def absFloat (x : Float) : Float :=
  if x < 0.0 then -x else x

def absInt (x : Int32) : UInt32 :=
  if x < 0 then (-x).toUInt32 else x.toUInt32

@[export geometry_ray_march]
partial def rayMarchLoop (fuel : UInt32) (startX startY : Float) (dx dy absDx absDy : Float)
    (stepX stepY : Int32) (endX endY : Int32) (curX curY : Int32) (acc : Array (Int32 × Int32)) : Array (Int32 × Int32) :=
  if fuel == 0 then acc
  else if curX == endX && curY == endY then acc
  else
    let xb : Float := if stepX > 0 then (curX + 1).toFloat else curX.toFloat
    let yb : Float := if stepY > 0 then (curY + 1).toFloat else curY.toFloat
    if stepX == 0 then
      let remY := absFloat (yb - startY)
      if remY >= absDy then acc
      else
        let nextY := curY + stepY
        rayMarchLoop (fuel - 1) startX startY dx dy absDx absDy stepX stepY endX endY curX nextY (acc.push (curX, nextY))
    else if stepY == 0 then
      let remX := absFloat (xb - startX)
      if remX >= absDx then acc
      else
        let nextX := curX + stepX
        rayMarchLoop (fuel - 1) startX startY dx dy absDx absDy stepX stepY endX endY nextX curY (acc.push (nextX, curY))
    else
      let remX := absFloat (xb - startX)
      let remY := absFloat (yb - startY)
      let crossX := remX * absDy
      let crossY := remY * absDx
      let limitCross := absDx * absDy
      let minCross := if crossX < crossY then crossX else crossY
      if minCross >= limitCross then acc
      else
        let nextX := if crossX <= crossY then curX + stepX else curX
        let nextY := if crossY <= crossX then curY + stepY else curY
        rayMarchLoop (fuel - 1) startX startY dx dy absDx absDy stepX stepY endX endY nextX nextY (acc.push (nextX, nextY))

@[export geometry_ray_march_segment]
def rayMarchSegmentCoords (startX startY endX endY : Float) (startCellX startCellY endCellX endCellY : Int32) : Array (Int32 × Int32) :=
  if startCellX == endCellX && startCellY == endCellY then
    #[(startCellX, startCellY)]
  else
    let dx := endX - startX
    let dy := endY - startY
    let stepX : Int32 := if dx > 0.0 then 1 else if dx < 0.0 then -1 else 0
    let stepY : Int32 := if dy > 0.0 then 1 else if dy < 0.0 then -1 else 0
    let absDx := absFloat dx
    let absDy := absFloat dy
    let maxSteps := absInt (endCellX - startCellX) + absInt (endCellY - startCellY) + 2
    let acc := #[(startCellX, startCellY), (endCellX, endCellY)]
    rayMarchLoop maxSteps startX startY dx dy absDx absDy stepX stepY endCellX endCellY startCellX startCellY acc

end Geometry
