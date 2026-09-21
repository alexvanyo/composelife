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
Ray marching loop that steps across grid boundary lines until reaching distance.
Terminates structurally over fuel (bounded by grid cell Manhattan distance).
-/
def rayMarch (fuel : Nat) (start ptEnd : Point) (distance : Float) (isWest isNorth : Float)
    (xStep yStep : Float) (tX tY : Float) (acc : List Cell) : List Cell :=
  match fuel with
  | 0 => acc
  | fuel + 1 =>
    let isCorner := tX == tY
    let nextT := if tX <= tY then tX else tY
    if nextT >= distance then
      acc
    else
      let fraction := nextT / distance
      let offsetX := start.x + (ptEnd.x - start.x) * fraction
      let offsetY := start.y + (ptEnd.y - start.y) * fraction
      if isCorner then
        let rx := roundToInt offsetX
        let ry := roundToInt offsetY
        let cellX := if isWest > 0.0 then rx - 1 else rx
        let cellY := if isNorth > 0.0 then ry - 1 else ry
        let nextTX := tX + xStep.abs
        let nextTY := tY + yStep.abs
        rayMarch fuel start ptEnd distance isWest isNorth xStep yStep nextTX nextTY (acc ++ [⟨cellX, cellY⟩])
      else
        let isX := tX < tY
        let newCells :=
          if isX then
            [⟨roundToInt offsetX, toInt offsetY.floor⟩,
             ⟨roundToInt offsetX - 1, toInt offsetY.floor⟩]
          else
            [⟨toInt offsetX.floor, roundToInt offsetY⟩,
             ⟨toInt offsetX.floor, roundToInt offsetY - 1⟩]
        let nextTX := if isX then tX + xStep.abs else tX
        let nextTY := if isX then tY else tY + yStep.abs
        rayMarch fuel start ptEnd distance isWest isNorth xStep yStep nextTX nextTY (acc ++ newCells)

/--
Computes the set of discrete grid cells intersected by the line segment from `start` to `ptEnd`.
Matches LineSegmentPath.cellIntersections in Kotlin.
-/
def cellIntersectionsSegment (start ptEnd : Point) : List Cell :=
  let startCell := floorPoint start
  let endCell := floorPoint ptEnd
  let chebyshev := chebyshevDistance startCell endCell
  let manhattan := manhattanDistance startCell endCell
  let isWest := sign (start.x - ptEnd.x)
  let isNorth := sign (start.y - ptEnd.y)
  if manhattan == 0 then
    [startCell]
  else if manhattan == 1 then
    [startCell, endCell]
  else if chebyshev == 1 then
    let maxX := if start.x > ptEnd.x then start.x else ptEnd.x
    let maxY := if start.y > ptEnd.y then start.y else ptEnd.y
    let cornerPt : Point := ⟨maxX.floor, maxY.floor⟩
    let side := sideOfLine cornerPt start ptEnd
    let combinedSign := side * isWest * isNorth
    let c1 : List Cell := if combinedSign < 0.0 then [⟨startCell.x, endCell.y⟩] else []
    let c2 : List Cell := if combinedSign > 0.0 then [⟨endCell.x, startCell.y⟩] else []
    dedupCells ([startCell, endCell] ++ c1 ++ c2)
  else
    let vx := ptEnd.x - start.x
    let vy := ptEnd.y - start.y
    let distance := (vx * vx + vy * vy).sqrt
    if distance < 1.0 then
      dedupCells [startCell, endCell]
    else
      let normX := vx / distance
      let normY := vy / distance
      let xStep := if normX != 0.0 then 1.0 / normX else 1.0 / 0.0
      let yStep := if normY != 0.0 then 1.0 / normY else 1.0 / 0.0
      let initTX :=
        if normX == 0.0 then
          1.0 / 0.0
        else
          let deltaX :=
            if isWest > 0.0 then
              let f := start.x.floor - start.x
              if f == 0.0 then -1.0 else f
            else
              let c := start.x.ceil - start.x
              if c == 0.0 then 1.0 else c
          xStep * deltaX
      let initTY :=
        if normY == 0.0 then
          1.0 / 0.0
        else
          let deltaY :=
            if isNorth > 0.0 then
              let f := start.y.floor - start.y
              if f == 0.0 then -1.0 else f
            else
              let c := start.y.ceil - start.y
              if c == 0.0 then 1.0 else c
          yStep * deltaY
      let maxSteps := manhattan + 4
      let marched := rayMarch maxSteps start ptEnd distance isWest isNorth xStep yStep initTX initTY []
      dedupCells ([startCell, endCell] ++ marched)

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
