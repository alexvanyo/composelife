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
import FloatLib

namespace Geometry

open FloatLib.Floats

/--
IEEE-754 binary32 representation format from FloatLib.
-/
abbrev Binary32 := ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)

/--
IEEE-754 binary64 (Double) representation format from FloatLib.
-/
abbrev Binary64 := ExecFloat.Binary (exponentBits := 11) (fractionBits := 52)

/--
Converts a Binary32 value to an exact rational number (ℚ).
Returns 0 for non-finite values (NaN, infinity).
-/
def binary32ToRat (b : Binary32) : ℚ :=
  (ExecFloat.Binary.toRat? b).getD 0

/--
Converts a Binary32 value to a 64-bit Float for evaluation.
-/
def binary32ToFloat (b : Binary32) : Float :=
  (Float32.ofBits (UInt32.ofNat (ExecFloat.Binary.toNatBits b))).toFloat

/--
Converts a Float32 to Binary32 preserving IEEE-754 bit representations.
-/
def float32ToBinary32 (f : Float32) : Binary32 :=
  ExecFloat.Binary.ofNatBits f.toBits.toNat

/--
Floors a Binary32 value to an Int, matching Kotlin's kotlin.math.floor.
-/
def floorBinary32 (f : Binary32) : Int :=
  match ExecFloat.Binary.toRat? f with
  | some (q : ℚ) => Rat.floor q
  | none => 0

/--
Whether a Binary32 is finite (not NaN and not infinite).
-/
def binary32IsFinite (b : Binary32) : Bool :=
  ExecFloat.Binary.isFinite b

/--
A 2D point with IEEE-754 32-bit floating point coordinates.
Directly models Kotlin's Offset(x: Float, y: Float).
-/
structure Point32 where
  x : Binary32
  y : Binary32
  deriving Repr, Inhabited, BEq, DecidableEq

/--
Converts a 32-bit floating point point to its exact rational representation.
-/
def Point32.toPoint (p : Point32) : Point :=
  ⟨binary32ToRat p.x, binary32ToRat p.y⟩


/--
Floors a continuous Point32 into discrete Cell coordinates.
-/
def floorPoint32 (p : Point32) : Cell :=
  ⟨floorBinary32 p.x, floorBinary32 p.y⟩

/--
Converts an integer cell coordinate to a 32-bit float value.
-/
def intToBinary32 (n : Int) : Binary32 :=
  ExecFloat.Binary.ofFloat32 (Float32.ofInt n)

/--
Widening cast from 32-bit Binary32 to 64-bit Binary64 (Double).
-/
def widen32To64 (x : Binary32) : Binary64 :=
  (x.cast (target := Binary64)).value?.getD (0.0 : Binary64)

/--
Determines the next cell transition in ray-marching using 32-bit floating point inputs
and 64-bit Double widening for intermediate cross products, matching `cellIntersections` in `LineSegment.kt`.
-/
def rayMarchStepFloat (start : Point32) (dx dy : Binary32) (stepX stepY : Int) (c : Cell) : Cell × Bool :=
  let currentX := if stepX > 0 then c.x + 1 else c.x
  let currentY := if stepY > 0 then c.y + 1 else c.y
  let xb : Binary64 := widen32To64 (intToBinary32 currentX)
  let yb : Binary64 := widen32To64 (intToBinary32 currentY)
  let startX : Binary64 := widen32To64 start.x
  let startY : Binary64 := widen32To64 start.y
  let absDx : Binary64 := ExecFloat.Binary.abs (widen32To64 dx)
  let absDy : Binary64 := ExecFloat.Binary.abs (widen32To64 dy)
  if stepX == 0 then
    let remY : Binary64 := ExecFloat.Binary.abs (yb - startY)
    if remY >= absDy then (c, true)
    else (⟨c.x, c.y + stepY⟩, false)
  else if stepY == 0 then
    let remX : Binary64 := ExecFloat.Binary.abs (xb - startX)
    if remX >= absDx then (c, true)
    else (⟨c.x + stepX, c.y⟩, false)
  else
    let remX : Binary64 := ExecFloat.Binary.abs (xb - startX)
    let remY : Binary64 := ExecFloat.Binary.abs (yb - startY)
    let crossX : Binary64 := remX * absDy
    let crossY : Binary64 := remY * absDx
    let limitCross : Binary64 := absDx * absDy
    if min crossX crossY >= limitCross then
      (c, true)
    else if crossX < crossY then
      (⟨c.x + stepX, c.y⟩, false)
    else if crossY < crossX then
      (⟨c.x, c.y + stepY⟩, false)
    else
      (⟨c.x + stepX, c.y + stepY⟩, false)

/--
Ray-marches from `startCell` towards `endCell` using floating-point operations.
Matches the while loop in `LineSegment.kt`.
-/
def rayMarchFloat (fuel : Nat) (start : Point32) (dx dy : Binary32) (stepX stepY : Int)
    (endCell : Cell) (current : Cell) (acc : List Cell) : List Cell :=
  match fuel with
  | 0 => acc
  | fuel + 1 =>
    if current == endCell then acc
    else
      let (nextCell, done) := rayMarchStepFloat start dx dy stepX stepY current
      if done then acc
      else rayMarchFloat fuel start dx dy stepX stepY endCell nextCell (acc ++ [nextCell])

/--
Computes the set of discrete grid cells intersected by the line segment from `A` to `B`
using the 32-bit floating point raymarching algorithm.
Directly corresponds to `cellIntersections(start, end)` in Kotlin's LineSegment.kt.
-/
def cellIntersectionsSegmentFloat (A B : Point32) : List Cell :=
  let startCell := floorPoint32 A
  let endCell := floorPoint32 B
  if startCell == endCell then
    [startCell]
  else
    let dx : Binary32 := B.x - A.x
    let dy : Binary32 := B.y - A.y
    let stepX : Int := if dx > 0.0 then 1 else if dx < 0.0 then -1 else 0
    let stepY : Int := if dy > 0.0 then 1 else if dy < 0.0 then -1 else 0
    let maxSteps := (endCell.x - startCell.x).natAbs + (endCell.y - startCell.y).natAbs + 2
    dedupCells ([startCell, endCell] ++ rayMarchFloat maxSteps A dx dy stepX stepY endCell startCell [])

/--
Computes all grid cells intersected by a polyline path with 32-bit floating point points.
Matches `cellIntersections(points)` in Kotlin's LineSegment.kt.
-/
def cellIntersectionsPathFloat (points : List Point32) : List Cell :=
  match points with
  | [] => []
  | [p] => [floorPoint32 p]
  | p1 :: p2 :: rest =>
    let firstSeg := cellIntersectionsSegmentFloat p1 p2
    let restSegs := cellIntersectionsPathFloat (p2 :: rest)
    dedupCells (firstSeg ++ restSegs)

end Geometry
