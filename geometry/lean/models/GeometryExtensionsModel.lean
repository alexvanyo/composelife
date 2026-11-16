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

namespace Geometry.KotlinModel

/-- Pack signed 32-bit coordinates `(x, y)` into Compose `IntOffset` `Long` representation. -/
def packOffset (x y : Int32) : UInt64 :=
  (x.toUInt32.toUInt64 <<< 32) ||| y.toUInt32.toUInt64

/-- Unpack `x` coordinate from packed `IntOffset`. -/
def offsetX (packed : UInt64) : Int32 :=
  (packed >>> 32).toUInt32.toInt32

/-- Unpack `y` coordinate from packed `IntOffset`. -/
def offsetY (packed : UInt64) : Int32 :=
  packed.toUInt32.toInt32

/-- Component-wise addition of two packed `IntOffset`s. -/
def addPackedOffset (a b : UInt64) : UInt64 :=
  packOffset (offsetX a + offsetX b) (offsetY a + offsetY b)

/-- Component-wise subtraction of two packed `IntOffset`s. -/
def subPackedOffset (a b : UInt64) : UInt64 :=
  packOffset (offsetX a - offsetX b) (offsetY a - offsetY b)

/-- Component-wise negation of a packed `IntOffset`. -/
def negPackedOffset (a : UInt64) : UInt64 :=
  packOffset (-offsetX a) (-offsetY a)

/-- Coordinate swap `(x, y) ↦ (y, x)` for symmetry proofs. -/
def swapPackedOffset (a : UInt64) : UInt64 :=
  packOffset (offsetY a) (offsetX a)

/-- Unpack `x` float coordinate from Compose packed `Offset` (`Long`). -/
def offsetFloatX (packed : UInt64) : Float32 :=
  Float32.ofBits (packed >>> 32).toUInt32

/-- Unpack `y` float coordinate from Compose packed `Offset` (`Long`). -/
def offsetFloatY (packed : UInt64) : Float32 :=
  Float32.ofBits packed.toUInt32

/-- JVM `f2i` (`Float.toInt()`) model on `Float32` via `Float`. -/
def float32ToInt32Model (x : Float32) : Int32 :=
  let d := x.toFloat
  (if d.isNaN then (0 : UInt32)
   else if d >= 2147483647.0 then 0x7FFFFFFF
   else if d <= -2147483648.0 then 0x80000000
   else if d >= 0.0 then UInt32.ofNat d.toUInt64.toNat
   else UInt32.ofNat (0x100000000 - (-d).toUInt64.toNat)).toInt32

/-- Standalone Lean model for `floor(Offset): IntOffset` in `GeometryExtensions.kt`. -/
def floorModel (packed : UInt64) : UInt64 :=
  packOffset
    (float32ToInt32Model (offsetFloatX packed).toFloat.floor.toFloat32)
    (float32ToInt32Model (offsetFloatY packed).toFloat.floor.toFloat32)

/-- `Math.signum(Float)` model matching JVM `java.lang.Math.signum(F)F`. -/
def signumFloat32 (x : Float32) : Float32 :=
  if x.isNaN || x == 0.0 then x
  else if x < 0.0 then (-1.0 : Float32)
  else (1.0 : Float32)

/-- Standalone Lean model for `Offset.sideOfLine(start, end)` in `GeometryExtensions.kt`. -/
def sideOfLineModel (point startPt endPt : UInt64) : Float32 :=
  signumFloat32
    ((offsetFloatX endPt - offsetFloatX startPt) * (offsetFloatY point - offsetFloatY startPt) -
     (offsetFloatY endPt - offsetFloatY startPt) * (offsetFloatX point - offsetFloatX startPt))

/-- Two's complement 32-bit `Math.abs(int)` model. -/
def absI32UInt (v : UInt32) : UInt32 :=
  if v.toBitVec.slt 0#32 then -v else v

/-- Two's complement 32-bit `Math.max(int, int)` model. -/
def maxI32UInt (a b : UInt32) : UInt32 :=
  if a.toBitVec.slt b.toBitVec then b else a

/-- Standalone Lean model for `IntOffset.chebyshevDistance()` in `GeometryExtensions.kt`. -/
def chebyshevDistanceModel (packed : UInt64) : UInt32 :=
  maxI32UInt (absI32UInt (offsetX packed).toUInt32) (absI32UInt (offsetY packed).toUInt32)

/-- Standalone Lean model for `IntOffset.manhattanDistance()` in `GeometryExtensions.kt`. -/
def manhattanDistanceModel (packed : UInt64) : UInt32 :=
  absI32UInt (offsetX packed).toUInt32 + absI32UInt (offsetY packed).toUInt32

/-- Standalone Lean model of `mooreNeighborOffsets` in `GeometryExtensions.kt`. -/
def mooreNeighborOffsetsModel : List (Int32 × Int32) :=
  [(-1, -1), (0, -1), (1, -1), (-1, 0), (1, 0), (-1, 1), (0, 1), (1, 1)]

/-- Standalone Lean model of `vonNeumannNeighborOffsets` in `GeometryExtensions.kt`. -/
def vonNeumannNeighborOffsetsModel : List (Int32 × Int32) :=
  [(0, -1), (-1, 0), (1, 0), (0, 1)]

/-- Standalone Lean model for `IntOffset.getMooreNeighbors()` returning packed `IntOffset` list. -/
def getMooreNeighborsModel (packed : UInt64) : List UInt64 :=
  mooreNeighborOffsetsModel.map fun (dx, dy) => addPackedOffset (packOffset dx dy) packed

/-- Standalone Lean model for `IntOffset.getVonNeumannNeighbors()` returning packed `IntOffset` list. -/
def getVonNeumannNeighborsModel (packed : UInt64) : List UInt64 :=
  vonNeumannNeighborOffsetsModel.map fun (dx, dy) => addPackedOffset (packOffset dx dy) packed

end Geometry.KotlinModel
