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

namespace Serialization.Model

/-- Bit-packing of two signed 32-bit integers into a 64-bit word (matches `androidx.compose.ui.util.packInts`). -/
def packInts (x y : Int32) : UInt64 :=
  (x.toInt64.toUInt64 <<< 32) ||| (y.toInt64.toUInt64 &&& (0xFFFFFFFF : UInt64))

/-- Unpacks the high 32 bits as a signed `Int32` (matches `androidx.compose.ui.util.unpackInt1`). -/
def unpackInt1 (v : UInt64) : Int32 :=
  (v.toInt64 >>> 32).toInt32

/-- Unpacks the low 32 bits as a signed `Int32` (matches `androidx.compose.ui.util.unpackInt2`). -/
def unpackInt2 (v : UInt64) : Int32 :=
  (v &&& (0xFFFFFFFF : UInt64)).toUInt32.toInt32

/-- Bit-packing of two IEEE-754 `Float32` values into a 64-bit word (matches `androidx.compose.ui.util.packFloats`). -/
def packFloats (x y : Float32) : UInt64 :=
  (x.toBits.toInt32.toInt64.toUInt64 <<< 32) ||| (y.toBits.toInt32.toInt64.toUInt64 &&& (0xFFFFFFFF : UInt64))

/-- Unpacks the high 32 bits as an IEEE-754 `Float32` (matches `androidx.compose.ui.util.unpackFloat1`). -/
def unpackFloat1 (v : UInt64) : Float32 :=
  Float32.ofBits (v.toInt64 >>> 32).toInt32.toUInt32

/-- Unpacks the low 32 bits as an IEEE-754 `Float32` (matches `androidx.compose.ui.util.unpackFloat2`). -/
def unpackFloat2 (v : UInt64) : Float32 :=
  Float32.ofBits (v &&& (0xFFFFFFFF : UInt64)).toUInt32

/-- Pure model of `androidx.compose.ui.geometry.Rect`. -/
structure RectModel where
  left : Float32
  top : Float32
  right : Float32
  bottom : Float32
  deriving DecidableEq, Repr, Inhabited

/-- Pure model of `kotlin.ranges.ClosedRange<Float>` (`ClosedFloatRange`). -/
structure ClosedFloatRangeModel where
  start : Float32
  endInclusive : Float32
  deriving DecidableEq, Repr, Inhabited

/-- Pure model of `RectSerializer.serialize`. -/
def serializeRect (r : RectModel) : Array Float32 :=
  #[r.left, r.top, r.right, r.bottom]

/-- Pure model of `RectSerializer.deserialize`. -/
def deserializeRect (arr : Array Float32) : Option RectModel :=
  if h : 4 ≤ arr.size then
    some { left := arr[0], top := arr[1], right := arr[2], bottom := arr[3] }
  else
    none

/-- Pure model of `ClosedFloatRangeSerializer.serialize`. -/
def serializeClosedFloatRange (r : ClosedFloatRangeModel) : UInt64 :=
  packFloats r.start r.endInclusive

/-- Pure model of `ClosedFloatRangeSerializer.deserialize`. -/
def deserializeClosedFloatRange (v : UInt64) : ClosedFloatRangeModel :=
  { start := unpackFloat1 v, endInclusive := unpackFloat2 v }

/-- Pure model of `SurrogatingSerializer.serialize`. -/
def serializeSurrogate {T S E : Type} (encodeS : S → E) (toSurr : T → S) (x : T) : E :=
  encodeS (toSurr x)

/-- Pure model of `SurrogatingSerializer.deserialize`. -/
def deserializeSurrogate {T S E : Type} (decodeS : E → S) (fromSurr : S → T) (raw : E) : T :=
  fromSurr (decodeS raw)

end Serialization.Model
