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

import models.GeometryExtensionsModel

namespace Geometry.KotlinModel

/-- Pure mathematical specification of 2D Chebyshev-shell spiral enumeration. -/
def toRingIndexMath (x y : Int) : Int :=
  if x = 0 ∧ y = 0 then 0
  else
    let r : Int := max x.natAbs y.natAbs
    let ringMin := (2 * (r - 1) + 1) * (2 * (r - 1) + 1)
    let ringQ := 2 * r
    let ringQ1 := ringMin + ringQ
    let ringQ2 := ringQ1 + ringQ
    let ringQ3 := ringQ2 + ringQ
    if y = -r then ringMin + (x + r)
    else if x = r then ringQ1 + (y + r)
    else if y = r then ringQ2 + (r - x)
    else ringQ3 + (r - y)

/-- Signed 32-bit JVM-faithful `IntOffset.toRingIndex` model returning `none` if `check` fails. -/
def toRingIndexModel (x y : Int32) : Option Int32 :=
  if x == 0 && y == 0 then
    some 0
  else
    let ring : Int32 :=
      (maxI32UInt (absI32UInt x.toUInt32) (absI32UInt y.toUInt32)).toInt32
    let ringMin : Int32 := (2 * (ring - 1) + 1) * (2 * (ring - 1) + 1)
    let ringMax : Int32 := (2 * ring + 1) * (2 * ring + 1)
    let ringQ : Int32 := Int32.ofBitVec ((ringMax - ringMin).toBitVec.sdiv 4#32)
    let ringQ1 : Int32 := ringMin + ringQ
    let ringQ2 : Int32 := ringQ1 + ringQ
    let ringQ3 : Int32 := ringQ2 + ringQ
    if ringMax == ringQ3 + ringQ then
      if y == -ring then
        some (ringMin + (x + ring))
      else if x == ring then
        some (ringQ1 + (y + ring))
      else if y == ring then
        some (ringQ2 + (ring - x))
      else if x == -ring then
        some (ringQ3 + (ring - y))
      else
        none
    else
      none

/-- Signed 32-bit JVM-faithful inverse `toRingOffset` model parameterized by float-to-int rounding. -/
def toRingOffsetModel (d2i : Float → Int32) (idx : Int32) : Option UInt64 :=
  if idx == 0 then
    some 0
  else
    let radInt : Int32 := (16 : Int32) - (16 : Int32) * ((1 : Int32) - idx)
    let ringD : Float :=
      Float.floor ((((-4 : Int32).toFloat) + Float.sqrt radInt.toFloat) / ((8 : Int32).toFloat))
    let ring : Int32 := d2i ringD + 1
    let ringMin : Int32 := (2 * (ring - 1) + 1) * (2 * (ring - 1) + 1)
    let ringMax : Int32 := (2 * ring + 1) * (2 * ring + 1)
    let ringQ : Int32 := Int32.ofBitVec ((ringMax - ringMin).toBitVec.sdiv 4#32)
    let ringQ1 : Int32 := ringMin + ringQ
    let ringQ2 : Int32 := ringQ1 + ringQ
    let ringQ3 : Int32 := ringQ2 + ringQ
    if ringMax == ringQ3 + ringQ then
      if idx < ringQ1 then
        some (packOffset (-ring + idx - ringMin) (-ring))
      else if idx < ringQ2 then
        some (packOffset ring (-ring + idx - ringQ1))
      else if idx < ringQ3 then
        some (packOffset (ring - idx + ringQ2) ring)
      else if idx < ringMax then
        some (packOffset (-ring) (ring - idx + ringQ3))
      else
        none
    else
      none

end Geometry.KotlinModel
