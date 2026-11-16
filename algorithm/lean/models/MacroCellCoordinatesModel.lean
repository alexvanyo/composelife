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

import Algorithm.Basic
import Algorithm.MacroCell
import AlgorithmDefs

namespace Algorithm.KotlinModel

/-!
# Standalone Mathematical Model of Hand-Written `MacroCellCoordinates.kt`

Models `cellToLeafBit` (with `Option` failure for out-of-range coordinates),
`coordinatesToLeaf`, `leafToCoordinates`, and `coordinatesToLevel4` over
32-bit `Int32 × Int32` (`IntOffset`) coordinate lists and 64-bit Morton leaves.
-/

def cellToLeafBitModel (x y : Int32) : Option UInt32 :=
  if 0 ≤ x.toInt ∧ x.toInt < 8 ∧ 0 ≤ y.toInt ∧ y.toInt < 8 then
    some (Algorithm.cellToLeafBitUInt x.toUInt32 y.toUInt32)
  else
    none

def coordinatesToLeafModel (coords : List (Int32 × Int32)) (ox oy : Int32) : UInt64 :=
  coords.foldl
    (fun acc p =>
      let dx := p.1 - ox
      let dy := p.2 - oy
      match cellToLeafBitModel dx dy with
      | some bit => acc ||| ((1 : UInt64) <<< bit.toUInt64)
      | none => acc)
    0

def leafToCoordinatesModel (leaf : UInt64) (ox oy : Int32) : List (Int32 × Int32) :=
  if leaf == 0 then []
  else
    (List.range 8).flatMap fun y =>
      (List.range 8).filterMap fun x =>
        let bit := Algorithm.cellToLeafBitUInt (UInt32.ofNat x) (UInt32.ofNat y)
        if ((leaf >>> bit.toUInt64) &&& 1) != 0 then
          some (Int32.ofInt (x : Int) + ox, Int32.ofInt (y : Int) + oy)
        else
          none

structure Level4Quads where
  nw : UInt64
  ne : UInt64
  sw : UInt64
  se : UInt64
  deriving DecidableEq, Repr

def coordinatesToLevel4Model (coords : List (Int32 × Int32)) (ox oy : Int32) : Level4Quads :=
  { nw := coordinatesToLeafModel coords ox oy
  , ne := coordinatesToLeafModel coords (ox + 8) oy
  , sw := coordinatesToLeafModel coords ox (oy + 8)
  , se := coordinatesToLeafModel coords (ox + 8) (oy + 8) }

end Algorithm.KotlinModel
