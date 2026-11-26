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

import models.SerializersModel

namespace Serialization.Mutations

open Serialization.Model

/-- Non-vacuity witness: negative `Int32` values survive `packInts` / `unpackInt` round-trip. -/
theorem packInts_negative_nonvacuous :
    unpackInt1 (packInts (-42) (-7)) = -42 ∧ unpackInt2 (packInts (-42) (-7)) = -7 := by
  decide +kernel

/-- Mutant 1: omitting the `0xFFFFFFFF` mask corrupts the high 32 bits when `y < 0` due to sign-extension. -/
def mutantPackIntsNoMask (x y : Int32) : UInt64 :=
  (x.toInt64.toUInt64 <<< 32) ||| y.toInt64.toUInt64

theorem mutantPackIntsNoMask_violates_roundtrip :
    unpackInt1 (mutantPackIntsNoMask 5 (-1)) ≠ 5 := by
  decide +kernel

/-- Mutant 2: swapping `top` and `right` in `RectSerializer` violates `rect_roundtrip`. -/
def mutantSerializeRectSwapped (r : RectModel) : Array Float32 :=
  #[r.left, r.right, r.top, r.bottom]

theorem mutantSerializeRectSwapped_violates_roundtrip :
    let r : RectModel := { left := 1.0, top := 2.0, right := 3.0, bottom := 4.0 }
    deserializeRect (mutantSerializeRectSwapped r) ≠ some r := by
  decide +kernel

end Serialization.Mutations
