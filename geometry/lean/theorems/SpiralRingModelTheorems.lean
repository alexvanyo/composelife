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

import proofs.SpiralRingModelProofs

namespace Geometry.KotlinModel

/-- Origin maps to ring index `0`. -/
theorem toRingIndex_origin : toRingIndexModel 0 0 = some 0 :=
  toRingIndex_origin_Impl

/-- No `check` assertions fail and Chebyshev shell bounds `(2r-1)^2 ≤ idx < (2r+1)^2` hold on `|x|,|y| ≤ 23169`. -/
theorem toRingIndex_noCheckFail_and_shellBounds
    (x y : Int32) (hx : x.toInt.natAbs ≤ 23169) (hy : y.toInt.natAbs ≤ 23169) :
    ∃ idx : Int32,
      toRingIndexModel x y = some idx ∧
      idx.toInt = toRingIndexMath x.toInt y.toInt ∧
      (x = 0 ∧ y = 0 → idx = 0) ∧
      (let r : Int := max x.toInt.natAbs y.toInt.natAbs
       1 ≤ r →
       (2 * (r - 1) + 1) * (2 * (r - 1) + 1) ≤ idx.toInt ∧
       idx.toInt < (2 * r + 1) * (2 * r + 1)) :=
  toRingIndex_noCheckFail_and_shellBounds_Impl x y hx hy

/-- Global injectivity of 2D spiral enumeration on `|x|,|y| ≤ 23169`. -/
theorem toRingIndex_injective
    (x1 y1 x2 y2 : Int32) (idx : Int32)
    (hx1 : x1.toInt.natAbs ≤ 23169) (hy1 : y1.toInt.natAbs ≤ 23169)
    (hx2 : x2.toInt.natAbs ≤ 23169) (hy2 : y2.toInt.natAbs ≤ 23169)
    (h1 : toRingIndexModel x1 y1 = some idx)
    (h2 : toRingIndexModel x2 y2 = some idx) :
    x1 = x2 ∧ y1 = y2 :=
  toRingIndex_injective_Impl x1 y1 x2 y2 idx hx1 hy1 hx2 hy2 h1 h2

end Geometry.KotlinModel
