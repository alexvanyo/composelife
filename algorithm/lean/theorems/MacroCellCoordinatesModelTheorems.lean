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
import models.MacroCellCoordinatesModel
import models.HashLifeComputationModel
import proofs.MacroCellCoordinatesModelProofs

namespace Algorithm.KotlinModel

/-!
# Formal Theorems About Hand-Written `MacroCellCoordinates.kt` Model

Range, Morton-index bijection, injectivity, union homomorphism, and round-trip
theorems for `cellToLeafBitModel`, `coordinatesToLeafModel`, and
`leafToCoordinatesModel`, and the cells of the leaves and Level-4 nodes that
`coordinatesToLeafModel` and `coordinatesToLevel4Model` encode.
-/

theorem cellToLeafBitModel_some_iff (x y : Int32) :
    (cellToLeafBitModel x y).isSome ↔
      (0 ≤ x.toInt ∧ x.toInt < 8 ∧ 0 ≤ y.toInt ∧ y.toInt < 8) :=
  cellToLeafBitModel_some_iff_Impl x y

theorem cellToLeafBitModel_lt64 (x y : Int32) (b : UInt32)
    (h : cellToLeafBitModel x y = some b) :
    b.toNat < 64 :=
  cellToLeafBitModel_lt64_Impl x y b h

theorem cellToLeafBitModel_eq_morton (x y : Int32) (b : UInt32)
    (h : cellToLeafBitModel x y = some b) :
    b.toNat = Algorithm.mortonIndex x.toInt.toNat y.toInt.toNat :=
  cellToLeafBitModel_eq_morton_Impl x y b h

theorem cellToLeafBitModel_inj (x1 y1 x2 y2 : Int32) (b : UInt32)
    (h1 : cellToLeafBitModel x1 y1 = some b)
    (h2 : cellToLeafBitModel x2 y2 = some b) :
    x1 = x2 ∧ y1 = y2 :=
  cellToLeafBitModel_inj_Impl x1 y1 x2 y2 b h1 h2

theorem coordinatesToLeafModel_empty (ox oy : Int32) :
    coordinatesToLeafModel [] ox oy = 0 :=
  coordinatesToLeafModel_empty_Impl ox oy

theorem coordinatesToLeafModel_append (xs ys : List (Int32 × Int32)) (ox oy : Int32) :
    coordinatesToLeafModel (xs ++ ys) ox oy =
      coordinatesToLeafModel xs ox oy ||| coordinatesToLeafModel ys ox oy :=
  coordinatesToLeafModel_append_Impl xs ys ox oy

/-- `leafToCoordinates` lists exactly the cells whose Morton bit is set, offset by `(ox, oy)` (wrapping
`Int` addition, as in Kotlin). -/
theorem mem_leafToCoordinatesModel_iff (leaf : UInt64) (ox oy : Int32) (p : Int32 × Int32) :
    p ∈ leafToCoordinatesModel leaf ox oy ↔
      ∃ nx < 8, ∃ ny < 8, leaf.toBitVec.getLsbD (Algorithm.mortonIndex nx ny) = true ∧
        p = (Int32.ofInt (nx : Int) + ox, Int32.ofInt (ny : Int) + oy) :=
  mem_leafToCoordinatesModel_iff_Impl leaf ox oy p

/-- Encoding the decoded cells of a leaf gives back the leaf, for every offset. -/
theorem coordinatesToLeaf_leafToCoordinates (leaf : UInt64) (ox oy : Int32) :
    coordinatesToLeafModel (leafToCoordinatesModel leaf ox oy) ox oy = leaf :=
  coordinatesToLeaf_leafToCoordinates_Impl leaf ox oy

/-- Decoding the encoded leaf gives back exactly the coordinates that lie in the 8x8 window at `(ox, oy)`. -/
theorem leafToCoordinates_coordinatesToLeaf (coords : List (Int32 × Int32)) (ox oy : Int32)
    (p : Int32 × Int32) :
    p ∈ leafToCoordinatesModel (coordinatesToLeafModel coords ox oy) ox oy ↔
      p ∈ coords ∧ (cellToLeafBitModel (p.1 - ox) (p.2 - oy)).isSome :=
  leafToCoordinates_coordinatesToLeaf_Impl coords ox oy p

/-- Cell `(x, y)` of the leaf encoded at `(ox, oy)` is alive exactly when `(ox + x, oy + y)` is a coordinate. -/
theorem leafAt_coordinatesToLeafModel (coords : List (Int32 × Int32)) (ox oy : Int32) (x y : Int)
    (hx : 0 ≤ x ∧ x < 8) (hy : 0 ≤ y ∧ y < 8) :
    Algorithm.leafAt (coordinatesToLeafModel coords ox oy) x y =
      decide ((ox + Int32.ofInt x, oy + Int32.ofInt y) ∈ coords) :=
  leafAt_coordinatesToLeafModel_Impl coords ox oy x y hx hy

/-- Cell `(x, y)` of the 16x16 Level-4 node encoded at `(ox, oy)` is alive exactly when `(ox + x, oy + y)` is a
coordinate. -/
theorem level4CellAt_coordinatesToLevel4Model (coords : List (Int32 × Int32)) (ox oy : Int32) (x y : Int)
    (hx : 0 ≤ x ∧ x < 16) (hy : 0 ≤ y ∧ y < 16) :
    level4CellAt (coordinatesToLevel4Model coords ox oy).nw (coordinatesToLevel4Model coords ox oy).ne
        (coordinatesToLevel4Model coords ox oy).sw (coordinatesToLevel4Model coords ox oy).se x y =
      decide ((ox + Int32.ofInt x, oy + Int32.ofInt y) ∈ coords) :=
  level4CellAt_coordinatesToLevel4Model_Impl coords ox oy x y hx hy

end Algorithm.KotlinModel
