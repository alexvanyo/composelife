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

import models.CellWindowModel
import proofs.CellWindowModelProofs

namespace Algorithm.KotlinModel

/-!
# Formal Theorems About Hand-Written `CellWindow.kt` Model

Constructor invariant, dimensions, cardinality formula, membership biconditional,
row-major order (`getElem?`), duplicate-freeness (`Nodup`), and translation
equivariance.
-/

theorem mkCellWindowModel_some_iff (l t r b : Int32) :
    (mkCellWindowModel l t r b).isSome ↔ (t ≤ b ∧ l ≤ r) :=
  mkCellWindowModel_some_iff_Impl l t r b

theorem mkCellWindowModel_invalid (l t r b : Int32) (h : b < t ∨ r < l) :
    mkCellWindowModel l t r b = none :=
  mkCellWindowModel_invalid_Impl l t r b h

theorem CellWindowModel_containedPoints_length (w : CellWindowModel) :
    w.containedPoints.length =
      (if w.left.toInt ≤ w.right.toInt then (w.right.toInt - w.left.toInt).toNat else 0) *
      (if w.top.toInt ≤ w.bottom.toInt then (w.bottom.toInt - w.top.toInt).toNat else 0) :=
  CellWindowModel_containedPoints_length_Impl w

theorem CellWindowModel_mem_containedPoints_iff (w : CellWindowModel) (x y : Int32) :
    (x, y) ∈ w.containedPoints ↔
      (w.left.toInt ≤ x.toInt ∧ x.toInt < w.right.toInt ∧
       w.top.toInt ≤ y.toInt ∧ y.toInt < w.bottom.toInt) :=
  CellWindowModel_mem_containedPoints_iff_Impl w x y

/-- `containedPoints` is row-major: the point at column `i` of row `j` is at index `j * width + i`. -/
theorem CellWindowModel_containedPoints_getElem? (w : CellWindowModel) (i j : Nat)
    (hi : i < (w.right.toInt - w.left.toInt).toNat) (hj : j < (w.bottom.toInt - w.top.toInt).toNat) :
    w.containedPoints[j * (w.right.toInt - w.left.toInt).toNat + i]? =
      some (Int32.ofInt (w.left.toInt + i), Int32.ofInt (w.top.toInt + j)) :=
  CellWindowModel_containedPoints_getElem?_Impl w i j hi hj

theorem CellWindowModel_containedPoints_nodup (w : CellWindowModel) :
    w.containedPoints.Nodup :=
  CellWindowModel_containedPoints_nodup_Impl w

theorem CellWindowModel_translate_containedPoints (w w' : CellWindowModel) (dx dy : Int32)
    (ht : w.translate dx dy = some w')
    (hvx : w.left.toInt ≤ w.right.toInt) (hvy : w.top.toInt ≤ w.bottom.toInt)
    (hminX : Int32.minValue.toInt ≤ w.left.toInt + dx.toInt)
    (hmaxX : w.right.toInt + dx.toInt ≤ Int32.maxValue.toInt)
    (hminY : Int32.minValue.toInt ≤ w.top.toInt + dy.toInt)
    (hmaxY : w.bottom.toInt + dy.toInt ≤ Int32.maxValue.toInt) :
    w'.containedPoints = w.containedPoints.map (fun p => (p.1 + dx, p.2 + dy)) :=
  CellWindowModel_translate_containedPoints_Impl w w' dx dy ht hvx hvy hminX hmaxX hminY hmaxY

/-- `width` is `right - left` whenever that difference fits in an `Int`. -/
theorem CellWindowModel_width_toInt (w : CellWindowModel) (h : w.left.toInt ≤ w.right.toInt)
    (hfit : w.right.toInt - w.left.toInt ≤ Int32.maxValue.toInt) :
    w.width.toInt = w.right.toInt - w.left.toInt :=
  CellWindowModel_width_toInt_Impl w h hfit

/-- `height` is `bottom - top` whenever that difference fits in an `Int`. -/
theorem CellWindowModel_height_toInt (w : CellWindowModel) (h : w.top.toInt ≤ w.bottom.toInt)
    (hfit : w.bottom.toInt - w.top.toInt ≤ Int32.maxValue.toInt) :
    w.height.toInt = w.bottom.toInt - w.top.toInt :=
  CellWindowModel_height_toInt_Impl w h hfit

end Algorithm.KotlinModel
