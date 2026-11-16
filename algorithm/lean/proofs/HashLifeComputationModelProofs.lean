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

import Std.Tactic.BVDecide
import models.HashLifeComputationModel
import proofs.BitComputationModelProofs
import proofs.HashLifeKernelProofs

namespace Algorithm.KotlinModel

/-!
# Proofs about the `HashLifeComputation.kt` model

The leaf packing laws and the centered extractors are proved bit by bit with `bv_check`. The Level-4 step is
proved equal to the Lean `computeLevel4NextGen16x16WithUInt`, whose correctness against Conway's rule is
`leafAt_computeLevel4NextGen16x16UInt`.
-/

/-! ## Leaf packing -/

theorem packLeaf_laws (nw ne sw se : UInt32) (w : UInt64) :
    leafNwModel (packLeafNodeModel nw ne sw se) = nw &&& 0xffff ∧
    leafNeModel (packLeafNodeModel nw ne sw se) = ne &&& 0xffff ∧
    leafSwModel (packLeafNodeModel nw ne sw se) = sw &&& 0xffff ∧
    leafSeModel (packLeafNodeModel nw ne sw se) = se &&& 0xffff ∧
    packLeafNodeModel (leafNwModel w) (leafNeModel w) (leafSwModel w) (leafSeModel w) = w := by
  unfold packLeafNodeModel leafNwModel leafNeModel leafSwModel leafSeModel
  bv_check "lrat/HashLifeComputationModelProofs.Algorithm.KotlinModel.packLeaf_laws.lrat"

theorem packLeafNode_leafNw_Impl (nw ne sw se : UInt32) :
    leafNwModel (packLeafNodeModel nw ne sw se) = nw &&& 0xffff :=
  (packLeaf_laws nw ne sw se 0).1

theorem packLeafNode_leafNe_Impl (nw ne sw se : UInt32) :
    leafNeModel (packLeafNodeModel nw ne sw se) = ne &&& 0xffff :=
  (packLeaf_laws nw ne sw se 0).2.1

theorem packLeafNode_leafSw_Impl (nw ne sw se : UInt32) :
    leafSwModel (packLeafNodeModel nw ne sw se) = sw &&& 0xffff :=
  (packLeaf_laws nw ne sw se 0).2.2.1

theorem packLeafNode_leafSe_Impl (nw ne sw se : UInt32) :
    leafSeModel (packLeafNodeModel nw ne sw se) = se &&& 0xffff :=
  (packLeaf_laws nw ne sw se 0).2.2.2.1

theorem packLeafNode_unpack_Impl (w : UInt64) :
    packLeafNodeModel (leafNwModel w) (leafNeModel w) (leafSwModel w) (leafSeModel w) = w :=
  (packLeaf_laws 0 0 0 0 w).2.2.2.2

/-! ## The 16x16 grid of a Level-4 node -/

/-- `level4CellAt` is the quadrant composition `quadSel` of the four leaves. -/
private theorem level4CellAt_eq_quadSel (nw ne sw se : UInt64) :
    level4CellAt nw ne sw se = quadSel (leafAt nw) (leafAt ne) (leafAt sw) (leafAt se) 8 := by
  funext x y
  unfold level4CellAt quadSel
  by_cases h : 0 ≤ x ∧ x < 16 ∧ 0 ≤ y ∧ y < 16
  · have h1 : ¬(x < 0 ∨ x ≥ 16 ∨ y < 0 ∨ y ≥ 16) := by omega
    have h2 : 0 ≤ x ∧ x < 2 * 8 ∧ 0 ≤ y ∧ y < 2 * 8 := by omega
    simp only [h1, h2, and_self, ↓reduceIte]
    by_cases hx : x < 8 <;> by_cases hy : y < 8 <;> simp only [hx, hy, ↓reduceIte]
  · have h1 : x < 0 ∨ x ≥ 16 ∨ y < 0 ∨ y ≥ 16 := by omega
    have h2 : ¬(0 ≤ x ∧ x < 2 * 8 ∧ 0 ≤ y ∧ y < 2 * 8) := by omega
    simp only [h1, h2, ↓reduceIte]

/-! ## Centered extractors -/

theorem centered3_bits (a : UInt64) :
    (centeredSubnodeLevel3Model a).toBitVec.getLsbD 0 = a.toBitVec.getLsbD 12 ∧
    (centeredSubnodeLevel3Model a).toBitVec.getLsbD 1 = a.toBitVec.getLsbD 13 ∧
    (centeredSubnodeLevel3Model a).toBitVec.getLsbD 2 = a.toBitVec.getLsbD 14 ∧
    (centeredSubnodeLevel3Model a).toBitVec.getLsbD 3 = a.toBitVec.getLsbD 15 ∧
    (centeredSubnodeLevel3Model a).toBitVec.getLsbD 4 = a.toBitVec.getLsbD 24 ∧
    (centeredSubnodeLevel3Model a).toBitVec.getLsbD 5 = a.toBitVec.getLsbD 25 ∧
    (centeredSubnodeLevel3Model a).toBitVec.getLsbD 6 = a.toBitVec.getLsbD 26 ∧
    (centeredSubnodeLevel3Model a).toBitVec.getLsbD 7 = a.toBitVec.getLsbD 27 ∧
    (centeredSubnodeLevel3Model a).toBitVec.getLsbD 8 = a.toBitVec.getLsbD 36 ∧
    (centeredSubnodeLevel3Model a).toBitVec.getLsbD 9 = a.toBitVec.getLsbD 37 ∧
    (centeredSubnodeLevel3Model a).toBitVec.getLsbD 10 = a.toBitVec.getLsbD 38 ∧
    (centeredSubnodeLevel3Model a).toBitVec.getLsbD 11 = a.toBitVec.getLsbD 39 ∧
    (centeredSubnodeLevel3Model a).toBitVec.getLsbD 12 = a.toBitVec.getLsbD 48 ∧
    (centeredSubnodeLevel3Model a).toBitVec.getLsbD 13 = a.toBitVec.getLsbD 49 ∧
    (centeredSubnodeLevel3Model a).toBitVec.getLsbD 14 = a.toBitVec.getLsbD 50 ∧
    (centeredSubnodeLevel3Model a).toBitVec.getLsbD 15 = a.toBitVec.getLsbD 51 := by
  unfold centeredSubnodeLevel3Model leafNwModel leafNeModel leafSwModel leafSeModel
  bv_check "lrat/HashLifeComputationModelProofs.Algorithm.KotlinModel.centered3_bits.lrat"

theorem centeredH3_bits (a b : UInt64) :
    (centeredHorizontalSubnodeLevel3Model a b).toBitVec.getLsbD 0 = a.toBitVec.getLsbD 28 ∧
    (centeredHorizontalSubnodeLevel3Model a b).toBitVec.getLsbD 1 = a.toBitVec.getLsbD 29 ∧
    (centeredHorizontalSubnodeLevel3Model a b).toBitVec.getLsbD 2 = a.toBitVec.getLsbD 30 ∧
    (centeredHorizontalSubnodeLevel3Model a b).toBitVec.getLsbD 3 = a.toBitVec.getLsbD 31 ∧
    (centeredHorizontalSubnodeLevel3Model a b).toBitVec.getLsbD 4 = b.toBitVec.getLsbD 8 ∧
    (centeredHorizontalSubnodeLevel3Model a b).toBitVec.getLsbD 5 = b.toBitVec.getLsbD 9 ∧
    (centeredHorizontalSubnodeLevel3Model a b).toBitVec.getLsbD 6 = b.toBitVec.getLsbD 10 ∧
    (centeredHorizontalSubnodeLevel3Model a b).toBitVec.getLsbD 7 = b.toBitVec.getLsbD 11 ∧
    (centeredHorizontalSubnodeLevel3Model a b).toBitVec.getLsbD 8 = a.toBitVec.getLsbD 52 ∧
    (centeredHorizontalSubnodeLevel3Model a b).toBitVec.getLsbD 9 = a.toBitVec.getLsbD 53 ∧
    (centeredHorizontalSubnodeLevel3Model a b).toBitVec.getLsbD 10 = a.toBitVec.getLsbD 54 ∧
    (centeredHorizontalSubnodeLevel3Model a b).toBitVec.getLsbD 11 = a.toBitVec.getLsbD 55 ∧
    (centeredHorizontalSubnodeLevel3Model a b).toBitVec.getLsbD 12 = b.toBitVec.getLsbD 32 ∧
    (centeredHorizontalSubnodeLevel3Model a b).toBitVec.getLsbD 13 = b.toBitVec.getLsbD 33 ∧
    (centeredHorizontalSubnodeLevel3Model a b).toBitVec.getLsbD 14 = b.toBitVec.getLsbD 34 ∧
    (centeredHorizontalSubnodeLevel3Model a b).toBitVec.getLsbD 15 = b.toBitVec.getLsbD 35 := by
  unfold centeredHorizontalSubnodeLevel3Model leafNwModel leafNeModel leafSwModel leafSeModel
  bv_check "lrat/HashLifeComputationModelProofs.Algorithm.KotlinModel.centeredH3_bits.lrat"

theorem centeredV3_bits (a c : UInt64) :
    (centeredVerticalSubnodeLevel3Model a c).toBitVec.getLsbD 0 = a.toBitVec.getLsbD 44 ∧
    (centeredVerticalSubnodeLevel3Model a c).toBitVec.getLsbD 1 = a.toBitVec.getLsbD 45 ∧
    (centeredVerticalSubnodeLevel3Model a c).toBitVec.getLsbD 2 = a.toBitVec.getLsbD 46 ∧
    (centeredVerticalSubnodeLevel3Model a c).toBitVec.getLsbD 3 = a.toBitVec.getLsbD 47 ∧
    (centeredVerticalSubnodeLevel3Model a c).toBitVec.getLsbD 4 = a.toBitVec.getLsbD 56 ∧
    (centeredVerticalSubnodeLevel3Model a c).toBitVec.getLsbD 5 = a.toBitVec.getLsbD 57 ∧
    (centeredVerticalSubnodeLevel3Model a c).toBitVec.getLsbD 6 = a.toBitVec.getLsbD 58 ∧
    (centeredVerticalSubnodeLevel3Model a c).toBitVec.getLsbD 7 = a.toBitVec.getLsbD 59 ∧
    (centeredVerticalSubnodeLevel3Model a c).toBitVec.getLsbD 8 = c.toBitVec.getLsbD 4 ∧
    (centeredVerticalSubnodeLevel3Model a c).toBitVec.getLsbD 9 = c.toBitVec.getLsbD 5 ∧
    (centeredVerticalSubnodeLevel3Model a c).toBitVec.getLsbD 10 = c.toBitVec.getLsbD 6 ∧
    (centeredVerticalSubnodeLevel3Model a c).toBitVec.getLsbD 11 = c.toBitVec.getLsbD 7 ∧
    (centeredVerticalSubnodeLevel3Model a c).toBitVec.getLsbD 12 = c.toBitVec.getLsbD 16 ∧
    (centeredVerticalSubnodeLevel3Model a c).toBitVec.getLsbD 13 = c.toBitVec.getLsbD 17 ∧
    (centeredVerticalSubnodeLevel3Model a c).toBitVec.getLsbD 14 = c.toBitVec.getLsbD 18 ∧
    (centeredVerticalSubnodeLevel3Model a c).toBitVec.getLsbD 15 = c.toBitVec.getLsbD 19 := by
  unfold centeredVerticalSubnodeLevel3Model leafNwModel leafNeModel leafSwModel leafSeModel
  bv_check "lrat/HashLifeComputationModelProofs.Algorithm.KotlinModel.centeredV3_bits.lrat"

theorem centered4_bits (a b c d : UInt64) :
    (centeredSubSubnodeLevel4Model a b c d).toBitVec.getLsbD 0 = a.toBitVec.getLsbD 60 ∧
    (centeredSubSubnodeLevel4Model a b c d).toBitVec.getLsbD 1 = a.toBitVec.getLsbD 61 ∧
    (centeredSubSubnodeLevel4Model a b c d).toBitVec.getLsbD 2 = a.toBitVec.getLsbD 62 ∧
    (centeredSubSubnodeLevel4Model a b c d).toBitVec.getLsbD 3 = a.toBitVec.getLsbD 63 ∧
    (centeredSubSubnodeLevel4Model a b c d).toBitVec.getLsbD 4 = b.toBitVec.getLsbD 40 ∧
    (centeredSubSubnodeLevel4Model a b c d).toBitVec.getLsbD 5 = b.toBitVec.getLsbD 41 ∧
    (centeredSubSubnodeLevel4Model a b c d).toBitVec.getLsbD 6 = b.toBitVec.getLsbD 42 ∧
    (centeredSubSubnodeLevel4Model a b c d).toBitVec.getLsbD 7 = b.toBitVec.getLsbD 43 ∧
    (centeredSubSubnodeLevel4Model a b c d).toBitVec.getLsbD 8 = c.toBitVec.getLsbD 20 ∧
    (centeredSubSubnodeLevel4Model a b c d).toBitVec.getLsbD 9 = c.toBitVec.getLsbD 21 ∧
    (centeredSubSubnodeLevel4Model a b c d).toBitVec.getLsbD 10 = c.toBitVec.getLsbD 22 ∧
    (centeredSubSubnodeLevel4Model a b c d).toBitVec.getLsbD 11 = c.toBitVec.getLsbD 23 ∧
    (centeredSubSubnodeLevel4Model a b c d).toBitVec.getLsbD 12 = d.toBitVec.getLsbD 0 ∧
    (centeredSubSubnodeLevel4Model a b c d).toBitVec.getLsbD 13 = d.toBitVec.getLsbD 1 ∧
    (centeredSubSubnodeLevel4Model a b c d).toBitVec.getLsbD 14 = d.toBitVec.getLsbD 2 ∧
    (centeredSubSubnodeLevel4Model a b c d).toBitVec.getLsbD 15 = d.toBitVec.getLsbD 3 := by
  unfold centeredSubSubnodeLevel4Model leafNwModel leafNeModel leafSwModel leafSeModel
  bv_check "lrat/HashLifeComputationModelProofs.Algorithm.KotlinModel.centered4_bits.lrat"


set_option linter.unusedSimpArgs false in
theorem centeredSubnodeLevel3Model_correct_Impl (w : UInt64) (lx ly : Int)
    (hx : 0 ≤ lx ∧ lx < 4) (hy : 0 ≤ ly ∧ ly < 4) :
    grid4At (centeredSubnodeLevel3Model w) lx ly = leafAt w (lx + 2) (ly + 2) := by
  obtain ⟨k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15⟩ := centered3_bits w
  have hx' : lx = 0 ∨ lx = 1 ∨ lx = 2 ∨ lx = 3 := by omega
  have hy' : ly = 0 ∨ ly = 1 ∨ ly = 2 ∨ ly = 3 := by omega
  rcases hx' with rfl | rfl | rfl | rfl <;> rcases hy' with rfl | rfl | rfl | rfl <;>
    simp only [grid4At, quadSel, leafAt, mortonIndex, mortonIndex4, Int.reduceAdd, Int.reduceSub, Int.reduceLT,
      Int.reduceLE, Int.reduceToNat, Int.reduceMul, Nat.reduceMod, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd,
      ↓reduceIte, and_self, true_and, and_true] <;>
    simp only [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15]

set_option linter.unusedSimpArgs false in
theorem centeredHorizontalSubnodeLevel3Model_correct_Impl (nw ne sw se : UInt64) (lx ly : Int)
    (hx : 0 ≤ lx ∧ lx < 4) (hy : 0 ≤ ly ∧ ly < 4) :
    grid4At (centeredHorizontalSubnodeLevel3Model nw ne) lx ly =
      level4CellAt nw ne sw se (lx + 6) (ly + 2) := by
  obtain ⟨k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15⟩ := centeredH3_bits nw ne
  rw [level4CellAt_eq_quadSel]
  have hx' : lx = 0 ∨ lx = 1 ∨ lx = 2 ∨ lx = 3 := by omega
  have hy' : ly = 0 ∨ ly = 1 ∨ ly = 2 ∨ ly = 3 := by omega
  rcases hx' with rfl | rfl | rfl | rfl <;> rcases hy' with rfl | rfl | rfl | rfl <;>
    simp only [grid4At, quadSel, leafAt, mortonIndex, mortonIndex4, Int.reduceAdd, Int.reduceSub, Int.reduceLT,
      Int.reduceLE, Int.reduceToNat, Int.reduceMul, Nat.reduceMod, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd,
      ↓reduceIte, and_self, true_and, and_true] <;>
    simp only [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15]

set_option linter.unusedSimpArgs false in
theorem centeredVerticalSubnodeLevel3Model_correct_Impl (nw ne sw se : UInt64) (lx ly : Int)
    (hx : 0 ≤ lx ∧ lx < 4) (hy : 0 ≤ ly ∧ ly < 4) :
    grid4At (centeredVerticalSubnodeLevel3Model nw sw) lx ly =
      level4CellAt nw ne sw se (lx + 2) (ly + 6) := by
  obtain ⟨k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15⟩ := centeredV3_bits nw sw
  rw [level4CellAt_eq_quadSel]
  have hx' : lx = 0 ∨ lx = 1 ∨ lx = 2 ∨ lx = 3 := by omega
  have hy' : ly = 0 ∨ ly = 1 ∨ ly = 2 ∨ ly = 3 := by omega
  rcases hx' with rfl | rfl | rfl | rfl <;> rcases hy' with rfl | rfl | rfl | rfl <;>
    simp only [grid4At, quadSel, leafAt, mortonIndex, mortonIndex4, Int.reduceAdd, Int.reduceSub, Int.reduceLT,
      Int.reduceLE, Int.reduceToNat, Int.reduceMul, Nat.reduceMod, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd,
      ↓reduceIte, and_self, true_and, and_true] <;>
    simp only [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15]

set_option linter.unusedSimpArgs false in
theorem centeredSubSubnodeLevel4Model_correct_Impl (nw ne sw se : UInt64) (lx ly : Int)
    (hx : 0 ≤ lx ∧ lx < 4) (hy : 0 ≤ ly ∧ ly < 4) :
    grid4At (centeredSubSubnodeLevel4Model nw ne sw se) lx ly =
      level4CellAt nw ne sw se (lx + 6) (ly + 6) := by
  obtain ⟨k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15⟩ := centered4_bits nw ne sw se
  rw [level4CellAt_eq_quadSel]
  have hx' : lx = 0 ∨ lx = 1 ∨ lx = 2 ∨ lx = 3 := by omega
  have hy' : ly = 0 ∨ ly = 1 ∨ ly = 2 ∨ ly = 3 := by omega
  rcases hx' with rfl | rfl | rfl | rfl <;> rcases hy' with rfl | rfl | rfl | rfl <;>
    simp only [grid4At, quadSel, leafAt, mortonIndex, mortonIndex4, Int.reduceAdd, Int.reduceSub, Int.reduceLT,
      Int.reduceLE, Int.reduceToNat, Int.reduceMul, Nat.reduceMod, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd,
      ↓reduceIte, and_self, true_and, and_true] <;>
    simp only [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15]

/-! ## Level-4 step -/

theorem centered3_eq (a : UInt64) :
    centeredSubnodeLevel3Model a = centeredSubnodeLevel3BitsUInt a := by
  unfold centeredSubnodeLevel3Model centeredSubnodeLevel3BitsUInt packCentralNibblesUInt leafNwModel leafNeModel
    leafSwModel leafSeModel
  bv_check "lrat/HashLifeComputationModelProofs.Algorithm.KotlinModel.centered3_eq.lrat"

theorem centeredH3_eq (a b : UInt64) :
    centeredHorizontalSubnodeLevel3Model a b = centeredHorizontalSubnodeLevel3BitsUInt a b := by
  unfold centeredHorizontalSubnodeLevel3Model centeredHorizontalSubnodeLevel3BitsUInt packCentralNibblesUInt
    leafNwModel leafNeModel leafSwModel leafSeModel
  bv_check "lrat/HashLifeComputationModelProofs.Algorithm.KotlinModel.centeredH3_eq.lrat"

theorem centeredV3_eq (a b : UInt64) :
    centeredVerticalSubnodeLevel3Model a b = centeredVerticalSubnodeLevel3BitsUInt a b := by
  unfold centeredVerticalSubnodeLevel3Model centeredVerticalSubnodeLevel3BitsUInt packCentralNibblesUInt
    leafNwModel leafNeModel leafSwModel leafSeModel
  bv_check "lrat/HashLifeComputationModelProofs.Algorithm.KotlinModel.centeredV3_eq.lrat"

theorem centered4_eq (a b c d : UInt64) :
    centeredSubSubnodeLevel4Model a b c d = centeredSubSubnodeLevel4BitsUInt a b c d := by
  unfold centeredSubSubnodeLevel4Model centeredSubSubnodeLevel4BitsUInt packCentralNibblesUInt
    leafNwModel leafNeModel leafSwModel leafSeModel
  bv_check "lrat/HashLifeComputationModelProofs.Algorithm.KotlinModel.centered4_eq.lrat"

theorem computeLevel4NextGenerationModel_eq_lean_Impl (nw ne sw se : UInt64) (computeLeafNextGen : UInt64 → UInt32) :
    computeLevel4NextGenerationModel nw ne sw se computeLeafNextGen =
      computeLevel4NextGen16x16WithUInt nw ne sw se computeLeafNextGen := by
  unfold computeLevel4NextGenerationModel computeLevel4NextGen16x16WithUInt
  simp only [centered3_eq, centeredH3_eq,
    centeredV3_eq, centered4_eq]
  rfl

theorem computeLevel4NextGenerationModel_correct_Impl (nw ne sw se : UInt64) (x y : Int)
    (hx : 0 ≤ x ∧ x < 8) (hy : 0 ≤ y ∧ y < 8) :
    leafAt (computeLevel4NextGenerationModel nw ne sw se computeNextGenerationPureKotlinModel) x y =
      nextGenAt (level4CellAt nw ne sw se) (x + 4) (y + 4) := by
  have hleaf : computeNextGenerationPureKotlinModel = computeLeafNextGen8x8BranchUInt :=
    funext fun w => (computeNextGenerationPureKotlinModel_eq_fast_Impl w).trans
      (computeLeafNextGen8x8BranchUInt_eq_fast w).symm
  rw [computeLevel4NextGenerationModel_eq_lean_Impl, hleaf, level4CellAt_eq_quadSel]
  exact leafAt_computeLevel4NextGen16x16UInt nw ne sw se x y hx.1 hx.2 hy.1 hy.2

end Algorithm.KotlinModel
