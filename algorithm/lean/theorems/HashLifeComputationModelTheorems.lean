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
import Algorithm.BitComputation
import AlgorithmDefs
import models.BitComputationModel
import models.HashLifeComputationModel
import proofs.HashLifeComputationModelProofs

namespace Algorithm.KotlinModel

/-!
# Formal Theorems About Hand-Written `HashLifeComputation.kt` Model

Pack/unpack bijection laws, centered subnode coordinate mappings, and end-to-end
16×16 → centered 8×8 Conway's Game of Life next-generation soundness.
-/

theorem packLeafNode_leafNw (nw ne sw se : UInt32) :
    leafNwModel (packLeafNodeModel nw ne sw se) = nw &&& 0xffff :=
  packLeafNode_leafNw_Impl nw ne sw se

theorem packLeafNode_leafNe (nw ne sw se : UInt32) :
    leafNeModel (packLeafNodeModel nw ne sw se) = ne &&& 0xffff :=
  packLeafNode_leafNe_Impl nw ne sw se

theorem packLeafNode_leafSw (nw ne sw se : UInt32) :
    leafSwModel (packLeafNodeModel nw ne sw se) = sw &&& 0xffff :=
  packLeafNode_leafSw_Impl nw ne sw se

theorem packLeafNode_leafSe (nw ne sw se : UInt32) :
    leafSeModel (packLeafNodeModel nw ne sw se) = se &&& 0xffff :=
  packLeafNode_leafSe_Impl nw ne sw se

theorem packLeafNode_unpack (w : UInt64) :
    packLeafNodeModel (leafNwModel w) (leafNeModel w) (leafSwModel w) (leafSeModel w) = w :=
  packLeafNode_unpack_Impl w

theorem centeredSubnodeLevel3Model_correct (w : UInt64) (lx ly : Int)
    (hx : 0 ≤ lx ∧ lx < 4) (hy : 0 ≤ ly ∧ ly < 4) :
    Algorithm.grid4At (centeredSubnodeLevel3Model w) lx ly = Algorithm.leafAt w (lx + 2) (ly + 2) :=
  centeredSubnodeLevel3Model_correct_Impl w lx ly hx hy

theorem centeredHorizontalSubnodeLevel3Model_correct (nw ne sw se : UInt64) (lx ly : Int)
    (hx : 0 ≤ lx ∧ lx < 4) (hy : 0 ≤ ly ∧ ly < 4) :
    Algorithm.grid4At (centeredHorizontalSubnodeLevel3Model nw ne) lx ly =
      level4CellAt nw ne sw se (lx + 6) (ly + 2) :=
  centeredHorizontalSubnodeLevel3Model_correct_Impl nw ne sw se lx ly hx hy

theorem centeredVerticalSubnodeLevel3Model_correct (nw ne sw se : UInt64) (lx ly : Int)
    (hx : 0 ≤ lx ∧ lx < 4) (hy : 0 ≤ ly ∧ ly < 4) :
    Algorithm.grid4At (centeredVerticalSubnodeLevel3Model nw sw) lx ly =
      level4CellAt nw ne sw se (lx + 2) (ly + 6) :=
  centeredVerticalSubnodeLevel3Model_correct_Impl nw ne sw se lx ly hx hy

theorem centeredSubSubnodeLevel4Model_correct (nw ne sw se : UInt64) (lx ly : Int)
    (hx : 0 ≤ lx ∧ lx < 4) (hy : 0 ≤ ly ∧ ly < 4) :
    Algorithm.grid4At (centeredSubSubnodeLevel4Model nw ne sw se) lx ly =
      level4CellAt nw ne sw se (lx + 6) (ly + 6) :=
  centeredSubSubnodeLevel4Model_correct_Impl nw ne sw se lx ly hx hy

/-- For every leaf kernel, the Kotlin Level-4 step is the Lean `computeLevel4NextGen16x16WithUInt`. -/
theorem computeLevel4NextGenerationModel_eq_lean (nw ne sw se : UInt64) (computeLeafNextGen : UInt64 → UInt32) :
    computeLevel4NextGenerationModel nw ne sw se computeLeafNextGen =
      Algorithm.computeLevel4NextGen16x16WithUInt nw ne sw se computeLeafNextGen :=
  computeLevel4NextGenerationModel_eq_lean_Impl nw ne sw se computeLeafNextGen

/-- With the default leaf kernel, every cell of the centered 8x8 result is Conway's rule applied to the 16x16
grid. -/
theorem computeLevel4NextGenerationModel_correct (nw ne sw se : UInt64) (x y : Int)
    (hx : 0 ≤ x ∧ x < 8) (hy : 0 ≤ y ∧ y < 8) :
    Algorithm.leafAt (computeLevel4NextGenerationModel nw ne sw se computeNextGenerationPureKotlinModel) x y =
      Algorithm.nextGenAt (level4CellAt nw ne sw se) (x + 4) (y + 4) :=
  computeLevel4NextGenerationModel_correct_Impl nw ne sw se x y hx hy

end Algorithm.KotlinModel
