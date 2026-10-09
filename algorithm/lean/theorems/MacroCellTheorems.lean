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
import Algorithm.MacroCell
import AlgorithmDefs
import proofs.MacroCellProofs

local notation "ℕ" => Nat

namespace Algorithm

/--
Population count of an all-zero 64-bit leaf is 0.
-/
theorem popcount64_zero : popcount64 0 = 0 :=
  popcount64_zero_Impl

/--
Extracting the center 8x8 leaf from four empty leaves produces an empty leaf.
-/
theorem centeredSubnodeLevel4_zero : centeredSubnodeLevel4 0 0 0 0 = 0 :=
  centeredSubnodeLevel4_zero_Impl

/--
Level 4 nodes have level 4.
-/
theorem macroCell_level_level4Node (nw ne sw se : UInt64) :
    (MacroCell.level4Node nw ne sw se).level = 4 :=
  macroCell_level_level4Node_Impl nw ne sw se

/--
Cell nodes have level equal to child level + 1.
-/
theorem macroCell_level_cellNode (nw ne sw se : MacroCell) :
    (MacroCell.cellNode nw ne sw se).level = nw.level + 1 :=
  macroCell_level_cellNode_Impl nw ne sw se

/--
An empty level 4 node has size 0.
-/
theorem macroCell_size_emptyLevel4 : emptyLevel4.size = 0 :=
  macroCell_size_emptyLevel4_Impl

/--
Empty nodes at any level have size 0.
-/
theorem macroCell_size_emptyNode (k : ℕ) : (emptyNode k).size = 0 :=
  macroCell_size_emptyNode_Impl k

/--
Empty nodes at any level are well-formed.
-/
theorem macroCell_emptyNode_isWellFormed (k : ℕ) : isWellFormed (emptyNode k) :=
  macroCell_emptyNode_isWellFormed_Impl k

/--
Horizontal reflection on MacroCell is an involution.
-/
theorem macroCell_flipX_involution (m : MacroCell) :
    macroCellFlipX (macroCellFlipX m) = m :=
  macroCell_flipX_involution_Impl m

/--
Vertical reflection on MacroCell is an involution.
-/
theorem macroCell_flipY_involution (m : MacroCell) :
    macroCellFlipY (macroCellFlipY m) = m :=
  macroCell_flipY_involution_Impl m

end Algorithm
