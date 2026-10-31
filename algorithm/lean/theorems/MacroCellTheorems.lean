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
import proofs.MacroCellProofs
import proofs.MacroCellQueryProofs

local notation "ℕ" => Nat

namespace Algorithm

/-!
# MacroCell members

Facts about the members of the compiled `MacroCell` class (level, size, equality, hash code).
-/

/-- Level 4 nodes have level 4. -/
theorem macroCell_level_level4Node (hash : UInt32) (nw ne sw se : UInt64) :
    (MacroCell.level4Node hash nw ne sw se).level = 4 :=
  macroCell_level_level4Node_Impl hash nw ne sw se

/-- Cell nodes have level equal to child level + 1. -/
theorem macroCell_level_cellNode (hash : UInt32) (nw ne sw se : MacroCell) :
    (MacroCell.cellNode hash nw ne sw se).level = nw.level + 1 :=
  macroCell_level_cellNode_Impl hash nw ne sw se

/-- The `UInt32` level of a well-formed node is its depth. -/
theorem macroCell_level_eq_depth {m : MacroCell} {d : ℕ} (hm : WFd m d) (hd : d < 2 ^ 32) : m.level.toNat = d :=
  WFd_level_toNat hm hd

/-- The `UInt64` population of a well-formed node of depth at most 31 is its exact number of live cells. -/
theorem macroCell_size_eq {m : MacroCell} {d : ℕ} (hm : WFd m d) (hd : d ≤ 31) : m.size.toNat = macroCellSize m :=
  size_toNat_of_WFd hm hd

/-- Empty nodes at any level have size 0. -/
theorem macroCell_size_emptyNode (k : ℕ) : (emptyNode k).size = 0 :=
  macroCell_size_emptyNode_Impl k

/-- Empty nodes at any level are well-formed. -/
theorem macroCell_emptyNode_isWellFormed (k : ℕ) : isWellFormed (emptyNode k) :=
  macroCell_emptyNode_isWellFormed_Impl k

/-- Structural equality on MacroCell is equivalent to propositional equality. -/
theorem macroCell_cellEquals_iff_eq (m1 m2 : MacroCell) :
    m1.cellEquals m2 = true ↔ m1 = m2 :=
  macroCell_cellEquals_iff_eq_Impl m1 m2

/-- `Level4Node.cellEquals`, which Kotlin's `Level4Node.equals` falls back to, is equality. -/
theorem level4Node_cellEquals_iff_eq (h1 h2 : UInt32) (a1 b1 c1 d1 a2 b2 c2 d2 : UInt64) :
    Level4Node.cellEquals (.level4Node h1 a1 b1 c1 d1) (.level4Node h2 a2 b2 c2 d2) = true ↔
      MacroCell.level4Node h1 a1 b1 c1 d1 = .level4Node h2 a2 b2 c2 d2 :=
  level4Node_cellEquals_iff h1 h2 a1 b1 c1 d1 a2 b2 c2 d2

/-- `CellNode.cellEquals`, which Kotlin's `CellNode.equals` falls back to, is equality. -/
theorem cellNode_cellEquals_iff_eq (h1 h2 : UInt32) (a1 b1 c1 d1 a2 b2 c2 d2 : MacroCell) :
    CellNode.cellEquals (.cellNode h1 a1 b1 c1 d1) (.cellNode h2 a2 b2 c2 d2) = true ↔
      MacroCell.cellNode h1 a1 b1 c1 d1 = .cellNode h2 a2 b2 c2 d2 :=
  cellNode_cellEquals_iff h1 h2 a1 b1 c1 d1 a2 b2 c2 d2

/-- Kotlin hashCode matches cellHashCode. -/
theorem macroCell_hashCode_eq (m : MacroCell) :
    m.hashCode = m.cellHashCode :=
  macroCell_hashCode_eq_Impl m

end Algorithm
