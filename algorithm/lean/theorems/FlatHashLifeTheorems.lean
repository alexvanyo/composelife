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

import Algorithm.MacroCell
import Algorithm.HashLife
import Algorithm.HashLifeEquivalence
import Algorithm.FlatHashLife
import AlgorithmDefs
import proofs.FlatHashLifeProofs

local notation "ℕ" => Nat

namespace Algorithm

/-!
# Flat HashLife arena: master theorems

Master theorems for every public function of the compiled flat-arena engine (`FlatHashLifeArena`). They are
stated in terms of the structural arena invariant `ArenaWF`, node preservation `NodesPreserved`, the
denotation of arena nodes as MacroCells, and the reference HashLife and grid semantics. Every function reports
failure explicitly (an `UNCOMPUTED` result and, where it can be caused by capacity, the `overflow` flag), and
every result that is not reported as a failure is exact.
-/

/--
Initializing a freshly allocated arena (whose node tables have room for their masks, and room for the 56
pre-interned empty CellNodes) yields a well-formed arena that has not failed, holding exactly the pre-interned
empty nodes, without touching the masks or the scratch tables.
-/
theorem flat_initEmptyNodes_wf {a : FlatHashLifeArena}
    (hl4 :
      a.l4Mask.toNat + 1 ≤ a.l4Nw.size ∧ a.l4Mask.toNat + 1 ≤ a.l4Ne.size ∧
      a.l4Mask.toNat + 1 ≤ a.l4Sw.size ∧ a.l4Mask.toNat + 1 ≤ a.l4Se.size ∧
      a.l4Mask.toNat + 1 ≤ a.l4StepRes.size ∧ a.l4Mask.toNat + 1 ≤ a.l4HasRes.size)
    (hcell :
      a.cellMask.toNat + 1 ≤ a.cellNw.size ∧ a.cellMask.toNat + 1 ≤ a.cellNe.size ∧
      a.cellMask.toNat + 1 ≤ a.cellSw.size ∧ a.cellMask.toNat + 1 ≤ a.cellSe.size ∧
      a.cellMask.toNat + 1 ≤ a.cellLevel.size ∧ a.cellMask.toNat + 1 ≤ a.cellPop.size ∧
      a.cellMask.toNat + 1 ≤ a.cellStepRes.size)
    (hmask : 55 ≤ a.cellMask.toNat) :
    ArenaWF a.initEmptyNodes ∧ a.initEmptyNodes.overflow = 0 ∧ a.initEmptyNodes.l4Count = 1 ∧
      a.initEmptyNodes.cellCount = 56 ∧ a.initEmptyNodes.l4Mask = a.l4Mask ∧
      a.initEmptyNodes.cellMask = a.cellMask ∧ a.initEmptyNodes.remapL4 = a.remapL4 ∧
      a.initEmptyNodes.remapCell = a.remapCell :=
  flat_initEmptyNodes_Impl hl4 hcell hmask

/--
Interning a Level 4 node keeps the arena well-formed and every existing node intact, and unless the arena
reports failure, returns a Level 4 node with exactly the requested leaves.
-/
theorem flat_internLevel4_correct {a : FlatHashLifeArena} (hwf : ArenaWF a) (nw ne sw se : UInt64) :
    ArenaWF (a.internLevel4 nw ne sw se).2 ∧ NodesPreserved a (a.internLevel4 nw ne sw se).2 ∧
    ((a.internLevel4 nw ne sw se).2.overflow = 0 →
      (a.internLevel4 nw ne sw se).1 < (a.internLevel4 nw ne sw se).2.l4Count ∧
      denoteLevel4 (a.internLevel4 nw ne sw se).2 (a.internLevel4 nw ne sw se).1 = makeLevel4Node nw ne sw se) :=
  flat_internLevel4_Impl hwf nw ne sw se

/--
Interning a CellNode whose children are nodes one level down keeps the arena well-formed and every existing
node intact, and unless the arena reports failure, returns a node at the requested level denoting the cell node
of its children.
-/
theorem flat_internCellNode_correct {a : FlatHashLifeArena} (hwf : ArenaWF a) {lvl : UInt8} {h : ℕ}
    (hl : lvl.toNat = h + 5) {nw ne sw se : UInt32} {m1 m2 m3 m4 : MacroCell}
    (h1 : NodeIs a h nw m1) (h2 : NodeIs a h ne m2) (h3 : NodeIs a h sw m3) (h4 : NodeIs a h se m4) :
    ArenaWF (a.internCellNode lvl nw ne sw se).2 ∧ NodesPreserved a (a.internCellNode lvl nw ne sw se).2 ∧
    ((a.internCellNode lvl nw ne sw se).2.overflow = 0 →
      NodeIs (a.internCellNode lvl nw ne sw se).2 (h + 1) (a.internCellNode lvl nw ne sw se).1
        (makeCellNode m1 m2 m3 m4)) :=
  flat_internCellNode_Impl hwf hl h1 h2 h3 h4

/--
Importing a Level 4 pattern whose top-left corner is `(ox, oy)` keeps the arena well-formed and every
existing node intact. On success the new root is the centered two-level expansion of the pattern, its corner is
24 cells up and to the left, and it has exactly the pattern's live cells. It succeeds whenever that corner is
representable and the arena does not report running out of capacity.
-/
theorem flat_importLevel4Root_correct {a : FlatHashLifeArena} (hwf : ArenaWF a) (ox oy : Int32)
    (nw ne sw se : UInt64) :
    ArenaWF (a.importLevel4Root ox oy nw ne sw se).2 ∧ NodesPreserved a (a.importLevel4Root ox oy nw ne sw se).2 ∧
    ((a.importLevel4Root ox oy nw ne sw se).1.2.2 ≠ UNCOMPUTED →
      (a.importLevel4Root ox oy nw ne sw se).2.overflow = 0 ∧
      (a.importLevel4Root ox oy nw ne sw se).1.2.2 < (a.importLevel4Root ox oy nw ne sw se).2.cellCount ∧
      flatState (a.importLevel4Root ox oy nw ne sw se).2 (a.importLevel4Root ox oy nw ne sw se).1.1
        (a.importLevel4Root ox oy nw ne sw se).1.2.1 (a.importLevel4Root ox oy nw ne sw se).1.2.2 =
        { offset := (ox.toInt - 24, oy.toInt - 24), macroCell := expandCentered (makeLevel4Node nw ne sw se) } ∧
      ∀ c, c ∈ hashLifeToGrid (flatState (a.importLevel4Root ox oy nw ne sw se).2
          (a.importLevel4Root ox oy nw ne sw se).1.1 (a.importLevel4Root ox oy nw ne sw se).1.2.1
          (a.importLevel4Root ox oy nw ne sw se).1.2.2) ↔
        c ∈ hashLifeToGrid { offset := (ox.toInt, oy.toInt), macroCell := makeLevel4Node nw ne sw se }) ∧
    (-2 ^ 31 ≤ ox.toInt - 24 → -2 ^ 31 ≤ oy.toInt - 24 →
      (a.importLevel4Root ox oy nw ne sw se).2.overflow = 0 →
      (a.importLevel4Root ox oy nw ne sw se).1.2.2 ≠ UNCOMPUTED) :=
  flat_importLevel4Root_Impl hwf ox oy nw ne sw se

/--
The flat engine's generation function (`flatNextGeneration`: expand if needed, then one HashLife step)
computes exactly one Conway generation of any well-formed state of depth at most 30.
-/
theorem flat_nextGeneration_equivalence (st : HashLifeCellState)
    (h_wf : isWellFormed st.macroCell) (h_depth : st.macroCell.depth ≤ 30) :
    isWellFormed (flatNextGeneration st).macroCell ∧
    ∀ c, c ∈ hashLifeToGrid (flatNextGeneration st) ↔ c ∈ stepGrid (hashLifeToGrid st) :=
  flat_nextGeneration_Impl st h_wf h_depth

/--
Master single-generation theorem for the compiled flat engine: `stepOneGeneration` keeps the arena
well-formed and every existing node intact. Whenever it returns a root other than `UNCOMPUTED`, the arena has
not failed, the new root and corner are exactly `flatNextGeneration` of the input, and the cells are exactly one
Conway generation of the input cells. It succeeds whenever the input root is valid, the next generation is
representable (`flatStepInRange`), and the arena does not report a failure.
-/
theorem flat_stepOneGeneration_correct {a : FlatHashLifeArena} (hwf : ArenaWF a) (ox oy : Int32) (root : UInt32) :
    ArenaWF (a.stepOneGeneration ox oy root).2 ∧ NodesPreserved a (a.stepOneGeneration ox oy root).2 ∧
    ((a.stepOneGeneration ox oy root).1.2.2 ≠ UNCOMPUTED →
      (a.stepOneGeneration ox oy root).2.overflow = 0 ∧
      (a.stepOneGeneration ox oy root).1.2.2 < (a.stepOneGeneration ox oy root).2.cellCount ∧
      flatState (a.stepOneGeneration ox oy root).2 (a.stepOneGeneration ox oy root).1.1
        (a.stepOneGeneration ox oy root).1.2.1 (a.stepOneGeneration ox oy root).1.2.2 =
        flatNextGeneration (flatState a ox oy root) ∧
      cellsEqual
        (hashLifeToGrid (flatState (a.stepOneGeneration ox oy root).2 (a.stepOneGeneration ox oy root).1.1
          (a.stepOneGeneration ox oy root).1.2.1 (a.stepOneGeneration ox oy root).1.2.2))
        (stepGrid (hashLifeToGrid (flatState a ox oy root))) = true) ∧
    (root < a.cellCount → flatStepInRange (flatState a ox oy root) →
      (a.stepOneGeneration ox oy root).2.overflow = 0 → (a.stepOneGeneration ox oy root).1.2.2 ≠ UNCOMPUTED) :=
  flat_stepOneGeneration_Impl hwf ox oy root

/--
Master multi-generation theorem: `n` successive successful steps compute exactly `n` generations of the
flat engine and `n` Conway generations of the cells.
-/
theorem flat_stepOneGenerationN_correct (n : ℕ) {a : FlatHashLifeArena} (hwf : ArenaWF a) (ox oy : Int32)
    (root : UInt32) (hid : root < a.cellCount) :
    ArenaWF (a.stepOneGenerationN n ox oy root).2 ∧
    ((a.stepOneGenerationN n ox oy root).1.2.2 ≠ UNCOMPUTED →
      (a.stepOneGenerationN n ox oy root).1.2.2 < (a.stepOneGenerationN n ox oy root).2.cellCount ∧
      flatState (a.stepOneGenerationN n ox oy root).2 (a.stepOneGenerationN n ox oy root).1.1
        (a.stepOneGenerationN n ox oy root).1.2.1 (a.stepOneGenerationN n ox oy root).1.2.2 =
        flatStepN n (flatState a ox oy root) ∧
      cellsEqual
        (hashLifeToGrid (flatState (a.stepOneGenerationN n ox oy root).2 (a.stepOneGenerationN n ox oy root).1.1
          (a.stepOneGenerationN n ox oy root).1.2.1 (a.stepOneGenerationN n ox oy root).1.2.2))
        (stepN n (hashLifeToGrid (flatState a ox oy root))) = true) :=
  flat_stepOneGenerationN_Impl n hwf ox oy root hid

/--
`canCopySubgraphFrom` holds exactly when the destination's scratch tables can hold the remapping of every
node of the source plus the copy work stack.
-/
theorem flat_canCopySubgraphFrom_iff (dst src : FlatHashLifeArena) (h1 : dst.remapL4.size < 2 ^ 32)
    (h2 : dst.remapCell.size < 2 ^ 32) :
    dst.canCopySubgraphFrom src = true ↔
      src.l4Count.toNat ≤ dst.remapL4.size ∧ src.cellCount.toNat + 256 ≤ dst.remapCell.size :=
  flat_canCopySubgraphFrom_Impl dst src h1 h2

/--
Copying a subgraph between well-formed arenas keeps the destination well-formed, keeps every existing node and
the scratch table sizes, and succeeds exactly when it leaves the failure flag clear. On success the copied root
has the source root's level and denotation, so it represents the same cells at any corner.
-/
theorem flat_copySubgraphFrom_correct {src dst : FlatHashLifeArena} (hsrc : ArenaWF src) (hwf : ArenaWF dst)
    (rootId : UInt32) (copyMemos : Bool) :
    ArenaWF (dst.copySubgraphFrom src rootId copyMemos).2 ∧
    NodesPreserved dst (dst.copySubgraphFrom src rootId copyMemos).2 ∧
    (dst.copySubgraphFrom src rootId copyMemos).2.remapL4.size = dst.remapL4.size ∧
    (dst.copySubgraphFrom src rootId copyMemos).2.remapCell.size = dst.remapCell.size ∧
    ((dst.copySubgraphFrom src rootId copyMemos).1 ≠ UNCOMPUTED ↔
      (dst.copySubgraphFrom src rootId copyMemos).2.overflow = 0) ∧
    ((dst.copySubgraphFrom src rootId copyMemos).1 ≠ UNCOMPUTED →
      rootId < src.cellCount ∧
      (dst.copySubgraphFrom src rootId copyMemos).1 < (dst.copySubgraphFrom src rootId copyMemos).2.cellCount ∧
      cellLevelOf (dst.copySubgraphFrom src rootId copyMemos).2 (dst.copySubgraphFrom src rootId copyMemos).1 =
        cellLevelOf src rootId ∧
      denoteCell (dst.copySubgraphFrom src rootId copyMemos).2 (dst.copySubgraphFrom src rootId copyMemos).1 =
        denoteCell src rootId ∧
      ∀ ox oy : Int32, flatState (dst.copySubgraphFrom src rootId copyMemos).2 ox oy
        (dst.copySubgraphFrom src rootId copyMemos).1 = flatState src ox oy rootId) :=
  flat_copySubgraphFrom_Impl hsrc hwf rootId copyMemos

/--
Compacting a root into a destination arena keeps the destination well-formed, keeps every existing node and the
scratch table sizes. On success the compacted root has the source root's level and denotation, so it represents
the same cells at any corner. It succeeds whenever the root is a node of a non-failed source and the destination
does not report running out of capacity.
-/
theorem flat_compactRootFrom_correct {src dst : FlatHashLifeArena} (hsrc : ArenaWF src) (hwf : ArenaWF dst)
    (rootId : UInt32) :
    ArenaWF (dst.compactRootFrom src rootId).2 ∧ NodesPreserved dst (dst.compactRootFrom src rootId).2 ∧
    (dst.compactRootFrom src rootId).2.remapL4.size = dst.remapL4.size ∧
    (dst.compactRootFrom src rootId).2.remapCell.size = dst.remapCell.size ∧
    ((dst.compactRootFrom src rootId).1.1 ≠ UNCOMPUTED →
      (dst.compactRootFrom src rootId).2.overflow = 0 ∧ rootId < src.cellCount ∧
      (dst.compactRootFrom src rootId).1.1 < (dst.compactRootFrom src rootId).2.cellCount ∧
      cellLevelOf (dst.compactRootFrom src rootId).2 (dst.compactRootFrom src rootId).1.1 =
        cellLevelOf src rootId ∧
      denoteCell (dst.compactRootFrom src rootId).2 (dst.compactRootFrom src rootId).1.1 = denoteCell src rootId ∧
      ∀ ox oy : Int32, flatState (dst.compactRootFrom src rootId).2 ox oy (dst.compactRootFrom src rootId).1.1 =
        flatState src ox oy rootId) ∧
    (rootId < src.cellCount → src.overflow = 0 → (dst.compactRootFrom src rootId).2.overflow = 0 →
      (dst.compactRootFrom src rootId).1.1 ≠ UNCOMPUTED) :=
  flat_compactRootFrom_Impl hsrc hwf rootId

/--
For any root of a well-formed arena with top-left corner `(ox, oy)`, `containsCell` at the 64-bit offset of
`(x, y)` is `true` exactly when `(x, y)` is a live cell of the state, at every level.
-/
theorem flat_containsCell_correct {a : FlatHashLifeArena} (hwf : ArenaWF a) {root : UInt32}
    (hid : root < a.cellCount) (ox oy x y : Int32) :
    a.containsCell root (x.toInt64 - ox.toInt64) (y.toInt64 - oy.toInt64) = true ↔
      (x.toInt, y.toInt) ∈ hashLifeToGrid (flatState a ox oy root) :=
  flat_containsCell_Impl hwf hid ox oy x y

/--
The compaction trigger `isNearCapacity` holds exactly when either node table is at least 75% full.
-/
theorem flat_isNearCapacity_iff {a : FlatHashLifeArena} (hwf : ArenaWF a) (hl : a.l4Mask.toNat < 2 ^ 29)
    (hc : a.cellMask.toNat < 2 ^ 29) :
    a.isNearCapacity = true ↔
      3 * (a.l4Mask.toNat + 1) ≤ 4 * a.l4Count.toNat ∨ 3 * (a.cellMask.toNat + 1) ≤ 4 * a.cellCount.toNat :=
  flat_isNearCapacity_Impl hwf hl hc

/--
The growth trigger `isOver60Percent` holds exactly when either node table is at least 60% full.
-/
theorem flat_isOver60Percent_iff {a : FlatHashLifeArena} (hwf : ArenaWF a) (hl : a.l4Mask.toNat < 2 ^ 29)
    (hc : a.cellMask.toNat < 2 ^ 29) :
    a.isOver60Percent = true ↔
      3 * (a.l4Mask.toNat + 1) ≤ 5 * a.l4Count.toNat ∨ 3 * (a.cellMask.toNat + 1) ≤ 5 * a.cellCount.toNat :=
  flat_isOver60Percent_Impl hwf hl hc

end Algorithm
