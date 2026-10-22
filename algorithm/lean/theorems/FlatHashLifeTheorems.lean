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
import Algorithm.FlatHashLife
import AlgorithmDefs
import proofs.FlatHashLifeProofs
import proofs.FlatArenaLiveness
import proofs.FlatArenaBudget
import proofs.FlatArenaConvert
import proofs.FlatArenaCursor

local notation "ℕ" => Nat
local notation "ℤ" => Int

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
Success condition for one step, on the input only: `stepOneGeneration` succeeds whenever the root is valid, its
depth is at most 28, its window center lies within `2 ^ 30` of the origin, and the arena does not report a
failure. By `flat_stepOneGeneration_fails_only_when_full`, a failure means a node table is full.
-/
theorem flat_stepOneGeneration_succeeds {a : FlatHashLifeArena} (hwf : ArenaWF a) (ox oy : Int32) (root : UInt32)
    (hid : root < a.cellCount) (hd : (flatState a ox oy root).macroCell.depth ≤ 28)
    (hcx : -2 ^ 30 ≤ (windowCenter (flatState a ox oy root)).1 ∧ (windowCenter (flatState a ox oy root)).1 ≤ 2 ^ 30)
    (hcy : -2 ^ 30 ≤ (windowCenter (flatState a ox oy root)).2 ∧ (windowCenter (flatState a ox oy root)).2 ≤ 2 ^ 30)
    (hov : (a.stepOneGeneration ox oy root).2.overflow = 0) :
    (a.stepOneGeneration ox oy root).1.2.2 ≠ UNCOMPUTED :=
  (flat_stepOneGeneration_Impl hwf ox oy root).2.2.2 hid
    (flatStepInRange_of_center _ (flatState_isWellFormed hwf hid ox oy) hd hcx hcy) hov

/--
A full node table is the only failure one step can report: when the work stack `remapL4` has room for 26 frames
(130 entries) and the CellNode table has at most `2 ^ 28` slots (the Kotlin arenas have at least 256 entries and
`2 ^ 18` slots), `stepOneGeneration` raises the failure flag only if the arena had already failed or a node table is
full afterwards. Its step budget and work stack never run out. With `flat_stepOneGeneration_succeeds`, a step of
a valid, representable root in a healthy arena returns the next generation unless a node table fills up.
-/
theorem flat_stepOneGeneration_fails_only_when_full {a : FlatHashLifeArena} (hwf : ArenaWF a) (ox oy : Int32)
    (root : UInt32) (hsz : 130 ≤ a.remapL4.size) (hsz' : a.remapL4.size < 2 ^ 32)
    (hmask : a.cellMask.toNat < 2 ^ 28) :
    (a.stepOneGeneration ox oy root).2.overflow ≠ 0 →
      a.overflow ≠ 0 ∨ ArenaFull (a.stepOneGeneration ox oy root).2 :=
  stepOneGeneration_budget hwf ox oy root hsz hsz' hmask

/--
Master multi-generation theorem: `n` successive steps keep the arena well-formed and every existing node intact;
when they succeed they compute exactly `n` generations of the flat engine and `n` Conway generations of the
cells; and they succeed whenever the root's depth `d` satisfies `d + n ≤ 29`, its window center lies within
`2 ^ 30` of the origin, and the arena does not report a failure.
-/
theorem flat_stepOneGenerationN_correct (n : ℕ) {a : FlatHashLifeArena} (hwf : ArenaWF a) (ox oy : Int32)
    (root : UInt32) (hid : root < a.cellCount) :
    ArenaWF (a.stepOneGenerationN n ox oy root).2 ∧ NodesPreserved a (a.stepOneGenerationN n ox oy root).2 ∧
    ((a.stepOneGenerationN n ox oy root).1.2.2 ≠ UNCOMPUTED →
      (a.stepOneGenerationN n ox oy root).1.2.2 < (a.stepOneGenerationN n ox oy root).2.cellCount ∧
      flatState (a.stepOneGenerationN n ox oy root).2 (a.stepOneGenerationN n ox oy root).1.1
        (a.stepOneGenerationN n ox oy root).1.2.1 (a.stepOneGenerationN n ox oy root).1.2.2 =
        flatStepN n (flatState a ox oy root) ∧
      cellsEqual
        (hashLifeToGrid (flatState (a.stepOneGenerationN n ox oy root).2 (a.stepOneGenerationN n ox oy root).1.1
          (a.stepOneGenerationN n ox oy root).1.2.1 (a.stepOneGenerationN n ox oy root).1.2.2))
        (stepN n (hashLifeToGrid (flatState a ox oy root))) = true) ∧
    ((flatState a ox oy root).macroCell.depth + n ≤ 29 →
      (-2 ^ 30 ≤ (windowCenter (flatState a ox oy root)).1 ∧ (windowCenter (flatState a ox oy root)).1 ≤ 2 ^ 30) →
      (-2 ^ 30 ≤ (windowCenter (flatState a ox oy root)).2 ∧ (windowCenter (flatState a ox oy root)).2 ≤ 2 ^ 30) →
      (a.stepOneGenerationN n ox oy root).2.overflow = 0 → (a.stepOneGenerationN n ox oy root).1.2.2 ≠ UNCOMPUTED) :=
  have h := flat_stepOneGenerationN_Impl n hwf ox oy root hid
  have l := stepOneGenerationN_live n hwf ox oy root hid
  ⟨h.1, l.1, h.2, l.2⟩

/--
A full node table is the only failure `n` steps can report, under the capacity assumptions of
`flat_stepOneGeneration_fails_only_when_full`.
-/
theorem flat_stepOneGenerationN_fails_only_when_full (n : ℕ) {a : FlatHashLifeArena} (hwf : ArenaWF a)
    (ox oy : Int32) (root : UInt32) (hsz : 130 ≤ a.remapL4.size) (hsz' : a.remapL4.size < 2 ^ 32)
    (hmask : a.cellMask.toNat < 2 ^ 28) :
    (a.stepOneGenerationN n ox oy root).2.overflow ≠ 0 →
      a.overflow ≠ 0 ∨ ArenaFull (a.stepOneGenerationN n ox oy root).2 :=
  stepOneGenerationN_budget n hwf ox oy root hsz hsz' hmask

/--
Master theorem for the generation loop of `FlatLeanHashLifeAlgorithm`: every state it reaches after `k`
successful generations, through any interleaving of steps, failed steps, failure-flag clears and compactions
into fresh arenas, is a well-formed arena whose root denotes exactly `k` generations of the flat engine from the
start, with exactly `k` Conway generations of the starting cells.
-/
theorem flat_generationLoop_correct {st0 : HashLifeCellState} {k : ℕ} {a : FlatHashLifeArena} {ox oy : Int32}
    {root : UInt32} (h : FlatRun st0 k a ox oy root) :
    ArenaWF a ∧ root < a.cellCount ∧ flatState a ox oy root = flatStepN k st0 ∧
      cellsEqual (hashLifeToGrid (flatState a ox oy root)) (stepN k (hashLifeToGrid st0)) = true :=
  flatRun_correct h

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
A full node table is the only failure of a copy that has its scratch space: copying a valid root of `src` into a
non-failed destination for which `canCopySubgraphFrom` holds fails only when a node table of the destination is
full, provided the source has at most `2 ^ 28` CellNode slots. The copy's step budget and work stack never run
out.
-/
theorem flat_copySubgraphFrom_fails_only_when_full {src dst : FlatHashLifeArena} (hsrc : ArenaWF src)
    (hwf : ArenaWF dst) (rootId : UInt32) (copyMemos : Bool) (hid : rootId < src.cellCount)
    (hov : dst.overflow = 0) (hcan : dst.canCopySubgraphFrom src = true) (hmask : src.cellMask.toNat < 2 ^ 28)
    (h32 : dst.remapCell.size < 2 ^ 32) :
    (dst.copySubgraphFrom src rootId copyMemos).1 = UNCOMPUTED →
      ArenaFull (dst.copySubgraphFrom src rootId copyMemos).2 :=
  fun h => copySubgraphFrom_budget hsrc hwf hov hcan hid (by have := hsrc.cellCountLe; omega) h32 copyMemos
    (fun h0 => (copySubgraphFrom_spec hsrc hwf rootId copyMemos).2.1.mpr h0 h)

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
A full node table is the only failure of compaction that has its scratch space: compacting a valid root of a
non-failed `src` into a destination for which `canCopySubgraphFrom` holds fails only when a node table of the
destination is full, provided the source has at most `2 ^ 28` CellNode slots.
-/
theorem flat_compactRootFrom_fails_only_when_full {src dst : FlatHashLifeArena} (hsrc : ArenaWF src)
    (hwf : ArenaWF dst) (rootId : UInt32) (hid : rootId < src.cellCount) (hso : src.overflow = 0)
    (hcan : dst.canCopySubgraphFrom src = true) (hmask : src.cellMask.toNat < 2 ^ 28)
    (h32 : dst.remapCell.size < 2 ^ 32) :
    (dst.compactRootFrom src rootId).1.1 = UNCOMPUTED → ArenaFull (dst.compactRootFrom src rootId).2 :=
  compactRootFrom_budget hsrc hwf hid hso hcan (by have := hsrc.cellCountLe; omega) h32

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
Master theorem for `internMacroCellDag` in `FlatHashLifeCellState.kt`, whose memoized recursion `DagIntern` drives
`importMacroCellNode` node by node: importing a well-formed, hash-consistent HashLife state whose root is a
CellNode of depth at most 60 into a non-failed well-formed arena, from an empty memo table, keeps the arena
well-formed and every node in it, returns a root that denotes exactly the state at the same corner, and fails only
when a node table is full. The memo table is the Kotlin map from nodes to the ids they were imported as.
-/
theorem flat_internMacroCellDag_correct {a : FlatHashLifeArena} (hwf : ArenaWF a) (hov : a.overflow = 0)
    (st : HashLifeCellState) (ox oy : Int32) (hoff : st.offset = (ox.toInt, oy.toInt)) {d : ℕ}
    (hm : WFd st.macroCell d) (h5 : 5 ≤ d) (h60 : d ≤ 60) (H : HashOK st.macroCell)
    {id : UInt32} {memo : List (MacroCell × UInt32)} {a' : FlatHashLifeArena}
    (hrun : DagIntern [] a st.macroCell id memo a') :
    ArenaWF a' ∧ NodesPreserved a a' ∧
    (id ≠ UNCOMPUTED → id < a'.cellCount ∧ flatState a' ox oy id = st) ∧
    (id = UNCOMPUTED → ArenaFull a') :=
  internMacroCellDag_Impl hwf hov st ox oy hoff hm h5 h60 H hrun

/--
`cellsToMacroCell` builds the quadtree of a list of cells given by their keys (`coordKey`): at the corner of their
bounding box (in key coordinates), a well-formed, hash-consistent node of level between 5 and 32 whose state has
exactly the cells of the keys.
-/
theorem flat_cellsToMacroCell_correct (cells : Array UInt64) (hsz : cells.size < 2 ^ 32) :
    ∃ L, 5 ≤ L ∧ L ≤ 32 ∧ WFd (cellsToMacroCell cells).2.2 L ∧ HashOK (cellsToMacroCell cells).2.2 ∧
      ∀ c, c ∈ hashLifeToGrid ⟨(((cellsToMacroCell cells).1.toNat : ℤ) - 2 ^ 31,
        ((cellsToMacroCell cells).2.1.toNat : ℤ) - 2 ^ 31), (cellsToMacroCell cells).2.2⟩ ↔
        c ∈ cells.toList.map keyCoord :=
  cellsToMacroCell_Impl cells hsz

/--
Master theorem for `buildQuadtreeBottomUp` in `FlatHashLifeCellState.kt`, which imports `cellsToMacroCell` of the
cells' keys with the recursion of `internMacroCellDag`, at the corner `(ox, oy)` decoded from the returned key
coordinates: into a non-failed well-formed arena, it keeps the arena well-formed and every node in it; unless it
fails, the root has level at most 32 and its state has exactly the given cells; and it fails only when a node table is
full.
-/
theorem flat_buildQuadtree_correct {a : FlatHashLifeArena} (hwf : ArenaWF a) (hov : a.overflow = 0)
    (cells : Array UInt64) (hsz : cells.size < 2 ^ 32) (ox oy : Int32)
    (hox : ox.toInt = ((cellsToMacroCell cells).1.toNat : ℤ) - 2 ^ 31)
    (hoy : oy.toInt = ((cellsToMacroCell cells).2.1.toNat : ℤ) - 2 ^ 31) {id : UInt32}
    {memo : List (MacroCell × UInt32)} {a' : FlatHashLifeArena}
    (hrun : DagIntern [] a (cellsToMacroCell cells).2.2 id memo a') :
    ArenaWF a' ∧ NodesPreserved a a' ∧
    (id ≠ UNCOMPUTED → id < a'.cellCount ∧ cellLevelOf a' id ≤ 32 ∧
      ∀ c, c ∈ hashLifeToGrid (flatState a' ox oy id) ↔ c ∈ cells.toList.map keyCoord) ∧
    (id = UNCOMPUTED → ArenaFull a') :=
  buildQuadtree_Impl hwf hov cells hsz ox oy hox hoy hrun

/--
The cursor behind `FlatHashLifeCellState.getAliveCellsInWindow`: `cellCursorStepInWindow`, run from
`cellCursorStart` until the stack is empty, stops (after at most `stackWeight` steps) and emits, through its
`leafRowMask` chunks, the key (`coordKey`) of each live cell, of a root of level at most 61, that lies in the window
`[l, r) × [t, b)`, exactly once and in a fixed order, and nothing else.
-/
theorem flat_cellCursorInWindow_correct {a : FlatHashLifeArena} (hwf : ArenaWF a) {root : UInt32}
    (hid : root < a.cellCount) (hlv : cellLevelOf a root ≤ 61) (ox oy l t r b : Int32) :
    ∃ L : List Coord, L.Nodup ∧
      (∀ c, c ∈ L ↔ c ∈ hashLifeToGrid (flatState a ox oy root) ∧ InWindow l.toInt t.toInt r.toInt b.toInt c) ∧
      ∀ n, stackWeight (a.cellCursorStart root ox oy) ≤ n →
        cellCursorRun (a.cellCursorStepInWindow l t r b) n (a.cellCursorStart root ox oy) = (L.map coordKey, []) :=
  cellCursorInWindow_Impl hwf hid hlv ox oy l t r b

/--
The cursor behind `FlatHashLifeCellState.aliveCells`: `cellCursorStepAll`, run from `cellCursorStart` until the stack
is empty, stops and emits the key of each live cell with 32-bit coordinates, of a root of level at most 61, exactly
once and in a fixed order, and nothing else.
-/
theorem flat_cellCursorAll_correct {a : FlatHashLifeArena} (hwf : ArenaWF a) {root : UInt32}
    (hid : root < a.cellCount) (hlv : cellLevelOf a root ≤ 61) (ox oy : Int32) :
    ∃ L : List Coord, L.Nodup ∧
      (∀ c, c ∈ L ↔ c ∈ hashLifeToGrid (flatState a ox oy root) ∧ InWindow (-2 ^ 31) (-2 ^ 31) (2 ^ 31) (2 ^ 31) c) ∧
      ∀ n, stackWeight (a.cellCursorStart root ox oy) ≤ n →
        cellCursorRun a.cellCursorStepAll n (a.cellCursorStart root ox oy) = (L.map coordKey, []) :=
  cellCursorAll_Impl hwf hid hlv ox oy

/--
`FlatHashLifeCellState.fitsInIntRange`: running `cellCursorStepPastX` and `cellCursorStepPastY` from `cellCursorStart`
emits no cell exactly when every live cell of the state, of a root of level at most 61, has 32-bit coordinates.
-/
theorem flat_fitsInIntRange_correct {a : FlatHashLifeArena} (hwf : ArenaWF a) {root : UInt32}
    (hid : root < a.cellCount) (hlv : cellLevelOf a root ≤ 61) (ox oy : Int32) :
    ∀ n, stackWeight (a.cellCursorStart root ox oy) ≤ n →
      (((cellCursorRun a.cellCursorStepPastX n (a.cellCursorStart root ox oy)).1 = [] ∧
        (cellCursorRun a.cellCursorStepPastY n (a.cellCursorStart root ox oy)).1 = []) ↔
      ∀ c ∈ hashLifeToGrid (flatState a ox oy root), InWindow (-2 ^ 31) (-2 ^ 31) (2 ^ 31) (2 ^ 31) c) :=
  fitsInIntRange_Impl hwf hid hlv ox oy

/--
`FlatHashLifeCellState.fitsInIntRange`'s fast path: when `rootFitsInIntRange` holds (the root's square lies in the
32-bit coordinate range, checked in O(1)), every live cell of the state has 32-bit coordinates, so the cursors of
`flat_fitsInIntRange_correct` need not run.
-/
theorem flat_rootFitsInIntRange_sound {a : FlatHashLifeArena} (hwf : ArenaWF a) {root : UInt32} (ox oy : Int32)
    (h : a.rootFitsInIntRange root ox oy = true) :
    ∀ c ∈ hashLifeToGrid (flatState a ox oy root), InWindow (-2 ^ 31) (-2 ^ 31) (2 ^ 31) (2 ^ 31) c :=
  rootFitsInIntRange_Impl hwf ox oy h

/-- A step of the cursor emits no cell exactly when its mask is zero, where the Kotlin iterators skip it. -/
theorem flat_chunkKeys_eq_nil_iff (mask : UInt64) (x0 y0 : Int64) : chunkKeys mask x0 y0 = [] ↔ mask = 0 :=
  chunkKeys_eq_nil_iff mask x0 y0

/-- The keys the cursor emits decode (`keyCoord`, as Kotlin decodes them) to their cells. -/
theorem flat_keyCoord_coordKey {c : Coord} (h : InWindow (-2 ^ 31) (-2 ^ 31) (2 ^ 31) (2 ^ 31) c) :
    keyCoord (coordKey c) = c :=
  keyCoord_coordKey h

/--
Replacing an arena's scratch tables (`withScratch`, as `FlatHashLifeCellState.kt` does to make room for a copy) keeps
it well-formed, with the same nodes, failure flag and states, so it can start a generation loop (`FlatRun.start`) or
receive a compaction (`FlatRun.compact`) as before.
-/
theorem flat_withScratch_correct {a : FlatHashLifeArena} (hwf : ArenaWF a) (l4 cell : Array UInt32) :
    ArenaWF (a.withScratch l4 cell) ∧ NodesPreserved a (a.withScratch l4 cell) ∧
    (a.withScratch l4 cell).overflow = a.overflow ∧ (a.withScratch l4 cell).cellCount = a.cellCount ∧
    ∀ (ox oy : Int32) (root : UInt32), flatState (a.withScratch l4 cell) ox oy root = flatState a ox oy root :=
  withScratch_Impl hwf l4 cell

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
