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
import proofs.FlatArenaBasics
import proofs.FlatArenaIntern
import proofs.FlatArenaExtract
import proofs.FlatArenaStep
import proofs.FlatArenaGeneration
import proofs.FlatArenaGrid
import proofs.FlatArenaCopy
import proofs.FlatArenaQuery
import proofs.FlatArenaInit
import proofs.FlatArenaImport

local notation "ℕ" => Nat

namespace Algorithm

/-!
# Flat HashLife arena: master theorem proofs

Proofs of the master theorems in `theorems/FlatHashLifeTheorems.lean`, stated only in terms of `ArenaWF`,
`NodesPreserved`, the denotation of arena nodes, and the reference HashLife and grid semantics.
-/

theorem u32_mul_toNat {x y : UInt32} (h : x.toNat * y.toNat < 2 ^ 32) : (x * y).toNat = x.toNat * y.toNat := by
  rw [UInt32.toNat_mul, Nat.mod_eq_of_lt h]

theorem flat_isNearCapacity_Impl {a : FlatHashLifeArena} (hwf : ArenaWF a) (hl : a.l4Mask.toNat < 2 ^ 29)
    (hc : a.cellMask.toNat < 2 ^ 29) :
    a.isNearCapacity = true ↔
      3 * (a.l4Mask.toNat + 1) ≤ 4 * a.l4Count.toNat ∨ 3 * (a.cellMask.toNat + 1) ≤ 4 * a.cellCount.toNat := by
  have h1 := hwf.l4CountLe
  have h2 := hwf.cellCountLe
  unfold FlatHashLifeArena.isNearCapacity
  have m1 : (a.l4Mask + 1).toNat = a.l4Mask.toNat + 1 := u32_toNat_add_one (by omega)
  have m2 : (a.cellMask + 1).toNat = a.cellMask.toNat + 1 := u32_toNat_add_one (by omega)
  simp only [Bool.or_eq_true, decide_eq_true_eq, ge_iff_le, u32_le_iff,
    u32_mul_toNat (x := a.l4Count) (y := 4) (by simp; omega),
    u32_mul_toNat (x := a.cellCount) (y := 4) (by simp; omega),
    u32_mul_toNat (x := a.l4Mask + 1) (y := 3) (by rw [m1]; simp; omega),
    u32_mul_toNat (x := a.cellMask + 1) (y := 3) (by rw [m2]; simp; omega), m1, m2, UInt32.reduceToNat]
  omega

theorem flat_isOver60Percent_Impl {a : FlatHashLifeArena} (hwf : ArenaWF a) (hl : a.l4Mask.toNat < 2 ^ 29)
    (hc : a.cellMask.toNat < 2 ^ 29) :
    a.isOver60Percent = true ↔
      3 * (a.l4Mask.toNat + 1) ≤ 5 * a.l4Count.toNat ∨ 3 * (a.cellMask.toNat + 1) ≤ 5 * a.cellCount.toNat := by
  have h1 := hwf.l4CountLe
  have h2 := hwf.cellCountLe
  unfold FlatHashLifeArena.isOver60Percent
  have m1 : (a.l4Mask + 1).toNat = a.l4Mask.toNat + 1 := u32_toNat_add_one (by omega)
  have m2 : (a.cellMask + 1).toNat = a.cellMask.toNat + 1 := u32_toNat_add_one (by omega)
  simp only [Bool.or_eq_true, decide_eq_true_eq, ge_iff_le, u32_le_iff,
    u32_mul_toNat (x := a.l4Count) (y := 5) (by simp; omega),
    u32_mul_toNat (x := a.cellCount) (y := 5) (by simp; omega),
    u32_mul_toNat (x := a.l4Mask + 1) (y := 3) (by rw [m1]; simp; omega),
    u32_mul_toNat (x := a.cellMask + 1) (y := 3) (by rw [m2]; simp; omega), m1, m2, UInt32.reduceToNat]
  omega

theorem flat_initEmptyNodes_Impl {a : FlatHashLifeArena}
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
  initEmptyNodes_spec hl4 hcell hmask

theorem flat_internLevel4_Impl {a : FlatHashLifeArena} (hwf : ArenaWF a) (nw ne sw se : UInt64) :
    ArenaWF (a.internLevel4 nw ne sw se).2 ∧ NodesPreserved a (a.internLevel4 nw ne sw se).2 ∧
    ((a.internLevel4 nw ne sw se).2.overflow = 0 →
      (a.internLevel4 nw ne sw se).1 < (a.internLevel4 nw ne sw se).2.l4Count ∧
      denoteLevel4 (a.internLevel4 nw ne sw se).2 (a.internLevel4 nw ne sw se).1 = makeLevel4Node nw ne sw se) := by
  obtain ⟨g, hn⟩ := internLevel4_spec hwf nw ne sw se
  exact ⟨g.wf, g.nodes hwf, fun h => hn h⟩

theorem flat_internCellNode_Impl {a : FlatHashLifeArena} (hwf : ArenaWF a) {lvl : UInt8} {h : ℕ}
    (hl : lvl.toNat = h + 5) {nw ne sw se : UInt32} {m1 m2 m3 m4 : MacroCell}
    (h1 : NodeIs a h nw m1) (h2 : NodeIs a h ne m2) (h3 : NodeIs a h sw m3) (h4 : NodeIs a h se m4) :
    ArenaWF (a.internCellNode lvl nw ne sw se).2 ∧ NodesPreserved a (a.internCellNode lvl nw ne sw se).2 ∧
    ((a.internCellNode lvl nw ne sw se).2.overflow = 0 →
      NodeIs (a.internCellNode lvl nw ne sw se).2 (h + 1) (a.internCellNode lvl nw ne sw se).1
        (makeCellNode m1 m2 m3 m4)) := by
  obtain ⟨g, hn⟩ := internCellNode_spec hwf hl h1 h2 h3 h4
  exact ⟨g.wf, g.nodes hwf, hn⟩

theorem flat_importLevel4Root_Impl {a : FlatHashLifeArena} (hwf : ArenaWF a) (ox oy : Int32)
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
      (a.importLevel4Root ox oy nw ne sw se).1.2.2 ≠ UNCOMPUTED) := by
  obtain ⟨g, hs, hc⟩ := importLevel4Root_spec hwf ox oy nw ne sw se
  refine ⟨g.wf, g.nodes hwf, fun hok => ?_, hc⟩
  obtain ⟨h1, h2, h3⟩ := hs hok
  exact ⟨h1, h2, h3, importLevel4Root_grid hwf ox oy nw ne sw se hok⟩

theorem flat_stepOneGeneration_Impl {a : FlatHashLifeArena} (hwf : ArenaWF a) (ox oy : Int32) (root : UInt32) :
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
      (a.stepOneGeneration ox oy root).2.overflow = 0 → (a.stepOneGeneration ox oy root).1.2.2 ≠ UNCOMPUTED) := by
  obtain ⟨l, hs, hc⟩ := stepOneGeneration_spec hwf ox oy root
  refine ⟨l.wf, NodesPreserved.of_extends hwf l.ext, fun hok => ?_, hc⟩
  obtain ⟨h1, _, h3, h4, _⟩ := hs hok
  exact ⟨h1, h3, h4, stepOneGeneration_grid hwf ox oy root hok⟩

theorem flat_stepOneGenerationN_Impl (n : ℕ) {a : FlatHashLifeArena} (hwf : ArenaWF a) (ox oy : Int32)
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
  stepOneGenerationN_spec n hwf ox oy root hid

theorem flat_nextGeneration_Impl (st : HashLifeCellState)
    (h_wf : isWellFormed st.macroCell) (h_depth : st.macroCell.depth ≤ 30) :
    isWellFormed (flatNextGeneration st).macroCell ∧
    ∀ c, c ∈ hashLifeToGrid (flatNextGeneration st) ↔ c ∈ stepGrid (hashLifeToGrid st) :=
  flatNextGeneration_correct st h_wf h_depth

theorem flat_canCopySubgraphFrom_Impl (dst src : FlatHashLifeArena) (h1 : dst.remapL4.size < 2 ^ 32)
    (h2 : dst.remapCell.size < 2 ^ 32) :
    dst.canCopySubgraphFrom src = true ↔
      src.l4Count.toNat ≤ dst.remapL4.size ∧ src.cellCount.toNat + 256 ≤ dst.remapCell.size := by
  unfold FlatHashLifeArena.canCopySubgraphFrom
  have e1 : dst.remapL4.size.toUInt32.toNat = dst.remapL4.size := u32_ofNat_toNat h1
  have e2 : dst.remapCell.size.toUInt32.toNat = dst.remapCell.size := u32_ofNat_toNat h2
  have hd : copyStackDepth.toNat = 256 := rfl
  simp only [Bool.and_eq_true, decide_eq_true_eq, ge_iff_le, u32_le_iff, e1, e2, hd]
  by_cases h : 256 ≤ dst.remapCell.size
  · rw [u32_toNat_sub (by rw [e2, hd]; omega), e2, hd]
    omega
  · constructor
    · intro hh
      omega
    · intro hh
      omega

/--
Shared consequences of a successful copy: the copied root denotes the same MacroCell at the same level, so it
represents the same cells at any offset.
-/
theorem copied_root {src d : FlatHashLifeArena} (hsrc : ArenaWF src) {rootId newId : UInt32}
    (hid : rootId < src.cellCount) (hn : NodeIs d (cellLevelOf src rootId - 4) newId (denoteCell src rootId)) :
    newId < d.cellCount ∧ cellLevelOf d newId = cellLevelOf src rootId ∧ denoteCell d newId = denoteCell src rootId ∧
      ∀ ox oy : Int32, flatState d ox oy newId = flatState src ox oy rootId := by
  obtain ⟨k, hk, _⟩ := NodeIs.of_lt' hsrc hid
  rw [hk, show k + 5 - 4 = k + 1 by omega] at hn
  refine ⟨hn.lt_cell, by rw [hn.level, hk], hn.denoteCell_eq, fun ox oy => ?_⟩
  unfold flatState
  rw [hn.denoteCell_eq]

theorem flat_copySubgraphFrom_Impl {src dst : FlatHashLifeArena} (hsrc : ArenaWF src) (hwf : ArenaWF dst)
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
        (dst.copySubgraphFrom src rootId copyMemos).1 = flatState src ox oy rootId) := by
  obtain ⟨sc, hiff, hs⟩ := copySubgraphFrom_spec hsrc hwf rootId copyMemos
  refine ⟨sc.wf, NodesPreserved.of_extends hwf sc.ext, sc.remapL4Size, sc.remapCellSize, hiff, fun hok => ?_⟩
  obtain ⟨_, hid, hn⟩ := hs (hiff.mp hok)
  exact ⟨hid, copied_root hsrc hid hn⟩

theorem flat_compactRootFrom_Impl {src dst : FlatHashLifeArena} (hsrc : ArenaWF src) (hwf : ArenaWF dst)
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
      (dst.compactRootFrom src rootId).1.1 ≠ UNCOMPUTED) := by
  obtain ⟨sc, hs, hc⟩ := compactRootFrom_spec hsrc hwf rootId
  refine ⟨sc.wf, NodesPreserved.of_extends hwf sc.ext, sc.remapL4Size, sc.remapCellSize, fun hok => ?_, hc⟩
  obtain ⟨hov, hid, hn⟩ := hs hok
  exact ⟨hov, hid, copied_root hsrc hid hn⟩

theorem flat_containsCell_Impl {a : FlatHashLifeArena} (hwf : ArenaWF a) {root : UInt32}
    (hid : root < a.cellCount) (ox oy x y : Int32) :
    a.containsCell root (x.toInt64 - ox.toInt64) (y.toInt64 - oy.toInt64) = true ↔
      (x.toInt, y.toInt) ∈ hashLifeToGrid (flatState a ox oy root) :=
  containsCell_grid hwf hid ox oy x y

end Algorithm
