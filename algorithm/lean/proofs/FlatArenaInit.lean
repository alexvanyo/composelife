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
import proofs.MacroCellProofs
import proofs.HashLifeProofs
import proofs.BitEquivalenceProofs
import proofs.FlatArenaBasics
import proofs.FlatArenaIntern

local notation "ℕ" => Nat

namespace Algorithm

/-!
# Flat HashLife arena: initialization

`initEmptyNodes` turns any freshly allocated arena whose tables are large enough into a well-formed arena with
the pre-interned empty nodes of levels 4 through 60.
-/

/--
CellNode slot `k` holds the empty node of level `k + 5` (with a correct population and step memo).
-/
def EmptySlot (a : FlatHashLifeArena) (k : ℕ) : Prop :=
  a.cellNw[k]! = emptyNodeForLevel (k + 4).toUInt32 ∧ a.cellNe[k]! = emptyNodeForLevel (k + 4).toUInt32 ∧
  a.cellSw[k]! = emptyNodeForLevel (k + 4).toUInt32 ∧ a.cellSe[k]! = emptyNodeForLevel (k + 4).toUInt32 ∧
  (a.cellLevel[k]!).toNat = k + 5 ∧ a.cellPop[k]! = 0 ∧
  a.cellStepRes[k]! = emptyNodeForLevel (k + 4).toUInt32

theorem emptyNodeForLevel_succ {i : UInt32} (h1 : 1 ≤ i.toNat) (h56 : i.toNat < 56) :
    emptyNodeForLevel (i.toNat + 4).toUInt32 = i - 1 := by
  obtain ⟨k, hk⟩ : ∃ k, i.toNat = k + 1 := ⟨i.toNat - 1, by omega⟩
  rw [hk, show k + 1 + 4 = k + 5 by omega, emptyNodeForLevel_of_ge (by omega)]
  apply u32_eq_of_toNat
  rw [u32_ofNat_toNat (by omega), u32_toNat_sub (by simp; omega)]
  simp only [UInt32.toNat_one]
  omega

theorem initEmptyNodesLoop_spec (n : ℕ) :
    ∀ (a : FlatHashLifeArena) (fuel i : UInt32), fuel.toNat ≤ n → 1 ≤ i.toNat → i.toNat ≤ 56 →
      56 ≤ i.toNat + fuel.toNat →
      56 ≤ a.cellNw.size → 56 ≤ a.cellNe.size → 56 ≤ a.cellSw.size → 56 ≤ a.cellSe.size →
      56 ≤ a.cellLevel.size → 56 ≤ a.cellPop.size → 56 ≤ a.cellStepRes.size →
      (∀ k, k < i.toNat → EmptySlot a k) →
      ∃ (nw ne sw se : Array UInt32) (lv : Array UInt8) (pop : Array UInt64) (sr : Array UInt32),
        a.initEmptyNodesLoop fuel i = { a with
          cellNw := nw, cellNe := ne, cellSw := sw, cellSe := se,
          cellLevel := lv, cellPop := pop, cellStepRes := sr } ∧
        nw.size = a.cellNw.size ∧ ne.size = a.cellNe.size ∧ sw.size = a.cellSw.size ∧ se.size = a.cellSe.size ∧
        lv.size = a.cellLevel.size ∧ pop.size = a.cellPop.size ∧ sr.size = a.cellStepRes.size ∧
        ∀ k, k < 56 → EmptySlot (a.initEmptyNodesLoop fuel i) k := by
  induction n with
  | zero =>
    intro a fuel i hn h1 h56 hf s1 s2 s3 s4 s5 s6 s7 hs
    have : fuel = 0 := u32_eq_of_toNat (by simp; omega)
    subst this
    rw [FlatHashLifeArena.initEmptyNodesLoop.eq_1]
    simp only [dite_true]
    exact ⟨_, _, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun k hk => hs k (by simp at hf; omega)⟩
  | succ n ih =>
    intro a fuel i hn h1 h56 hf s1 s2 s3 s4 s5 s6 s7 hs
    rw [FlatHashLifeArena.initEmptyNodesLoop.eq_1]
    by_cases hf0 : fuel = 0
    · subst hf0
      simp only [dite_true]
      exact ⟨_, _, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun k hk => hs k (by simp at hf; omega)⟩
    simp only [hf0, dite_false]
    split
    · rename_i hge
      rw [ge_iff_le, u32_le_iff] at hge
      have : (56 : UInt32).toNat = 56 := rfl
      exact ⟨_, _, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun k hk => hs k (by omega)⟩
    · rename_i hlt
      have hi : i.toNat < 56 := by
        have h' : ¬ (56 : UInt32) ≤ i := hlt
        rw [u32_le_iff] at h'
        have : (56 : UInt32).toNat = 56 := rfl
        omega
      have hfuel : (fuel - 1).toNat = fuel.toNat - 1 := u32_toNat_sub (by simp; omega)
      have hi1 : (i + 1).toNat = i.toNat + 1 := u32_toNat_add_one (by omega)
      obtain ⟨nw, ne, sw, se, lv, pop, sr, heq, z1, z2, z3, z4, z5, z6, z7, hall⟩ :=
        ih { a with
            cellNw := a.cellNw.set! i.toNat (i - 1), cellNe := a.cellNe.set! i.toNat (i - 1),
            cellSw := a.cellSw.set! i.toNat (i - 1), cellSe := a.cellSe.set! i.toNat (i - 1),
            cellLevel := a.cellLevel.set! i.toNat (i + 5).toUInt8, cellPop := a.cellPop.set! i.toNat 0,
            cellStepRes := a.cellStepRes.set! i.toNat (i - 1) }
          (fuel - 1) (i + 1) (by omega) (by omega) (by omega) (by omega)
          (by simp only [size_set!]; exact s1) (by simp only [size_set!]; exact s2)
          (by simp only [size_set!]; exact s3) (by simp only [size_set!]; exact s4)
          (by simp only [size_set!]; exact s5) (by simp only [size_set!]; exact s6)
          (by simp only [size_set!]; exact s7) (by
            intro k hk
            rw [hi1] at hk
            simp only [EmptySlot]
            by_cases hki : k = i.toNat
            · subst hki
              rw [getElem!_set!_self _ _ _ (by omega), getElem!_set!_self _ _ _ (by omega),
                getElem!_set!_self _ _ _ (by omega), getElem!_set!_self _ _ _ (by omega),
                getElem!_set!_self _ _ _ (by omega), getElem!_set!_self _ _ _ (by omega),
                getElem!_set!_self _ _ _ (by omega), emptyNodeForLevel_succ h1 hi]
              refine ⟨rfl, rfl, rfl, rfl, ?_, rfl, rfl⟩
              rw [UInt32.toNat_toUInt8, u32_toNat_add (by simp; omega)]
              simp only [UInt32.reduceToNat]
              omega
            · obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hs k (by omega)
              rw [getElem!_set!_ne _ _ _ _ (Ne.symm hki), getElem!_set!_ne _ _ _ _ (Ne.symm hki),
                getElem!_set!_ne _ _ _ _ (Ne.symm hki), getElem!_set!_ne _ _ _ _ (Ne.symm hki),
                getElem!_set!_ne _ _ _ _ (Ne.symm hki), getElem!_set!_ne _ _ _ _ (Ne.symm hki),
                getElem!_set!_ne _ _ _ _ (Ne.symm hki)]
              exact ⟨e1, e2, e3, e4, e5, e6, e7⟩)
      refine ⟨nw, ne, sw, se, lv, pop, sr, heq, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hall⟩ <;>
        simp only [z1, z2, z3, z4, z5, z6, z7, size_set!]

/--
Running the empty-node loop on an arena whose Level 4 empty node and level 5 empty node (slot 0) are in place
yields a well-formed arena.
-/
theorem initEmptyNodesLoop_wf (b : FlatHashLifeArena)
    (hl4 :
      b.l4Mask.toNat + 1 ≤ b.l4Nw.size ∧ b.l4Mask.toNat + 1 ≤ b.l4Ne.size ∧
      b.l4Mask.toNat + 1 ≤ b.l4Sw.size ∧ b.l4Mask.toNat + 1 ≤ b.l4Se.size ∧
      b.l4Mask.toNat + 1 ≤ b.l4StepRes.size ∧ b.l4Mask.toNat + 1 ≤ b.l4HasRes.size)
    (hcell :
      b.cellMask.toNat + 1 ≤ b.cellNw.size ∧ b.cellMask.toNat + 1 ≤ b.cellNe.size ∧
      b.cellMask.toNat + 1 ≤ b.cellSw.size ∧ b.cellMask.toNat + 1 ≤ b.cellSe.size ∧
      b.cellMask.toNat + 1 ≤ b.cellLevel.size ∧ b.cellMask.toNat + 1 ≤ b.cellPop.size ∧
      b.cellMask.toNat + 1 ≤ b.cellStepRes.size)
    (hmask : 55 ≤ b.cellMask.toNat) (hl4c : b.l4Count = 1) (hcc : b.cellCount = 56)
    (hl40 : b.l4Nw[0]! = 0 ∧ b.l4Ne[0]! = 0 ∧ b.l4Sw[0]! = 0 ∧ b.l4Se[0]! = 0)
    (hmemo0 : b.l4HasRes[0]! = 1 → b.l4StepRes[0]! = 0) (hs0 : EmptySlot b 0) :
    ArenaWF (b.initEmptyNodesLoop 60 1) ∧ (b.initEmptyNodesLoop 60 1).overflow = b.overflow ∧
      (b.initEmptyNodesLoop 60 1).l4Count = b.l4Count ∧ (b.initEmptyNodesLoop 60 1).cellCount = b.cellCount ∧
      (b.initEmptyNodesLoop 60 1).l4Mask = b.l4Mask ∧ (b.initEmptyNodesLoop 60 1).cellMask = b.cellMask ∧
      (b.initEmptyNodesLoop 60 1).remapL4 = b.remapL4 ∧ (b.initEmptyNodesLoop 60 1).remapCell = b.remapCell := by
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := hl4
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hcell
  obtain ⟨nw, ne, sw, se, lv, pop, sr, heq, z1, z2, z3, z4, z5, z6, z7, hall⟩ :=
    initEmptyNodesLoop_spec 60 b 60 1 (by simp) (by simp) (by simp) (by simp) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (fun k hk => by
        have hk0 : k = 0 := by simp at hk; omega
        subst hk0
        exact hs0)
  rw [heq] at hall ⊢
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hc56 : (56 : UInt32).toNat = 56 := rfl
  have he : EmptiesWF { b with
      cellNw := nw, cellNe := ne, cellSw := sw, cellSe := se, cellLevel := lv, cellPop := pop,
      cellStepRes := sr } := by
    refine ⟨⟨by rw [hl4c]; decide, hl40⟩, by dsimp only; rw [hcc]; decide, fun k hk => ?_⟩
    obtain ⟨e1, e2, e3, e4, e5, _, _⟩ := hall k hk
    refine ⟨?_, e1, e2, e3, e4⟩
    unfold cellLevelOf
    dsimp only
    rw [u32_ofNat_toNat (by omega)]
    exact e5
  -- every CellNode slot is the empty node of its level
  have hslot : ∀ id : UInt32, id < (56 : UInt32) →
      EmptySlot { b with
        cellNw := nw, cellNe := ne, cellSw := sw, cellSe := se, cellLevel := lv, cellPop := pop,
        cellStepRes := sr } id.toNat ∧
      NodeIs { b with
        cellNw := nw, cellNe := ne, cellSw := sw, cellSe := se, cellLevel := lv, cellPop := pop,
        cellStepRes := sr } (id.toNat + 1) id (emptyNode (id.toNat + 5)) := by
    intro id hid
    have hk := u32_lt_iff.mp hid
    rw [hc56] at hk
    have hn := NodeIs.emptyCell_of he id.toNat hk
    rw [u32_eq_of_toNat (u32_ofNat_toNat (u32_toNat_lt id))] at hn
    exact ⟨hall id.toNat hk, hn⟩
  have cs : b.cellMask.toNat + 1 ≤ nw.size ∧ b.cellMask.toNat + 1 ≤ ne.size ∧
      b.cellMask.toNat + 1 ≤ sw.size ∧ b.cellMask.toNat + 1 ≤ se.size ∧
      b.cellMask.toNat + 1 ≤ lv.size ∧ b.cellMask.toNat + 1 ≤ pop.size ∧
      b.cellMask.toNat + 1 ≤ sr.size := by
    omega
  refine ⟨⟨l1, l2, l3, l4, l5, l6⟩, cs,
    by dsimp only; rw [hl4c]; simp, by dsimp only; rw [hcc, hc56]; omega, he.l4Empty, he.cellEmptyCount,
    he.cellEmpty, ?_, ?_, ?_, ?_⟩
  · -- the Level 4 memo of the empty node
    intro id hid hhas
    have h0 : id = 0 := by
      have := u32_lt_iff.mp hid
      dsimp only at this
      rw [hl4c] at this
      apply u32_eq_of_toNat
      simp at this ⊢
      omega
    subst h0
    obtain ⟨e1, e2, e3, e4⟩ := hl40
    dsimp only at hhas ⊢
    simp only [UInt32.toNat_zero] at hhas ⊢
    rw [hmemo0 hhas, e1, e2, e3, e4, computeLevel4NextGen16x16UInt_zero_eq]
  · -- children
    intro id hid
    rw [show (({ b with
        cellNw := nw, cellNe := ne, cellSw := sw, cellSe := se, cellLevel := lv, cellPop := pop,
        cellStepRes := sr } : FlatHashLifeArena)).cellCount = 56 from hcc] at hid
    obtain ⟨⟨e1, e2, e3, e4, e5, _, _⟩, hn⟩ := hslot id hid
    have hk := u32_lt_iff.mp hid
    rw [hc56] at hk
    unfold CellChildrenWF cellLevelOf
    dsimp only at e1 e2 e3 e4 e5 ⊢
    rw [e5, e1, e2, e3, e4]
    refine ⟨by omega, fun h5 => ?_, fun h5 => ?_⟩
    · have h0 : id.toNat = 0 := by omega
      rw [h0]
      have : (0 + 4 : ℕ).toUInt32 = (4 : ℕ).toUInt32 := rfl
      rw [this, emptyNodeForLevel_four, hl4c]
      exact ⟨by decide, by decide, by decide, by decide⟩
    · obtain ⟨j, hj⟩ : ∃ j, id.toNat = j + 1 := ⟨id.toNat - 1, by omega⟩
      rw [hj, show j + 1 + 4 = j + 5 by omega, emptyNodeForLevel_of_ge (by omega)]
      have hjl : j.toUInt32 < 56 := by rw [u32_lt_iff, u32_ofNat_toNat (by omega), hc56]; omega
      obtain ⟨⟨_, _, _, _, ej, _, _⟩, _⟩ := hslot j.toUInt32 hjl
      dsimp only at ej
      rw [u32_ofNat_toNat (by omega)] at ej
      have hcj : j.toUInt32 < b.cellCount := by rw [hcc]; exact hjl
      exact ⟨⟨hcj, by rw [u32_ofNat_toNat (by omega)]; omega⟩, ⟨hcj, by rw [u32_ofNat_toNat (by omega)]; omega⟩,
        ⟨hcj, by rw [u32_ofNat_toNat (by omega)]; omega⟩, ⟨hcj, by rw [u32_ofNat_toNat (by omega)]; omega⟩⟩
  · -- populations
    intro id hid
    rw [show (({ b with
        cellNw := nw, cellNe := ne, cellSw := sw, cellSe := se, cellLevel := lv, cellPop := pop,
        cellStepRes := sr } : FlatHashLifeArena)).cellCount = 56 from hcc] at hid
    obtain ⟨⟨_, _, _, _, _, e6, _⟩, hn⟩ := hslot id hid
    rw [hn.denoteCell_eq, e6, macroCell_size_emptyNode_Impl]
  · -- step memos
    intro id hid _
    rw [show (({ b with
        cellNw := nw, cellNe := ne, cellSw := sw, cellSe := se, cellLevel := lv, cellPop := pop,
        cellStepRes := sr } : FlatHashLifeArena)).cellCount = 56 from hcc] at hid
    obtain ⟨⟨_, _, _, _, _, _, e7⟩, hn⟩ := hslot id hid
    have hk := u32_lt_iff.mp hid
    rw [hc56] at hk
    rw [e7, hn.denoteCell_eq, hn.level, show id.toNat + 5 - 5 = id.toNat by omega, hashLifeStep_emptyNode_Impl]
    exact NodeIs.emptyForLevel_of he id.toNat (by omega)

/--
`initEmptyNodes` produces a well-formed arena with no failure, one Level 4 node, and the 56 pre-interned
empty CellNodes, provided every node table has room for its mask (and the CellNode table for the 56 empty
nodes). It does not touch the masks or the scratch tables.
-/
theorem initEmptyNodes_spec {a : FlatHashLifeArena}
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
      a.initEmptyNodes.remapCell = a.remapCell := by
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := hl4
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hcell
  unfold FlatHashLifeArena.initEmptyNodes
  dsimp only
  refine initEmptyNodesLoop_wf _ ?_ ?_ hmask rfl rfl ?_ ?_ ?_
  · simp only [size_set!]
    omega
  · simp only [size_set!]
    omega
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> exact getElem!_set!_self _ _ _ (by omega)
  · intro _
    exact getElem!_set!_self _ _ _ (by omega)
  · simp only [EmptySlot]
    rw [getElem!_set!_self _ _ _ (by omega), getElem!_set!_self _ _ _ (by omega),
      getElem!_set!_self _ _ _ (by omega), getElem!_set!_self _ _ _ (by omega),
      getElem!_set!_self _ _ _ (by omega), getElem!_set!_self _ _ _ (by omega),
      getElem!_set!_self _ _ _ (by omega)]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Algorithm
