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
import Algorithm.FlatHashLife
import Algorithm.HashLifeEquivalence
import AlgorithmDefs
import proofs.SemanticModelProofs

local notation "ℕ" => Nat

namespace Algorithm

/-!
# Flat HashLife arena: basic lemmas

Array, fixed-width integer, and denotation lemmas shared by the flat arena refinement proofs.
-/

-- =========================================================================
-- Arrays
-- =========================================================================

theorem getElem!_setIfInBounds_eq {α : Type} [Inhabited α] (a : Array α) (i j : ℕ) (v : α) :
    (a.setIfInBounds i v)[j]! = if i = j ∧ i < a.size then v else a[j]! := by
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases h1 : i = j
  · subst h1
    by_cases h2 : i < a.size
    · simp [h2]
    · simp [h2]
  · simp [h1]

theorem getElem!_setIfInBounds_self {α : Type} [Inhabited α] (a : Array α) (i : ℕ) (v : α)
    (h : i < a.size) : (a.setIfInBounds i v)[i]! = v := by
  rw [getElem!_setIfInBounds_eq]
  simp [h]

theorem getElem!_setIfInBounds_ne {α : Type} [Inhabited α] (a : Array α) (i j : ℕ) (v : α)
    (h : i ≠ j) : (a.setIfInBounds i v)[j]! = a[j]! := by
  rw [getElem!_setIfInBounds_eq]
  simp [h]

theorem getElem!_set!_eq {α : Type} [Inhabited α] (a : Array α) (i j : ℕ) (v : α) :
    (a.set! i v)[j]! = if i = j ∧ i < a.size then v else a[j]! :=
  getElem!_setIfInBounds_eq a i j v

theorem getElem!_set!_self {α : Type} [Inhabited α] (a : Array α) (i : ℕ) (v : α)
    (h : i < a.size) : (a.set! i v)[i]! = v :=
  getElem!_setIfInBounds_self a i v h

theorem getElem!_set!_ne {α : Type} [Inhabited α] (a : Array α) (i j : ℕ) (v : α)
    (h : i ≠ j) : (a.set! i v)[j]! = a[j]! :=
  getElem!_setIfInBounds_ne a i j v h

theorem size_set! {α : Type} (a : Array α) (i : ℕ) (v : α) : (a.set! i v).size = a.size := by
  simp [Array.set!]

-- =========================================================================
-- Fixed-width integers
-- =========================================================================

theorem u32_lt_iff {a b : UInt32} : a < b ↔ a.toNat < b.toNat := UInt32.lt_iff_toNat_lt

theorem u32_le_iff {a b : UInt32} : a ≤ b ↔ a.toNat ≤ b.toNat := UInt32.le_iff_toNat_le

theorem u32_ge_false {a b : UInt32} : (a ≥ b) = False ↔ a.toNat < b.toNat := by
  rw [ge_iff_le, u32_le_iff]
  simp

theorem u32_toNat_lt (a : UInt32) : a.toNat < 2 ^ 32 := UInt32.toNat_lt a

theorem u32_toNat_add_one {a : UInt32} (h : a.toNat + 1 < 2 ^ 32) : (a + 1).toNat = a.toNat + 1 := by
  rw [UInt32.toNat_add]
  simp only [UInt32.toNat_one]
  omega

theorem u32_toNat_add {a b : UInt32} (h : a.toNat + b.toNat < 2 ^ 32) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt32.toNat_add]
  omega

theorem u32_toNat_sub {a b : UInt32} (h : b.toNat ≤ a.toNat) : (a - b).toNat = a.toNat - b.toNat := by
  rw [UInt32.toNat_sub_of_le]
  exact u32_le_iff.mpr h

theorem u32_ofNat_toNat {n : ℕ} (h : n < 2 ^ 32) : n.toUInt32.toNat = n := by
  rw [Nat.toUInt32, UInt32.toNat_ofNat']
  omega

theorem u32_eq_of_toNat {a b : UInt32} (h : a.toNat = b.toNat) : a = b := UInt32.toNat.inj h

theorem u32_ne_of_toNat {a b : UInt32} (h : a.toNat ≠ b.toNat) : a ≠ b := by
  intro e
  exact h (congrArg UInt32.toNat e)

theorem uncomputed_toNat : UNCOMPUTED.toNat = 2 ^ 32 - 1 := rfl

theorem ne_uncomputed_of_lt {id c : UInt32} (h : id < c) : id ≠ UNCOMPUTED := by
  intro e
  subst e
  have := u32_lt_iff.mp h
  have := u32_toNat_lt c
  rw [uncomputed_toNat] at *
  omega

theorem u8_toNat_lt (a : UInt8) : a.toNat < 2 ^ 8 := UInt8.toNat_lt a

theorem u8_toNat_sub {a b : UInt8} (h : b.toNat ≤ a.toNat) : (a - b).toNat = a.toNat - b.toNat := by
  rw [UInt8.toNat_sub_of_le]
  exact UInt8.le_iff_toNat_le.mpr h

theorem u8_toNat_add {a b : UInt8} (h : a.toNat + b.toNat < 2 ^ 8) : (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt8.toNat_add]
  omega

theorem u8_eq_iff_toNat {a b : UInt8} : a = b ↔ a.toNat = b.toNat :=
  ⟨fun h => congrArg UInt8.toNat h, fun h => UInt8.toNat.inj h⟩

theorem u8_beq_iff_toNat {a b : UInt8} : (a == b) = true ↔ a.toNat = b.toNat := by
  rw [beq_iff_eq, u8_eq_iff_toNat]

theorem u8_le_iff {a b : UInt8} : a ≤ b ↔ a.toNat ≤ b.toNat := UInt8.le_iff_toNat_le

theorem u8_toUInt32_toNat (a : UInt8) : a.toUInt32.toNat = a.toNat := UInt8.toNat_toUInt32 a

-- =========================================================================
-- Well-formedness of denotations
-- =========================================================================

theorem emptyNode_succ_four (k : ℕ) :
    emptyNode (k + 5) = makeCellNode (emptyNode (k + 4)) (emptyNode (k + 4))
      (emptyNode (k + 4)) (emptyNode (k + 4)) := rfl

theorem emptyNode_four : emptyNode 4 = emptyLevel4 := rfl

theorem WFd_emptyNode : ∀ k : ℕ, WFd (emptyNode (k + 4)) (k + 4)
  | 0 => rfl
  | k + 1 => by
    rw [show k + 1 + 4 = k + 5 by omega, emptyNode_succ_four]
    exact WFd_makeCellNode (WFd_emptyNode k) (WFd_emptyNode k) (WFd_emptyNode k) (WFd_emptyNode k)

theorem denoteLevel4_WFd (a : FlatHashLifeArena) (id : UInt32) : WFd (denoteLevel4 a id) 4 := by
  unfold denoteLevel4
  split
  · exact WFd_makeLevel4Node _ _ _ _
  · exact WFd_makeLevel4Node _ _ _ _

theorem denoteAt_WFd : ∀ (h : ℕ) (a : FlatHashLifeArena) (id : UInt32), WFd (denoteAt h a id) (h + 4)
  | 0, a, id => denoteLevel4_WFd a id
  | h + 1, a, id => by
    unfold denoteAt
    split
    · exact WFd_makeCellNode (denoteAt_WFd h a _) (denoteAt_WFd h a _) (denoteAt_WFd h a _)
        (denoteAt_WFd h a _)
    · exact WFd_emptyNode (h + 1)

theorem denoteAt_level (h : ℕ) (a : FlatHashLifeArena) (id : UInt32) (hh : h + 4 < 2 ^ 32) :
    (denoteAt h a id).level.toNat = h + 4 :=
  WFd_level_toNat (denoteAt_WFd h a id) hh

theorem denoteAt_depth (h : ℕ) (a : FlatHashLifeArena) (id : UInt32) :
    (denoteAt h a id).depth = h + 4 :=
  WFd_depth (denoteAt_WFd h a id)

theorem denoteAt_succ_of_lt {h : ℕ} {a : FlatHashLifeArena} {id : UInt32} (hid : id < a.cellCount) :
    denoteAt (h + 1) a id =
      makeCellNode
        (denoteAt h a a.cellNw[id.toNat]!) (denoteAt h a a.cellNe[id.toNat]!)
        (denoteAt h a a.cellSw[id.toNat]!) (denoteAt h a a.cellSe[id.toNat]!) := by
  show (if id < a.cellCount then _ else _) = _
  rw [ite_eq_left hid]

theorem denoteLevel4_of_lt {a : FlatHashLifeArena} {id : UInt32} (hid : id < a.l4Count) :
    denoteLevel4 a id =
      makeLevel4Node a.l4Nw[id.toNat]! a.l4Ne[id.toNat]! a.l4Sw[id.toNat]! a.l4Se[id.toNat]! := by
  unfold denoteLevel4
  rw [ite_eq_left hid]

-- =========================================================================
-- Arena extension and node preservation
-- =========================================================================

/--
`b` extends `a`: tables only grow, and every in-range slot of `a` keeps its structural contents in `b`.
-/
structure Extends (a b : FlatHashLifeArena) : Prop where
  l4Count : a.l4Count.toNat ≤ b.l4Count.toNat
  cellCount : a.cellCount.toNat ≤ b.cellCount.toNat
  l4 : ∀ i : ℕ, i < a.l4Count.toNat →
    b.l4Nw[i]! = a.l4Nw[i]! ∧ b.l4Ne[i]! = a.l4Ne[i]! ∧ b.l4Sw[i]! = a.l4Sw[i]! ∧ b.l4Se[i]! = a.l4Se[i]!
  cell : ∀ i : ℕ, i < a.cellCount.toNat →
    b.cellNw[i]! = a.cellNw[i]! ∧ b.cellNe[i]! = a.cellNe[i]! ∧ b.cellSw[i]! = a.cellSw[i]! ∧
    b.cellSe[i]! = a.cellSe[i]! ∧ b.cellLevel[i]! = a.cellLevel[i]!

theorem Extends.refl (a : FlatHashLifeArena) : Extends a a :=
  ⟨Nat.le_refl _, Nat.le_refl _, fun _ _ => ⟨rfl, rfl, rfl, rfl⟩, fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

theorem Extends.trans {a b c : FlatHashLifeArena} (h1 : Extends a b) (h2 : Extends b c) : Extends a c := by
  refine ⟨Nat.le_trans h1.l4Count h2.l4Count, Nat.le_trans h1.cellCount h2.cellCount, ?_, ?_⟩
  · intro i hi
    obtain ⟨e1, e2, e3, e4⟩ := h1.l4 i hi
    obtain ⟨f1, f2, f3, f4⟩ := h2.l4 i (Nat.lt_of_lt_of_le hi h1.l4Count)
    exact ⟨f1.trans e1, f2.trans e2, f3.trans e3, f4.trans e4⟩
  · intro i hi
    obtain ⟨e1, e2, e3, e4, e5⟩ := h1.cell i hi
    obtain ⟨f1, f2, f3, f4, f5⟩ := h2.cell i (Nat.lt_of_lt_of_le hi h1.cellCount)
    exact ⟨f1.trans e1, f2.trans e2, f3.trans e3, f4.trans e4, f5.trans e5⟩

theorem Extends.l4_lt {a b : FlatHashLifeArena} (h : Extends a b) {id : UInt32} (hid : id < a.l4Count) :
    id < b.l4Count :=
  u32_lt_iff.mpr (Nat.lt_of_lt_of_le (u32_lt_iff.mp hid) h.l4Count)

theorem Extends.cell_lt {a b : FlatHashLifeArena} (h : Extends a b) {id : UInt32} (hid : id < a.cellCount) :
    id < b.cellCount :=
  u32_lt_iff.mpr (Nat.lt_of_lt_of_le (u32_lt_iff.mp hid) h.cellCount)

theorem Extends.cellLevelOf {a b : FlatHashLifeArena} (h : Extends a b) {id : UInt32}
    (hid : id < a.cellCount) : cellLevelOf b id = cellLevelOf a id := by
  unfold Algorithm.cellLevelOf
  rw [(h.cell id.toNat (u32_lt_iff.mp hid)).2.2.2.2]

theorem Extends.denoteLevel4 {a b : FlatHashLifeArena} (h : Extends a b) {id : UInt32}
    (hid : id < a.l4Count) : Algorithm.denoteLevel4 b id = Algorithm.denoteLevel4 a id := by
  rw [denoteLevel4_of_lt hid, denoteLevel4_of_lt (h.l4_lt hid)]
  obtain ⟨e1, e2, e3, e4⟩ := h.l4 id.toNat (u32_lt_iff.mp hid)
  rw [e1, e2, e3, e4]

-- =========================================================================
-- Children of well-formed nodes
-- =========================================================================

theorem cellLevelOf_ge_five {a : FlatHashLifeArena} (hwf : ArenaWF a) {id : UInt32} (hid : id < a.cellCount) :
    5 ≤ cellLevelOf a id :=
  (hwf.cellChildren id hid).1

/--
The four children of a well-formed node of height `h + 1` are nodes of height `h`, and the node denotes the
cell node of its children.
-/
theorem NodeIs.children {a : FlatHashLifeArena} (hwf : ArenaWF a) {h : ℕ} {id : UInt32} {m : MacroCell}
    (hn : NodeIs a (h + 1) id m) :
    NodeIs a h a.cellNw[id.toNat]! (denoteAt h a a.cellNw[id.toNat]!) ∧
    NodeIs a h a.cellNe[id.toNat]! (denoteAt h a a.cellNe[id.toNat]!) ∧
    NodeIs a h a.cellSw[id.toNat]! (denoteAt h a a.cellSw[id.toNat]!) ∧
    NodeIs a h a.cellSe[id.toNat]! (denoteAt h a a.cellSe[id.toNat]!) ∧
    m = makeCellNode
        (denoteAt h a a.cellNw[id.toNat]!) (denoteAt h a a.cellNe[id.toNat]!)
        (denoteAt h a a.cellSw[id.toNat]!) (denoteAt h a a.cellSe[id.toNat]!) := by
  obtain ⟨hid, hlvl, hden⟩ := hn
  have hc := hwf.cellChildren id hid
  obtain ⟨_, h5, hne5⟩ := hc
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  rotate_left 4
  · rw [← hden, denoteAt_succ_of_lt hid]
  all_goals
    cases h with
    | zero =>
      obtain ⟨c1, c2, c3, c4⟩ := h5 (by omega)
      first
      | exact ⟨c1, rfl⟩
      | exact ⟨c2, rfl⟩
      | exact ⟨c3, rfl⟩
      | exact ⟨c4, rfl⟩
    | succ h =>
      obtain ⟨⟨c1, l1⟩, ⟨c2, l2⟩, ⟨c3, l3⟩, ⟨c4, l4⟩⟩ := hne5 (by omega)
      first
      | exact ⟨c1, by omega, rfl⟩
      | exact ⟨c2, by omega, rfl⟩
      | exact ⟨c3, by omega, rfl⟩
      | exact ⟨c4, by omega, rfl⟩

theorem NodeIs.eq {a : FlatHashLifeArena} {h : ℕ} {id : UInt32} {m : MacroCell} (hn : NodeIs a h id m) :
    denoteAt h a id = m := by
  cases h with
  | zero => exact hn.2
  | succ h => exact hn.2.2

theorem NodeIs.lt_l4 {a : FlatHashLifeArena} {id : UInt32} {m : MacroCell} (hn : NodeIs a 0 id m) :
    id < a.l4Count := hn.1

theorem NodeIs.lt_cell {a : FlatHashLifeArena} {h : ℕ} {id : UInt32} {m : MacroCell}
    (hn : NodeIs a (h + 1) id m) : id < a.cellCount := hn.1

theorem NodeIs.level {a : FlatHashLifeArena} {h : ℕ} {id : UInt32} {m : MacroCell}
    (hn : NodeIs a (h + 1) id m) : cellLevelOf a id = h + 5 := hn.2.1

theorem NodeIs.WFd {a : FlatHashLifeArena} {h : ℕ} {id : UInt32} {m : MacroCell} (hn : NodeIs a h id m) :
    WFd m (h + 4) := by
  rw [← hn.eq]
  exact denoteAt_WFd h a id

theorem NodeIs.denoteCell_eq {a : FlatHashLifeArena} {h : ℕ} {id : UInt32} {m : MacroCell}
    (hn : NodeIs a (h + 1) id m) : Algorithm.denoteCell a id = m := by
  unfold Algorithm.denoteCell
  rw [hn.level, show h + 5 - 4 = h + 1 by omega]
  exact hn.eq

theorem NodeIs.of_lt {a : FlatHashLifeArena} (hwf : ArenaWF a) {id : UInt32} (hid : id < a.cellCount) :
    NodeIs a (cellLevelOf a id - 4) id (Algorithm.denoteCell a id) := by
  have h5 := cellLevelOf_ge_five hwf hid
  obtain ⟨k, hk⟩ : ∃ k, cellLevelOf a id - 4 = k + 1 := ⟨cellLevelOf a id - 5, by omega⟩
  rw [hk]
  refine ⟨hid, by omega, ?_⟩
  unfold Algorithm.denoteCell
  rw [hk]

/--
Every node of a well-formed arena keeps its height and denotation in any extension.
-/
theorem NodeIs.extend {a b : FlatHashLifeArena} (hwf : ArenaWF a) (hext : Extends a b) :
    ∀ {h : ℕ} {id : UInt32} {m : MacroCell}, NodeIs a h id m → NodeIs b h id m
  | 0, id, m, hn => ⟨hext.l4_lt hn.1, by rw [hext.denoteLevel4 hn.1]; exact hn.2⟩
  | h + 1, id, m, hn => by
    obtain ⟨c1, c2, c3, c4, hm⟩ := hn.children hwf
    have e1 := (NodeIs.extend hwf hext c1).eq
    have e2 := (NodeIs.extend hwf hext c2).eq
    have e3 := (NodeIs.extend hwf hext c3).eq
    have e4 := (NodeIs.extend hwf hext c4).eq
    obtain ⟨f1, f2, f3, f4, _⟩ := hext.cell id.toNat (u32_lt_iff.mp hn.1)
    refine ⟨hext.cell_lt hn.1, by rw [hext.cellLevelOf hn.1]; exact hn.level, ?_⟩
    rw [denoteAt_succ_of_lt (hext.cell_lt hn.1), f1, f2, f3, f4, e1, e2, e3, e4, hm]

theorem NodesPreserved.of_extends {a b : FlatHashLifeArena} (hwf : ArenaWF a) (hext : Extends a b) :
    NodesPreserved a b :=
  fun _ _ _ hn => NodeIs.extend hwf hext hn

theorem NodesPreserved.refl (a : FlatHashLifeArena) : NodesPreserved a a := fun _ _ _ h => h

theorem NodesPreserved.trans {a b c : FlatHashLifeArena} (h1 : NodesPreserved a b) (h2 : NodesPreserved b c) :
    NodesPreserved a c := fun _ _ _ h => h2 _ _ _ (h1 _ _ _ h)

-- =========================================================================
-- Pre-interned empty nodes
-- =========================================================================

theorem emptyNodeForLevel_of_ge {k : ℕ} (hk : k + 5 < 2 ^ 32) :
    emptyNodeForLevel (k + 5).toUInt32 = k.toUInt32 := by
  unfold emptyNodeForLevel
  have h1 : ((k + 5).toUInt32).toNat = k + 5 := u32_ofNat_toNat hk
  rw [ite_eq_right (by rw [u32_le_iff, h1]; simp)]
  apply u32_eq_of_toNat
  rw [u32_toNat_sub (by rw [h1]; simp), h1, u32_ofNat_toNat (by omega)]
  simp

theorem emptyNodeForLevel_four : emptyNodeForLevel (4 : ℕ).toUInt32 = 0 := rfl

/--
The pre-interned empty nodes are in place: the facts about them that `ArenaWF` records.
-/
structure EmptiesWF (a : FlatHashLifeArena) : Prop where
  l4Empty :
    0 < a.l4Count ∧ a.l4Nw[0]! = 0 ∧ a.l4Ne[0]! = 0 ∧ a.l4Sw[0]! = 0 ∧ a.l4Se[0]! = 0
  cellEmptyCount : 56 ≤ a.cellCount.toNat
  cellEmpty : ∀ k : ℕ, k < 56 →
    cellLevelOf a k.toUInt32 = k + 5 ∧
    a.cellNw[k]! = emptyNodeForLevel (k + 4).toUInt32 ∧
    a.cellNe[k]! = emptyNodeForLevel (k + 4).toUInt32 ∧
    a.cellSw[k]! = emptyNodeForLevel (k + 4).toUInt32 ∧
    a.cellSe[k]! = emptyNodeForLevel (k + 4).toUInt32

theorem ArenaWF.empties {a : FlatHashLifeArena} (hwf : ArenaWF a) : EmptiesWF a :=
  ⟨hwf.l4Empty, hwf.cellEmptyCount, hwf.cellEmpty⟩

theorem NodeIs.emptyL4_of {a : FlatHashLifeArena} (hwf : EmptiesWF a) : NodeIs a 0 0 emptyLevel4 := by
  obtain ⟨hpos, e1, e2, e3, e4⟩ := hwf.l4Empty
  refine ⟨hpos, ?_⟩
  rw [denoteLevel4_of_lt hpos]
  simp only [UInt32.toNat_zero, e1, e2, e3, e4]
  rfl

/--
Slot `k < 56` of an arena whose pre-interned empty nodes are in place is the empty node of level `k + 5`.
-/
theorem NodeIs.emptyCell_of {a : FlatHashLifeArena} (hwf : EmptiesWF a) :
    ∀ k : ℕ, k < 56 → NodeIs a (k + 1) k.toUInt32 (emptyNode (k + 5))
  | 0, _ => by
    obtain ⟨hl, c1, c2, c3, c4⟩ := hwf.cellEmpty 0 (by omega)
    have hlt : (0 : ℕ).toUInt32 < a.cellCount := by
      rw [u32_lt_iff]
      have := hwf.cellEmptyCount
      simp only [Nat.toUInt32, UInt32.toNat_ofNat']
      omega
    refine ⟨hlt, hl, ?_⟩
    rw [denoteAt_succ_of_lt hlt]
    have h0 : ((0 : ℕ).toUInt32).toNat = 0 := rfl
    rw [h0, c1, c2, c3, c4, emptyNodeForLevel_four]
    have := (NodeIs.emptyL4_of hwf).eq
    show makeCellNode (denoteAt 0 a 0) (denoteAt 0 a 0) (denoteAt 0 a 0) (denoteAt 0 a 0) = _
    rw [this]
    rfl
  | k + 1, hk => by
    obtain ⟨hl, c1, c2, c3, c4⟩ := hwf.cellEmpty (k + 1) hk
    have hlt : (k + 1).toUInt32 < a.cellCount := by
      rw [u32_lt_iff, u32_ofNat_toNat (by omega)]
      have := hwf.cellEmptyCount
      omega
    refine ⟨hlt, hl, ?_⟩
    rw [denoteAt_succ_of_lt hlt, u32_ofNat_toNat (by omega), c1, c2, c3, c4,
      show k + 1 + 4 = k + 5 by omega, emptyNodeForLevel_of_ge (by omega)]
    have ih := (NodeIs.emptyCell_of hwf k (by omega)).eq
    rw [ih, show k + 1 + 5 = k + 6 by omega]
    rfl

theorem NodeIs.emptyForLevel_of {a : FlatHashLifeArena} (hwf : EmptiesWF a) (h : ℕ) (hh : h ≤ 56) :
    NodeIs a h (emptyNodeForLevel (h + 4).toUInt32) (emptyNode (h + 4)) := by
  cases h with
  | zero => exact NodeIs.emptyL4_of hwf
  | succ k =>
    rw [show k + 1 + 4 = k + 5 by omega, emptyNodeForLevel_of_ge (by omega)]
    exact NodeIs.emptyCell_of hwf k (by omega)

theorem NodeIs.emptyL4 {a : FlatHashLifeArena} (hwf : ArenaWF a) : NodeIs a 0 0 emptyLevel4 :=
  NodeIs.emptyL4_of hwf.empties

/--
Slot `k < 56` of a well-formed arena is the empty node of level `k + 5`.
-/
theorem NodeIs.emptyCell {a : FlatHashLifeArena} (hwf : ArenaWF a) :
    ∀ k : ℕ, k < 56 → NodeIs a (k + 1) k.toUInt32 (emptyNode (k + 5)) :=
  NodeIs.emptyCell_of hwf.empties

/--
`emptyNodeForLevel L` is the empty node of level `L` for `4 ≤ L ≤ 60`.
-/
theorem NodeIs.emptyForLevel {a : FlatHashLifeArena} (hwf : ArenaWF a) (h : ℕ) (hh : h ≤ 56) :
    NodeIs a h (emptyNodeForLevel (h + 4).toUInt32) (emptyNode (h + 4)) :=
  NodeIs.emptyForLevel_of hwf.empties h hh

theorem emptySubnode_of_WFd : ∀ {m : MacroCell} {d : ℕ}, WFd m (d + 4) → emptySubnode m = emptyNode (d + 4)
  | .level4Node .., d, hm => by
    rw [WFd_level4Node_iff] at hm
    have : d = 0 := by omega
    subst this
    rfl
  | .cellNode _ nw _ _ _, d, hm => by
    rw [WFd_cellNode_iff] at hm
    obtain ⟨h5, hnw, _⟩ := hm
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    have ih := emptySubnode_of_WFd (m := nw) (d := d') (by simpa using hnw)
    show makeCellNode (emptySubnode nw) (emptySubnode nw) (emptySubnode nw) (emptySubnode nw) = _
    rw [ih, show d' + 1 + 4 = d' + 5 by omega]
    rfl

end Algorithm
