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
import AlgorithmDefs
import proofs.FlatArenaBasics

local notation "ℕ" => Nat

namespace Algorithm

/-!
# Flat HashLife arena: interning

The invariant is preserved by every primitive arena transition (appending a slot, writing a memo, writing
scratch tables or the failure flag), and the two hash-consing functions return a node denoting exactly the
requested MacroCell.
-/

-- =========================================================================
-- Arenas with the same node tables
-- =========================================================================

/--
`a` and `b` have identical node tables (they may differ in memos, populations, scratch tables, and the
failure flag).
-/
structure SameNodes (a b : FlatHashLifeArena) : Prop where
  l4Nw : b.l4Nw = a.l4Nw
  l4Ne : b.l4Ne = a.l4Ne
  l4Sw : b.l4Sw = a.l4Sw
  l4Se : b.l4Se = a.l4Se
  l4Count : b.l4Count = a.l4Count
  cellNw : b.cellNw = a.cellNw
  cellNe : b.cellNe = a.cellNe
  cellSw : b.cellSw = a.cellSw
  cellSe : b.cellSe = a.cellSe
  cellLevel : b.cellLevel = a.cellLevel
  cellCount : b.cellCount = a.cellCount

theorem denoteLevel4_same {a b : FlatHashLifeArena} (hs : SameNodes a b) (id : UInt32) :
    denoteLevel4 b id = denoteLevel4 a id := by
  unfold denoteLevel4
  rw [hs.l4Count, hs.l4Nw, hs.l4Ne, hs.l4Sw, hs.l4Se]

theorem denoteAt_same {a b : FlatHashLifeArena} (hs : SameNodes a b) :
    ∀ (h : ℕ) (id : UInt32), denoteAt h b id = denoteAt h a id
  | 0, id => denoteLevel4_same hs id
  | h + 1, id => by
    show (if id < b.cellCount then _ else _) = (if id < a.cellCount then _ else _)
    rw [hs.cellCount, hs.cellNw, hs.cellNe, hs.cellSw, hs.cellSe, denoteAt_same hs h, denoteAt_same hs h,
      denoteAt_same hs h, denoteAt_same hs h]

theorem cellLevelOf_same {a b : FlatHashLifeArena} (hs : SameNodes a b) (id : UInt32) :
    cellLevelOf b id = cellLevelOf a id := by
  unfold cellLevelOf
  rw [hs.cellLevel]

theorem denoteCell_same {a b : FlatHashLifeArena} (hs : SameNodes a b) (id : UInt32) :
    denoteCell b id = denoteCell a id := by
  unfold denoteCell
  rw [cellLevelOf_same hs, denoteAt_same hs]

theorem NodeIs.same {a b : FlatHashLifeArena} (hs : SameNodes a b) :
    ∀ {h : ℕ} {id : UInt32} {m : MacroCell}, NodeIs a h id m → NodeIs b h id m
  | 0, _, _, hn => ⟨by rw [hs.l4Count]; exact hn.1, by rw [denoteLevel4_same hs]; exact hn.2⟩
  | _ + 1, _, _, hn => ⟨by rw [hs.cellCount]; exact hn.1, by rw [cellLevelOf_same hs]; exact hn.2.1,
      by rw [denoteAt_same hs]; exact hn.2.2⟩

theorem Extends.of_same {a b : FlatHashLifeArena} (hs : SameNodes a b) : Extends a b :=
  ⟨by rw [hs.l4Count]; exact Nat.le_refl _, by rw [hs.cellCount]; exact Nat.le_refl _,
    fun _ _ => ⟨by rw [hs.l4Nw], by rw [hs.l4Ne], by rw [hs.l4Sw], by rw [hs.l4Se]⟩,
    fun _ _ => ⟨by rw [hs.cellNw], by rw [hs.cellNe], by rw [hs.cellSw], by rw [hs.cellSe],
      by rw [hs.cellLevel]⟩⟩

/--
The invariant transfers to an arena with the same node tables and capacities, given that its populations
are unchanged and its memos are correct.
-/
theorem ArenaWF.of_same {a b : FlatHashLifeArena} (hwf : ArenaWF a) (hs : SameNodes a b)
    (hl4Mask : b.l4Mask = a.l4Mask) (hcellMask : b.cellMask = a.cellMask)
    (hl4StepRes : b.l4StepRes.size = a.l4StepRes.size) (hl4HasRes : b.l4HasRes.size = a.l4HasRes.size)
    (hcellPop : b.cellPop = a.cellPop) (hcellStepRes : b.cellStepRes.size = a.cellStepRes.size)
    (hl4Memo : ∀ id : UInt32, id < b.l4Count → b.l4HasRes[id.toNat]! = 1 →
      b.l4StepRes[id.toNat]! =
        computeLevel4NextGen16x16UInt b.l4Nw[id.toNat]! b.l4Ne[id.toNat]! b.l4Sw[id.toNat]! b.l4Se[id.toNat]!)
    (hcellMemo : ∀ id : UInt32, id < b.cellCount → CellMemoWF b id) :
    ArenaWF b := by
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := hwf.l4Size
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hwf.cellSize
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hl4Memo, ?_, ?_, hcellMemo⟩
  · rw [hl4Mask, hs.l4Nw, hs.l4Ne, hs.l4Sw, hs.l4Se, hl4StepRes, hl4HasRes]
    exact ⟨s1, s2, s3, s4, s5, s6⟩
  · rw [hcellMask, hs.cellNw, hs.cellNe, hs.cellSw, hs.cellSe, hs.cellLevel, hcellPop, hcellStepRes]
    exact ⟨c1, c2, c3, c4, c5, c6, c7⟩
  · rw [hs.l4Count, hl4Mask]; exact hwf.l4CountLe
  · rw [hs.cellCount, hcellMask]; exact hwf.cellCountLe
  · rw [hs.l4Count, hs.l4Nw, hs.l4Ne, hs.l4Sw, hs.l4Se]; exact hwf.l4Empty
  · rw [hs.cellCount]; exact hwf.cellEmptyCount
  · intro k hk
    rw [cellLevelOf_same hs, hs.cellNw, hs.cellNe, hs.cellSw, hs.cellSe]
    exact hwf.cellEmpty k hk
  · intro id hid
    rw [hs.cellCount] at hid
    have hc := hwf.cellChildren id hid
    unfold CellChildrenWF at hc ⊢
    simp only [cellLevelOf_same hs, hs.cellNw, hs.cellNe, hs.cellSw, hs.cellSe, hs.cellCount, hs.l4Count]
    exact hc
  · intro id hid
    rw [hs.cellCount] at hid
    rw [hcellPop, denoteCell_same hs]
    exact hwf.cellPop id hid

/--
The invariant transfers to an arena that differs only in its memos, which are correct.
-/
theorem CellMemoWF.same {a b : FlatHashLifeArena} (hs : SameNodes a b) (hm : b.cellStepRes = a.cellStepRes)
    {id : UInt32} (h : CellMemoWF a id) : CellMemoWF b id := by
  unfold CellMemoWF at h ⊢
  rw [hm, cellLevelOf_same hs, denoteCell_same hs]
  intro hne
  exact NodeIs.same hs (h hne)

theorem ArenaWF.of_same_memos {a b : FlatHashLifeArena} (hwf : ArenaWF a) (hs : SameNodes a b)
    (hl4Mask : b.l4Mask = a.l4Mask) (hcellMask : b.cellMask = a.cellMask)
    (hl4StepRes : b.l4StepRes = a.l4StepRes) (hl4HasRes : b.l4HasRes = a.l4HasRes)
    (hcellPop : b.cellPop = a.cellPop) (hcellStepRes : b.cellStepRes = a.cellStepRes) :
    ArenaWF b := by
  refine ArenaWF.of_same hwf hs hl4Mask hcellMask (by rw [hl4StepRes]) (by rw [hl4HasRes]) hcellPop
    (by rw [hcellStepRes]) ?_ ?_
  · intro id hid hhas
    rw [hs.l4Count] at hid
    rw [hl4HasRes] at hhas
    rw [hl4StepRes, hs.l4Nw, hs.l4Ne, hs.l4Sw, hs.l4Se]
    exact hwf.l4Memo id hid hhas
  · intro id hid
    rw [hs.cellCount] at hid
    exact CellMemoWF.same hs hcellStepRes (hwf.cellMemo id hid)

theorem NodeIs.of_lt' {a : FlatHashLifeArena} (hwf : ArenaWF a) {id : UInt32} (hid : id < a.cellCount) :
    ∃ k, cellLevelOf a id = k + 5 ∧ NodeIs a (k + 1) id (denoteCell a id) := by
  have h5 := cellLevelOf_ge_five hwf hid
  refine ⟨cellLevelOf a id - 5, by omega, ?_⟩
  have hn := NodeIs.of_lt hwf hid
  rwa [show cellLevelOf a id - 4 = cellLevelOf a id - 5 + 1 by omega] at hn

theorem denoteCell_extend {a b : FlatHashLifeArena} (hwf : ArenaWF a) (hext : Extends a b) {id : UInt32}
    (hid : id < a.cellCount) : denoteCell b id = denoteCell a id := by
  obtain ⟨k, _, hn⟩ := NodeIs.of_lt' hwf hid
  rw [(NodeIs.extend hwf hext hn).denoteCell_eq, hn.denoteCell_eq]

theorem u32_not_lt {a b : UInt32} (h : ¬ a < b) : b.toNat ≤ a.toNat := by
  rw [u32_lt_iff] at h
  omega

/--
The invariant transfers to an extension `b` of `a` that keeps populations and memos of existing slots, and
whose new CellNode slots are well-formed.
-/
theorem ArenaWF.transfer {a b : FlatHashLifeArena} (hwf : ArenaWF a) (hext : Extends a b)
    (hl4Size :
      b.l4Mask.toNat + 1 ≤ b.l4Nw.size ∧ b.l4Mask.toNat + 1 ≤ b.l4Ne.size ∧
      b.l4Mask.toNat + 1 ≤ b.l4Sw.size ∧ b.l4Mask.toNat + 1 ≤ b.l4Se.size ∧
      b.l4Mask.toNat + 1 ≤ b.l4StepRes.size ∧ b.l4Mask.toNat + 1 ≤ b.l4HasRes.size)
    (hcellSize :
      b.cellMask.toNat + 1 ≤ b.cellNw.size ∧ b.cellMask.toNat + 1 ≤ b.cellNe.size ∧
      b.cellMask.toNat + 1 ≤ b.cellSw.size ∧ b.cellMask.toNat + 1 ≤ b.cellSe.size ∧
      b.cellMask.toNat + 1 ≤ b.cellLevel.size ∧ b.cellMask.toNat + 1 ≤ b.cellPop.size ∧
      b.cellMask.toNat + 1 ≤ b.cellStepRes.size)
    (hl4Le : b.l4Count.toNat ≤ b.l4Mask.toNat + 1)
    (hcellLe : b.cellCount.toNat ≤ b.cellMask.toNat + 1)
    (hl4Memo : ∀ id : UInt32, id < b.l4Count → b.l4HasRes[id.toNat]! = 1 →
      b.l4StepRes[id.toNat]! =
        computeLevel4NextGen16x16UInt b.l4Nw[id.toNat]! b.l4Ne[id.toNat]! b.l4Sw[id.toNat]! b.l4Se[id.toNat]!)
    (hpopOld : ∀ i : ℕ, i < a.cellCount.toNat → b.cellPop[i]! = a.cellPop[i]!)
    (hmemoOld : ∀ i : ℕ, i < a.cellCount.toNat → b.cellStepRes[i]! = a.cellStepRes[i]!)
    (hnew : ∀ id : UInt32, a.cellCount ≤ id → id < b.cellCount →
      CellChildrenWF b id ∧ b.cellPop[id.toNat]! = (denoteCell b id).size ∧ CellMemoWF b id) :
    ArenaWF b := by
  have hl4e := hwf.l4Empty
  have hpos := u32_lt_iff.mp hl4e.1
  have hce := hwf.cellEmptyCount
  refine ⟨hl4Size, hcellSize, hl4Le, hcellLe, ?_, ?_, ?_, hl4Memo, ?_, ?_, ?_⟩
  · obtain ⟨e1, e2, e3, e4⟩ := hext.l4 0 (by simpa using hpos)
    refine ⟨hext.l4_lt hl4e.1, ?_, ?_, ?_, ?_⟩
    · rw [e1]; exact hl4e.2.1
    · rw [e2]; exact hl4e.2.2.1
    · rw [e3]; exact hl4e.2.2.2.1
    · rw [e4]; exact hl4e.2.2.2.2
  · exact Nat.le_trans hce hext.cellCount
  · intro k hk
    have hkc : k < a.cellCount.toNat := by omega
    obtain ⟨hl, c1, c2, c3, c4⟩ := hwf.cellEmpty k hk
    obtain ⟨f1, f2, f3, f4, f5⟩ := hext.cell k hkc
    refine ⟨?_, by rw [f1]; exact c1, by rw [f2]; exact c2, by rw [f3]; exact c3, by rw [f4]; exact c4⟩
    have hkk : (k.toUInt32).toNat = k := u32_ofNat_toNat (by omega)
    unfold cellLevelOf at hl ⊢
    rw [hkk] at hl ⊢
    rw [f5]
    exact hl
  · intro id hid
    by_cases hold : id < a.cellCount
    · have hc := hwf.cellChildren id hold
      have hlv := hext.cellLevelOf hold
      obtain ⟨f1, f2, f3, f4, _⟩ := hext.cell id.toNat (u32_lt_iff.mp hold)
      obtain ⟨h5, hc5, hcn⟩ := hc
      refine ⟨by rw [hlv]; exact h5, ?_, ?_⟩
      · intro hL
        rw [hlv] at hL
        obtain ⟨c1, c2, c3, c4⟩ := hc5 hL
        rw [f1, f2, f3, f4]
        exact ⟨hext.l4_lt c1, hext.l4_lt c2, hext.l4_lt c3, hext.l4_lt c4⟩
      · intro hL
        rw [hlv] at hL ⊢
        obtain ⟨⟨c1, l1⟩, ⟨c2, l2⟩, ⟨c3, l3⟩, ⟨c4, l4⟩⟩ := hcn hL
        rw [f1, f2, f3, f4]
        exact ⟨⟨hext.cell_lt c1, by rw [hext.cellLevelOf c1]; exact l1⟩,
          ⟨hext.cell_lt c2, by rw [hext.cellLevelOf c2]; exact l2⟩,
          ⟨hext.cell_lt c3, by rw [hext.cellLevelOf c3]; exact l3⟩,
          ⟨hext.cell_lt c4, by rw [hext.cellLevelOf c4]; exact l4⟩⟩
    · exact (hnew id (u32_le_iff.mpr (u32_not_lt hold)) hid).1
  · intro id hid
    by_cases hold : id < a.cellCount
    · rw [hpopOld id.toNat (u32_lt_iff.mp hold), hwf.cellPop id hold, denoteCell_extend hwf hext hold]
    · exact (hnew id (u32_le_iff.mpr (u32_not_lt hold)) hid).2.1
  · intro id hid
    by_cases hold : id < a.cellCount
    · have hm := hwf.cellMemo id hold
      unfold CellMemoWF at hm ⊢
      rw [hmemoOld id.toNat (u32_lt_iff.mp hold), hext.cellLevelOf hold, denoteCell_extend hwf hext hold]
      intro hne
      exact NodeIs.extend hwf hext (hm hne)
    · exact (hnew id (u32_le_iff.mpr (u32_not_lt hold)) hid).2.2

-- =========================================================================
-- Arena transitions that preserve the invariant
-- =========================================================================

/--
`b` is a correct successor of `a` for operations that do not touch the scratch tables: `b` is well-formed,
extends `a`, and can only have a clear failure flag if `a` did.
-/
structure Grows (a b : FlatHashLifeArena) : Prop where
  wf : ArenaWF b
  ext : Extends a b
  remapL4 : b.remapL4 = a.remapL4
  remapCell : b.remapCell = a.remapCell
  ovf : b.overflow = 0 → a.overflow = 0
  masks : b.l4Mask = a.l4Mask ∧ b.cellMask = a.cellMask
  /-- The failure flag is only raised when a node table is at capacity. -/
  cap : b.overflow ≠ 0 → a.overflow ≠ 0 ∨ ArenaFull b
  /-- Memoized step results are never cleared. -/
  memo : ∀ i, i < a.cellCount.toNat → a.cellStepRes[i]! ≠ UNCOMPUTED → b.cellStepRes[i]! ≠ UNCOMPUTED

theorem ArenaFull.mono {b c : FlatHashLifeArena} (hf : ArenaFull b) (hext : Extends b c)
    (hm : c.l4Mask = b.l4Mask ∧ c.cellMask = b.cellMask) : ArenaFull c := by
  unfold ArenaFull at hf ⊢
  rw [hm.1, hm.2]
  have := hext.l4Count
  have := hext.cellCount
  rcases hf with h | h
  · left; rw [ge_iff_le, u32_le_iff] at h ⊢; omega
  · right; rw [ge_iff_le, u32_le_iff] at h ⊢; omega

theorem Grows.refl {a : FlatHashLifeArena} (hwf : ArenaWF a) : Grows a a :=
  ⟨hwf, Extends.refl a, rfl, rfl, fun h => h, ⟨rfl, rfl⟩, fun h => Or.inl h, fun _ _ h => h⟩

theorem Grows.trans {a b c : FlatHashLifeArena} (h1 : Grows a b) (h2 : Grows b c) : Grows a c :=
  ⟨h2.wf, h1.ext.trans h2.ext, h2.remapL4.trans h1.remapL4, h2.remapCell.trans h1.remapCell,
    fun h => h1.ovf (h2.ovf h), ⟨h2.masks.1.trans h1.masks.1, h2.masks.2.trans h1.masks.2⟩,
    fun h => (h2.cap h).elim (fun h' => (h1.cap h').elim Or.inl (fun hf => Or.inr (hf.mono h2.ext h2.masks)))
      Or.inr,
    fun i hi hm => h2.memo i (Nat.lt_of_lt_of_le hi h1.ext.cellCount) (h1.memo i hi hm)⟩

theorem Grows.node {a b : FlatHashLifeArena} (hwf : ArenaWF a) (hg : Grows a b) {h : ℕ} {id : UInt32}
    {m : MacroCell} (hn : NodeIs a h id m) : NodeIs b h id m :=
  NodeIs.extend hwf hg.ext hn

theorem Grows.nodes {a b : FlatHashLifeArena} (hwf : ArenaWF a) (hg : Grows a b) : NodesPreserved a b :=
  fun _ _ _ hn => hg.node hwf hn

theorem ArenaWF.with_overflow {a : FlatHashLifeArena} (hwf : ArenaWF a) (x : UInt8) :
    ArenaWF { a with overflow := x } :=
  ArenaWF.of_same_memos hwf ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl rfl

theorem ArenaWF.setOverflow {a : FlatHashLifeArena} (hwf : ArenaWF a) : ArenaWF a.setOverflow :=
  hwf.with_overflow 1

theorem ArenaWF.clearOverflow {a : FlatHashLifeArena} (hwf : ArenaWF a) : ArenaWF a.clearOverflow :=
  hwf.with_overflow 0

theorem SameNodes.setOverflow (a : FlatHashLifeArena) : SameNodes a a.setOverflow :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem SameNodes.clearOverflow (a : FlatHashLifeArena) : SameNodes a a.clearOverflow :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem SameNodes.setRemapL4 (a : FlatHashLifeArena) (i v : UInt32) : SameNodes a (a.setRemapL4 i v) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem SameNodes.setRemapCell (a : FlatHashLifeArena) (i v : UInt32) : SameNodes a (a.setRemapCell i v) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Grows.setOverflow {a : FlatHashLifeArena} (hwf : ArenaWF a) (hf : ArenaFull a) : Grows a a.setOverflow :=
  ⟨hwf.setOverflow, Extends.of_same (SameNodes.setOverflow a), rfl, rfl,
    fun h => absurd h (show (1 : UInt8) ≠ 0 by decide), ⟨rfl, rfl⟩, fun _ => Or.inr hf, fun _ _ h => h⟩

theorem NodeIs.ne_uncomputed {a : FlatHashLifeArena} {h : ℕ} {id : UInt32} {m : MacroCell} (hn : NodeIs a h id m) :
    id ≠ UNCOMPUTED := by
  intro e
  subst e
  cases h with
  | zero =>
    have := u32_lt_iff.mp hn.1
    have := a.l4Count.toNat_lt
    simp [UNCOMPUTED] at *
    omega
  | succ h =>
    have := u32_lt_iff.mp hn.1
    have := a.cellCount.toNat_lt
    simp [UNCOMPUTED] at *
    omega

theorem ArenaWF.setRemapL4 {a : FlatHashLifeArena} (hwf : ArenaWF a) (i v : UInt32) :
    ArenaWF (a.setRemapL4 i v) :=
  ArenaWF.of_same_memos hwf (SameNodes.setRemapL4 a i v) rfl rfl rfl rfl rfl rfl

theorem ArenaWF.setRemapCell {a : FlatHashLifeArena} (hwf : ArenaWF a) (i v : UInt32) :
    ArenaWF (a.setRemapCell i v) :=
  ArenaWF.of_same_memos hwf (SameNodes.setRemapCell a i v) rfl rfl rfl rfl rfl rfl

/--
Writing a correct Level 4 memo preserves the invariant.
-/
theorem Grows.setL4StepRes {a : FlatHashLifeArena} (hwf : ArenaWF a) {id : UInt32} (hid : id < a.l4Count)
    {v : UInt64}
    (hv : v = computeLevel4NextGen16x16UInt a.l4Nw[id.toNat]! a.l4Ne[id.toNat]! a.l4Sw[id.toNat]!
      a.l4Se[id.toNat]!) :
    Grows a (a.setL4StepRes id v) := by
  have hs : SameNodes a (a.setL4StepRes id v) := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨?_, Extends.of_same hs, rfl, rfl, fun h => h, ⟨rfl, rfl⟩, fun h => Or.inl h, fun _ _ h => h⟩
  refine ArenaWF.of_same hwf hs rfl rfl (by simp only [FlatHashLifeArena.setL4StepRes, size_set!])
    (by simp only [FlatHashLifeArena.setL4StepRes, size_set!]) rfl rfl ?_ ?_
  · intro j hj hhas
    simp only [FlatHashLifeArena.setL4StepRes] at hhas ⊢
    have hlt : id.toNat < a.l4StepRes.size := by
      have := u32_lt_iff.mp hid; have := hwf.l4CountLe; have := hwf.l4Size.2.2.2.2.1; omega
    by_cases hji : id.toNat = j.toNat
    · rw [← hji, getElem!_set!_self _ _ _ hlt, hv]
    · rw [getElem!_set!_ne _ _ _ _ hji] at hhas ⊢
      exact hwf.l4Memo j hj hhas
  · intro j hj
    exact CellMemoWF.same hs rfl (hwf.cellMemo j hj)

/--
Writing a correct CellNode memo preserves the invariant.
-/
theorem Grows.setCellStepRes {a : FlatHashLifeArena} (hwf : ArenaWF a) {id r : UInt32} {h : ℕ} {m : MacroCell}
    (hn : NodeIs a (h + 1) id m) (hr : NodeIs a h r (hashLifeStep m)) :
    Grows a (a.setCellStepRes id r) := by
  have hs : SameNodes a (a.setCellStepRes id r) := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hid := hn.lt_cell
  have hlt : id.toNat < a.cellStepRes.size := by
    have := u32_lt_iff.mp hid; have := hwf.cellCountLe; have := hwf.cellSize.2.2.2.2.2.2; omega
  have hmemo : ∀ i, i < a.cellCount.toNat → a.cellStepRes[i]! ≠ UNCOMPUTED →
      (a.setCellStepRes id r).cellStepRes[i]! ≠ UNCOMPUTED := by
    intro i _ hm
    show (a.cellStepRes.set! id.toNat r)[i]! ≠ UNCOMPUTED
    by_cases hii : id.toNat = i
    · subst hii
      rw [getElem!_set!_self _ _ _ hlt]
      exact hr.ne_uncomputed
    · rw [getElem!_set!_ne _ _ _ _ hii]
      exact hm
  refine ⟨?_, Extends.of_same hs, rfl, rfl, fun h => h, ⟨rfl, rfl⟩, fun h => Or.inl h, hmemo⟩
  refine ArenaWF.of_same hwf hs rfl rfl rfl rfl rfl (by simp only [FlatHashLifeArena.setCellStepRes, size_set!]) ?_ ?_
  · intro j hj hhas
    exact hwf.l4Memo j hj hhas
  · intro j hj
    have hsr : (a.setCellStepRes id r).cellStepRes = a.cellStepRes.set! id.toNat r := rfl
    unfold CellMemoWF
    rw [hsr, cellLevelOf_same hs, denoteCell_same hs]
    by_cases hji : id.toNat = j.toNat
    · have hjeq : id = j := u32_eq_of_toNat hji
      subst hjeq
      rw [getElem!_set!_self _ _ _ hlt, hn.level, show h + 5 - 5 = h by omega, hn.denoteCell_eq]
      intro _
      exact NodeIs.same hs hr
    · rw [getElem!_set!_ne _ _ _ _ hji]
      intro hne
      exact NodeIs.same hs (hwf.cellMemo j hj hne)

-- =========================================================================
-- Probing
-- =========================================================================

theorem probeLevel4_found {a : FlatHashLifeArena} {nw ne sw se : UInt64} :
    ∀ {head fuel id : UInt32}, probeLevel4 a head nw ne sw se fuel = id → id ≠ EMPTY_BUCKET →
      id < a.l4Count ∧ a.l4Nw[id.toNat]! = nw ∧ a.l4Ne[id.toNat]! = ne ∧ a.l4Sw[id.toNat]! = sw ∧
        a.l4Se[id.toNat]! = se := by
  intro head fuel
  induction head, fuel using probeLevel4.induct (arena := a) (nw := nw) (ne := ne) (sw := sw) (se := se) with
  | case1 head =>
    intro id h hne
    rw [probeLevel4.eq_1] at h
    simp at h
    exact absurd h.symm hne
  | case2 head fuel hf hb =>
    intro id h hne
    rw [probeLevel4.eq_1] at h
    simp [hf, hb] at h
    exact absurd h.symm hne
  | case3 head fuel hf hb hc =>
    intro id h hne
    rw [probeLevel4.eq_1] at h
    simp [hf, hb, hc] at h
    exact absurd h.symm hne
  | case4 head fuel hf hb hc _ hm =>
    intro id h hne
    rw [probeLevel4.eq_1] at h
    simp only [hf, hb, hc, dite_false, ite_false, Bool.false_eq_true] at h
    rw [ite_eq_left hm] at h
    subst h
    simp only [Bool.and_eq_true, beq_iff_eq] at hm
    obtain ⟨⟨⟨e1, e2⟩, e3⟩, e4⟩ := hm
    refine ⟨?_, e1, e2, e3, e4⟩
    rw [u32_lt_iff]
    rw [ge_iff_le, u32_le_iff] at hc
    omega
  | case5 head fuel hf hb hc _ hm _ _ ih =>
    intro id h hne
    rw [probeLevel4.eq_1] at h
    simp only [hf, hb, hc, dite_false, ite_false, Bool.false_eq_true] at h
    rw [ite_eq_right hm] at h
    exact ih h hne

theorem probeCellNode_found {a : FlatHashLifeArena} {lvl : UInt8} {nw ne sw se : UInt32} :
    ∀ {head fuel id : UInt32}, probeCellNode a head lvl nw ne sw se fuel = id → id ≠ EMPTY_BUCKET →
      id < a.cellCount ∧ a.cellLevel[id.toNat]! = lvl ∧ a.cellNw[id.toNat]! = nw ∧ a.cellNe[id.toNat]! = ne ∧
        a.cellSw[id.toNat]! = sw ∧ a.cellSe[id.toNat]! = se := by
  intro head fuel
  induction head, fuel using probeCellNode.induct (arena := a) (lvl := lvl) (nw := nw) (ne := ne) (sw := sw)
    (se := se) with
  | case1 head =>
    intro id h hne
    rw [probeCellNode.eq_1] at h
    simp at h
    exact absurd h.symm hne
  | case2 head fuel hf hb =>
    intro id h hne
    rw [probeCellNode.eq_1] at h
    simp [hf, hb] at h
    exact absurd h.symm hne
  | case3 head fuel hf hb hc =>
    intro id h hne
    rw [probeCellNode.eq_1] at h
    simp [hf, hb, hc] at h
    exact absurd h.symm hne
  | case4 head fuel hf hb hc _ hm =>
    intro id h hne
    rw [probeCellNode.eq_1] at h
    simp only [hf, hb, hc, dite_false, ite_false, Bool.false_eq_true] at h
    rw [ite_eq_left hm] at h
    subst h
    simp only [Bool.and_eq_true, beq_iff_eq] at hm
    obtain ⟨⟨⟨⟨e0, e1⟩, e2⟩, e3⟩, e4⟩ := hm
    refine ⟨?_, e0, e1, e2, e3, e4⟩
    rw [u32_lt_iff]
    rw [ge_iff_le, u32_le_iff] at hc
    omega
  | case5 head fuel hf hb hc _ hm _ _ ih =>
    intro id h hne
    rw [probeCellNode.eq_1] at h
    simp only [hf, hb, hc, dite_false, ite_false, Bool.false_eq_true] at h
    rw [ite_eq_right hm] at h
    exact ih h hne

-- =========================================================================
-- Appending slots
-- =========================================================================

theorem room_toNat {count mask : UInt32} (h : ¬ (count ≥ mask + 1)) :
    count.toNat < mask.toNat + 1 ∧ (count + 1).toNat = count.toNat + 1 := by
  have h1 : count.toNat < (mask + 1).toNat := by
    rw [ge_iff_le, u32_le_iff] at h
    omega
  have hm := u32_toNat_lt mask
  have hc := u32_toNat_lt count
  by_cases hw : mask.toNat + 1 < 2 ^ 32
  · rw [u32_toNat_add_one hw] at h1
    exact ⟨h1, u32_toNat_add_one (by omega)⟩
  · have : (mask + 1).toNat = 0 := by
      rw [UInt32.toNat_add]
      simp only [UInt32.toNat_one]
      omega
    omega

/--
Appending a new Level 4 slot with the given leaves at index `l4Count` preserves the invariant.
-/
theorem Grows.appendL4 {a : FlatHashLifeArena} (hwf : ArenaWF a) (nw ne sw se : UInt64) (nxt bkt : Array UInt32)
    (hroom : ¬ (a.l4Count ≥ a.l4Mask + 1)) :
    Grows a { a with
      l4Nw := a.l4Nw.set! a.l4Count.toNat nw,
      l4Ne := a.l4Ne.set! a.l4Count.toNat ne,
      l4Sw := a.l4Sw.set! a.l4Count.toNat sw,
      l4Se := a.l4Se.set! a.l4Count.toNat se,
      l4StepRes := a.l4StepRes.set! a.l4Count.toNat 0,
      l4HasRes := a.l4HasRes.set! a.l4Count.toNat 0,
      l4Next := nxt,
      l4Buckets := bkt,
      l4Count := a.l4Count + 1 } ∧
    NodeIs { a with
      l4Nw := a.l4Nw.set! a.l4Count.toNat nw,
      l4Ne := a.l4Ne.set! a.l4Count.toNat ne,
      l4Sw := a.l4Sw.set! a.l4Count.toNat sw,
      l4Se := a.l4Se.set! a.l4Count.toNat se,
      l4StepRes := a.l4StepRes.set! a.l4Count.toNat 0,
      l4HasRes := a.l4HasRes.set! a.l4Count.toNat 0,
      l4Next := nxt,
      l4Buckets := bkt,
      l4Count := a.l4Count + 1 } 0 a.l4Count (makeLevel4Node nw ne sw se) := by
  obtain ⟨hlt, hsucc⟩ := room_toNat hroom
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := hwf.l4Size
  have hne : ∀ i : ℕ, i < a.l4Count.toNat → a.l4Count.toNat ≠ i := fun i hi => by omega
  have hext : Extends a { a with
      l4Nw := a.l4Nw.set! a.l4Count.toNat nw,
      l4Ne := a.l4Ne.set! a.l4Count.toNat ne,
      l4Sw := a.l4Sw.set! a.l4Count.toNat sw,
      l4Se := a.l4Se.set! a.l4Count.toNat se,
      l4StepRes := a.l4StepRes.set! a.l4Count.toNat 0,
      l4HasRes := a.l4HasRes.set! a.l4Count.toNat 0,
      l4Next := nxt,
      l4Buckets := bkt,
      l4Count := a.l4Count + 1 } := by
    refine ⟨by (try dsimp only); omega, Nat.le_refl _, ?_, fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
    intro i hi
    (try dsimp only)
    exact ⟨getElem!_set!_ne _ _ _ _ (hne i hi), getElem!_set!_ne _ _ _ _ (hne i hi),
      getElem!_set!_ne _ _ _ _ (hne i hi), getElem!_set!_ne _ _ _ _ (hne i hi)⟩
  refine ⟨⟨?_, hext, rfl, rfl, fun h => h, ⟨rfl, rfl⟩, fun h => Or.inl h, fun _ _ h => h⟩, ?_⟩
  · refine ArenaWF.transfer hwf hext ?_ hwf.cellSize ?_ hwf.cellCountLe ?_ (fun _ _ => rfl) (fun _ _ => rfl) ?_
    · simp only [size_set!]
      exact ⟨s1, s2, s3, s4, s5, s6⟩
    · (try dsimp only)
      omega
    · intro j hj hhas
      try dsimp only at hj hhas ⊢
      have hj' : j.toNat < a.l4Count.toNat + 1 := by rw [← hsucc]; exact u32_lt_iff.mp hj
      by_cases hji : a.l4Count.toNat = j.toNat
      · rw [← hji, getElem!_set!_self _ _ _ (by omega)] at hhas
        exact absurd hhas (by decide)
      · rw [getElem!_set!_ne _ _ _ _ hji] at hhas
        rw [getElem!_set!_ne _ _ _ _ hji, getElem!_set!_ne _ _ _ _ hji, getElem!_set!_ne _ _ _ _ hji,
          getElem!_set!_ne _ _ _ _ hji, getElem!_set!_ne _ _ _ _ hji]
        exact hwf.l4Memo j (u32_lt_iff.mpr (by omega)) hhas
    · intro j hj1 hj2
      exact absurd hj2 (by rw [u32_lt_iff]; rw [u32_le_iff] at hj1; (try dsimp only); omega)
  · refine ⟨by rw [u32_lt_iff]; (try dsimp only); omega, ?_⟩
    rw [denoteLevel4_of_lt (by rw [u32_lt_iff]; (try dsimp only); omega)]
    (try dsimp only)
    rw [getElem!_set!_self _ _ _ (by omega), getElem!_set!_self _ _ _ (by omega),
      getElem!_set!_self _ _ _ (by omega), getElem!_set!_self _ _ _ (by omega)]

theorem u8_beq_five_iff {lvl : UInt8} {h : ℕ} (hl : lvl.toNat = h + 5) : (lvl == 5) = (h == 0) := by
  by_cases h0 : h = 0
  · subst h0
    have : lvl = 5 := UInt8.toNat.inj (by rw [hl]; rfl)
    subst this
    rfl
  · have : lvl ≠ 5 := fun e => by
      subst e
      have h5 : (5 : UInt8).toNat = 5 := rfl
      omega
    have e1 : (lvl == 5) = false := by
      cases hb : (lvl == 5)
      · rfl
      · exact absurd (beq_iff_eq.mp hb) this
    have e2 : (h == 0) = false := by
      cases hb : (h == 0)
      · rfl
      · exact absurd (beq_iff_eq.mp hb) h0
    rw [e1, e2]

theorem computePopulation_eq {a : FlatHashLifeArena} (hwf : ArenaWF a) {lvl : UInt8} {h : ℕ}
    (hl : lvl.toNat = h + 5) {nw ne sw se : UInt32} {m1 m2 m3 m4 : MacroCell}
    (h1 : NodeIs a h nw m1) (h2 : NodeIs a h ne m2) (h3 : NodeIs a h sw m3) (h4 : NodeIs a h se m4) :
    computePopulation a lvl nw ne sw se = (makeCellNode m1 m2 m3 m4).size := by
  unfold computePopulation
  rw [u8_beq_five_iff hl]
  show _ = m1.size + m2.size + m3.size + m4.size
  cases h with
  | zero =>
    simp only [beq_self_eq_true, ite_true]
    obtain ⟨c1, e1⟩ := h1
    obtain ⟨c2, e2⟩ := h2
    obtain ⟨c3, e3⟩ := h3
    obtain ⟨c4, e4⟩ := h4
    rw [← e1, ← e2, ← e3, ← e4, denoteLevel4_of_lt c1, denoteLevel4_of_lt c2, denoteLevel4_of_lt c3,
      denoteLevel4_of_lt c4]
    unfold popLevel4Id
    rw [ite_eq_left c1, ite_eq_left c2, ite_eq_left c3, ite_eq_left c4]
    rfl
  | succ k =>
    simp only [Nat.add_one_ne_zero, beq_iff_eq, ite_false]
    unfold popCellId
    rw [ite_eq_left h1.lt_cell, ite_eq_left h2.lt_cell, ite_eq_left h3.lt_cell, ite_eq_left h4.lt_cell,
      hwf.cellPop _ h1.lt_cell, hwf.cellPop _ h2.lt_cell, hwf.cellPop _ h3.lt_cell, hwf.cellPop _ h4.lt_cell,
      h1.denoteCell_eq, h2.denoteCell_eq, h3.denoteCell_eq, h4.denoteCell_eq]

/--
Appending a new CellNode slot with well-formed children at index `cellCount` preserves the invariant.
-/
theorem Grows.appendCell {a : FlatHashLifeArena} (hwf : ArenaWF a) (lvl : UInt8) (nw ne sw se : UInt32)
    {h : ℕ} (hl : lvl.toNat = h + 5) {m1 m2 m3 m4 : MacroCell}
    (h1 : NodeIs a h nw m1) (h2 : NodeIs a h ne m2) (h3 : NodeIs a h sw m3) (h4 : NodeIs a h se m4)
    (nxt bkt : Array UInt32) (hroom : ¬ (a.cellCount ≥ a.cellMask + 1)) :
    Grows a { a with
      cellNw := a.cellNw.set! a.cellCount.toNat nw,
      cellNe := a.cellNe.set! a.cellCount.toNat ne,
      cellSw := a.cellSw.set! a.cellCount.toNat sw,
      cellSe := a.cellSe.set! a.cellCount.toNat se,
      cellLevel := a.cellLevel.set! a.cellCount.toNat lvl,
      cellPop := a.cellPop.set! a.cellCount.toNat (computePopulation a lvl nw ne sw se),
      cellStepRes := a.cellStepRes.set! a.cellCount.toNat UNCOMPUTED,
      cellNext := nxt,
      cellBuckets := bkt,
      cellCount := a.cellCount + 1 } ∧
    NodeIs { a with
      cellNw := a.cellNw.set! a.cellCount.toNat nw,
      cellNe := a.cellNe.set! a.cellCount.toNat ne,
      cellSw := a.cellSw.set! a.cellCount.toNat sw,
      cellSe := a.cellSe.set! a.cellCount.toNat se,
      cellLevel := a.cellLevel.set! a.cellCount.toNat lvl,
      cellPop := a.cellPop.set! a.cellCount.toNat (computePopulation a lvl nw ne sw se),
      cellStepRes := a.cellStepRes.set! a.cellCount.toNat UNCOMPUTED,
      cellNext := nxt,
      cellBuckets := bkt,
      cellCount := a.cellCount + 1 } (h + 1) a.cellCount (makeCellNode m1 m2 m3 m4) := by
  obtain ⟨hlt, hsucc⟩ := room_toNat hroom
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hwf.cellSize
  have hne : ∀ i : ℕ, i < a.cellCount.toNat → a.cellCount.toNat ≠ i := fun i hi => by omega
  have hext : Extends a { a with
      cellNw := a.cellNw.set! a.cellCount.toNat nw,
      cellNe := a.cellNe.set! a.cellCount.toNat ne,
      cellSw := a.cellSw.set! a.cellCount.toNat sw,
      cellSe := a.cellSe.set! a.cellCount.toNat se,
      cellLevel := a.cellLevel.set! a.cellCount.toNat lvl,
      cellPop := a.cellPop.set! a.cellCount.toNat (computePopulation a lvl nw ne sw se),
      cellStepRes := a.cellStepRes.set! a.cellCount.toNat UNCOMPUTED,
      cellNext := nxt,
      cellBuckets := bkt,
      cellCount := a.cellCount + 1 } := by
    refine ⟨Nat.le_refl _, by (try dsimp only); omega, fun _ _ => ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
    intro i hi
    (try dsimp only)
    exact ⟨getElem!_set!_ne _ _ _ _ (hne i hi), getElem!_set!_ne _ _ _ _ (hne i hi),
      getElem!_set!_ne _ _ _ _ (hne i hi), getElem!_set!_ne _ _ _ _ (hne i hi),
      getElem!_set!_ne _ _ _ _ (hne i hi)⟩
  have e1 := (NodeIs.extend hwf hext h1).eq
  have e2 := (NodeIs.extend hwf hext h2).eq
  have e3 := (NodeIs.extend hwf hext h3).eq
  have e4 := (NodeIs.extend hwf hext h4).eq
  have hcnt : a.cellCount < a.cellCount + 1 := by rw [u32_lt_iff]; omega
  have hlvl : cellLevelOf { a with
      cellNw := a.cellNw.set! a.cellCount.toNat nw,
      cellNe := a.cellNe.set! a.cellCount.toNat ne,
      cellSw := a.cellSw.set! a.cellCount.toNat sw,
      cellSe := a.cellSe.set! a.cellCount.toNat se,
      cellLevel := a.cellLevel.set! a.cellCount.toNat lvl,
      cellPop := a.cellPop.set! a.cellCount.toNat (computePopulation a lvl nw ne sw se),
      cellStepRes := a.cellStepRes.set! a.cellCount.toNat UNCOMPUTED,
      cellNext := nxt,
      cellBuckets := bkt,
      cellCount := a.cellCount + 1 } a.cellCount = h + 5 := by
    unfold cellLevelOf
    (try dsimp only)
    rw [getElem!_set!_self _ _ _ (by omega), hl]
  have hnode : NodeIs { a with
      cellNw := a.cellNw.set! a.cellCount.toNat nw,
      cellNe := a.cellNe.set! a.cellCount.toNat ne,
      cellSw := a.cellSw.set! a.cellCount.toNat sw,
      cellSe := a.cellSe.set! a.cellCount.toNat se,
      cellLevel := a.cellLevel.set! a.cellCount.toNat lvl,
      cellPop := a.cellPop.set! a.cellCount.toNat (computePopulation a lvl nw ne sw se),
      cellStepRes := a.cellStepRes.set! a.cellCount.toNat UNCOMPUTED,
      cellNext := nxt,
      cellBuckets := bkt,
      cellCount := a.cellCount + 1 } (h + 1) a.cellCount (makeCellNode m1 m2 m3 m4) := by
    refine ⟨hcnt, hlvl, ?_⟩
    rw [denoteAt_succ_of_lt hcnt]
    (try dsimp only)
    rw [getElem!_set!_self _ _ _ (by omega), getElem!_set!_self _ _ _ (by omega),
      getElem!_set!_self _ _ _ (by omega), getElem!_set!_self _ _ _ (by omega), e1, e2, e3, e4]
  refine ⟨⟨?_, hext, rfl, rfl, fun h => h, ⟨rfl, rfl⟩, fun h => Or.inl h, fun i hi hm => by
    (try dsimp only)
    rw [getElem!_set!_ne _ _ _ _ (hne i hi)]
    exact hm⟩, hnode⟩
  refine ArenaWF.transfer hwf hext hwf.l4Size ?_ hwf.l4CountLe ?_ hwf.l4Memo ?_ ?_ ?_
  · simp only [size_set!]
    exact ⟨c1, c2, c3, c4, c5, c6, c7⟩
  · (try dsimp only)
    omega
  · intro i hi
    exact getElem!_set!_ne _ _ _ _ (hne i hi)
  · intro i hi
    exact getElem!_set!_ne _ _ _ _ (hne i hi)
  · intro j hj1 hj2
    have hj : j = a.cellCount := by
      apply u32_eq_of_toNat
      rw [u32_le_iff] at hj1
      rw [u32_lt_iff] at hj2
      try dsimp only at hj2
      omega
    subst hj
    refine ⟨?_, ?_, ?_⟩
    · -- children
      unfold CellChildrenWF
      rw [hlvl]
      (try dsimp only)
      rw [getElem!_set!_self _ _ _ (by omega), getElem!_set!_self _ _ _ (by omega),
        getElem!_set!_self _ _ _ (by omega), getElem!_set!_self _ _ _ (by omega)]
      refine ⟨by omega, ?_, ?_⟩
      · intro h5
        have h0 : h = 0 := by omega
        subst h0
        exact ⟨h1.1, h2.1, h3.1, h4.1⟩
      · intro h5
        obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
        have l1 := (NodeIs.extend hwf hext h1).level
        have l2 := (NodeIs.extend hwf hext h2).level
        have l3 := (NodeIs.extend hwf hext h3).level
        have l4 := (NodeIs.extend hwf hext h4).level
        refine ⟨⟨(NodeIs.extend hwf hext h1).1, ?_⟩, ⟨(NodeIs.extend hwf hext h2).1, ?_⟩,
          ⟨(NodeIs.extend hwf hext h3).1, ?_⟩, ⟨(NodeIs.extend hwf hext h4).1, ?_⟩⟩ <;> omega
    · -- population
      (try dsimp only)
      rw [getElem!_set!_self _ _ _ (by omega), hnode.denoteCell_eq]
      exact computePopulation_eq hwf hl h1 h2 h3 h4
    · -- memo
      unfold CellMemoWF
      (try dsimp only)
      rw [getElem!_set!_self _ _ _ (by omega)]
      intro hne'
      exact absurd rfl hne'

-- =========================================================================
-- Interning
-- =========================================================================

/--
`internLevel4` keeps the invariant and, unless the arena fails, returns a Level 4 node with exactly the
requested leaves.
-/
theorem internLevel4_spec {a : FlatHashLifeArena} (hwf : ArenaWF a) (nw ne sw se : UInt64) :
    Grows a (a.internLevel4 nw ne sw se).2 ∧
    ((a.internLevel4 nw ne sw se).2.overflow = 0 →
      NodeIs (a.internLevel4 nw ne sw se).2 0 (a.internLevel4 nw ne sw se).1 (makeLevel4Node nw ne sw se)) := by
  unfold FlatHashLifeArena.internLevel4
  split
  · rename_i hov
    refine ⟨Grows.refl hwf, fun h => ?_⟩
    simp only [bne_iff_ne, ne_eq] at hov
    exact absurd h hov
  · split
    · rename_i _ hz
      simp only [Bool.and_eq_true, beq_iff_eq] at hz
      obtain ⟨⟨⟨⟨e1, e2⟩, e3⟩, e4⟩, _⟩ := hz
      subst e1 e2 e3 e4
      exact ⟨Grows.refl hwf, fun _ => NodeIs.emptyL4 hwf⟩
    · dsimp only
      split
      · rename_i hp
        rw [bne_iff_ne, ne_eq] at hp
        obtain ⟨hid, e1, e2, e3, e4⟩ := probeLevel4_found rfl hp
        dsimp only
        refine ⟨Grows.refl hwf, fun _ => ⟨hid, ?_⟩⟩
        rw [denoteLevel4_of_lt hid, e1, e2, e3, e4]
      · split
        · rename_i hfull
          exact ⟨Grows.setOverflow hwf (by unfold ArenaFull; first | exact Or.inl hfull | exact Or.inr hfull),
            fun h => absurd h (show (1 : UInt8) ≠ 0 by decide)⟩
        · rename_i hroom
          obtain ⟨hg, hn⟩ := Grows.appendL4 hwf nw ne sw se _ _ hroom
          exact ⟨hg, fun _ => hn⟩

theorem emptyNodeForLevel_pred {lvl : UInt8} {h : ℕ} (hl : lvl.toNat = h + 5) :
    emptyNodeForLevel (lvl.toUInt32 - 1) = emptyNodeForLevel (h + 4).toUInt32 := by
  have := u8_toNat_lt lvl
  congr 1
  apply u32_eq_of_toNat
  rw [u32_toNat_sub (by rw [u8_toUInt32_toNat]; simp; omega), u8_toUInt32_toNat, hl,
    u32_ofNat_toNat (by omega)]
  simp

theorem emptyNodeForLevel_self {lvl : UInt8} {h : ℕ} (hl : lvl.toNat = h + 5) :
    emptyNodeForLevel lvl.toUInt32 = h.toUInt32 := by
  have : lvl.toUInt32 = (h + 5).toUInt32 := by
    apply u32_eq_of_toNat
    rw [u8_toUInt32_toNat, hl, u32_ofNat_toNat (by have := u8_toNat_lt lvl; omega)]
  rw [this, emptyNodeForLevel_of_ge (by have := u8_toNat_lt lvl; omega)]

/--
`internCellNode` keeps the invariant and, unless the arena fails, returns a CellNode at the requested level
denoting the cell node of its children.
-/
theorem internCellNode_spec {a : FlatHashLifeArena} (hwf : ArenaWF a) {lvl : UInt8} {h : ℕ}
    (hl : lvl.toNat = h + 5) {nw ne sw se : UInt32} {m1 m2 m3 m4 : MacroCell}
    (h1 : NodeIs a h nw m1) (h2 : NodeIs a h ne m2) (h3 : NodeIs a h sw m3) (h4 : NodeIs a h se m4) :
    Grows a (a.internCellNode lvl nw ne sw se).2 ∧
    ((a.internCellNode lvl nw ne sw se).2.overflow = 0 →
      NodeIs (a.internCellNode lvl nw ne sw se).2 (h + 1) (a.internCellNode lvl nw ne sw se).1
        (makeCellNode m1 m2 m3 m4)) := by
  unfold FlatHashLifeArena.internCellNode
  split
  · rename_i hov
    refine ⟨Grows.refl hwf, fun h => ?_⟩
    simp only [bne_iff_ne, ne_eq] at hov
    exact absurd h hov
  · dsimp only
    split
    · rename_i _ hz
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hz
      obtain ⟨⟨⟨⟨⟨⟨_, h60⟩, _⟩, e1⟩, e2⟩, e3⟩, e4⟩ := hz
      rw [emptyNodeForLevel_pred hl] at e1 e2 e3 e4
      refine ⟨Grows.refl hwf, fun _ => ?_⟩
      have h60' : h < 56 := by
        have := u8_le_iff.mp h60
        have h60n : (60 : UInt8).toNat = 60 := rfl
        omega
      have he := NodeIs.emptyForLevel hwf h (by omega)
      have q1 := he.eq
      rw [← e1, h1.eq] at q1
      have q2 := he.eq
      rw [← e2, h2.eq] at q2
      have q3 := he.eq
      rw [← e3, h3.eq] at q3
      have q4 := he.eq
      rw [← e4, h4.eq] at q4
      rw [emptyNodeForLevel_self hl, q1, q2, q3, q4, ← emptyNode_succ_four,
        show h + 4 + 1 = h + 5 by omega]
      have := NodeIs.emptyCell hwf h h60'
      rw [show h + 4 + 1 = h + 1 + 4 by omega] at this ⊢ <;> assumption
    · split
      · rename_i hp
        rw [bne_iff_ne, ne_eq] at hp
        obtain ⟨hid, el, e1, e2, e3, e4⟩ := probeCellNode_found rfl hp
        dsimp only
        refine ⟨Grows.refl hwf, fun _ => ⟨hid, ?_, ?_⟩⟩
        · unfold cellLevelOf
          rw [el, hl]
        · rw [denoteAt_succ_of_lt hid, e1, e2, e3, e4, h1.eq, h2.eq, h3.eq, h4.eq]
      · split
        · rename_i hfull
          exact ⟨Grows.setOverflow hwf (by unfold ArenaFull; first | exact Or.inl hfull | exact Or.inr hfull),
            fun h => absurd h (show (1 : UInt8) ≠ 0 by decide)⟩
        · rename_i hroom
          obtain ⟨hg, hn⟩ := Grows.appendCell hwf lvl nw ne sw se hl h1 h2 h3 h4 _ _ hroom
          exact ⟨hg, fun _ => hn⟩

theorem internCellNode_overflow {a : FlatHashLifeArena} (h : a.overflow ≠ 0) (lvl : UInt8) (nw ne sw se : UInt32) :
    a.internCellNode lvl nw ne sw se = (UNCOMPUTED, a) := by
  unfold FlatHashLifeArena.internCellNode
  rw [ite_eq_left (by simpa using h)]

/--
`internCellNode_spec` where the children only need to be nodes if the arena has not failed yet (a failed
arena returns immediately).
-/
theorem internCellNode_spec' {a : FlatHashLifeArena} (hwf : ArenaWF a) {lvl : UInt8} {h : ℕ}
    (hl : lvl.toNat = h + 5) {nw ne sw se : UInt32} {m1 m2 m3 m4 : MacroCell}
    (hc : a.overflow = 0 →
      NodeIs a h nw m1 ∧ NodeIs a h ne m2 ∧ NodeIs a h sw m3 ∧ NodeIs a h se m4) :
    Grows a (a.internCellNode lvl nw ne sw se).2 ∧
    ((a.internCellNode lvl nw ne sw se).2.overflow = 0 →
      NodeIs (a.internCellNode lvl nw ne sw se).2 (h + 1) (a.internCellNode lvl nw ne sw se).1
        (makeCellNode m1 m2 m3 m4)) := by
  by_cases hov : a.overflow = 0
  · obtain ⟨h1, h2, h3, h4⟩ := hc hov
    exact internCellNode_spec hwf hl h1 h2 h3 h4
  · rw [internCellNode_overflow hov]
    exact ⟨Grows.refl hwf, fun h => absurd h hov⟩

end Algorithm
