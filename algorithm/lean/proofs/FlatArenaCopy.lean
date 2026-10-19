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
import proofs.FlatArenaIntern

local notation "ℕ" => Nat

namespace Algorithm

/-!
# Flat HashLife arena: subgraph copy and compaction

Copying a node (with or without its memos) from one well-formed arena into another produces a node with the
same level and denotation, and keeps both the invariant and every existing node of the destination.
-/

/--
Every set copy-remap entry of `dst` for a slot of `src` is a node of `dst` with the same height and
denotation as that slot in `src`.
-/
structure RemapOK (src dst : FlatHashLifeArena) : Prop where
  l4 : ∀ j : UInt32, j < src.l4Count → dst.remapL4[j.toNat]! ≠ UNCOMPUTED →
    NodeIs dst 0 dst.remapL4[j.toNat]! (denoteLevel4 src j)
  cell : ∀ j : UInt32, j < src.cellCount → getRemapCell dst j ≠ UNCOMPUTED →
    NodeIs dst (cellLevelOf src j - 4) (getRemapCell dst j) (denoteCell src j)

/--
`b` is a correct successor of `a` during a copy from `src`: `b` is well-formed, extends `a`, can only have a
clear failure flag if `a` did, keeps the remap invariant, and keeps the scratch table sizes.
-/
structure CopyOK (src a b : FlatHashLifeArena) : Prop where
  wf : ArenaWF b
  ext : Extends a b
  ovf : b.overflow = 0 → a.overflow = 0
  remap : RemapOK src b
  remapL4Size : b.remapL4.size = a.remapL4.size
  remapCellSize : b.remapCell.size = a.remapCell.size

theorem CopyOK.refl {src a : FlatHashLifeArena} (hwf : ArenaWF a) (hr : RemapOK src a) : CopyOK src a a :=
  ⟨hwf, Extends.refl a, fun h => h, hr, rfl, rfl⟩

theorem CopyOK.trans {src a b c : FlatHashLifeArena} (h1 : CopyOK src a b) (h2 : CopyOK src b c) :
    CopyOK src a c :=
  ⟨h2.wf, h1.ext.trans h2.ext, fun h => h1.ovf (h2.ovf h), h2.remap, h2.remapL4Size.trans h1.remapL4Size,
    h2.remapCellSize.trans h1.remapCellSize⟩

theorem getRemapCell_same {a b : FlatHashLifeArena} (h : b.remapCell = a.remapCell) (j : UInt32) :
    getRemapCell b j = getRemapCell a j := by
  unfold getRemapCell
  rw [h]

theorem RemapOK.grows {src a b : FlatHashLifeArena} (hwf : ArenaWF a) (hr : RemapOK src a) (g : Grows a b) :
    RemapOK src b :=
  ⟨fun j hj hne => by
      rw [g.remapL4] at hne ⊢
      exact g.node hwf (hr.l4 j hj hne),
    fun j hj hne => by
      rw [getRemapCell_same g.remapCell] at hne ⊢
      exact g.node hwf (hr.cell j hj hne)⟩

theorem CopyOK.of_grows {src a b : FlatHashLifeArena} (hwf : ArenaWF a) (hr : RemapOK src a) (g : Grows a b) :
    CopyOK src a b :=
  ⟨g.wf, g.ext, g.ovf, hr.grows hwf g, by rw [g.remapL4], by rw [g.remapCell]⟩

theorem lt_of_lt_toUInt32 {j : UInt32} {n : ℕ} (h : j < n.toUInt32) : j.toNat < n := by
  rw [u32_lt_iff, Nat.toUInt32, UInt32.toNat_ofNat'] at h
  have := Nat.mod_le n (2 ^ 32)
  omega

theorem getRemapCell_set_self {a : FlatHashLifeArena} {j v : UInt32} (hj : j < a.remapCell.size.toUInt32) :
    getRemapCell (a.setRemapCell j v) j = v := by
  unfold getRemapCell FlatHashLifeArena.setRemapCell
  rw [size_set!, ite_eq_left hj, getElem!_set!_self _ _ _ (lt_of_lt_toUInt32 hj)]

theorem getRemapCell_set_ne {a : FlatHashLifeArena} {i j v : UInt32} (hij : i.toNat ≠ j.toNat) :
    getRemapCell (a.setRemapCell i v) j = getRemapCell a j := by
  unfold getRemapCell FlatHashLifeArena.setRemapCell
  rw [size_set!, getElem!_set!_ne _ _ _ _ hij]

/--
Writing a remap entry `j ↦ v` keeps the copy invariant when `v` is a node denoting slot `j` of `src`, or when
`j` is not a slot of `src` (a work-stack write).
-/
theorem CopyOK.setRemapCell {src a : FlatHashLifeArena} (hwf : ArenaWF a) (hr : RemapOK src a) {j v : UInt32}
    (hv : j < src.cellCount → j < a.remapCell.size.toUInt32 ∧
      NodeIs a (cellLevelOf src j - 4) v (denoteCell src j)) :
    CopyOK src a (a.setRemapCell j v) := by
  have hs := SameNodes.setRemapCell a j v
  refine ⟨hwf.setRemapCell j v, Extends.of_same hs, fun h => h, ⟨?_, ?_⟩, rfl, by simp [FlatHashLifeArena.setRemapCell]⟩
  · intro i hi hne
    exact NodeIs.same hs (hr.l4 i hi hne)
  · intro i hi hne
    by_cases hij : j.toNat = i.toNat
    · have := u32_eq_of_toNat hij
      subst this
      obtain ⟨hsz, hn⟩ := hv hi
      rw [getRemapCell_set_self hsz]
      exact NodeIs.same hs hn
    · rw [getRemapCell_set_ne hij] at hne ⊢
      exact NodeIs.same hs (hr.cell i hi hne)

theorem CopyOK.setRemapL4 {src a : FlatHashLifeArena} (hwf : ArenaWF a) (hr : RemapOK src a) {j v : UInt32}
    (hj : j.toNat < a.remapL4.size) (hv : j < src.l4Count → NodeIs a 0 v (denoteLevel4 src j)) :
    CopyOK src a (a.setRemapL4 j v) := by
  have hs := SameNodes.setRemapL4 a j v
  refine ⟨hwf.setRemapL4 j v, Extends.of_same hs, fun h => h, ⟨?_, ?_⟩,
    by simp [FlatHashLifeArena.setRemapL4], rfl⟩
  · intro i hi hne
    simp only [FlatHashLifeArena.setRemapL4] at hne ⊢
    by_cases hij : j.toNat = i.toNat
    · have := u32_eq_of_toNat hij
      subst this
      rw [getElem!_set!_self _ _ _ hj]
      exact NodeIs.same hs (hv hi)
    · rw [getElem!_set!_ne _ _ _ _ hij] at hne ⊢
      exact NodeIs.same hs (hr.l4 i hi hne)
  · intro i hi hne
    rw [getRemapCell_same (b := a.setRemapL4 j v) rfl] at hne ⊢
    exact NodeIs.same hs (hr.cell i hi hne)

theorem makeLevel4Node_inj {a b c d a' b' c' d' : UInt64}
    (h : makeLevel4Node a b c d = makeLevel4Node a' b' c' d') : a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  unfold makeLevel4Node at h
  injection h with _ h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

/--
Copying a Level 4 node returns a Level 4 node of `dst` with the same leaves.
-/
theorem copyL4From_spec {src dst : FlatHashLifeArena} (hsrc : ArenaWF src) (hwf : ArenaWF dst)
    (hr : RemapOK src dst) (hsz : src.l4Count.toNat ≤ dst.remapL4.size) (copyMemos : Bool) {l4Id : UInt32}
    (hid : l4Id < src.l4Count) :
    CopyOK src dst (dst.copyL4From src l4Id copyMemos).2 ∧
    ((dst.copyL4From src l4Id copyMemos).2.overflow = 0 →
      NodeIs (dst.copyL4From src l4Id copyMemos).2 0 (dst.copyL4From src l4Id copyMemos).1
        (denoteLevel4 src l4Id)) := by
  have hidN := u32_lt_iff.mp hid
  unfold FlatHashLifeArena.copyL4From
  split
  · rename_i hc
    have h0 : l4Id = 0 := by
      simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
      rcases hc with hc | hc
      · exact hc
      · rw [ge_iff_le, u32_le_iff] at hc
        omega
    subst h0
    refine ⟨CopyOK.refl hwf hr, fun _ => ?_⟩
    rw [(NodeIs.emptyL4 hsrc).2]
    exact NodeIs.emptyL4 hwf
  · dsimp only
    split
    · rename_i hex
      exact ⟨CopyOK.refl hwf hr, fun _ => hr.l4 l4Id hid (by simpa using hex)⟩
    · have hs := internLevel4_spec hwf src.l4Nw[l4Id.toNat]! src.l4Ne[l4Id.toNat]! src.l4Sw[l4Id.toNat]!
        src.l4Se[l4Id.toNat]!
      rcases e : dst.internLevel4 src.l4Nw[l4Id.toNat]! src.l4Ne[l4Id.toNat]! src.l4Sw[l4Id.toNat]!
          src.l4Se[l4Id.toNat]! with ⟨newId, d1⟩
      rw [e] at hs
      obtain ⟨g1, r1⟩ := hs
      have c1 := CopyOK.of_grows hwf hr g1
      dsimp only at g1 r1 c1 ⊢
      rw [← denoteLevel4_of_lt hid] at r1
      split
      · exact ⟨c1, fun h => absurd h (by simpa using (by assumption : (d1.overflow != 0) = true))⟩
      · rename_i hov
        have hov' : d1.overflow = 0 := by simpa using hov
        have hn1 := r1 hov'
        have hsz1 : l4Id.toNat < d1.remapL4.size := by rw [c1.remapL4Size]; omega
        split
        · rename_i hm
          simp only [Bool.and_eq_true, beq_iff_eq] at hm
          have hleaves := hn1.2
          rw [denoteLevel4_of_lt hn1.1, denoteLevel4_of_lt hid] at hleaves
          obtain ⟨q1, q2, q3, q4⟩ := makeLevel4Node_inj hleaves
          have gm := Grows.setL4StepRes c1.wf hn1.1 (v := src.l4StepRes[l4Id.toNat]!) (by
            rw [hsrc.l4Memo l4Id hid hm.2, q1, q2, q3, q4])
          have c2 := c1.trans (CopyOK.of_grows c1.wf c1.remap gm)
          have hn2 := gm.node c1.wf hn1
          have c3 := CopyOK.setRemapL4 c2.wf c2.remap (j := l4Id) (v := newId)
            (by rw [c2.remapL4Size]; omega) (fun _ => hn2)
          exact ⟨c2.trans c3, fun _ => NodeIs.same (SameNodes.setRemapL4 _ _ _) hn2⟩
        · have c3 := CopyOK.setRemapL4 c1.wf c1.remap (j := l4Id) (v := newId) hsz1 (fun _ => hn1)
          exact ⟨c1.trans c3, fun _ => NodeIs.same (SameNodes.setRemapL4 _ _ _) hn1⟩

theorem RemapOK.child {src dst : FlatHashLifeArena} (hr : RemapOK src dst) {h : ℕ} {c : UInt32} {m : MacroCell}
    (hc : NodeIs src (h + 1) c m) (hne : getRemapCell dst c ≠ UNCOMPUTED) :
    NodeIs dst (h + 1) (getRemapCell dst c) m := by
  have := hr.cell c hc.lt_cell hne
  rwa [hc.level, show h + 5 - 4 = h + 1 by omega, hc.denoteCell_eq] at this

/--
One step of the copy loop keeps the copy invariant: every remap entry it writes is a node of `dst` with the
height and denotation of its `src` slot, and every memo it writes is correct.
-/
theorem copyCellTryStep_spec {src dst : FlatHashLifeArena} (hsrc : ArenaWF src) (hwf : ArenaWF dst)
    (hr : RemapOK src dst) (hsz : src.l4Count.toNat ≤ dst.remapL4.size)
    (hszC : src.cellCount ≤ dst.remapCell.size.toUInt32) (copyMemos : Bool) {cellId : UInt32}
    (hid : cellId < src.cellCount) :
    CopyOK src dst (copyCellTryStep dst src cellId copyMemos).2 := by
  obtain ⟨k, hk, hnode⟩ := NodeIs.of_lt' hsrc hid
  have hcs := hnode.children hsrc
  have hidR : cellId < dst.remapCell.size.toUInt32 := UInt32.lt_of_lt_of_le hid hszC
  have fin : ∀ d : FlatHashLifeArena, CopyOK src dst d → ∀ newId : UInt32,
      NodeIs d (k + 1) newId (denoteCell src cellId) → CopyOK src dst (d.setRemapCell cellId newId) := by
    intro d hd newId hn
    refine hd.trans (CopyOK.setRemapCell hd.wf hd.remap fun _ => ⟨?_, ?_⟩)
    · rw [hd.remapCellSize]
      exact hidR
    · rw [hk, show k + 5 - 4 = k + 1 by omega]
      exact hn
  have hmemo : src.cellStepRes[cellId.toNat]! ≠ UNCOMPUTED →
      NodeIs src k src.cellStepRes[cellId.toNat]! (hashLifeStep (denoteCell src cellId)) := by
    intro hne
    have := hsrc.cellMemo cellId hid hne
    unfold CellMemoWF at this
    rwa [hk, show k + 5 - 5 = k by omega] at this
  unfold copyCellTryStep
  dsimp only
  split
  · -- level 5
    rename_i h5
    have hk0 : k = 0 := by
      have := u8_beq_iff_toNat.mp h5
      unfold cellLevelOf at hk
      have : (5 : UInt8).toNat = 5 := rfl
      omega
    subst hk0
    obtain ⟨c1, c2, c3, c4, hM⟩ := hcs
    have s1 := copyL4From_spec hsrc hwf hr hsz copyMemos c1.lt_l4
    rcases e1 : dst.copyL4From src src.cellNw[cellId.toNat]! copyMemos with ⟨nw, d1⟩
    rw [e1] at s1
    obtain ⟨k1, n1⟩ := s1
    have s2 := copyL4From_spec hsrc k1.wf k1.remap (by rw [k1.remapL4Size]; exact hsz) copyMemos c2.lt_l4
    rcases e2 : d1.copyL4From src src.cellNe[cellId.toNat]! copyMemos with ⟨ne, d2⟩
    rw [e2] at s2
    obtain ⟨k2, n2⟩ := s2
    have k12 := k1.trans k2
    have s3 := copyL4From_spec hsrc k2.wf k2.remap (by rw [k12.remapL4Size]; exact hsz) copyMemos c3.lt_l4
    rcases e3 : d2.copyL4From src src.cellSw[cellId.toNat]! copyMemos with ⟨sw, d3⟩
    rw [e3] at s3
    obtain ⟨k3, n3⟩ := s3
    have k13 := k12.trans k3
    have s4 := copyL4From_spec hsrc k3.wf k3.remap (by rw [k13.remapL4Size]; exact hsz) copyMemos c4.lt_l4
    rcases e4 : d3.copyL4From src src.cellSe[cellId.toNat]! copyMemos with ⟨se, d4⟩
    rw [e4] at s4
    obtain ⟨k4, n4⟩ := s4
    have k14 := k13.trans k4
    dsimp only at n1 n2 n3 n4 k1 k2 k3 k4 ⊢
    split
    · exact k14
    · rename_i hov4
      have hov4' : d4.overflow = 0 := by simpa using hov4
      have hov3 := k4.ovf hov4'
      have hov2 := k3.ovf hov3
      have hov1 := k2.ovf hov2
      have m1 := NodeIs.extend k1.wf (k2.ext.trans (k3.ext.trans k4.ext)) (n1 hov1)
      have m2 := NodeIs.extend k2.wf (k3.ext.trans k4.ext) (n2 hov2)
      have m3 := NodeIs.extend k3.wf k4.ext (n3 hov3)
      have m4 := n4 hov4'
      have si := internCellNode_spec k14.wf (lvl := 5) (h := 0) rfl m1 m2 m3 m4
      rcases e5 : d4.internCellNode 5 nw ne sw se with ⟨newId, d5⟩
      rw [e5] at si
      obtain ⟨g5, n5⟩ := si
      have k5 := k14.trans (CopyOK.of_grows k14.wf k14.remap g5)
      dsimp only at g5 n5 k5 ⊢
      split
      · exact k5
      · rename_i hov5
        have hM5 : NodeIs d5 1 newId (denoteCell src cellId) := by
          rw [hM]
          exact n5 (by simpa using hov5)
        split
        · rename_i hcm
          have hcm' := hcm
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hcm'
          have hm0 := hmemo hcm'.2
          have s6 := copyL4From_spec hsrc k5.wf k5.remap (by rw [k5.remapL4Size]; exact hsz) copyMemos
            hm0.lt_l4
          rcases e6 : d5.copyL4From src src.cellStepRes[cellId.toNat]! copyMemos with ⟨rr, d6⟩
          rw [e6] at s6
          obtain ⟨k6, n6⟩ := s6
          dsimp only at k6 n6 ⊢
          have hn6 := NodeIs.extend k5.wf k6.ext hM5
          split
          · rename_i hov6
            have hr6 := n6 (by simpa using hov6)
            rw [hm0.2] at hr6
            have g7 := Grows.setCellStepRes k6.wf hn6 hr6
            exact fin _ ((k5.trans k6).trans (CopyOK.of_grows k6.wf k6.remap g7)) newId (g7.node k6.wf hn6)
          · exact fin _ (k5.trans k6) newId hn6
        · exact fin _ k5 newId hM5
  · -- level ≥ 6
    rename_i h5
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := by
      have : ¬ (src.cellLevel[cellId.toNat]!).toNat = (5 : UInt8).toNat := fun h => h5 (u8_beq_iff_toNat.mpr h)
      unfold cellLevelOf at hk
      have h5n : (5 : UInt8).toNat = 5 := rfl
      exact ⟨k - 1, by omega⟩
    obtain ⟨c1, c2, c3, c4, hM⟩ := hcs
    split
    · exact CopyOK.refl hwf hr
    split
    · exact CopyOK.refl hwf hr
    split
    · exact CopyOK.refl hwf hr
    split
    · exact CopyOK.refl hwf hr
    rename_i hn1 hn2 hn3 hn4
    have r1 := hr.child c1 (by simpa using hn1)
    have r2 := hr.child c2 (by simpa using hn2)
    have r3 := hr.child c3 (by simpa using hn3)
    have r4 := hr.child c4 (by simpa using hn4)
    have si := internCellNode_spec hwf (h := j + 1) hk r1 r2 r3 r4
    rcases e1 : dst.internCellNode src.cellLevel[cellId.toNat]! (getRemapCell dst src.cellNw[cellId.toNat]!)
        (getRemapCell dst src.cellNe[cellId.toNat]!) (getRemapCell dst src.cellSw[cellId.toNat]!)
        (getRemapCell dst src.cellSe[cellId.toNat]!) with ⟨newId, d1⟩
    rw [e1] at si
    obtain ⟨g1, n1⟩ := si
    have k1 := CopyOK.of_grows hwf hr g1
    dsimp only at g1 n1 k1 ⊢
    have hM1 : d1.overflow = 0 → NodeIs d1 (j + 1 + 1) newId (denoteCell src cellId) := fun h => by
      rw [hM]
      exact n1 h
    cases hA : (copyMemos && src.cellStepRes[cellId.toNat]! != UNCOMPUTED)
    · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      split
      · exact k1
      · rename_i hov1
        exact fin _ k1 newId (hM1 (by simpa using hov1))
    · have hA' := hA
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hA'
      simp only [Bool.true_and, ↓reduceIte]
      split
      · exact CopyOK.refl hwf hr
      · rename_i hrr
        split
        · exact k1
        · rename_i hov1
          have hn1' := hM1 (by simpa using hov1)
          have hm0 := hr.child (hmemo hA'.2) (by simpa using hrr)
          have g2 := Grows.setCellStepRes g1.wf hn1' (g1.node hwf hm0)
          exact fin _ (k1.trans (CopyOK.of_grows g1.wf k1.remap g2)) newId (g2.node g1.wf hn1')

-- =========================================================================
-- The copy loop
-- =========================================================================

/--
The copy loop keeps the copy invariant. Its work stack lives at `remapCell[stackBase ..]`, past every remap
entry of `src`, so pushes never disturb the remap entries.
-/
theorem copyCellFromLoop_spec {src : FlatHashLifeArena} (hsrc : ArenaWF src) (copyMemos : Bool)
    (stackBase : UInt32) (hbase : src.cellCount.toNat ≤ stackBase.toNat) (hnw : stackBase.toNat + 256 < 2 ^ 32)
    (n : ℕ) :
    ∀ (d : FlatHashLifeArena) (sp fuel : UInt32), fuel.toNat ≤ n → ArenaWF d → RemapOK src d →
      src.l4Count.toNat ≤ d.remapL4.size → src.cellCount ≤ d.remapCell.size.toUInt32 →
      CopyOK src d (d.copyCellFromLoop src copyMemos stackBase sp fuel) := by
  induction n with
  | zero =>
    intro d sp fuel hn hwf hr _ _
    have : fuel = 0 := u32_eq_of_toNat (by simp; omega)
    subst this
    rw [FlatHashLifeArena.copyCellFromLoop.eq_1]
    simp only [dite_true]
    exact CopyOK.refl hwf hr
  | succ n ih =>
    intro d sp fuel hn hwf hr hsz hszC
    rw [FlatHashLifeArena.copyCellFromLoop.eq_1]
    by_cases hf : fuel = 0
    · simp only [hf, dite_true]
      exact CopyOK.refl hwf hr
    simp only [hf, dite_false]
    have hfuel : (fuel - 1).toNat ≤ n := by
      have := uint32_sub_one_lt fuel hf
      omega
    have ih' := fun (d' : FlatHashLifeArena) (sp' : UInt32) (k : CopyOK src d d') =>
      k.trans (ih d' sp' (fuel - 1) hfuel k.wf k.remap (by rw [k.remapL4Size]; exact hsz)
        (by rw [k.remapCellSize]; exact hszC))
    split
    · exact CopyOK.refl hwf hr
    · try dsimp only
      split
      · exact ih' d _ (CopyOK.refl hwf hr)
      · rename_i hlt
        have hid : getRemapCell d (stackBase + sp - 1) < src.cellCount := by
          rw [ge_iff_le, u32_le_iff] at hlt
          rw [u32_lt_iff]
          omega
        split
        · exact ih' d _ (CopyOK.refl hwf hr)
        · have k1 := copyCellTryStep_spec hsrc hwf hr hsz hszC copyMemos hid
          rcases e : copyCellTryStep d src (getRemapCell d (stackBase + sp - 1)) copyMemos with ⟨missing, d1⟩
          rw [e] at k1
          dsimp only at k1 ⊢
          split
          · exact ih' d1 _ k1
          · split
            · exact ih' d1 _ k1
            · split
              · exact ih' d1 _ k1
              · rename_i hdepth
                have hsp : sp.toNat < 256 := by
                  have : ¬ copyStackDepth ≤ sp := by simpa using hdepth
                  rw [u32_le_iff] at this
                  have h256 : copyStackDepth.toNat = 256 := rfl
                  omega
                have k2 := CopyOK.setRemapCell k1.wf k1.remap (j := stackBase + sp) (v := missing)
                  (fun h => by
                    exfalso
                    rw [u32_lt_iff, u32_toNat_add (by omega)] at h
                    omega)
                exact ih' _ _ (k1.trans k2)

-- =========================================================================
-- Remap table initialization
-- =========================================================================

theorem SameNodes.trans {a b c : FlatHashLifeArena} (h1 : SameNodes a b) (h2 : SameNodes b c) : SameNodes a c :=
  ⟨h2.l4Nw.trans h1.l4Nw, h2.l4Ne.trans h1.l4Ne, h2.l4Sw.trans h1.l4Sw, h2.l4Se.trans h1.l4Se,
    h2.l4Count.trans h1.l4Count, h2.cellNw.trans h1.cellNw, h2.cellNe.trans h1.cellNe, h2.cellSw.trans h1.cellSw,
    h2.cellSe.trans h1.cellSe, h2.cellLevel.trans h1.cellLevel, h2.cellCount.trans h1.cellCount⟩

theorem initRemapL4Loop_spec (limit : UInt32) (n : ℕ) :
    ∀ (a : FlatHashLifeArena) (i : UInt32), limit.toNat - i.toNat ≤ n → ArenaWF a →
      limit.toNat ≤ a.remapL4.size →
      ArenaWF (a.initRemapL4Loop i limit) ∧ SameNodes a (a.initRemapL4Loop i limit) ∧
      (a.initRemapL4Loop i limit).overflow = a.overflow ∧
      (a.initRemapL4Loop i limit).remapCell = a.remapCell ∧
      (a.initRemapL4Loop i limit).remapL4.size = a.remapL4.size ∧
      ∀ j : ℕ, j < limit.toNat → (a.initRemapL4Loop i limit).remapL4[j]! =
        if j < i.toNat then a.remapL4[j]! else if j = 0 then 0 else UNCOMPUTED := by
  induction n with
  | zero =>
    intro a i hn hwf _
    rw [FlatHashLifeArena.initRemapL4Loop]
    split
    · rename_i h
      have := u32_lt_iff.mp h
      omega
    · refine ⟨hwf, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, fun j hj => ?_⟩
      rename_i h
      have := u32_not_lt h
      rw [ite_eq_left (by omega)]
  | succ n ih =>
    intro a i hn hwf hsz
    rw [FlatHashLifeArena.initRemapL4Loop]
    split
    · rename_i h
      have hi := u32_lt_iff.mp h
      have hi1 : (i + 1).toNat = i.toNat + 1 := u32_toNat_add_one (by have := u32_toNat_lt limit; omega)
      obtain ⟨w, s, o, c, z, e⟩ := ih (a.setRemapL4 i (if i == 0 then 0 else UNCOMPUTED)) (i + 1) (by omega)
        (hwf.setRemapL4 _ _) (by simp only [FlatHashLifeArena.setRemapL4, size_set!]; exact hsz)
      refine ⟨w, (SameNodes.setRemapL4 a _ _).trans s, o, c,
        by rw [z]; simp only [FlatHashLifeArena.setRemapL4, size_set!],
        fun j hj => ?_⟩
      rw [e j hj, hi1]
      simp only [FlatHashLifeArena.setRemapL4]
      by_cases hji : j < i.toNat
      · rw [ite_eq_left (by omega), ite_eq_left hji, getElem!_set!_ne _ _ _ _ (by omega)]
      · rw [ite_eq_right hji]
        by_cases hji' : j = i.toNat
        · subst hji'
          rw [ite_eq_left (by omega), getElem!_set!_self _ _ _ (by omega)]
          by_cases h0 : i.toNat = 0
          · have : i = 0 := u32_eq_of_toNat h0
            subst this
            rfl
          · have : (i == 0) = false := by
              simp only [beq_eq_false_iff_ne, ne_eq]
              intro hz
              subst hz
              exact h0 rfl
            rw [this, ite_eq_right h0]
            rfl
        · rw [ite_eq_right (by omega)]
    · refine ⟨hwf, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, fun j hj => ?_⟩
      rename_i h
      have := u32_not_lt h
      rw [ite_eq_left (by omega)]

theorem initRemapCellLoop_spec (limit : UInt32) (n : ℕ) :
    ∀ (a : FlatHashLifeArena) (i : UInt32), limit.toNat - i.toNat ≤ n → ArenaWF a →
      limit.toNat ≤ a.remapCell.size →
      ArenaWF (a.initRemapCellLoop i limit) ∧ SameNodes a (a.initRemapCellLoop i limit) ∧
      (a.initRemapCellLoop i limit).overflow = a.overflow ∧
      (a.initRemapCellLoop i limit).remapL4 = a.remapL4 ∧
      (a.initRemapCellLoop i limit).remapCell.size = a.remapCell.size ∧
      ∀ j : ℕ, j < limit.toNat → (a.initRemapCellLoop i limit).remapCell[j]! =
        if j < i.toNat then a.remapCell[j]! else if j < 56 then j.toUInt32 else UNCOMPUTED := by
  induction n with
  | zero =>
    intro a i hn hwf _
    rw [FlatHashLifeArena.initRemapCellLoop]
    split
    · rename_i h
      have := u32_lt_iff.mp h
      omega
    · refine ⟨hwf, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, fun j hj => ?_⟩
      rename_i h
      have := u32_not_lt h
      rw [ite_eq_left (by omega)]
  | succ n ih =>
    intro a i hn hwf hsz
    rw [FlatHashLifeArena.initRemapCellLoop]
    split
    · rename_i h
      have hi := u32_lt_iff.mp h
      have hi1 : (i + 1).toNat = i.toNat + 1 := u32_toNat_add_one (by have := u32_toNat_lt limit; omega)
      obtain ⟨w, s, o, c, z, e⟩ := ih (a.setRemapCell i (if i < 56 then i else UNCOMPUTED)) (i + 1) (by omega)
        (hwf.setRemapCell _ _) (by simp only [FlatHashLifeArena.setRemapCell, size_set!]; exact hsz)
      refine ⟨w, (SameNodes.setRemapCell a _ _).trans s, o, c,
        by rw [z]; simp only [FlatHashLifeArena.setRemapCell, size_set!],
        fun j hj => ?_⟩
      rw [e j hj, hi1]
      simp only [FlatHashLifeArena.setRemapCell]
      by_cases hji : j < i.toNat
      · rw [ite_eq_left (by omega), ite_eq_left hji, getElem!_set!_ne _ _ _ _ (by omega)]
      · rw [ite_eq_right hji]
        by_cases hji' : j = i.toNat
        · subst hji'
          rw [ite_eq_left (by omega), getElem!_set!_self _ _ _ (by omega)]
          have hii : i.toNat.toUInt32 = i := u32_eq_of_toNat (u32_ofNat_toNat (u32_toNat_lt i))
          by_cases h56 : i.toNat < 56
          · have : i < 56 := u32_lt_iff.mpr h56
            rw [ite_eq_left this, ite_eq_left h56, hii]
          · have : ¬ i < 56 := fun h => h56 (u32_lt_iff.mp h)
            rw [ite_eq_right this, ite_eq_right h56]
        · rw [ite_eq_right (by omega)]
    · refine ⟨hwf, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, fun j hj => ?_⟩
      rename_i h
      have := u32_not_lt h
      rw [ite_eq_left (by omega)]

/--
Freshly initialized remap tables satisfy the remap invariant: only the pre-interned empty nodes are mapped,
each to itself.
-/
theorem RemapOK.init {src a : FlatHashLifeArena} (hsrc : ArenaWF src) (hwf : ArenaWF a)
    (hl4 : ∀ j : ℕ, j < src.l4Count.toNat → a.remapL4[j]! = if j = 0 then 0 else UNCOMPUTED)
    (hcell : ∀ j : ℕ, j < src.cellCount.toNat → a.remapCell[j]! = if j < 56 then j.toUInt32 else UNCOMPUTED)
    (hszC : src.cellCount ≤ a.remapCell.size.toUInt32) : RemapOK src a := by
  refine ⟨fun j hj hne => ?_, fun j hj hne => ?_⟩
  · have e := hl4 j.toNat (u32_lt_iff.mp hj)
    by_cases h0 : j.toNat = 0
    · have : j = 0 := u32_eq_of_toNat h0
      subst this
      rw [e, ite_eq_left h0, (NodeIs.emptyL4 hsrc).2]
      exact NodeIs.emptyL4 hwf
    · rw [e, ite_eq_right h0] at hne
      exact absurd rfl hne
  · have hjs : j < a.remapCell.size.toUInt32 := UInt32.lt_of_lt_of_le hj hszC
    unfold getRemapCell at hne ⊢
    rw [ite_eq_left hjs] at hne ⊢
    have e := hcell j.toNat (u32_lt_iff.mp hj)
    by_cases h56 : j.toNat < 56
    · have hjj : j.toNat.toUInt32 = j := u32_eq_of_toNat (u32_ofNat_toNat (u32_toNat_lt j))
      have hs := NodeIs.emptyCell hsrc j.toNat h56
      have hd := NodeIs.emptyCell hwf j.toNat h56
      rw [hjj] at hs hd
      rw [e, ite_eq_left h56, hjj, hs.level, show j.toNat + 5 - 4 = j.toNat + 1 by omega, hs.denoteCell_eq]
      exact hd
    · rw [e, ite_eq_right h56] at hne
      exact absurd rfl hne

-- =========================================================================
-- Subgraph copy and compaction
-- =========================================================================

/--
`b` results from `a` by adding nodes and memos only, possibly using both remap tables as scratch space (and
possibly changing the failure flag).
-/
structure ScratchOK (a b : FlatHashLifeArena) : Prop where
  wf : ArenaWF b
  ext : Extends a b
  remapL4Size : b.remapL4.size = a.remapL4.size
  remapCellSize : b.remapCell.size = a.remapCell.size

theorem ScratchOK.trans {a b c : FlatHashLifeArena} (h1 : ScratchOK a b) (h2 : ScratchOK b c) : ScratchOK a c :=
  ⟨h2.wf, h1.ext.trans h2.ext, h2.remapL4Size.trans h1.remapL4Size, h2.remapCellSize.trans h1.remapCellSize⟩

theorem ScratchOK.of_same {a b : FlatHashLifeArena} (hwf : ArenaWF b) (hs : SameNodes a b)
    (h1 : b.remapL4.size = a.remapL4.size) (h2 : b.remapCell.size = a.remapCell.size) : ScratchOK a b :=
  ⟨hwf, Extends.of_same hs, h1, h2⟩

theorem CopyOK.scratch {src a b : FlatHashLifeArena} (h : CopyOK src a b) : ScratchOK a b :=
  ⟨h.wf, h.ext, h.remapL4Size, h.remapCellSize⟩

theorem toUInt32_toNat_le (n : ℕ) : n.toUInt32.toNat ≤ n := by
  rw [Nat.toUInt32, UInt32.toNat_ofNat']
  exact Nat.mod_le n _

theorem copySubgraphInto_spec {src dst : FlatHashLifeArena} (hsrc : ArenaWF src) (hwf : ArenaWF dst)
    (rootId : UInt32) (copyMemos : Bool) :
    ScratchOK dst (copySubgraphInto dst src rootId copyMemos) ∧
    ((copySubgraphInto dst src rootId copyMemos).overflow = 0 →
      dst.overflow = 0 ∧ RemapOK src (copySubgraphInto dst src rootId copyMemos)) := by
  unfold copySubgraphInto
  split
  · exact ⟨ScratchOK.of_same hwf.setOverflow (SameNodes.setOverflow dst) rfl rfl,
      fun h => absurd h (show (1 : UInt8) ≠ 0 by decide)⟩
  · rename_i hcan
    simp only [FlatHashLifeArena.canCopySubgraphFrom, Bool.not_eq_true', Bool.and_eq_false_iff,
      decide_eq_false_iff_not, Classical.not_not, not_or] at hcan
    obtain ⟨⟨hl4, hst⟩, hcells⟩ := hcan
    rw [ge_iff_le] at hst
    rw [u32_le_iff] at hl4 hst hcells
    have hs1 := toUInt32_toNat_le dst.remapL4.size
    have hs2 := toUInt32_toNat_le dst.remapCell.size
    have h256 : copyStackDepth.toNat = 256 := rfl
    rw [u32_toNat_sub (by omega), h256] at hcells
    have hc32 := u32_toNat_lt dst.remapCell.size.toUInt32
    obtain ⟨w1, s1, o1, c1, z1, e1⟩ := initRemapL4Loop_spec src.l4Count _ dst 0 (Nat.le_refl _) hwf (by omega)
    obtain ⟨w2, s2, o2, c2, z2, e2⟩ := initRemapCellLoop_spec src.cellCount _ (dst.initRemapL4Loop 0 src.l4Count) 0
      (Nat.le_refl _) w1 (by rw [c1]; omega)
    have hszC : src.cellCount ≤
        ((dst.initRemapL4Loop 0 src.l4Count).initRemapCellLoop 0 src.cellCount).remapCell.size.toUInt32 := by
      rw [z2, c1, u32_le_iff]
      omega
    have hr2 : RemapOK src ((dst.initRemapL4Loop 0 src.l4Count).initRemapCellLoop 0 src.cellCount) := by
      refine RemapOK.init hsrc w2 (fun j hj => ?_) (fun j hj => ?_) hszC
      · rw [c2, e1 j hj]
        simp
      · rw [e2 j hj]
        simp
    have sc2 : ScratchOK dst ((dst.initRemapL4Loop 0 src.l4Count).initRemapCellLoop 0 src.cellCount) :=
      ScratchOK.of_same w2 (s1.trans s2) (by rw [c2, z1]) (by rw [z2, c1])
    have ov2 : ((dst.initRemapL4Loop 0 src.l4Count).initRemapCellLoop 0 src.cellCount).overflow = dst.overflow := by
      rw [o2, o1]
    dsimp only
    split
    · exact ⟨sc2, fun h => ⟨ov2 ▸ h, hr2⟩⟩
    · have k3 := CopyOK.setRemapCell w2 hr2 (j := src.cellCount) (v := rootId)
        (fun h => absurd h (UInt32.lt_irrefl _))
      have hl := copyCellFromLoop_spec hsrc copyMemos src.cellCount (Nat.le_refl _) (by omega)
        ((src.cellCount + 1) * 6 + 256).toNat
        (((dst.initRemapL4Loop 0 src.l4Count).initRemapCellLoop 0 src.cellCount).setRemapCell src.cellCount rootId)
        1 ((src.cellCount + 1) * 6 + 256)
        (Nat.le_refl _) k3.wf k3.remap (by rw [k3.remapL4Size, c2, z1]; omega) (by rw [k3.remapCellSize]; exact hszC)
      have k := k3.trans hl
      exact ⟨sc2.trans k.scratch, fun h => ⟨ov2 ▸ k.ovf h, k.remap⟩⟩

/--
`copySubgraphFrom` keeps the invariant of `dst` and every node already in it; it succeeds (returns an id other
than `UNCOMPUTED`) exactly when it leaves the failure flag clear; and on success the returned id is a node of
`dst` with the same level and denotation as `rootId` in `src`.
-/
theorem copySubgraphFrom_spec {src dst : FlatHashLifeArena} (hsrc : ArenaWF src) (hwf : ArenaWF dst)
    (rootId : UInt32) (copyMemos : Bool) :
    ScratchOK dst (dst.copySubgraphFrom src rootId copyMemos).2 ∧
    ((dst.copySubgraphFrom src rootId copyMemos).1 ≠ UNCOMPUTED ↔
      (dst.copySubgraphFrom src rootId copyMemos).2.overflow = 0) ∧
    ((dst.copySubgraphFrom src rootId copyMemos).2.overflow = 0 →
      dst.overflow = 0 ∧ rootId < src.cellCount ∧
      NodeIs (dst.copySubgraphFrom src rootId copyMemos).2 (cellLevelOf src rootId - 4)
        (dst.copySubgraphFrom src rootId copyMemos).1 (denoteCell src rootId)) := by
  unfold FlatHashLifeArena.copySubgraphFrom
  obtain ⟨sc, hr⟩ := copySubgraphInto_spec hsrc hwf rootId copyMemos
  generalize copySubgraphInto dst src rootId copyMemos = d1 at sc hr ⊢
  dsimp only
  have fail : ScratchOK dst (UNCOMPUTED, d1.setOverflow).2 ∧
      ((UNCOMPUTED, d1.setOverflow).1 ≠ UNCOMPUTED ↔ (UNCOMPUTED, d1.setOverflow).2.overflow = 0) ∧
      ((UNCOMPUTED, d1.setOverflow).2.overflow = 0 → dst.overflow = 0 ∧ rootId < src.cellCount ∧
        NodeIs (UNCOMPUTED, d1.setOverflow).2 (cellLevelOf src rootId - 4) (UNCOMPUTED, d1.setOverflow).1
          (denoteCell src rootId)) :=
    ⟨sc.trans (ScratchOK.of_same sc.wf.setOverflow (SameNodes.setOverflow d1) rfl rfl),
      ⟨fun h => absurd rfl h, fun h => absurd h (show (1 : UInt8) ≠ 0 by decide)⟩,
      fun h => absurd h (show (1 : UInt8) ≠ 0 by decide)⟩
  by_cases hroot : rootId ≥ src.cellCount
  · rw [ite_eq_left hroot]
    rw [ite_eq_left (by simp)]
    exact fail
  · rw [ite_eq_right hroot]
    split
    · exact fail
    · rename_i hok
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, not_or] at hok
      obtain ⟨hov, hres⟩ := hok
      unfold getOverflow at hov
      have hov' : d1.overflow = 0 := by simpa using hov
      have hid : rootId < src.cellCount := by
        rw [ge_iff_le, u32_le_iff] at hroot
        rw [u32_lt_iff]
        omega
      obtain ⟨hov0, hr1⟩ := hr hov'
      exact ⟨sc, ⟨fun _ => hov', fun _ => hres⟩, fun _ => ⟨hov0, hid, hr1.cell rootId hid hres⟩⟩

/--
`compactRootFrom` keeps the invariant of `dst` and every node already in it; on success the returned id is a
node of `dst` with the same level and denotation as `rootId` in `src`; and it succeeds whenever `rootId` is a
node of a non-failed `src` and `dst` does not report running out of capacity.
-/
theorem compactRootFrom_spec {src dst : FlatHashLifeArena} (hsrc : ArenaWF src) (hwf : ArenaWF dst)
    (rootId : UInt32) :
    ScratchOK dst (dst.compactRootFrom src rootId).2 ∧
    ((dst.compactRootFrom src rootId).1.1 ≠ UNCOMPUTED →
      (dst.compactRootFrom src rootId).2.overflow = 0 ∧ rootId < src.cellCount ∧
      NodeIs (dst.compactRootFrom src rootId).2 (cellLevelOf src rootId - 4)
        (dst.compactRootFrom src rootId).1.1 (denoteCell src rootId)) ∧
    (rootId < src.cellCount → src.overflow = 0 → (dst.compactRootFrom src rootId).2.overflow = 0 →
      (dst.compactRootFrom src rootId).1.1 ≠ UNCOMPUTED) := by
  unfold FlatHashLifeArena.compactRootFrom
  split
  · rename_i hbad
    refine ⟨ScratchOK.of_same hwf ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl,
      fun h => absurd rfl h, fun hid hso _ => ?_⟩
    simp only [Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hbad
    rcases hbad with h | h
    · rw [ge_iff_le, u32_le_iff] at h
      have := u32_lt_iff.mp hid
      omega
    · exact absurd hso h
  · obtain ⟨sc1, hi1, hs1⟩ := copySubgraphFrom_spec hsrc hwf rootId true
    rcases e1 : dst.copySubgraphFrom src rootId true with ⟨id1, d1⟩
    rw [e1] at sc1 hi1 hs1
    dsimp only at sc1 hi1 hs1 ⊢
    split
    · rename_i hov
      have hov' : d1.overflow = 0 := by simpa using hov
      obtain ⟨_, hid, hn⟩ := hs1 hov'
      exact ⟨sc1, fun _ => ⟨hov', hid, hn⟩, fun _ _ _ => hi1.mpr hov'⟩
    · have w2 := sc1.wf.clearOverflow
      obtain ⟨sc3, hi3, hs3⟩ := copySubgraphFrom_spec hsrc w2 rootId false
      rcases e3 : d1.clearOverflow.copySubgraphFrom src rootId false with ⟨id2, d3⟩
      rw [e3] at sc3 hi3 hs3
      dsimp only at sc3 hi3 hs3 ⊢
      refine ⟨sc1.trans ((ScratchOK.of_same w2 (SameNodes.clearOverflow d1) rfl rfl).trans sc3),
        fun h => ?_, fun _ _ h => hi3.mpr h⟩
      obtain ⟨_, hid, hn⟩ := hs3 (hi3.mp h)
      exact ⟨hi3.mp h, hid, hn⟩

end Algorithm
