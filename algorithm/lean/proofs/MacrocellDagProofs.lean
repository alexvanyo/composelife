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

import proofs.MacrocellProofs

namespace Algorithm

/-!
# Macrocell serialization of a DAG

`serializeMacrocellDag` uses hash tables for what `MacrocellWriterState` keeps in association lists, and writes
each entry of a DAG with its children's numbers. It writes what writing the entries one after another with
`addTree` writes, so its lines read back as the tree of the last entry.
-/

/-! ## Chained hash tables -/

/-- `t` holds the association list `l`, with buckets chosen by `slot` (given the number of buckets). -/
def ChainTable.Rep {K : Type} [BEq K] (t : ChainTable K) (slot : K → UInt32 → UInt32) (l : List (K × UInt32)) :
    Prop :=
  0 < t.size ∧ t.size < 2 ^ 32 ∧ (∀ k, (slot k t.size.toUInt32).toNat < t.size) ∧
    ∀ k, t.get (slot k t.size.toUInt32) k = l.lookup k

theorem ChainTable.rep_insert {K : Type} [BEq K] [LawfulBEq K] {t : ChainTable K} {slot : K → UInt32 → UInt32}
    {l : List (K × UInt32)} (h : t.Rep slot l) (k : K) (v : UInt32) :
    (t.insert (slot k t.size.toUInt32) k v).Rep slot ((k, v) :: l) := by
  obtain ⟨h0, h32, hs, hg⟩ := h
  have hsz : (t.insert (slot k t.size.toUInt32) k v).size = t.size := by simp [ChainTable.insert]
  refine ⟨by rw [hsz]; exact h0, by rw [hsz]; exact h32, fun k' => by rw [hsz]; exact hs k', fun k' => ?_⟩
  rw [hsz]
  unfold ChainTable.get ChainTable.insert
  rw [List.lookup_cons]
  have hk := hs k
  have hk' := hs k'
  simp only [Array.set!_eq_setIfInBounds]
  rw [getElem!_pos _ _ (by simp; omega)]
  by_cases he : (slot k' t.size.toUInt32).toNat = (slot k t.size.toUInt32).toNat
  · rw [Array.getElem_setIfInBounds (by omega), ite_eq_left he.symm]
    rw [List.lookup_cons]
    have := hg k'
    unfold ChainTable.get at this
    rw [he] at this
    rw [this]
  · rw [Array.getElem_setIfInBounds (by omega), ite_eq_right (Ne.symm he)]
    have hne : (k' == k) = false := by
      rw [beq_eq_false_iff_ne]; intro hkk; subst hkk; exact he rfl
    simp only [hne]
    have := hg k'
    unfold ChainTable.get at this
    rw [← this, getElem!_pos _ _ (by omega)]

theorem ChainTable.rep_replicate {K : Type} [BEq K] (slot : K → UInt32 → UInt32) (n : Nat) (h0 : 0 < n)
    (h32 : n < 2 ^ 32) (hs : ∀ k, (slot k n.toUInt32).toNat < n) :
    ChainTable.Rep (Array.replicate n ([] : List (K × UInt32))) slot [] := by
  refine ⟨by simp; omega, by simp; omega, fun k => by simpa using hs k, fun k => ?_⟩
  unfold ChainTable.get
  simp only [Array.size_replicate]
  rw [getElem!_pos _ _ (by simp; exact hs k)]
  simp

theorem leafSlot_lt (k : UInt64) (n : Nat) (h0 : 0 < n) (h32 : n < 2 ^ 32) : (leafSlot k n.toUInt32).toNat < n := by
  unfold leafSlot
  rw [UInt32.toNat_mod, u32_size_toNat h32]
  exact Nat.mod_lt _ h0

theorem nodeSlot_lt (k : UInt32 × UInt32 × UInt32 × UInt32 × UInt32) (n : Nat) (h0 : 0 < n) (h32 : n < 2 ^ 32) :
    (nodeSlot k n.toUInt32).toNat < n := by
  unfold nodeSlot
  rw [UInt32.toNat_mod, u32_size_toNat h32]
  exact Nat.mod_lt _ h0

/-! ## The writer state -/

/-- The DAG writer holds the state `st`. -/
def DagWriter.Rep (w : DagWriter) (st : MacrocellWriterState) : Prop :=
  w.lines.Rep st.lines.toArray ∧ w.leafT.Rep leafSlot st.leaves ∧ w.nodeT.Rep nodeSlot st.nodes

theorem DagWriter.lines_size {w : DagWriter} {st : MacrocellWriterState} (h : w.lines.Rep st.lines.toArray)
    (hl : st.lines.length < 2 ^ 31) : w.lines.size = st.nextId := by
  apply UInt32.toNat_inj.mp
  rw [h.1]; unfold MacrocellWriterState.nextId; rw [u32_size_toNat (by omega)]; simp

theorem DagWriter.addLeafAt_some (w : DagWriter) (leaf : UInt64) (s id : UInt32) (h : w.leafT.get s leaf = some id) :
    w.addLeafAt leaf s = (id, w) := by
  unfold DagWriter.addLeafAt; rw [h]

theorem DagWriter.addLeafAt_none (w : DagWriter) (leaf : UInt64) (s : UInt32) (h : w.leafT.get s leaf = none) :
    w.addLeafAt leaf s =
      (w.lines.size, ⟨w.lines.push (formatLeafNode leaf), w.leafT.insert s leaf w.lines.size, w.nodeT⟩) := by
  unfold DagWriter.addLeafAt; rw [h]

theorem DagWriter.addNodeAt_some (w : DagWriter) (key : UInt32 × UInt32 × UInt32 × UInt32 × UInt32) (s id : UInt32)
    (h : w.nodeT.get s key = some id) : w.addNodeAt key s = (id, w) := by
  unfold DagWriter.addNodeAt; rw [h]

theorem DagWriter.addNodeAt_none (w : DagWriter) (key : UInt32 × UInt32 × UInt32 × UInt32 × UInt32) (s : UInt32)
    (h : w.nodeT.get s key = none) :
    w.addNodeAt key s = (w.lines.size, ⟨w.lines.push (formatMacrocellNode key.1 key.2.1 key.2.2.1 key.2.2.2.1
      key.2.2.2.2), w.leafT, w.nodeT.insert s key w.lines.size⟩) := by
  unfold DagWriter.addNodeAt; rw [h]

theorem DagWriter.addLeaf_rep {w : DagWriter} {st : MacrocellWriterState} (h : w.Rep st) (leaf : UInt64)
    (hl : (st.addLeaf leaf).2.lines.length < 2 ^ 31) :
    (w.addLeaf leaf).1 = (st.addLeaf leaf).1 ∧ (w.addLeaf leaf).2.Rep (st.addLeaf leaf).2 := by
  obtain ⟨hli, hlf, hnd⟩ := h
  have hst : st.lines.length < 2 ^ 31 := by have := addLeaf_lines st leaf; omega
  unfold MacrocellWriterState.addLeaf at hl
  unfold DagWriter.addLeaf MacrocellWriterState.addLeaf
  by_cases h0 : (leaf == 0) = true
  · simp only [h0, ite_true]; exact ⟨trivial, hli, hlf, hnd⟩
  simp only [h0, Bool.false_eq_true, ite_false] at hl ⊢
  have hsz := DagWriter.lines_size hli (by omega)
  have hg := hlf.2.2.2 leaf
  cases hk : st.leaves.lookup leaf with
  | some id =>
    rw [hk] at hg
    rw [DagWriter.addLeafAt_some _ _ _ _ hg]; exact ⟨rfl, hli, hlf, hnd⟩
  | none =>
    rw [hk] at hg
    rw [DagWriter.addLeafAt_none _ _ _ hg]
    rw [hk] at hl; simp only [List.length_append, List.length_singleton] at hl
    refine ⟨hsz, ?_, ?_, hnd⟩
    · have := GrowBuf.rep_push hli (formatLeafNode leaf) (by simp; omega)
      simpa using this
    · show ChainTable.Rep (w.leafT.insert (leafSlot leaf w.leafT.size.toUInt32) leaf w.lines.size) leafSlot
        ((leaf, st.nextId) :: st.leaves)
      rw [hsz]; exact ChainTable.rep_insert hlf leaf st.nextId

theorem DagWriter.addNode_rep {w : DagWriter} {st : MacrocellWriterState} (h : w.Rep st) (L a b c d : UInt32)
    (hl : (st.addNode L a b c d).2.lines.length < 2 ^ 31) :
    (w.addNode L a b c d).1 = (st.addNode L a b c d).1 ∧ (w.addNode L a b c d).2.Rep (st.addNode L a b c d).2 := by
  obtain ⟨hli, hlf, hnd⟩ := h
  have hst : st.lines.length < 2 ^ 31 := by have := addNode_lines st L a b c d; omega
  unfold MacrocellWriterState.addNode at hl
  unfold DagWriter.addNode MacrocellWriterState.addNode
  have hsz := DagWriter.lines_size hli (by omega)
  have hg := hnd.2.2.2 (L, a, b, c, d)
  cases hk : st.nodes.lookup (L, a, b, c, d) with
  | some id =>
    rw [hk] at hg
    rw [DagWriter.addNodeAt_some _ _ _ _ hg]; exact ⟨rfl, hli, hlf, hnd⟩
  | none =>
    rw [hk] at hg
    rw [DagWriter.addNodeAt_none _ _ _ hg]
    rw [hk] at hl; simp only [List.length_append, List.length_singleton] at hl
    refine ⟨hsz, ?_, hlf, ?_⟩
    · have := GrowBuf.rep_push hli (formatMacrocellNode L a b c d) (by simp; omega)
      simpa using this
    · show ChainTable.Rep (w.nodeT.insert (nodeSlot (L, a, b, c, d) w.nodeT.size.toUInt32) (L, a, b, c, d)
        w.lines.size) nodeSlot (((L, a, b, c, d), st.nextId) :: st.nodes)
      rw [hsz]; exact ChainTable.rep_insert hnd (L, a, b, c, d) st.nextId

/-! ## Memos -/

/-- The memos of `st` are kept by `st'`. -/
def MemoSub (st st' : MacrocellWriterState) : Prop :=
  (∀ k v, st.leaves.lookup k = some v → st'.leaves.lookup k = some v) ∧
    (∀ k v, st.nodes.lookup k = some v → st'.nodes.lookup k = some v)

theorem MemoSub.refl (st : MacrocellWriterState) : MemoSub st st := ⟨fun _ _ h => h, fun _ _ h => h⟩

theorem MemoSub.trans {a b c : MacrocellWriterState} (h1 : MemoSub a b) (h2 : MemoSub b c) : MemoSub a c :=
  ⟨fun k v h => h2.1 k v (h1.1 k v h), fun k v h => h2.2 k v (h1.2 k v h)⟩

theorem addLeaf_sub (st : MacrocellWriterState) (x : UInt64) : MemoSub st (st.addLeaf x).2 := by
  unfold MacrocellWriterState.addLeaf
  split
  · exact MemoSub.refl _
  · cases hx : st.leaves.lookup x with
    | some _ => exact MemoSub.refl _
    | none =>
      refine ⟨fun k v hk => ?_, fun k v hk => hk⟩
      simp only [List.lookup_cons]
      have : (k == x) = false := by
        rw [beq_eq_false_iff_ne]; intro he; subst he; rw [hx] at hk; simp at hk
      simp [this, hk]

theorem addNode_sub (st : MacrocellWriterState) (L a b c d : UInt32) : MemoSub st (st.addNode L a b c d).2 := by
  unfold MacrocellWriterState.addNode
  cases hx : st.nodes.lookup (L, a, b, c, d) with
  | some _ => exact MemoSub.refl _
  | none =>
    refine ⟨fun k v hk => hk, fun k v hk => ?_⟩
    simp only [List.lookup_cons]
    have : (k == (L, a, b, c, d)) = false := by
      rw [beq_eq_false_iff_ne]; intro he; subst he; rw [hx] at hk; simp at hk
    simp [this, hk]

theorem addTree_sub : ∀ (m : MacroCell) (st : MacrocellWriterState), MemoSub st (st.addTree m).2
  | .level4Node _ nw ne sw se, st => by
    unfold MacrocellWriterState.addTree
    split
    · exact MemoSub.refl _
    · exact (addLeaf_sub _ _).trans ((addLeaf_sub _ _).trans ((addLeaf_sub _ _).trans
        ((addLeaf_sub _ _).trans (addNode_sub _ _ _ _ _ _))))
  | .cellNode _ nw ne sw se, st => by
    unfold MacrocellWriterState.addTree
    simp only
    generalize hs1 : st.addTree nw = s1
    generalize hs2 : s1.2.addTree ne = s2
    generalize hs3 : s2.2.addTree sw = s3
    generalize hs4 : s3.2.addTree se = s4
    have h := (hs1 ▸ addTree_sub nw st).trans ((hs2 ▸ addTree_sub ne s1.2).trans ((hs3 ▸ addTree_sub sw s2.2).trans
      (hs4 ▸ addTree_sub se s3.2)))
    split
    · exact h
    · exact h.trans (addNode_sub _ _ _ _ _ _)

theorem addLeaf_hit (st st' : MacrocellWriterState) (x : UInt64) (h : MemoSub (st.addLeaf x).2 st') :
    st'.addLeaf x = ((st.addLeaf x).1, st') := by
  unfold MacrocellWriterState.addLeaf at h ⊢
  by_cases h0 : (x == 0) = true
  · simp [h0]
  simp only [h0, Bool.false_eq_true, ite_false] at h ⊢
  cases hx : st.leaves.lookup x with
  | some id =>
    rw [hx] at h
    rw [h.1 x id hx]
  | none =>
    rw [hx] at h
    have := h.1 x st.nextId (by simp)
    rw [this]

theorem addNode_hit (st st' : MacrocellWriterState) (L a b c d : UInt32) (h : MemoSub (st.addNode L a b c d).2 st') :
    st'.addNode L a b c d = ((st.addNode L a b c d).1, st') := by
  unfold MacrocellWriterState.addNode at h ⊢
  cases hx : st.nodes.lookup (L, a, b, c, d) with
  | some id =>
    rw [hx] at h
    rw [h.2 _ id hx]
  | none =>
    rw [hx] at h
    have := h.2 (L, a, b, c, d) st.nextId (by simp)
    rw [this]

/-- `m` has been written as `id`: writing it again in any later state gives `id` and changes nothing. -/
def Processed (st : MacrocellWriterState) (m : MacroCell) (id : UInt32) : Prop :=
  ∀ st', MemoSub st st' → st'.addTree m = (id, st')

theorem Processed.mono {st st' : MacrocellWriterState} {m : MacroCell} {id : UInt32} (h : Processed st m id)
    (hs : MemoSub st st') : Processed st' m id :=
  fun st'' hs' => h st'' (hs.trans hs')

/-- What the DAG writer does for an entry, given its children's numbers. -/
def dagStep (st : MacrocellWriterState) (m : MacroCell) (c1 c2 c3 c4 : UInt32) : UInt32 × MacrocellWriterState :=
  match m with
  | .level4Node .. => st.addTree m
  | .cellNode _ nw _ _ _ =>
    if c1 == 0 && c2 == 0 && c3 == 0 && c4 == 0 then (0, st) else st.addNode (nw.level + 1) c1 c2 c3 c4

theorem addTree_eq_dagStep (st : MacrocellWriterState) (h : UInt32) (a b c d : MacroCell) (c1 c2 c3 c4 : UInt32)
    (p1 : Processed st a c1) (p2 : Processed st b c2) (p3 : Processed st c c3) (p4 : Processed st d c4) :
    st.addTree (.cellNode h a b c d) = dagStep st (.cellNode h a b c d) c1 c2 c3 c4 := by
  unfold MacrocellWriterState.addTree dagStep
  simp only [p1 st (MemoSub.refl _), p2 st (MemoSub.refl _), p3 st (MemoSub.refl _), p4 st (MemoSub.refl _)]

theorem processed_level4 (st : MacrocellWriterState) (h : UInt32) (nw ne sw se : UInt64) :
    Processed (st.addTree (.level4Node h nw ne sw se)).2 (.level4Node h nw ne sw se)
      (st.addTree (.level4Node h nw ne sw se)).1 := by
  intro st' hs
  unfold MacrocellWriterState.addTree at hs ⊢
  by_cases hz : (nw == 0 && ne == 0 && sw == 0 && se == 0) = true
  · simp only [hz, ite_true]
  simp only [hz, Bool.false_eq_true, ite_false] at hs ⊢
  generalize hs1 : st.addLeaf nw = s1 at hs ⊢
  generalize hs2 : s1.2.addLeaf ne = s2 at hs ⊢
  generalize hs3 : s2.2.addLeaf sw = s3 at hs ⊢
  generalize hs4 : s3.2.addLeaf se = s4 at hs ⊢
  have e5 := hs
  have e4 := (addNode_sub s4.2 4 s1.1 s2.1 s3.1 s4.1).trans e5
  have e3 := (hs4 ▸ addLeaf_sub s3.2 se).trans e4
  have e2 := (hs3 ▸ addLeaf_sub s2.2 sw).trans e3
  have e1 := (hs2 ▸ addLeaf_sub s1.2 ne).trans e2
  rw [addLeaf_hit st st' nw (hs1 ▸ e1), hs1, addLeaf_hit s1.2 st' ne (hs2 ▸ e2), hs2,
    addLeaf_hit s2.2 st' sw (hs3 ▸ e3), hs3, addLeaf_hit s3.2 st' se (hs4 ▸ e4), hs4]
  exact addNode_hit s4.2 st' 4 s1.1 s2.1 s3.1 s4.1 e5

theorem processed_cell (st : MacrocellWriterState) (h : UInt32) (a b c d : MacroCell) (c1 c2 c3 c4 : UInt32)
    (p1 : Processed st a c1) (p2 : Processed st b c2) (p3 : Processed st c c3) (p4 : Processed st d c4) :
    Processed (dagStep st (.cellNode h a b c d) c1 c2 c3 c4).2 (.cellNode h a b c d)
      (dagStep st (.cellNode h a b c d) c1 c2 c3 c4).1 := by
  intro st' hs
  simp only [dagStep] at hs ⊢
  by_cases hz : (c1 == 0 && c2 == 0 && c3 == 0 && c4 == 0) = true
  · simp only [hz, ite_true] at hs ⊢
    rw [addTree_eq_dagStep st' h a b c d c1 c2 c3 c4 (p1.mono hs) (p2.mono hs) (p3.mono hs) (p4.mono hs)]
    simp [dagStep, hz]
  · simp only [hz, Bool.false_eq_true, ite_false] at hs ⊢
    have hsub := (addNode_sub _ _ _ _ _ _).trans hs
    rw [addTree_eq_dagStep st' h a b c d c1 c2 c3 c4 (p1.mono hsub) (p2.mono hsub) (p3.mono hsub) (p4.mono hsub)]
    simp only [dagStep, hz, Bool.false_eq_true, ite_false]
    exact addNode_hit st st' _ _ _ _ _ hs

theorem dagStep_sub (st : MacrocellWriterState) (m : MacroCell) (c1 c2 c3 c4 : UInt32) :
    MemoSub st (dagStep st m c1 c2 c3 c4).2 := by
  unfold dagStep
  split
  · exact addTree_sub _ _
  · split
    · exact MemoSub.refl _
    · exact addNode_sub _ _ _ _ _ _

theorem dagStep_lines (st : MacrocellWriterState) (m : MacroCell) (c1 c2 c3 c4 : UInt32) :
    st.lines.length ≤ (dagStep st m c1 c2 c3 c4).2.lines.length := by
  unfold dagStep
  split
  · exact addTree_lines _ _
  · split
    · exact Nat.le_refl _
    · exact addNode_lines _ _ _ _ _ _

/-! ## The DAG writer's steps -/

theorem DagWriter.addEntry_rep {w : DagWriter} {st : MacrocellWriterState} (h : w.Rep st) (m : MacroCell)
    (c1 c2 c3 c4 : UInt32) (hl : (dagStep st m c1 c2 c3 c4).2.lines.length < 2 ^ 31) :
    (w.addEntry m c1 c2 c3 c4).1 = (dagStep st m c1 c2 c3 c4).1 ∧
      (w.addEntry m c1 c2 c3 c4).2.Rep (dagStep st m c1 c2 c3 c4).2 := by
  cases m with
  | level4Node hh nw ne sw se =>
    unfold DagWriter.addEntry dagStep at *
    unfold MacrocellWriterState.addTree at hl ⊢
    by_cases hz : (nw == 0 && ne == 0 && sw == 0 && se == 0) = true
    · simp only [hz, ite_true]; exact ⟨trivial, h⟩
    simp only [hz, Bool.false_eq_true, ite_false] at hl ⊢
    generalize hs1 : st.addLeaf nw = s1 at hl ⊢
    generalize hs2 : s1.2.addLeaf ne = s2 at hl ⊢
    generalize hs3 : s2.2.addLeaf sw = s3 at hl ⊢
    generalize hs4 : s3.2.addLeaf se = s4 at hl ⊢
    have l5 := addNode_lines s4.2 4 s1.1 s2.1 s3.1 s4.1
    have l4 := hs4 ▸ addLeaf_lines s3.2 se
    have l3 := hs3 ▸ addLeaf_lines s2.2 sw
    have l2 := hs2 ▸ addLeaf_lines s1.2 ne
    have l1 := hs1 ▸ addLeaf_lines st nw
    obtain ⟨r1, w1⟩ := DagWriter.addLeaf_rep h nw (by rw [hs1]; omega)
    rw [hs1] at r1 w1
    obtain ⟨r2, w2⟩ := DagWriter.addLeaf_rep w1 ne (by rw [hs2]; omega)
    rw [hs2] at r2 w2
    obtain ⟨r3, w3⟩ := DagWriter.addLeaf_rep w2 sw (by rw [hs3]; omega)
    rw [hs3] at r3 w3
    obtain ⟨r4, w4⟩ := DagWriter.addLeaf_rep w3 se (by rw [hs4]; omega)
    rw [hs4] at r4 w4
    obtain ⟨r5, w5⟩ := DagWriter.addNode_rep w4 4 s1.1 s2.1 s3.1 s4.1 hl
    simp only [r1, r2, r3, r4] at r5 w5 ⊢
    exact ⟨r5, w5⟩
  | cellNode hh nw ne sw se =>
    unfold DagWriter.addEntry dagStep at *
    by_cases hz : (c1 == 0 && c2 == 0 && c3 == 0 && c4 == 0) = true
    · simp only [hz, ite_true]; exact ⟨trivial, h⟩
    simp only [hz, Bool.false_eq_true, ite_false] at hl ⊢
    exact DagWriter.addNode_rep h _ _ _ _ _ hl

/-! ## Writing the entries -/

/-- Writes the trees `l` one after another. -/
def addTrees (st : MacrocellWriterState) : List MacroCell → MacrocellWriterState
  | [] => st
  | m :: ms => addTrees (st.addTree m).2 ms

theorem addTrees_lines : ∀ (l : List MacroCell) (st : MacrocellWriterState),
    st.lines.length ≤ (addTrees st l).lines.length
  | [], _ => Nat.le_refl _
  | m :: ms, st => Nat.le_trans (addTree_lines m st) (addTrees_lines ms _)

/-- The entries are a DAG: the children of each node entry are earlier entries, numbered in `kids`. -/
def DagWF (entries : Array MacroCell) (kids : Array UInt32) : Prop :=
  kids.size = 4 * entries.size ∧
    ∀ k < entries.size, ∀ h a b c d, entries[k]! = .cellNode h a b c d →
      kids[4 * k]!.toNat < k ∧ entries[kids[4 * k]!.toNat]! = a ∧
      kids[4 * k + 1]!.toNat < k ∧ entries[kids[4 * k + 1]!.toNat]! = b ∧
      kids[4 * k + 2]!.toNat < k ∧ entries[kids[4 * k + 2]!.toNat]! = c ∧
      kids[4 * k + 3]!.toNat < k ∧ entries[kids[4 * k + 3]!.toNat]! = d

theorem U64Buf.getElem!_of_rep {b : U64Buf} {a : Array UInt64} (h : U64Buf.Rep b a) (j : Nat) (hj : j < a.size) :
    b[j + 1]! = a[j]! := by
  obtain ⟨h0, hlt, -, harr⟩ := h
  have hsz : (U64Buf.toArray b).size = a.size := by rw [harr]
  rw [← harr]
  simp only [U64Buf.toArray, Array.size_extract] at hsz
  rw [getElem!_pos _ j (by rw [← harr] at hj; exact hj)]
  simp only [U64Buf.toArray, Array.getElem_extract]
  rw [getElem!_pos b (j + 1) (by omega)]
  congr 1; omega

theorem u32_toUInt64_toUInt32 (x : UInt32) : x.toUInt64.toUInt32 = x := by
  apply UInt32.toNat_inj.mp
  rw [UInt64.toNat_toUInt32, UInt32.toNat_toUInt64]
  have := UInt32.toNat_lt x; omega

theorem writeDag_spec (entries : Array MacroCell) (kids : Array UInt32) (hwf : DagWF entries kids)
    (hn : entries.size < 2 ^ 29) :
    ∀ (n k : Nat) (ids : U64Buf) (I : Array UInt64) (w : DagWriter) (st : MacrocellWriterState),
      entries.size - k = n → k ≤ entries.size → U64Buf.Rep ids I → I.size = k →
      (∀ j < k, Processed st entries[j]! I[j]!.toUInt32) → w.Rep st →
      (addTrees st (entries.toList.drop k)).lines.length < 2 ^ 31 →
      (writeDag entries kids k.toUInt32 entries.size.toUInt32 ids w).Rep
        (addTrees st (entries.toList.drop k)) := by
  have hs32 : entries.size < 2 ^ 32 := by omega
  intro n
  induction n with
  | zero =>
    intro k ids I w st hn' hk hids hI hp hw _
    have hnot : ¬ k.toUInt32 < entries.size.toUInt32 := by
      rw [u32_lt_size_iff hs32, u32_size_toNat (by omega)]; omega
    rw [writeDag]
    simp only [hnot, ↓reduceDIte, List.drop_eq_nil_of_le (show entries.toList.length ≤ k by simp; omega), addTrees]
    exact hw
  | succ n ih =>
    intro k ids I w st hn' hk hids hI hp hw hl
    have hlt : k < entries.size := by omega
    have hkU : k.toUInt32.toNat = k := u32_size_toNat (by omega)
    have hyes : k.toUInt32 < entries.size.toUInt32 := by rw [u32_lt_size_iff hs32, hkU]; exact hlt
    have hnext : k.toUInt32 + 1 = (k + 1).toUInt32 := by
      apply UInt32.toNat_inj.mp; rw [UInt32.toNat_add, hkU, u32_size_toNat (by omega)]; simp; omega
    have h4 : ∀ i < 4, (4 * k.toUInt32 + i.toUInt32).toNat = 4 * k + i := by
      intro i hi
      rw [UInt32.toNat_add, UInt32.toNat_mul, hkU, u32_size_toNat (by omega)]; simp; omega
    have hdrop := toList_drop_eq_cons entries k hlt
    rw [hdrop] at hl ⊢
    simp only [addTrees] at hl ⊢
    rw [writeDag]
    simp only [hyes, ↓reduceDIte, hkU]
    rw [hnext]
    have he : entries[k]! = entries[k] := getElem!_pos entries k hlt
    have hids' : ∀ j : UInt32, j.toNat < k → entryId ids j = I[j.toNat]!.toUInt32 := by
      intro j hj
      unfold entryId
      rw [UInt32.toNat_add, UInt32.toNat_one, Nat.mod_eq_of_lt (by omega),
        U64Buf.getElem!_of_rep hids _ (by omega)]
    -- The entry's number and the state after it, as `addTree` gives them.
    have key : ∀ (c1 c2 c3 c4 : UInt32), (∀ h a b c d, entries[k] = .cellNode h a b c d →
        Processed st a c1 ∧ Processed st b c2 ∧ Processed st c c3 ∧ Processed st d c4) →
        (w.addEntry entries[k] c1 c2 c3 c4).1 = (st.addTree entries[k]).1 ∧
          (w.addEntry entries[k] c1 c2 c3 c4).2.Rep (st.addTree entries[k]).2 ∧
          Processed (st.addTree entries[k]).2 entries[k] (st.addTree entries[k]).1 := by
      intro c1 c2 c3 c4 hc
      have hl' : (st.addTree entries[k]).2.lines.length < 2 ^ 31 := by
        have := addTrees_lines (entries.toList.drop (k + 1)) (st.addTree entries[k]).2; omega
      generalize entries[k] = m at hc hl' ⊢
      cases m with
      | level4Node hh nw ne sw se =>
        have := DagWriter.addEntry_rep hw (.level4Node hh nw ne sw se) c1 c2 c3 c4 hl'
        exact ⟨this.1, this.2, processed_level4 st hh nw ne sw se⟩
      | cellNode hh a b c d =>
        obtain ⟨p1, p2, p3, p4⟩ := hc hh a b c d rfl
        rw [addTree_eq_dagStep st hh a b c d c1 c2 c3 c4 p1 p2 p3 p4] at hl' ⊢
        have := DagWriter.addEntry_rep hw (.cellNode hh a b c d) c1 c2 c3 c4 hl'
        exact ⟨this.1, this.2, processed_cell st hh a b c d c1 c2 c3 c4 p1 p2 p3 p4⟩
    have e0 : (4 * k.toUInt32).toNat = 4 * k := by
      rw [UInt32.toNat_mul, hkU]; simp; omega
    have e1 : (4 * k.toUInt32 + 1).toNat = 4 * k + 1 := by
      rw [UInt32.toNat_add, UInt32.toNat_mul, hkU]; simp; omega
    have e2 : (4 * k.toUInt32 + 2).toNat = 4 * k + 2 := by
      rw [UInt32.toNat_add, UInt32.toNat_mul, hkU]; simp; omega
    have e3 : (4 * k.toUInt32 + 3).toNat = 4 * k + 3 := by
      rw [UInt32.toNat_add, UInt32.toNat_mul, hkU]; simp; omega
    rw [e0, e1, e2, e3]
    obtain ⟨k1, k2, kp⟩ := key (entryId ids kids[4 * k]!) (entryId ids kids[4 * k + 1]!)
      (entryId ids kids[4 * k + 2]!) (entryId ids kids[4 * k + 3]!) (by
        intro h a b c d heq
        obtain ⟨g0, a', g1, b', g2, c', g3, d'⟩ := hwf.2 k hlt h a b c d (by rw [he]; exact heq)
        rw [hids' _ g0, hids' _ g1, hids' _ g2, hids' _ g3]
        refine ⟨?_, ?_, ?_, ?_⟩
        · have := hp _ g0; rwa [a'] at this
        · have := hp _ g1; rwa [b'] at this
        · have := hp _ g2; rwa [c'] at this
        · have := hp _ g3; rwa [d'] at this)
    rw [he]
    generalize w.addEntry entries[k] (entryId ids kids[4 * k]!) (entryId ids kids[4 * k + 1]!)
      (entryId ids kids[4 * k + 2]!) (entryId ids kids[4 * k + 3]!) = r at k1 k2
    have hsub := addTree_sub entries[k] st
    have hpush := U64Buf.rep_push hids r.1.toUInt64 (by omega)
    refine ih (k + 1) _ (I.push r.1.toUInt64) _ _ (by omega) (by omega) hpush (by simp [hI]) ?_ k2 hl
    intro j hj
    by_cases hjk : j < k
    · have : (I.push r.1.toUInt64)[j]! = I[j]! := by
        rw [getElem!_pos _ j (by rw [Array.size_push]; omega), Array.getElem_push_lt (by omega),
          ← getElem!_pos I j (by omega)]
      rw [this]
      exact (hp j hjk).mono hsub
    · have hjk' : j = I.size := by omega
      have : (I.push r.1.toUInt64)[j]! = r.1.toUInt64 := by subst hjk'; simp
      rw [this, u32_toUInt64_toUInt32, k1, show j = k by omega, he]
      exact kp

/-! ## Round trip -/

theorem addTrees_append : ∀ (l1 l2 : List MacroCell) (st : MacrocellWriterState),
    addTrees st (l1 ++ l2) = addTrees (addTrees st l1) l2
  | [], _, _ => rfl
  | _ :: ms, l2, _ => addTrees_append ms l2 _

theorem addTrees_spec : ∀ (l : List MacroCell) (st : MacrocellWriterState) (N : Array MacroCell) (Lv : Array UInt64)
    (IL : Array Bool), Inv st N Lv IL → (∀ m ∈ l, Canonical m ∧ m.depth ≤ 63) →
    (addTrees st l).lines.length < 2 ^ 31 →
    ∃ N' Lv' IL', Inv (addTrees st l) N' Lv' IL' ∧
      ∀ p ∈ (addTrees st l).nodes, p ∈ st.nodes ∨ ∃ m ∈ l, p.1.1.toNat ≤ m.level.toNat
  | [], st, N, Lv, IL, h, _, _ => ⟨N, Lv, IL, h, fun p hp => Or.inl hp⟩
  | m :: ms, st, N, Lv, IL, h, hc, hl => by
    simp only [addTrees] at hl ⊢
    have hl1 := addTrees_lines ms (st.addTree m).2
    obtain ⟨hcan, hd⟩ := hc m (by simp)
    obtain ⟨N1, Lv1, IL1, hi1, -, -, hn1, -⟩ := addTree_spec m st N Lv IL h hcan hd (by omega)
    obtain ⟨N2, Lv2, IL2, hi2, hn2⟩ := addTrees_spec ms _ N1 Lv1 IL1 hi1 (fun m' hm' => hc m' (by simp [hm'])) hl
    refine ⟨N2, Lv2, IL2, hi2, fun p hp => ?_⟩
    rcases hn2 p hp with hp | ⟨m', hm', hle⟩
    · rcases hn1 p hp with hp | hle
      · exact Or.inl hp
      · exact Or.inr ⟨m, by simp, hle⟩
    · exact Or.inr ⟨m', by simp [hm'], hle⟩

theorem DagWriter.rep_initial (n : Nat) (hn : n < 2 ^ 29) :
    DagWriter.Rep ⟨GrowBuf.empty.push macrocellHeader, Array.replicate (4 * n.toUInt32 + 1).toNat [],
      Array.replicate (4 * n.toUInt32 + 1).toNat []⟩ ⟨[macrocellHeader], [], []⟩ := by
  have hc : (4 * n.toUInt32 + 1).toNat = 4 * n + 1 := by
    rw [UInt32.toNat_add, UInt32.toNat_mul, u32_size_toNat (by omega)]; simp; omega
  rw [hc]
  refine ⟨?_, ?_, ?_⟩
  · simpa using GrowBuf.rep_push (GrowBuf.rep_empty (α := String)) macrocellHeader (by decide)
  · exact ChainTable.rep_replicate leafSlot _ (by omega) (by omega)
      (fun k => leafSlot_lt k _ (by omega) (by omega))
  · exact ChainTable.rep_replicate nodeSlot _ (by omega) (by omega)
      (fun k => nodeSlot_lt k _ (by omega) (by omega))

/--
Round trip of the DAG writer: for the distinct subtrees `entries` of a tree, children first and the tree last, the
lines read back as the tree. (The writer numbers nodes by line, so it must write fewer than 2 ^ 31 lines.)
-/
theorem macrocell_dag_round_trip (entries : Array MacroCell) (kids : Array UInt32) (hwf : DagWF entries kids)
    (h0 : 0 < entries.size) (hn : entries.size < 2 ^ 29)
    (hcan : ∀ m ∈ entries, Canonical m ∧ m.depth ≤ 63)
    (hlev : ∀ j < entries.size - 1, entries[j]!.level.toNat < entries[entries.size - 1]!.level.toNat)
    (hsl : macrocellSingleLeaf entries[entries.size - 1]! = none)
    (hne : entries[entries.size - 1]! ≠ emptyMacroCellUInt32 entries[entries.size - 1]!.level)
    (hlen : (addTrees ⟨[macrocellHeader], [], []⟩ entries.toList).lines.length < 2 ^ 31) :
    deserializeMacrocell (serializeMacrocellDag entries kids) = ⟨.ok, #[], entries[entries.size - 1]!⟩ := by
  have hs32 : entries.size < 2 ^ 32 := by omega
  have hlast : (entries.size.toUInt32 - 1).toNat = entries.size - 1 := by
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, u32_size_toNat hs32]; simp; omega),
      u32_size_toNat hs32]; simp
  have hspec := writeDag_spec entries kids hwf hn _ 0 U64Buf.empty #[] _ _ rfl (by omega) U64Buf.rep_empty rfl
    (fun j hj => absurd hj (by omega)) (DagWriter.rep_initial entries.size hn) (by simpa using hlen)
  simp only [List.drop_zero, show (0 : Nat).toUInt32 = 0 from rfl] at hspec
  -- The entries are the earlier ones and then the root.
  have hsplit : entries.toList = entries.toList.take (entries.size - 1) ++ [entries[entries.size - 1]!] := by
    conv => lhs; rw [← List.take_append_drop (entries.size - 1) entries.toList]
    congr 1
    rw [List.drop_eq_getElem_cons (by simp; omega)]
    simp only [Array.getElem_toList]
    rw [List.drop_eq_nil_of_le (by simp; omega), getElem!_pos entries _ (by omega)]
  have hinit : ∀ m ∈ entries.toList.take (entries.size - 1), m ∈ entries ∧
      m.level.toNat < entries[entries.size - 1]!.level.toNat := by
    intro m hm
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hm
    simp only [List.length_take, Array.length_toList] at hj
    refine ⟨by simp, ?_⟩
    have := hlev j (by omega)
    rw [getElem!_pos entries j (by omega)] at this
    simpa using this
  have hrm : entries[entries.size - 1]! ∈ entries := by
    rw [getElem!_pos entries _ (by omega)]; exact Array.getElem_mem _
  generalize entries.toList.take (entries.size - 1) = init at hsplit hinit
  generalize hroot : entries[entries.size - 1]! = root at hsl hne hlev hsplit hinit hrm ⊢
  unfold serializeMacrocellDag
  simp only [hlast, hroot, hsl]
  rw [hspec.1.2.2.2]
  rw [hsplit, addTrees_append] at hlen ⊢
  simp only [addTrees] at hlen ⊢
  obtain ⟨hcr, hdr⟩ := hcan root hrm
  have hl1 := addTree_lines root (addTrees ⟨[macrocellHeader], [], []⟩ init)
  obtain ⟨N1, Lv1, IL1, hi1, hn1⟩ := addTrees_spec init _ #[] #[] #[] Inv.initial
    (fun m hm => hcan m (hinit m hm).1) (by omega)
  obtain ⟨N', Lv', IL', hinv, -, hc, -, hlast'⟩ := addTree_spec root _ N1 Lv1 IL1 hi1 hcr hdr hlen
  have hid : ((addTrees ⟨[macrocellHeader], [], []⟩ init).addTree root).1 ≠ 0 := by
    intro h0
    rw [h0] at hc
    simp only [cellChildA, beq_self_eq_true, ite_true, Option.some.injEq] at hc
    exact hne hc.symm
  have hlow : ∀ p ∈ (addTrees ⟨[macrocellHeader], [], []⟩ init).nodes, p.1.1.toNat < root.level.toNat := by
    intro p hp
    rcases hn1 p hp with hp | ⟨m, hm, hle⟩
    · simp at hp
    · have := (hinit m hm).2; omega
  obtain ⟨hN, hm⟩ := hlast' hlow hid
  obtain ⟨ls, hls, hr, hll, -⟩ := hinv
  rw [deserializeMacrocell_reads hr _ (by simp [hls]) (by simpa using hll) hN, hm]

/-- A single leaf is written as just its leaf line, as by `serializeMacrocell`. -/
theorem serializeMacrocellDag_single_leaf (entries : Array MacroCell) (kids : Array UInt32) (h0 : 0 < entries.size)
    (hs : entries.size < 2 ^ 32) (leaf : UInt64)
    (hsl : macrocellSingleLeaf entries[entries.size - 1]! = some leaf) :
    serializeMacrocellDag entries kids = serializeMacrocell entries[entries.size - 1]! := by
  have hlast : (entries.size.toUInt32 - 1).toNat = entries.size - 1 := by
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, u32_size_toNat hs]; simp; omega),
      u32_size_toNat hs]; simp
  unfold serializeMacrocellDag serializeMacrocell
  simp only [hlast, hsl]

end Algorithm
