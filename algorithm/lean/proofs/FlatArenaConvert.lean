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
import proofs.FlatArenaQuery
import proofs.HashLifeConfinementProofs
import proofs.MacroCellQueryProofs
import proofs.MacroCellEngineProofs
import proofs.HashLifeProofs

local notation "ℕ" => Nat
local notation "ℤ" => Int

namespace Algorithm

/-!
# Flat HashLife arena: converting cell states

The conversions `FlatHashLifeCellState.kt` makes between other cell states and a flat arena:
- `importMacroCellNode`, driven node by node by the memoized recursion of `internMacroCellDag` (modeled by
  `DagIntern`), imports a `MacroCell` DAG exactly;
- `foldCellsInWindow` and `foldAllCells` call a function once on each live cell of a root, in a fixed order;
- `cellsToMacroCell` builds the quadtree of a list of cells, which `buildQuadtreeBottomUp` imports with the DAG
  import.
-/

-- =========================================================================
-- Importing a MacroCell DAG
-- =========================================================================

theorem importMacroCellNode_spec {a : FlatHashLifeArena} (hwf : ArenaWF a) {m : MacroCell} {d : ℕ}
    (hm : WFd m d) (hd : d < 2 ^ 32) (H : HashOK m) {i1 i2 i3 i4 : UInt32}
    (hc : ∀ (hh : UInt32) (nw ne sw se : MacroCell), m = .cellNode hh nw ne sw se →
      importNeedsChildren m = true →
      (i1 ≠ UNCOMPUTED → NodeIs a (d - 5) i1 nw) ∧ (i2 ≠ UNCOMPUTED → NodeIs a (d - 5) i2 ne) ∧
      (i3 ≠ UNCOMPUTED → NodeIs a (d - 5) i3 sw) ∧ (i4 ≠ UNCOMPUTED → NodeIs a (d - 5) i4 se)) :
    Grows a (a.importMacroCellNode m i1 i2 i3 i4).2 ∧
    ((a.importMacroCellNode m i1 i2 i3 i4).1 ≠ UNCOMPUTED →
      NodeIs (a.importMacroCellNode m i1 i2 i3 i4).2 (d - 4) (a.importMacroCellNode m i1 i2 i3 i4).1 m) ∧
    ((a.importMacroCellNode m i1 i2 i3 i4).1 = UNCOMPUTED →
      (a.importMacroCellNode m i1 i2 i3 i4).2.overflow ≠ 0 ∨ 60 < d ∨
      (importNeedsChildren m = true ∧
        (i1 = UNCOMPUTED ∨ i2 = UNCOMPUTED ∨ i3 = UNCOMPUTED ∨ i4 = UNCOMPUTED))) := by
  cases m with
  | level4Node hh nw ne sw se =>
    rw [WFd_level4Node_iff] at hm
    subst hm
    have hM : MacroCell.level4Node hh nw ne sw se = makeLevel4Node nw ne sw se := by
      rw [show hh = level4Hash nw ne sw se from H]
      rfl
    unfold FlatHashLifeArena.importMacroCellNode
    have s := internLevel4_spec hwf nw ne sw se
    rcases e : a.internLevel4 nw ne sw se with ⟨l4Id, a1⟩
    rw [e] at s
    obtain ⟨g, n⟩ := s
    simp only [e]
    split
    · rename_i hov
      exact ⟨g, fun h => absurd rfl h, fun _ => Or.inl (by simpa using hov)⟩
    · rename_i hov
      refine ⟨g, fun _ => by rw [hM]; exact n (by simpa using hov), fun h => ?_⟩
      exact absurd h (n (by simpa using hov)).ne_uncomputed
  | cellNode hh nw ne sw se =>
    have hm' := (WFd_cellNode_iff _ _ _ _ _ _).mp hm
    obtain ⟨h5, w1, w2, w3, w4⟩ := hm'
    have hM : MacroCell.cellNode hh nw ne sw se = makeCellNode nw ne sw se := by
      rw [H.1]
      rfl
    have hlev := WFd_level_toNat hm hd
    unfold FlatHashLifeArena.importMacroCellNode
    dsimp only
    split
    · -- empty
      rename_i hE
      have hE' := hE
      unfold importsAsEmpty at hE'
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hE'
      obtain ⟨hs, hl⟩ := hE'
      rw [UInt32.le_iff_toNat_le, hlev] at hl
      have hl' : d ≤ 31 := by simpa using hl
      have hsize := size_toNat_of_WFd hm hl'
      rw [hs] at hsize
      have hemp := eq_emptyNode_of_size_zero hm H (by simpa using hsize.symm)
      have hn := NodeIs.emptyCell hwf (d - 5) (by omega)
      have hid : (MacroCell.cellNode hh nw ne sw se).level - 5 = (d - 5).toUInt32 := by
        apply u32_eq_of_toNat
        rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, hlev]; simp; omega), hlev]
        simp
        omega
      refine ⟨Grows.refl hwf, fun _ => ?_, fun h => ?_⟩
      · rw [hid, hemp, show d - 4 = d - 5 + 1 by omega]
        rw [show d = d - 5 + 5 by omega] at hemp ⊢
        simpa using hn
      · exact absurd h (by rw [hid]; exact hn.ne_uncomputed)
    · rename_i hE
      split
      · rename_i h60
        refine ⟨Grows.refl hwf, fun h => absurd rfl h, fun _ => Or.inr (Or.inl ?_)⟩
        rw [gt_iff_lt, UInt32.lt_iff_toNat_lt, hlev] at h60
        simpa using h60
      · rename_i h60
        have hd60 : d ≤ 60 := by
          rw [gt_iff_lt, UInt32.lt_iff_toNat_lt, hlev] at h60
          simpa using h60
        have hneeds : importNeedsChildren (MacroCell.cellNode hh nw ne sw se) = true := by
          simp only [importNeedsChildren, hE, Bool.not_false, Bool.true_and, decide_eq_true_eq]
          rw [UInt32.le_iff_toNat_le, hlev]
          simpa using hd60
        split
        · rename_i hU
          refine ⟨Grows.refl hwf, fun h => absurd rfl h, fun _ => Or.inr (Or.inr ⟨hneeds, ?_⟩)⟩
          simpa [or_assoc] using hU
        · rename_i hU
          simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hU
          obtain ⟨⟨⟨u1, u2⟩, u3⟩, u4⟩ := hU
          obtain ⟨n1, n2, n3, n4⟩ := hc hh nw ne sw se rfl hneeds
          have hl8 : ((MacroCell.cellNode hh nw ne sw se).level.toUInt8).toNat = d - 5 + 5 := by
            rw [UInt32.toNat_toUInt8, hlev]
            omega
          have s := internCellNode_spec hwf hl8 (n1 u1) (n2 u2) (n3 u3) (n4 u4)
          rcases e : a.internCellNode (MacroCell.cellNode hh nw ne sw se).level.toUInt8 i1 i2 i3 i4 with
            ⟨cellId, a1⟩
          rw [e] at s
          obtain ⟨g, n⟩ := s
          dsimp only at g n ⊢
          split
          · rename_i hov
            exact ⟨g, fun h => absurd rfl h, fun _ => Or.inl (by simpa using hov)⟩
          · rename_i hov
            have hn := n (by simpa using hov)
            refine ⟨g, fun _ => ?_, fun h => absurd h hn.ne_uncomputed⟩
            rw [hM, show d - 4 = d - 5 + 1 by omega]
            exact hn

theorem WFd_depth_unique {m : MacroCell} {d d' : ℕ} (h : WFd m d) (h' : WFd m d') (hd : d < 2 ^ 32)
    (hd' : d' < 2 ^ 32) : d = d' := by
  have := WFd_level_toNat h hd
  have := WFd_level_toNat h' hd'
  omega

/--
Every memo entry of the DAG import is correct for `a`: a set id is a node of `a` denoting the entry's node, and
an unset id (`UNCOMPUTED`) was only stored after the arena failed.
-/
def MemoOK (a : FlatHashLifeArena) (memo : List (MacroCell × UInt32)) : Prop :=
  ∀ n id, (n, id) ∈ memo →
    (id ≠ UNCOMPUTED → ∀ d, WFd n d → d < 2 ^ 32 → NodeIs a (d - 4) id n) ∧
    (id = UNCOMPUTED → a.overflow ≠ 0)

theorem Grows.overflow_ne {a b : FlatHashLifeArena} (g : Grows a b) (h : a.overflow ≠ 0) : b.overflow ≠ 0 :=
  fun hb => h (g.ovf hb)

theorem MemoOK.grows {a b : FlatHashLifeArena} (hwf : ArenaWF a) {memo : List (MacroCell × UInt32)}
    (hm : MemoOK a memo) (g : Grows a b) : MemoOK b memo := fun n id hmem =>
  ⟨fun hne d hd hd32 => g.node hwf ((hm n id hmem).1 hne d hd hd32),
    fun hu => g.overflow_ne ((hm n id hmem).2 hu)⟩

theorem MemoOK.cons {a : FlatHashLifeArena} {memo : List (MacroCell × UInt32)} (hm : MemoOK a memo)
    {m : MacroCell} {id : UInt32} {d : ℕ} (hmd : WFd m d) (hd : d < 2 ^ 32)
    (hn : id ≠ UNCOMPUTED → NodeIs a (d - 4) id m) (hu : id = UNCOMPUTED → a.overflow ≠ 0) :
    MemoOK a ((m, id) :: memo) := by
  intro n id' hmem
  rcases List.mem_cons.mp hmem with e | e
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
    exact ⟨fun hne d' hd' hd32 => WFd_depth_unique hmd hd' hd hd32 ▸ hn hne, hu⟩
  · exact hm n id' e

/--
The DAG import model is correct: started from a well-formed arena and a correct memo table on a well-formed,
hash-consistent node of depth at most 60, it grows the arena, keeps the memo table correct, and returns a node
denoting `m` unless the arena failed.
-/
theorem dagIntern_spec {memo memo' : List (MacroCell × UInt32)} {a a' : FlatHashLifeArena} {m : MacroCell}
    {id : UInt32} (hrun : DagIntern memo a m id memo' a') :
    ArenaWF a → MemoOK a memo → ∀ d, WFd m d → d ≤ 60 → HashOK m →
      Grows a a' ∧ MemoOK a' memo' ∧ (id ≠ UNCOMPUTED → NodeIs a' (d - 4) id m) ∧
      (id = UNCOMPUTED → a'.overflow ≠ 0) := by
  induction hrun with
  | hit hmem =>
    intro hwf hmo d hd _ _
    exact ⟨Grows.refl hwf, hmo, fun hne => (hmo _ _ hmem).1 hne d hd (by omega), (hmo _ _ hmem).2⟩
  | @leaf memo a m hneeds =>
    intro hwf hmo d hd h60 H
    have s := importMacroCellNode_spec hwf hd (by omega) H (i1 := UNCOMPUTED) (i2 := UNCOMPUTED)
      (i3 := UNCOMPUTED) (i4 := UNCOMPUTED) (fun _ _ _ _ _ _ h => by rw [hneeds] at h; exact absurd h (by decide))
    obtain ⟨g, hn, hu⟩ := s
    have hu' : (a.importMacroCellNode m UNCOMPUTED UNCOMPUTED UNCOMPUTED UNCOMPUTED).1 = UNCOMPUTED →
        (a.importMacroCellNode m UNCOMPUTED UNCOMPUTED UNCOMPUTED UNCOMPUTED).2.overflow ≠ 0 := fun h => by
      rcases hu h with h' | h' | h'
      · exact h'
      · omega
      · rw [hneeds] at h'
        exact absurd h'.1 (by decide)
    exact ⟨g, (hmo.grows hwf g).cons hd (by omega) hn hu', hn, hu'⟩
  | @node memo memo1 memo2 memo3 memo4 a a1 a2 a3 a4 hh nw ne sw se i1 i2 i3 i4 hneeds _ _ _ _ ih1 ih2 ih3 ih4 =>
    intro hwf hmo d hd h60 H
    have hd' := (WFd_cellNode_iff _ _ _ _ _ _).mp hd
    obtain ⟨h5, w1, w2, w3, w4⟩ := hd'
    obtain ⟨_, H1, H2, H3, H4⟩ := H
    obtain ⟨g1, m1, n1, u1⟩ := ih1 hwf hmo (d - 1) w1 (by omega) H1
    obtain ⟨g2, m2, n2, u2⟩ := ih2 g1.wf m1 (d - 1) w2 (by omega) H2
    obtain ⟨g3, m3, n3, u3⟩ := ih3 g2.wf m2 (d - 1) w3 (by omega) H3
    obtain ⟨g4, m4, n4, u4⟩ := ih4 g3.wf m3 (d - 1) w4 (by omega) H4
    have e5 : d - 1 - 4 = d - 5 := by omega
    rw [e5] at n1 n2 n3 n4
    have s := importMacroCellNode_spec g4.wf hd (by omega) ⟨by assumption, H1, H2, H3, H4⟩
      (i1 := i1) (i2 := i2) (i3 := i3) (i4 := i4) (fun hh' nw' ne' sw' se' e _ => by
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := MacroCell.cellNode.inj e
        exact ⟨fun h => (g2.trans (g3.trans g4)).node g1.wf (n1 h), fun h => (g3.trans g4).node g2.wf (n2 h),
          fun h => g4.node g3.wf (n3 h), n4⟩)
    obtain ⟨g, hn, hu⟩ := s
    have g14 := g1.trans (g2.trans (g3.trans g4))
    have hu' : (a4.importMacroCellNode (.cellNode hh nw ne sw se) i1 i2 i3 i4).1 = UNCOMPUTED →
        (a4.importMacroCellNode (.cellNode hh nw ne sw se) i1 i2 i3 i4).2.overflow ≠ 0 := fun h => by
      rcases hu h with h' | h' | ⟨_, h' | h' | h' | h'⟩
      · exact h'
      · omega
      · exact g.overflow_ne ((g2.trans (g3.trans g4)).overflow_ne (u1 h'))
      · exact g.overflow_ne ((g3.trans g4).overflow_ne (u2 h'))
      · exact g.overflow_ne (g4.overflow_ne (u3 h'))
      · exact g.overflow_ne (u4 h')
    exact ⟨g14.trans g, (m4.grows g4.wf g).cons hd (by omega) hn hu', hn, hu'⟩

/--
Importing a well-formed, hash-consistent HashLife state whose root is a CellNode of depth at most 60 into a
non-failed well-formed arena, by the recursion of `internMacroCellDag` from an empty memo table, keeps every node
of the arena, returns a root denoting exactly the state at the same corner, and fails only when a node table is
full.
-/
theorem internMacroCellDag_Impl {a : FlatHashLifeArena} (hwf : ArenaWF a) (hov : a.overflow = 0)
    (st : HashLifeCellState) (ox oy : Int32) (hoff : st.offset = (ox.toInt, oy.toInt)) {d : ℕ}
    (hm : WFd st.macroCell d) (h5 : 5 ≤ d) (h60 : d ≤ 60) (H : HashOK st.macroCell)
    {id : UInt32} {memo : List (MacroCell × UInt32)} {a' : FlatHashLifeArena}
    (hrun : DagIntern [] a st.macroCell id memo a') :
    ArenaWF a' ∧ NodesPreserved a a' ∧
    (id ≠ UNCOMPUTED → id < a'.cellCount ∧ flatState a' ox oy id = st) ∧
    (id = UNCOMPUTED → ArenaFull a') := by
  obtain ⟨g, _, hn, hu⟩ := dagIntern_spec hrun hwf (fun _ _ h => absurd h List.not_mem_nil) d hm h60 H
  refine ⟨g.wf, g.nodes hwf, fun hne => ?_, fun h => (g.cap (hu h)).resolve_left (fun h' => h' hov)⟩
  have hn' := hn hne
  rw [show d - 4 = d - 5 + 1 by omega] at hn'
  refine ⟨hn'.lt_cell, ?_⟩
  unfold flatState
  rw [hn'.denoteCell_eq, ← hoff]

-- =========================================================================
-- Enumerating live cells
-- =========================================================================

/-- A fold, from an accumulator of any type, over the keys of a list of cells. -/
abbrev KeyFold := ∀ {α : Type}, (α → UInt64 → α) → α → α

/--
The key the enumeration computes for a cell (`cellKeyOf` of its 64-bit coordinates). It is `coordKey` on cells with
32-bit coordinates.
-/
def enumKey (c : Coord) : UInt64 := cellKeyOf (Int64.ofInt c.1) (Int64.ofInt c.2)

theorem cellKeyOf_enumKey (x y : Int64) : cellKeyOf x y = enumKey (x.toInt, y.toInt) := by
  simp [enumKey]

/--
`run` folds `f` over the keys `enumKey c` of a duplicate-free list of cells, exactly those satisfying `P`, in a fixed
order that does not depend on `f`.
-/
def FoldsAs (run : KeyFold) (P : Coord → Prop) : Prop :=
  ∃ L : List Coord, L.Nodup ∧ (∀ c, c ∈ L ↔ P c) ∧
    ∀ (α : Type) (f : α → UInt64 → α) (acc : α), run f acc = L.foldl (fun a c => f a (enumKey c)) acc

theorem FoldsAs.refl {P : Coord → Prop} (h : ∀ c, ¬ P c) : FoldsAs (fun _ acc => acc) P :=
  ⟨[], List.nodup_nil, fun c => by simp [h c], fun _ _ _ => rfl⟩

theorem FoldsAs.congr {run run' : KeyFold} {P Q : Coord → Prop}
    (h : FoldsAs run P) (e : ∀ c, P c ↔ Q c) (er : ∀ (α : Type) (f : α → UInt64 → α) acc, run' f acc = run f acc) :
    FoldsAs run' Q := by
  obtain ⟨L, n, m, r⟩ := h
  exact ⟨L, n, fun c => (m c).trans (e c), fun α f acc => (er α f acc).trans (r α f acc)⟩

theorem FoldsAs.seq {r1 r2 : KeyFold} {P Q : Coord → Prop}
    (h1 : FoldsAs r1 P) (h2 : FoldsAs r2 Q) (hd : ∀ c, P c → Q c → False) :
    FoldsAs (fun f acc => r2 f (r1 f acc)) (fun c => P c ∨ Q c) := by
  obtain ⟨L1, n1, m1, e1⟩ := h1
  obtain ⟨L2, n2, m2, e2⟩ := h2
  refine ⟨L1 ++ L2, ?_, fun c => by simp [m1, m2], fun α f acc => by
    have e1' := e1 α f; have e2' := e2 α f; dsimp only at e1' e2' ⊢; rw [e1', e2', List.foldl_append]⟩
  rw [List.nodup_append]
  exact ⟨n1, n2, fun a ha b hb hab => hd a ((m1 a).mp ha) (hab ▸ (m2 b).mp hb)⟩

theorem FoldsAs.single (c : Coord) : FoldsAs (fun f acc => f acc (enumKey c)) (fun p => p = c) :=
  ⟨[c], by simp, fun p => by simp, fun _ _ _ => rfl⟩

/-- Four folds whose cells lie in the four quadrants (split at `(X + w, Y + w)`) make one fold. -/
theorem FoldsAs.quad {r1 r2 r3 r4 : KeyFold} {P1 P2 P3 P4 : Coord → Prop}
    (X Y w : ℤ) (h1 : FoldsAs r1 P1) (h2 : FoldsAs r2 P2) (h3 : FoldsAs r3 P3) (h4 : FoldsAs r4 P4)
    (q1 : ∀ c, P1 c → c.1 < X + w ∧ c.2 < Y + w) (q2 : ∀ c, P2 c → X + w ≤ c.1 ∧ c.2 < Y + w)
    (q3 : ∀ c, P3 c → c.1 < X + w ∧ Y + w ≤ c.2) (q4 : ∀ c, P4 c → X + w ≤ c.1 ∧ Y + w ≤ c.2) :
    FoldsAs (fun f acc => r4 f (r3 f (r2 f (r1 f acc)))) (fun c => P1 c ∨ P2 c ∨ P3 c ∨ P4 c) := by
  have a12 := h1.seq h2 fun c p q => by have := q1 c p; have := q2 c q; omega
  have a123 := a12.seq h3 fun c p q => by
    rcases p with p | p
    · have := q1 c p; have := q3 c q; omega
    · have := q2 c p; have := q3 c q; omega
  have a1234 := a123.seq h4 fun c p q => by
    rcases p with (p | p) | p
    · have := q1 c p; have := q4 c q; omega
    · have := q2 c p; have := q4 c q; omega
    · have := q3 c p; have := q4 c q; omega
  exact a1234.congr (fun c => by simp only [or_assoc]) fun _ _ _ => rfl

theorem i64_toUInt64_toNat {x : Int64} (h : 0 ≤ x.toInt) : x.toUInt64.toNat = x.toInt.toNat := by
  rw [Int64.toNat_toUInt64_of_le (Int64.le_iff_toInt_le.mpr (by simpa using h))]
  rfl

theorem cellKeyOf_eq {x y : Int64} (hx1 : -2 ^ 31 ≤ x.toInt) (hx2 : x.toInt < 2 ^ 31) (hy1 : -2 ^ 31 ≤ y.toInt)
    (hy2 : y.toInt < 2 ^ 31) : cellKeyOf x y = coordKey (x.toInt, y.toInt) := by
  have h31 : (2147483648 : Int64).toInt = 2 ^ 31 := by decide
  have ex : (x + 2147483648).toInt = x.toInt + 2 ^ 31 := by rw [i64_add_toInt (by rw [h31]; omega)
    (by rw [h31]; omega), h31]
  have ey : (y + 2147483648).toInt = y.toInt + 2 ^ 31 := by rw [i64_add_toInt (by rw [h31]; omega)
    (by rw [h31]; omega), h31]
  have nx := i64_toUInt64_toNat (x := x + 2147483648) (by rw [ex]; omega)
  have ny := i64_toUInt64_toNat (x := y + 2147483648) (by rw [ey]; omega)
  rw [ex] at nx
  rw [ey] at ny
  apply UInt64.toNat_inj.mp
  unfold cellKeyOf coordKey
  rw [UInt64.toNat_add, UInt64.toNat_shiftLeft, nx, ny, UInt64.toNat_ofNat']
  have : (32 : UInt64).toNat % 64 = 32 := rfl
  rw [this, Nat.shiftLeft_eq]
  dsimp only
  omega

theorem keyCoord_coordKey {c : Coord} (h : InWindow (-2 ^ 31) (-2 ^ 31) (2 ^ 31) (2 ^ 31) c) :
    keyCoord (coordKey c) = c := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold keyCoord coordKey
  rw [UInt64.toNat_ofNat']
  apply Prod.ext <;> dsimp only <;> omega

theorem u32_toInt64_toInt (x : UInt32) : x.toUInt64.toInt64.toInt = x.toNat := by
  have hx := x.toNat_lt
  have h1 : x.toUInt64.toNat = x.toNat := UInt32.toNat_toUInt64 x
  have h2 : x.toUInt64.toInt64.toInt = x.toUInt64.toNat := by
    rw [UInt64.toInt64, Int64.toInt]
    simp only [BitVec.toInt]
    have h3 : x.toUInt64.toBitVec.toNat = x.toNat := by rw [UInt64.toNat_toBitVec, h1]
    change (if 2 * x.toUInt64.toBitVec.toNat < 2 ^ 64 then (x.toUInt64.toBitVec.toNat : ℤ)
      else (x.toUInt64.toBitVec.toNat : ℤ) - ((2 ^ 64 : ℕ) : ℤ)) = _
    rw [h3, h1, ite_eq_left (by omega)]
  rw [h2, h1]

/-- The window and coordinate bounds under which the enumeration's 64-bit arithmetic is exact. -/
structure EnumBounds (l t r b : Int64) : Prop where
  l : -2 ^ 31 ≤ l.toInt
  t : -2 ^ 31 ≤ t.toInt
  r : r.toInt ≤ 2 ^ 31
  b : b.toInt ≤ 2 ^ 31

/-- The live cells of leaf `leaf` at `(X, Y)` in the window, from leaf cell index `i` on. -/
def LeafP (leaf : UInt64) (X Y : ℤ) (l t r b : Int64) (i : ℕ) (c : Coord) : Prop :=
  InWindow l.toInt t.toInt r.toInt b.toInt c ∧ leafAt leaf (c.1 - X) (c.2 - Y) = true ∧
    (i : ℤ) ≤ (c.2 - Y) * 8 + (c.1 - X)

theorem foldLeafCellsLoop_spec (leaf : UInt64) {x0 y0 l t r b : Int64}
    (hx : -2 ^ 62 ≤ x0.toInt ∧ x0.toInt ≤ 2 ^ 62) (hy : -2 ^ 62 ≤ y0.toInt ∧ y0.toInt ≤ 2 ^ 62) :
    ∀ (n : ℕ) (i : UInt32), 64 - i.toNat = n → i.toNat ≤ 64 →
      FoldsAs (fun f acc => foldLeafCellsLoop leaf x0 y0 l t r b f i acc)
        (LeafP leaf x0.toInt y0.toInt l t r b i.toNat) := by
  intro n
  induction n with
  | zero =>
    intro i hn hi
    have hnone : ∀ c, ¬ LeafP leaf x0.toInt y0.toInt l t r b i.toNat c := fun c ⟨_, hl, hidx⟩ => by
      have := leafAt_bounds hl
      omega
    refine (FoldsAs.refl hnone).congr (fun _ => Iff.rfl) fun _ f acc => ?_
    show foldLeafCellsLoop leaf x0 y0 l t r b f i acc = acc
    rw [foldLeafCellsLoop, dite_eq_right (by rw [UInt32.lt_iff_toNat_lt]; simp; omega)]
  | succ n ih =>
    intro i hn hi
    have hi64 : i < 64 := by rw [UInt32.lt_iff_toNat_lt]; simp; omega
    have hx7 : (i &&& 7).toNat = i.toNat % 8 := by
      rw [UInt32.toNat_and]
      have : (7 : UInt32).toNat = 2 ^ 3 - 1 := rfl
      rw [this, Nat.and_two_pow_sub_one_eq_mod]
    have hy3 : (i >>> 3).toNat = i.toNat / 8 := by
      rw [UInt32.toNat_shiftRight]
      have : (3 : UInt32).toNat % 32 = 3 := rfl
      rw [this, Nat.shiftRight_eq_div_pow]
    have hi1 : (i + 1).toNat = i.toNat + 1 := by
      rw [UInt32.toNat_add]
      simp only [UInt32.toNat_one]
      omega
    have hcx : (x0 + (i &&& 7).toUInt64.toInt64).toInt = x0.toInt + (i.toNat % 8 : ℕ) := by
      rw [i64_add_toInt (by rw [u32_toInt64_toInt, hx7]; omega) (by rw [u32_toInt64_toInt, hx7]; omega),
        u32_toInt64_toInt, hx7]
    have hcy : (y0 + (i >>> 3).toUInt64.toInt64).toInt = y0.toInt + (i.toNat / 8 : ℕ) := by
      rw [i64_add_toInt (by rw [u32_toInt64_toInt, hy3]; omega) (by rw [u32_toInt64_toInt, hy3]; omega),
        u32_toInt64_toInt, hy3]
    have hleaf : leafContains leaf (i &&& 7) (i >>> 3) =
        leafAt leaf ((i.toNat % 8 : ℕ) : ℤ) ((i.toNat / 8 : ℕ) : ℤ) := by
      rw [leafContains_toNat leaf _ _ (by rw [hx7]; omega) (by rw [hy3]; omega), hx7, hy3]
    have hrest : FoldsAs (fun f acc => foldLeafCellsLoop leaf x0 y0 l t r b f (i + 1) acc)
        (LeafP leaf x0.toInt y0.toInt l t r b (i.toNat + 1)) := by
      have := ih (i + 1) (by omega) (by omega)
      rwa [hi1] at this
    have hstep : ∀ {α : Type} (f : α → UInt64 → α) (acc : α), foldLeafCellsLoop leaf x0 y0 l t r b f i acc =
        foldLeafCellsLoop leaf x0 y0 l t r b f (i + 1)
          (if (leafContains leaf (i &&& 7) (i >>> 3) && l ≤ x0 + (i &&& 7).toUInt64.toInt64 &&
              x0 + (i &&& 7).toUInt64.toInt64 < r && t ≤ y0 + (i >>> 3).toUInt64.toInt64 &&
              y0 + (i >>> 3).toUInt64.toInt64 < b) = true then
            f acc (cellKeyOf (x0 + (i &&& 7).toUInt64.toInt64) (y0 + (i >>> 3).toUInt64.toInt64))
          else acc) := by
      intro _ f acc
      rw [foldLeafCellsLoop, dite_eq_left hi64]
    generalize hcxv : x0 + (i &&& 7).toUInt64.toInt64 = cx at hcx hstep
    generalize hcyv : y0 + (i >>> 3).toUInt64.toInt64 = cy at hcy hstep
    have hcell : ∀ c : Coord, LeafP leaf x0.toInt y0.toInt l t r b i.toNat c ↔
        (c = (cx.toInt, cy.toInt) ∧ InWindow l.toInt t.toInt r.toInt b.toInt c ∧
          leafAt leaf ((i.toNat % 8 : ℕ) : ℤ) ((i.toNat / 8 : ℕ) : ℤ) = true) ∨
        LeafP leaf x0.toInt y0.toInt l t r b (i.toNat + 1) c := by
      intro c
      unfold LeafP
      constructor
      · rintro ⟨hw', hl, hidx⟩
        have hb := leafAt_bounds hl
        by_cases e : (i.toNat : ℤ) = (c.2 - y0.toInt) * 8 + (c.1 - x0.toInt)
        · left
          have e1 : c.1 - x0.toInt = ((i.toNat % 8 : ℕ) : ℤ) := by omega
          have e2 : c.2 - y0.toInt = ((i.toNat / 8 : ℕ) : ℤ) := by omega
          refine ⟨Prod.ext (by rw [hcx]; omega) (by rw [hcy]; omega), hw', ?_⟩
          rw [← e1, ← e2]
          exact hl
        · right
          exact ⟨hw', hl, by push_cast; omega⟩
      · rintro (⟨rfl, hw', hl⟩ | ⟨hw', hl, hidx⟩)
        · refine ⟨hw', ?_, ?_⟩
          · rw [hcx, hcy, show x0.toInt + ((i.toNat % 8 : ℕ) : ℤ) - x0.toInt = ((i.toNat % 8 : ℕ) : ℤ) by omega,
              show y0.toInt + ((i.toNat / 8 : ℕ) : ℤ) - y0.toInt = ((i.toNat / 8 : ℕ) : ℤ) by omega]
            exact hl
          · rw [hcx, hcy]
            omega
        · exact ⟨hw', hl, by push_cast at hidx; omega⟩
    by_cases hc : (leafContains leaf (i &&& 7) (i >>> 3) && l ≤ cx && cx < r && t ≤ cy && cy < b) = true
    · have hc' := hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc'
      obtain ⟨⟨⟨⟨hlc, h1⟩, h2⟩, h3⟩, h4⟩ := hc'
      rw [Int64.le_iff_toInt_le] at h1 h3
      rw [Int64.lt_iff_toInt_lt] at h2 h4
      have hkey : cellKeyOf cx cy = enumKey (cx.toInt, cy.toInt) := cellKeyOf_enumKey cx cy
      refine ((FoldsAs.single (cx.toInt, cy.toInt)).seq hrest ?_).congr ?_ ?_
      · rintro c rfl ⟨_, _, hidx⟩
        rw [hcx, hcy] at hidx
        simp at hidx
        omega
      · intro c
        rw [hcell c]
        constructor
        · rintro (rfl | h)
          · exact Or.inl ⟨rfl, ⟨h1, h2, h3, h4⟩, by rw [← hleaf]; exact hlc⟩
          · exact Or.inr h
        · rintro (⟨rfl, _, _⟩ | h)
          · exact Or.inl rfl
          · exact Or.inr h
      · intro _ f acc
        show foldLeafCellsLoop leaf x0 y0 l t r b f i acc = _
        rw [hstep, ite_eq_left hc, hkey]
    · refine hrest.congr (fun c => ?_) fun _ f acc => by
        show foldLeafCellsLoop leaf x0 y0 l t r b f i acc = _
        rw [hstep, ite_eq_right hc]
      rw [hcell c]
      constructor
      · exact Or.inr
      · rintro (⟨rfl, ⟨h1, h2, h3, h4⟩, hl⟩ | h)
        · exfalso
          apply hc
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          rw [Int64.le_iff_toInt_le, Int64.le_iff_toInt_le, Int64.lt_iff_toInt_lt, Int64.lt_iff_toInt_lt, hleaf]
          exact ⟨⟨⟨⟨hl, h1⟩, h2⟩, h3⟩, h4⟩
        · exact h

theorem foldLeafCells_spec (leaf : UInt64) {x0 y0 l t r b : Int64}
    (hx : -2 ^ 62 ≤ x0.toInt ∧ x0.toInt ≤ 2 ^ 62) (hy : -2 ^ 62 ≤ y0.toInt ∧ y0.toInt ≤ 2 ^ 62) :
    FoldsAs (fun f acc => foldLeafCellsLoop leaf x0 y0 l t r b f 0 acc)
      (fun c => InWindow l.toInt t.toInt r.toInt b.toInt c ∧ leafAt leaf (c.1 - x0.toInt) (c.2 - y0.toInt) = true) :=
  (foldLeafCellsLoop_spec leaf hx hy 64 0 rfl (by decide)).congr (fun c => by
    unfold LeafP
    constructor
    · exact fun ⟨h1, h2, _⟩ => ⟨h1, h2⟩
    · intro ⟨h1, h2⟩
      have := leafAt_bounds h2
      exact ⟨h1, h2, by simp; omega⟩) fun _ _ _ => rfl

theorem i64_add_small {x : Int64} {k : ℤ} (y : Int64) (hy : y.toInt = k) (h1 : -2 ^ 62 ≤ x.toInt)
    (h2 : x.toInt ≤ 2 ^ 62) (hk : 0 ≤ k ∧ k < 2 ^ 62) : (x + y).toInt = x.toInt + k := by
  rw [i64_add_toInt (by omega) (by omega), hy]

theorem i64_lit8 : (8 : Int64).toInt = 8 := by decide
theorem i64_lit16 : (16 : Int64).toInt = 16 := by decide

theorem foldLevel4Cells_spec {a : FlatHashLifeArena} (hwf : ArenaWF a) {id : UInt32} {M : MacroCell}
    (hn : NodeIs a 0 id M) {x0 y0 l t r b : Int64}
    (hx : -2 ^ 62 ≤ x0.toInt ∧ x0.toInt + 16 ≤ 2 ^ 62) (hy : -2 ^ 62 ≤ y0.toInt ∧ y0.toInt + 16 ≤ 2 ^ 62) :
    FoldsAs (fun f acc => a.foldLevel4Cells id x0 y0 l t r b f acc)
      (fun c => InWindow l.toInt t.toInt r.toInt b.toInt c ∧ cellAt M (c.1 - x0.toInt) (c.2 - y0.toInt) = true) := by
  have hW := hn.WFd
  have hx16 := i64_add_small (x := x0) 16 i64_lit16 hx.1 (by omega) (by decide)
  have hy16 := i64_add_small (x := y0) 16 i64_lit16 hy.1 (by omega) (by decide)
  by_cases hc : (id == 0 || id >= a.l4Count || r <= x0 || b <= y0 || x0 + 16 <= l || y0 + 16 <= t) = true
  · have hnone : ∀ c, ¬ (InWindow l.toInt t.toInt r.toInt b.toInt c ∧
        cellAt M (c.1 - x0.toInt) (c.2 - y0.toInt) = true) := by
      rintro c ⟨hwc, hcell⟩
      have hc' := hc
      simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hc'
      have hb := cellAt_bounds hW (by decide) hcell
      have e16 : (2 : ℤ) ^ (0 + 4) = 16 := by decide
      rw [e16] at hb
      obtain ⟨hwl, hwr, hwt, hwb⟩ := hwc
      rcases hc' with ((((h0 | h0) | h0) | h0) | h0) | h0
      · subst h0
        rw [← hn.2, (NodeIs.emptyL4 hwf).2, cellAt_emptyLevel4] at hcell
        cases hcell
      · exact absurd hn.1 (by rw [ge_iff_le] at h0; exact UInt32.not_lt.mpr h0)
      · rw [Int64.le_iff_toInt_le] at h0; omega
      · rw [Int64.le_iff_toInt_le] at h0; omega
      · rw [Int64.le_iff_toInt_le, hx16] at h0; omega
      · rw [Int64.le_iff_toInt_le, hy16] at h0; omega
    refine (FoldsAs.refl hnone).congr (fun _ => Iff.rfl) fun _ f acc => ?_
    show a.foldLevel4Cells id x0 y0 l t r b f acc = acc
    unfold FlatHashLifeArena.foldLevel4Cells
    rw [ite_eq_left hc]
  · have hM : M = makeLevel4Node a.l4Nw[id.toNat]! a.l4Ne[id.toNat]! a.l4Sw[id.toNat]! a.l4Se[id.toNat]! := by
      rw [← hn.2]
      unfold denoteLevel4
      rw [ite_eq_left hn.1]
    have hx8 := i64_add_small (x := x0) 8 i64_lit8 hx.1 (by omega) (by decide)
    have hy8 := i64_add_small (x := y0) 8 i64_lit8 hy.1 (by omega) (by decide)
    have hxb : -2 ^ 62 ≤ x0.toInt ∧ x0.toInt ≤ 2 ^ 62 := ⟨hx.1, by omega⟩
    have hyb : -2 ^ 62 ≤ y0.toInt ∧ y0.toInt ≤ 2 ^ 62 := ⟨hy.1, by omega⟩
    have hxb8 : -2 ^ 62 ≤ (x0 + 8).toInt ∧ (x0 + 8).toInt ≤ 2 ^ 62 := by rw [hx8]; omega
    have hyb8 : -2 ^ 62 ≤ (y0 + 8).toInt ∧ (y0 + 8).toInt ≤ 2 ^ 62 := by rw [hy8]; omega
    have q := FoldsAs.quad x0.toInt y0.toInt 8
      (foldLeafCells_spec a.l4Nw[id.toNat]! (l := l) (t := t) (r := r) (b := b) hxb hyb)
      (foldLeafCells_spec a.l4Ne[id.toNat]! (l := l) (t := t) (r := r) (b := b) hxb8 hyb)
      (foldLeafCells_spec a.l4Sw[id.toNat]! (l := l) (t := t) (r := r) (b := b) hxb hyb8)
      (foldLeafCells_spec a.l4Se[id.toNat]! (l := l) (t := t) (r := r) (b := b) hxb8 hyb8)
      (fun c ⟨_, h⟩ => by have := leafAt_bounds h; omega)
      (fun c ⟨_, h⟩ => by have := leafAt_bounds h; rw [hx8] at this; omega)
      (fun c ⟨_, h⟩ => by have := leafAt_bounds h; rw [hy8] at this; omega)
      (fun c ⟨_, h⟩ => by have := leafAt_bounds h; rw [hx8, hy8] at this; omega)
    refine q.congr (fun c => ?_) fun _ f acc => ?_
    · rw [hM, cellAt_makeLevel4Node, quadSel_eq_true_iff (leafAt_supp _) (leafAt_supp _) (leafAt_supp _)
        (leafAt_supp _), hx8, hy8]
      have e1 : c.1 - (x0.toInt + 8) = c.1 - x0.toInt - 8 := by omega
      have e2 : c.2 - (y0.toInt + 8) = c.2 - y0.toInt - 8 := by omega
      rw [e1, e2]
      simp only [and_or_left]
    · show a.foldLevel4Cells id x0 y0 l t r b f acc = _
      unfold FlatHashLifeArena.foldLevel4Cells
      rw [ite_eq_right hc]

theorem foldCellsLoop_spec {a : FlatHashLifeArena} (hwf : ArenaWF a) {l t r b : Int64} :
    ∀ (h : ℕ) {id : UInt32} {m : MacroCell}, NodeIs a (h + 1) id m → h + 5 ≤ 62 →
      ∀ (x0 y0 : Int64) (fuel : UInt32), h + 1 ≤ fuel.toNat →
      -2 ^ 62 ≤ x0.toInt → x0.toInt + 2 ^ (h + 5) ≤ 2 ^ 62 →
      -2 ^ 62 ≤ y0.toInt → y0.toInt + 2 ^ (h + 5) ≤ 2 ^ 62 →
      FoldsAs (fun f acc => a.foldCellsLoop id x0 y0 l t r b f acc fuel)
        (fun c => InWindow l.toInt t.toInt r.toInt b.toInt c ∧ cellAt m (c.1 - x0.toInt) (c.2 - y0.toInt) = true)
  | h, id, m, hn, h62, x0, y0, fuel, hf, hx1, hx2, hy1, hy2 => by
    have hf0 : fuel ≠ 0 := fun h0 => by subst h0; simp at hf
    have hW := hn.WFd
    have hpos5 := pow_two_pos' (h + 5)
    have hpos4 := pow_two_pos' (h + 4)
    have h2pow : (2 : ℤ) ^ (h + 5) = 2 * 2 ^ (h + 4) := by
      rw [show h + 5 = h + 4 + 1 from rfl, Int.pow_succ]
      omega
    obtain ⟨c1, c2, c3, c4, hM⟩ := hn.children hwf
    have hL : (a.cellLevel[id.toNat]!).toUInt32.toNat = h + 5 := by
      rw [u8_toUInt32_toNat]
      exact hn.level
    have hlt : ¬ (id ≥ a.cellCount) := by rw [ge_iff_le, u32_le_iff]; have := u32_lt_iff.mp hn.lt_cell; omega
    have hnone : ∀ c : Coord, cellAt m (c.1 - x0.toInt) (c.2 - y0.toInt) = true →
        x0.toInt ≤ c.1 ∧ c.1 < x0.toInt + 2 ^ (h + 5) ∧ y0.toInt ≤ c.2 ∧ c.2 < y0.toInt + 2 ^ (h + 5) := by
      intro c hc
      have := cellAt_bounds hW (by omega) hc
      rw [show h + 1 + 4 = h + 5 by omega] at this
      omega
    by_cases hA : ((a.cellLevel[id.toNat]!).toUInt32 > 62 ||
        ((a.cellLevel[id.toNat]!).toUInt32 <= 31 && a.cellPop[id.toNat]! == 0)) = true
    · have hnone' : ∀ c, ¬ (InWindow l.toInt t.toInt r.toInt b.toInt c ∧
          cellAt m (c.1 - x0.toInt) (c.2 - y0.toInt) = true) := by
        rintro c ⟨_, hcell⟩
        have hc := hA
        simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at hc
        rcases hc with hc | ⟨hc31, hp⟩
        · rw [gt_iff_lt, u32_lt_iff, hL] at hc
          simp at hc
          omega
        · rw [u32_le_iff, hL] at hc31
          simp at hc31
          have hpop := hwf.cellPop id hn.lt_cell
          rw [hp, hn.denoteCell_eq] at hpop
          have hs := size_toNat_of_WFd hW (by omega)
          rw [← hpop] at hs
          have := cellAt_pos hcell
          simp at hs
          omega
      refine (FoldsAs.refl hnone').congr (fun _ => Iff.rfl) fun _ f acc => ?_
      show a.foldCellsLoop id x0 y0 l t r b f acc fuel = acc
      rw [FlatHashLifeArena.foldCellsLoop, dite_eq_right hf0, ite_eq_right hlt]
      dsimp only
      rw [ite_eq_left hA]
    · have hspan : (pow2Int64 (a.cellLevel[id.toNat]!).toUInt32).toInt = 2 ^ (h + 5) := by
        rw [pow2Int64_toInt (by omega), hL]
      have hxs : (x0 + pow2Int64 (a.cellLevel[id.toNat]!).toUInt32).toInt = x0.toInt + 2 ^ (h + 5) := by
        rw [i64_add_toInt (by rw [hspan]; omega) (by rw [hspan]; omega), hspan]
      have hys : (y0 + pow2Int64 (a.cellLevel[id.toNat]!).toUInt32).toInt = y0.toInt + 2 ^ (h + 5) := by
        rw [i64_add_toInt (by rw [hspan]; omega) (by rw [hspan]; omega), hspan]
      by_cases hB : (r <= x0 || b <= y0 || x0 + pow2Int64 (a.cellLevel[id.toNat]!).toUInt32 <= l ||
          y0 + pow2Int64 (a.cellLevel[id.toNat]!).toUInt32 <= t) = true
      · have hnone' : ∀ c, ¬ (InWindow l.toInt t.toInt r.toInt b.toInt c ∧
            cellAt m (c.1 - x0.toInt) (c.2 - y0.toInt) = true) := by
          rintro c ⟨⟨hwl, hwr, hwt, hwb⟩, hcell⟩
          have := hnone c hcell
          have hc := hB
          simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
          rw [Int64.le_iff_toInt_le, Int64.le_iff_toInt_le, Int64.le_iff_toInt_le, Int64.le_iff_toInt_le, hxs,
            hys] at hc
          omega
        refine (FoldsAs.refl hnone').congr (fun _ => Iff.rfl) fun _ f acc => ?_
        show a.foldCellsLoop id x0 y0 l t r b f acc fuel = acc
        rw [FlatHashLifeArena.foldCellsLoop, dite_eq_right hf0, ite_eq_right hlt]
        dsimp only
        rw [ite_eq_right hA, ite_eq_left hB]
      · have hL1 : ((a.cellLevel[id.toNat]!).toUInt32 - 1).toNat = h + 4 := by
          rw [UInt32.toNat_sub_of_le _ _ (by rw [u32_le_iff, hL]; show 1 ≤ h + 5; omega), hL]
          show h + 5 - 1 = h + 4
          omega
        have hhalf : (pow2Int64 ((a.cellLevel[id.toNat]!).toUInt32 - 1)).toInt = 2 ^ (h + 4) := by
          rw [pow2Int64_toInt (by omega), hL1]
        have hxh : (x0 + pow2Int64 ((a.cellLevel[id.toNat]!).toUInt32 - 1)).toInt = x0.toInt + 2 ^ (h + 4) := by
          rw [i64_add_toInt (by rw [hhalf]; omega) (by rw [hhalf]; omega), hhalf]
        have hyh : (y0 + pow2Int64 ((a.cellLevel[id.toNat]!).toUInt32 - 1)).toInt = y0.toInt + 2 ^ (h + 4) := by
          rw [i64_add_toInt (by rw [hhalf]; omega) (by rw [hhalf]; omega), hhalf]
        generalize hhv : pow2Int64 ((a.cellLevel[id.toNat]!).toUInt32 - 1) = half at hxh hyh
        have hw4 : (denoteAt h a a.cellNw[id.toNat]!).level.toNat = h + 4 :=
          WFd_level_toNat c1.WFd (by omega)
        have hsup : ∀ (c : UInt32), NodeIs a h c (denoteAt h a c) →
            Supp (cellAt (denoteAt h a c)) (2 ^ (h + 4)) :=
          fun c hc => cellAt_supp hc.WFd (by omega)
        have target : ∀ c : Coord,
            ((InWindow l.toInt t.toInt r.toInt b.toInt c ∧
                cellAt (denoteAt h a a.cellNw[id.toNat]!) (c.1 - x0.toInt) (c.2 - y0.toInt) = true) ∨
              (InWindow l.toInt t.toInt r.toInt b.toInt c ∧
                cellAt (denoteAt h a a.cellNe[id.toNat]!) (c.1 - (x0 + half).toInt) (c.2 - y0.toInt) = true) ∨
              (InWindow l.toInt t.toInt r.toInt b.toInt c ∧
                cellAt (denoteAt h a a.cellSw[id.toNat]!) (c.1 - x0.toInt) (c.2 - (y0 + half).toInt) = true) ∨
              (InWindow l.toInt t.toInt r.toInt b.toInt c ∧
                cellAt (denoteAt h a a.cellSe[id.toNat]!) (c.1 - (x0 + half).toInt)
                  (c.2 - (y0 + half).toInt) = true)) ↔
            (InWindow l.toInt t.toInt r.toInt b.toInt c ∧ cellAt m (c.1 - x0.toInt) (c.2 - y0.toInt) = true) := by
          intro c
          rw [hM, cellAt_makeCellNode, hw4, quadSel_eq_true_iff (hsup _ c1) (hsup _ c2) (hsup _ c3) (hsup _ c4),
            hxh, hyh]
          have e1 : c.1 - (x0.toInt + 2 ^ (h + 4)) = c.1 - x0.toInt - 2 ^ (h + 4) := by omega
          have e2 : c.2 - (y0.toInt + 2 ^ (h + 4)) = c.2 - y0.toInt - 2 ^ (h + 4) := by omega
          rw [e1, e2]
          simp only [and_or_left]
        have reg : ∀ (c : UInt32), NodeIs a h c (denoteAt h a c) → ∀ (X Y : ℤ) (p : Coord),
            cellAt (denoteAt h a c) (p.1 - X) (p.2 - Y) = true →
            X ≤ p.1 ∧ p.1 < X + 2 ^ (h + 4) ∧ Y ≤ p.2 ∧ p.2 < Y + 2 ^ (h + 4) := by
          intro c hc X Y p hp
          have := hsup c hc _ _ hp
          omega
        by_cases h5 : (a.cellLevel[id.toNat]!).toUInt32 <= 5
        · -- level 5: Level 4 children
          have hh0 : h = 0 := by
            rw [u32_le_iff, hL] at h5
            simp at h5
            omega
          subst hh0
          have e16 : (2 : ℤ) ^ (0 + 4) = 16 := by decide
          rw [e16] at hxh hyh reg
          have hb : ∀ X : Int64, -2 ^ 62 ≤ X.toInt → X.toInt + 16 ≤ 2 ^ 62 →
              -2 ^ 62 ≤ X.toInt ∧ X.toInt + 16 ≤ 2 ^ 62 := fun _ h1 h2 => ⟨h1, h2⟩
          have e32 : (2 : ℤ) ^ (0 + 5) = 32 := by decide
          rw [e32] at hx2 hy2
          refine (FoldsAs.quad x0.toInt y0.toInt 16
            (foldLevel4Cells_spec hwf c1 (l := l) (t := t) (r := r) (b := b) (hb _ hx1 (by omega)) (hb _ hy1 (by omega)))
            (foldLevel4Cells_spec hwf c2 (l := l) (t := t) (r := r) (b := b) (hb _ (by rw [hxh]; omega) (by rw [hxh]; omega)) (hb _ hy1 (by omega)))
            (foldLevel4Cells_spec hwf c3 (l := l) (t := t) (r := r) (b := b) (hb _ hx1 (by omega)) (hb _ (by rw [hyh]; omega) (by rw [hyh]; omega)))
            (foldLevel4Cells_spec hwf c4 (l := l) (t := t) (r := r) (b := b) (hb _ (by rw [hxh]; omega) (by rw [hxh]; omega))
              (hb _ (by rw [hyh]; omega) (by rw [hyh]; omega)))
            (fun p ⟨_, hp⟩ => by have := reg _ c1 _ _ p hp; omega)
            (fun p ⟨_, hp⟩ => by have := reg _ c2 _ _ p hp; rw [hxh] at this; omega)
            (fun p ⟨_, hp⟩ => by have := reg _ c3 _ _ p hp; rw [hyh] at this; omega)
            (fun p ⟨_, hp⟩ => by have := reg _ c4 _ _ p hp; rw [hxh, hyh] at this; omega)).congr
            target fun _ f acc => ?_
          show a.foldCellsLoop id x0 y0 l t r b f acc fuel = _
          rw [FlatHashLifeArena.foldCellsLoop, dite_eq_right hf0, ite_eq_right hlt]
          dsimp only
          rw [ite_eq_right hA, ite_eq_right hB, ite_eq_left h5, hhv]
        · obtain ⟨j, rfl⟩ : ∃ j, h = j + 1 := by
            rw [u32_le_iff, hL] at h5
            simp at h5
            exact ⟨h - 1, by omega⟩
          have hf1 : (fuel - 1).toNat = fuel.toNat - 1 := u32_toNat_sub (by simp; omega)
          have hrec := fun (c : UInt32) (hc : NodeIs a (j + 1) c (denoteAt (j + 1) a c)) (X Y : Int64)
              (h1 : -2 ^ 62 ≤ X.toInt) (h2 : X.toInt + 2 ^ (j + 1 + 4) ≤ 2 ^ 62)
              (h3 : -2 ^ 62 ≤ Y.toInt) (h4 : Y.toInt + 2 ^ (j + 1 + 4) ≤ 2 ^ 62) =>
            foldCellsLoop_spec hwf (l := l) (t := t) (r := r) (b := b) j hc (by omega) X Y (fuel - 1) (by omega) h1
              (by rw [show j + 5 = j + 1 + 4 by omega]; exact h2) h3
              (by rw [show j + 5 = j + 1 + 4 by omega]; exact h4)
          refine (FoldsAs.quad x0.toInt y0.toInt (2 ^ (j + 1 + 4))
            (hrec _ c1 x0 y0 hx1 (by omega) hy1 (by omega))
            (hrec _ c2 _ y0 (by rw [hxh]; omega) (by rw [hxh]; omega) hy1 (by omega))
            (hrec _ c3 x0 _ hx1 (by omega) (by rw [hyh]; omega) (by rw [hyh]; omega))
            (hrec _ c4 _ _ (by rw [hxh]; omega) (by rw [hxh]; omega) (by rw [hyh]; omega) (by rw [hyh]; omega))
            (fun p ⟨_, hp⟩ => by have := reg _ c1 _ _ p hp; omega)
            (fun p ⟨_, hp⟩ => by have := reg _ c2 _ _ p hp; rw [hxh] at this; omega)
            (fun p ⟨_, hp⟩ => by have := reg _ c3 _ _ p hp; rw [hyh] at this; omega)
            (fun p ⟨_, hp⟩ => by have := reg _ c4 _ _ p hp; rw [hxh, hyh] at this; omega)).congr
            target fun _ f acc => ?_
          show a.foldCellsLoop id x0 y0 l t r b f acc fuel = _
          rw [FlatHashLifeArena.foldCellsLoop, dite_eq_right hf0, ite_eq_right hlt]
          dsimp only
          rw [ite_eq_right hA, ite_eq_right hB, ite_eq_right h5, hhv]

/-- The enumeration of a root folds over the live cells of its state in the window, for any window. -/
theorem foldCellsLoop_root_enum {a : FlatHashLifeArena} (hwf : ArenaWF a) {root : UInt32} (hid : root < a.cellCount)
    (hlv : cellLevelOf a root ≤ 61) (ox oy : Int32) (l t r b : Int64) :
    ∃ L : List Coord, L.Nodup ∧
      (∀ c, c ∈ L ↔ c ∈ hashLifeToGrid (flatState a ox oy root) ∧ InWindow l.toInt t.toInt r.toInt b.toInt c) ∧
      ∀ (α : Type) (f : α → UInt64 → α) (acc : α),
        a.foldCellsLoop root ox.toInt64 oy.toInt64 l t r b f acc 64 = L.foldl (fun a c => f a (enumKey c)) acc := by
  obtain ⟨k, hk, hn⟩ := NodeIs.of_lt' hwf hid
  have hW := hn.WFd
  have hp := pow_two_le_pow (show k + 5 ≤ 61 by omega)
  have h61 : (2 : ℤ) ^ 61 = 2305843009213693952 := by decide
  have hx1 := Int32.le_toInt ox
  have hx2 := Int32.toInt_lt ox
  have hy1 := Int32.le_toInt oy
  have hy2 := Int32.toInt_lt oy
  have hp31 : (2 : ℤ) ^ 31 = 2147483648 := by decide
  have hp62 : (2 : ℤ) ^ 62 = 4611686018427387904 := by decide
  obtain ⟨L, hnd, hmem, heq⟩ := foldCellsLoop_spec hwf (l := l) (t := t) (r := r) (b := b) k hn (by omega)
    ox.toInt64 oy.toInt64 64 (by simp; omega) (by rw [Int32.toInt_toInt64]; omega)
    (by rw [Int32.toInt_toInt64]; omega) (by rw [Int32.toInt_toInt64]; omega) (by rw [Int32.toInt_toInt64]; omega)
  refine ⟨L, hnd, fun c => ?_, heq⟩
  rw [hmem c]
  unfold hashLifeToGrid flatState
  dsimp only
  rw [hn.denoteCell_eq, mem_macroCellToGrid_iff hW (by omega), Int32.toInt_toInt64, Int32.toInt_toInt64]
  exact and_comm

theorem enumKey_eq_coordKey {c : Coord} (h : InWindow (-2 ^ 31) (-2 ^ 31) (2 ^ 31) (2 ^ 31) c) :
    enumKey c = coordKey c := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hs : Int64.size = 18446744073709551616 := rfl
  have e1 : (Int64.ofInt c.1).toInt = c.1 := by
    rw [Int64.toInt_ofInt, Int.bmod_eq_of_le] <;> rw [hs] <;> omega
  have e2 : (Int64.ofInt c.2).toInt = c.2 := by
    rw [Int64.toInt_ofInt, Int.bmod_eq_of_le] <;> rw [hs] <;> omega
  unfold enumKey
  rw [cellKeyOf_eq (by rw [e1]; omega) (by rw [e1]; omega) (by rw [e2]; omega) (by rw [e2]; omega), e1, e2]

theorem foldl_key_congr {α : Type} (f : α → UInt64 → α) {g g' : Coord → UInt64} :
    ∀ (L : List Coord) (acc : α), (∀ c ∈ L, g c = g' c) →
      L.foldl (fun a c => f a (g c)) acc = L.foldl (fun a c => f a (g' c)) acc
  | [], _, _ => rfl
  | c :: L, acc, h => by
    rw [List.foldl_cons, List.foldl_cons, h c (by simp)]
    exact foldl_key_congr f L _ fun c' hc' => h c' (by simp [hc'])

theorem foldCellsLoop_root {a : FlatHashLifeArena} (hwf : ArenaWF a) {root : UInt32} (hid : root < a.cellCount)
    (hlv : cellLevelOf a root ≤ 61) (ox oy : Int32) {l t r b : Int64} (hw : EnumBounds l t r b) :
    ∃ L : List Coord, L.Nodup ∧
      (∀ c, c ∈ L ↔ c ∈ hashLifeToGrid (flatState a ox oy root) ∧ InWindow l.toInt t.toInt r.toInt b.toInt c) ∧
      ∀ (α : Type) (f : α → UInt64 → α) (acc : α),
        a.foldCellsLoop root ox.toInt64 oy.toInt64 l t r b f acc 64 = L.foldl (fun a c => f a (coordKey c)) acc := by
  obtain ⟨L, hnd, hmem, heq⟩ := foldCellsLoop_root_enum hwf hid hlv ox oy l t r b
  refine ⟨L, hnd, hmem, fun α f acc => ?_⟩
  rw [heq]
  apply foldl_key_congr
  intro c hc
  obtain ⟨_, h1, h2, h3, h4⟩ := (hmem c).mp hc
  have := hw.l; have := hw.t; have := hw.r; have := hw.b
  exact enumKey_eq_coordKey ⟨by omega, by omega, by omega, by omega⟩

-- =========================================================================
-- The quadtree of a list of cells
-- =========================================================================

theorem u32_succ_toNat {i limit : UInt32} (h : i < limit) : (i + 1).toNat = i.toNat + 1 := by
  have h1 := UInt32.lt_iff_toNat_lt.mp h
  have := UInt32.toNat_lt limit
  rw [UInt32.toNat_add]
  simp only [UInt32.toNat_one]
  omega

/-- The decoded key coordinates. -/
def keyX (k : UInt64) : ℕ := (keyHi k).toNat
def keyY (k : UInt64) : ℕ := (keyLo k).toNat

theorem keyX_toNat (k : UInt64) : keyX k = k.toNat / 2 ^ 32 := by
  unfold keyX keyHi
  rw [UInt64.toNat_shiftRight]
  have : (32 : UInt64).toNat % 64 = 32 := rfl
  rw [this, Nat.shiftRight_eq_div_pow]

theorem keyY_toNat (k : UInt64) : keyY k = k.toNat % 2 ^ 32 := by
  unfold keyY keyLo
  rw [UInt64.toNat_and]
  have : (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

theorem keyX_lt (k : UInt64) : keyX k < 2 ^ 32 := by
  rw [keyX_toNat]; have := k.toNat_lt; omega

theorem keyY_lt (k : UInt64) : keyY k < 2 ^ 32 := by
  rw [keyY_toNat]; omega

theorem keyCoord_eq (k : UInt64) : keyCoord k = ((keyX k : ℤ) - 2 ^ 31, (keyY k : ℤ) - 2 ^ 31) := by
  unfold keyCoord
  rw [keyX_toNat, keyY_toNat]

/-- The key relative to the corner `(minX, minY)`, in key coordinates. -/
theorem relKey_decode {k minX minY : UInt64} (hx : minX.toNat ≤ keyX k) (hy : minY.toNat ≤ keyY k) :
    keyX (((keyHi k - minX) <<< 32) + (keyLo k - minY)) = keyX k - minX.toNat ∧
    keyY (((keyHi k - minX) <<< 32) + (keyLo k - minY)) = keyY k - minY.toNat := by
  have hX := keyX_lt k
  have hY := keyY_lt k
  have e1 : (keyHi k - minX).toNat = keyX k - minX.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; exact hx)]
    rfl
  have e2 : (keyLo k - minY).toNat = keyY k - minY.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; exact hy)]
    rfl
  have hk : (((keyHi k - minX) <<< 32) + (keyLo k - minY)).toNat =
      (keyX k - minX.toNat) * 2 ^ 32 + (keyY k - minY.toNat) := by
    rw [UInt64.toNat_add, UInt64.toNat_shiftLeft, e1, e2]
    have : (32 : UInt64).toNat % 64 = 32 := rfl
    rw [this, Nat.shiftLeft_eq]
    have : (keyX k - minX.toNat) * 2 ^ 32 < 2 ^ 64 := by
      have : keyX k - minX.toNat < 2 ^ 32 := by omega
      calc (keyX k - minX.toNat) * 2 ^ 32 < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul_of_pos_right this (by decide)
        _ = 2 ^ 64 := by decide
    rw [Nat.mod_eq_of_lt this]
    omega
  rw [keyX_toNat, keyY_toNat, hk]
  omega

/-- Key `k` is the cell `(x, y)` of the 8x8 leaf with corner `(x0, y0)`. -/
def KeyInLeaf (x0 y0 : ℕ) (k : UInt64) (x y : ℤ) : Prop :=
  x0 ≤ keyX k ∧ keyX k < x0 + 8 ∧ y0 ≤ keyY k ∧ keyY k < y0 + 8 ∧ (keyX k : ℤ) = x0 + x ∧ (keyY k : ℤ) = y0 + y

theorem cellAt_emptyNode_false (k : ℕ) (x y : ℤ) : cellAt (emptyNode k) x y = false := by
  cases h : cellAt (emptyNode k) x y
  · rfl
  · have := cellAt_pos h
    rw [macroCellSize_emptyNode_Impl] at this
    omega

/-- The keys all lie in the node of height `H` whose corner is at key coordinates `(x0, y0)`. -/
def KeysIn (keys : List UInt64) (x0 y0 : ℕ) (H : ℕ) : Prop :=
  ∀ k ∈ keys, x0 ≤ keyX k ∧ keyX k < x0 + 2 ^ (H + 4) ∧ y0 ≤ keyY k ∧ keyY k < y0 + 2 ^ (H + 4)

/-- The cell function whose live cells are exactly the keys, relative to the corner `(x0, y0)`. -/
def KeysCells (keys : List UInt64) (x0 y0 : ℕ) (x y : ℤ) : Prop :=
  ∃ k ∈ keys, (keyX k : ℤ) = x0 + x ∧ (keyY k : ℤ) = y0 + y

/-- The quadrant test of `filterKeysLoop`. -/
def InQuadrant (midX midY : ℕ) (east south : Bool) (k : UInt64) : Prop :=
  (decide (midX ≤ keyX k) = east) ∧ (decide (midY ≤ keyY k) = south)

/--
The keys of `keys` (prepended to `acc`) in the quadrant selected by `east` and `south` of a node split at `(midX, midY)`.
-/
def filterKeys (keys : List UInt64) (midX midY : UInt64) (east south : Bool) (acc : List UInt64) : List UInt64 :=
  match keys with
  | [] => acc
  | k :: rest =>
    filterKeys rest midX midY east south
      (if decide (keyHi k ≥ midX) == east && decide (keyLo k ≥ midY) == south then k :: acc else acc)

theorem splitKeys_eq (midX midY : UInt64) : ∀ (keys nw ne sw se : List UInt64),
    splitKeys keys midX midY nw ne sw se =
      (filterKeys keys midX midY false false nw, filterKeys keys midX midY true false ne,
        filterKeys keys midX midY false true sw, filterKeys keys midX midY true true se)
  | [], _, _, _, _ => rfl
  | k :: rest, nw, ne, sw, se => by
    rw [splitKeys]
    by_cases hy : keyLo k ≥ midY <;> by_cases hx : keyHi k ≥ midX <;>
      simp only [hy, hx, ↓reduceIte, splitKeys_eq midX midY rest, filterKeys, decide_true, decide_false,
        beq_self_eq_true, Bool.and_self, Bool.and_true, Bool.true_and, beq_iff_eq, Bool.true_eq_false, Bool.false_eq_true, ↓reduceIte] <;> simp

theorem nwChild_emptyAtHeight {h : UInt32} (h0 : h ≠ 0) : nwChild (emptyAtHeight h) = emptyAtHeight (h - 1) := by
  rw [emptyAtHeight, dite_eq_right h0]
  rfl

theorem filterKeys_mem (midX midY : UInt64) (east south : Bool) :
    ∀ (keys acc : List UInt64) (k : UInt64), k ∈ filterKeys keys midX midY east south acc ↔
      k ∈ acc ∨ (k ∈ keys ∧ InQuadrant midX.toNat midY.toNat east south k)
  | [], acc, k => by simp [filterKeys]
  | k' :: rest, acc, k => by
    rw [filterKeys, filterKeys_mem midX midY east south rest]
    have hq : (decide (keyHi k' ≥ midX) == east && decide (keyLo k' ≥ midY) == south) = true ↔
        InQuadrant midX.toNat midY.toNat east south k' := by
      unfold InQuadrant keyX keyY
      simp only [Bool.and_eq_true, beq_iff_eq]
      rw [decide_eq_decide.mpr (show keyHi k' ≥ midX ↔ midX.toNat ≤ (keyHi k').toNat from UInt64.le_iff_toNat_le),
        decide_eq_decide.mpr (show keyLo k' ≥ midY ↔ midY.toNat ≤ (keyLo k').toNat from UInt64.le_iff_toNat_le)]
    split
    · rename_i hc
      simp only [List.mem_cons]
      constructor
      · rintro ((rfl | h) | ⟨h1, h2⟩)
        · exact Or.inr ⟨Or.inl rfl, hq.mp hc⟩
        · exact Or.inl h
        · exact Or.inr ⟨Or.inr h1, h2⟩
      · rintro (h | ⟨rfl | h1, h2⟩)
        · exact Or.inl (Or.inr h)
        · exact Or.inl (Or.inl rfl)
        · exact Or.inr ⟨h1, h2⟩
    · rename_i hc
      simp only [List.mem_cons]
      constructor
      · rintro (h | ⟨h1, h2⟩)
        · exact Or.inl h
        · exact Or.inr ⟨Or.inr h1, h2⟩
      · rintro (h | ⟨rfl | h1, h2⟩)
        · exact Or.inl h
        · exact absurd (hq.mpr h2) hc
        · exact Or.inr ⟨h1, h2⟩

theorem leafFromKeys_spec {x0 y0 : UInt64} (hx : x0.toNat + 8 < 2 ^ 64) (hy : y0.toNat + 8 < 2 ^ 64) :
    ∀ (keys : List UInt64) (leaf : UInt64) (x y : ℤ),
      leafAt (leafFromKeys keys x0 y0 leaf) x y = true ↔ leafAt leaf x y = true ∨
        ∃ k ∈ keys, KeyInLeaf x0.toNat y0.toNat k x y
  | [], leaf, x, y => by simp [leafFromKeys]
  | k :: rest, leaf, x, y => by
    rw [leafFromKeys]
    rw [leafFromKeys_spec hx hy rest]
    have hx8 : (x0 + 8).toNat = x0.toNat + 8 := by rw [UInt64.toNat_add]; simp; omega
    have hy8 : (y0 + 8).toNat = y0.toNat + 8 := by rw [UInt64.toNat_add]; simp; omega
    have hcond : (x0 ≤ keyHi k && keyHi k < x0 + 8 && y0 ≤ keyLo k && keyLo k < y0 + 8) = true ↔
        x0.toNat ≤ keyX k ∧ keyX k < x0.toNat + 8 ∧ y0.toNat ≤ keyY k ∧ keyY k < y0.toNat + 8 := by
      unfold keyX keyY
      simp only [Bool.and_eq_true, decide_eq_true_eq, UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, hx8, hy8]
      omega
    split
    · rename_i hc
      obtain ⟨c1, c2, c3, c4⟩ := hcond.mp hc
      have hxs : (keyHi k - x0).toUInt32.toNat = keyX k - x0.toNat := by
        rw [UInt64.toNat_toUInt32, UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; exact c1)]
        unfold keyX at c2 ⊢
        omega
      have hys : (keyLo k - y0).toUInt32.toNat = keyY k - y0.toNat := by
        rw [UInt64.toNat_toUInt32, UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; exact c3)]
        unfold keyY at c4 ⊢
        omega
      rw [leafAt_leafWithCell _ _ _ (by omega) (by omega), hxs, hys]
      simp only [List.mem_cons]
      constructor
      · rintro (h | ⟨k', hk', h3⟩)
        · split at h
          · exact Or.inr ⟨k, Or.inl rfl, ⟨c1, c2, c3, c4, by omega, by omega⟩⟩
          · exact Or.inl h
        · exact Or.inr ⟨k', Or.inr hk', h3⟩
      · rintro (h | ⟨k', rfl | hk', h3⟩)
        · left
          split
          · rfl
          · exact h
        · obtain ⟨_, _, _, _, e1, e2⟩ := h3
          left
          rw [ite_eq_left ⟨by omega, by omega⟩]
        · exact Or.inr ⟨k', hk', h3⟩
    · rename_i hc
      simp only [List.mem_cons]
      constructor
      · rintro (h | ⟨k', hk', h3⟩)
        · exact Or.inl h
        · exact Or.inr ⟨k', Or.inr hk', h3⟩
      · rintro (h | ⟨k', rfl | hk', h3⟩)
        · exact Or.inl h
        · obtain ⟨c1, c2, c3, c4, _, _⟩ := h3
          exact absurd (hcond.mpr ⟨c1, c2, c3, c4⟩) hc
        · exact Or.inr ⟨k', hk', h3⟩

theorem leaf_cells (keys : List UInt64) {x0 y0 : UInt64} (hx : x0.toNat + 8 < 2 ^ 64) (hy : y0.toNat + 8 < 2 ^ 64)
    (x y : ℤ) :
    leafAt (leafFromKeys keys x0 y0 0) x y = true ↔ ∃ k ∈ keys, KeyInLeaf x0.toNat y0.toNat k x y := by
  rw [leafFromKeys_spec hx hy keys 0 x y, leafAt_zero]
  simp

theorem keysCells_leaves (K : List UInt64) (x0 y0 : ℕ) (hin : KeysIn K x0 y0 0) (x y : ℤ) :
    ((∃ k ∈ K, KeyInLeaf x0 y0 k x y) ∨ (∃ k ∈ K, KeyInLeaf (x0 + 8) y0 k (x - 8) y) ∨
      (∃ k ∈ K, KeyInLeaf x0 (y0 + 8) k x (y - 8)) ∨ (∃ k ∈ K, KeyInLeaf (x0 + 8) (y0 + 8) k (x - 8) (y - 8))) ↔
      KeysCells K x0 y0 x y := by
  unfold KeyInLeaf KeysCells
  constructor
  · rintro (⟨k, hk, h⟩ | ⟨k, hk, h⟩ | ⟨k, hk, h⟩ | ⟨k, hk, h⟩) <;> exact ⟨k, hk, by push_cast at h ⊢; omega⟩
  · rintro ⟨k, hk, h1, h2⟩
    have := hin k hk
    have e16 : 2 ^ (0 + 4) = 16 := rfl
    rw [e16] at this
    by_cases hx : keyX k < x0 + 8 <;> by_cases hy : keyY k < y0 + 8
    · exact Or.inl ⟨k, hk, by omega⟩
    · exact Or.inr (Or.inr (Or.inl ⟨k, hk, by push_cast; omega⟩))
    · exact Or.inr (Or.inl ⟨k, hk, by push_cast; omega⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨k, hk, by push_cast; omega⟩))

theorem keysCells_quad (K K1 K2 K3 K4 : List UInt64) (x0 y0 w : ℕ)
    (h1 : ∀ k, k ∈ K1 ↔ k ∈ K ∧ InQuadrant (x0 + w) (y0 + w) false false k)
    (h2 : ∀ k, k ∈ K2 ↔ k ∈ K ∧ InQuadrant (x0 + w) (y0 + w) true false k)
    (h3 : ∀ k, k ∈ K3 ↔ k ∈ K ∧ InQuadrant (x0 + w) (y0 + w) false true k)
    (h4 : ∀ k, k ∈ K4 ↔ k ∈ K ∧ InQuadrant (x0 + w) (y0 + w) true true k) (x y : ℤ) :
    (KeysCells K1 x0 y0 x y ∨ KeysCells K2 (x0 + w) y0 (x - w) y ∨ KeysCells K3 x0 (y0 + w) x (y - w) ∨
      KeysCells K4 (x0 + w) (y0 + w) (x - w) (y - w)) ↔ KeysCells K x0 y0 x y := by
  unfold KeysCells
  constructor
  · rintro (⟨k, hk, e⟩ | ⟨k, hk, e⟩ | ⟨k, hk, e⟩ | ⟨k, hk, e⟩)
    · exact ⟨k, ((h1 k).mp hk).1, by push_cast at e ⊢; omega⟩
    · exact ⟨k, ((h2 k).mp hk).1, by push_cast at e ⊢; omega⟩
    · exact ⟨k, ((h3 k).mp hk).1, by push_cast at e ⊢; omega⟩
    · exact ⟨k, ((h4 k).mp hk).1, by push_cast at e ⊢; omega⟩
  · rintro ⟨k, hk, e⟩
    unfold InQuadrant at h1 h2 h3 h4
    by_cases hx : x0 + w ≤ keyX k <;> by_cases hy : y0 + w ≤ keyY k
    · exact Or.inr (Or.inr (Or.inr ⟨k, (h4 k).mpr ⟨hk, by simp [hx], by simp [hy]⟩, by push_cast; omega⟩))
    · exact Or.inr (Or.inl ⟨k, (h2 k).mpr ⟨hk, by simp [hx], by simp [hy]⟩, by push_cast; omega⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨k, (h3 k).mpr ⟨hk, by simp [hx], by simp [hy]⟩, by push_cast; omega⟩))
    · exact Or.inl ⟨k, (h1 k).mpr ⟨hk, by simp [hx], by simp [hy]⟩, by omega⟩

theorem HashOK_emptyNode : ∀ k : ℕ, HashOK (emptyNode k)
  | 0 | 1 | 2 | 3 | 4 => HashOK_makeLevel4Node 0 0 0 0
  | k + 5 => by
    have ih := HashOK_emptyNode (k + 4)
    exact HashOK_makeCellNode ih ih ih ih

theorem emptyAtHeight_eq : ∀ (H : ℕ) (h : UInt32), h.toNat = H → emptyAtHeight h = emptyNode (H + 4)
  | 0, h, hH => by
    rw [emptyAtHeight, dite_eq_left (u32_eq_of_toNat (by simpa using hH))]
    rfl
  | J + 1, h, hH => by
    have h0 : h ≠ 0 := fun e => by subst e; simp at hH
    rw [emptyAtHeight, dite_eq_right h0]
    dsimp only
    rw [emptyAtHeight_eq J (h - 1) (by rw [toNat_sub_one_of_ne_zero h0]; omega)]
    rfl

theorem filter_mem (keys : List UInt64) (midX midY : UInt64) (east south : Bool) (k : UInt64) :
    k ∈ filterKeys keys midX midY east south [] ↔ k ∈ keys ∧ InQuadrant midX.toNat midY.toNat east south k := by
  rw [filterKeys_mem]
  simp

/--
`keysToMacroCell` builds a well-formed, hash-consistent node of height `H` whose live cells are exactly the keys'
cells.
-/
theorem keysToMacroCell_spec : ∀ (H : ℕ) {keys : List UInt64} {x0 y0 : UInt64} {h : UInt32} {e : MacroCell},
    h.toNat = H → e = emptyAtHeight h → H + 4 ≤ 32 → x0.toNat + 2 ^ (H + 4) ≤ 2 ^ 33 →
    y0.toNat + 2 ^ (H + 4) ≤ 2 ^ 33 → KeysIn keys x0.toNat y0.toNat H →
    WFd (keysToMacroCell keys x0 y0 h e) (H + 4) ∧ HashOK (keysToMacroCell keys x0 y0 h e) ∧
    ∀ x y, cellAt (keysToMacroCell keys x0 y0 h e) x y = true ↔ KeysCells keys x0.toNat y0.toNat x y := by
  intro H
  induction H with
  | zero =>
    intro keys x0 y0 h e hH he h32 hx hy hin
    cases keys with
    | nil =>
      rw [keysToMacroCell, he, emptyAtHeight_eq 0 h hH]
      refine ⟨WFd_emptyNode 0, HashOK_emptyNode _, fun x y => ?_⟩
      rw [cellAt_emptyNode_false]
      simp [KeysCells]
    | cons k0 rest =>
      have h0 : h = 0 := u32_eq_of_toNat (by simpa using hH)
      rw [keysToMacroCell, dite_eq_left h0]
      have hx8 : (x0 + 8).toNat = x0.toNat + 8 := by rw [UInt64.toNat_add]; simp; omega
      have hy8 : (y0 + 8).toNat = y0.toNat + 8 := by rw [UInt64.toNat_add]; simp; omega
      have hp : (2 : ℕ) ^ (0 + 4) = 16 := rfl
      rw [hp] at hx hy
      refine ⟨WFd_makeLevel4Node _ _ _ _, HashOK_makeLevel4Node _ _ _ _, fun x y => ?_⟩
      rw [cellAt_makeLevel4Node, quadSel_eq_true_iff (leafAt_supp _) (leafAt_supp _) (leafAt_supp _)
        (leafAt_supp _), leaf_cells _ (by omega) (by omega), leaf_cells _ (by omega) (by omega),
        leaf_cells _ (by omega) (by omega), leaf_cells _ (by omega) (by omega), hx8, hy8]
      exact keysCells_leaves _ _ _ hin x y
  | succ J ih =>
    intro keys x0 y0 h e hH he h32 hx hy hin
    cases keys with
    | nil =>
      rw [keysToMacroCell, he, emptyAtHeight_eq (J + 1) h hH]
      refine ⟨WFd_emptyNode (J + 1), HashOK_emptyNode _, fun x y => ?_⟩
      rw [cellAt_emptyNode_false]
      simp [KeysCells]
    | cons k0 rest =>
      have h0 : h ≠ 0 := fun e => by subst e; simp at hH
      rw [keysToMacroCell, dite_eq_right h0]
      dsimp only
      rw [splitKeys_eq, he, nwChild_emptyAtHeight h0]
      dsimp only
      generalize hK : k0 :: rest = keys at hin ⊢
      have hh1 : (h - 1).toNat = J := by rw [toNat_sub_one_of_ne_zero h0]; omega
      have hhalf : ((1 : UInt64) <<< (h + 3).toUInt64).toNat = 2 ^ (J + 4) := by
        rw [UInt64.toNat_shiftLeft]
        have e3 : (h + 3).toUInt64.toNat % 64 = J + 4 := by
          rw [UInt32.toNat_toUInt64, UInt32.toNat_add]
          simp
          omega
        rw [e3, UInt64.toNat_one, Nat.shiftLeft_eq, Nat.one_mul]
        apply Nat.mod_eq_of_lt
        exact Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) (show J + 4 ≤ 31 by omega)) (by decide)
      generalize hw : (1 : UInt64) <<< (h + 3).toUInt64 = half at hhalf
      have hp : (2 : ℕ) ^ (J + 1 + 4) = 2 * 2 ^ (J + 4) := by
        rw [show J + 1 + 4 = J + 4 + 1 by omega, Nat.pow_succ]
        omega
      rw [hp] at hx hy
      have hmx : (x0 + half).toNat = x0.toNat + 2 ^ (J + 4) := by rw [UInt64.toNat_add, hhalf]; omega
      have hmy : (y0 + half).toNat = y0.toNat + 2 ^ (J + 4) := by rw [UInt64.toNat_add, hhalf]; omega
      have kin : ∀ (e s : Bool) (X Y : UInt64), X.toNat = (if e then x0.toNat + 2 ^ (J + 4) else x0.toNat) →
          Y.toNat = (if s then y0.toNat + 2 ^ (J + 4) else y0.toNat) →
          KeysIn (filterKeys keys (x0 + half) (y0 + half) e s []) X.toNat Y.toNat J := by
        intro e s X Y hX hY k hk
        rw [filter_mem] at hk
        obtain ⟨hk, hq1, hq2⟩ := hk
        have := hin k hk
        rw [hmx] at hq1
        rw [hmy] at hq2
        rw [hp] at this
        cases e <;> cases s <;> simp at hX hY hq1 hq2 <;> omega
      obtain ⟨w1, H1, c1⟩ := ih hh1 rfl (by omega) (by omega) (by omega) (kin false false x0 y0 (by simp) (by simp))
      obtain ⟨w2, H2, c2⟩ := ih hh1 rfl (by omega) (by omega) (by omega)
        (kin true false (x0 + half) y0 (by simp [hmx]) (by simp))
      obtain ⟨w3, H3, c3⟩ := ih hh1 rfl (by omega) (by omega) (by omega)
        (kin false true x0 (y0 + half) (by simp) (by simp [hmy]))
      obtain ⟨w4, H4, c4⟩ := ih hh1 rfl (by omega) (by omega) (by omega)
        (kin true true (x0 + half) (y0 + half) (by simp [hmx]) (by simp [hmy]))
      refine ⟨WFd_makeCellNode w1 w2 w3 w4, HashOK_makeCellNode H1 H2 H3 H4, fun x y => ?_⟩
      have hw4 := WFd_level_toNat w1 (by omega)
      rw [cellAt_makeCellNode, hw4, quadSel_eq_true_iff (cellAt_supp w1 (by omega)) (cellAt_supp w2 (by omega))
        (cellAt_supp w3 (by omega)) (cellAt_supp w4 (by omega)), c1, c2, c3, c4, hmx, hmy]
      have q := keysCells_quad keys
        (filterKeys keys (x0 + half) (y0 + half) false false [])
        (filterKeys keys (x0 + half) (y0 + half) true false [])
        (filterKeys keys (x0 + half) (y0 + half) false true [])
        (filterKeys keys (x0 + half) (y0 + half) true true [])
        x0.toNat y0.toNat (2 ^ (J + 4))
        (fun k => by rw [filter_mem, hmx, hmy]) (fun k => by rw [filter_mem, hmx, hmy])
        (fun k => by rw [filter_mem, hmx, hmy]) (fun k => by rw [filter_mem, hmx, hmy]) x y
      push_cast at q
      exact q

theorem u64_min_toNat (a b : UInt64) : (min a b).toNat = min a.toNat b.toNat := by
  rw [UInt64.min_def, Nat.min_def]
  split <;> rename_i h <;> rw [UInt64.le_iff_toNat_le] at h <;> split <;> omega

theorem u64_max_toNat (a b : UInt64) : (max a b).toNat = max a.toNat b.toNat := by
  rw [UInt64.max_def, Nat.max_def]
  split <;> rename_i h <;> rw [UInt64.le_iff_toNat_le] at h <;> split <;> omega

/-- The bounding box loop returns a box containing its starting box and every key it scans. -/
theorem cellBoundsLoop_spec (cells : Array UInt64) (limit : UInt32) :
    ∀ (n : ℕ) (i : UInt32) (mnX mnY mxX mxY : UInt64), limit.toNat - i.toNat = n →
      let r := cellBoundsLoop cells i limit mnX mnY mxX mxY
      r.1.toNat ≤ mnX.toNat ∧ r.2.1.toNat ≤ mnY.toNat ∧ mxX.toNat ≤ r.2.2.1.toNat ∧ mxY.toNat ≤ r.2.2.2.toNat ∧
      (mxX.toNat < 2 ^ 32 → r.2.2.1.toNat < 2 ^ 32) ∧ (mxY.toNat < 2 ^ 32 → r.2.2.2.toNat < 2 ^ 32) ∧
      ∀ j, i.toNat ≤ j → j < limit.toNat →
        r.1.toNat ≤ keyX cells[j]! ∧ keyX cells[j]! ≤ r.2.2.1.toNat ∧
        r.2.1.toNat ≤ keyY cells[j]! ∧ keyY cells[j]! ≤ r.2.2.2.toNat := by
  intro n
  induction n with
  | zero =>
    intro i mnX mnY mxX mxY hn
    rw [cellBoundsLoop, dite_eq_right (by rw [UInt32.lt_iff_toNat_lt]; omega)]
    exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, id, id, fun j h1 h2 => by omega⟩
  | succ n ih =>
    intro i mnX mnY mxX mxY hn
    have hi : i < limit := by rw [UInt32.lt_iff_toNat_lt]; omega
    rw [cellBoundsLoop, dite_eq_left hi]
    dsimp only
    have hs1 := u32_succ_toNat hi
    obtain ⟨a1, a2, a3, a4, u1, u2, a5⟩ := ih (i + 1) (min mnX (keyHi cells[i.toNat]!))
      (min mnY (keyLo cells[i.toNat]!)) (max mxX (keyHi cells[i.toNat]!)) (max mxY (keyLo cells[i.toNat]!)) (by omega)
    rw [u64_min_toNat] at a1 a2
    rw [u64_max_toNat] at a3 a4 u1 u2
    have kx := keyX_lt cells[i.toNat]!
    have ky := keyY_lt cells[i.toNat]!
    change max mxX.toNat (keyX cells[i.toNat]!) < 2 ^ 32 → _ at u1
    change max mxY.toNat (keyY cells[i.toNat]!) < 2 ^ 32 → _ at u2
    change _ ≤ min mnX.toNat (keyX cells[i.toNat]!) at a1
    change _ ≤ min mnY.toNat (keyY cells[i.toNat]!) at a2
    change max mxX.toNat (keyX cells[i.toNat]!) ≤ _ at a3
    change max mxY.toNat (keyY cells[i.toNat]!) ≤ _ at a4
    refine ⟨by omega, by omega, by omega, by omega, fun h => u1 (by omega), fun h => u2 (by omega),
      fun j h1 h2 => ?_⟩
    by_cases e : j = i.toNat
    · subst e
      omega
    · exact a5 j (by omega) h2

theorem relativeKeysLoop_spec (cells : Array UInt64) (limit : UInt32) (minX minY : UInt64) :
    ∀ (n : ℕ) (i : UInt32) (acc : List UInt64), limit.toNat - i.toNat = n → ∀ k,
      k ∈ relativeKeysLoop cells i limit minX minY acc ↔ k ∈ acc ∨
        ∃ j, i.toNat ≤ j ∧ j < limit.toNat ∧
          k = ((keyHi cells[j]! - minX) <<< 32) + (keyLo cells[j]! - minY) := by
  intro n
  induction n with
  | zero =>
    intro i acc hn k
    rw [relativeKeysLoop, dite_eq_right (by rw [UInt32.lt_iff_toNat_lt]; omega)]
    exact ⟨Or.inl, fun h => h.elim id fun ⟨j, h1, h2, _⟩ => absurd h2 (by omega)⟩
  | succ n ih =>
    intro i acc hn k
    have hi : i < limit := by rw [UInt32.lt_iff_toNat_lt]; omega
    rw [relativeKeysLoop, dite_eq_left hi]
    dsimp only
    have hs1 := u32_succ_toNat hi
    rw [ih (i + 1) _ (by omega) k, hs1, List.mem_cons]
    constructor
    · rintro ((rfl | h) | ⟨j, h1, h2, rfl⟩)
      · exact Or.inr ⟨i.toNat, Nat.le_refl _, by omega, rfl⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, by omega, h2, rfl⟩
    · rintro (h | ⟨j, h1, h2, rfl⟩)
      · exact Or.inl (Or.inr h)
      · by_cases e : j = i.toNat
        · subst e
          exact Or.inl (Or.inl rfl)
        · exact Or.inr ⟨j, by omega, h2, rfl⟩

theorem shl_one_toNat {L : UInt32} (h : L.toNat < 64) : ((1 : UInt64) <<< L.toUInt64).toNat = 2 ^ L.toNat := by
  rw [UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64, UInt64.toNat_one, Nat.mod_eq_of_lt h, Nat.shiftLeft_eq,
    Nat.one_mul]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) h)

theorem levelForSpanLoop_spec (span : UInt64) :
    ∀ (n : ℕ) (lvl : UInt32), 32 - lvl.toNat = n → lvl.toNat ≤ 32 →
      lvl.toNat ≤ (levelForSpanLoop span lvl).toNat ∧ (levelForSpanLoop span lvl).toNat ≤ 32 ∧
      ((levelForSpanLoop span lvl).toNat = 32 ∨ span.toNat ≤ 2 ^ (levelForSpanLoop span lvl).toNat) := by
  intro n
  induction n with
  | zero =>
    intro lvl hn hl
    rw [levelForSpanLoop]
    split
    · rename_i h
      have := UInt32.lt_iff_toNat_lt.mp h.1
      simp at this
      omega
    · exact ⟨Nat.le_refl _, hl, Or.inl (by omega)⟩
  | succ n ih =>
    intro lvl hn hl
    rw [levelForSpanLoop]
    split
    · rename_i h
      dsimp only
      have h32 := UInt32.lt_iff_toNat_lt.mp h.1
      simp at h32
      have hs := u32_succ_toNat h.1
      obtain ⟨a1, a2, a3⟩ := ih (lvl + 1) (by omega) (by omega)
      exact ⟨by omega, a2, a3⟩
    · rename_i h
      refine ⟨Nat.le_refl _, hl, ?_⟩
      by_cases h32 : lvl.toNat = 32
      · exact Or.inl h32
      · right
        have hlt : lvl < 32 := by rw [UInt32.lt_iff_toNat_lt]; simp; omega
        have := mt (And.intro hlt) h
        rw [UInt64.lt_iff_toNat_lt, shl_one_toNat (by omega)] at this
        omega

theorem mem_toList_map_iff (cells : Array UInt64) (c : Coord) :
    c ∈ cells.toList.map keyCoord ↔ ∃ j, j < cells.size ∧ keyCoord cells[j]! = c := by
  rw [List.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hk
    have hj' : j < cells.size := by simpa using hj
    exact ⟨j, hj', by simp [hj']⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨cells[j]!, List.mem_iff_getElem.mpr ⟨j, by simpa using hj, by simp [hj]⟩, rfl⟩

/--
`cellsToMacroCell` builds, at the corner of the cells' bounding box, a well-formed, hash-consistent node of level
between 5 and 32 whose state has exactly the cells of the keys.
-/
theorem cellsToMacroCell_Impl (cells : Array UInt64) (hsz : cells.size < 2 ^ 32) :
    ∃ L, 5 ≤ L ∧ L ≤ 32 ∧ WFd (cellsToMacroCell cells).2.2 L ∧ HashOK (cellsToMacroCell cells).2.2 ∧
      ∀ c, c ∈ hashLifeToGrid ⟨(((cellsToMacroCell cells).1.toNat : ℤ) - 2 ^ 31,
        ((cellsToMacroCell cells).2.1.toNat : ℤ) - 2 ^ 31), (cellsToMacroCell cells).2.2⟩ ↔
        c ∈ cells.toList.map keyCoord := by
  have hn : cells.size.toUInt32.toNat = cells.size := by simp; omega
  unfold cellsToMacroCell
  dsimp only
  split
  · -- no cells
    rename_i h0
    have h0' : cells.size = 0 := by
      have := congrArg UInt32.toNat (beq_iff_eq.mp h0)
      rw [hn] at this
      simpa using this
    rw [emptyAtHeight_eq 1 1 rfl]
    refine ⟨5, by decide, by decide, WFd_emptyNode 1, HashOK_emptyNode _, fun c => ?_⟩
    unfold hashLifeToGrid
    dsimp only
    rw [mem_macroCellToGrid_iff (WFd_emptyNode 1) (by decide), cellAt_emptyNode_false, mem_toList_map_iff]
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro j hj
    omega
  · rename_i h0
    have hnz : cells.size ≠ 0 := fun e => h0 (by rw [beq_iff_eq]; apply u32_eq_of_toNat; rw [hn, e]; rfl)
    obtain ⟨b1, b2, b3, b4, bu1, bu2, b5⟩ := cellBoundsLoop_spec cells cells.size.toUInt32 _ 1 (keyHi cells[0]!)
      (keyLo cells[0]!) (keyHi cells[0]!) (keyLo cells[0]!) rfl
    generalize hB : cellBoundsLoop cells 1 cells.size.toUInt32 (keyHi cells[0]!) (keyLo cells[0]!) (keyHi cells[0]!)
      (keyLo cells[0]!) = B at b1 b2 b3 b4 bu1 bu2 b5
    obtain ⟨minX, minY, maxX, maxY⟩ := B
    dsimp only at b1 b2 b3 b4 bu1 bu2 b5 ⊢
    rw [hn] at b5
    change minX.toNat ≤ keyX cells[0]! at b1
    change minY.toNat ≤ keyY cells[0]! at b2
    change keyX cells[0]! ≤ maxX.toNat at b3
    change keyY cells[0]! ≤ maxY.toNat at b4
    have hall : ∀ j, j < cells.size →
        minX.toNat ≤ keyX cells[j]! ∧ keyX cells[j]! ≤ maxX.toNat ∧
        minY.toNat ≤ keyY cells[j]! ∧ keyY cells[j]! ≤ maxY.toNat := by
      intro j hj
      by_cases e : j = 0
      · subst e
        omega
      · exact b5 j (by simp; omega) hj
    have hX := keyX_lt cells[0]!
    have hY := keyY_lt cells[0]!
    have hmx := hall 0 (by omega)
    have hmxX : maxX.toNat < 2 ^ 32 := bu1 hX
    have hmxY : maxY.toNat < 2 ^ 32 := bu2 hY
    have hsub : ∀ a b : UInt64, b.toNat ≤ a.toNat → (a - b).toNat = a.toNat - b.toNat := fun a b h =>
      UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr h)
    have hspan : (max (maxX - minX) (maxY - minY) + 1).toNat =
        max (maxX.toNat - minX.toNat) (maxY.toNat - minY.toNat) + 1 := by
      rw [UInt64.toNat_add, u64_max_toNat, hsub _ _ (by omega), hsub _ _ (by omega)]
      simp only [UInt64.toNat_one]
      omega
    -- the level
    obtain ⟨l1, l2, l3⟩ := levelForSpanLoop_spec (max (maxX - minX) (maxY - minY) + 1) _ 5 rfl (by decide)
    generalize hL : levelForSpanLoop (max (maxX - minX) (maxY - minY) + 1) 5 = L at l1 l2 l3
    rw [hspan] at l3
    have h5 : (5 : UInt32).toNat = 5 := rfl
    rw [h5] at l1
    have hfit : max (maxX.toNat - minX.toNat) (maxY.toNat - minY.toNat) + 1 ≤ 2 ^ L.toNat := by
      rcases l3 with e | e
      · rw [e]
        omega
      · exact e
    -- the keys
    have hk := relativeKeysLoop_spec cells cells.size.toUInt32 minX minY _ 0 [] rfl
    rw [hn] at hk
    simp only [List.not_mem_nil, false_or, UInt32.toNat_zero, Nat.zero_le, true_and] at hk
    generalize hK : relativeKeysLoop cells 0 cells.size.toUInt32 minX minY [] = keys at hk
    have hdec : ∀ j, j < cells.size →
        keyX (((keyHi cells[j]! - minX) <<< 32) + (keyLo cells[j]! - minY)) = keyX cells[j]! - minX.toNat ∧
        keyY (((keyHi cells[j]! - minX) <<< 32) + (keyLo cells[j]! - minY)) = keyY cells[j]! - minY.toNat := by
      intro j hj
      obtain ⟨c1, _, c3, _⟩ := hall j hj
      exact relKey_decode c1 c3
    have hH : (L - 4).toNat = L.toNat - 4 := by
      rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; show 4 ≤ L.toNat; omega)]
      rfl
    have hp : 2 ^ (L.toNat - 4 + 4) = 2 ^ L.toNat := by rw [show L.toNat - 4 + 4 = L.toNat by omega]
    have hLp : 2 ^ L.toNat ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) l2
    have hin : KeysIn keys (0 : UInt64).toNat (0 : UInt64).toNat (L.toNat - 4) := by
      intro k hk'
      obtain ⟨j, hj, rfl⟩ := (hk k).mp hk'
      obtain ⟨d1, d2⟩ := hdec j hj
      obtain ⟨c1, c2, c3, c4⟩ := hall j hj
      rw [hp, d1, d2]
      simp only [UInt64.toNat_zero, Nat.zero_le, Nat.zero_add, true_and]
      omega
    obtain ⟨hw, hH', hcell⟩ := keysToMacroCell_spec (L.toNat - 4) hH rfl (by omega) (by rw [hp]; simp; omega)
      (by rw [hp]; simp; omega) hin
    refine ⟨L.toNat, by omega, l2, by rw [show L.toNat = L.toNat - 4 + 4 by omega]; exact hw, hH', fun c => ?_⟩
    unfold hashLifeToGrid
    dsimp only
    rw [mem_macroCellToGrid_iff hw (by omega), hcell, mem_toList_map_iff]
    unfold KeysCells
    simp only [UInt64.toNat_zero, Int.natCast_zero, Int.zero_add]
    constructor
    · rintro ⟨k, hk', e1, e2⟩
      obtain ⟨j, hj, rfl⟩ := (hk k).mp hk'
      obtain ⟨d1, d2⟩ := hdec j hj
      obtain ⟨c1, _, c3, _⟩ := hall j hj
      refine ⟨j, hj, ?_⟩
      rw [keyCoord_eq]
      rw [d1] at e1
      rw [d2] at e2
      apply Prod.ext <;> dsimp only <;> omega
    · rintro ⟨j, hj, rfl⟩
      obtain ⟨d1, d2⟩ := hdec j hj
      obtain ⟨c1, _, c3, _⟩ := hall j hj
      refine ⟨_, (hk _).mpr ⟨j, by omega, rfl⟩, ?_, ?_⟩ <;> rw [keyCoord_eq]
      · rw [d1]; dsimp only; omega
      · rw [d2]; dsimp only; omega

/--
`buildQuadtreeBottomUp` (`cellsToMacroCell`, then the DAG import of the result at the corner `(ox, oy)` that Kotlin
decodes from the returned key coordinates) imports exactly the given cells.
-/
theorem buildQuadtree_Impl {a : FlatHashLifeArena} (hwf : ArenaWF a) (hov : a.overflow = 0) (cells : Array UInt64)
    (hsz : cells.size < 2 ^ 32) (ox oy : Int32) (hox : ox.toInt = ((cellsToMacroCell cells).1.toNat : ℤ) - 2 ^ 31)
    (hoy : oy.toInt = ((cellsToMacroCell cells).2.1.toNat : ℤ) - 2 ^ 31) {id : UInt32}
    {memo : List (MacroCell × UInt32)} {a' : FlatHashLifeArena}
    (hrun : DagIntern [] a (cellsToMacroCell cells).2.2 id memo a') :
    ArenaWF a' ∧ NodesPreserved a a' ∧
    (id ≠ UNCOMPUTED → id < a'.cellCount ∧ cellLevelOf a' id ≤ 32 ∧
      ∀ c, c ∈ hashLifeToGrid (flatState a' ox oy id) ↔ c ∈ cells.toList.map keyCoord) ∧
    (id = UNCOMPUTED → ArenaFull a') := by
  obtain ⟨L, h5, h32, hw, H, hgrid⟩ := cellsToMacroCell_Impl cells hsz
  obtain ⟨w', p', hs, hu⟩ := internMacroCellDag_Impl hwf hov
    ⟨(ox.toInt, oy.toInt), (cellsToMacroCell cells).2.2⟩ ox oy rfl hw h5 (by omega) H hrun
  refine ⟨w', p', fun hne => ?_, hu⟩
  obtain ⟨hlt, heq⟩ := hs hne
  obtain ⟨k, hk, hn⟩ := NodeIs.of_lt' w' hlt
  have hden : denoteCell a' id = (cellsToMacroCell cells).2.2 := congrArg HashLifeCellState.macroCell heq
  have hW := hn.WFd
  rw [hn.denoteCell_eq.symm.trans hden] at hW
  have h256 := u8_toNat_lt (a'.cellLevel[id.toNat]!)
  unfold cellLevelOf at hk
  have := WFd_depth_unique hW hw (by omega) (by omega)
  refine ⟨hlt, by unfold cellLevelOf; omega, fun c => ?_⟩
  rw [heq, ← hgrid c, hox, hoy]

end Algorithm
