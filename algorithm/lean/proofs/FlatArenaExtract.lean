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
# Flat HashLife arena: subnode extraction

Each flat extraction function (centered subnodes, the four stepping quadrants, expansion) returns a node
denoting exactly the corresponding `MacroCell` function applied to the denotation of its inputs.
-/

theorem u8_sub_one_toNat {lvl : UInt8} {h : ℕ} (hl : lvl.toNat = h + 5) : (lvl - 1).toNat = h + 4 := by
  rw [u8_toNat_sub (by simp; omega), hl]
  simp

theorem u8_sub_two_toNat {lvl : UInt8} {h : ℕ} (hl : lvl.toNat = h + 6) : (lvl - 2).toNat = h + 4 := by
  rw [u8_toNat_sub (by simp; omega), hl]
  simp

theorem node_level_toNat {a : FlatHashLifeArena} {h : ℕ} {id : UInt32} {m : MacroCell}
    (hn : NodeIs a (h + 1) id m) : (a.cellLevel[id.toNat]!).toNat = h + 5 := hn.level

theorem node_not_ge {a : FlatHashLifeArena} {h : ℕ} {id : UInt32} {m : MacroCell}
    (hn : NodeIs a (h + 1) id m) : ¬ (id ≥ a.cellCount) := by
  have := u32_lt_iff.mp hn.lt_cell
  rw [ge_iff_le, u32_le_iff]
  omega

/--
The grandchild ids of a node of height `h + 2`, read through its child `c`.
-/
theorem NodeIs.grandchildren {a : FlatHashLifeArena} (hwf : ArenaWF a) {h : ℕ} {c : UInt32} {m : MacroCell}
    (hc : NodeIs a (h + 1) c m) :
    ∃ g1 g2 g3 g4 : MacroCell,
      NodeIs a h a.cellNw[c.toNat]! g1 ∧ NodeIs a h a.cellNe[c.toNat]! g2 ∧
      NodeIs a h a.cellSw[c.toNat]! g3 ∧ NodeIs a h a.cellSe[c.toNat]! g4 ∧ m = makeCellNode g1 g2 g3 g4 := by
  obtain ⟨c1, c2, c3, c4, hm⟩ := hc.children hwf
  exact ⟨_, _, _, _, c1, c2, c3, c4, hm⟩

/--
A node of height 1 (level 5) denotes the cell node of the four Level 4 nodes stored as its children.
-/
theorem NodeIs.level5 {a : FlatHashLifeArena} (hwf : ArenaWF a) {c : UInt32} {m : MacroCell}
    (hc : NodeIs a 1 c m) :
    m = makeCellNode
      (makeLevel4Node a.l4Nw[(a.cellNw[c.toNat]!).toNat]! a.l4Ne[(a.cellNw[c.toNat]!).toNat]!
        a.l4Sw[(a.cellNw[c.toNat]!).toNat]! a.l4Se[(a.cellNw[c.toNat]!).toNat]!)
      (makeLevel4Node a.l4Nw[(a.cellNe[c.toNat]!).toNat]! a.l4Ne[(a.cellNe[c.toNat]!).toNat]!
        a.l4Sw[(a.cellNe[c.toNat]!).toNat]! a.l4Se[(a.cellNe[c.toNat]!).toNat]!)
      (makeLevel4Node a.l4Nw[(a.cellSw[c.toNat]!).toNat]! a.l4Ne[(a.cellSw[c.toNat]!).toNat]!
        a.l4Sw[(a.cellSw[c.toNat]!).toNat]! a.l4Se[(a.cellSw[c.toNat]!).toNat]!)
      (makeLevel4Node a.l4Nw[(a.cellSe[c.toNat]!).toNat]! a.l4Ne[(a.cellSe[c.toNat]!).toNat]!
        a.l4Sw[(a.cellSe[c.toNat]!).toNat]! a.l4Se[(a.cellSe[c.toNat]!).toNat]!) := by
  obtain ⟨c1, c2, c3, c4, hm⟩ := hc.children hwf
  rw [hm]
  show makeCellNode (denoteLevel4 a _) (denoteLevel4 a _) (denoteLevel4 a _) (denoteLevel4 a _) = _
  rw [denoteLevel4_of_lt c1.1, denoteLevel4_of_lt c2.1, denoteLevel4_of_lt c3.1, denoteLevel4_of_lt c4.1]

-- =========================================================================
-- Centered subnodes
-- =========================================================================

theorem flatCenteredSubnode_spec {a : FlatHashLifeArena} (hwf : ArenaWF a) {h : ℕ} {id : UInt32} {m : MacroCell}
    (hn : NodeIs a (h + 1) id m) :
    Grows a (a.centeredSubnode id).2 ∧
    ((a.centeredSubnode id).2.overflow = 0 →
      NodeIs (a.centeredSubnode id).2 h (a.centeredSubnode id).1 (centeredSubnode m)) := by
  unfold FlatHashLifeArena.centeredSubnode
  rw [ite_eq_right (node_not_ge hn)]
  dsimp only
  rw [u8_beq_five_iff (node_level_toNat hn)]
  cases h with
  | zero =>
    simp only [beq_self_eq_true, ite_true]
    have hm := hn.level5 hwf
    refine ⟨(internLevel4_spec hwf _ _ _ _).1, fun hov => ?_⟩
    rw [hm]
    exact (internLevel4_spec hwf _ _ _ _).2 hov
  | succ k =>
    simp only [Nat.add_one_ne_zero, beq_iff_eq, ite_false]
    obtain ⟨c1, c2, c3, c4, hm⟩ := hn.children hwf
    obtain ⟨g11, g12, g13, g14, _, _, _, d1, e1⟩ := c1.grandchildren hwf
    obtain ⟨g21, g22, g23, g24, _, _, d2, _, e2⟩ := c2.grandchildren hwf
    obtain ⟨g31, g32, g33, g34, _, d3, _, _, e3⟩ := c3.grandchildren hwf
    obtain ⟨g41, g42, g43, g44, d4, _, _, _, e4⟩ := c4.grandchildren hwf
    have hs := internCellNode_spec hwf (u8_sub_one_toNat (node_level_toNat hn)) d1 d2 d3 d4
    refine ⟨hs.1, fun hov => ?_⟩
    have := hs.2 hov
    rw [hm, e1, e2, e3, e4]
    exact this

theorem or_not_ge {a : FlatHashLifeArena} {h h' : ℕ} {w e : UInt32} {W E : MacroCell}
    (hw : NodeIs a (h + 1) w W) (he : NodeIs a (h' + 1) e E) :
    ¬ ((decide (w ≥ a.cellCount) || decide (e ≥ a.cellCount)) = true) := by
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or]
  exact ⟨node_not_ge hw, node_not_ge he⟩

theorem centeredHorizontal_spec {a : FlatHashLifeArena} (hwf : ArenaWF a) {h : ℕ} {w e : UInt32}
    {W E : MacroCell} (hw : NodeIs a (h + 1) w W) (he : NodeIs a (h + 1) e E) :
    Grows a (a.centeredHorizontal w e).2 ∧
    ((a.centeredHorizontal w e).2.overflow = 0 →
      NodeIs (a.centeredHorizontal w e).2 h (a.centeredHorizontal w e).1 (centeredHorizontalSubnode W E)) := by
  unfold FlatHashLifeArena.centeredHorizontal
  rw [ite_eq_right (or_not_ge hw he)]
  dsimp only
  rw [u8_beq_five_iff (node_level_toNat hw)]
  cases h with
  | zero =>
    simp only [beq_self_eq_true, ite_true]
    have hW := hw.level5 hwf
    have hE := he.level5 hwf
    refine ⟨(internLevel4_spec hwf _ _ _ _).1, fun hov => ?_⟩
    rw [hW, hE]
    exact (internLevel4_spec hwf _ _ _ _).2 hov
  | succ k =>
    simp only [Nat.add_one_ne_zero, beq_iff_eq, ite_false]
    obtain ⟨_, w2, _, w4, hW⟩ := hw.children hwf
    obtain ⟨e1, _, e3, _, hE⟩ := he.children hwf
    obtain ⟨_, _, _, d1, f1⟩ := w2.children hwf
    obtain ⟨_, _, d2, _, f2⟩ := e1.children hwf
    obtain ⟨_, d3, _, _, f3⟩ := w4.children hwf
    obtain ⟨d4, _, _, _, f4⟩ := e3.children hwf
    have hs := internCellNode_spec hwf (u8_sub_one_toNat (node_level_toNat hw)) d1 d2 d3 d4
    refine ⟨hs.1, fun hov => ?_⟩
    rw [hW, hE, f1, f2, f3, f4]
    exact hs.2 hov

theorem centeredVertical_spec {a : FlatHashLifeArena} (hwf : ArenaWF a) {h : ℕ} {n s : UInt32}
    {N S : MacroCell} (hn : NodeIs a (h + 1) n N) (hs' : NodeIs a (h + 1) s S) :
    Grows a (a.centeredVertical n s).2 ∧
    ((a.centeredVertical n s).2.overflow = 0 →
      NodeIs (a.centeredVertical n s).2 h (a.centeredVertical n s).1 (centeredVerticalSubnode N S)) := by
  unfold FlatHashLifeArena.centeredVertical
  rw [ite_eq_right (or_not_ge hn hs')]
  dsimp only
  rw [u8_beq_five_iff (node_level_toNat hn)]
  cases h with
  | zero =>
    simp only [beq_self_eq_true, ite_true]
    have hN := hn.level5 hwf
    have hS := hs'.level5 hwf
    refine ⟨(internLevel4_spec hwf _ _ _ _).1, fun hov => ?_⟩
    rw [hN, hS]
    exact (internLevel4_spec hwf _ _ _ _).2 hov
  | succ k =>
    simp only [Nat.add_one_ne_zero, beq_iff_eq, ite_false]
    obtain ⟨_, _, n3, n4, hN⟩ := hn.children hwf
    obtain ⟨s1, s2, _, _, hS⟩ := hs'.children hwf
    obtain ⟨_, _, _, d1, f1⟩ := n3.children hwf
    obtain ⟨_, _, d2, _, f2⟩ := n4.children hwf
    obtain ⟨_, d3, _, _, f3⟩ := s1.children hwf
    obtain ⟨d4, _, _, _, f4⟩ := s2.children hwf
    have hsp := internCellNode_spec hwf (u8_sub_one_toNat (node_level_toNat hn)) d1 d2 d3 d4
    refine ⟨hsp.1, fun hov => ?_⟩
    rw [hN, hS, f1, f2, f3, f4]
    exact hsp.2 hov

theorem u8_beq_six_iff {lvl : UInt8} {h : ℕ} (hl : lvl.toNat = h + 6) : (lvl == 6) = (h == 0) := by
  by_cases h0 : h = 0
  · subst h0
    have : lvl = 6 := UInt8.toNat.inj (by rw [hl]; rfl)
    subst this
    rfl
  · have : lvl ≠ 6 := fun e => by
      subst e
      have h6 : (6 : UInt8).toNat = 6 := rfl
      omega
    have e1 : (lvl == 6) = false := by
      cases hb : (lvl == 6)
      · rfl
      · exact absurd (beq_iff_eq.mp hb) this
    have e2 : (h == 0) = false := by
      cases hb : (h == 0)
      · rfl
      · exact absurd (beq_iff_eq.mp hb) h0
    rw [e1, e2]

theorem centeredSubSubnode_spec {a : FlatHashLifeArena} (hwf : ArenaWF a) {h : ℕ} {id : UInt32} {m : MacroCell}
    (hn : NodeIs a (h + 2) id m) :
    Grows a (a.centeredSubSubnode id).2 ∧
    ((a.centeredSubSubnode id).2.overflow = 0 →
      NodeIs (a.centeredSubSubnode id).2 h (a.centeredSubSubnode id).1 (centeredSubSubnode m)) := by
  unfold FlatHashLifeArena.centeredSubSubnode
  rw [ite_eq_right (node_not_ge hn)]
  dsimp only
  have hl : (a.cellLevel[id.toNat]!).toNat = h + 6 := node_level_toNat hn
  rw [u8_beq_six_iff hl]
  obtain ⟨c1, c2, c3, c4, hm⟩ := hn.children hwf
  obtain ⟨_, _, _, g1, e1⟩ := c1.children hwf
  obtain ⟨_, _, g2, _, e2⟩ := c2.children hwf
  obtain ⟨_, g3, _, _, e3⟩ := c3.children hwf
  obtain ⟨g4, _, _, _, e4⟩ := c4.children hwf
  unfold centeredSubSubnode
  rw [hm, e1, e2, e3, e4]
  cases h with
  | zero =>
    simp only [beq_self_eq_true, ite_true]
    rw [← g1.eq, ← g2.eq, ← g3.eq, ← g4.eq]
    show Grows a _ ∧ (_ → NodeIs _ 0 _
      (centeredSubnode (makeCellNode (denoteLevel4 a _) (denoteLevel4 a _) (denoteLevel4 a _)
        (denoteLevel4 a _))))
    rw [denoteLevel4_of_lt g1.1, denoteLevel4_of_lt g2.1, denoteLevel4_of_lt g3.1, denoteLevel4_of_lt g4.1]
    refine ⟨(internLevel4_spec hwf _ _ _ _).1, fun hov => ?_⟩
    exact (internLevel4_spec hwf _ _ _ _).2 hov
  | succ k =>
    simp only [Nat.add_one_ne_zero, beq_iff_eq, ite_false]
    obtain ⟨_, _, _, d1, f1⟩ := g1.children hwf
    obtain ⟨_, _, d2, _, f2⟩ := g2.children hwf
    obtain ⟨_, d3, _, _, f3⟩ := g3.children hwf
    obtain ⟨d4, _, _, _, f4⟩ := g4.children hwf
    have hsp := internCellNode_spec hwf (u8_sub_two_toNat hl) d1 d2 d3 d4
    refine ⟨hsp.1, fun hov => ?_⟩
    rw [f1, f2, f3, f4]
    exact hsp.2 hov

-- =========================================================================
-- Stepping quadrants
-- =========================================================================

theorem stepQuadrants_cell {D1 D2 D3 D4 : MacroCell} {k : ℕ}
    (h1 : WFd D1 (k + 5)) (h2 : WFd D2 (k + 5)) (h3 : WFd D3 (k + 5)) (h4 : WFd D4 (k + 5)) :
    stepQuadrants (makeCellNode D1 D2 D3 D4) =
      { nw := makeCellNode (centeredSubnode D1) (centeredHorizontalSubnode D1 D2)
          (centeredVerticalSubnode D1 D3) (centeredSubSubnode (makeCellNode D1 D2 D3 D4)),
        ne := makeCellNode (centeredHorizontalSubnode D1 D2) (centeredSubnode D2)
          (centeredSubSubnode (makeCellNode D1 D2 D3 D4)) (centeredVerticalSubnode D2 D4),
        sw := makeCellNode (centeredVerticalSubnode D1 D3) (centeredSubSubnode (makeCellNode D1 D2 D3 D4))
          (centeredSubnode D3) (centeredHorizontalSubnode D3 D4),
        se := makeCellNode (centeredSubSubnode (makeCellNode D1 D2 D3 D4)) (centeredVerticalSubnode D2 D4)
          (centeredHorizontalSubnode D3 D4) (centeredSubnode D4) } := by
  obtain ⟨_, _, _, _, _, rfl, _⟩ := WFd_cell h1 (by omega)
  obtain ⟨_, _, _, _, _, rfl, _⟩ := WFd_cell h2 (by omega)
  obtain ⟨_, _, _, _, _, rfl, _⟩ := WFd_cell h3 (by omega)
  obtain ⟨_, _, _, _, _, rfl, _⟩ := WFd_cell h4 (by omega)
  rfl

theorem quadrantNW_spec {a : FlatHashLifeArena} (hwf : ArenaWF a) {h : ℕ} {id : UInt32} {m : MacroCell}
    (hn : NodeIs a (h + 1) id m) :
    Grows a (a.quadrantNW id).2 ∧
    ((a.quadrantNW id).2.overflow = 0 →
      NodeIs (a.quadrantNW id).2 h (a.quadrantNW id).1 (stepQuadrants m).nw) := by
  unfold FlatHashLifeArena.quadrantNW
  rw [ite_eq_right (node_not_ge hn)]
  dsimp only
  have hl := node_level_toNat hn
  rw [u8_beq_five_iff hl]
  cases h with
  | zero =>
    simp only [beq_self_eq_true, ite_true]
    rw [hn.level5 hwf]
    exact internLevel4_spec hwf _ _ _ _
  | succ k =>
    simp only [Nat.add_one_ne_zero, beq_iff_eq, ite_false]
    obtain ⟨c1, c2, c3, c4, hm⟩ := hn.children hwf
    rcases e1 : a.centeredSubnode a.cellNw[id.toNat]! with ⟨n00, a1⟩
    have s1 := flatCenteredSubnode_spec hwf c1
    rw [e1] at s1
    obtain ⟨g1, r1⟩ := s1
    have w1 := g1.wf
    rcases e2 : a1.centeredHorizontal a.cellNw[id.toNat]! a.cellNe[id.toNat]! with ⟨n01, a2⟩
    have s2 := centeredHorizontal_spec w1 (g1.node hwf c1) (g1.node hwf c2)
    rw [e2] at s2
    obtain ⟨g2, r2⟩ := s2
    have w2 := g2.wf
    rcases e3 : a2.centeredVertical a.cellNw[id.toNat]! a.cellSw[id.toNat]! with ⟨n10, a3⟩
    have s3 := centeredVertical_spec w2 ((g1.trans g2).node hwf c1) ((g1.trans g2).node hwf c3)
    rw [e3] at s3
    obtain ⟨g3, r3⟩ := s3
    have w3 := g3.wf
    rcases e4 : a3.centeredSubSubnode id with ⟨n11, a4⟩
    have s4 := centeredSubSubnode_spec w3 (((g1.trans g2).trans g3).node hwf hn)
    rw [e4] at s4
    obtain ⟨g4, r4⟩ := s4
    have w4 := g4.wf
    dsimp only at r1 r2 r3 r4 g1 g2 g3 g4 w1 w2 w3 w4 ⊢
    rw [hm, stepQuadrants_cell c1.WFd c2.WFd c3.WFd c4.WFd, ← hm]
    have hc := fun (hov4 : a4.overflow = 0) =>
      have hov3 := g4.ovf hov4
      have hov2 := g3.ovf hov3
      have hov1 := g2.ovf hov2
      (⟨((g2.trans g3).trans g4).node w1 (r1 hov1), (g3.trans g4).node w2 (r2 hov2), g4.node w3 (r3 hov3),
        r4 hov4⟩ : _ ∧ _ ∧ _ ∧ _)
    have hs := internCellNode_spec' w4 (u8_sub_one_toNat hl) hc
    exact ⟨(((g1.trans g2).trans g3).trans g4).trans hs.1, hs.2⟩

theorem quadrantNE_spec {a : FlatHashLifeArena} (hwf : ArenaWF a) {h : ℕ} {id : UInt32} {m : MacroCell}
    (hn : NodeIs a (h + 1) id m) :
    Grows a (a.quadrantNE id).2 ∧
    ((a.quadrantNE id).2.overflow = 0 →
      NodeIs (a.quadrantNE id).2 h (a.quadrantNE id).1 (stepQuadrants m).ne) := by
  unfold FlatHashLifeArena.quadrantNE
  rw [ite_eq_right (node_not_ge hn)]
  dsimp only
  have hl := node_level_toNat hn
  rw [u8_beq_five_iff hl]
  cases h with
  | zero =>
    simp only [beq_self_eq_true, ite_true]
    rw [hn.level5 hwf]
    exact internLevel4_spec hwf _ _ _ _
  | succ k =>
    simp only [Nat.add_one_ne_zero, beq_iff_eq, ite_false]
    obtain ⟨c1, c2, c3, c4, hm⟩ := hn.children hwf
    rcases e1 : a.centeredHorizontal a.cellNw[id.toNat]! a.cellNe[id.toNat]! with ⟨n1, a1⟩
    have s1 := centeredHorizontal_spec hwf c1 c2
    rw [e1] at s1
    obtain ⟨g1, r1⟩ := s1
    have w1 := g1.wf
    rcases e2 : a1.centeredSubnode a.cellNe[id.toNat]! with ⟨n2, a2⟩
    have s2 := flatCenteredSubnode_spec w1 (g1.node hwf c2)
    rw [e2] at s2
    obtain ⟨g2, r2⟩ := s2
    have w2 := g2.wf
    rcases e3 : a2.centeredSubSubnode id with ⟨n3, a3⟩
    have s3 := centeredSubSubnode_spec w2 ((g1.trans g2).node hwf hn)
    rw [e3] at s3
    obtain ⟨g3, r3⟩ := s3
    have w3 := g3.wf
    rcases e4 : a3.centeredVertical a.cellNe[id.toNat]! a.cellSe[id.toNat]! with ⟨n4, a4⟩
    have s4 := centeredVertical_spec w3 (((g1.trans g2).trans g3).node hwf c2) (((g1.trans g2).trans g3).node hwf c4)
    rw [e4] at s4
    obtain ⟨g4, r4⟩ := s4
    have w4 := g4.wf
    dsimp only at r1 r2 r3 r4 g1 g2 g3 g4 w1 w2 w3 w4 ⊢
    rw [hm, stepQuadrants_cell c1.WFd c2.WFd c3.WFd c4.WFd, ← hm]
    have hc := fun (hov4 : a4.overflow = 0) =>
      have hov3 := g4.ovf hov4
      have hov2 := g3.ovf hov3
      have hov1 := g2.ovf hov2
      (⟨((g2.trans g3).trans g4).node w1 (r1 hov1), (g3.trans g4).node w2 (r2 hov2), g4.node w3 (r3 hov3),
        r4 hov4⟩ : _ ∧ _ ∧ _ ∧ _)
    have hs := internCellNode_spec' w4 (u8_sub_one_toNat hl) hc
    exact ⟨(((g1.trans g2).trans g3).trans g4).trans hs.1, hs.2⟩

theorem quadrantSW_spec {a : FlatHashLifeArena} (hwf : ArenaWF a) {h : ℕ} {id : UInt32} {m : MacroCell}
    (hn : NodeIs a (h + 1) id m) :
    Grows a (a.quadrantSW id).2 ∧
    ((a.quadrantSW id).2.overflow = 0 →
      NodeIs (a.quadrantSW id).2 h (a.quadrantSW id).1 (stepQuadrants m).sw) := by
  unfold FlatHashLifeArena.quadrantSW
  rw [ite_eq_right (node_not_ge hn)]
  dsimp only
  have hl := node_level_toNat hn
  rw [u8_beq_five_iff hl]
  cases h with
  | zero =>
    simp only [beq_self_eq_true, ite_true]
    rw [hn.level5 hwf]
    exact internLevel4_spec hwf _ _ _ _
  | succ k =>
    simp only [Nat.add_one_ne_zero, beq_iff_eq, ite_false]
    obtain ⟨c1, c2, c3, c4, hm⟩ := hn.children hwf
    rcases e1 : a.centeredVertical a.cellNw[id.toNat]! a.cellSw[id.toNat]! with ⟨n1, a1⟩
    have s1 := centeredVertical_spec hwf c1 c3
    rw [e1] at s1
    obtain ⟨g1, r1⟩ := s1
    have w1 := g1.wf
    rcases e2 : a1.centeredSubSubnode id with ⟨n2, a2⟩
    have s2 := centeredSubSubnode_spec w1 (g1.node hwf hn)
    rw [e2] at s2
    obtain ⟨g2, r2⟩ := s2
    have w2 := g2.wf
    rcases e3 : a2.centeredSubnode a.cellSw[id.toNat]! with ⟨n3, a3⟩
    have s3 := flatCenteredSubnode_spec w2 ((g1.trans g2).node hwf c3)
    rw [e3] at s3
    obtain ⟨g3, r3⟩ := s3
    have w3 := g3.wf
    rcases e4 : a3.centeredHorizontal a.cellSw[id.toNat]! a.cellSe[id.toNat]! with ⟨n4, a4⟩
    have s4 := centeredHorizontal_spec w3 (((g1.trans g2).trans g3).node hwf c3) (((g1.trans g2).trans g3).node hwf c4)
    rw [e4] at s4
    obtain ⟨g4, r4⟩ := s4
    have w4 := g4.wf
    dsimp only at r1 r2 r3 r4 g1 g2 g3 g4 w1 w2 w3 w4 ⊢
    rw [hm, stepQuadrants_cell c1.WFd c2.WFd c3.WFd c4.WFd, ← hm]
    have hc := fun (hov4 : a4.overflow = 0) =>
      have hov3 := g4.ovf hov4
      have hov2 := g3.ovf hov3
      have hov1 := g2.ovf hov2
      (⟨((g2.trans g3).trans g4).node w1 (r1 hov1), (g3.trans g4).node w2 (r2 hov2), g4.node w3 (r3 hov3),
        r4 hov4⟩ : _ ∧ _ ∧ _ ∧ _)
    have hs := internCellNode_spec' w4 (u8_sub_one_toNat hl) hc
    exact ⟨(((g1.trans g2).trans g3).trans g4).trans hs.1, hs.2⟩

theorem quadrantSE_spec {a : FlatHashLifeArena} (hwf : ArenaWF a) {h : ℕ} {id : UInt32} {m : MacroCell}
    (hn : NodeIs a (h + 1) id m) :
    Grows a (a.quadrantSE id).2 ∧
    ((a.quadrantSE id).2.overflow = 0 →
      NodeIs (a.quadrantSE id).2 h (a.quadrantSE id).1 (stepQuadrants m).se) := by
  unfold FlatHashLifeArena.quadrantSE
  rw [ite_eq_right (node_not_ge hn)]
  dsimp only
  have hl := node_level_toNat hn
  rw [u8_beq_five_iff hl]
  cases h with
  | zero =>
    simp only [beq_self_eq_true, ite_true]
    rw [hn.level5 hwf]
    exact internLevel4_spec hwf _ _ _ _
  | succ k =>
    simp only [Nat.add_one_ne_zero, beq_iff_eq, ite_false]
    obtain ⟨c1, c2, c3, c4, hm⟩ := hn.children hwf
    rcases e1 : a.centeredSubSubnode id with ⟨n1, a1⟩
    have s1 := centeredSubSubnode_spec hwf hn
    rw [e1] at s1
    obtain ⟨g1, r1⟩ := s1
    have w1 := g1.wf
    rcases e2 : a1.centeredVertical a.cellNe[id.toNat]! a.cellSe[id.toNat]! with ⟨n2, a2⟩
    have s2 := centeredVertical_spec w1 (g1.node hwf c2) (g1.node hwf c4)
    rw [e2] at s2
    obtain ⟨g2, r2⟩ := s2
    have w2 := g2.wf
    rcases e3 : a2.centeredHorizontal a.cellSw[id.toNat]! a.cellSe[id.toNat]! with ⟨n3, a3⟩
    have s3 := centeredHorizontal_spec w2 ((g1.trans g2).node hwf c3) ((g1.trans g2).node hwf c4)
    rw [e3] at s3
    obtain ⟨g3, r3⟩ := s3
    have w3 := g3.wf
    rcases e4 : a3.centeredSubnode a.cellSe[id.toNat]! with ⟨n4, a4⟩
    have s4 := flatCenteredSubnode_spec w3 (((g1.trans g2).trans g3).node hwf c4)
    rw [e4] at s4
    obtain ⟨g4, r4⟩ := s4
    have w4 := g4.wf
    dsimp only at r1 r2 r3 r4 g1 g2 g3 g4 w1 w2 w3 w4 ⊢
    rw [hm, stepQuadrants_cell c1.WFd c2.WFd c3.WFd c4.WFd, ← hm]
    have hc := fun (hov4 : a4.overflow = 0) =>
      have hov3 := g4.ovf hov4
      have hov2 := g3.ovf hov3
      have hov1 := g2.ovf hov2
      (⟨((g2.trans g3).trans g4).node w1 (r1 hov1), (g3.trans g4).node w2 (r2 hov2), g4.node w3 (r3 hov3),
        r4 hov4⟩ : _ ∧ _ ∧ _ ∧ _)
    have hs := internCellNode_spec' w4 (u8_sub_one_toNat hl) hc
    exact ⟨(((g1.trans g2).trans g3).trans g4).trans hs.1, hs.2⟩

-- =========================================================================
-- Expansion
-- =========================================================================

theorem expandCentered_cell {D1 D2 D3 D4 : MacroCell} {h : ℕ} (h1 : WFd D1 (h + 4)) :
    expandCentered (makeCellNode D1 D2 D3 D4) =
      makeCellNode
        (makeCellNode (emptyNode (h + 5)) (emptyNode (h + 5)) (emptyNode (h + 5))
          (makeCellNode (emptyNode (h + 4)) (emptyNode (h + 4)) (emptyNode (h + 4)) D1))
        (makeCellNode (emptyNode (h + 5)) (emptyNode (h + 5))
          (makeCellNode (emptyNode (h + 4)) (emptyNode (h + 4)) D2 (emptyNode (h + 4))) (emptyNode (h + 5)))
        (makeCellNode (emptyNode (h + 5))
          (makeCellNode (emptyNode (h + 4)) D3 (emptyNode (h + 4)) (emptyNode (h + 4)))
          (emptyNode (h + 5)) (emptyNode (h + 5)))
        (makeCellNode (makeCellNode D4 (emptyNode (h + 4)) (emptyNode (h + 4)) (emptyNode (h + 4)))
          (emptyNode (h + 5)) (emptyNode (h + 5)) (emptyNode (h + 5))) := by
  have e : emptySubnode D1 = emptyNode (h + 4) := emptySubnode_of_WFd h1
  rw [emptyNode_succ_four h]
  show expandCentered (MacroCell.cellNode _ D1 D2 D3 D4) = _
  rw [expandCentered.eq_2]
  simp only [e]

theorem u8_add_toNat {lvl : UInt8} {k : ℕ} (hk : lvl.toNat + k < 2 ^ 8) :
    (lvl + k.toUInt8).toNat = lvl.toNat + k := by
  rw [UInt8.toNat_add]
  have : k.toUInt8.toNat = k := by
    rw [Nat.toUInt8, UInt8.toNat_ofNat']
    omega
  rw [this]
  omega

theorem u8_add_one_toNat {lvl : UInt8} {h : ℕ} (hl : lvl.toNat = h + 5) (hh : h ≤ 55) :
    (lvl + 1).toNat = h + 1 + 5 := by
  have := u8_add_toNat (lvl := lvl) (k := 1) (by omega)
  rw [show (1 : ℕ).toUInt8 = 1 from rfl] at this
  omega

theorem u8_add_two_toNat {lvl : UInt8} {h : ℕ} (hl : lvl.toNat = h + 5) (hh : h ≤ 55) :
    (lvl + 2).toNat = h + 2 + 5 := by
  have := u8_add_toNat (lvl := lvl) (k := 2) (by omega)
  rw [show (2 : ℕ).toUInt8 = 2 from rfl] at this
  omega

/--
Flat `expandCentered` builds exactly `MacroCell.expandCentered` of a node of level at most 60.
-/
theorem flatExpandCentered_spec {a : FlatHashLifeArena} (hwf : ArenaWF a) {h : ℕ} {id : UInt32} {m : MacroCell}
    (hn : NodeIs a (h + 1) id m) (hh : h ≤ 55) :
    Grows a (a.expandCentered id).2 ∧
    ((a.expandCentered id).2.overflow = 0 →
      NodeIs (a.expandCentered id).2 (h + 3) (a.expandCentered id).1 (expandCentered m)) := by
  unfold FlatHashLifeArena.expandCentered
  rw [ite_eq_right (node_not_ge hn)]
  dsimp only
  have hl := node_level_toNat hn
  have hidN := u32_lt_iff.mp hn.lt_cell
  obtain ⟨c1, c2, c3, c4, hm⟩ := hn.children hwf
  rw [hm, expandCentered_cell c1.WFd]
  rw [emptyNodeForLevel_pred hl, emptyNodeForLevel_self hl]
  have hek := NodeIs.emptyForLevel hwf h (by omega)
  have hek1 := NodeIs.emptyCell hwf h (by omega)
  -- the four corner nodes of the level-(h+5) ring
  rcases e1 : a.internCellNode a.cellLevel[id.toNat]! (emptyNodeForLevel (h + 4).toUInt32)
      (emptyNodeForLevel (h + 4).toUInt32) (emptyNodeForLevel (h + 4).toUInt32) a.cellNw[id.toNat]! with
    ⟨x1, a1⟩
  have s1 := internCellNode_spec hwf hl hek hek hek c1
  rw [e1] at s1
  obtain ⟨g1, r1⟩ := s1
  have w1 := g1.wf
  dsimp only at g1 r1 w1 ⊢
  rw [(g1.ext.cell _ hidN).2.1]
  rcases e2 : a1.internCellNode a.cellLevel[id.toNat]! (emptyNodeForLevel (h + 4).toUInt32)
      (emptyNodeForLevel (h + 4).toUInt32) a.cellNe[id.toNat]! (emptyNodeForLevel (h + 4).toUInt32) with
    ⟨x2, a2⟩
  have s2 := internCellNode_spec w1 hl (g1.node hwf hek) (g1.node hwf hek) (g1.node hwf c2) (g1.node hwf hek)
  rw [e2] at s2
  obtain ⟨g2, r2⟩ := s2
  have w2 := g2.wf
  dsimp only at g2 r2 w2 ⊢
  have g12 := g1.trans g2
  rw [(g12.ext.cell _ hidN).2.2.1]
  rcases e3 : a2.internCellNode a.cellLevel[id.toNat]! (emptyNodeForLevel (h + 4).toUInt32)
      a.cellSw[id.toNat]! (emptyNodeForLevel (h + 4).toUInt32) (emptyNodeForLevel (h + 4).toUInt32) with
    ⟨x3, a3⟩
  have s3 := internCellNode_spec w2 hl (g12.node hwf hek) (g12.node hwf c3) (g12.node hwf hek)
    (g12.node hwf hek)
  rw [e3] at s3
  obtain ⟨g3, r3⟩ := s3
  have w3 := g3.wf
  dsimp only at g3 r3 w3 ⊢
  have g13 := g12.trans g3
  rw [(g13.ext.cell _ hidN).2.2.2.1]
  rcases e4 : a3.internCellNode a.cellLevel[id.toNat]! a.cellSe[id.toNat]!
      (emptyNodeForLevel (h + 4).toUInt32) (emptyNodeForLevel (h + 4).toUInt32)
      (emptyNodeForLevel (h + 4).toUInt32) with
    ⟨x4, a4⟩
  have s4 := internCellNode_spec w3 hl (g13.node hwf c4) (g13.node hwf hek) (g13.node hwf hek)
    (g13.node hwf hek)
  rw [e4] at s4
  obtain ⟨g4, r4⟩ := s4
  have w4 := g4.wf
  dsimp only at g4 r4 w4 ⊢
  have g14 := g13.trans g4
  -- the four quadrants of the level-(h+6) ring
  have hl1 := u8_add_one_toNat hl hh
  rcases e5 : a4.internCellNode (a.cellLevel[id.toNat]! + 1) h.toUInt32 h.toUInt32 h.toUInt32 x1 with ⟨y1, a5⟩
  have s5 := internCellNode_spec' w4 hl1 (fun hov => ⟨g14.node hwf hek1, g14.node hwf hek1,
    g14.node hwf hek1, ((g2.trans g3).trans g4).node w1 (r1 (g2.ovf (g3.ovf (g4.ovf hov))))⟩)
  rw [e5] at s5
  obtain ⟨g5, r5⟩ := s5
  have w5 := g5.wf
  dsimp only at g5 r5 w5 ⊢
  have g15 := g14.trans g5
  rcases e6 : a5.internCellNode (a.cellLevel[id.toNat]! + 1) h.toUInt32 h.toUInt32 x2 h.toUInt32 with ⟨y2, a6⟩
  have s6 := internCellNode_spec' w5 hl1 (fun hov => ⟨g15.node hwf hek1, g15.node hwf hek1,
    ((g3.trans g4).trans g5).node w2 (r2 (g3.ovf (g4.ovf (g5.ovf hov)))), g15.node hwf hek1⟩)
  rw [e6] at s6
  obtain ⟨g6, r6⟩ := s6
  have w6 := g6.wf
  dsimp only at g6 r6 w6 ⊢
  have g16 := g15.trans g6
  rcases e7 : a6.internCellNode (a.cellLevel[id.toNat]! + 1) h.toUInt32 x3 h.toUInt32 h.toUInt32 with ⟨y3, a7⟩
  have s7 := internCellNode_spec' w6 hl1 (fun hov => ⟨g16.node hwf hek1,
    ((g4.trans g5).trans g6).node w3 (r3 (g4.ovf (g5.ovf (g6.ovf hov)))), g16.node hwf hek1,
    g16.node hwf hek1⟩)
  rw [e7] at s7
  obtain ⟨g7, r7⟩ := s7
  have w7 := g7.wf
  dsimp only at g7 r7 w7 ⊢
  have g17 := g16.trans g7
  rcases e8 : a7.internCellNode (a.cellLevel[id.toNat]! + 1) x4 h.toUInt32 h.toUInt32 h.toUInt32 with ⟨y4, a8⟩
  have s8 := internCellNode_spec' w7 hl1 (fun hov =>
    ⟨((g5.trans g6).trans g7).node w4 (r4 (g5.ovf (g6.ovf (g7.ovf hov)))), g17.node hwf hek1,
      g17.node hwf hek1, g17.node hwf hek1⟩)
  rw [e8] at s8
  obtain ⟨g8, r8⟩ := s8
  have w8 := g8.wf
  dsimp only at g8 r8 w8 ⊢
  have g18 := g17.trans g8
  -- the expanded root
  have hs := internCellNode_spec' w8 (u8_add_two_toNat hl hh) (fun hov =>
    ⟨((g6.trans g7).trans g8).node w5 (r5 (g6.ovf (g7.ovf (g8.ovf hov)))),
      (g7.trans g8).node w6 (r6 (g7.ovf (g8.ovf hov))), g8.node w7 (r7 (g8.ovf hov)), r8 hov⟩)
  exact ⟨g18.trans hs.1, hs.2⟩

/--
Flat `expandLevel4Centered` builds exactly `MacroCell.expandCentered` of a Level 4 node.
-/
theorem expandLevel4Centered_spec {a : FlatHashLifeArena} (hwf : ArenaWF a) {id : UInt32} {m : MacroCell}
    (hn : NodeIs a 0 id m) :
    Grows a (a.expandLevel4Centered id).2 ∧
    ((a.expandLevel4Centered id).2.overflow = 0 →
      NodeIs (a.expandLevel4Centered id).2 2 (a.expandLevel4Centered id).1 (expandCentered m)) := by
  unfold FlatHashLifeArena.expandLevel4Centered
  have hid := hn.1
  have hidN := u32_lt_iff.mp hid
  rw [ite_eq_right (by rw [ge_iff_le, u32_le_iff]; omega)]
  dsimp only
  rw [← hn.2, denoteLevel4_of_lt hid]
  have he := NodeIs.emptyL4 hwf
  rcases e1 : a.internLevel4 0 0 0 a.l4Nw[id.toNat]! with ⟨x1, a1⟩
  have s1 := internLevel4_spec hwf 0 0 0 a.l4Nw[id.toNat]!
  rw [e1] at s1
  obtain ⟨g1, r1⟩ := s1
  have w1 := g1.wf
  dsimp only at g1 r1 w1 ⊢
  rw [(g1.ext.l4 _ hidN).2.1]
  rcases e2 : a1.internLevel4 0 0 a.l4Ne[id.toNat]! 0 with ⟨x2, a2⟩
  have s2 := internLevel4_spec w1 0 0 a.l4Ne[id.toNat]! 0
  rw [e2] at s2
  obtain ⟨g2, r2⟩ := s2
  have w2 := g2.wf
  dsimp only at g2 r2 w2 ⊢
  have g12 := g1.trans g2
  rw [(g12.ext.l4 _ hidN).2.2.1]
  rcases e3 : a2.internLevel4 0 a.l4Sw[id.toNat]! 0 0 with ⟨x3, a3⟩
  have s3 := internLevel4_spec w2 0 a.l4Sw[id.toNat]! 0 0
  rw [e3] at s3
  obtain ⟨g3, r3⟩ := s3
  have w3 := g3.wf
  dsimp only at g3 r3 w3 ⊢
  have g13 := g12.trans g3
  rw [(g13.ext.l4 _ hidN).2.2.2]
  rcases e4 : a3.internLevel4 a.l4Se[id.toNat]! 0 0 0 with ⟨x4, a4⟩
  have s4 := internLevel4_spec w3 a.l4Se[id.toNat]! 0 0 0
  rw [e4] at s4
  obtain ⟨g4, r4⟩ := s4
  have w4 := g4.wf
  dsimp only at g4 r4 w4 ⊢
  have g14 := g13.trans g4
  have h5 : (5 : UInt8).toNat = 0 + 5 := rfl
  rcases e5 : a4.internCellNode 5 0 0 0 x1 with ⟨y1, a5⟩
  have s5 := internCellNode_spec' w4 h5 (fun hov => ⟨g14.node hwf he, g14.node hwf he, g14.node hwf he,
    ((g2.trans g3).trans g4).node w1 (r1 (g2.ovf (g3.ovf (g4.ovf hov))))⟩)
  rw [e5] at s5
  obtain ⟨g5, r5⟩ := s5
  have w5 := g5.wf
  dsimp only at g5 r5 w5 ⊢
  have g15 := g14.trans g5
  rcases e6 : a5.internCellNode 5 0 0 x2 0 with ⟨y2, a6⟩
  have s6 := internCellNode_spec' w5 h5 (fun hov => ⟨g15.node hwf he, g15.node hwf he,
    ((g3.trans g4).trans g5).node w2 (r2 (g3.ovf (g4.ovf (g5.ovf hov)))), g15.node hwf he⟩)
  rw [e6] at s6
  obtain ⟨g6, r6⟩ := s6
  have w6 := g6.wf
  dsimp only at g6 r6 w6 ⊢
  have g16 := g15.trans g6
  rcases e7 : a6.internCellNode 5 0 x3 0 0 with ⟨y3, a7⟩
  have s7 := internCellNode_spec' w6 h5 (fun hov => ⟨g16.node hwf he,
    ((g4.trans g5).trans g6).node w3 (r3 (g4.ovf (g5.ovf (g6.ovf hov)))), g16.node hwf he, g16.node hwf he⟩)
  rw [e7] at s7
  obtain ⟨g7, r7⟩ := s7
  have w7 := g7.wf
  dsimp only at g7 r7 w7 ⊢
  have g17 := g16.trans g7
  rcases e8 : a7.internCellNode 5 x4 0 0 0 with ⟨y4, a8⟩
  have s8 := internCellNode_spec' w7 h5 (fun hov =>
    ⟨((g5.trans g6).trans g7).node w4 (r4 (g5.ovf (g6.ovf (g7.ovf hov)))), g17.node hwf he,
      g17.node hwf he, g17.node hwf he⟩)
  rw [e8] at s8
  obtain ⟨g8, r8⟩ := s8
  have w8 := g8.wf
  dsimp only at g8 r8 w8 ⊢
  have g18 := g17.trans g8
  have h6 : (6 : UInt8).toNat = 1 + 5 := rfl
  have hs := internCellNode_spec' w8 h6 (fun hov =>
    ⟨((g6.trans g7).trans g8).node w5 (r5 (g6.ovf (g7.ovf (g8.ovf hov)))),
      (g7.trans g8).node w6 (r6 (g7.ovf (g8.ovf hov))), g8.node w7 (r7 (g8.ovf hov)), r8 hov⟩)
  exact ⟨g18.trans hs.1, hs.2⟩

-- =========================================================================
-- Expansion decision
-- =========================================================================

theorem popcount64_zero_eq : popcount64 0 = 0 := by decide

theorem u8_beq_toNat (x y : UInt8) : (x == y) = (x.toNat == y.toNat) := by
  by_cases e : x = y
  · subst e
    simp
  · have : x.toNat ≠ y.toNat := fun h => e (UInt8.toNat.inj h)
    rw [beq_eq_false_iff_ne.mpr e, beq_eq_false_iff_ne.mpr this]

theorem level4_size_eq (nw ne sw se : UInt64) :
    (makeLevel4Node nw ne sw se).size =
      (popcount64 nw).toUInt64 + (popcount64 ne).toUInt64 + (popcount64 sw).toUInt64 +
        (popcount64 se).toUInt64 := rfl

theorem cell_size_eq (nw ne sw se : MacroCell) :
    (makeCellNode nw ne sw se).size = nw.size + ne.size + sw.size + se.size := rfl

theorem popLevel4Id_eq {a : FlatHashLifeArena} {id : UInt32} {m : MacroCell} (hn : NodeIs a 0 id m) :
    popLevel4Id a id = m.size := by
  unfold popLevel4Id
  rw [ite_eq_left hn.1, ← hn.2, denoteLevel4_of_lt hn.1, level4_size_eq]

theorem cellPop_eq {a : FlatHashLifeArena} (hwf : ArenaWF a) {h : ℕ} {id : UInt32} {m : MacroCell}
    (hn : NodeIs a (h + 1) id m) : a.cellPop[id.toNat]! = m.size := by
  rw [hwf.cellPop id hn.lt_cell, hn.denoteCell_eq]

theorem centeredSubSubnodeSizeCell_spec {a : FlatHashLifeArena} (hwf : ArenaWF a) {h : ℕ} {id : UInt32}
    {m : MacroCell} (hn : NodeIs a (h + 1) id m) :
    centeredSubSubnodeSizeCell a id = (centeredSubSubnode m).size := by
  unfold centeredSubSubnodeSizeCell
  rw [ite_eq_right (node_not_ge hn)]
  dsimp only
  have hl := node_level_toNat hn
  obtain ⟨c1, c2, c3, c4, hm⟩ := hn.children hwf
  rcases h with _ | _ | _ | k
  · simp only [u8_beq_toNat _ 5, hl, UInt8.reduceToNat]
    simp only [show (0 + 5 == 5) = true from rfl, ite_true]
    rw [hn.level5 hwf]
    show _ = (makeLevel4Node 0 0 0 _).size
    rw [level4_size_eq, popcount64_zero_eq]
    simp
  · simp only [u8_beq_toNat _ 5, u8_beq_toNat _ 6, hl, UInt8.reduceToNat]
    simp only [show (0 + 1 + 5 == 5) = false from rfl, show (0 + 1 + 5 == 6) = true from rfl,
      Bool.false_eq_true, ite_false, ite_true]
    rw [hm, c1.level5 hwf, c2.level5 hwf, c3.level5 hwf, c4.level5 hwf]
    rfl
  · simp only [u8_beq_toNat _ 5, u8_beq_toNat _ 6, u8_beq_toNat _ 7, hl, UInt8.reduceToNat]
    simp only [show (0 + 1 + 1 + 5 == 5) = false from rfl, show (0 + 1 + 1 + 5 == 6) = false from rfl,
      show (0 + 1 + 1 + 5 == 7) = true from rfl, Bool.false_eq_true, ite_false, ite_true]
    obtain ⟨_, _, _, g1, f1⟩ := c1.children hwf
    obtain ⟨_, _, g2, _, f2⟩ := c2.children hwf
    obtain ⟨_, g3, _, _, f3⟩ := c3.children hwf
    obtain ⟨g4, _, _, _, f4⟩ := c4.children hwf
    obtain ⟨_, _, _, q1, p1⟩ := g1.children hwf
    obtain ⟨_, _, q2, _, p2⟩ := g2.children hwf
    obtain ⟨_, q3, _, _, p3⟩ := g3.children hwf
    obtain ⟨q4, _, _, _, p4⟩ := g4.children hwf
    rw [popLevel4Id_eq q1, popLevel4Id_eq q2, popLevel4Id_eq q3, popLevel4Id_eq q4, hm, f1, f2, f3, f4, p1, p2,
      p3, p4]
    rfl
  · simp only [u8_beq_toNat _ 5, u8_beq_toNat _ 6, u8_beq_toNat _ 7, hl, UInt8.reduceToNat]
    have e5 : (k + 1 + 1 + 1 + 5 == 5) = false := by simp
    have e6 : (k + 1 + 1 + 1 + 5 == 6) = false := by simp
    have e7 : (k + 1 + 1 + 1 + 5 == 7) = false := by simp
    simp only [e5, e6, e7, Bool.false_eq_true, ite_false]
    obtain ⟨_, _, _, g1, f1⟩ := c1.children hwf
    obtain ⟨_, _, g2, _, f2⟩ := c2.children hwf
    obtain ⟨_, g3, _, _, f3⟩ := c3.children hwf
    obtain ⟨g4, _, _, _, f4⟩ := c4.children hwf
    obtain ⟨_, _, _, q1, p1⟩ := g1.children hwf
    obtain ⟨_, _, q2, _, p2⟩ := g2.children hwf
    obtain ⟨_, q3, _, _, p3⟩ := g3.children hwf
    obtain ⟨q4, _, _, _, p4⟩ := g4.children hwf
    rw [cellPop_eq hwf q1, cellPop_eq hwf q2, cellPop_eq hwf q3, cellPop_eq hwf q4, hm, f1, f2, f3, f4, p1, p2,
      p3, p4]
    rfl

/--
The flat expansion decision is exactly `needToExpand` of the denoted node.
-/
theorem needToExpandCell_spec {a : FlatHashLifeArena} (hwf : ArenaWF a) {h : ℕ} {id : UInt32} {m : MacroCell}
    (hn : NodeIs a (h + 1) id m) :
    a.needToExpandCell id = needToExpand m := by
  unfold FlatHashLifeArena.needToExpandCell needToExpand centeredSubSubnodeSize
  rw [ite_eq_right (node_not_ge hn)]
  dsimp only
  rw [centeredSubSubnodeSizeCell_spec hwf hn, cellPop_eq hwf hn]
  have hb := node_level_toNat hn
  have hb' := u8_toNat_lt (a.cellLevel[id.toNat]!)
  have hlv : m.level.toNat = h + 5 := by
    have := WFd_level_toNat hn.WFd (by omega)
    omega
  have : (m.level ≤ 4) = False := by
    rw [UInt32.le_iff_toNat_le, hlv]
    simp
  simp [this]

end Algorithm
