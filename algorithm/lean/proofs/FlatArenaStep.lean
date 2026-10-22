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
import proofs.FlatArenaExtract

local notation "ℕ" => Nat

namespace Algorithm

/-!
# Flat HashLife arena: stepping

Memoized HashLife stepping in the flat arena computes exactly `hashLifeStep` of the denoted node, and every
memo it writes is correct.
-/

-- =========================================================================
-- HashLife step equations on well-formed nodes
-- =========================================================================

theorem hashLifeStep_eq_aux_of_WFd {m : MacroCell} {d : ℕ} (hm : WFd m d) :
    hashLifeStep m = hashLifeStepRecursiveAux d m := by
  unfold hashLifeStep hashLifeStepRecursive
  rw [WFd_depth hm]

theorem hashLifeStep_level5 {L1 L2 L3 L4 : MacroCell}
    (h1 : WFd L1 4) (h2 : WFd L2 4) (h3 : WFd L3 4) (h4 : WFd L4 4) :
    hashLifeStep (makeCellNode L1 L2 L3 L4) =
      makeLevel4Node (stepLevel4Node (stepQuadrants (makeCellNode L1 L2 L3 L4)).nw)
        (stepLevel4Node (stepQuadrants (makeCellNode L1 L2 L3 L4)).ne)
        (stepLevel4Node (stepQuadrants (makeCellNode L1 L2 L3 L4)).sw)
        (stepLevel4Node (stepQuadrants (makeCellNode L1 L2 L3 L4)).se) := by
  obtain ⟨_, _, _, _, _, rfl⟩ := WFd_level4 h1
  obtain ⟨_, _, _, _, _, rfl⟩ := WFd_level4 h2
  obtain ⟨_, _, _, _, _, rfl⟩ := WFd_level4 h3
  obtain ⟨_, _, _, _, _, rfl⟩ := WFd_level4 h4
  rfl

theorem hashLifeStep_cell {D1 D2 D3 D4 : MacroCell} {k : ℕ}
    (h1 : WFd D1 (k + 5)) (h2 : WFd D2 (k + 5)) (h3 : WFd D3 (k + 5)) (h4 : WFd D4 (k + 5))
    (q1 : WFd (stepQuadrants (makeCellNode D1 D2 D3 D4)).nw (k + 5))
    (q2 : WFd (stepQuadrants (makeCellNode D1 D2 D3 D4)).ne (k + 5))
    (q3 : WFd (stepQuadrants (makeCellNode D1 D2 D3 D4)).sw (k + 5))
    (q4 : WFd (stepQuadrants (makeCellNode D1 D2 D3 D4)).se (k + 5)) :
    hashLifeStep (makeCellNode D1 D2 D3 D4) =
      makeCellNode (hashLifeStep (stepQuadrants (makeCellNode D1 D2 D3 D4)).nw)
        (hashLifeStep (stepQuadrants (makeCellNode D1 D2 D3 D4)).ne)
        (hashLifeStep (stepQuadrants (makeCellNode D1 D2 D3 D4)).sw)
        (hashLifeStep (stepQuadrants (makeCellNode D1 D2 D3 D4)).se) := by
  rw [hashLifeStep_eq_aux_of_WFd (WFd_makeCellNode h1 h2 h3 h4), hashLifeStep_eq_aux_of_WFd q1,
    hashLifeStep_eq_aux_of_WFd q2, hashLifeStep_eq_aux_of_WFd q3, hashLifeStep_eq_aux_of_WFd q4]
  obtain ⟨_, _, _, _, _, rfl, _⟩ := WFd_cell h1 (by omega)
  obtain ⟨_, _, _, _, _, rfl, _⟩ := WFd_cell h2 (by omega)
  obtain ⟨_, _, _, _, _, rfl, _⟩ := WFd_cell h3 (by omega)
  obtain ⟨_, _, _, _, _, rfl, _⟩ := WFd_cell h4 (by omega)
  rfl

-- =========================================================================
-- Level 4 and level 5 steps
-- =========================================================================

theorem stepLevel4_spec {a : FlatHashLifeArena} (hwf : ArenaWF a) {id : UInt32} {m : MacroCell}
    (hn : NodeIs a 0 id m) :
    Grows a (a.stepLevel4 id).2 ∧ (a.stepLevel4 id).1 = stepLevel4Node m := by
  have hid := hn.1
  have hm : m = makeLevel4Node a.l4Nw[id.toNat]! a.l4Ne[id.toNat]! a.l4Sw[id.toNat]! a.l4Se[id.toNat]! := by
    rw [← hn.2, denoteLevel4_of_lt hid]
  unfold FlatHashLifeArena.stepLevel4
  rw [ite_eq_right (by rw [ge_iff_le, u32_le_iff]; have := u32_lt_iff.mp hid; omega)]
  dsimp only
  rw [hm]
  split
  · rename_i hhas
    exact ⟨Grows.refl hwf, hwf.l4Memo id hid (beq_iff_eq.mp hhas)⟩
  · exact ⟨Grows.setL4StepRes hwf hid rfl, rfl⟩

theorem stepLevel5_spec {a : FlatHashLifeArena} (hwf : ArenaWF a) {id : UInt32} {m : MacroCell}
    (hn : NodeIs a 1 id m) :
    Grows a (a.stepLevel5 id).2 ∧
    ((a.stepLevel5 id).2.overflow = 0 → NodeIs (a.stepLevel5 id).2 0 (a.stepLevel5 id).1 (hashLifeStep m)) ∧
    ((a.stepLevel5 id).2.overflow = 0 → (a.stepLevel5 id).2.cellStepRes[id.toNat]! ≠ UNCOMPUTED) := by
  unfold FlatHashLifeArena.stepLevel5
  rw [ite_eq_right (node_not_ge hn)]
  dsimp only
  split
  · rename_i hcached
    refine ⟨Grows.refl hwf, fun _ => ?_, fun _ => by simpa using hcached⟩
    have hmemo := hwf.cellMemo id hn.lt_cell (by simpa using hcached)
    rw [hn.level, hn.denoteCell_eq] at hmemo
    exact hmemo
  · rcases e1 : a.quadrantNW id with ⟨q1, a1⟩
    have s1 := quadrantNW_spec hwf hn
    rw [e1] at s1
    obtain ⟨g1, r1⟩ := s1
    have w1 := g1.wf
    rcases e2 : a1.quadrantNE id with ⟨q2, a2⟩
    have s2 := quadrantNE_spec w1 (g1.node hwf hn)
    rw [e2] at s2
    obtain ⟨g2, r2⟩ := s2
    have w2 := g2.wf
    rcases e3 : a2.quadrantSW id with ⟨q3, a3⟩
    have s3 := quadrantSW_spec w2 ((g1.trans g2).node hwf hn)
    rw [e3] at s3
    obtain ⟨g3, r3⟩ := s3
    have w3 := g3.wf
    rcases e4 : a3.quadrantSE id with ⟨q4, a4⟩
    have s4 := quadrantSE_spec w3 (((g1.trans g2).trans g3).node hwf hn)
    rw [e4] at s4
    obtain ⟨g4, r4⟩ := s4
    have w4 := g4.wf
    dsimp only at g1 g2 g3 g4 r1 r2 r3 r4 w1 w2 w3 w4 ⊢
    have g14 := ((g1.trans g2).trans g3).trans g4
    split
    · rename_i hov
      exact ⟨g14, fun h => absurd h (by simpa using hov), fun h => absurd h (by simpa using hov)⟩
    · rename_i hov
      have hov4 : a4.overflow = 0 := by simpa using hov
      have hov3 := g4.ovf hov4
      have hov2 := g3.ovf hov3
      have hov1 := g2.ovf hov2
      have n1 := ((g2.trans g3).trans g4).node w1 (r1 hov1)
      have n2 := (g3.trans g4).node w2 (r2 hov2)
      have n3 := g4.node w3 (r3 hov3)
      have n4 := r4 hov4
      rcases e5 : a4.stepLevel4 q1 with ⟨v1, a5⟩
      have s5 := stepLevel4_spec w4 n1
      rw [e5] at s5
      obtain ⟨g5, v1e⟩ := s5
      have w5 := g5.wf
      rcases e6 : a5.stepLevel4 q2 with ⟨v2, a6⟩
      have s6 := stepLevel4_spec w5 (g5.node w4 n2)
      rw [e6] at s6
      obtain ⟨g6, v2e⟩ := s6
      have w6 := g6.wf
      rcases e7 : a6.stepLevel4 q3 with ⟨v3, a7⟩
      have s7 := stepLevel4_spec w6 ((g5.trans g6).node w4 n3)
      rw [e7] at s7
      obtain ⟨g7, v3e⟩ := s7
      have w7 := g7.wf
      rcases e8 : a7.stepLevel4 q4 with ⟨v4, a8⟩
      have s8 := stepLevel4_spec w7 (((g5.trans g6).trans g7).node w4 n4)
      rw [e8] at s8
      obtain ⟨g8, v4e⟩ := s8
      have w8 := g8.wf
      dsimp only at g5 g6 g7 g8 v1e v2e v3e v4e w5 w6 w7 w8 ⊢
      have g18 := (((g14.trans g5).trans g6).trans g7).trans g8
      rcases e9 : a8.internLevel4 v1 v2 v3 v4 with ⟨res, a9⟩
      have s9 := internLevel4_spec w8 v1 v2 v3 v4
      rw [e9] at s9
      obtain ⟨g9, r9⟩ := s9
      have w9 := g9.wf
      dsimp only at g9 r9 w9 ⊢
      have g19 := g18.trans g9
      split
      · rename_i hov9
        exact ⟨g19, fun h => absurd h (by simpa using hov9), fun h => absurd h (by simpa using hov9)⟩
      · rename_i hov9
        have hov9' : a9.overflow = 0 := by simpa using hov9
        have hres := r9 hov9'
        have hm := hn.level5 hwf
        have hstep : hashLifeStep m = makeLevel4Node v1 v2 v3 v4 := by
          rw [v1e, v2e, v3e, v4e, hm]
          exact hashLifeStep_level5 (WFd_makeLevel4Node _ _ _ _) (WFd_makeLevel4Node _ _ _ _)
            (WFd_makeLevel4Node _ _ _ _) (WFd_makeLevel4Node _ _ _ _)
        rw [← hstep] at hres
        have gm := Grows.setCellStepRes w9 (g19.node hwf hn) hres
        refine ⟨g19.trans gm, fun _ => gm.node w9 hres, fun _ => ?_⟩
        have hid9 := (g19.node hwf hn).lt_cell
        have hlt : id.toNat < a9.cellStepRes.size := by
          have := u32_lt_iff.mp hid9; have := w9.cellCountLe; have := w9.cellSize.2.2.2.2.2.2; omega
        show (a9.cellStepRes.set! id.toNat res)[id.toNat]! ≠ UNCOMPUTED
        rw [getElem!_set!_self _ _ _ hlt]
        exact hres.ne_uncomputed

-- =========================================================================
-- Combining quadrant results
-- =========================================================================

theorem combineQuadrants_spec {a : FlatHashLifeArena} (hwf : ArenaWF a) {h : ℕ} {id : UInt32} {m : MacroCell}
    (hn : NodeIs a (h + 2) id m) {q1 q2 q3 q4 r1 r2 r3 r4 : UInt32}
    (n1 : NodeIs a (h + 1) q1 (stepQuadrants m).nw) (n2 : NodeIs a (h + 1) q2 (stepQuadrants m).ne)
    (n3 : NodeIs a (h + 1) q3 (stepQuadrants m).sw) (n4 : NodeIs a (h + 1) q4 (stepQuadrants m).se)
    (m1 : NodeIs a h r1 (hashLifeStep (stepQuadrants m).nw))
    (m2 : NodeIs a h r2 (hashLifeStep (stepQuadrants m).ne))
    (m3 : NodeIs a h r3 (hashLifeStep (stepQuadrants m).sw))
    (m4 : NodeIs a h r4 (hashLifeStep (stepQuadrants m).se)) :
    Grows a (a.combineQuadrants id a.cellLevel[id.toNat]! r1 r2 r3 r4).2 ∧
    ((a.combineQuadrants id a.cellLevel[id.toNat]! r1 r2 r3 r4).2.overflow = 0 →
      (a.combineQuadrants id a.cellLevel[id.toNat]! r1 r2 r3 r4).2.cellStepRes[id.toNat]! ≠ UNCOMPUTED) := by
  unfold FlatHashLifeArena.combineQuadrants
  dsimp only
  have hl : (a.cellLevel[id.toNat]! - 1).toNat = h + 5 := by
    have := u8_sub_one_toNat (h := h + 1) (node_level_toNat hn)
    omega
  rcases e1 : a.internCellNode (a.cellLevel[id.toNat]! - 1) r1 r2 r3 r4 with ⟨res, a1⟩
  have s1 := internCellNode_spec hwf hl m1 m2 m3 m4
  rw [e1] at s1
  obtain ⟨g1, r⟩ := s1
  have w1 := g1.wf
  dsimp only at g1 r w1 ⊢
  split
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
    have hres := r hc.1
    obtain ⟨c1, c2, c3, c4, hm⟩ := hn.children hwf
    have hstep : hashLifeStep m =
        makeCellNode (hashLifeStep (stepQuadrants m).nw) (hashLifeStep (stepQuadrants m).ne)
          (hashLifeStep (stepQuadrants m).sw) (hashLifeStep (stepQuadrants m).se) := by
      rw [hm]
      rw [hm] at n1 n2 n3 n4
      exact hashLifeStep_cell c1.WFd c2.WFd c3.WFd c4.WFd n1.WFd n2.WFd n3.WFd n4.WFd
    rw [← hstep] at hres
    refine ⟨g1.trans (Grows.setCellStepRes w1 (g1.node hwf hn) hres), fun _ => ?_⟩
    have hlt : id.toNat < a1.cellStepRes.size := by
      have := u32_lt_iff.mp hc.2; have := w1.cellCountLe; have := w1.cellSize.2.2.2.2.2.2; omega
    show (a1.cellStepRes.set! id.toNat res)[id.toNat]! ≠ UNCOMPUTED
    rw [getElem!_set!_self _ _ _ hlt]
    exact hres.ne_uncomputed
  · rename_i hc
    refine ⟨g1, fun hov => absurd ?_ hc⟩
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    exact ⟨hov, (g1.node hwf hn).lt_cell⟩

-- =========================================================================
-- The work-stack loop
-- =========================================================================

/--
`b` is a correct successor of `a` for operations that may use `remapL4` as scratch space.
-/
structure LoopOK (a b : FlatHashLifeArena) : Prop where
  wf : ArenaWF b
  ext : Extends a b
  ovf : b.overflow = 0 → a.overflow = 0
  remapCell : b.remapCell = a.remapCell
  masks : b.l4Mask = a.l4Mask ∧ b.cellMask = a.cellMask
  remapL4Size : b.remapL4.size = a.remapL4.size

theorem LoopOK.refl {a : FlatHashLifeArena} (hwf : ArenaWF a) : LoopOK a a :=
  ⟨hwf, Extends.refl a, fun h => h, rfl, ⟨rfl, rfl⟩, rfl⟩

theorem LoopOK.trans {a b c : FlatHashLifeArena} (h1 : LoopOK a b) (h2 : LoopOK b c) : LoopOK a c :=
  ⟨h2.wf, h1.ext.trans h2.ext, fun h => h1.ovf (h2.ovf h), h2.remapCell.trans h1.remapCell,
    ⟨h2.masks.1.trans h1.masks.1, h2.masks.2.trans h1.masks.2⟩, h2.remapL4Size.trans h1.remapL4Size⟩

theorem Grows.loopOK {a b : FlatHashLifeArena} (g : Grows a b) : LoopOK a b :=
  ⟨g.wf, g.ext, g.ovf, g.remapCell, g.masks, by rw [g.remapL4]⟩

theorem LoopOK.setRemapL4 {a : FlatHashLifeArena} (hwf : ArenaWF a) (i v : UInt32) :
    LoopOK a (a.setRemapL4 i v) :=
  ⟨hwf.setRemapL4 i v, Extends.of_same (SameNodes.setRemapL4 a i v), fun h => h, rfl, ⟨rfl, rfl⟩, size_set! _ _ _⟩

theorem LoopOK.setOverflow {a : FlatHashLifeArena} (hwf : ArenaWF a) : LoopOK a a.setOverflow :=
  ⟨hwf.setOverflow, Extends.of_same (SameNodes.setOverflow a), fun h => absurd h (show (1 : UInt8) ≠ 0 by decide),
    rfl, ⟨rfl, rfl⟩, rfl⟩

theorem getCellStepRes_memo {a : FlatHashLifeArena} (hwf : ArenaWF a) {h : ℕ} {q : UInt32} {Q : MacroCell}
    (hq : NodeIs a (h + 1) q Q) (hr : getCellStepRes a q ≠ UNCOMPUTED) :
    NodeIs a h (getCellStepRes a q) (hashLifeStep Q) := by
  unfold getCellStepRes at hr ⊢
  rw [ite_eq_left hq.lt_cell] at hr ⊢
  have hm := hwf.cellMemo q hq.lt_cell hr
  rw [hq.level, show h + 5 - 5 = h by omega, hq.denoteCell_eq] at hm
  exact hm

-- =========================================================================
-- Growth that may rewrite the top of the work stack
-- =========================================================================

/--
`b` grows into `c` as in `Grows`, except that the work-stack slots `remapL4[lo ..]` may change.
-/
structure GrowsAbove (b c : FlatHashLifeArena) (lo : ℕ) : Prop where
  wf : ArenaWF c
  ext : Extends b c
  remapCell : c.remapCell = b.remapCell
  ovf : c.overflow = 0 → b.overflow = 0
  masks : c.l4Mask = b.l4Mask ∧ c.cellMask = b.cellMask
  cap : c.overflow ≠ 0 → b.overflow ≠ 0 ∨ ArenaFull c
  memo : ∀ i, i < b.cellCount.toNat → b.cellStepRes[i]! ≠ UNCOMPUTED → c.cellStepRes[i]! ≠ UNCOMPUTED
  size : c.remapL4.size = b.remapL4.size
  below : ∀ i, i < lo → c.remapL4[i]! = b.remapL4[i]!

theorem Grows.above {b c : FlatHashLifeArena} (g : Grows b c) (lo : ℕ) : GrowsAbove b c lo :=
  ⟨g.wf, g.ext, g.remapCell, g.ovf, g.masks, g.cap, g.memo, by rw [g.remapL4], fun _ _ => by rw [g.remapL4]⟩

theorem GrowsAbove.refl {b : FlatHashLifeArena} (hwf : ArenaWF b) (lo : ℕ) : GrowsAbove b b lo :=
  (Grows.refl hwf).above lo

theorem GrowsAbove.trans {a b c : FlatHashLifeArena} {lo : ℕ} (h1 : GrowsAbove a b lo) (h2 : GrowsAbove b c lo) :
    GrowsAbove a c lo :=
  ⟨h2.wf, h1.ext.trans h2.ext, h2.remapCell.trans h1.remapCell, fun h => h1.ovf (h2.ovf h),
    ⟨h2.masks.1.trans h1.masks.1, h2.masks.2.trans h1.masks.2⟩,
    fun h => (h2.cap h).elim (fun h' => (h1.cap h').elim Or.inl (fun hf => Or.inr (hf.mono h2.ext h2.masks)))
      Or.inr,
    fun i hi hm => h2.memo i (Nat.lt_of_lt_of_le hi h1.ext.cellCount) (h1.memo i hi hm),
    h2.size.trans h1.size, fun i hi => (h2.below i hi).trans (h1.below i hi)⟩

theorem GrowsAbove.mono {b c : FlatHashLifeArena} {lo lo' : ℕ} (g : GrowsAbove b c lo) (h : lo' ≤ lo) :
    GrowsAbove b c lo' :=
  { g with below := fun i hi => g.below i (by omega) }

theorem GrowsAbove.setRemapL4 {b : FlatHashLifeArena} (hwf : ArenaWF b) {lo : ℕ} {i : UInt32} (hi : lo ≤ i.toNat)
    (v : UInt32) : GrowsAbove b (b.setRemapL4 i v) lo :=
  ⟨hwf.setRemapL4 i v, Extends.of_same (SameNodes.setRemapL4 b i v), rfl, fun h => h, ⟨rfl, rfl⟩,
    fun h => Or.inl h, fun _ _ h => h, size_set! _ _ _,
    fun j hj => getElem!_set!_ne _ _ _ _ (by omega)⟩

theorem GrowsAbove.loopOK {b c : FlatHashLifeArena} {lo : ℕ} (g : GrowsAbove b c lo) : LoopOK b c :=
  ⟨g.wf, g.ext, g.ovf, g.remapCell, g.masks, g.size⟩

-- =========================================================================
-- Work-stack frames
-- =========================================================================

theorem stepFrameWidth_toNat : stepFrameWidth.toNat = 5 := rfl

theorem frame_toNat {sp : UInt32} (h : 5 * sp.toNat < 2 ^ 32) : (sp * stepFrameWidth).toNat = 5 * sp.toNat := by
  rw [UInt32.toNat_mul, stepFrameWidth_toNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem frame_pred_toNat {sp : UInt32} (h1 : 1 ≤ sp.toNat) (h : 5 * sp.toNat < 2 ^ 32) :
    ((sp - 1) * stepFrameWidth).toNat = 5 * (sp.toNat - 1) := by
  have e : (sp - 1).toNat = sp.toNat - 1 := u32_toNat_sub (by simpa using h1)
  rw [frame_toNat (by omega), e]

/--
Frame `f` of the step work stack (`stepFrameWidth`), once expanded (its first quadrant slot is not `UNCOMPUTED`),
holds the four quadrants (`stepQuadrants`) of its node, one level down.
-/
def FrameOK (b : FlatHashLifeArena) (f : ℕ) : Prop :=
  b.remapL4[5 * f + 1]! ≠ UNCOMPUTED → ∃ (h : ℕ) (M : MacroCell), NodeIs b (h + 2) b.remapL4[5 * f]! M ∧
    NodeIs b (h + 1) b.remapL4[5 * f + 1]! (stepQuadrants M).nw ∧
    NodeIs b (h + 1) b.remapL4[5 * f + 2]! (stepQuadrants M).ne ∧
    NodeIs b (h + 1) b.remapL4[5 * f + 3]! (stepQuadrants M).sw ∧
    NodeIs b (h + 1) b.remapL4[5 * f + 4]! (stepQuadrants M).se

/-- The first `k` frames of the step work stack are correct. -/
def FramesOK (b : FlatHashLifeArena) (k : ℕ) : Prop := ∀ f, f < k → FrameOK b f

theorem FrameOK.fresh {b : FlatHashLifeArena} {f : ℕ} (h : b.remapL4[5 * f + 1]! = UNCOMPUTED) : FrameOK b f :=
  fun h' => absurd h h'

theorem FrameOK.transfer {b c : FlatHashLifeArena} (hwf : ArenaWF b) {lo f : ℕ} (g : GrowsAbove b c lo)
    (hlo : 5 * f + 5 ≤ lo) (hfr : FrameOK b f) : FrameOK c f := by
  intro hq
  rw [g.below _ (by omega)] at hq
  obtain ⟨h, M, hn, n1, n2, n3, n4⟩ := hfr hq
  refine ⟨h, M, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [g.below _ (by omega)] <;> exact NodeIs.extend hwf g.ext ‹_›

theorem FramesOK.transfer {b c : FlatHashLifeArena} (hwf : ArenaWF b) {lo k : ℕ} (g : GrowsAbove b c lo)
    (hlo : 5 * k ≤ lo) (hfr : FramesOK b k) : FramesOK c k :=
  fun f hf => (hfr f hf).transfer hwf g (by omega)

theorem FramesOK.mono {b : FlatHashLifeArena} {k j : ℕ} (hfr : FramesOK b k) (h : j ≤ k) : FramesOK b j :=
  fun f hf => hfr f (by omega)

theorem FrameOK.get {b : FlatHashLifeArena} {f : ℕ} (hfr : FrameOK b f) (hq : b.remapL4[5 * f + 1]! ≠ UNCOMPUTED)
    {j : ℕ} {M : MacroCell} (hn : NodeIs b (j + 2) b.remapL4[5 * f]! M) :
    NodeIs b (j + 1) b.remapL4[5 * f + 1]! (stepQuadrants M).nw ∧
    NodeIs b (j + 1) b.remapL4[5 * f + 2]! (stepQuadrants M).ne ∧
    NodeIs b (j + 1) b.remapL4[5 * f + 3]! (stepQuadrants M).sw ∧
    NodeIs b (j + 1) b.remapL4[5 * f + 4]! (stepQuadrants M).se := by
  obtain ⟨h, M', hn', n1, n2, n3, n4⟩ := hfr hq
  have hl := hn.level
  rw [hn'.level] at hl
  obtain rfl : h = j := by omega
  obtain rfl : M' = M := hn'.eq.symm.trans hn.eq
  exact ⟨n1, n2, n3, n4⟩

theorem u32_add_small_toNat {b : UInt32} {k : ℕ} (hk : k < 2 ^ 32) (h : b.toNat + k < 2 ^ 32) :
    (b + k.toUInt32).toNat = b.toNat + k :=
  u32_toNat_add (by rw [u32_ofNat_toNat hk]; exact h) |>.trans (by rw [u32_ofNat_toNat hk])

/-- Reading back the four quadrant slots of a frame after writing them. -/
theorem frame_writes (a : FlatHashLifeArena) {b : ℕ} {i1 i2 i3 i4 : UInt32} (h1 : i1.toNat = b + 1)
    (h2 : i2.toNat = b + 2) (h3 : i3.toNat = b + 3) (h4 : i4.toNat = b + 4) (hsz : b + 5 ≤ a.remapL4.size)
    (v1 v2 v3 v4 : UInt32) :
    ((((a.setRemapL4 i1 v1).setRemapL4 i2 v2).setRemapL4 i3 v3).setRemapL4 i4 v4).remapL4[b + 1]! = v1 ∧
    ((((a.setRemapL4 i1 v1).setRemapL4 i2 v2).setRemapL4 i3 v3).setRemapL4 i4 v4).remapL4[b + 2]! = v2 ∧
    ((((a.setRemapL4 i1 v1).setRemapL4 i2 v2).setRemapL4 i3 v3).setRemapL4 i4 v4).remapL4[b + 3]! = v3 ∧
    ((((a.setRemapL4 i1 v1).setRemapL4 i2 v2).setRemapL4 i3 v3).setRemapL4 i4 v4).remapL4[b + 4]! = v4 := by
  simp only [FlatHashLifeArena.setRemapL4]
  rw [h1, h2, h3, h4]
  have s1 : (a.remapL4.set! (b + 1) v1).size = a.remapL4.size := size_set! _ _ _
  have s2 : ((a.remapL4.set! (b + 1) v1).set! (b + 2) v2).size = a.remapL4.size := by rw [size_set!, s1]
  have s3 : (((a.remapL4.set! (b + 1) v1).set! (b + 2) v2).set! (b + 3) v3).size = a.remapL4.size := by
    rw [size_set!, s2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [getElem!_set!_ne _ _ _ _ (by omega), getElem!_set!_ne _ _ _ _ (by omega),
      getElem!_set!_ne _ _ _ _ (by omega), getElem!_set!_self _ _ _ (by omega)]
  · rw [getElem!_set!_ne _ _ _ _ (by omega), getElem!_set!_ne _ _ _ _ (by omega),
      getElem!_set!_self _ _ _ (by rw [s1]; omega)]
  · rw [getElem!_set!_ne _ _ _ _ (by omega), getElem!_set!_self _ _ _ (by rw [s2]; omega)]
  · rw [getElem!_set!_self _ _ _ (by rw [s3]; omega)]

/--
Expanding a frame keeps the invariant, changes only the frame's quadrant slots, and unless the arena fails, stores
the four quadrants of the node there.
-/
theorem expandFrame_spec {a : FlatHashLifeArena} (hwf : ArenaWF a) {h : ℕ} {id : UInt32} {m : MacroCell}
    (hn : NodeIs a (h + 2) id m) {base : UInt32} (hb : base.toNat + 5 ≤ a.remapL4.size)
    (h32 : base.toNat + 5 < 2 ^ 32) :
    GrowsAbove a (a.expandFrame id base) (base.toNat + 1) ∧
    ((a.expandFrame id base).overflow = 0 →
      NodeIs (a.expandFrame id base) (h + 1) (a.expandFrame id base).remapL4[base.toNat + 1]! (stepQuadrants m).nw ∧
      NodeIs (a.expandFrame id base) (h + 1) (a.expandFrame id base).remapL4[base.toNat + 2]! (stepQuadrants m).ne ∧
      NodeIs (a.expandFrame id base) (h + 1) (a.expandFrame id base).remapL4[base.toNat + 3]! (stepQuadrants m).sw ∧
      NodeIs (a.expandFrame id base) (h + 1) (a.expandFrame id base).remapL4[base.toNat + 4]!
        (stepQuadrants m).se) := by
  unfold FlatHashLifeArena.expandFrame
  rcases e1 : a.quadrantNW id with ⟨q1, a1⟩
  dsimp only
  have s1 := quadrantNW_spec hwf hn
  rw [e1] at s1
  obtain ⟨g1, r1⟩ := s1
  have w1 := g1.wf
  rcases e2 : a1.quadrantNE id with ⟨q2, a2⟩
  dsimp only
  have s2 := quadrantNE_spec w1 (g1.node hwf hn)
  rw [e2] at s2
  obtain ⟨g2, r2⟩ := s2
  have w2 := g2.wf
  rcases e3 : a2.quadrantSW id with ⟨q3, a3⟩
  dsimp only
  have s3 := quadrantSW_spec w2 ((g1.trans g2).node hwf hn)
  rw [e3] at s3
  obtain ⟨g3, r3⟩ := s3
  have w3 := g3.wf
  rcases e4 : a3.quadrantSE id with ⟨q4, a4⟩
  dsimp only
  have s4 := quadrantSE_spec w3 (((g1.trans g2).trans g3).node hwf hn)
  rw [e4] at s4
  obtain ⟨g4, r4⟩ := s4
  have w4 := g4.wf
  dsimp only at g1 g2 g3 g4 r1 r2 r3 r4 w1 w2 w3 w4
  have g14 := ((g1.trans g2).trans g3).trans g4
  split
  · rename_i hov
    exact ⟨g14.above _, fun h => absurd h (by simpa using hov)⟩
  · rename_i hov
    have hov4 : a4.overflow = 0 := by simpa using hov
    have hov3 := g4.ovf hov4
    have hov2 := g3.ovf hov3
    have hov1 := g2.ovf hov2
    have n1 := ((g2.trans g3).trans g4).node w1 (r1 hov1)
    have n2 := (g3.trans g4).node w2 (r2 hov2)
    have n3 := g4.node w3 (r3 hov3)
    have n4 := r4 hov4
    have i1 : (base + 1).toNat = base.toNat + 1 := u32_add_small_toNat (k := 1) (by decide) (by omega)
    have i2 : (base + 2).toNat = base.toNat + 2 := u32_add_small_toNat (k := 2) (by decide) (by omega)
    have i3 : (base + 3).toNat = base.toNat + 3 := u32_add_small_toNat (k := 3) (by decide) (by omega)
    have i4 : (base + 4).toNat = base.toNat + 4 := u32_add_small_toNat (k := 4) (by decide) (by omega)
    have k1 := GrowsAbove.setRemapL4 w4 (lo := base.toNat + 1) (i := base + 1) (by omega) q1
    have k2 := GrowsAbove.setRemapL4 k1.wf (lo := base.toNat + 1) (i := base + 2) (by omega) q2
    have k3 := GrowsAbove.setRemapL4 k2.wf (lo := base.toNat + 1) (i := base + 3) (by omega) q3
    have k4 := GrowsAbove.setRemapL4 k3.wf (lo := base.toNat + 1) (i := base + 4) (by omega) q4
    have k14 := ((k1.trans k2).trans k3).trans k4
    have hsz4 : base.toNat + 5 ≤ a4.remapL4.size := by rw [g14.remapL4]; exact hb
    obtain ⟨f1, f2, f3, f4⟩ := frame_writes a4 i1 i2 i3 i4 hsz4 q1 q2 q3 q4
    refine ⟨(g14.above _).trans k14, fun _ => ⟨?_, ?_, ?_, ?_⟩⟩
    · rw [f1]; exact NodeIs.extend w4 k14.ext n1
    · rw [f2]; exact NodeIs.extend w4 k14.ext n2
    · rw [f3]; exact NodeIs.extend w4 k14.ext n3
    · rw [f4]; exact NodeIs.extend w4 k14.ext n4

/--
The top frame `f` of the work stack, expanded if needed (`expandFrameIfNeeded`): only the frame's quadrant slots
change, and unless the arena fails, the frame holds the four quadrants of its node.
-/
theorem topFrame_spec {b : FlatHashLifeArena} (hwf : ArenaWF b) {f : ℕ} {base : UInt32} (hbase : base.toNat = 5 * f)
    (hsz : 5 * f + 5 ≤ b.remapL4.size) (h32 : 5 * f + 5 < 2 ^ 32) (hfr : FrameOK b f) {j : ℕ} {M : MacroCell}
    (hn : NodeIs b (j + 2) b.remapL4[base.toNat]! M) :
    GrowsAbove b (b.expandFrameIfNeeded b.remapL4[base.toNat]! base) (5 * f + 1) ∧
    ((b.expandFrameIfNeeded b.remapL4[base.toNat]! base).overflow = 0 →
      FrameOK (b.expandFrameIfNeeded b.remapL4[base.toNat]! base) f ∧
      NodeIs (b.expandFrameIfNeeded b.remapL4[base.toNat]! base) (j + 1)
        (b.expandFrameIfNeeded b.remapL4[base.toNat]! base).remapL4[5 * f + 1]! (stepQuadrants M).nw ∧
      NodeIs (b.expandFrameIfNeeded b.remapL4[base.toNat]! base) (j + 1)
        (b.expandFrameIfNeeded b.remapL4[base.toNat]! base).remapL4[5 * f + 2]! (stepQuadrants M).ne ∧
      NodeIs (b.expandFrameIfNeeded b.remapL4[base.toNat]! base) (j + 1)
        (b.expandFrameIfNeeded b.remapL4[base.toNat]! base).remapL4[5 * f + 3]! (stepQuadrants M).sw ∧
      NodeIs (b.expandFrameIfNeeded b.remapL4[base.toNat]! base) (j + 1)
        (b.expandFrameIfNeeded b.remapL4[base.toNat]! base).remapL4[5 * f + 4]! (stepQuadrants M).se) := by
  have i1' : (base + 1).toNat = base.toNat + 1 := u32_add_small_toNat (k := 1) (by decide) (by omega)
  have i1 : (base + 1).toNat = 5 * f + 1 := by rw [i1', hbase]
  unfold FlatHashLifeArena.expandFrameIfNeeded
  rw [i1]
  split
  · have e := expandFrame_spec hwf hn (base := base) (by omega) (by omega)
    rw [show base.toNat + 1 = 5 * f + 1 by omega, show base.toNat + 2 = 5 * f + 2 by omega,
      show base.toNat + 3 = 5 * f + 3 by omega, show base.toNat + 4 = 5 * f + 4 by omega] at e
    obtain ⟨g, r⟩ := e
    refine ⟨g, fun hov => ?_⟩
    obtain ⟨n1, n2, n3, n4⟩ := r hov
    refine ⟨fun _ => ⟨j, M, ?_, n1, n2, n3, n4⟩, n1, n2, n3, n4⟩
    rw [g.below _ (by omega), ← hbase]
    exact NodeIs.extend hwf g.ext hn
  · rename_i hq
    have hq' : b.remapL4[5 * f + 1]! ≠ UNCOMPUTED := by simpa using hq
    rw [hbase] at hn
    exact ⟨GrowsAbove.refl hwf _, fun _ => ⟨hfr, hfr.get hq' hn⟩⟩

/--
The work-stack loop keeps the invariant, given a stack of at most `stackLimit` correct frames that fit in `remapL4`.
-/
theorem stepCellSerialLoop_spec (stackLimit : UInt32) (hlim : 5 * stackLimit.toNat < 2 ^ 32) (n : ℕ) :
    ∀ (a : FlatHashLifeArena) (sp fuel : UInt32), fuel.toNat ≤ n → ArenaWF a → sp.toNat ≤ stackLimit.toNat →
      5 * stackLimit.toNat ≤ a.remapL4.size → FramesOK a sp.toNat →
      LoopOK a (a.stepCellSerialLoop sp stackLimit fuel) := by
  induction n with
  | zero =>
    intro a sp fuel hn hwf _ _ _
    have : fuel = 0 := u32_eq_of_toNat (by simp; omega)
    subst this
    rw [FlatHashLifeArena.stepCellSerialLoop.eq_1]
    simp only [dite_true]
    exact LoopOK.refl hwf
  | succ n ih =>
    intro a sp fuel hn hwf hsp hsz hfr
    rw [FlatHashLifeArena.stepCellSerialLoop.eq_1]
    by_cases hf : fuel = 0
    · simp only [hf, dite_true]
      exact LoopOK.refl hwf
    simp only [hf, dite_false]
    have hfuel : (fuel - 1).toNat ≤ n := by
      have := uint32_sub_one_lt fuel hf
      omega
    have ih' := fun a' sp' (hw : ArenaWF a') => ih a' sp' (fuel - 1) hfuel hw
    split
    · exact LoopOK.refl hwf
    · rename_i hcond
      have hsp0 : sp ≠ 0 := fun h => by simp [h] at hcond
      have hsp1 : 1 ≤ sp.toNat := by
        have : sp.toNat ≠ 0 := fun h => hsp0 (u32_eq_of_toNat (by simpa using h))
        omega
      have hpred : (sp - 1).toNat = sp.toNat - 1 := u32_toNat_sub (by simpa using hsp1)
      have hbase := frame_pred_toNat hsp1 (by omega)
      have hfr' : FramesOK a (sp - 1).toNat := hfr.mono (by omega)
      have pop := fun (b : FlatHashLifeArena) (hb : LoopOK a b) (hfb : FramesOK b (sp - 1).toNat) =>
        hb.trans (ih' b (sp - 1) hb.wf (by omega) (by rw [hb.remapL4Size]; exact hsz) hfb)
      have stop := fun (b : FlatHashLifeArena) (hb : LoopOK a b) =>
        hb.trans (ih' b 0 hb.wf (by simp) (by rw [hb.remapL4Size]; exact hsz) (fun _ h => absurd h (by simp)))
      try dsimp only
      split
      · exact pop a (LoopOK.refl hwf) hfr'
      · rename_i hlt
        have hid : a.remapL4[((sp - 1) * stepFrameWidth).toNat]! < a.cellCount := by
          rw [ge_iff_le, u32_le_iff] at hlt
          rw [u32_lt_iff]
          omega
        obtain ⟨k, hk, hnode⟩ := NodeIs.of_lt' hwf hid
        split
        · exact pop a (LoopOK.refl hwf) hfr'
        · split
          · -- level 5
            rename_i hle
            have hk0 : k = 0 := by
              have := u8_le_iff.mp hle
              unfold cellLevelOf at hk
              have h5 : (5 : UInt8).toNat = 5 := rfl
              omega
            subst hk0
            rcases e : a.stepLevel5 a.remapL4[((sp - 1) * stepFrameWidth).toNat]! with ⟨r, a1⟩
            have s := stepLevel5_spec hwf hnode
            rw [e] at s
            exact pop a1 s.1.loopOK (hfr'.transfer hwf (s.1.above (5 * sp.toNat)) (by omega))
          · -- level ≥ 6
            rename_i hle
            obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := by
              have := mt u8_le_iff.mpr hle
              unfold cellLevelOf at hk
              have h5 : (5 : UInt8).toNat = 5 := rfl
              exact ⟨k - 1, by omega⟩
            have T := topFrame_spec hwf hbase (by omega) (by omega) (hfr (sp.toNat - 1) (by omega)) hnode
            generalize a.expandFrameIfNeeded a.remapL4[((sp - 1) * stepFrameWidth).toNat]!
              ((sp - 1) * stepFrameWidth) = a4 at T ⊢
            obtain ⟨g4, r4⟩ := T
            have w4 := g4.wf
            have hfr4 : FramesOK a4 (sp - 1).toNat := hfr'.transfer hwf g4 (by omega)
            split
            · exact stop a4 g4.loopOK
            · rename_i hov
              have hov4 : a4.overflow = 0 := by simpa using hov
              obtain ⟨hf4, n1, n2, n3, n4⟩ := r4 hov4
              have q1' : ((sp - 1) * stepFrameWidth + 1).toNat = ((sp - 1) * stepFrameWidth).toNat + 1 :=
                u32_add_small_toNat (k := 1) (by decide) (by omega)
              have q1 : ((sp - 1) * stepFrameWidth + 1).toNat = 5 * (sp.toNat - 1) + 1 := by rw [q1', hbase]
              have q2' : ((sp - 1) * stepFrameWidth + 2).toNat = ((sp - 1) * stepFrameWidth).toNat + 2 :=
                u32_add_small_toNat (k := 2) (by decide) (by omega)
              have q2 : ((sp - 1) * stepFrameWidth + 2).toNat = 5 * (sp.toNat - 1) + 2 := by rw [q2', hbase]
              have q3' : ((sp - 1) * stepFrameWidth + 3).toNat = ((sp - 1) * stepFrameWidth).toNat + 3 :=
                u32_add_small_toNat (k := 3) (by decide) (by omega)
              have q3 : ((sp - 1) * stepFrameWidth + 3).toNat = 5 * (sp.toNat - 1) + 3 := by rw [q3', hbase]
              have q4' : ((sp - 1) * stepFrameWidth + 4).toNat = ((sp - 1) * stepFrameWidth).toNat + 4 :=
                u32_add_small_toNat (k := 4) (by decide) (by omega)
              have q4 : ((sp - 1) * stepFrameWidth + 4).toNat = 5 * (sp.toNat - 1) + 4 := by rw [q4', hbase]
              simp only [q1, q2, q3, q4]
              split
              · split
                · exact stop a4 g4.loopOK
                · rename_i hroom
                  have hroom' : sp.toNat < stackLimit.toNat := by
                    rw [ge_iff_le, u32_le_iff] at hroom
                    omega
                  have ht := frame_toNat (sp := sp) (by omega)
                  have ht1' : (sp * stepFrameWidth + 1).toNat = (sp * stepFrameWidth).toNat + 1 :=
                    u32_add_small_toNat (k := 1) (by decide) (by omega)
                  have ht1 : (sp * stepFrameWidth + 1).toNat = 5 * sp.toNat + 1 := by rw [ht1', ht]
                  generalize (if getCellStepRes a4 a4.remapL4[5 * (sp.toNat - 1) + 1]! == UNCOMPUTED then
                    a4.remapL4[5 * (sp.toNat - 1) + 1]! else _) = c
                  have k1 := GrowsAbove.setRemapL4 w4 (lo := 5 * sp.toNat) (i := sp * stepFrameWidth) (by omega) c
                  have k2 := GrowsAbove.setRemapL4 k1.wf (lo := 5 * sp.toNat) (i := sp * stepFrameWidth + 1)
                    (by omega) UNCOMPUTED
                  have k12 := k1.trans k2
                  have hsz4 : 5 * stackLimit.toNat ≤ a4.remapL4.size := by rw [g4.size]; exact hsz
                  have hsp' : (sp + 1).toNat = sp.toNat + 1 := u32_toNat_add_one (by omega)
                  refine (g4.loopOK.trans k12.loopOK).trans (ih' _ _ k12.wf (by omega)
                    (by rw [k12.size]; exact hsz4) ?_)
                  rw [hsp']
                  intro f hf
                  by_cases hfe : f = sp.toNat
                  · subst hfe
                    apply FrameOK.fresh
                    show ((a4.remapL4.set! (sp * stepFrameWidth).toNat c).set! (sp * stepFrameWidth + 1).toNat
                      UNCOMPUTED)[5 * sp.toNat + 1]! = UNCOMPUTED
                    rw [ht1, getElem!_set!_self _ _ _ (by rw [size_set!]; omega)]
                  · have hf' : f < sp.toNat := by omega
                    have hfa : FrameOK a4 f := by
                      by_cases hft : f = sp.toNat - 1
                      · subst hft; exact hf4
                      · exact hfr4 f (by omega)
                    exact hfa.transfer w4 k12 (by omega)
              · rename_i hall
                simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hall
                obtain ⟨⟨⟨hr1, hr2⟩, hr3⟩, hr4⟩ := hall
                have m1 := getCellStepRes_memo w4 n1 hr1
                have m2 := getCellStepRes_memo w4 n2 hr2
                have m3 := getCellStepRes_memo w4 n3 hr3
                have m4 := getCellStepRes_memo w4 n4 hr4
                have hlv : a4.cellLevel[(a.remapL4[((sp - 1) * stepFrameWidth).toNat]!).toNat]! =
                    a.cellLevel[(a.remapL4[((sp - 1) * stepFrameWidth).toNat]!).toNat]! :=
                  (g4.ext.cell _ (u32_lt_iff.mp hid)).2.2.2.2
                have gc := combineQuadrants_spec w4 (NodeIs.extend hwf g4.ext hnode) n1 n2 n3 n4 m1 m2 m3 m4
                rw [hlv] at gc
                rcases e5 : a4.combineQuadrants a.remapL4[((sp - 1) * stepFrameWidth).toNat]!
                    a.cellLevel[(a.remapL4[((sp - 1) * stepFrameWidth).toNat]!).toNat]!
                    (getCellStepRes a4 a4.remapL4[5 * (sp.toNat - 1) + 1]!)
                    (getCellStepRes a4 a4.remapL4[5 * (sp.toNat - 1) + 2]!)
                    (getCellStepRes a4 a4.remapL4[5 * (sp.toNat - 1) + 3]!)
                    (getCellStepRes a4 a4.remapL4[5 * (sp.toNat - 1) + 4]!) with ⟨res, a5⟩
                rw [e5] at gc
                exact pop a5 (g4.loopOK.trans gc.1.loopOK) (hfr4.transfer w4 (gc.1.above (5 * sp.toNat)) (by omega))

/--
Flat `stepCellSerial` keeps the invariant and, unless it reports failure, returns a node denoting
`hashLifeStep` of its argument.
-/
theorem stepCellSerial_spec {a : FlatHashLifeArena} (hwf : ArenaWF a) {h : ℕ} {id : UInt32} {m : MacroCell}
    (hn : NodeIs a (h + 1) id m) :
    LoopOK a (a.stepCellSerial id).2 ∧
    ((a.stepCellSerial id).2.overflow = 0 →
      NodeIs (a.stepCellSerial id).2 h (a.stepCellSerial id).1 (hashLifeStep m)) := by
  unfold FlatHashLifeArena.stepCellSerial
  dsimp only
  split
  · exact ⟨LoopOK.setOverflow hwf, fun h => absurd h (show (1 : UInt8) ≠ 0 by decide)⟩
  · rename_i hlim0
    have hlimN : (a.remapL4.size.toUInt32 / stepFrameWidth).toNat = a.remapL4.size % 2 ^ 32 / 5 := by
      rw [UInt32.toNat_div, stepFrameWidth_toNat]
      simp
    have hlim1 : 1 ≤ (a.remapL4.size.toUInt32 / stepFrameWidth).toNat := by
      have : (a.remapL4.size.toUInt32 / stepFrameWidth).toNat ≠ 0 := fun h0 =>
        hlim0 (by simpa using u32_eq_of_toNat (b := 0) (by simpa using h0))
      omega
    have hmod := Nat.mod_le a.remapL4.size (2 ^ 32)
    have hmod' := Nat.mod_lt a.remapL4.size (show 2 ^ 32 > 0 by decide)
    have l0 := (LoopOK.setRemapL4 hwf 0 id).trans (LoopOK.setRemapL4 (hwf.setRemapL4 0 id) 1 UNCOMPUTED)
    have hsz0 : ((a.setRemapL4 0 id).setRemapL4 1 UNCOMPUTED).remapL4.size = a.remapL4.size := by
      simp [FlatHashLifeArena.setRemapL4]
    have hfr0 : FramesOK ((a.setRemapL4 0 id).setRemapL4 1 UNCOMPUTED) (UInt32.toNat 1) := by
      intro f hf
      simp only [UInt32.reduceToNat] at hf
      obtain rfl : f = 0 := by omega
      apply FrameOK.fresh
      show ((a.remapL4.set! (UInt32.toNat 0) id).set! (UInt32.toNat 1) UNCOMPUTED)[5 * 0 + 1]! = UNCOMPUTED
      simp only [UInt32.reduceToNat, Nat.mul_zero, Nat.zero_add]
      rw [getElem!_set!_self _ _ _ (by rw [size_set!]; omega)]
    have l1 := stepCellSerialLoop_spec (a.remapL4.size.toUInt32 / stepFrameWidth) (by omega)
      ((a.cellMask + 1) * 8 + 1024).toNat ((a.setRemapL4 0 id).setRemapL4 1 UNCOMPUTED) 1
      ((a.cellMask + 1) * 8 + 1024) (Nat.le_refl _) l0.wf (by simpa using hlim1) (by rw [hsz0]; omega) hfr0
    have l01 := l0.trans l1
    split
    · exact ⟨l01.trans (LoopOK.setOverflow l1.wf), fun h => absurd h (show (1 : UInt8) ≠ 0 by decide)⟩
    · rename_i hok
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, not_or, Decidable.not_not] at hok
      refine ⟨l01, fun _ => ?_⟩
      have hn1 := NodeIs.extend hwf l01.ext hn
      exact getCellStepRes_memo l01.wf hn1 hok.2

end Algorithm
