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

import proofs.FlatHashLifeProofs
import proofs.MacroCellEngineProofs

/-!
# Flat engine: success conditions and the Kotlin generation loop

Each generation of the flat engine keeps the window center fixed and grows the depth by at most one, so
`n` generations stay representable whenever the input does (`d + n ≤ 29`, center within `2 ^ 30`): the engine
then fails only by running out of capacity. `FlatRun` models the generation loop of
`FlatLeanHashLifeAlgorithm`, which interleaves steps with retries, failure-flag clears and compactions, and every
state it reaches denotes the right generation.
-/

local notation "ℕ" => Nat
local notation "ℤ" => Int

namespace Algorithm

/--
One generation of the flat engine from a well-formed state of depth `L ≤ 30`: either it expands (to depth `L + 2`),
steps, and moves the corner by `-2 ^ (L - 1)` to depth `L + 1`, or it steps the node itself (of depth `L ≥ 6`) and
moves the corner by `2 ^ (L - 2)` to depth `L - 1`.
-/
theorem flatNextGeneration_shape (st : HashLifeCellState) (hwf : isWellFormed st.macroCell)
    (hd : st.macroCell.depth ≤ 30) :
    ((st.macroCell.level ≤ 5 || needToExpand st.macroCell) = true →
      (flatPrepare st).macroCell.level.toNat = st.macroCell.depth + 2 ∧
      (flatNextGeneration st).offset =
        (st.offset.1 - 2 ^ (st.macroCell.depth - 1), st.offset.2 - 2 ^ (st.macroCell.depth - 1)) ∧
      WFd (flatNextGeneration st).macroCell (st.macroCell.depth + 1)) ∧
    ((st.macroCell.level ≤ 5 || needToExpand st.macroCell) = false →
      6 ≤ st.macroCell.depth ∧
      (flatPrepare st).macroCell.level.toNat = st.macroCell.depth ∧
      (flatNextGeneration st).offset =
        (st.offset.1 + 2 ^ (st.macroCell.depth - 2), st.offset.2 + 2 ^ (st.macroCell.depth - 2)) ∧
      WFd (flatNextGeneration st).macroCell (st.macroCell.depth - 1)) := by
  obtain ⟨⟨o1, o2⟩, m⟩ := st
  simp only at hwf hd ⊢
  have hm := WFd_of_isWellFormed hwf
  generalize hL : m.depth = L at hm hd
  have h4 := WFd_ge_four hm
  have hl := WFd_level_toNat hm (by omega)
  have hp : (2 : ℤ) ^ L = 2 * 2 ^ (L - 1) := pow_two_pred L (by omega)
  refine ⟨fun hne => ?_, fun hne => ?_⟩
  · obtain ⟨hwE, _⟩ := expandCentered_spec hm (by omega)
    have hlE := WFd_level_toNat hwE (by omega)
    have hw := depth_hashLifeStep hwE (by omega) (by omega)
    simp only [flatNextGeneration, flatPrepare, hne, ↓reduceIte, hashLifeNextGenerationStep, hl, hlE,
      expandOffsetDelta, stepOffsetDelta, show L + 2 - 2 = L by omega]
    refine ⟨trivial, ?_, by rw [show L + 1 = L + 2 - 1 by omega]; exact hw⟩
    simp only [Prod.mk.injEq]
    constructor <;> omega
  · have hpop : macroCellSize m < 2 ^ 64 := by
      have h1 := macroCellSize_le_pow hm
      have h2 : 4 ^ L ≤ 4 ^ 30 := Nat.pow_le_pow_right (by decide) hd
      have h3 : (4 : ℕ) ^ 30 < 2 ^ 64 := by decide
      omega
    rw [Bool.or_eq_false_iff] at hne
    obtain ⟨hlev5, hne⟩ := hne
    have h6 : 6 ≤ L := by
      have : ¬ m.level ≤ 5 := by simpa using hlev5
      rw [UInt32.le_iff_toNat_le, hl] at this
      simp at this
      omega
    obtain ⟨h5, _⟩ := confine_of_not_needToExpand hm (by omega) hpop hne
    have hw := depth_hashLifeStep hm h5 (by omega)
    simp only [flatNextGeneration, flatPrepare, hlev5, hne, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
      hashLifeNextGenerationStep, hl, stepOffsetDelta]
    exact ⟨h6, trivial, trivial, hw⟩

/-- Every generation of the flat engine keeps the center of the window fixed and grows the depth by at most one. -/
theorem flatNextGeneration_center (st : HashLifeCellState) (hwf : isWellFormed st.macroCell)
    (hd : st.macroCell.depth ≤ 30) :
    windowCenter (flatNextGeneration st) = windowCenter st ∧
    isWellFormed (flatNextGeneration st).macroCell ∧
    (flatNextGeneration st).macroCell.depth ≤ st.macroCell.depth + 1 := by
  obtain ⟨hexp, hstep⟩ := flatNextGeneration_shape st hwf hd
  have h4 := WFd_ge_four (WFd_of_isWellFormed hwf)
  unfold windowCenter
  cases hne : (st.macroCell.level ≤ 5 || needToExpand st.macroCell)
  · obtain ⟨h6, _, ho, hw⟩ := hstep hne
    refine ⟨?_, isWellFormed_of_WFd hw, by rw [WFd_depth hw]; omega⟩
    rw [ho, WFd_depth hw]
    have : (2 : ℤ) ^ (st.macroCell.depth - 1) = 2 * 2 ^ (st.macroCell.depth - 1 - 1) :=
      pow_two_pred _ (by omega)
    simp only [Prod.mk.injEq, show st.macroCell.depth - 1 - 1 = st.macroCell.depth - 2 by omega] at this ⊢
    constructor <;> omega
  · obtain ⟨_, ho, hw⟩ := hexp hne
    refine ⟨?_, isWellFormed_of_WFd hw, by rw [WFd_depth hw]; omega⟩
    rw [ho, WFd_depth hw]
    have : (2 : ℤ) ^ (st.macroCell.depth + 1 - 1) = 2 * 2 ^ (st.macroCell.depth - 1) := by
      rw [show st.macroCell.depth + 1 - 1 = st.macroCell.depth by omega]
      exact pow_two_pred _ (by omega)
    simp only [Prod.mk.injEq]
    constructor <;> omega

/-- A state of depth at most 28 whose window center lies within `2 ^ 30` of the origin has a representable next generation. -/
theorem flatStepInRange_of_center (st : HashLifeCellState) (hwf : isWellFormed st.macroCell)
    (hd : st.macroCell.depth ≤ 28)
    (hcx : -2 ^ 30 ≤ (windowCenter st).1 ∧ (windowCenter st).1 ≤ 2 ^ 30)
    (hcy : -2 ^ 30 ≤ (windowCenter st).2 ∧ (windowCenter st).2 ≤ 2 ^ 30) :
    flatStepInRange st := by
  obtain ⟨hc, hw', hd'⟩ := flatNextGeneration_center st hwf (by omega)
  obtain ⟨hexp, hstep⟩ := flatNextGeneration_shape st hwf (by omega)
  have h4 := WFd_ge_four (WFd_of_isWellFormed hwf)
  have hcx' := hcx; have hcy' := hcy
  rw [← hc] at hcx' hcy'
  unfold windowCenter at hcx' hcy'
  have hpos := pow_two_pos ((flatNextGeneration st).macroCell.depth - 1)
  have hle : (2 : ℤ) ^ ((flatNextGeneration st).macroCell.depth - 1) ≤ 2 ^ 28 := pow_two_mono (by omega)
  have h28 : (2 : ℤ) ^ 28 = 268435456 := by decide
  have h30 : (2 : ℤ) ^ 30 = 1073741824 := by decide
  refine ⟨?_, by omega, by omega, by omega, by omega⟩
  cases hne : (st.macroCell.level ≤ 5 || needToExpand st.macroCell)
  · rw [(hstep hne).2.1]; omega
  · rw [(hexp hne).1]; omega


theorem nodesPreserved_trans {a b c : FlatHashLifeArena} (h1 : NodesPreserved a b) (h2 : NodesPreserved b c) :
    NodesPreserved a c :=
  fun h id m hn => h2 h id m (h1 h id m hn)

/--
`n` steps of the flat engine keep every node of the arena, and fail only by running out of capacity: they succeed
whenever the input root's depth `d` satisfies `d + n ≤ 29`, its window center lies within `2 ^ 30` of the origin,
and the arena does not report a failure.
-/
theorem stepOneGenerationN_live (n : ℕ) :
    ∀ {a : FlatHashLifeArena} (_ : ArenaWF a) (ox oy : Int32) (root : UInt32), root < a.cellCount →
      NodesPreserved a (a.stepOneGenerationN n ox oy root).2 ∧
      ((flatState a ox oy root).macroCell.depth + n ≤ 29 →
        (-2 ^ 30 ≤ (windowCenter (flatState a ox oy root)).1 ∧ (windowCenter (flatState a ox oy root)).1 ≤ 2 ^ 30) →
        (-2 ^ 30 ≤ (windowCenter (flatState a ox oy root)).2 ∧ (windowCenter (flatState a ox oy root)).2 ≤ 2 ^ 30) →
        (a.stepOneGenerationN n ox oy root).2.overflow = 0 → (a.stepOneGenerationN n ox oy root).1.2.2 ≠ UNCOMPUTED) := by
  induction n with
  | zero =>
    intro a hwf ox oy root hid
    refine ⟨fun _ _ _ hn => hn, fun _ _ _ _ => ?_⟩
    show root ≠ UNCOMPUTED
    intro h
    subst h
    have := u32_lt_iff.mp hid
    have := a.cellCount.toNat_lt
    simp [UNCOMPUTED] at *
    omega
  | succ n ih =>
    intro a hwf ox oy root hid
    have hstep := stepOneGeneration_spec hwf ox oy root
    have hwfs := flatState_isWellFormed hwf hid ox oy
    unfold FlatHashLifeArena.stepOneGenerationN
    rcases e : a.stepOneGeneration ox oy root with ⟨⟨ox1, oy1, id1⟩, a1⟩
    rw [e] at hstep
    obtain ⟨l1, hs1, hlive⟩ := hstep
    have hp1 : NodesPreserved a a1 := NodesPreserved.of_extends hwf l1.ext
    dsimp only
    split
    · rename_i hu
      have hu' : id1 = UNCOMPUTED := by simpa using hu
      refine ⟨hp1, fun hd hcx hcy hov => ?_⟩
      exact absurd hu' (hlive hid (flatStepInRange_of_center _ hwfs (by omega) hcx hcy) hov)
    · rename_i hu
      have hne : id1 ≠ UNCOMPUTED := by simpa using hu
      obtain ⟨_, _, hid1, heq1, _⟩ := hs1 hne
      obtain ⟨hp2, hl2⟩ := ih l1.wf ox1 oy1 id1 hid1
      refine ⟨nodesPreserved_trans hp1 hp2, fun hd hcx hcy hov => ?_⟩
      obtain ⟨hc, _, hd'⟩ := flatNextGeneration_center (flatState a ox oy root) hwfs (by omega)
      dsimp only at heq1
      rw [heq1] at hl2
      exact hl2 (by omega) (by rw [hc]; exact hcx) (by rw [hc]; exact hcy) hov


theorem flatStepN_succ' (k : ℕ) : ∀ st, flatStepN (k + 1) st = flatNextGeneration (flatStepN k st) := by
  induction k with
  | zero => intro st; rfl
  | succ k ih => intro st; show flatStepN (k + 1) (flatNextGeneration st) = _; rw [ih]; rfl

/-- A root of a well-formed arena still denotes the same state in any arena that keeps its nodes. -/
theorem flatState_of_preserved {a b : FlatHashLifeArena} (hwf : ArenaWF a) (hp : NodesPreserved a b) {root : UInt32}
    (hid : root < a.cellCount) (ox oy : Int32) :
    root < b.cellCount ∧ flatState b ox oy root = flatState a ox oy root := by
  obtain ⟨k, _, hn⟩ := NodeIs.of_lt' hwf hid
  have hn' := hp _ _ _ hn
  refine ⟨hn'.lt_cell, ?_⟩
  unfold flatState
  rw [hn'.denoteCell_eq]

/--
Every state reachable by the generation loop of `FlatLeanHashLifeAlgorithm` after `k` successful generations is
a well-formed arena whose root denotes exactly `k` generations of the flat engine from the start, and whose cells
are exactly `k` Conway generations of the starting cells.
-/
theorem flatRun_correct {st0 : HashLifeCellState} {k : ℕ} {a : FlatHashLifeArena} {ox oy : Int32} {root : UInt32}
    (h : FlatRun st0 k a ox oy root) :
    ArenaWF a ∧ root < a.cellCount ∧ flatState a ox oy root = flatStepN k st0 ∧
      cellsEqual (hashLifeToGrid (flatState a ox oy root)) (stepN k (hashLifeToGrid st0)) = true := by
  induction h with
  | start hwf hid heq =>
    subst heq
    exact ⟨hwf, hid, rfl, cellsEqual_deduplicate_self _⟩
  | step _ hs ih =>
    obtain ⟨hwf, hid, heq, hcells⟩ := ih
    obtain ⟨hwf', _, hsucc, _⟩ := flat_stepOneGeneration_Impl hwf _ _ _
    obtain ⟨_, hid', heq', hgrid⟩ := hsucc hs
    refine ⟨hwf', hid', by rw [heq', heq, flatStepN_succ'], ?_⟩
    exact cellsEqual_trans hgrid (stepGrid_cellsEqual_stepGrid hcells)
  | failedStep _ _ ih =>
    obtain ⟨hwf, hid, heq, hcells⟩ := ih
    obtain ⟨hwf', hp, _⟩ := flat_stepOneGeneration_Impl hwf _ _ _
    obtain ⟨hid', hst⟩ := flatState_of_preserved hwf hp hid _ _
    exact ⟨hwf', hid', by rw [hst, heq], by rw [hst]; exact hcells⟩
  | clearOverflow _ ih =>
    obtain ⟨hwf, hid, heq, hcells⟩ := ih
    obtain ⟨hid', hst⟩ := flatState_of_preserved hwf
      (NodesPreserved.of_extends hwf (Extends.of_same (SameNodes.clearOverflow _))) hid _ _
    exact ⟨hwf.clearOverflow, hid', hst.trans heq, hst ▸ hcells⟩
  | compact _ hdst hs ih =>
    obtain ⟨hwf, hid, heq, hcells⟩ := ih
    obtain ⟨hwf', _, _, _, hsucc, _⟩ := flat_compactRootFrom_Impl hwf hdst _
    obtain ⟨_, _, hid', _, _, hst⟩ := hsucc hs
    exact ⟨hwf', hid', by rw [hst, heq], by rw [hst]; exact hcells⟩

end Algorithm
