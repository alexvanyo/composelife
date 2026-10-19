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
import proofs.GridEquivalenceProofs
import proofs.SemanticModelProofs
import proofs.HashLifeStepProofs
import proofs.HashLifeConfinementProofs
import proofs.HashLifeSingleStepProofs
import proofs.FlatArenaBasics
import proofs.FlatArenaIntern
import proofs.FlatArenaStep
import proofs.FlatArenaGeneration

local notation "ℕ" => Nat
local notation "ℤ" => Int

namespace Algorithm

/-!
# Flat HashLife arena: Conway's rule on grids

One generation of the flat engine (`flatNextGeneration`) is exactly one Conway generation of the cells,
and so is every successful `stepOneGeneration` (and `n` of them for `stepOneGenerationN`).
-/

/--
`flatNextGeneration` computes one Conway generation of any well-formed state of depth at most 30.
-/
theorem flatNextGeneration_correct (st : HashLifeCellState)
    (h_wf : isWellFormed st.macroCell) (h_depth : st.macroCell.depth ≤ 30) :
    isWellFormed (flatNextGeneration st).macroCell ∧
    ∀ c, c ∈ hashLifeToGrid (flatNextGeneration st) ↔ c ∈ stepGrid (hashLifeToGrid st) := by
  obtain ⟨⟨o1, o2⟩, m⟩ := st
  simp only at h_wf h_depth
  have hm := WFd_of_isWellFormed h_wf
  have hpop : macroCellSize m < 2 ^ 64 := by
    have h1 := macroCellSize_le_pow hm
    have h2 : 4 ^ m.depth ≤ 4 ^ 30 := Nat.pow_le_pow_right (by decide) h_depth
    have h3 : (4 : ℕ) ^ 30 < 2 ^ 64 := by decide
    omega
  generalize hK0 : m.depth = K0 at hm h_depth
  have h4 := WFd_ge_four hm
  have hl := WFd_level_toNat hm (by omega)
  have hgrid : ∀ c, c ∈ hashLifeToGrid { offset := (o1, o2), macroCell := m } ↔
      cellAt m (c.1 - o1) (c.2 - o2) = true := by
    intro c
    exact mem_macroCellToGrid_iff hm (by omega) o1 o2 c
  unfold flatNextGeneration flatPrepare
  split
  · obtain ⟨hwE, hcE⟩ := expandCentered_spec hm (by omega)
    have hd : (2 : ℤ) ^ (K0 + 2 - 3) = 2 ^ (K0 - 1) := by rw [show K0 + 2 - 3 = K0 - 1 by omega]
    have hp : (2 : ℤ) ^ K0 = 2 * 2 ^ (K0 - 1) := pow_two_pred K0 (by omega)
    obtain ⟨hw, hc⟩ := nextGenerationStep_correct
      { offset := (o1 + expandOffsetDelta m.level.toNat, o2 + expandOffsetDelta m.level.toNat),
        macroCell := expandCentered m } (K := K0 + 2) hwE (by omega) (by omega)
      (by
        intro x y hxy
        simp only at hxy
        rw [hcE] at hxy
        have := cellAt_bounds hm (by omega) hxy
        rw [hd]
        omega)
      (hashLifeToGrid { offset := (o1, o2), macroCell := m })
      (by
        intro c
        rw [hgrid]
        simp only [hcE, expandOffsetDelta, hl]
        constructor <;> intro h <;> refine (fn_congr2 _ ?_ ?_).trans h <;> omega)
    exact ⟨isWellFormed_of_WFd hw, hc⟩
  · rename_i hne
    have hne' : needToExpand m = false := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hne
      simpa using hne.2
    obtain ⟨h5, hconf⟩ := confine_of_not_needToExpand hm (by omega) hpop hne'
    obtain ⟨hw, hc⟩ := nextGenerationStep_correct { offset := (o1, o2), macroCell := m } hm h5
      (by omega) hconf (hashLifeToGrid { offset := (o1, o2), macroCell := m }) hgrid
    exact ⟨isWellFormed_of_WFd hw, hc⟩

theorem flatState_isWellFormed {a : FlatHashLifeArena} (hwf : ArenaWF a) {root : UInt32}
    (hid : root < a.cellCount) (ox oy : Int32) : isWellFormed (flatState a ox oy root).macroCell := by
  obtain ⟨k, _, hn⟩ := NodeIs.of_lt' hwf hid
  show isWellFormed (denoteCell a root)
  rw [hn.denoteCell_eq]
  exact isWellFormed_of_WFd hn.WFd

theorem flatPrepare_level_ge {st : HashLifeCellState} {K : ℕ} (hm : WFd st.macroCell K) (hK : K + 2 < 2 ^ 32) :
    K ≤ (flatPrepare st).macroCell.level.toNat := by
  unfold flatPrepare
  split
  · rw [WFd_level_toNat (expandCentered_spec hm hK).1 (by omega)]
    omega
  · rw [WFd_level_toNat hm (by omega)]
    omega

theorem flatStepInRange_depth {a : FlatHashLifeArena} (hwf : ArenaWF a) {root : UInt32}
    (hid : root < a.cellCount) {ox oy : Int32} (hr : flatStepInRange (flatState a ox oy root)) :
    (flatState a ox oy root).macroCell.depth ≤ 30 := by
  obtain ⟨k, hk, hn⟩ := NodeIs.of_lt' hwf hid
  have hk256 : k + 5 < 256 := by
    have := u8_toNat_lt (a.cellLevel[root.toNat]!)
    unfold cellLevelOf at hk
    omega
  have hW : WFd (flatState a ox oy root).macroCell (k + 1 + 4) := hn.WFd
  rw [WFd_depth hW]
  have := flatPrepare_level_ge hW (by omega)
  have hl := hr.1
  omega

/--
Every successful `stepOneGeneration` computes exactly one Conway generation of the cells.
-/
theorem stepOneGeneration_grid {a : FlatHashLifeArena} (hwf : ArenaWF a) (ox oy : Int32) (root : UInt32)
    (hok : (a.stepOneGeneration ox oy root).1.2.2 ≠ UNCOMPUTED) :
    cellsEqual
      (hashLifeToGrid (flatState (a.stepOneGeneration ox oy root).2 (a.stepOneGeneration ox oy root).1.1
        (a.stepOneGeneration ox oy root).1.2.1 (a.stepOneGeneration ox oy root).1.2.2))
      (stepGrid (hashLifeToGrid (flatState a ox oy root))) = true := by
  obtain ⟨_, hs, _⟩ := stepOneGeneration_spec hwf ox oy root
  obtain ⟨_, hid, _, heq, hrange⟩ := hs hok
  rw [heq]
  apply cellsEqual_of_same_elements
  exact (flatNextGeneration_correct _ (flatState_isWellFormed hwf hid ox oy)
    (flatStepInRange_depth hwf hid hrange)).2

/--
`n` successful generations of `stepOneGeneration` compute exactly `flatStepN n` and `n` Conway generations.
-/
theorem stepOneGenerationN_spec (n : ℕ) :
    ∀ {a : FlatHashLifeArena} (_ : ArenaWF a) (ox oy : Int32) (root : UInt32), root < a.cellCount →
      ArenaWF (a.stepOneGenerationN n ox oy root).2 ∧
      ((a.stepOneGenerationN n ox oy root).1.2.2 ≠ UNCOMPUTED →
        (a.stepOneGenerationN n ox oy root).1.2.2 < (a.stepOneGenerationN n ox oy root).2.cellCount ∧
        flatState (a.stepOneGenerationN n ox oy root).2 (a.stepOneGenerationN n ox oy root).1.1
          (a.stepOneGenerationN n ox oy root).1.2.1 (a.stepOneGenerationN n ox oy root).1.2.2 =
          flatStepN n (flatState a ox oy root) ∧
        cellsEqual
          (hashLifeToGrid (flatState (a.stepOneGenerationN n ox oy root).2 (a.stepOneGenerationN n ox oy root).1.1
            (a.stepOneGenerationN n ox oy root).1.2.1 (a.stepOneGenerationN n ox oy root).1.2.2))
          (stepN n (hashLifeToGrid (flatState a ox oy root))) = true) := by
  induction n with
  | zero =>
    intro a hwf ox oy root hid
    refine ⟨hwf, fun _ => ⟨hid, rfl, ?_⟩⟩
    exact cellsEqual_deduplicate_self _
  | succ n ih =>
    intro a hwf ox oy root hid
    have hstep := stepOneGeneration_spec hwf ox oy root
    have hgrid := stepOneGeneration_grid hwf ox oy root
    unfold FlatHashLifeArena.stepOneGenerationN
    rcases e : a.stepOneGeneration ox oy root with ⟨⟨ox1, oy1, id1⟩, a1⟩
    rw [e] at hstep hgrid
    obtain ⟨l1, hs1, _⟩ := hstep
    dsimp only
    split
    · rename_i hu
      exact ⟨l1.wf, fun h => absurd rfl h⟩
    · rename_i hu
      have hne : id1 ≠ UNCOMPUTED := by simpa using hu
      obtain ⟨_, _, hid1, heq1, _⟩ := hs1 hne
      have hg1 := hgrid hne
      obtain ⟨hw, hrest⟩ := ih l1.wf ox1 oy1 id1 hid1
      refine ⟨hw, fun hok => ?_⟩
      obtain ⟨hlt, heq, hg⟩ := hrest hok
      refine ⟨hlt, ?_, ?_⟩
      · rw [heq]
        dsimp only at heq1
        rw [heq1]
        rfl
      · exact cellsEqual_trans (cellsEqual_trans hg (stepN_cellsEqual_stepN n hg1))
          (stepN_stepGrid_cellsEqual n _)

end Algorithm
