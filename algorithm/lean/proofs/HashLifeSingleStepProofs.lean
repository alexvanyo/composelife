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


import Algorithm.Basic
import Algorithm.BitComputation
import Algorithm.MacroCell
import Algorithm.HashLife
import Algorithm.HashLifeEquivalence
import AlgorithmDefs
import proofs.GridEquivalenceProofs
import proofs.SemanticModelProofs
import proofs.HashLifeStepProofs
import proofs.HashLifeConfinementProofs

local notation "ℕ" => Nat
local notation "ℤ" => Int

namespace Algorithm

-- =========================================================================
-- One Generation of HashLife on a Prepared Node
-- =========================================================================

theorem pow_two_ge_four {K : ℕ} (h : 5 ≤ K) : (4 : ℤ) ≤ 2 ^ (K - 3) := by
  have : (2 : ℤ) ^ (K - 3) = 2 ^ (K - 5) * 2 ^ 2 := by
    rw [← Int.pow_add]
    congr 1
    omega
  rw [this]
  have := pow_two_pos (K - 5)
  omega

theorem hashLifeStep_eq_aux {m : MacroCell} {K : ℕ} (hm : WFd m K) :
    hashLifeStep m = hashLifeStepRecursiveAux K m := by
  unfold hashLifeStep hashLifeStepRecursive
  rw [WFd_depth hm]

/--
Stepping a prepared node (well-formed, level `K ≥ 5`, with all alive cells inside its centered
sub-subnode) produces exactly one Conway generation of its cells.
-/
theorem nextGenerationStep_correct (st : HashLifeCellState) {K : ℕ} (hm : WFd st.macroCell K)
    (h5 : 5 ≤ K) (hK : K < 2 ^ 32)
    (hconf : ∀ x y, cellAt st.macroCell x y = true →
      3 * 2 ^ (K - 3) ≤ x ∧ x < 5 * 2 ^ (K - 3) ∧ 3 * 2 ^ (K - 3) ≤ y ∧ y < 5 * 2 ^ (K - 3))
    (L : List Coord)
    (hL : ∀ c, c ∈ L ↔ cellAt st.macroCell (c.1 - st.offset.1) (c.2 - st.offset.2) = true) :
    WFd (hashLifeNextGenerationStep st).macroCell (K - 1) ∧
    ∀ c, c ∈ hashLifeToGrid (hashLifeNextGenerationStep st) ↔ c ∈ stepGrid L := by
  obtain ⟨⟨o1, o2⟩, m⟩ := st
  simp only at hm hconf hL
  obtain ⟨hwR, hR⟩ := hashLifeStepRecursiveAux_spec K hm h5 hK (by omega)
  have hs := hashLifeStep_eq_aux hm
  have hl := WFd_level_toNat hm hK
  obtain ⟨e, hev⟩ : ∃ e, (2 : ℤ) ^ (K - 3) = e := ⟨_, rfl⟩
  have he4 : 4 ≤ e := hev ▸ pow_two_ge_four h5
  have hK2 : (2 : ℤ) ^ (K - 2) = 2 * e := by
    rw [pow_two_pred (K - 2) (by omega), show K - 2 - 1 = K - 3 by omega, hev]
  have hK1 : (2 : ℤ) ^ (K - 1) = 2 * (2 * e) := by
    rw [pow_two_pred (K - 1) (by omega), show K - 1 - 1 = K - 2 by omega, hK2]
  rw [hev] at hconf
  have hstep : hashLifeNextGenerationStep { offset := (o1, o2), macroCell := m } =
      { offset := (o1 + 2 * e, o2 + 2 * e), macroCell := hashLifeStepRecursiveAux K m } := by
    simp only [hashLifeNextGenerationStep, stepOffsetDelta, hl, hK2, hs]
  rw [hstep]
  refine ⟨hwR, fun c => ?_⟩
  simp only [hashLifeToGrid]
  rw [mem_macroCellToGrid_iff hwR (by omega),
    mem_stepGrid_iff_nextGenAt L (fun X Y => cellAt m (X - o1) (Y - o2)) hL]
  have hshift : nextGenAt (fun X Y => cellAt m (X - o1) (Y - o2)) c.1 c.2 =
      nextGenAt (cellAt m) (c.1 - o1) (c.2 - o2) := by
    apply nextGenAt_congr
    intro dx dy _ _ _ _
    coord_congr
  rw [hshift]
  have key : cellAt (hashLifeStepRecursiveAux K m) (c.1 - (o1 + 2 * e)) (c.2 - (o2 + 2 * e)) =
      nextGenAt (cellAt m) (c.1 - o1) (c.2 - o2) := by
    by_cases hin : 0 ≤ c.1 - (o1 + 2 * e) ∧ c.1 - (o1 + 2 * e) < 2 * (2 * e) ∧
        0 ≤ c.2 - (o2 + 2 * e) ∧ c.2 - (o2 + 2 * e) < 2 * (2 * e)
    · obtain ⟨h1, h2, h3, h4⟩ := hin
      rw [hR _ _ h1 (by rw [hK1]; exact h2) h3 (by rw [hK1]; exact h4), hK2]
      apply nextGenAt_congr
      intro dx dy _ _ _ _
      coord_congr
    · have hl : cellAt (hashLifeStepRecursiveAux K m) (c.1 - (o1 + 2 * e)) (c.2 - (o2 + 2 * e)) =
          false := by
        cases hc : cellAt (hashLifeStepRecursiveAux K m) (c.1 - (o1 + 2 * e)) (c.2 - (o2 + 2 * e))
        · rfl
        · have := cellAt_bounds hwR (by omega) hc
          rw [hK1] at this
          exact absurd this hin
      rw [hl]
      symm
      apply nextGenAt_dead_of_isolated
      intro dx dy _ _ _ _
      cases hc : cellAt m (c.1 - o1 + dx) (c.2 - o2 + dy)
      · rfl
      · have := hconf _ _ hc
        exact absurd ⟨by omega, by omega, by omega, by omega⟩ hin
  rw [key]

-- =========================================================================
-- One Generation of HashLife (with Expansion)
-- =========================================================================

/--
One full HashLife generation (expanding first when needed) computes exactly one Conway generation,
and preserves well-formedness.
-/
theorem hashLifeNextGeneration_correct (st : HashLifeCellState)
    (h_wf : isWellFormed st.macroCell) (h_bounds : isInInt32Bounds st) :
    isWellFormed (hashLifeNextGeneration st).macroCell ∧
    ∀ c, c ∈ hashLifeToGrid (hashLifeNextGeneration st) ↔ c ∈ stepGrid (hashLifeToGrid st) := by
  obtain ⟨⟨o1, o2⟩, m⟩ := st
  obtain ⟨_, _, _, _, _, _, _, _, hdepth⟩ := h_bounds
  simp only at h_wf hdepth
  have hm := WFd_of_isWellFormed h_wf
  have hpop : macroCellSize m < 2 ^ 64 := by
    have h1 := macroCellSize_le_pow hm
    have h2 : 4 ^ m.depth ≤ 4 ^ 30 := Nat.pow_le_pow_right (by decide) hdepth
    have h3 : (4 : ℕ) ^ 30 < 2 ^ 64 := by decide
    omega
  generalize hK0 : m.depth = K0 at hm hdepth
  have h4 := WFd_ge_four hm
  have hl := WFd_level_toNat hm (by omega)
  have hgrid : ∀ c, c ∈ hashLifeToGrid { offset := (o1, o2), macroCell := m } ↔
      cellAt m (c.1 - o1) (c.2 - o2) = true := by
    intro c
    exact mem_macroCellToGrid_iff hm (by omega) o1 o2 c
  unfold hashLifeNextGeneration
  split
  · rename_i hne
    obtain ⟨hwE, hcE⟩ := expandCentered_spec hm (by omega)
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
    have hne' : needToExpand m = false := by simpa using hne
    obtain ⟨h5, hconf⟩ := confine_of_not_needToExpand hm (by omega) hpop hne'
    obtain ⟨hw, hc⟩ := nextGenerationStep_correct { offset := (o1, o2), macroCell := m } hm h5
      (by omega) hconf (hashLifeToGrid { offset := (o1, o2), macroCell := m }) hgrid
    exact ⟨isWellFormed_of_WFd hw, hc⟩

end Algorithm
