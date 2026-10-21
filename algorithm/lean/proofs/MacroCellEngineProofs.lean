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
import AlgorithmDefs
import proofs.SemanticModelProofs
import proofs.HashLifeStepProofs
import proofs.HashLifeConfinementProofs
import proofs.HashLifeSingleStepProofs
import proofs.HashLifeEquivalenceProofs
import proofs.PopcountProofs

/-!
# The MacroCell engine as called from Kotlin

`LeanHashLifeAlgorithm.kt` does not call `hashLifeStep`: it calls the compiled callback-based functions
(`stepHashLifeStateWith`, `stepCellNodeWith`, `canonicalizeMacroCellWith`, `computeGenerationStep`), passing
memoizing Kotlin lambdas, and the generated code replaces some functions by faster ones (`kotlin_expr`). This
file proves that these functions compute HashLife exactly, for any callbacks that return the values their
memo tables are keyed on.
-/

local notation "ℕ" => Nat
local notation "ℤ" => Int

namespace Algorithm

theorem centeredSubSubnodeFast_eq {m : MacroCell} {d : ℕ} (hm : WFd m d) (h5 : 5 ≤ d) :
    centeredSubSubnodeFast m = centeredSubSubnode m := by
  obtain ⟨h, A, B, C, D, rfl, hA, hB, hC, hD⟩ := WFd_cell hm h5
  by_cases h5' : d = 5
  · subst h5'
    obtain ⟨_, a1, a2, a3, a4, rfl⟩ := WFd_level4 hA
    obtain ⟨_, b1, b2, b3, b4, rfl⟩ := WFd_level4 hB
    obtain ⟨_, c1, c2, c3, c4, rfl⟩ := WFd_level4 hC
    obtain ⟨_, d1, d2, d3, d4, rfl⟩ := WFd_level4 hD
    rfl
  obtain ⟨_, A1, A2, A3, A4, rfl, hA1, hA2, hA3, hA4⟩ := WFd_cell hA (by omega)
  obtain ⟨_, B1, B2, B3, B4, rfl, hB1, hB2, hB3, hB4⟩ := WFd_cell hB (by omega)
  obtain ⟨_, C1, C2, C3, C4, rfl, hC1, hC2, hC3, hC4⟩ := WFd_cell hC (by omega)
  obtain ⟨_, D1, D2, D3, D4, rfl, hD1, hD2, hD3, hD4⟩ := WFd_cell hD (by omega)
  by_cases h6 : d = 6
  · subst h6
    obtain ⟨_, a1, a2, a3, a4, rfl⟩ := WFd_level4 hA4
    obtain ⟨_, b1, b2, b3, b4, rfl⟩ := WFd_level4 hB3
    obtain ⟨_, c1, c2, c3, c4, rfl⟩ := WFd_level4 hC2
    obtain ⟨_, d1, d2, d3, d4, rfl⟩ := WFd_level4 hD1
    rfl
  obtain ⟨_, _, _, _, _, rfl, _⟩ := WFd_cell hA4 (by omega)
  obtain ⟨_, _, _, _, _, rfl, _⟩ := WFd_cell hB3 (by omega)
  obtain ⟨_, _, _, _, _, rfl, _⟩ := WFd_cell hC2 (by omega)
  obtain ⟨_, _, _, _, _, rfl, _⟩ := WFd_cell hD1 (by omega)
  rfl

theorem popcount64_sum4_toUInt64 (a b c d : UInt64) :
    (popcount64 a + popcount64 b + popcount64 c + popcount64 d).toUInt64 =
      (popcount64 a).toUInt64 + (popcount64 b).toUInt64 + (popcount64 c).toUInt64 + (popcount64 d).toUInt64 := by
  have := popcount64_toNat_le a; have := popcount64_toNat_le b
  have := popcount64_toNat_le c; have := popcount64_toNat_le d
  apply UInt64.toNat_inj.mp
  simp only [UInt32.toNat_toUInt64, UInt32.toNat_add, UInt64.toNat_add]
  omega

theorem centeredSubSubnodeSizeFast_eq {m : MacroCell} {d : ℕ} (hm : WFd m d) (h5 : 5 ≤ d) :
    centeredSubSubnodeSizeFast m = centeredSubSubnodeSize m := by
  obtain ⟨h, A, B, C, D, rfl, hA, hB, hC, hD⟩ := WFd_cell hm h5
  by_cases h5' : d = 5
  · subst h5'
    obtain ⟨_, a1, a2, a3, a4, rfl⟩ := WFd_level4 hA
    obtain ⟨_, b1, b2, b3, b4, rfl⟩ := WFd_level4 hB
    obtain ⟨_, c1, c2, c3, c4, rfl⟩ := WFd_level4 hC
    obtain ⟨_, d1, d2, d3, d4, rfl⟩ := WFd_level4 hD
    show _ = MacroCell.size (makeLevel4Node 0 0 0 _)
    simp [MacroCell.size, makeLevel4Node, show popcount64 0 = 0 from rfl, centeredSubSubnodeSizeFast]
  obtain ⟨_, A1, A2, A3, A4, rfl, hA1, hA2, hA3, hA4⟩ := WFd_cell hA (by omega)
  obtain ⟨_, B1, B2, B3, B4, rfl, hB1, hB2, hB3, hB4⟩ := WFd_cell hB (by omega)
  obtain ⟨_, C1, C2, C3, C4, rfl, hC1, hC2, hC3, hC4⟩ := WFd_cell hC (by omega)
  obtain ⟨_, D1, D2, D3, D4, rfl, hD1, hD2, hD3, hD4⟩ := WFd_cell hD (by omega)
  by_cases h6 : d = 6
  · subst h6
    obtain ⟨_, a1, a2, a3, a4, rfl⟩ := WFd_level4 hA4
    obtain ⟨_, b1, b2, b3, b4, rfl⟩ := WFd_level4 hB3
    obtain ⟨_, c1, c2, c3, c4, rfl⟩ := WFd_level4 hC2
    obtain ⟨_, d1, d2, d3, d4, rfl⟩ := WFd_level4 hD1
    exact popcount64_sum4_toUInt64 _ _ _ _
  obtain ⟨_, _, _, _, _, rfl, _⟩ := WFd_cell hA4 (by omega)
  obtain ⟨_, _, _, _, _, rfl, _⟩ := WFd_cell hB3 (by omega)
  obtain ⟨_, _, _, _, _, rfl, _⟩ := WFd_cell hC2 (by omega)
  obtain ⟨_, _, _, _, _, rfl, _⟩ := WFd_cell hD1 (by omega)
  rfl

/-- The four overlapping quadrants of a CellNode of depth `d ≥ 6` are nodes of depth `d - 1`. -/
theorem stepQuadrants_WFd {m : MacroCell} {d : ℕ} (hm : WFd m d) (h6 : 6 ≤ d) (hd : d < 2 ^ 32) :
    WFd (stepQuadrants m).nw (d - 1) ∧ WFd (stepQuadrants m).ne (d - 1) ∧
    WFd (stepQuadrants m).sw (d - 1) ∧ WFd (stepQuadrants m).se (d - 1) := by
  obtain ⟨h, A, B, C, D, rfl, hA, hB, hC, hD⟩ := WFd_cell hm (by omega)
  obtain ⟨_, A1, A2, A3, A4, rfl, hA1, hA2, hA3, hA4⟩ := WFd_cell hA (by omega)
  obtain ⟨_, B1, B2, B3, B4, rfl, hB1, hB2, hB3, hB4⟩ := WFd_cell hB (by omega)
  obtain ⟨_, C1, C2, C3, C4, rfl, hC1, hC2, hC3, hC4⟩ := WFd_cell hC (by omega)
  obtain ⟨_, D1, D2, D3, D4, rfl, hD1, hD2, hD3, hD4⟩ := WFd_cell hD (by omega)
  have w00 := (centeredSubnode_spec hA (by omega) (by omega)).1
  have w02 := (centeredSubnode_spec hB (by omega) (by omega)).1
  have w20 := (centeredSubnode_spec hC (by omega) (by omega)).1
  have w22 := (centeredSubnode_spec hD (by omega) (by omega)).1
  have w01 := (chs_spec hA hB (by omega) (by omega) rfl).1
  have w21 := (chs_spec hC hD (by omega) (by omega) rfl).1
  have w10 := (cvs_spec hA hC (by omega) (by omega) rfl).1
  have w12 := (cvs_spec hB hD (by omega) (by omega) rfl).1
  have wm := (centeredSubnode_spec hm (by omega) (by omega)).1
  have w11 := (centeredSubnode_spec wm (by omega) (by omega)).1
  have e : d - 1 - 1 = d - 1 - 1 - 1 + 1 := by omega
  rw [e] at w00 w02 w20 w22 w01 w21 w10 w12
  rw [show d - 1 - 1 = d - 1 - 1 - 1 + 1 by omega] at w11
  have k : d - 1 = d - 1 - 1 - 1 + 1 + 1 := by omega
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [k] <;> exact WFd_makeCellNode (by assumption) (by assumption) (by assumption) (by assumption)

/-- Stepping with `stepCellNodeWith` and the exact HashLife callbacks is HashLife stepping. -/
theorem stepCellNodeWith_exact {m : MacroCell} {d : ℕ} (hm : WFd m d) (h5 : 5 ≤ d) (hd : d < 2 ^ 32) :
    stepCellNodeWith m stepLevel4Node hashLifeStep = hashLifeStep m := by
  rw [hashLifeStep_eq_aux hm]
  by_cases h5' : d = 5
  · subst h5'
    obtain ⟨h, A, B, C, D, rfl, hA, hB, hC, hD⟩ := WFd_cell hm (by omega)
    obtain ⟨_, a1, a2, a3, a4, rfl⟩ := WFd_level4 hA
    obtain ⟨_, b1, b2, b3, b4, rfl⟩ := WFd_level4 hB
    obtain ⟨_, c1, c2, c3, c4, rfl⟩ := WFd_level4 hC
    obtain ⟨_, d1, d2, d3, d4, rfl⟩ := WFd_level4 hD
    rfl
  obtain ⟨q1, q2, q3, q4⟩ := stepQuadrants_WFd hm (by omega) hd
  obtain ⟨h, A, B, C, D, rfl, hA, hB, hC, hD⟩ := WFd_cell hm (by omega)
  obtain ⟨_, A1, A2, A3, A4, rfl, _⟩ := WFd_cell hA (by omega)
  obtain ⟨_, B1, B2, B3, B4, rfl, _⟩ := WFd_cell hB (by omega)
  obtain ⟨_, C1, C2, C3, C4, rfl, _⟩ := WFd_cell hC (by omega)
  obtain ⟨_, D1, D2, D3, D4, rfl, _⟩ := WFd_cell hD (by omega)
  rw [show d = d - 1 + 1 by omega]
  simp only [stepQuadrants] at q1 q2 q3 q4
  simp only [stepCellNodeWith, hashLifeStepRecursiveAux, stepQuadrants, hashLifeStep_eq_aux q1, hashLifeStep_eq_aux q2,
    hashLifeStep_eq_aux q3, hashLifeStep_eq_aux q4]

-- =========================================================================
-- Hash Consistency
-- =========================================================================

theorem HashOK_makeLevel4Node (nw ne sw se : UInt64) : HashOK (makeLevel4Node nw ne sw se) := rfl

theorem HashOK_makeCellNode {nw ne sw se : MacroCell} (h1 : HashOK nw) (h2 : HashOK ne) (h3 : HashOK sw)
    (h4 : HashOK se) : HashOK (makeCellNode nw ne sw se) :=
  ⟨rfl, h1, h2, h3, h4⟩

theorem HashOK_emptySubnode : ∀ m, HashOK (emptySubnode m)
  | .level4Node .. => rfl
  | .cellNode _ nw _ _ _ => HashOK_makeCellNode (HashOK_emptySubnode nw) (HashOK_emptySubnode nw)
      (HashOK_emptySubnode nw) (HashOK_emptySubnode nw)

theorem cellNode_eq_make {h : UInt32} {nw ne sw se : MacroCell} (H : HashOK (.cellNode h nw ne sw se)) :
    MacroCell.cellNode h nw ne sw se = makeCellNode nw ne sw se := by
  rw [H.1]; rfl

theorem HashOK_hashLifeStepRecursiveAux : ∀ (fuel : ℕ) (m : MacroCell), HashOK (hashLifeStepRecursiveAux fuel m)
  | 0, _ => rfl
  | fuel + 1, m => by
    unfold hashLifeStepRecursiveAux
    split
    · rfl
    · rfl
    · exact HashOK_makeCellNode (HashOK_hashLifeStepRecursiveAux fuel _) (HashOK_hashLifeStepRecursiveAux fuel _)
        (HashOK_hashLifeStepRecursiveAux fuel _) (HashOK_hashLifeStepRecursiveAux fuel _)

theorem HashOK_hashLifeStep (m : MacroCell) : HashOK (hashLifeStep m) :=
  HashOK_hashLifeStepRecursiveAux _ _

theorem HashOK_centeredSubnode {n : MacroCell} {L : ℕ} (hn : WFd n L) (h5 : 5 ≤ L) (H : HashOK n) :
    HashOK (centeredSubnode n) := by
  obtain ⟨h, A, B, C, D, rfl, hA, hB, hC, hD⟩ := WFd_cell hn h5
  obtain ⟨_, HA, HB, HC, HD⟩ := H
  by_cases h5' : L = 5
  · subst h5'
    obtain ⟨_, _, _, _, _, rfl⟩ := WFd_level4 hA
    obtain ⟨_, _, _, _, _, rfl⟩ := WFd_level4 hB
    obtain ⟨_, _, _, _, _, rfl⟩ := WFd_level4 hC
    obtain ⟨_, _, _, _, _, rfl⟩ := WFd_level4 hD
    rfl
  obtain ⟨_, _, _, _, _, rfl, _⟩ := WFd_cell hA (by omega)
  obtain ⟨_, _, _, _, _, rfl, _⟩ := WFd_cell hB (by omega)
  obtain ⟨_, _, _, _, _, rfl, _⟩ := WFd_cell hC (by omega)
  obtain ⟨_, _, _, _, _, rfl, _⟩ := WFd_cell hD (by omega)
  exact HashOK_makeCellNode HA.2.2.2.2 HB.2.2.2.1 HC.2.2.1 HD.2.1

theorem HashOK_centeredHorizontalSubnode {W E : MacroCell} {L : ℕ} (hW : WFd W L) (hE : WFd E L) (h5 : 5 ≤ L)
    (HW : HashOK W) (HE : HashOK E) : HashOK (centeredHorizontalSubnode W E) := by
  obtain ⟨_, A, B, C, D, rfl, hA, hB, hC, hD⟩ := WFd_cell hW h5
  obtain ⟨_, A', B', C', D', rfl, hA', hB', hC', hD'⟩ := WFd_cell hE h5
  obtain ⟨_, _, HB, _, HD⟩ := HW
  obtain ⟨_, HA', _, HC', _⟩ := HE
  by_cases h5' : L = 5
  · subst h5'
    obtain ⟨_, _, _, _, _, rfl⟩ := WFd_level4 hB
    obtain ⟨_, _, _, _, _, rfl⟩ := WFd_level4 hD
    obtain ⟨_, _, _, _, _, rfl⟩ := WFd_level4 hA'
    obtain ⟨_, _, _, _, _, rfl⟩ := WFd_level4 hC'
    rfl
  obtain ⟨_, _, _, _, _, rfl, _⟩ := WFd_cell hB (by omega)
  obtain ⟨_, _, _, _, _, rfl, _⟩ := WFd_cell hD (by omega)
  obtain ⟨_, _, _, _, _, rfl, _⟩ := WFd_cell hA' (by omega)
  obtain ⟨_, _, _, _, _, rfl, _⟩ := WFd_cell hC' (by omega)
  exact HashOK_makeCellNode HB.2.2.2.2 HA'.2.2.2.1 HD.2.2.1 HC'.2.1

theorem HashOK_centeredVerticalSubnode {N S : MacroCell} {L : ℕ} (hN : WFd N L) (hS : WFd S L) (h5 : 5 ≤ L)
    (HN : HashOK N) (HS : HashOK S) : HashOK (centeredVerticalSubnode N S) := by
  obtain ⟨_, A, B, C, D, rfl, hA, hB, hC, hD⟩ := WFd_cell hN h5
  obtain ⟨_, A', B', C', D', rfl, hA', hB', hC', hD'⟩ := WFd_cell hS h5
  obtain ⟨_, _, _, HC, HD⟩ := HN
  obtain ⟨_, HA', HB', _, _⟩ := HS
  by_cases h5' : L = 5
  · subst h5'
    obtain ⟨_, _, _, _, _, rfl⟩ := WFd_level4 hC
    obtain ⟨_, _, _, _, _, rfl⟩ := WFd_level4 hD
    obtain ⟨_, _, _, _, _, rfl⟩ := WFd_level4 hA'
    obtain ⟨_, _, _, _, _, rfl⟩ := WFd_level4 hB'
    rfl
  obtain ⟨_, _, _, _, _, rfl, _⟩ := WFd_cell hC (by omega)
  obtain ⟨_, _, _, _, _, rfl, _⟩ := WFd_cell hD (by omega)
  obtain ⟨_, _, _, _, _, rfl, _⟩ := WFd_cell hA' (by omega)
  obtain ⟨_, _, _, _, _, rfl, _⟩ := WFd_cell hB' (by omega)
  exact HashOK_makeCellNode HC.2.2.2.2 HD.2.2.2.1 HA'.2.2.1 HB'.2.1

theorem HashOK_stepQuadrants {m : MacroCell} {d : ℕ} (hm : WFd m d) (h6 : 6 ≤ d) (hd : d < 2 ^ 32) (H : HashOK m) :
    HashOK (stepQuadrants m).nw ∧ HashOK (stepQuadrants m).ne ∧
    HashOK (stepQuadrants m).sw ∧ HashOK (stepQuadrants m).se := by
  have hc := HashOK_centeredSubnode hm (by omega) H
  have wc := (centeredSubnode_spec hm (by omega) hd).1
  have h11 := HashOK_centeredSubnode wc (by omega) hc
  obtain ⟨h, A, B, C, D, rfl, hA, hB, hC, hD⟩ := WFd_cell hm (by omega)
  obtain ⟨_, HA, HB, HC, HD⟩ := H
  have h00 := HashOK_centeredSubnode hA (by omega) HA
  have h02 := HashOK_centeredSubnode hB (by omega) HB
  have h20 := HashOK_centeredSubnode hC (by omega) HC
  have h22 := HashOK_centeredSubnode hD (by omega) HD
  have h01 := HashOK_centeredHorizontalSubnode hA hB (by omega) HA HB
  have h21 := HashOK_centeredHorizontalSubnode hC hD (by omega) HC HD
  have h10 := HashOK_centeredVerticalSubnode hA hC (by omega) HA HC
  have h12 := HashOK_centeredVerticalSubnode hB hD (by omega) HB HD
  obtain ⟨_, _, _, _, _, rfl, _⟩ := WFd_cell hA (by omega)
  obtain ⟨_, _, _, _, _, rfl, _⟩ := WFd_cell hB (by omega)
  obtain ⟨_, _, _, _, _, rfl, _⟩ := WFd_cell hC (by omega)
  obtain ⟨_, _, _, _, _, rfl, _⟩ := WFd_cell hD (by omega)
  exact ⟨HashOK_makeCellNode h00 h01 h10 h11, HashOK_makeCellNode h01 h02 h11 h12,
    HashOK_makeCellNode h10 h11 h20 h21, HashOK_makeCellNode h11 h12 h21 h22⟩

theorem HashOK_expandCentered {m : MacroCell} (H : HashOK m) : HashOK (expandCentered m) := by
  cases m with
  | level4Node =>
    have l := HashOK_makeLevel4Node
    exact HashOK_makeCellNode (HashOK_makeCellNode (l _ _ _ _) (l _ _ _ _) (l _ _ _ _) (l _ _ _ _))
      (HashOK_makeCellNode (l _ _ _ _) (l _ _ _ _) (l _ _ _ _) (l _ _ _ _))
      (HashOK_makeCellNode (l _ _ _ _) (l _ _ _ _) (l _ _ _ _) (l _ _ _ _))
      (HashOK_makeCellNode (l _ _ _ _) (l _ _ _ _) (l _ _ _ _) (l _ _ _ _))
  | cellNode h nw ne sw se =>
    obtain ⟨_, H1, H2, H3, H4⟩ := H
    have e := HashOK_emptySubnode nw
    have e1 := HashOK_makeCellNode e e e e
    exact HashOK_makeCellNode (HashOK_makeCellNode e1 e1 e1 (HashOK_makeCellNode e e e H1))
      (HashOK_makeCellNode e1 e1 (HashOK_makeCellNode e e H2 e) e1)
      (HashOK_makeCellNode e1 (HashOK_makeCellNode e H3 e e) e1 e1)
      (HashOK_makeCellNode (HashOK_makeCellNode H4 e e e) e1 e1 e1)

/-- A hash-consistent well-formed node with no live cells is the empty node of its depth. -/
theorem eq_emptyNode_of_size_zero : ∀ {m : MacroCell} {d : ℕ}, WFd m d → HashOK m → macroCellSize m = 0 →
    m = emptyNode d
  | .level4Node h nw ne sw se, d, hm, H, hs => by
    rw [WFd_level4Node_iff] at hm
    subst hm
    rw [macroCellSize_level4Node] at hs
    have z : ∀ l : UInt64, (popcount64 l).toNat = 0 → l = 0 := fun l hl =>
      (popcount64_eq_zero_iff l).mp (UInt32.toNat_inj.mp (by simpa using hl))
    rw [z nw (by omega), z ne (by omega), z sw (by omega), z se (by omega)] at H ⊢
    rw [H]
    rfl
  | .cellNode h nw ne sw se, d, hm, H, hs => by
    obtain ⟨h5, h1, h2, h3, h4⟩ := hm
    obtain ⟨Hh, H1, H2, H3, H4⟩ := H
    rw [macroCellSize_cellNode] at hs
    have e1 := eq_emptyNode_of_size_zero h1 H1 (by omega)
    have e2 := eq_emptyNode_of_size_zero h2 H2 (by omega)
    have e3 := eq_emptyNode_of_size_zero h3 H3 (by omega)
    have e4 := eq_emptyNode_of_size_zero h4 H4 (by omega)
    subst e1 e2 e3 e4
    rw [Hh]
    obtain ⟨k, rfl⟩ : ∃ k, d = k + 5 := ⟨d - 5, by omega⟩
    rfl

-- =========================================================================
-- Canonicalization
-- =========================================================================

/--
`canonicalizeMacroCellWith` returns its argument, for callbacks that do. This holds for the callbacks of
`LeanHashLifeAlgorithm`: its canonical maps return values equal to their keys (a Level 4 node is equal to its
key, and a CellNode has the same level and identical children, so by hash consistency the same value), and the
subnode canonicalization is the same recursion.
-/
theorem canonicalize_fixpoint (internLevel4 : MacroCell → MacroCell) (findExistingCell : MacroCell → Option MacroCell)
    (canonicalizeSubnode internCell : MacroCell → MacroCell)
    (hI4 : ∀ q, internLevel4 q = q)
    (hFe : ∀ q e, HashOK q → findExistingCell q = some e → e = q)
    (hIc : ∀ q, HashOK q → internCell q = q)
    (hS : ∀ q d, WFd q d → d ≤ 30 → HashOK q →
      canonicalizeSubnode q = canonicalizeMacroCellWith q internLevel4 findExistingCell canonicalizeSubnode internCell) :
    ∀ (d : ℕ) (q : MacroCell), WFd q d → d ≤ 30 → HashOK q →
      canonicalizeMacroCellWith q internLevel4 findExistingCell canonicalizeSubnode internCell = q := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro q hq hd H
    cases q with
    | level4Node => exact hI4 _
    | cellNode h nw ne sw se =>
      obtain ⟨h5, h1, h2, h3, h4⟩ := hq
      have hrec : ∀ c, WFd c (d - 1) → HashOK c → canonicalizeSubnode c = c := fun c hc Hc => by
        rw [hS c (d - 1) hc (by omega) Hc]
        exact ih (d - 1) (by omega) c hc (by omega) Hc
      obtain ⟨Hh, H1, H2, H3, H4⟩ := H
      cases hfe : findExistingCell (.cellNode h nw ne sw se) with
      | some e =>
        simp only [canonicalizeMacroCellWith, hfe]
        exact hFe _ _ ⟨Hh, H1, H2, H3, H4⟩ hfe
      | none =>
        simp only [canonicalizeMacroCellWith, hfe]
        by_cases hz : (MacroCell.cellNode h nw ne sw se).size = 0
        · have hz' : macroCellSize (.cellNode h nw ne sw se) = 0 := by
            have hs := size_toNat (.cellNode h nw ne sw se)
            have hle := macroCellSize_le_pow (m := .cellNode h nw ne sw se) ⟨h5, h1, h2, h3, h4⟩
            have : (4 : ℕ) ^ d ≤ 4 ^ 30 := Nat.pow_le_pow_right (by decide) hd
            have : (4 : ℕ) ^ 30 < 2 ^ 64 := by decide
            rw [hz] at hs
            simp at hs
            omega
          have hall := eq_emptyNode_of_size_zero (m := .cellNode h nw ne sw se) ⟨h5, h1, h2, h3, h4⟩
            ⟨Hh, H1, H2, H3, H4⟩ hz'
          rw [macroCellSize_cellNode] at hz'
          have e1 := eq_emptyNode_of_size_zero h1 H1 (by omega)
          simp only [hz, BEq.rfl, ↓reduceIte]
          rw [hrec nw h1 H1, hIc _ (HashOK_makeCellNode H1 H1 H1 H1), hall, e1]
          obtain ⟨k, rfl⟩ : ∃ k, d = k + 5 := ⟨d - 5, by omega⟩
          rfl
        · simp only [beq_iff_eq, hz, ↓reduceIte]
          rw [hrec nw h1 H1, hrec ne h2 H2, hrec sw h3 H3, hrec se h4 H4,
            hIc _ (HashOK_makeCellNode H1 H2 H3 H4)]
          exact (cellNode_eq_make ⟨Hh, H1, H2, H3, H4⟩).symm

-- =========================================================================
-- Stepping
-- =========================================================================

/--
`stepCellNodeWith` with callbacks that agree with HashLife on the four quadrants (the Level 4 step on depth 4
quadrants, the HashLife step on deeper ones) is HashLife's step.
-/
theorem stepCellNodeWith_spec {m : MacroCell} {d : ℕ} (G : MacroCell → UInt64) (F : MacroCell → MacroCell)
    (hm : WFd m d) (h5 : 5 ≤ d) (hd : d < 2 ^ 32) (H : HashOK m)
    (hG : ∀ q, WFd q 4 → G q = stepLevel4Node q)
    (hF : 6 ≤ d → ∀ q, WFd q (d - 1) → HashOK q → F q = hashLifeStep q) :
    stepCellNodeWith m G F = hashLifeStep m := by
  rw [← stepCellNodeWith_exact hm h5 hd]
  by_cases h5' : d = 5
  · subst h5'
    obtain ⟨h, A, B, C, D, rfl, hA, hB, hC, hD⟩ := WFd_cell hm (by omega)
    obtain ⟨_, _, _, _, _, rfl⟩ := WFd_level4 hA
    obtain ⟨_, _, _, _, _, rfl⟩ := WFd_level4 hB
    obtain ⟨_, _, _, _, _, rfl⟩ := WFd_level4 hC
    obtain ⟨_, _, _, _, _, rfl⟩ := WFd_level4 hD
    simp only [stepCellNodeWith, hG _ (WFd_makeLevel4Node _ _ _ _)]
  obtain ⟨q1, q2, q3, q4⟩ := stepQuadrants_WFd hm (by omega) hd
  obtain ⟨k1, k2, k3, k4⟩ := HashOK_stepQuadrants hm (by omega) hd H
  obtain ⟨h, A, B, C, D, rfl, hA, hB, hC, hD⟩ := WFd_cell hm (by omega)
  obtain ⟨_, _, _, _, _, rfl, _⟩ := WFd_cell hA (by omega)
  obtain ⟨_, _, _, _, _, rfl, _⟩ := WFd_cell hB (by omega)
  obtain ⟨_, _, _, _, _, rfl, _⟩ := WFd_cell hC (by omega)
  obtain ⟨_, _, _, _, _, rfl, _⟩ := WFd_cell hD (by omega)
  simp only [stepQuadrants] at q1 q2 q3 q4 k1 k2 k3 k4
  simp only [stepCellNodeWith, hF (by omega) _ q1 k1, hF (by omega) _ q2 k2, hF (by omega) _ q3 k3,
    hF (by omega) _ q4 k4]

/--
The memoized recursion of `LeanHashLifeAlgorithm` computes HashLife's step: any `F` that steps a node by
`stepCellNodeWith` with itself as the recursive callback, and a Level 4 callback `G` that computes the Level 4
step, is HashLife's step on every hash-consistent well-formed node of depth 5 to 30.
-/
theorem stepCellNodeWith_fixpoint (G : MacroCell → UInt64) (F : MacroCell → MacroCell)
    (hG : ∀ q, WFd q 4 → G q = stepLevel4Node q)
    (hF : ∀ q d, WFd q d → 5 ≤ d → d ≤ 30 → HashOK q → F q = stepCellNodeWith q G F) :
    ∀ (d : ℕ) (q : MacroCell), WFd q d → 5 ≤ d → d ≤ 30 → HashOK q → F q = hashLifeStep q := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro q hq h5 hd H
    rw [hF q d hq h5 hd H]
    exact stepCellNodeWith_spec G F hq h5 (by omega) H hG
      (fun h6 c hc Hc => ih (d - 1) (by omega) c hc (by omega) (by omega) Hc)

-- =========================================================================
-- Int32 Offsets and Iteration
-- =========================================================================

theorem int32_toInt_add_of_range (a b : Int32) (h1 : -2 ^ 31 ≤ a.toInt + b.toInt) (h2 : a.toInt + b.toInt < 2 ^ 31) :
    (a + b).toInt = a.toInt + b.toInt := by
  rw [Int32.toInt_add, Int.bmod_eq_emod]
  split <;> omega

/-- The offset deltas `prepareStep` computes in `Int32`, for every depth the engine is used at. -/
theorem prepare_deltas : ∀ L : ℕ, L < 29 → 4 ≤ L →
    (expandOffsetDeltaUInt L.toUInt32 + stepOffsetDeltaUInt (L + 2).toUInt32).toInt = -(2 ^ (L - 1)) ∧
    (5 ≤ L → (stepOffsetDeltaUInt L.toUInt32).toInt = 2 ^ (L - 2)) := by
  decide +kernel

theorem level_eq_of_WFd {m : MacroCell} {d : ℕ} (hm : WFd m d) (hd : d < 2 ^ 32) : m.level = d.toUInt32 := by
  apply UInt32.toNat_inj.mp
  rw [WFd_level_toNat hm hd, UInt32.toNat_ofNat']
  omega

theorem depth_hashLifeStep {m : MacroCell} {K : ℕ} (hm : WFd m K) (h5 : 5 ≤ K) (hK : K < 2 ^ 32) :
    WFd (hashLifeStep m) (K - 1) := by
  rw [hashLifeStep_eq_aux hm]
  exact (hashLifeStepRecursiveAux_spec K hm h5 hK (by omega)).1

/--
One HashLife generation of a well-formed state of depth `L ≤ 30`: either it expands, steps the expanded node and
moves the corner by `-2 ^ (L - 1)` to depth `L + 1`, or it steps the node itself and moves the corner by
`2 ^ (L - 2)` to depth `L - 1`.
-/
theorem hashLifeNextGeneration_shape (st : HashLifeCellState) (hwf : isWellFormed st.macroCell)
    (hd : st.macroCell.depth ≤ 30) :
    (needToExpand st.macroCell = true →
      (hashLifeNextGeneration st).macroCell = hashLifeStep (expandCentered st.macroCell) ∧
      (hashLifeNextGeneration st).offset =
        (st.offset.1 - 2 ^ (st.macroCell.depth - 1), st.offset.2 - 2 ^ (st.macroCell.depth - 1)) ∧
      WFd (hashLifeNextGeneration st).macroCell (st.macroCell.depth + 1)) ∧
    (needToExpand st.macroCell = false →
      5 ≤ st.macroCell.depth ∧
      (hashLifeNextGeneration st).macroCell = hashLifeStep st.macroCell ∧
      (hashLifeNextGeneration st).offset =
        (st.offset.1 + 2 ^ (st.macroCell.depth - 2), st.offset.2 + 2 ^ (st.macroCell.depth - 2)) ∧
      WFd (hashLifeNextGeneration st).macroCell (st.macroCell.depth - 1)) := by
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
    simp only [hashLifeNextGeneration, hne, ↓reduceIte, hashLifeNextGenerationStep, hl, hlE, expandOffsetDelta,
      stepOffsetDelta, show L + 2 - 2 = L by omega]
    refine ⟨trivial, ?_, hw⟩
    simp only [Prod.mk.injEq]
    constructor <;> omega
  · have hpop : macroCellSize m < 2 ^ 64 := by
      have h1 := macroCellSize_le_pow hm
      have h2 : 4 ^ L ≤ 4 ^ 30 := Nat.pow_le_pow_right (by decide) hd
      have h3 : (4 : ℕ) ^ 30 < 2 ^ 64 := by decide
      omega
    obtain ⟨h5, _⟩ := confine_of_not_needToExpand hm (by omega) hpop hne
    have hw := depth_hashLifeStep hm h5 (by omega)
    simp only [hashLifeNextGeneration, hne, Bool.false_eq_true, ↓reduceIte, hashLifeNextGenerationStep, hl,
      stepOffsetDelta]
    exact ⟨h5, trivial, trivial, hw⟩

/-- Every HashLife generation keeps the center of the window fixed. -/
theorem windowCenter_hashLifeNextGeneration (st : HashLifeCellState) (hwf : isWellFormed st.macroCell)
    (hd : st.macroCell.depth ≤ 30) :
    windowCenter (hashLifeNextGeneration st) = windowCenter st := by
  obtain ⟨hexp, hstep⟩ := hashLifeNextGeneration_shape st hwf hd
  have h4 := WFd_ge_four (WFd_of_isWellFormed hwf)
  unfold windowCenter
  cases hne : needToExpand st.macroCell
  · obtain ⟨h5, _, ho, hw⟩ := hstep hne
    rw [ho, WFd_depth hw]
    have : (2 : ℤ) ^ (st.macroCell.depth - 1) = 2 * 2 ^ (st.macroCell.depth - 1 - 1) :=
      pow_two_pred _ (by omega)
    simp only [Prod.mk.injEq, show st.macroCell.depth - 1 - 1 = st.macroCell.depth - 2 by omega] at this ⊢
    constructor <;> omega
  · obtain ⟨_, ho, hw⟩ := hexp hne
    rw [ho, WFd_depth hw]
    have : (2 : ℤ) ^ (st.macroCell.depth + 1 - 1) = 2 * 2 ^ (st.macroCell.depth - 1) := by
      rw [show st.macroCell.depth + 1 - 1 = st.macroCell.depth by omega]
      exact pow_two_pred _ (by omega)
    simp only [Prod.mk.injEq]
    constructor <;> omega

theorem pow_two_le_pow_two_30 : ∀ k < 31, (2 : ℤ) ^ k ≤ 2 ^ 30 := by decide +kernel

theorem pow_two_mono {j k : ℕ} (h : j ≤ k) : (2 : ℤ) ^ j ≤ 2 ^ k := by
  have : (2 : ℤ) ^ k = 2 ^ j * 2 ^ (k - j) := by rw [← Int.pow_add]; congr 1; omega
  rw [this]
  have := pow_two_pos (k - j)
  have := pow_two_pos j
  have : (1 : ℤ) ≤ 2 ^ (k - j) := by omega
  calc (2 : ℤ) ^ j = 2 ^ j * 1 := by omega
    _ ≤ 2 ^ j * 2 ^ (k - j) := Int.mul_le_mul_of_nonneg_left this (by omega)

/--
One step of `LeanHashLifeAlgorithm`: `stepHashLifeStateWith` with a prepared-node step `P` that is HashLife's
step computes exactly one HashLife generation, `Int32` offsets included, for any hash-consistent well-formed
state of depth at most 28 whose window center lies within `2 ^ 30` of the origin.
-/
theorem stepHashLifeStateWith_correct (st : HashLifeStepState) (P : MacroCell → MacroCell)
    (hP : ∀ q d, WFd q d → 5 ≤ d → d ≤ 30 → HashOK q → P q = hashLifeStep q)
    (hwf : isWellFormed st.macroCell) (hok : HashOK st.macroCell) (hd : st.macroCell.depth ≤ 28)
    (hcx : -2 ^ 30 ≤ (windowCenter st.toCellState).1 ∧ (windowCenter st.toCellState).1 ≤ 2 ^ 30)
    (hcy : -2 ^ 30 ≤ (windowCenter st.toCellState).2 ∧ (windowCenter st.toCellState).2 ≤ 2 ^ 30) :
    (stepHashLifeStateWith st P).toCellState = hashLifeNextGeneration st.toCellState := by
  obtain ⟨hexp, hstep⟩ := hashLifeNextGeneration_shape st.toCellState hwf (by simp [HashLifeStepState.toCellState]; omega)
  obtain ⟨ox, oy, m⟩ := st
  simp only [HashLifeStepState.toCellState, windowCenter] at hexp hstep hcx hcy hwf hok hd ⊢
  have hm := WFd_of_isWellFormed hwf
  generalize hL : m.depth = L at hm hd hexp hstep hcx hcy
  have h4 := WFd_ge_four hm
  have hlev := level_eq_of_WFd hm (by omega)
  have hpL := pow_two_le_pow_two_30 (L - 1) (by omega)
  have hp1 : (2 : ℤ) ^ L = 2 * 2 ^ (L - 1) := pow_two_pred L (by omega)
  have hpos := pow_two_pos (L - 1)
  have hpL1 : (2 : ℤ) ^ (L - 1) ≤ 2 ^ 27 := pow_two_mono (by omega)
  have h27 : (2 : ℤ) ^ 27 = 134217728 := by decide
  have h30 : (2 : ℤ) ^ 30 = 1073741824 := by decide
  unfold stepHashLifeStateWith prepareStep
  cases hne : needToExpand m
  · obtain ⟨h5, hmc, ho, _⟩ := hstep hne
    have hp2 : (2 : ℤ) ^ (L - 1) = 2 * 2 ^ (L - 2) := by
      rw [show L - 1 = L - 2 + 1 by omega]; exact pow_two_pred _ (by omega)
    have hdl := (prepare_deltas L (by omega) h4).2 h5
    simp only [Bool.false_eq_true, ↓reduceIte, hlev]
    rw [hP m L hm h5 (by omega) hok]
    generalize hashLifeNextGeneration { offset := (ox.toInt, oy.toInt), macroCell := m } = N at hmc ho ⊢
    obtain ⟨⟨n1, n2⟩, nc⟩ := N
    simp only [Prod.mk.injEq] at hmc ho
    obtain ⟨rfl, rfl⟩ := ho
    subst hmc
    simp only [HashLifeCellState.mk.injEq, Prod.mk.injEq, and_true]
    constructor
    · rw [int32_toInt_add_of_range _ _ (by omega) (by omega), hdl]
    · rw [int32_toInt_add_of_range _ _ (by omega) (by omega), hdl]
  · obtain ⟨hmc, ho, _⟩ := hexp hne
    obtain ⟨hwE, _⟩ := expandCentered_spec hm (by omega)
    have hlevE := level_eq_of_WFd hwE (by omega)
    have hdl := (prepare_deltas L (by omega) h4).1
    simp only [↓reduceIte, hlev, hlevE]
    rw [hP _ (L + 2) hwE (by omega) (by omega) (HashOK_expandCentered hok)]
    generalize hashLifeNextGeneration { offset := (ox.toInt, oy.toInt), macroCell := m } = N at hmc ho ⊢
    obtain ⟨⟨n1, n2⟩, nc⟩ := N
    simp only [Prod.mk.injEq] at hmc ho
    obtain ⟨rfl, rfl⟩ := ho
    subst hmc
    simp only [HashLifeCellState.mk.injEq, Prod.mk.injEq, and_true]
    constructor
    · rw [int32_toInt_add_of_range _ _ (by omega) (by omega), hdl]; omega
    · rw [int32_toInt_add_of_range _ _ (by omega) (by omega), hdl]; omega

theorem stepNGenerationsWith_ne_zero (f : HashLifeStepState → HashLifeStepState) (n : UInt32) (st : HashLifeStepState)
    (hn : n ≠ 0) : stepNGenerationsWith n st f = stepNGenerationsWith (n - 1) (f st) f := by
  rw [stepNGenerationsWith]
  simp [hn]

theorem toNat_sub_one_of_ne_zero {n : UInt32} (hn : n ≠ 0) : (n - 1).toNat = n.toNat - 1 := by
  have h1 : (1 : UInt32) ≤ n := by
    rw [UInt32.le_iff_toNat_le]
    have : n.toNat ≠ 0 := fun h => hn (UInt32.toNat_inj.mp (by simpa using h))
    simp; omega
  rw [UInt32.toNat_sub_of_le n 1 h1]
  rfl

/--
`n` steps of `stepNGenerationsWith` over `stepHashLifeStateWith` compute `n` HashLife generations (`Int32`
offsets included), for a hash-consistent well-formed state of depth `d` with `d + n ≤ 29` whose window center
lies within `2 ^ 30` of the origin.
-/
theorem stepNGenerationsWith_stepHashLifeStateWith (P : MacroCell → MacroCell)
    (hP : ∀ q d, WFd q d → 5 ≤ d → d ≤ 30 → HashOK q → P q = hashLifeStep q) :
    ∀ (k : ℕ) (n : UInt32) (st : HashLifeStepState), n.toNat = k → isWellFormed st.macroCell → HashOK st.macroCell →
      st.macroCell.depth + k ≤ 29 →
      (-2 ^ 30 ≤ (windowCenter st.toCellState).1 ∧ (windowCenter st.toCellState).1 ≤ 2 ^ 30) →
      (-2 ^ 30 ≤ (windowCenter st.toCellState).2 ∧ (windowCenter st.toCellState).2 ≤ 2 ^ 30) →
      (stepNGenerationsWith n st (fun s => stepHashLifeStateWith s P)).toCellState = hashLifeStepN k st.toCellState := by
  intro k
  induction k with
  | zero =>
    intro n st hn _ _ _ _ _
    have : n = 0 := UInt32.toNat_inj.mp (by simpa using hn)
    subst this
    rw [stepNGenerationsWith]
    rfl
  | succ k ih =>
    intro n st hn hwf hok hd hcx hcy
    have hn0 : n ≠ 0 := fun h => by subst h; simp at hn
    have h1 := stepHashLifeStateWith_correct st P hP hwf hok (by omega) hcx hcy
    obtain ⟨hw', hd', _⟩ :=
      hashLifeNextGeneration_correct st.toCellState hwf (by simp [HashLifeStepState.toCellState]; omega)
    have hd'' : (hashLifeNextGeneration st.toCellState).macroCell.depth ≤ st.macroCell.depth + 1 := hd'
    have hc := windowCenter_hashLifeNextGeneration st.toCellState hwf (by simp [HashLifeStepState.toCellState]; omega)
    have hmc : (stepHashLifeStateWith st P).macroCell = (hashLifeNextGeneration st.toCellState).macroCell := by
      rw [← h1]; rfl
    have hok' : HashOK (stepHashLifeStateWith st P).macroCell := by
      rw [hmc]
      unfold hashLifeNextGeneration hashLifeNextGenerationStep
      split <;> exact HashOK_hashLifeStep _
    rw [stepNGenerationsWith_ne_zero _ _ _ hn0,
      ih (n - 1) _ (by rw [toNat_sub_one_of_ne_zero hn0]; omega) (by rw [hmc]; exact hw') hok'
        (by rw [hmc]; omega)
        (by rw [h1, hc]; exact hcx) (by rw [h1, hc]; exact hcy), h1]
    rfl

/--
The prepared-node step of `LeanHashLifeAlgorithm` is HashLife's step. The callbacks are those of
`LeanHashLifeAlgorithm.kt`, described by what their memo tables and canonical maps return:
- `L` is the memoized leaf step (`leafNodeMap`, loading `computeLeafNextGen8x8BranchUInt`);
- `G` and `F` step canonicalized Level 4 nodes and CellNodes (`level4NodeMap`, `cellNodeMap`), with `F` calling
  itself on subnodes;
- the canonical maps return a value equal to their argument: a Level 4 node is found by structural equality,
  and a CellNode by its level and identical children, which for hash-consistent nodes is the same value;
- `canonicalizeSubnode` is the same canonicalization.
-/
theorem leanHashLife_preparedStep (L : UInt64 → UInt32) (G : MacroCell → UInt64) (F : MacroCell → MacroCell)
    (internLevel4 : MacroCell → MacroCell) (findExistingCell : MacroCell → Option MacroCell)
    (canonicalizeSubnode internCell : MacroCell → MacroCell)
    (hL : ∀ w, L w = computeLeafNextGen8x8BranchUInt w)
    (hG : ∀ q, G q = stepLevel4NodeWith
      (canonicalizeMacroCellWith q internLevel4 findExistingCell canonicalizeSubnode internCell) L)
    (hF : ∀ q, F q = stepCellNodeWith
      (canonicalizeMacroCellWith q internLevel4 findExistingCell canonicalizeSubnode internCell) G F)
    (hI4 : ∀ q, internLevel4 q = q)
    (hFe : ∀ q e, HashOK q → findExistingCell q = some e → e = q)
    (hIc : ∀ q, HashOK q → internCell q = q)
    (hS : ∀ q, canonicalizeSubnode q =
      canonicalizeMacroCellWith q internLevel4 findExistingCell canonicalizeSubnode internCell) :
    ∀ q d, WFd q d → 5 ≤ d → d ≤ 30 → HashOK q →
      canonicalizeMacroCellWith (stepCellNodeWith q G F) internLevel4 findExistingCell canonicalizeSubnode internCell =
        hashLifeStep q := by
  have hcanon := canonicalize_fixpoint internLevel4 findExistingCell canonicalizeSubnode internCell hI4 hFe hIc
    (fun q _ _ _ _ => hS q)
  have hL' : L = computeLeafNextGen8x8BranchUInt := funext hL
  have hG' : ∀ q, WFd q 4 → G q = stepLevel4Node q := by
    intro q hq
    obtain ⟨_, _, _, _, _, rfl⟩ := WFd_level4 hq
    rw [hG]
    simp only [canonicalizeMacroCellWith, hI4]
    rw [hL', ← stepLevel4Node_eq_stepLevel4NodeWith_Impl]
  have hstep := stepCellNodeWith_fixpoint G F hG'
    (fun q d hq h5 hd H => by rw [hF, hcanon d q hq hd H])
  intro q d hq h5 hd H
  rw [stepCellNodeWith_spec G F hq h5 (by omega) H hG'
    (fun _ c hc Hc => hstep (d - 1) c hc (by omega) (by omega) Hc)]
  exact hcanon (d - 1) _ (depth_hashLifeStep hq h5 (by omega)) (by omega) (HashOK_hashLifeStep q)

end Algorithm
