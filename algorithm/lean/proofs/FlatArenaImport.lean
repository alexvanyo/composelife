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
import proofs.SemanticModelProofs
import proofs.HashLifeStepProofs
import proofs.FlatArenaBasics
import proofs.FlatArenaIntern
import proofs.FlatArenaExtract
import proofs.FlatArenaGeneration
import proofs.FlatArenaQuery

local notation "ℕ" => Nat
local notation "ℤ" => Int

namespace Algorithm

/-!
# Flat HashLife arena: importing a Level 4 root

A Level 4 pattern is imported as its centered two-level expansion, whose top-left corner is 24 cells up and
to the left of the pattern's.
-/

/--
`importLevel4Root` keeps the invariant; whenever it succeeds the new root denotes the centered expansion of
the Level 4 node, with its top-left corner 24 cells up and to the left; and it succeeds whenever that corner
is representable and the arena did not run out of capacity.
-/
theorem importLevel4Root_spec {a : FlatHashLifeArena} (hwf : ArenaWF a) (ox oy : Int32) (nw ne sw se : UInt64) :
    Grows a (a.importLevel4Root ox oy nw ne sw se).2 ∧
    ((a.importLevel4Root ox oy nw ne sw se).1.2.2 ≠ UNCOMPUTED →
      (a.importLevel4Root ox oy nw ne sw se).2.overflow = 0 ∧
      (a.importLevel4Root ox oy nw ne sw se).1.2.2 < (a.importLevel4Root ox oy nw ne sw se).2.cellCount ∧
      flatState (a.importLevel4Root ox oy nw ne sw se).2 (a.importLevel4Root ox oy nw ne sw se).1.1
        (a.importLevel4Root ox oy nw ne sw se).1.2.1 (a.importLevel4Root ox oy nw ne sw se).1.2.2 =
        { offset := (ox.toInt - 24, oy.toInt - 24), macroCell := expandCentered (makeLevel4Node nw ne sw se) }) ∧
    (-2 ^ 31 ≤ ox.toInt - 24 → -2 ^ 31 ≤ oy.toInt - 24 →
      (a.importLevel4Root ox oy nw ne sw se).2.overflow = 0 →
      (a.importLevel4Root ox oy nw ne sw se).1.2.2 ≠ UNCOMPUTED) := by
  have hx1 := Int32.toInt_lt ox
  have hx2 := Int32.le_toInt ox
  have hy1 := Int32.toInt_lt oy
  have hy2 := Int32.le_toInt oy
  have h31 : (2 : ℤ) ^ 31 = 2147483648 := by decide
  have h63 : (2 : ℤ) ^ 63 = 9223372036854775808 := by decide
  have h24 : (24 : Int64).toInt = 24 := by decide
  have hm : (-2147483648 : Int64).toInt = -2147483648 := by decide
  have hnx : (ox.toInt64 - 24).toInt = ox.toInt - 24 := by
    rw [i64_sub_toInt (by rw [Int32.toInt_toInt64, h24]; omega) (by rw [Int32.toInt_toInt64, h24]; omega),
      Int32.toInt_toInt64, h24]
  have hny : (oy.toInt64 - 24).toInt = oy.toInt - 24 := by
    rw [i64_sub_toInt (by rw [Int32.toInt_toInt64, h24]; omega) (by rw [Int32.toInt_toInt64, h24]; omega),
      Int32.toInt_toInt64, h24]
  unfold FlatHashLifeArena.importLevel4Root
  dsimp only
  by_cases hr : (ox.toInt64 - 24 < -2147483648 || oy.toInt64 - 24 < -2147483648) = true
  · rw [ite_eq_left hr]
    refine ⟨Grows.refl hwf, fun h => absurd rfl h, fun h1 h2 _ => ?_⟩
    simp only [Bool.or_eq_true, decide_eq_true_eq, Int64.lt_iff_toInt_lt, hnx, hny, hm] at hr
    omega
  · rw [ite_eq_right hr]
    simp only [Bool.or_eq_true, decide_eq_true_eq, Int64.lt_iff_toInt_lt, hnx, hny, hm, not_or,
      Int.not_lt] at hr
    have s1 := internLevel4_spec hwf nw ne sw se
    rcases e1 : a.internLevel4 nw ne sw se with ⟨l4Id, a1⟩
    rw [e1] at s1
    obtain ⟨g1, n1⟩ := s1
    dsimp only
    split
    · rename_i hov1
      exact ⟨g1, fun h => absurd rfl h, fun _ _ h => absurd h (by simpa using hov1)⟩
    · rename_i hov1
      have hn1 := n1 (by simpa using hov1)
      have s2 := expandLevel4Centered_spec g1.wf hn1
      rcases e2 : a1.expandLevel4Centered l4Id with ⟨rootId, a2⟩
      rw [e2] at s2
      obtain ⟨g2, n2⟩ := s2
      dsimp only
      split
      · rename_i hov2
        exact ⟨g1.trans g2, fun h => absurd rfl h, fun _ _ h => absurd h (by simpa using hov2)⟩
      · rename_i hov2
        have hov2' : a2.overflow = 0 := by simpa using hov2
        have hn2 := n2 hov2'
        refine ⟨g1.trans g2, fun _ => ⟨hov2', hn2.lt_cell, ?_⟩, fun _ _ _ => ne_uncomputed_of_lt hn2.lt_cell⟩
        unfold flatState
        rw [hn2.denoteCell_eq, i64_toInt32_toInt (by rw [hnx]; omega) (by rw [hnx]; omega),
          i64_toInt32_toInt (by rw [hny]; omega) (by rw [hny]; omega), hnx, hny]

/--
Whenever `importLevel4Root` succeeds, the imported state has exactly the live cells of the Level 4 pattern
whose top-left corner is `(ox, oy)`.
-/
theorem importLevel4Root_grid {a : FlatHashLifeArena} (hwf : ArenaWF a) (ox oy : Int32) (nw ne sw se : UInt64)
    (hok : (a.importLevel4Root ox oy nw ne sw se).1.2.2 ≠ UNCOMPUTED) (c : Coord) :
    c ∈ hashLifeToGrid (flatState (a.importLevel4Root ox oy nw ne sw se).2
        (a.importLevel4Root ox oy nw ne sw se).1.1 (a.importLevel4Root ox oy nw ne sw se).1.2.1
        (a.importLevel4Root ox oy nw ne sw se).1.2.2) ↔
      c ∈ hashLifeToGrid { offset := (ox.toInt, oy.toInt), macroCell := makeLevel4Node nw ne sw se } := by
  obtain ⟨_, hs, _⟩ := importLevel4Root_spec hwf ox oy nw ne sw se
  obtain ⟨_, _, heq⟩ := hs hok
  rw [heq]
  have hm : WFd (makeLevel4Node nw ne sw se) 4 := WFd_makeLevel4Node nw ne sw se
  obtain ⟨hwE, hcE⟩ := expandCentered_spec hm (by omega)
  unfold hashLifeToGrid
  dsimp only
  rw [mem_macroCellToGrid_iff hwE (by omega), mem_macroCellToGrid_iff hm (by omega), hcE]
  have h3 : (3 : ℤ) * 2 ^ (4 - 1) = 24 := by decide
  rw [h3]
  constructor <;> intro h <;> refine (fn_congr2 _ ?_ ?_).trans h <;> omega

end Algorithm
