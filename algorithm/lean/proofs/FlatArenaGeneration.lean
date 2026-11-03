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
import proofs.FlatArenaStep

local notation "ℕ" => Nat
local notation "ℤ" => Int

namespace Algorithm

/-!
# Flat HashLife arena: one generation

`stepOneGeneration` refines `flatNextGeneration` exactly (root and offsets), whenever it reports success,
and it reports success whenever the next generation is representable and the arena has capacity.
-/

-- =========================================================================
-- Fixed-width offset arithmetic
-- =========================================================================

theorem bmod64_small {x : ℤ} (h1 : -2 ^ 63 ≤ x) (h2 : x < 2 ^ 63) : x.bmod (2 ^ 64) = x := by
  rw [Int.bmod_def]
  split <;> omega

theorem bmod32_small {x : ℤ} (h1 : -2 ^ 31 ≤ x) (h2 : x < 2 ^ 31) : x.bmod (2 ^ 32) = x := by
  rw [Int.bmod_def]
  split <;> omega

theorem pow2Int64_table : ∀ k : Fin 63, (pow2Int64 (UInt32.ofNat k.val)).toInt = 2 ^ k.val := by
  decide

theorem pow2Int64_toInt {k : UInt32} (hk : k.toNat < 63) : (pow2Int64 k).toInt = 2 ^ k.toNat := by
  have := pow2Int64_table ⟨k.toNat, hk⟩
  simpa using this

theorem i64_add_toInt {x y : Int64} (h1 : -2 ^ 63 ≤ x.toInt + y.toInt) (h2 : x.toInt + y.toInt < 2 ^ 63) :
    (x + y).toInt = x.toInt + y.toInt := by
  rw [Int64.toInt_add, bmod64_small h1 h2]

theorem i64_mul_toInt {x y : Int64} (h1 : -2 ^ 63 ≤ x.toInt * y.toInt) (h2 : x.toInt * y.toInt < 2 ^ 63) :
    (x * y).toInt = x.toInt * y.toInt := by
  rw [Int64.toInt_mul, bmod64_small h1 h2]

theorem i64_neg_toInt {x : Int64} (h1 : -2 ^ 63 ≤ -x.toInt) (h2 : -x.toInt < 2 ^ 63) :
    (-x).toInt = -x.toInt := by
  rw [Int64.toInt_neg, bmod64_small h1 h2]

theorem i64_toInt32_toInt {x : Int64} (h1 : -2 ^ 31 ≤ x.toInt) (h2 : x.toInt < 2 ^ 31) :
    x.toInt32.toInt = x.toInt := by
  rw [Int64.toInt_toInt32, bmod32_small h1 h2]

theorem pow_two_le_pow {a b : ℕ} (h : a ≤ b) : (2 : ℤ) ^ a ≤ 2 ^ b := by
  have := Nat.pow_le_pow_right (show 2 > 0 by decide) h
  have e1 : ((2 ^ a : ℕ) : ℤ) = (2 : ℤ) ^ a := by simp
  have e2 : ((2 ^ b : ℕ) : ℤ) = (2 : ℤ) ^ b := by simp
  rw [← e1, ← e2]
  exact Int.ofNat_le.mpr this

theorem pow_two_pos' (n : ℕ) : (0 : ℤ) < 2 ^ n := Int.pow_pos (by decide)

/--
The offset delta computed by `stepOneGeneration` for a root at level `L` (expanding first if `expand`).
-/
theorem flatDelta_toInt {L : UInt32} (hL5 : 5 ≤ L.toNat) (expand : Bool)
    (hK : (if expand then L.toNat + 2 else L.toNat) ≤ 30) :
    ((if expand then -(3 * pow2Int64 (L - 1)) else 0) + pow2Int64 ((if expand then L + 2 else L) - 2)).toInt =
      (if expand then -3 * 2 ^ (L.toNat - 1) else 0) + 2 ^ ((if expand then L.toNat + 2 else L.toNat) - 2) := by
  have hL1 : (L - 1).toNat = L.toNat - 1 := u32_toNat_sub (by simp; omega)
  cases expand with
  | false =>
    simp only [Bool.false_eq_true, ite_false] at hK ⊢
    have hL2 : (L - 2).toNat = L.toNat - 2 := u32_toNat_sub (by simp; omega)
    have hp := pow2Int64_toInt (k := L - 2) (by omega)
    rw [hL2] at hp
    have hz : (0 : Int64).toInt = 0 := by decide
    have hb := pow_two_le_pow (show L.toNat - 2 ≤ 28 by omega)
    have hpos := pow_two_pos' (L.toNat - 2)
    have h28 : (2 : ℤ) ^ 28 = 268435456 := by decide
    rw [i64_add_toInt (by rw [hz, hp]; omega) (by rw [hz, hp]; omega), hz, hp]
  | true =>
    simp only [ite_true] at hK ⊢
    have hLp : (L + 2).toNat = L.toNat + 2 := u32_toNat_add (by simp; omega)
    have hL2 : (L + 2 - 2).toNat = L.toNat := by
      rw [u32_toNat_sub (by rw [hLp]; simp), hLp]
      simp
    have hp1 := pow2Int64_toInt (k := L - 1) (by omega)
    have hp2 := pow2Int64_toInt (k := L + 2 - 2) (by omega)
    rw [hL1] at hp1
    rw [hL2] at hp2
    have h3 : (3 : Int64).toInt = 3 := by decide
    have hb1 := pow_two_le_pow (show L.toNat - 1 ≤ 27 by omega)
    have hb2 := pow_two_le_pow (show L.toNat ≤ 28 by omega)
    have hpos1 := pow_two_pos' (L.toNat - 1)
    have hpos2 := pow_two_pos' L.toNat
    have h27 : (2 : ℤ) ^ 27 = 134217728 := by decide
    have h28 : (2 : ℤ) ^ 28 = 268435456 := by decide
    have hm : (3 * pow2Int64 (L - 1)).toInt = 3 * 2 ^ (L.toNat - 1) := by
      rw [i64_mul_toInt (by rw [h3, hp1]; omega) (by rw [h3, hp1]; omega), h3, hp1]
    have hn : (-(3 * pow2Int64 (L - 1))).toInt = -(3 * 2 ^ (L.toNat - 1)) := by
      rw [i64_neg_toInt (by rw [hm]; omega) (by rw [hm]; omega), hm]
    rw [i64_add_toInt (by rw [hn, hp2]; omega) (by rw [hn, hp2]; omega), hn, hp2,
      show L.toNat + 2 - 2 = L.toNat by omega]
    omega

-- =========================================================================
-- Levels of prepared roots
-- =========================================================================

theorem WFd_expandCentered_cell {D1 D2 D3 D4 : MacroCell} {h : ℕ}
    (h1 : WFd D1 (h + 4)) (h2 : WFd D2 (h + 4)) (h3 : WFd D3 (h + 4)) (h4 : WFd D4 (h + 4)) :
    WFd (expandCentered (makeCellNode D1 D2 D3 D4)) (h + 7) := by
  rw [expandCentered_cell h1]
  have e4 := WFd_emptyNode h
  have e5 : WFd (emptyNode (h + 5)) (h + 5) := by
    have := WFd_emptyNode (h + 1)
    rwa [show h + 1 + 4 = h + 5 by omega] at this
  have i1 : WFd (makeCellNode (emptyNode (h + 4)) (emptyNode (h + 4)) (emptyNode (h + 4)) D1) (h + 5) :=
    WFd_makeCellNode e4 e4 e4 h1
  have i2 : WFd (makeCellNode (emptyNode (h + 4)) (emptyNode (h + 4)) D2 (emptyNode (h + 4))) (h + 5) :=
    WFd_makeCellNode e4 e4 h2 e4
  have i3 : WFd (makeCellNode (emptyNode (h + 4)) D3 (emptyNode (h + 4)) (emptyNode (h + 4))) (h + 5) :=
    WFd_makeCellNode e4 h3 e4 e4
  have i4 : WFd (makeCellNode D4 (emptyNode (h + 4)) (emptyNode (h + 4)) (emptyNode (h + 4))) (h + 5) :=
    WFd_makeCellNode h4 e4 e4 e4
  have o1 := WFd_makeCellNode e5 e5 e5 i1
  have o2 := WFd_makeCellNode e5 e5 i2 e5
  have o3 := WFd_makeCellNode e5 i3 e5 e5
  have o4 := WFd_makeCellNode i4 e5 e5 e5
  exact WFd_makeCellNode o1 o2 o3 o4

theorem WFd_expandCentered_of_node {a : FlatHashLifeArena} (hwf : ArenaWF a) {k : ℕ} {id : UInt32}
    {m : MacroCell} (hn : NodeIs a (k + 1) id m) : WFd (expandCentered m) (k + 7) := by
  obtain ⟨c1, c2, c3, c4, hm⟩ := hn.children hwf
  rw [hm]
  have w1 := c1.WFd
  have w2 := c2.WFd
  have w3 := c3.WFd
  have w4 := c4.WFd
  exact WFd_expandCentered_cell w1 w2 w3 w4

-- =========================================================================
-- One generation
-- =========================================================================

/--
`stepOneGeneration` keeps the invariant; whenever it succeeds (returns a root other than `UNCOMPUTED`) the
new root and top-left corner are exactly `flatNextGeneration` of the input; and it succeeds whenever the input
root is valid, the next generation is representable (`flatStepInRange`), and the arena did not run out of
capacity.
-/
theorem stepOneGeneration_spec {a : FlatHashLifeArena} (hwf : ArenaWF a) (ox oy : Int32) (root : UInt32) :
    LoopOK a (a.stepOneGeneration ox oy root).2 ∧
    ((a.stepOneGeneration ox oy root).1.2.2 ≠ UNCOMPUTED →
      (a.stepOneGeneration ox oy root).2.overflow = 0 ∧ root < a.cellCount ∧
      (a.stepOneGeneration ox oy root).1.2.2 < (a.stepOneGeneration ox oy root).2.cellCount ∧
      flatState (a.stepOneGeneration ox oy root).2 (a.stepOneGeneration ox oy root).1.1
        (a.stepOneGeneration ox oy root).1.2.1 (a.stepOneGeneration ox oy root).1.2.2 =
        flatNextGeneration (flatState a ox oy root) ∧
      flatStepInRange (flatState a ox oy root)) ∧
    (root < a.cellCount → flatStepInRange (flatState a ox oy root) →
      (a.stepOneGeneration ox oy root).2.overflow = 0 → (a.stepOneGeneration ox oy root).1.2.2 ≠ UNCOMPUTED) := by
  unfold FlatHashLifeArena.stepOneGeneration
  by_cases hroot : root ≥ a.cellCount
  · rw [ite_eq_left hroot]
    refine ⟨LoopOK.refl hwf, fun h => absurd rfl h, fun h => ?_⟩
    rw [ge_iff_le, u32_le_iff] at hroot
    have := u32_lt_iff.mp h
    omega
  rw [ite_eq_right hroot]
  have hid : root < a.cellCount := by
    rw [ge_iff_le, u32_le_iff] at hroot
    rw [u32_lt_iff]
    omega
  obtain ⟨k, hk, hnode⟩ := NodeIs.of_lt' hwf hid
  have hLnat : (a.cellLevel[root.toNat]!.toUInt32).toNat = k + 5 := by
    rw [u8_toUInt32_toNat]
    exact hk
  have hWm := hnode.WFd
  have hMlev : (denoteCell a root).level = a.cellLevel[root.toNat]!.toUInt32 := by
    apply u32_eq_of_toNat
    rw [hLnat, WFd_level_toNat hWm (by have := u8_toNat_lt (a.cellLevel[root.toNat]!); unfold cellLevelOf at hk; omega)]
  have hexp : a.needToExpandCell root = needToExpand (denoteCell a root) := needToExpandCell_spec hwf hnode
  dsimp only
  rw [hexp, ← hMlev]
  have hst : flatState a ox oy root = { offset := (ox.toInt, oy.toInt), macroCell := denoteCell a root } := rfl
  rw [hst]
  unfold flatNextGeneration flatPrepare flatStepInRange flatNextGeneration flatPrepare
  have hLv : (denoteCell a root).level.toNat = k + 5 := by rw [hMlev]; exact hLnat
  generalize hM : denoteCell a root = M at hnode hWm hLv hexp hMlev
  cases hE : (decide (M.level ≤ 5) || needToExpand M) with
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    have hk1 : 1 ≤ k := by
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hE
      have := hE.1
      rw [UInt32.le_iff_toNat_le, hLv] at this
      simp at this
      omega
    split
    · -- prepared level too large
      rename_i hK
      refine ⟨LoopOK.refl hwf, fun h => absurd rfl h, fun _ hr _ => ?_⟩
      exfalso
      rw [gt_iff_lt, u32_lt_iff] at hK
      try simp only at hr
      have := hr.1
      try simp at hK
      omega
    · rename_i hK
      have hK' : M.level.toNat ≤ 30 := by
        rw [gt_iff_lt, u32_lt_iff] at hK
        simp at hK
        omega
      have hdelta := flatDelta_toInt (L := M.level) (by omega) false (by simpa using hK')
      simp only [Bool.false_eq_true, ite_false] at hdelta
      have hnx : (ox.toInt64 + ((0 : Int64) + pow2Int64 (M.level - 2))).toInt =
          ox.toInt + 2 ^ (M.level.toNat - 2) := by
        have hb := pow_two_le_pow (show M.level.toNat - 2 ≤ 28 by omega)
        have h28 : (2 : ℤ) ^ 28 = 268435456 := by decide
        have hx1 := Int32.le_toInt ox
        have hx2 := Int32.toInt_lt ox
        have hp31 : (2 : ℤ) ^ 31 = 2147483648 := by decide
        rw [i64_add_toInt (by rw [Int32.toInt_toInt64, hdelta]; have := pow_two_pos' (M.level.toNat - 2); omega)
          (by rw [Int32.toInt_toInt64, hdelta]; omega), Int32.toInt_toInt64, hdelta]
        omega
      have hny : (oy.toInt64 + ((0 : Int64) + pow2Int64 (M.level - 2))).toInt =
          oy.toInt + 2 ^ (M.level.toNat - 2) := by
        have hb := pow_two_le_pow (show M.level.toNat - 2 ≤ 28 by omega)
        have h28 : (2 : ℤ) ^ 28 = 268435456 := by decide
        have hx1 := Int32.le_toInt oy
        have hx2 := Int32.toInt_lt oy
        have hp31 : (2 : ℤ) ^ 31 = 2147483648 := by decide
        rw [i64_add_toInt (by rw [Int32.toInt_toInt64, hdelta]; have := pow_two_pos' (M.level.toNat - 2); omega)
          (by rw [Int32.toInt_toInt64, hdelta]; omega), Int32.toInt_toInt64, hdelta]
        omega
      have hlo : ((-2147483648 : Int64)).toInt = -2147483648 := by decide
      have hhi : ((2147483647 : Int64)).toInt = 2147483647 := by decide
      split
      · -- next offset out of range
        rename_i hR
        refine ⟨LoopOK.refl hwf, fun h => absurd rfl h, fun _ hr _ => ?_⟩
        exfalso
        simp only [Bool.or_eq_true, decide_eq_true_eq, Int64.lt_iff_toInt_lt, hnx, hny, hlo, hhi] at hR
        unfold hashLifeNextGenerationStep stepOffsetDelta at hr
        simp only at hr
        omega
      · rename_i hR
        simp only [Bool.or_eq_true, decide_eq_true_eq, Int64.lt_iff_toInt_lt, hnx, hny, hlo, hhi, not_or,
          Int.not_lt] at hR
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        try dsimp only
        split
        · rename_i hov
          refine ⟨LoopOK.refl hwf, fun h => absurd rfl h, fun _ _ h => absurd h (by simpa using hov)⟩
        · rename_i hov
          have hs := stepCellSerial_spec hwf hnode
          rcases e : a.stepCellSerial root with ⟨nextId, a2⟩
          rw [e] at hs
          obtain ⟨l2, r2⟩ := hs
          dsimp only at l2 r2 ⊢
          split
          · rename_i hov2
            refine ⟨l2, fun h => absurd rfl h, fun _ _ h => absurd h (by simpa using hov2)⟩
          · rename_i hov2
            have hov2' : a2.overflow = 0 := by simpa using hov2
            have hres := r2 hov2'
            have hp31 : (2 : ℤ) ^ 31 = 2147483648 := by decide
            refine ⟨l2, fun _ => ⟨hov2', hid, hres.lt_cell, ?_, ?_⟩, fun _ _ _ => ne_uncomputed_of_lt hres.lt_cell⟩
            rotate_left
            · unfold hashLifeNextGenerationStep stepOffsetDelta
              refine ⟨hK', ?_, ?_, ?_, ?_⟩ <;> dsimp only <;> omega
            unfold flatState hashLifeNextGenerationStep stepOffsetDelta
            rw [hres.denoteCell_eq, i64_toInt32_toInt (by rw [hnx]; omega) (by rw [hnx]; omega),
              i64_toInt32_toInt (by rw [hny]; omega) (by rw [hny]; omega), hnx, hny]
  | true =>
    simp only [ite_true]
    have hk256 : k + 5 < 256 := by
      have := u8_toNat_lt (a.cellLevel[root.toNat]!)
      unfold cellLevelOf at hk
      omega
    have hk28 : (M.level + 2).toNat = M.level.toNat + 2 := u32_toNat_add (by simp; omega)
    have hWe : WFd (expandCentered M) (k + 7) := WFd_expandCentered_of_node hwf hnode
    have hLe : (expandCentered M).level.toNat = M.level.toNat + 2 := by
      rw [WFd_level_toNat hWe (by omega), hLv]
    split
    · rename_i hK
      refine ⟨LoopOK.refl hwf, fun h => absurd rfl h, fun _ hr _ => ?_⟩
      exfalso
      rw [gt_iff_lt, u32_lt_iff, hk28] at hK
      try simp only at hr
      have := hr.1
      rw [hLe] at this
      try simp at hK
      omega
    · rename_i hK
      have hK' : M.level.toNat + 2 ≤ 30 := by
        rw [gt_iff_lt, u32_lt_iff, hk28] at hK
        simp at hK
        omega
      have hdelta := flatDelta_toInt (L := M.level) (by omega) true (by simpa using hK')
      simp only [ite_true] at hdelta
      have hb1 := pow_two_le_pow (show M.level.toNat - 1 ≤ 27 by omega)
      have hb2 := pow_two_le_pow (show M.level.toNat + 2 - 2 ≤ 28 by omega)
      have h27 : (2 : ℤ) ^ 27 = 134217728 := by decide
      have h28 : (2 : ℤ) ^ 28 = 268435456 := by decide
      have hp31 : (2 : ℤ) ^ 31 = 2147483648 := by decide
      have hpos1 := pow_two_pos' (M.level.toNat - 1)
      have hpos2 := pow_two_pos' (M.level.toNat + 2 - 2)
      have hnx : (ox.toInt64 + (-(3 * pow2Int64 (M.level - 1)) + pow2Int64 (M.level + 2 - 2))).toInt =
          ox.toInt + (-3 * 2 ^ (M.level.toNat - 1) + 2 ^ (M.level.toNat + 2 - 2)) := by
        have hx1 := Int32.le_toInt ox
        have hx2 := Int32.toInt_lt ox
        rw [i64_add_toInt (by rw [Int32.toInt_toInt64, hdelta]; omega) (by rw [Int32.toInt_toInt64, hdelta]; omega),
          Int32.toInt_toInt64, hdelta]
      have hny : (oy.toInt64 + (-(3 * pow2Int64 (M.level - 1)) + pow2Int64 (M.level + 2 - 2))).toInt =
          oy.toInt + (-3 * 2 ^ (M.level.toNat - 1) + 2 ^ (M.level.toNat + 2 - 2)) := by
        have hx1 := Int32.le_toInt oy
        have hx2 := Int32.toInt_lt oy
        rw [i64_add_toInt (by rw [Int32.toInt_toInt64, hdelta]; omega) (by rw [Int32.toInt_toInt64, hdelta]; omega),
          Int32.toInt_toInt64, hdelta]
      have hlo : ((-2147483648 : Int64)).toInt = -2147483648 := by decide
      have hhi : ((2147483647 : Int64)).toInt = 2147483647 := by decide
      split
      · rename_i hR
        refine ⟨LoopOK.refl hwf, fun h => absurd rfl h, fun _ hr _ => ?_⟩
        exfalso
        simp only [Bool.or_eq_true, decide_eq_true_eq, Int64.lt_iff_toInt_lt, hnx, hny, hlo, hhi] at hR
        unfold hashLifeNextGenerationStep stepOffsetDelta expandOffsetDelta at hr
        simp only at hr
        rw [hLe] at hr
        omega
      · rename_i hR
        simp only [Bool.or_eq_true, decide_eq_true_eq, Int64.lt_iff_toInt_lt, hnx, hny, hlo, hhi, not_or,
          Int.not_lt] at hR
        try dsimp only
        have he := flatExpandCentered_spec hwf hnode (by omega)
        rcases e1 : a.expandCentered root with ⟨prepId, a1⟩
        rw [e1] at he
        obtain ⟨g1, r1⟩ := he
        have w1 := g1.wf
        dsimp only at g1 r1 w1 ⊢
        split
        · rename_i hov
          refine ⟨g1.loopOK, fun h => absurd rfl h, fun _ _ h => absurd h (by simpa using hov)⟩
        · rename_i hov
          have hov' : a1.overflow = 0 := by simpa using hov
          have hprep := r1 hov'
          have hs := stepCellSerial_spec w1 hprep
          rcases e2 : a1.stepCellSerial prepId with ⟨nextId, a2⟩
          rw [e2] at hs
          obtain ⟨l2, r2⟩ := hs
          dsimp only at l2 r2 ⊢
          split
          · rename_i hov2
            refine ⟨g1.loopOK.trans l2, fun h => absurd rfl h, fun _ _ h => absurd h (by simpa using hov2)⟩
          · rename_i hov2
            have hov2' : a2.overflow = 0 := by simpa using hov2
            have hres := r2 hov2'
            refine ⟨g1.loopOK.trans l2, fun _ => ⟨hov2', hid, hres.lt_cell, ?_, ?_⟩,
              fun _ _ _ => ne_uncomputed_of_lt hres.lt_cell⟩
            rotate_left
            · unfold hashLifeNextGenerationStep stepOffsetDelta expandOffsetDelta
              rw [hLe]
              refine ⟨by omega, ?_, ?_, ?_, ?_⟩ <;> dsimp only <;> omega
            unfold flatState hashLifeNextGenerationStep stepOffsetDelta expandOffsetDelta
            rw [hres.denoteCell_eq, i64_toInt32_toInt (by rw [hnx]; omega) (by rw [hnx]; omega),
              i64_toInt32_toInt (by rw [hny]; omega) (by rw [hny]; omega), hnx, hny, hLe]
            simp only [HashLifeCellState.mk.injEq, Prod.mk.injEq, and_true]
            constructor <;> omega

end Algorithm
