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

import Algorithm.RLE
import proofs.SerialCoreProofs

namespace Algorithm

/-! ## Rules -/

theorem scanDigitSet_list (L : List UInt8) (hL : L.length < 2 ^ 32) (p : Nat) (ds rest : List UInt8)
    (hsplit : L.drop p = ds ++ rest) (hds : ∀ d ∈ ds, isDigitByte d = true)
    (hrest : ∀ y, rest.head? = some y → isDigitByte y = false) (hp : p ≤ L.length) :
    (scanDigitSet ⟨L.toArray⟩ (⟨L.toArray⟩ : ByteArray).size.toUInt32 p.toUInt32 0).1.toNat = p + ds.length ∧
      (scanDigitSet ⟨L.toArray⟩ (⟨L.toArray⟩ : ByteArray).size.toUInt32 p.toUInt32 0).2 = ds.foldl digitMaskStep 0 := by
  have hsz : (⟨L.toArray⟩ : ByteArray).size < 2 ^ 32 := by rw [size_of_list]; exact hL
  have hp' : p.toUInt32.toNat = p := u32_size_toNat (by omega)
  obtain ⟨h1, h2⟩ := scanDigitSet_spec ⟨L.toArray⟩ hsz _ p.toUInt32 0 rfl (by rw [hp', size_of_list]; exact hp)
  rw [hp', bytesFrom_of_list, hsplit, takeWhile_digits_append ds rest hds hrest] at h1 h2
  exact ⟨h1, h2⟩

open Classical in
/--
A rule `B<birth>/S<survival>` (with either case of letters) after `prefix` is Conway's rules (0) exactly when the
birth digits are {3} and the survival digits are {2, 3}, in any order and with repeats, and another rule (3)
otherwise.
-/
theorem checkRLERule_letters (pre b s : List UInt8) (cB cS : UInt8) (hcB : cB = 66 ∨ cB = 98)
    (hcS : cS = 83 ∨ cS = 115) (hb : b ≠ []) (hs : s ≠ []) (hbd : ∀ d ∈ b, isDigitByte d = true)
    (hsd : ∀ d ∈ s, isDigitByte d = true) (hsz : pre.length + b.length + s.length + 3 < 2 ^ 32) :
    checkRLERule ⟨(pre ++ cB :: (b ++ 47 :: cS :: s)).toArray⟩ pre.length.toUInt32
        (⟨(pre ++ cB :: (b ++ 47 :: cS :: s)).toArray⟩ : ByteArray).size.toUInt32 =
      if ((∀ d ∈ b, d = 51) ∧ 51 ∈ b) ∧ ((∀ d ∈ s, d = 50 ∨ d = 51) ∧ 50 ∈ s ∧ 51 ∈ s) then 0 else 3 := by
  generalize hL : pre ++ cB :: (b ++ 47 :: cS :: s) = L
  have hLlen : L.length = pre.length + b.length + s.length + 3 := by rw [← hL]; simp; omega
  have hsize : (⟨L.toArray⟩ : ByteArray).size = L.length := size_of_list L
  have hB32 : (⟨L.toArray⟩ : ByteArray).size < 2 ^ 32 := by omega
  have hlimit : (⟨L.toArray⟩ : ByteArray).size.toUInt32.toNat = L.length := by rw [u32_size_toNat hB32, hsize]
  have hget : ∀ k, k < L.length → (⟨L.toArray⟩ : ByteArray).get! k = L[k]! := get!_of_list L
  have hidx : ∀ k, k ≤ L.length → k.toUInt32.toNat = k := fun k hk => u32_size_toNat (by omega)
  have hcBl : isLetterByte cB 98 = true := by rcases hcB with rfl | rfl <;> decide
  have hcSl : isLetterByte cS 115 = true := by rcases hcS with rfl | rfl <;> decide
  have hcBs : isSpaceByte cB = false := by rcases hcB with rfl | rfl <;> decide
  unfold checkRLERule
  -- No spaces before the rule.
  have hp0 : skipSpaces ⟨L.toArray⟩ pre.length.toUInt32 (⟨L.toArray⟩ : ByteArray).size.toUInt32 =
      pre.length.toUInt32 := by
    apply skipSpaces_of_not_space _ hB32 _ (by rw [hidx _ (by omega), hsize]; omega)
    intro y hy
    rw [hidx _ (by omega), bytesFrom_of_list, ← hL, List.drop_left] at hy
    simp at hy; subst hy; exact hcBs
  rw [hp0]
  have hlt0 : pre.length.toUInt32 < (⟨L.toArray⟩ : ByteArray).size.toUInt32 := by
    rw [UInt32.lt_iff_toNat_lt, hidx _ (by omega), hlimit]; omega
  have hg0 : (⟨L.toArray⟩ : ByteArray).get! pre.length.toUInt32.toNat = cB := by
    rw [hidx _ (by omega), hget _ (by omega), ← hL, getElem!_pos _ _ (by simp)]; simp
  simp only [hlt0, decide_true, hg0, hcBl, Bool.and_self, ite_true]
  -- The birth digits.
  have hs1 : (pre.length.toUInt32 + 1) = (pre.length + 1).toUInt32 := by
    apply UInt32.toNat_inj.mp; rw [UInt32.toNat_add, hidx _ (by omega), hidx _ (by omega)]; simp; omega
  rw [hs1]
  obtain ⟨he1, hm1⟩ := scanDigitSet_list L (by omega) (pre.length + 1) b (47 :: cS :: s)
    (by rw [← hL]; simp [List.drop_append]) hbd (by intro y hy; simp at hy; subst hy; decide) (by omega)
  generalize hsc1 : scanDigitSet ⟨L.toArray⟩ (⟨L.toArray⟩ : ByteArray).size.toUInt32 (pre.length + 1).toUInt32 0 = r1
    at he1 hm1
  obtain ⟨e1, m1⟩ := r1
  simp only at he1 hm1 ⊢
  have hblen : 0 < b.length := List.length_pos_iff.mpr hb
  have hne1 : ¬ (e1 == (pre.length + 1).toUInt32) = true := by
    intro h; have := congrArg UInt32.toNat (beq_iff_eq.mp h); rw [he1, hidx _ (by omega)] at this; omega
  have hlt1 : e1 < (⟨L.toArray⟩ : ByteArray).size.toUInt32 := by rw [UInt32.lt_iff_toNat_lt, hlimit]; omega
  have hg1 : (⟨L.toArray⟩ : ByteArray).get! e1.toNat = 47 := by
    rw [hget _ (by omega), he1, ← hL, getElem!_pos _ _ (by simp; omega)]
    rw [List.getElem_append_right (by omega)]
    simp only [show pre.length + 1 + b.length - pre.length = b.length + 1 by omega, List.getElem_cons_succ]
    rw [List.getElem_append_right (by omega)]
    simp
  simp only [hne1, decide_true, hlt1, Bool.not_true, hg1, bne_self_eq_false, Bool.or_false,
    Bool.false_eq_true, ite_false]
  have hlt2 : e1 + 1 < (⟨L.toArray⟩ : ByteArray).size.toUInt32 := by
    rw [UInt32.lt_iff_toNat_lt, hlimit, UInt32.toNat_add, he1]; simp; omega
  have hg2 : (⟨L.toArray⟩ : ByteArray).get! (e1 + 1).toNat = cS := by
    have : (e1 + 1).toNat = pre.length + 1 + b.length + 1 := by rw [UInt32.toNat_add, he1]; simp; omega
    rw [this, hget _ (by omega), ← hL, getElem!_pos _ _ (by simp; omega)]
    rw [List.getElem_append_right (by omega)]
    simp only [show pre.length + 1 + b.length + 1 - pre.length = b.length + 2 by omega, List.getElem_cons_succ]
    rw [List.getElem_append_right (by omega)]
    simp
  simp only [hlt2, decide_true, hg2, hcSl, Bool.and_self, Bool.not_true, Bool.or_true,
    Bool.false_eq_true, ite_false]
  -- The survival digits.
  have hs2 : e1 + 2 = (pre.length + b.length + 3).toUInt32 := by
    apply UInt32.toNat_inj.mp; rw [UInt32.toNat_add, he1, hidx _ (by omega)]; simp; omega
  rw [hs2]
  obtain ⟨he2, hm2⟩ := scanDigitSet_list L (by omega) (pre.length + b.length + 3) s []
    (by
      rw [← hL, List.append_nil]; simp [List.drop_append]
      rw [show pre.length + b.length + 3 = pre.length + (b.length + 3) by omega, ← List.drop_drop]; simp)
    hsd (by simp) (by omega)
  generalize hsc2 : scanDigitSet ⟨L.toArray⟩ (⟨L.toArray⟩ : ByteArray).size.toUInt32
    (pre.length + b.length + 3).toUInt32 0 = r2 at he2 hm2
  obtain ⟨e2, m2⟩ := r2
  simp only at he2 hm2 ⊢
  have hslen : 0 < s.length := List.length_pos_iff.mpr hs
  have hne2 : ¬ (e2 == (pre.length + b.length + 3).toUInt32) = true := by
    intro h; have := congrArg UInt32.toNat (beq_iff_eq.mp h); rw [he2, hidx _ (by omega)] at this; omega
  have heq : e2 = (⟨L.toArray⟩ : ByteArray).size.toUInt32 := by
    apply UInt32.toNat_inj.mp; rw [he2, hlimit]; omega
  have hend : skipSpaces ⟨L.toArray⟩ e2 (⟨L.toArray⟩ : ByteArray).size.toUInt32 =
      (⟨L.toArray⟩ : ByteArray).size.toUInt32 := by
    rw [heq]
    apply skipSpaces_of_not_space _ hB32 _ (by rw [hlimit, hsize]; exact Nat.le_refl _)
    intro y hy; rw [hlimit, bytesFrom_of_list, List.drop_length] at hy; simp at hy
  simp only [hne2, hend, bne_self_eq_false, Bool.or_false, Bool.false_eq_true, ite_false]
  rw [hm1, hm2]
  have hBi := digitMask_eq_birth3 b hbd
  have hS := digitMask_eq_survival23 s hsd
  by_cases hc : ((∀ d ∈ b, d = 51) ∧ 51 ∈ b) ∧ ((∀ d ∈ s, d = 50 ∨ d = 51) ∧ 50 ∈ s ∧ 51 ∈ s)
  · rw [ite_eq_left hc, hBi.mpr hc.1, hS.mpr hc.2]; simp
  · rw [ite_eq_right hc]
    have : ¬ (b.foldl digitMaskStep 0 == birth3Mask && s.foldl digitMaskStep 0 == survival23Mask) = true := by
      simp only [Bool.and_eq_true, beq_iff_eq]
      rintro ⟨h1, h2⟩
      exact hc ⟨hBi.mp h1, hS.mp h2⟩
    rw [ite_eq_right this]

open Classical in
/--
A rule `<survival>/<birth>` after `prefix` is Conway's rules (0) exactly when the survival digits are {2, 3} and
the birth digits are {3}, in any order and with repeats, and another rule (3) otherwise.
-/
theorem checkRLERule_digits (pre s b : List UInt8) (hs : s ≠ []) (hb : b ≠ [])
    (hsd : ∀ d ∈ s, isDigitByte d = true) (hbd : ∀ d ∈ b, isDigitByte d = true)
    (hsz : pre.length + s.length + b.length + 1 < 2 ^ 32) :
    checkRLERule ⟨(pre ++ (s ++ 47 :: b)).toArray⟩ pre.length.toUInt32
        (⟨(pre ++ (s ++ 47 :: b)).toArray⟩ : ByteArray).size.toUInt32 =
      if ((∀ d ∈ s, d = 50 ∨ d = 51) ∧ 50 ∈ s ∧ 51 ∈ s) ∧ ((∀ d ∈ b, d = 51) ∧ 51 ∈ b) then 0 else 3 := by
  obtain ⟨d0, ds, rfl⟩ : ∃ d0 ds, s = d0 :: ds := by
    cases s with
    | nil => exact absurd rfl hs
    | cons d0 ds => exact ⟨d0, ds, rfl⟩
  have hd0 : isDigitByte d0 = true := hsd d0 (by simp)
  generalize hS : d0 :: ds = s at hsd hs hsz ⊢
  generalize hL : pre ++ (s ++ 47 :: b) = L
  have hLlen : L.length = pre.length + s.length + b.length + 1 := by rw [← hL]; simp; omega
  have hsize : (⟨L.toArray⟩ : ByteArray).size = L.length := size_of_list L
  have hB32 : (⟨L.toArray⟩ : ByteArray).size < 2 ^ 32 := by omega
  have hlimit : (⟨L.toArray⟩ : ByteArray).size.toUInt32.toNat = L.length := by rw [u32_size_toNat hB32, hsize]
  have hget : ∀ k, k < L.length → (⟨L.toArray⟩ : ByteArray).get! k = L[k]! := get!_of_list L
  have hidx : ∀ k, k ≤ L.length → k.toUInt32.toNat = k := fun k hk => u32_size_toNat (by omega)
  have hslen : 0 < s.length := List.length_pos_iff.mpr hs
  unfold checkRLERule
  have hp0 : skipSpaces ⟨L.toArray⟩ pre.length.toUInt32 (⟨L.toArray⟩ : ByteArray).size.toUInt32 =
      pre.length.toUInt32 := by
    apply skipSpaces_of_not_space _ hB32 _ (by rw [hidx _ (by omega), hsize]; omega)
    intro y hy
    rw [hidx _ (by omega), bytesFrom_of_list, ← hL, List.drop_left, ← hS] at hy
    simp at hy; subst hy; exact isDigitByte_not_space hd0
  rw [hp0]
  have hg0 : (⟨L.toArray⟩ : ByteArray).get! pre.length.toUInt32.toNat = d0 := by
    rw [hidx _ (by omega), hget _ (by omega), ← hL, getElem!_pos _ _ (by simp; omega)]
    rw [List.getElem_append_right (by omega)]; simp only [Nat.sub_self, ← hS]; rfl
  have hnotB : isLetterByte d0 98 = false := by
    have := (isDigitByte_iff d0).mp hd0
    have h1 : d0 ≠ 98 := by intro h; subst h; simp at this
    have h2 : d0 ≠ 66 := by intro h; subst h; simp at this
    simp [isLetterByte, h1, h2]
  simp only [hg0, hnotB, Bool.and_false, Bool.false_eq_true, ite_false]
  -- The survival digits.
  obtain ⟨he1, hm1⟩ := scanDigitSet_list L (by omega) pre.length s (47 :: b)
    (by rw [← hL]; simp) hsd (by intro y hy; simp at hy; subst hy; decide) (by omega)
  generalize hsc1 : scanDigitSet ⟨L.toArray⟩ (⟨L.toArray⟩ : ByteArray).size.toUInt32 pre.length.toUInt32 0 = r1
    at he1 hm1
  obtain ⟨e1, m1⟩ := r1
  simp only at he1 hm1 ⊢
  have hne1 : ¬ (e1 == pre.length.toUInt32) = true := by
    intro h; have := congrArg UInt32.toNat (beq_iff_eq.mp h); rw [he1, hidx _ (by omega)] at this; omega
  have hlt1 : e1 < (⟨L.toArray⟩ : ByteArray).size.toUInt32 := by rw [UInt32.lt_iff_toNat_lt, hlimit]; omega
  have hg1 : (⟨L.toArray⟩ : ByteArray).get! e1.toNat = 47 := by
    rw [hget _ (by omega), he1, ← hL, getElem!_pos _ _ (by simp only [List.length_append, List.length_cons]; omega)]
    rw [List.getElem_append_right (by omega)]
    simp only [show pre.length + s.length - pre.length = s.length by omega]
    rw [List.getElem_append_right (Nat.le_refl _)]
    simp
  simp only [hne1, decide_true, hlt1, Bool.not_true, hg1, bne_self_eq_false, Bool.or_false,
    Bool.false_eq_true, ite_false, Bool.not_false, Bool.true_or]
  -- The birth digits.
  have hs2 : e1 + 1 = (pre.length + s.length + 1).toUInt32 := by
    apply UInt32.toNat_inj.mp; rw [UInt32.toNat_add, he1, hidx _ (by omega)]; simp; omega
  rw [hs2]
  obtain ⟨he2, hm2⟩ := scanDigitSet_list L (by omega) (pre.length + s.length + 1) b []
    (by rw [← hL, List.append_nil, show pre.length + s.length + 1 = pre.length + (s.length + 1) by omega,
      ← List.drop_drop]; simp) hbd (by simp) (by omega)
  generalize hsc2 : scanDigitSet ⟨L.toArray⟩ (⟨L.toArray⟩ : ByteArray).size.toUInt32
    (pre.length + s.length + 1).toUInt32 0 = r2 at he2 hm2
  obtain ⟨e2, m2⟩ := r2
  simp only at he2 hm2 ⊢
  have hblen : 0 < b.length := List.length_pos_iff.mpr hb
  have hne2 : ¬ (e2 == (pre.length + s.length + 1).toUInt32) = true := by
    intro h; have := congrArg UInt32.toNat (beq_iff_eq.mp h); rw [he2, hidx _ (by omega)] at this; omega
  have heq : e2 = (⟨L.toArray⟩ : ByteArray).size.toUInt32 := by
    apply UInt32.toNat_inj.mp; rw [he2, hlimit]; omega
  have hend : skipSpaces ⟨L.toArray⟩ e2 (⟨L.toArray⟩ : ByteArray).size.toUInt32 =
      (⟨L.toArray⟩ : ByteArray).size.toUInt32 := by
    rw [heq]
    apply skipSpaces_of_not_space _ hB32 _ (by rw [hlimit, hsize]; exact Nat.le_refl _)
    intro y hy; rw [hlimit, bytesFrom_of_list, List.drop_length] at hy; simp at hy
  simp only [hne2, hend, bne_self_eq_false, Bool.or_false, Bool.false_eq_true, ite_false]
  rw [hm1, hm2]
  have hBi := digitMask_eq_birth3 b hbd
  have hSu := digitMask_eq_survival23 s hsd
  by_cases hc : ((∀ d ∈ s, d = 50 ∨ d = 51) ∧ 50 ∈ s ∧ 51 ∈ s) ∧ ((∀ d ∈ b, d = 51) ∧ 51 ∈ b)
  · rw [ite_eq_left hc, hBi.mpr hc.2, hSu.mpr hc.1]; simp
  · rw [ite_eq_right hc]
    have : ¬ (b.foldl digitMaskStep 0 == birth3Mask && s.foldl digitMaskStep 0 == survival23Mask) = true := by
      simp only [Bool.and_eq_true, beq_iff_eq]
      rintro ⟨h1, h2⟩
      exact hc ⟨hSu.mp h2, hBi.mp h1⟩
    rw [ite_eq_right this]

/-! ## Runs -/

/-- The cells `k` until `n` of an alive run starting at (`x`, `y`). -/
def runCells (x y : Int32) (k n : Nat) : List (Int32 × Int32) :=
  (List.range' k (n - k)).map (fun j => (x + j.toUInt32.toInt32, y))

/--
The cells of runs `(tag, count)` (tag 2: alive, 1: dead, otherwise: end of row) from (`x`, `y`), with rows starting
at `sx`.
-/
def decodeRuns (sx : Int32) : List (UInt32 × UInt32) → Int32 → Int32 → List (Int32 × Int32)
  | [], _, _ => []
  | (t, n) :: rs, x, y =>
    if t == 2 then runCells x y 0 n.toNat ++ decodeRuns sx rs (x + n.toInt32) y
    else if t == 1 then decodeRuns sx rs (x + n.toInt32) y
    else decodeRuns sx rs sx (y + n.toInt32)

theorem runCells_of_lt (x y : Int32) (k n : Nat) (h : k < n) :
    runCells x y k n = (x + k.toUInt32.toInt32, y) :: runCells x y (k + 1) n := by
  unfold runCells
  rw [show n - k = (n - (k + 1)) + 1 by omega, List.range'_succ, List.map_cons]

theorem runCells_of_ge (x y : Int32) (k n : Nat) (h : n ≤ k) : runCells x y k n = [] := by
  simp [runCells, show n - k = 0 by omega]

theorem expandRuns_alive (runs : Array (UInt32 × UInt32)) (numRuns j : UInt32) (hj : j < numRuns) (count : UInt32)
    (hrun : runs[j.toNat]! = (2, count)) (x y sx : Int32) :
    ∀ (m : Nat) (k : UInt32) (cells : GrowBuf (Int32 × Int32)) (a : Array (Int32 × Int32)),
      count.toNat - k.toNat = m → k.toNat ≤ count.toNat → cells.Rep a → a.size + (count.toNat - k.toNat) < 2 ^ 31 →
      ∃ cells', cells'.Rep (a ++ (runCells x y k.toNat count.toNat).toArray) ∧
        expandRuns runs numRuns j k x y sx cells = expandRuns runs numRuns (j + 1) 0 (x + count.toInt32) y sx cells' := by
  intro m
  induction m with
  | zero =>
    intro k cells a hm hk hrep ha
    have hnot : ¬ k < count := by rw [UInt32.lt_iff_toNat_lt]; omega
    refine ⟨cells, by rw [runCells_of_ge _ _ _ _ (by omega)]; simpa using hrep, ?_⟩
    rw [expandRuns]
    simp only [hj, ↓reduceDIte, hrun, show ((2 : UInt32) == 2) = true from rfl, ite_true, hnot]
  | succ m ih =>
    intro k cells a hm hk hrep ha
    have hlt : k < count := by rw [UInt32.lt_iff_toNat_lt]; omega
    have hsucc : (k + 1).toNat = k.toNat + 1 := by
      rw [UInt32.toNat_add]; have := UInt32.toNat_lt count; simp only [UInt32.toNat_one]; omega
    rw [expandRuns]
    simp only [hj, ↓reduceDIte, hrun, show ((2 : UInt32) == 2) = true from rfl, ite_true, hlt]
    obtain ⟨c', hc', heq⟩ := ih (k + 1) _ _ (by omega) (by omega) (GrowBuf.rep_push hrep (x + k.toInt32, y) (by omega))
      (by simp only [Array.size_push]; omega)
    refine ⟨c', ?_, heq⟩
    rw [runCells_of_lt _ _ _ _ (by omega)]
    rw [hsucc] at hc'
    have hk' : k.toNat.toUInt32 = k := by apply UInt32.toNat_inj.mp; rw [u32_size_toNat (UInt32.toNat_lt _)]
    simpa [hk'] using hc'

theorem runCells_length (x y : Int32) (k n : Nat) : (runCells x y k n).length = n - k := by
  simp [runCells]

theorem expandRuns_spec (runs : Array (UInt32 × UInt32)) (hn : runs.size < 2 ^ 32) (sx : Int32) :
    ∀ (m : Nat) (j : Nat) (x y : Int32) (cells : GrowBuf (Int32 × Int32)) (a : Array (Int32 × Int32)),
      runs.size - j = m → j ≤ runs.size → cells.Rep a →
      a.size + (decodeRuns sx (runs.toList.drop j) x y).length < 2 ^ 31 →
      (expandRuns runs runs.size.toUInt32 j.toUInt32 0 x y sx cells).Rep
        (a ++ (decodeRuns sx (runs.toList.drop j) x y).toArray) := by
  intro m
  induction m with
  | zero =>
    intro j x y cells a hm hj hrep _
    have hnot : ¬ j.toUInt32 < runs.size.toUInt32 := by
      rw [u32_lt_size_iff hn, u32_size_toNat (by omega)]; omega
    rw [expandRuns]
    simp only [hnot, ↓reduceDIte, List.drop_eq_nil_of_le (show runs.toList.length ≤ j by simp; omega), decodeRuns]
    simpa using hrep
  | succ m ih =>
    intro j x y cells a hm hj hrep ha
    have hlt : j < runs.size := by omega
    have hjU : j.toUInt32.toNat = j := u32_size_toNat (by omega)
    have hyes : j.toUInt32 < runs.size.toUInt32 := by rw [u32_lt_size_iff hn, hjU]; exact hlt
    have hnext : j.toUInt32 + 1 = (j + 1).toUInt32 := by
      apply UInt32.toNat_inj.mp; rw [UInt32.toNat_add, hjU, u32_size_toNat (by omega)]; simp; omega
    have hdrop : runs.toList.drop j = runs[j] :: runs.toList.drop (j + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hlt), Array.getElem_toList]
    generalize hr : runs[j] = run at hdrop
    obtain ⟨t, c⟩ := run
    have hrun : runs[j.toUInt32.toNat]! = (t, c) := by rw [hjU, getElem!_pos runs j hlt, hr]
    rw [hdrop] at ha ⊢
    simp only [decodeRuns] at ha ⊢
    by_cases h2 : t == 2
    · simp only [h2, ite_true] at ha ⊢
      have hrun2 : runs[j.toUInt32.toNat]! = (2, c) := by rw [hrun, beq_iff_eq.mp h2]
      have hrl := runCells_length x y 0 c.toNat
      simp only [List.length_append] at ha
      obtain ⟨c', hc', heq⟩ := expandRuns_alive runs runs.size.toUInt32 j.toUInt32 hyes c hrun2 x y sx _ 0 cells a
        rfl (by simp) hrep (by simp; omega)
      rw [heq, hnext]
      have := ih (j + 1) (x + c.toInt32) y c' _ (by omega) (by omega) hc' (by simp at ha ⊢; omega)
      simpa [Array.append_assoc] using this
    · have hrunt : runs[j.toUInt32.toNat]! = (t, c) := hrun
      by_cases h1 : t == 1
      · simp only [h2, h1, Bool.false_eq_true, ite_false, ite_true] at ha ⊢
        rw [expandRuns]
        simp only [hyes, ↓reduceDIte, hrunt, h2, h1, Bool.false_eq_true, ite_false, ite_true, hnext]
        exact ih (j + 1) _ y cells a (by omega) (by omega) hrep ha
      · simp only [h2, h1, Bool.false_eq_true, ite_false] at ha ⊢
        rw [expandRuns]
        simp only [hyes, ↓reduceDIte, hrunt, h2, h1, Bool.false_eq_true, ite_false, hnext]
        exact ih (j + 1) _ _ cells a (by omega) (by omega) hrep ha

/-! ## Equivalent runs -/

/-- Where decoding runs ends. -/
def decodeEnd (sx : Int32) : List (UInt32 × UInt32) → Int32 → Int32 → Int32 × Int32
  | [], x, y => (x, y)
  | (t, n) :: rs, x, y =>
    if t == 2 then decodeEnd sx rs (x + n.toInt32) y
    else if t == 1 then decodeEnd sx rs (x + n.toInt32) y
    else decodeEnd sx rs sx (y + n.toInt32)

theorem decodeRuns_append (sx : Int32) (l1 l2 : List (UInt32 × UInt32)) : ∀ x y,
    decodeRuns sx (l1 ++ l2) x y =
      decodeRuns sx l1 x y ++ decodeRuns sx l2 (decodeEnd sx l1 x y).1 (decodeEnd sx l1 x y).2 := by
  induction l1 with
  | nil => intro x y; rfl
  | cons r rs ih =>
    intro x y
    obtain ⟨t, n⟩ := r
    simp only [List.cons_append, decodeRuns, decodeEnd]
    split
    · simp [ih]
    · split <;> simp [ih]

theorem decodeEnd_append (sx : Int32) (l1 l2 : List (UInt32 × UInt32)) : ∀ x y,
    decodeEnd sx (l1 ++ l2) x y = decodeEnd sx l2 (decodeEnd sx l1 x y).1 (decodeEnd sx l1 x y).2 := by
  induction l1 with
  | nil => intro x y; rfl
  | cons r rs ih =>
    intro x y
    obtain ⟨t, n⟩ := r
    simp only [List.cons_append, decodeEnd]
    split
    · simp [ih]
    · split <;> simp [ih]

/-- Runs that decode to the same cells and end at the same place, from anywhere. -/
def RunsEq (sx : Int32) (l1 l2 : List (UInt32 × UInt32)) : Prop :=
  ∀ x y, decodeRuns sx l1 x y = decodeRuns sx l2 x y ∧ decodeEnd sx l1 x y = decodeEnd sx l2 x y

theorem RunsEq.refl (sx : Int32) (l : List (UInt32 × UInt32)) : RunsEq sx l l := fun _ _ => ⟨rfl, rfl⟩

theorem RunsEq.trans {sx : Int32} {l1 l2 l3 : List (UInt32 × UInt32)} (h1 : RunsEq sx l1 l2) (h2 : RunsEq sx l2 l3) :
    RunsEq sx l1 l3 := fun x y => ⟨(h1 x y).1.trans (h2 x y).1, (h1 x y).2.trans (h2 x y).2⟩

theorem RunsEq.symm {sx : Int32} {l1 l2 : List (UInt32 × UInt32)} (h : RunsEq sx l1 l2) : RunsEq sx l2 l1 :=
  fun x y => ⟨(h x y).1.symm, (h x y).2.symm⟩

theorem RunsEq.append_left {sx : Int32} {l1 l2 : List (UInt32 × UInt32)} (p : List (UInt32 × UInt32))
    (h : RunsEq sx l1 l2) : RunsEq sx (p ++ l1) (p ++ l2) := by
  intro x y
  rw [decodeRuns_append, decodeRuns_append, decodeEnd_append, decodeEnd_append]
  exact ⟨by rw [(h _ _).1], (h _ _).2⟩

theorem RunsEq.append_right {sx : Int32} {l1 l2 : List (UInt32 × UInt32)} (q : List (UInt32 × UInt32))
    (h : RunsEq sx l1 l2) : RunsEq sx (l1 ++ q) (l2 ++ q) := by
  intro x y
  rw [decodeRuns_append, decodeRuns_append, decodeEnd_append, decodeEnd_append, (h x y).1, (h x y).2]
  exact ⟨rfl, rfl⟩

theorem uint32_toInt32_add_one (n : UInt32) : n.toInt32 + 1 = (n + 1).toInt32 := rfl

theorem runCells_succ (x y : Int32) (n : Nat) :
    runCells x y 0 (n + 1) = runCells x y 0 n ++ [(x + n.toUInt32.toInt32, y)] := by
  unfold runCells
  simp only [Nat.sub_zero, List.range'_concat, List.map_append, List.map_cons, List.map_nil, Nat.zero_add,
    Nat.one_mul]

/-- An alive or dead run followed by one more of its cells is the run with one more cell. -/
theorem runsEq_extend (sx : Int32) (t n : UInt32) (ht : t = 2 ∨ t = 1) (hn : n.toNat + 1 < 2 ^ 32) :
    RunsEq sx [(t, n), (t, 1)] [(t, n + 1)] := by
  intro x y
  have hn1 : (n + 1).toNat = n.toNat + 1 := by rw [UInt32.toNat_add]; simp; omega
  have hend : x + n.toInt32 + (1 : UInt32).toInt32 = x + (n + 1).toInt32 := by
    rw [Int32.add_assoc]; rfl
  rcases ht with rfl | rfl
  · simp only [decodeRuns, decodeEnd, show ((2 : UInt32) == 2) = true from rfl, ite_true, List.append_nil]
    refine ⟨?_, by rw [hend]⟩
    rw [hn1, runCells_succ]
    simp [runCells, show (1 : UInt32).toNat = 1 from rfl]
  · simp only [decodeRuns, decodeEnd, show ((1 : UInt32) == 2) = false from rfl, show ((1 : UInt32) == 1) = true from rfl,
      Bool.false_eq_true, ite_false, ite_true]
    exact ⟨trivial, by rw [hend]⟩

/-- A dead run just before an end of row doesn't matter. -/
theorem runsEq_drop_dead (sx : Int32) (n m : UInt32) : RunsEq sx [(1, n), (0, m)] [(0, m)] := by
  intro x y
  simp [decodeRuns, decodeEnd]

/-- Consecutive ends of rows merge. -/
theorem runsEq_merge_rowEnds (sx : Int32) (a b : UInt32) : RunsEq sx [(0, a), (0, b)] [(0, a + b)] := by
  intro x y
  simp only [decodeRuns, decodeEnd, show ((0 : UInt32) == 2) = false from rfl,
    show ((0 : UInt32) == 1) = false from rfl, Bool.false_eq_true, ite_false]
  refine ⟨trivial, ?_⟩
  rw [Int32.add_assoc]; rfl

/-! ## From the grid to run items -/

/-- The run of an item. -/
def itemRun (it : UInt8 × UInt32) : UInt32 × UInt32 :=
  (if it.1 == rleAlive then 2 else if it.1 == rleDead then 1 else 0, it.2)

/-- The items not emitted yet: the pending ends of rows, then the current run. -/
def pendItems (runTag : UInt8) (runLen rowEnds : UInt32) : List (UInt8 × UInt32) :=
  (if rowEnds = 0 then [] else [(rleRowEnd, rowEnds)]) ++ (if runLen = 0 then [] else [(runTag, runLen)])

/-- What one step of `gridItems` emits. -/
def stepEmitted (tag runTag : UInt8) (runLen rowEnds : UInt32) (rowEnd : Bool) : List (UInt8 × UInt32) :=
  let grows := runLen != 0 && tag == runTag
  let flush := runLen != 0 && !grows
  let rowEnds1 := if flush then 0 else rowEnds
  let curTag := if grows then runTag else tag
  let curLen := if grows then runLen + 1 else 1
  (if flush && rowEnds != 0 then [(rleRowEnd, rowEnds)] else []) ++ (if flush then [(runTag, runLen)] else []) ++
    (if rowEnd && curTag == rleAlive && rowEnds1 != 0 then [(rleRowEnd, rowEnds1)] else []) ++
    (if rowEnd && curTag == rleAlive then [(rleAlive, curLen)] else [])

/-- The pending items after one step of `gridItems`. -/
def stepPend (tag runTag : UInt8) (runLen rowEnds : UInt32) (rowEnd : Bool) : List (UInt8 × UInt32) :=
  let grows := runLen != 0 && tag == runTag
  let flush := runLen != 0 && !grows
  let rowEnds1 := if flush then 0 else rowEnds
  let curTag := if grows then runTag else tag
  let curLen := if grows then runLen + 1 else 1
  if rowEnd then pendItems rleDead 0 ((if curTag == rleAlive then 0 else rowEnds1) + 1)
  else pendItems curTag curLen rowEnds1

theorem itemRun_alive (n : UInt32) : itemRun (rleAlive, n) = (2, n) := rfl
theorem itemRun_dead (n : UInt32) : itemRun (rleDead, n) = (1, n) := rfl
theorem itemRun_rowEnd (n : UInt32) : itemRun (rleRowEnd, n) = (0, n) := rfl

theorem stepEmitted_pend (sx : Int32) (tag runTag : UInt8) (runLen rowEnds : UInt32) (rowEnd : Bool)
    (htag : tag = rleDead ∨ tag = rleAlive) (hrun : runLen ≠ 0 → runTag = rleDead ∨ runTag = rleAlive)
    (hlen : runLen.toNat + 1 < 2 ^ 32) (hends : rowEnds.toNat + 1 < 2 ^ 32) :
    RunsEq sx ((stepEmitted tag runTag runLen rowEnds rowEnd ++ stepPend tag runTag runLen rowEnds rowEnd).map itemRun)
      ((pendItems runTag runLen rowEnds ++ [(tag, 1)] ++ (if rowEnd then [(rleRowEnd, 1)] else [])).map itemRun) := by
  have hlen1 : (runLen + 1).toNat = runLen.toNat + 1 := by rw [UInt32.toNat_add]; simp; omega
  have hadd : ∀ x : Int32, x + runLen.toInt32 + (1 : UInt32).toInt32 = x + (runLen + 1).toInt32 := by
    intro x; rw [Int32.add_assoc]; rfl
  have hends1 : ∀ y : Int32, y + rowEnds.toInt32 + (1 : UInt32).toInt32 = y + (rowEnds + 1).toInt32 := by
    intro y; rw [Int32.add_assoc]; rfl
  have hrc : ∀ x y : Int32, runCells x y 0 (runLen.toNat + 1) =
      runCells x y 0 runLen.toNat ++ [(x + runLen.toNat.toUInt32.toInt32, y)] := fun x y => runCells_succ x y _
  have hk : runLen.toNat.toUInt32 = runLen := by apply UInt32.toNat_inj.mp; rw [u32_size_toNat (UInt32.toNat_lt _)]
  have hne1 : runLen + 1 ≠ 0 := by intro h; have := congrArg UInt32.toNat h; rw [hlen1] at this; simp at this
  have hne2 : rowEnds + 1 ≠ 0 := by
    intro h; have := congrArg UInt32.toNat h; rw [UInt32.toNat_add] at this; simp at this; omega
  have hmod : (runLen.toNat + 1) % 4294967296 = runLen.toNat + 1 := Nat.mod_eq_of_lt hlen
  have hof : Int32.ofNat runLen.toNat = runLen.toInt32 := by rw [← UInt32.toInt32_ofNat', UInt32.ofNat_toNat]
  rcases htag with rfl | rfl <;> by_cases hz : runLen = 0 <;> by_cases hr0 : rowEnds = 0 <;> cases rowEnd
  all_goals
    try (have hrt := hrun hz; rcases hrt with rfl | rfl)
  all_goals
    simp_all [stepEmitted, stepPend, pendItems, itemRun, rleAlive, rleDead, rleRowEnd, RunsEq, decodeRuns,
      decodeEnd, runCells, List.range'_concat]
  all_goals
    intros
    rw [Nat.mod_eq_of_lt (by omega), List.range'_concat]
    simp [hof]

/-- The raw items of grid cells before `k`: one per cell, and an end of row after each row. -/
def rawItems (g : AsciiBytes) (W : Nat) : Nat → List (UInt8 × UInt32)
  | 0 => []
  | k + 1 => rawItems g W k ++ [(g.1[k]!, 1)] ++ (if (k + 1) % W = 0 then [(rleRowEnd, 1)] else [])

theorem GrowBuf.rep_push_if {α : Type} {b : GrowBuf α} {a : Array α} (h : b.Rep a) (c : Bool) (x : α)
    (hs : a.size + 1 < 2 ^ 31) : (if c then b.push x else b).Rep (a ++ (if c then [x] else []).toArray) := by
  cases c
  · simpa using h
  · simpa using GrowBuf.rep_push h x hs

theorem gridItems_step (g : AsciiBytes) (w total k : UInt32) (runTag : UInt8) (runLen rowEnds : UInt32)
    (items : GrowBuf (UInt8 × UInt32)) (hk : k < total) :
    gridItems g w total k runTag runLen rowEnds items =
      let tag := g.1.get! k.toNat
      let grows := runLen != 0 && tag == runTag
      let flush := runLen != 0 && !grows
      let items1 := if flush && rowEnds != 0 then items.push (rleRowEnd, rowEnds) else items
      let items2 := if flush then items1.push (runTag, runLen) else items1
      let rowEnds1 := if flush then 0 else rowEnds
      let curTag := if grows then runTag else tag
      let curLen := if grows then runLen + 1 else 1
      if (k + 1) % w == 0 then
        let emit := curTag == rleAlive
        let items3 := if emit && rowEnds1 != 0 then items2.push (rleRowEnd, rowEnds1) else items2
        let items4 := if emit then items3.push (rleAlive, curLen) else items3
        gridItems g w total (k + 1) rleDead 0 ((if emit then 0 else rowEnds1) + 1) items4
      else gridItems g w total (k + 1) curTag curLen rowEnds1 items2 := by
  rw [gridItems]
  simp only [hk, ↓reduceDIte]

/-- A valid item that isn't the end: a tag `o`, `b` or `$` and a count that fits. -/
def ValidItem (it : UInt8 × UInt32) : Prop :=
  (it.1 = rleAlive ∨ it.1 = rleDead ∨ it.1 = rleRowEnd) ∧ 1 ≤ it.2.toNat ∧ it.2.toNat ≤ 2147483647

theorem stepEmitted_valid (tag runTag : UInt8) (runLen rowEnds : UInt32) (rowEnd : Bool)
    (htag : tag = rleDead ∨ tag = rleAlive) (hrun : runLen ≠ 0 → runTag = rleDead ∨ runTag = rleAlive)
    (hlen : runLen.toNat + 1 < 2 ^ 31) (hends : rowEnds.toNat < 2 ^ 31) :
    ∀ it ∈ stepEmitted tag runTag runLen rowEnds rowEnd, ValidItem it := by
  have hlen1 : (runLen + 1).toNat = runLen.toNat + 1 := by rw [UInt32.toNat_add]; simp; omega
  have hz' : runLen ≠ 0 → 1 ≤ runLen.toNat := fun h => by
    have : runLen.toNat ≠ 0 := fun h' => h (UInt32.toNat_inj.mp (by rw [h']; rfl))
    omega
  have hr' : rowEnds ≠ 0 → 1 ≤ rowEnds.toNat := fun h => by
    have : rowEnds.toNat ≠ 0 := fun h' => h (UInt32.toNat_inj.mp (by rw [h']; rfl))
    omega
  have hle : ∀ (c : Prop) [Decidable c], (if c then (0 : UInt32) else rowEnds).toNat ≤ rowEnds.toNat := by
    intro c _; split <;> simp
  intro ⟨t, n⟩ hit
  have hv : ∀ (t' : UInt8) (n' : UInt32), (t' = rleAlive ∨ t' = rleDead ∨ t' = rleRowEnd) → 1 ≤ n'.toNat →
      n'.toNat ≤ 2147483647 → ValidItem (t', n') := fun _ _ h1 h2 h3 => ⟨h1, h2, h3⟩
  rcases htag with rfl | rfl <;> by_cases hz : runLen = 0
  all_goals first | (have hrt := hrun ‹runLen ≠ 0›; rcases hrt with rfl | rfl) | skip
  all_goals by_cases hr0 : rowEnds = 0
  all_goals cases rowEnd
  all_goals simp [stepEmitted, hz, hr0, rleAlive, rleDead, rleRowEnd] at hit
  all_goals
    rcases hit with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    refine hv _ _ (by decide) ?_ ?_ <;> (try subst_vars) <;> first | omega | (have := hz' ‹_›; omega) | (have := hr' ‹_›; omega) | (simp_all; done) | (simp_all; omega)

theorem toNat_ite_zero_le {p : Prop} [Decidable p] (x : UInt32) : (if p then (0 : UInt32) else x).toNat ≤ x.toNat := by
  split <;> simp

theorem gridItems_spec (sx : Int32) (g : AsciiBytes) (w total : UInt32)
    (hgs : g.1.size = total.toNat) (hT : 8 * total.toNat < 2 ^ 31) (hdiv : total.toNat % w.toNat = 0)
    (hg : ∀ k, k < total.toNat → g.1[k]! = rleDead ∨ g.1[k]! = rleAlive) :
    ∀ (n : Nat) (k : UInt32) (runTag : UInt8) (runLen rowEnds : UInt32) (items : GrowBuf (UInt8 × UInt32))
      (a : Array (UInt8 × UInt32)),
      total.toNat - k.toNat = n → k.toNat ≤ total.toNat → items.Rep a → a.size ≤ 4 * k.toNat →
      runLen.toNat ≤ k.toNat → rowEnds.toNat ≤ k.toNat → (runLen ≠ 0 → runTag = rleDead ∨ runTag = rleAlive) →
      (k.toNat % w.toNat = 0 → runLen = 0) → (∀ it ∈ a.toList, ValidItem it) →
      RunsEq sx ((a.toList ++ pendItems runTag runLen rowEnds).map itemRun) ((rawItems g w.toNat k.toNat).map itemRun) →
      ∃ (a' : Array (UInt8 × UInt32)) (re : UInt32), (gridItems g w total k runTag runLen rowEnds items).Rep a' ∧
        RunsEq sx ((a'.toList ++ pendItems rleDead 0 re).map itemRun)
          ((rawItems g w.toNat total.toNat).map itemRun) ∧ (∀ it ∈ a'.toList, ValidItem it) ∧
          a'.size ≤ 4 * total.toNat := by
  intro n
  induction n with
  | zero =>
    intro k runTag runLen rowEnds items a hn hk hrep ha _ _ _ hmod hval heq
    have hkT : k.toNat = total.toNat := by omega
    have hnot : ¬ k < total := by rw [UInt32.lt_iff_toNat_lt]; omega
    have h0 : runLen = 0 := hmod (by rw [hkT]; exact hdiv)
    refine ⟨a, rowEnds, ?_, ?_, hval, by omega⟩
    · rw [gridItems]; simp only [hnot, ↓reduceDIte]; exact hrep
    · rw [← hkT]; subst h0; simpa [pendItems] using heq
  | succ n ih =>
    intro k runTag runLen rowEnds items a hn hk hrep ha hlen hends hrun hmod hval heq
    have hlt : k < total := by rw [UInt32.lt_iff_toNat_lt]; omega
    have hkT : k.toNat < total.toNat := by omega
    have hsucc : (k + 1).toNat = k.toNat + 1 := by rw [UInt32.toNat_add]; simp; omega
    rw [gridItems_step g w total k runTag runLen rowEnds items hlt]
    -- The cell and whether its row ends here.
    have htag0 : g.1.get! k.toNat = g.1[k.toNat]! := by
      rw [byteArray_get!_eq (by omega), getElem!_pos g.1 _ (by omega)]
    rw [htag0]
    generalize htg : g.1[k.toNat]! = tag
    have htag : tag = rleDead ∨ tag = rleAlive := htg ▸ hg _ hkT
    have hvalid : ∀ (re : Bool) (L : List (UInt8 × UInt32)), L = a.toList ++ stepEmitted tag runTag runLen rowEnds re →
        ∀ it ∈ L, ValidItem it := fun re L hL it hit => by
      have hv := stepEmitted_valid tag runTag runLen rowEnds re htag hrun (by omega) (by omega)
      rw [hL, List.mem_append] at hit
      exact hit.elim (hval it) (hv it)
    have hre : ((k + 1) % w == 0) = decide ((k.toNat + 1) % w.toNat = 0) := by
      have hm : ((k + 1) % w).toNat = (k.toNat + 1) % w.toNat := by rw [UInt32.toNat_mod, hsucc]
      by_cases h : (k.toNat + 1) % w.toNat = 0
      · have : (k + 1) % w = 0 := UInt32.toNat_inj.mp (by rw [hm, h]; rfl)
        simp [this, h]
      · have : (k + 1) % w ≠ 0 := fun h' => h (by rw [← hm, h']; rfl)
        simp [this, h]
    rw [hre]
    -- The items after the step.
    have hchain : ∀ (E P R : List (UInt8 × UInt32)),
        RunsEq sx ((E ++ P).map itemRun) ((pendItems runTag runLen rowEnds ++ R).map itemRun) →
        RunsEq sx ((a.toList ++ E ++ P).map itemRun) ((rawItems g w.toNat k.toNat ++ R).map itemRun) := by
      intro E P R h
      have h1 := RunsEq.append_left (a.toList.map itemRun) h
      have h2 := RunsEq.append_right (R.map itemRun) heq
      simp only [List.map_append, List.append_assoc] at h1 h2 ⊢
      exact h1.trans h2
    have hif : ∀ (c : Bool) (x : UInt8 × UInt32), (if c then [x] else []).toArray.size ≤ 1 := by
      intro c x; cases c <;> simp
    have hgr : (runLen != 0 && tag == runTag) = true → runTag = rleDead ∨ runTag = rleAlive := by
      intro h; simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h; exact hrun h.1
    have r1 := GrowBuf.rep_push_if hrep (runLen != 0 && !(runLen != 0 && tag == runTag) && rowEnds != 0)
      (rleRowEnd, rowEnds) (show a.size + 1 < 2 ^ 31 by omega)
    have r2 := GrowBuf.rep_push_if r1 (runLen != 0 && !(runLen != 0 && tag == runTag)) (runTag, runLen) (by
      rw [Array.size_append]; have := hif (runLen != 0 && !(runLen != 0 && tag == runTag) && rowEnds != 0)
        (rleRowEnd, rowEnds); omega)
    by_cases hrow : (k.toNat + 1) % w.toNat = 0
    · simp only [hrow, decide_true, ite_true]
      have hstep := stepEmitted_pend sx tag runTag runLen rowEnds true htag hrun (by omega) (by omega)
      have r3 := GrowBuf.rep_push_if r2 ((if (runLen != 0 && tag == runTag) = true then runTag else tag) == rleAlive &&
        (if (runLen != 0 && !(runLen != 0 && tag == runTag)) = true then 0 else rowEnds) != 0) (rleRowEnd, if (runLen != 0 && !(runLen != 0 && tag == runTag)) = true then 0
        else rowEnds) (by
          rw [Array.size_append, Array.size_append]
          have := hif (runLen != 0 && !(runLen != 0 && tag == runTag) && rowEnds != 0) (rleRowEnd, rowEnds)
          have := hif (runLen != 0 && !(runLen != 0 && tag == runTag)) (runTag, runLen); omega)
      have r4 := GrowBuf.rep_push_if r3 ((if (runLen != 0 && tag == runTag) = true then runTag else tag) == rleAlive)
        (rleAlive, if (runLen != 0 && tag == runTag) = true then runLen + 1 else 1) (by
          rw [Array.size_append, Array.size_append, Array.size_append]
          have := hif (runLen != 0 && !(runLen != 0 && tag == runTag) && rowEnds != 0) (rleRowEnd, rowEnds)
          have := hif (runLen != 0 && !(runLen != 0 && tag == runTag)) (runTag, runLen)
          have := hif ((if (runLen != 0 && tag == runTag) = true then runTag else tag) == rleAlive &&
            (if (runLen != 0 && !(runLen != 0 && tag == runTag)) = true then 0 else rowEnds) != 0)
            (rleRowEnd, if (runLen != 0 && !(runLen != 0 && tag == runTag)) = true then 0 else rowEnds)
          omega)
      have hraw : rawItems g w.toNat (k.toNat + 1) = rawItems g w.toNat k.toNat ++ [(tag, 1), (rleRowEnd, 1)] := by
        simp [rawItems, htg, hrow]
      refine ih (k + 1) rleDead 0 _ _ _ (by omega) (by omega) r4 ?_ (by simp) ?_ (by simp) (by simp) ?_ ?_
      · simp only [Array.size_append]
        have := hif (runLen != 0 && !(runLen != 0 && tag == runTag) && rowEnds != 0) (rleRowEnd, rowEnds)
        have := hif (runLen != 0 && !(runLen != 0 && tag == runTag)) (runTag, runLen)
        have := hif ((if (runLen != 0 && tag == runTag) = true then runTag else tag) == rleAlive &&
          (if (runLen != 0 && !(runLen != 0 && tag == runTag)) = true then 0 else rowEnds) != 0)
          (rleRowEnd, if (runLen != 0 && !(runLen != 0 && tag == runTag)) = true then 0 else rowEnds)
        have := hif ((if (runLen != 0 && tag == runTag) = true then runTag else tag) == rleAlive)
          (rleAlive, if (runLen != 0 && tag == runTag) = true then runLen + 1 else 1)
        rw [hsucc]; omega
      · rw [hsucc, UInt32.toNat_add]
        generalize hX : (if ((if (runLen != 0 && tag == runTag) = true then runTag else tag) == rleAlive) = true then
          (0 : UInt32) else if (runLen != 0 && !(runLen != 0 && tag == runTag)) = true then 0 else rowEnds) = X
        have : X.toNat ≤ rowEnds.toNat := by
          rw [← hX]
          exact Nat.le_trans (toNat_ite_zero_le _) (toNat_ite_zero_le _)
        simp; omega
      · apply hvalid true
        simp [stepEmitted, List.append_assoc]
      · rw [hsucc, hraw]
        have := hchain (stepEmitted tag runTag runLen rowEnds true) (stepPend tag runTag runLen rowEnds true)
          [(tag, 1), (rleRowEnd, 1)] (by simpa using hstep)
        have key : ∀ L, L = a.toList ++ stepEmitted tag runTag runLen rowEnds true ++ stepPend tag runTag runLen rowEnds true →
            RunsEq sx (L.map itemRun) ((rawItems g w.toNat k.toNat ++ [(tag, 1), (rleRowEnd, 1)]).map itemRun) := fun L hL => hL ▸ this
        apply key
        simp [stepEmitted, stepPend, List.append_assoc]
    · simp only [hrow, decide_false, Bool.false_eq_true, ite_false]
      have hstep := stepEmitted_pend sx tag runTag runLen rowEnds false htag hrun (by omega) (by omega)
      have hraw : rawItems g w.toNat (k.toNat + 1) = rawItems g w.toNat k.toNat ++ [(tag, 1)] := by
        simp [rawItems, htg, hrow]
      refine ih (k + 1) _ _ _ _ _ (by omega) (by omega) r2 ?_ ?_ ?_ ?_ (by rw [hsucc]; intro h; exact absurd h hrow) ?_ ?_
      · simp only [Array.size_append]
        have := hif (runLen != 0 && !(runLen != 0 && tag == runTag) && rowEnds != 0) (rleRowEnd, rowEnds)
        have := hif (runLen != 0 && !(runLen != 0 && tag == runTag)) (runTag, runLen)
        rw [hsucc]; omega
      · rw [hsucc]
        split
        · rename_i hg'
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hg'
          rw [UInt32.toNat_add]; simp; omega
        · simp
      · rw [hsucc]; have := toNat_ite_zero_le (p := (runLen != 0 && !(runLen != 0 && tag == runTag)) = true) rowEnds
        omega
      · intro _
        split
        · rename_i hg'; exact hgr hg'
        · exact htag
      · apply hvalid false
        simp [stepEmitted]
      · rw [hsucc, hraw]
        have := hchain (stepEmitted tag runTag runLen rowEnds false) (stepPend tag runTag runLen rowEnds false)
          [(tag, 1)] (by simpa using hstep)
        have key : ∀ L, L = a.toList ++ stepEmitted tag runTag runLen rowEnds false ++ stepPend tag runTag runLen rowEnds false →
            RunsEq sx (L.map itemRun) ((rawItems g w.toNat k.toNat ++ [(tag, 1)]).map itemRun) := fun L hL => hL ▸ this
        apply key
        simp [stepEmitted, stepPend, List.append_assoc]

/-- The alive cells of grid cells before `k`, row by row, in the box at (`minX`, `minY`) with rows of `W` cells. -/
def gridCells (g : AsciiBytes) (W : Nat) (minX minY : Int32) (k : Nat) : List (Int32 × Int32) :=
  (List.range k).flatMap (fun j =>
    if g.1[j]! = rleAlive then [(minX + (j % W).toUInt32.toInt32, minY + (j / W).toUInt32.toInt32)] else [])

theorem nat_toUInt32_toInt32_succ (n : Nat) : (n + 1).toUInt32.toInt32 = n.toUInt32.toInt32 + 1 := by
  have : (n + 1).toUInt32 = n.toUInt32 + 1 := by
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_add, Nat.toUInt32_eq, Nat.toUInt32_eq, UInt32.toNat_ofNat', UInt32.toNat_ofNat']
    simp
  rw [this]; rfl

theorem rawItems_decode (g : AsciiBytes) (W : Nat) (hW : 1 ≤ W) (minX minY : Int32) (hbytes : ∀ j, j < g.1.size →
      g.1[j]! = rleDead ∨ g.1[j]! = rleAlive) :
    ∀ k, k ≤ g.1.size →
      decodeRuns minX ((rawItems g W k).map itemRun) minX minY = gridCells g W minX minY k ∧
        decodeEnd minX ((rawItems g W k).map itemRun) minX minY =
          (minX + (k % W).toUInt32.toInt32, minY + (k / W).toUInt32.toInt32) := by
  intro k
  induction k with
  | zero => intro _; simp [rawItems, gridCells, decodeRuns, decodeEnd]
  | succ k ih =>
    intro hk
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hgcells : gridCells g W minX minY (k + 1) = gridCells g W minX minY k ++
        (if g.1[k]! = rleAlive then [(minX + (k % W).toUInt32.toInt32, minY + (k / W).toUInt32.toInt32)] else []) := by
      simp [gridCells, List.range_succ, List.flatMap_append]
    simp only [rawItems, List.map_append, decodeRuns_append, decodeEnd_append, ih1, ih2, hgcells]
    have hc : (k % W + 1 = W ∧ (k + 1) % W = 0 ∧ (k + 1) / W = k / W + 1) ∨
        ((k + 1) % W = k % W + 1 ∧ (k + 1) / W = k / W ∧ ¬ (k + 1) % W = 0) := by
      have hlt := Nat.mod_lt k (show W > 0 by omega)
      have hdm := Nat.div_add_mod k W
      generalize k / W = q at hdm ⊢
      generalize k % W = r at hdm hlt ⊢
      subst hdm
      by_cases h : r + 1 = W
      · left
        have e : W * q + r + 1 = W * (q + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
        refine ⟨h, by rw [e, Nat.mul_mod_right], by rw [e, Nat.mul_div_cancel_left _ (by omega)]⟩
      · right
        have e : W * q + r + 1 = W * q + (r + 1) := by omega
        have hm : (W * q + (r + 1)) % W = r + 1 := by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
        refine ⟨by rw [e, hm], by rw [e, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega)]; simp,
          by rw [e, hm]; omega⟩
    rcases hbytes k (by omega) with hb | hb <;> rcases hc with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    all_goals
      simp [hb, h1, h2, h3, itemRun, rleAlive, rleDead, rleRowEnd, decodeRuns, decodeEnd, runCells,
        Int32.add_assoc]

/-! ## Lines -/

/-- The text of a line of items. -/
def lineOf (g : List (UInt8 × UInt32)) : String := g.foldl (fun s it => s ++ formatRLEItem it.1 it.2) ""

theorem decimalLength_le (n : UInt32) : 1 ≤ (decimalLength n).toNat ∧ (decimalLength n).toNat ≤ 10 := by
  unfold decimalLength
  repeat' split
  all_goals exact ⟨by decide, by decide⟩

theorem formatRLEItemLength_bounds (n : UInt32) :
    1 ≤ (formatRLEItemLength n).toNat ∧ (formatRLEItemLength n).toNat ≤ 11 := by
  unfold formatRLEItemLength
  split
  · decide
  · have := decimalLength_le n
    rw [UInt32.toNat_add]; simp; omega

theorem wrapRLEItems_spec (items : Array (UInt8 × UInt32)) (hn : items.size < 2 ^ 31) :
    ∀ (m j : Nat) (cur : List (UInt8 × UInt32)) (lineLen : UInt32) (out : GrowBuf String) (o : Array String),
      items.size - j = m → j ≤ items.size → lineLen.toNat ≤ 70 → (lineLen = 0 ↔ cur = []) → out.Rep o →
      o.size + (items.size - j) + 1 < 2 ^ 31 →
      ∃ groups : List (List (UInt8 × UInt32)), (∀ g ∈ groups, g ≠ []) ∧
        groups.flatten = cur ++ items.toList.drop j ∧
        (wrapRLEItems items items.size.toUInt32 j.toUInt32 (lineOf cur) lineLen out).Rep
          (o ++ (groups.map lineOf).toArray) := by
  have hn32 : items.size < 2 ^ 32 := by omega
  intro m
  induction m with
  | zero =>
    intro j cur lineLen out o hm hj _ hcur hrep _
    have hnot : ¬ j.toUInt32 < items.size.toUInt32 := by
      rw [u32_lt_size_iff hn32, u32_size_toNat (by omega)]; omega
    rw [wrapRLEItems]
    simp only [hnot, ↓reduceDIte]
    have hdrop : items.toList.drop j = [] := List.drop_eq_nil_of_le (by simp; omega)
    by_cases h0 : lineLen = 0
    · refine ⟨[], by simp, by simp [hdrop, hcur.mp h0], ?_⟩
      simp only [h0, bne_self_eq_false, Bool.false_eq_true, ite_false]
      simpa using hrep
    · have hne : cur ≠ [] := fun h => h0 (hcur.mpr h)
      refine ⟨[cur], by simpa using hne, by simp [hdrop], ?_⟩
      have : (lineLen != 0) = true := by simpa using h0
      simp only [this, ite_true]
      simpa using GrowBuf.rep_push hrep (lineOf cur) (by omega)
  | succ m ih =>
    intro j cur lineLen out o hm hj hlen hcur hrep ho
    have hlt : j < items.size := by omega
    have hjU : j.toUInt32.toNat = j := u32_size_toNat (by omega)
    have hyes : j.toUInt32 < items.size.toUInt32 := by rw [u32_lt_size_iff hn32, hjU]; exact hlt
    have hnext : j.toUInt32 + 1 = (j + 1).toUInt32 := by
      apply UInt32.toNat_inj.mp; rw [UInt32.toNat_add, hjU, u32_size_toNat (by omega)]; simp; omega
    have hdrop : items.toList.drop j = items[j] :: items.toList.drop (j + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hlt), Array.getElem_toList]
    rw [wrapRLEItems]
    simp only [hyes, ↓reduceDIte, hjU, getElem!_pos items j hlt, hnext]
    generalize hit : items[j] = it at hdrop
    obtain ⟨hl1, hl2⟩ := formatRLEItemLength_bounds it.2
    have hsum : (lineLen + formatRLEItemLength it.2).toNat = lineLen.toNat + (formatRLEItemLength it.2).toNat := by
      rw [UInt32.toNat_add]; omega
    by_cases hgt : lineLen + formatRLEItemLength it.2 > 70
    · have hgt' : lineLen.toNat + (formatRLEItemLength it.2).toNat > 70 := by
        rw [← hsum]; exact (show (70 : UInt32).toNat = 70 from rfl) ▸ UInt32.lt_iff_toNat_lt.mp hgt
      simp only [hgt, ite_true]
      have hne : cur ≠ [] := fun h => by have := hcur.mpr h; subst this; simp at hgt'; omega
      obtain ⟨gs, hgs, hflat, hres⟩ := ih (j + 1) [it] (formatRLEItemLength it.2) (out.push (lineOf cur))
        (o.push (lineOf cur)) (by omega) (by omega) (by omega)
        (by constructor
            · intro h; have := congrArg UInt32.toNat h; simp at this; omega
            · intro h; simp at h)
        (GrowBuf.rep_push hrep (lineOf cur) (by omega)) (by simp; omega)
      refine ⟨cur :: gs, ?_, ?_, ?_⟩
      · intro g hg; simp at hg; rcases hg with rfl | hg
        · exact hne
        · exact hgs g hg
      · rw [List.flatten_cons, hflat, hdrop]; simp
      · have : lineOf [it] = formatRLEItem it.1 it.2 := by simp [lineOf]
        rw [this] at hres
        simpa [Array.append_assoc] using hres
    · have hle : lineLen.toNat + (formatRLEItemLength it.2).toNat ≤ 70 := by
        have := mt UInt32.lt_iff_toNat_lt.mpr hgt; rw [hsum, show (70 : UInt32).toNat = 70 from rfl] at this; omega
      simp only [hgt, ite_false]
      have hline : lineOf cur ++ formatRLEItem it.1 it.2 = lineOf (cur ++ [it]) := by simp [lineOf, List.foldl_append]
      rw [hline]
      obtain ⟨gs, hgs, hflat, hres⟩ := ih (j + 1) (cur ++ [it]) (lineLen + formatRLEItemLength it.2) out o
        (by omega) (by omega) (by rw [hsum]; omega)
        (by constructor
            · intro h; have := congrArg UInt32.toNat h; rw [hsum] at this; simp at this; omega
            · intro h; simp at h) hrep (by omega)
      exact ⟨gs, hgs, by rw [hflat, hdrop]; simp, hres⟩

/-! ## Parsing items -/

/-- The byte of an item's tag. -/
def tagByte (t : UInt8) : UInt8 := if t == rleAlive then 111 else if t == rleDead then 98 else if t == rleRowEnd then 36 else 33

/-- The bytes of an item's text. -/
def itemBytes (it : UInt8 × UInt32) : List UInt8 :=
  (if it.2 == 1 then [] else natDigitBytes it.2.toNat) ++ [tagByte it.1]

/-- The text of an item's tag. -/
def tagText (t : UInt8) : String :=
  if t == rleAlive then "o" else if t == rleDead then "b" else if t == rleRowEnd then "$" else "!"

theorem bytes_tagText (t : UInt8) : (tagText t).toByteArray.data.toList = [tagByte t] := by
  unfold tagText tagByte
  split
  · rfl
  · split
    · rfl
    · split <;> rfl

theorem formatRLEItem_eq (t : UInt8) (n : UInt32) :
    formatRLEItem t n = if n == 1 then tagText t else toString n.toNat ++ tagText t := rfl

theorem bytes_formatRLEItem (t : UInt8) (n : UInt32) :
    (formatRLEItem t n).toByteArray.data.toList = itemBytes (t, n) := by
  rw [formatRLEItem_eq]
  unfold itemBytes
  by_cases hn : (n == 1) = true
  · rw [ite_eq_left hn, ite_eq_left hn, List.nil_append, bytes_tagText]
  · rw [ite_eq_right hn, ite_eq_right hn, String.toByteArray_append, byteArray_append_toList, Nat.toString_eq_repr,
      bytes_natRepr, bytes_tagText]

/-- The bytes of a line of items. -/
theorem bytes_lineOf (g : List (UInt8 × UInt32)) : (lineOf g).toByteArray.data.toList = g.flatMap itemBytes := by
  unfold lineOf
  suffices ∀ (acc : String), (g.foldl (fun s it => s ++ formatRLEItem it.1 it.2) acc).toByteArray.data.toList =
      acc.toByteArray.data.toList ++ g.flatMap itemBytes by simpa using this ""
  induction g with
  | nil => intro acc; simp
  | cons it g ih =>
    intro acc
    rw [List.foldl_cons, ih, String.toByteArray_append, byteArray_append_toList, bytes_formatRLEItem]
    simp

theorem bytesFrom_take_cons {B : ByteArray} {p : Nat} {d : UInt8} {ds : List UInt8}
    (h : (bytesFrom B p).take (ds.length + 1) = d :: ds) : p < B.size ∧ B[p]! = d ∧
      (bytesFrom B (p + 1)).take ds.length = ds := by
  by_cases hp : p < B.size
  · rw [bytesFrom_of_lt hp, List.take_succ_cons] at h
    simp only [List.cons.injEq] at h
    exact ⟨hp, by rw [getElem!_pos B p hp]; exact h.1, h.2⟩
  · rw [bytesFrom_of_ge (by omega)] at h; simp at h

theorem parseRLEData_digits (lines : Array String) (numLines i : UInt32) (hi : i < numLines) (B : ByteArray)
    (hB : B.size < 2 ^ 32) (warns : GrowBuf RLEWarning) (runs : GrowBuf (UInt32 × UInt32)) (sx sy : Int32) :
    ∀ (ds : List UInt8) (p col : UInt32) (c : UInt64) (h : Bool) (cP cC : UInt32),
      (bytesFrom B p.toNat).take ds.length = ds → (∀ d ∈ ds, isDigitByte d = true) →
      p.toNat + ds.length ≤ B.size → c.toNat ≤ 42949672969 →
      ∃ (c' : UInt64) (cP' cC' : UInt32), c'.toNat = ds.foldl satStep c.toNat ∧
        parseRLEData lines numLines i true B B.size.toUInt32 p col c h cP cC warns runs sx sy =
          parseRLEData lines numLines i true B B.size.toUInt32 (p + ds.length.toUInt32) (col + ds.length.toUInt32) c'
            (h || ds ≠ []) cP' cC' warns runs sx sy := by
  intro ds
  induction ds with
  | nil => intro p col c h cP cC _ _ _ _; exact ⟨c, cP, cC, rfl, by simp⟩
  | cons d ds ih =>
    intro p col c h cP cC htake hds hlen hc
    obtain ⟨hp, hd, htake'⟩ := bytesFrom_take_cons htake
    have hdig : isDigitByte d = true := hds d (by simp)
    obtain ⟨hd1, hd2⟩ := (isDigitByte_iff d).mp hdig
    have hyes : p < B.size.toUInt32 := by rw [u32_lt_size_iff hB]; exact hp
    have hsucc := u32_toNat_succ hp hB
    have hget : B.get! p.toNat = d := by rw [byteArray_get!_eq hp, ← getElem!_pos B _ hp, hd]
    rw [parseRLEData]
    simp only [hi, ↓reduceDIte, ite_true, hyes]
    rw [decodeCharAt_ascii B p _ (by rw [hget]; rw [UInt8.lt_iff_toNat_lt]; simp; omega), hget]
    have hcp1 : (48 : UInt32) ≤ d.toUInt32 := by rw [UInt32.le_iff_toNat_le]; simp; omega
    have hcp2 : d.toUInt32 ≤ 57 := by rw [UInt32.le_iff_toNat_le]; simp; omega
    simp only [hcp1, hcp2, decide_true, Bool.and_self, ite_true]
    have hstep : (if c > 4294967296 then c else c * 10 + (d.toUInt32.toUInt64 - 48)).toNat = satStep c.toNat d := by
      unfold satStep
      by_cases hgt : c > 4294967296
      · have : c.toNat > 4294967296 := hgt
        simp [hgt, this]
      · have : ¬ c.toNat > 4294967296 := hgt
        simp only [hgt, this, ite_false]
        rw [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_sub_of_le _ _ (by
          rw [UInt64.le_iff_toNat_le]; simp; omega)]
        simp; omega
    obtain ⟨c', cP', cC', hc', heq⟩ := ih (p + 1) (col + 1) _ true _ _ (by rw [hsucc]; exact htake')
      (fun d' hd' => hds d' (by simp [hd'])) (by rw [hsucc]; simp at hlen; omega)
      (by rw [hstep]; exact satStep_le hc hdig)
    refine ⟨c', cP', cC', by rw [hc', hstep]; rfl, ?_⟩
    rw [heq]
    have h1 : p + 1 + ds.length.toUInt32 = p + (d :: ds).length.toUInt32 := by
      rw [List.length_cons, UInt32.add_assoc]; congr 1
      apply UInt32.toNat_inj.mp; rw [UInt32.toNat_add]; simp [Nat.toUInt32_eq, UInt32.toNat_ofNat']; omega
    have h2 : col + 1 + ds.length.toUInt32 = col + (d :: ds).length.toUInt32 := by
      rw [List.length_cons, UInt32.add_assoc]; congr 1
      apply UInt32.toNat_inj.mp; rw [UInt32.toNat_add]; simp [Nat.toUInt32_eq, UInt32.toNat_ofNat']; omega
    rw [h1, h2]
    simp

theorem tag_step (lines : Array String) (numLines i : UInt32) (hi : i < numLines) (B : ByteArray)
    (hB : B.size < 2 ^ 32) (warns : GrowBuf RLEWarning) (runs : GrowBuf (UInt32 × UInt32)) (sx sy : Int32)
    (t : UInt8) (ht : t = rleAlive ∨ t = rleDead ∨ t = rleRowEnd) (p col : UInt32) (hp : p.toNat < B.size)
    (hb : B[p.toNat]! = tagByte t) (c : UInt64) (h : Bool) (cP cC : UInt32) (n : UInt32)
    (hn : n = if h then c.toUInt32 else 1) (hc : ¬ (h = true ∧ c > maxRunCount)) :
    parseRLEData lines numLines i true B B.size.toUInt32 p col c h cP cC warns runs sx sy =
      parseRLEData lines numLines i true B B.size.toUInt32 (p + 1) (col + 1) 0 false 0 0 warns
        (runs.push (itemRun (t, n))) sx sy := by
  have hyes : p < B.size.toUInt32 := by rw [u32_lt_size_iff hB]; exact hp
  have hget : B.get! p.toNat = tagByte t := by rw [byteArray_get!_eq hp, ← getElem!_pos B _ hp, hb]
  rw [parseRLEData]
  simp only [hi, ↓reduceDIte, ite_true, hyes]
  rw [decodeCharAt_ascii B p _ (by rw [hget]; rcases ht with rfl | rfl | rfl <;> decide), hget]
  have hcnt : (h && decide (c > maxRunCount)) = false := by
    cases h <;> simp_all
  rcases ht with rfl | rfl | rfl <;>
    simp [tagByte, rleAlive, rleDead, rleRowEnd, itemRun, hcnt, hn] <;> (cases h <;> simp_all)

theorem parseRLEData_item (lines : Array String) (numLines i : UInt32) (hi : i < numLines) (B : ByteArray)
    (hB : B.size < 2 ^ 32) (warns : GrowBuf RLEWarning) (runs : GrowBuf (UInt32 × UInt32)) (sx sy : Int32)
    (it : UInt8 × UInt32) (hit : ValidItem it) (p col : UInt32) (cP cC : UInt32)
    (htake : (bytesFrom B p.toNat).take (itemBytes it).length = itemBytes it)
    (hlen : p.toNat + (itemBytes it).length ≤ B.size) :
    parseRLEData lines numLines i true B B.size.toUInt32 p col 0 false cP cC warns runs sx sy =
      parseRLEData lines numLines i true B B.size.toUInt32 (p + (itemBytes it).length.toUInt32)
        (col + (itemBytes it).length.toUInt32) 0 false 0 0 warns (runs.push (itemRun it)) sx sy := by
  obtain ⟨t, n⟩ := it
  obtain ⟨ht, hn1, hn2⟩ := hit
  simp only at ht hn1 hn2
  unfold itemBytes at htake hlen ⊢
  by_cases h1 : (n == 1) = true
  · simp only [h1, ite_true, List.nil_append, List.length_singleton] at htake hlen ⊢
    obtain ⟨hp, hb, -⟩ := bytesFrom_take_cons (ds := []) htake
    rw [tag_step lines numLines i hi B hB warns runs sx sy t ht p col hp hb 0 false cP cC n (by simp [beq_iff_eq.mp h1])
      (by simp)]
    rfl
  · simp only [h1, Bool.false_eq_true, ite_false] at htake hlen ⊢
    obtain ⟨hd, hv, hne⟩ := natDigitBytes_spec n.toNat
    have hdig := natDigitBytes_digits n.toNat
    generalize hD : natDigitBytes n.toNat = D at hd hv hne hdig htake hlen ⊢
    rw [List.length_append, List.length_singleton] at htake hlen ⊢
    have htD : (bytesFrom B p.toNat).take D.length = D := by
      have := congrArg (List.take D.length) htake
      rw [List.take_take, Nat.min_eq_left (by omega), List.take_left' rfl] at this
      exact this
    obtain ⟨c', cP', cC', hc', heq⟩ := parseRLEData_digits lines numLines i hi B hB warns runs sx sy D p col 0 false
      cP cC htD hdig (by omega) (by simp)
    rw [heq]
    have hval : c'.toNat = n.toNat := by
      rw [hc', UInt64.toNat_zero]
      have := foldl_satStep_eq D 0 (by omega)
      rw [this.1 (by have := hv; unfold digitsValue at this; omega)]
      exact hv
    -- The tag after the digits.
    have hplen : (p + D.length.toUInt32).toNat = p.toNat + D.length := by
      rw [UInt32.toNat_add, u32_size_toNat (by omega)]; omega
    have htag : (bytesFrom B (p + D.length.toUInt32).toNat).take ([] : List UInt8).length.succ = [tagByte t] := by
      have hd' : bytesFrom B (p.toNat + D.length) = (bytesFrom B p.toNat).drop D.length := by
        rw [bytesFrom_eq_drop, bytesFrom_eq_drop, List.drop_drop, Nat.add_comm]
      rw [hplen, hd']
      have := congrArg (List.drop D.length) htake
      rw [List.drop_take, List.drop_left' rfl, show D.length + 1 - D.length = 1 by omega] at this
      simpa using this
    obtain ⟨hp, hb, -⟩ := bytesFrom_take_cons (ds := []) htag
    have hgt : ¬ ((!decide (D = []) || false) = true ∧ c' > maxRunCount) := by
      intro ⟨_, h⟩
      have := UInt64.lt_iff_toNat_lt.mp h
      simp [maxRunCount] at this; omega
    rw [tag_step lines numLines i hi B hB warns runs sx sy t ht _ _ hp hb c' _ cP' cC' n (by
      simp [hne]; apply UInt32.toNat_inj.mp; rw [UInt64.toNat_toUInt32, hval]; omega) (by simpa [hne] using hgt)]
    have e1 : p + D.length.toUInt32 + 1 = p + (D.length + 1).toUInt32 := by
      rw [UInt32.add_assoc]; congr 1; apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_add]; simp [Nat.toUInt32_eq, UInt32.toNat_ofNat']
    have e2 : col + D.length.toUInt32 + 1 = col + (D.length + 1).toUInt32 := by
      rw [UInt32.add_assoc]; congr 1; apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_add]; simp [Nat.toUInt32_eq, UInt32.toNat_ofNat']
    rw [e1, e2]

theorem parseRLEData_items (lines : Array String) (numLines i : UInt32) (hi : i < numLines) (B : ByteArray)
    (hB : B.size < 2 ^ 32) (warns : GrowBuf RLEWarning) (sx sy : Int32) :
    ∀ (g : List (UInt8 × UInt32)) (p : UInt32) (runs : GrowBuf (UInt32 × UInt32)) (r : Array (UInt32 × UInt32)),
      (∀ it ∈ g, ValidItem it) → (bytesFrom B p.toNat).take (g.flatMap itemBytes).length = g.flatMap itemBytes →
      p.toNat + (g.flatMap itemBytes).length ≤ B.size → runs.Rep r → r.size + g.length < 2 ^ 31 →
      ∃ runs' : GrowBuf (UInt32 × UInt32), runs'.Rep (r ++ (g.map itemRun).toArray) ∧
        parseRLEData lines numLines i true B B.size.toUInt32 p p 0 false 0 0 warns runs sx sy =
          parseRLEData lines numLines i true B B.size.toUInt32 (p + (g.flatMap itemBytes).length.toUInt32)
            (p + (g.flatMap itemBytes).length.toUInt32) 0 false 0 0 warns runs' sx sy := by
  intro g
  induction g with
  | nil => intro p runs r _ _ _ hrep _; exact ⟨runs, by simpa using hrep, by simp⟩
  | cons it g ih =>
    intro p runs r hval htake hlen hrep hr
    rw [List.flatMap_cons, List.length_append] at htake hlen
    have h1 : (bytesFrom B p.toNat).take (itemBytes it).length = itemBytes it := by
      have := congrArg (List.take (itemBytes it).length) htake
      rw [List.take_take, Nat.min_eq_left (by omega), List.take_left' rfl] at this
      exact this
    rw [parseRLEData_item lines numLines i hi B hB warns runs sx sy it (hval it (by simp)) p p 0 0 h1 (by omega)]
    have hplen : (p + (itemBytes it).length.toUInt32).toNat = p.toNat + (itemBytes it).length := by
      rw [UInt32.toNat_add, u32_size_toNat (by omega)]; omega
    have h2 : (bytesFrom B (p + (itemBytes it).length.toUInt32).toNat).take (g.flatMap itemBytes).length =
        g.flatMap itemBytes := by
      have hd' : bytesFrom B (p.toNat + (itemBytes it).length) = (bytesFrom B p.toNat).drop (itemBytes it).length := by
        rw [bytesFrom_eq_drop, bytesFrom_eq_drop, List.drop_drop, Nat.add_comm]
      rw [hplen, hd']
      have := congrArg (List.drop (itemBytes it).length) htake
      rw [List.drop_take, List.drop_left' rfl, Nat.add_sub_cancel_left] at this
      exact this
    obtain ⟨runs', hr', heq⟩ := ih _ _ _ (fun it' h' => hval it' (by simp [h'])) h2 (by rw [hplen]; omega)
      (GrowBuf.rep_push hrep (itemRun it) (by simp at hr; omega)) (by simp at hr ⊢; omega)
    refine ⟨runs', by simpa [Array.append_assoc] using hr', ?_⟩
    rw [heq]
    have e : p + (itemBytes it).length.toUInt32 + (g.flatMap itemBytes).length.toUInt32 =
        p + ((itemBytes it).length + (g.flatMap itemBytes).length).toUInt32 := by
      rw [UInt32.add_assoc]; congr 1; apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_add]; simp [Nat.toUInt32_eq, UInt32.toNat_ofNat']
    simp only [List.flatMap_cons, List.length_append]
    rw [e]

theorem lineOf_bytes_take (g : List (UInt8 × UInt32)) :
    (bytesFrom (lineOf g).toByteArray (0 : UInt32).toNat).take (g.flatMap itemBytes).length = g.flatMap itemBytes := by
  rw [bytesFrom_eq_drop, UInt32.toNat_zero, List.drop_zero, bytes_lineOf, List.take_length]

theorem lineOf_size (g : List (UInt8 × UInt32)) : (lineOf g).toByteArray.size = (g.flatMap itemBytes).length := by
  rw [byteArray_size_eq_length, bytes_lineOf]

/-- Reading a line of valid items adds their runs and moves to the next line. -/
theorem parseRLEData_line (lines : Array String) (i : UInt32)
    (hi : i < lines.size.toUInt32) (g : List (UInt8 × UInt32)) (hg : ∀ it ∈ g, ValidItem it)
    (hline : lines[i.toNat]! = lineOf g) (hsz : (g.flatMap itemBytes).length < 2 ^ 32) (warns : GrowBuf RLEWarning)
    (runs : GrowBuf (UInt32 × UInt32)) (r : Array (UInt32 × UInt32)) (hrep : runs.Rep r)
    (hr : r.size + g.length < 2 ^ 31) (sx sy : Int32) (B : ByteArray) (lim p col : UInt32) (c : UInt64) (h : Bool)
    (cP cC : UInt32) :
    ∃ (runs' : GrowBuf (UInt32 × UInt32)) (B' : ByteArray) (lim' : UInt32), runs'.Rep (r ++ (g.map itemRun).toArray) ∧
      parseRLEData lines lines.size.toUInt32 i false B lim p col c h cP cC warns runs sx sy =
        parseRLEData lines lines.size.toUInt32 (i + 1) false B' lim' 0 0 0 false 0 0 warns runs' sx sy := by
  have hB : (lineOf g).toByteArray.size < 2 ^ 32 := by rw [lineOf_size]; exact hsz
  rw [parseRLEData]
  simp only [hi, ↓reduceDIte, Bool.false_eq_true, ite_false, hline]
  obtain ⟨runs', hr', heq⟩ := parseRLEData_items lines lines.size.toUInt32 i hi (lineOf g).toByteArray hB warns sx sy g
    0 runs r hg (lineOf_bytes_take g) (by rw [lineOf_size]; simp) hrep hr
  refine ⟨runs', (lineOf g).toByteArray, (lineOf g).toByteArray.size.toUInt32, hr', ?_⟩
  rw [heq]
  have hend : (0 : UInt32) + (g.flatMap itemBytes).length.toUInt32 = (lineOf g).toByteArray.size.toUInt32 := by
    rw [lineOf_size]; simp
  rw [hend, parseRLEData]
  simp only [hi, ↓reduceDIte, ite_true, UInt32.lt_irrefl]

theorem itemRun_end : itemRun (rleEnd, 1) = (0, 1) := rfl

theorem itemBytes_end : itemBytes (rleEnd, 1) = [33] := rfl

/-- Reading the last line, valid items and then `!`, finishes with their runs and the end's. -/
theorem parseRLEData_last_line (lines : Array String) (hL : lines.size < 2 ^ 32) (i : UInt32)
    (hi : i < lines.size.toUInt32) (hlast : i.toNat + 1 = lines.size) (g : List (UInt8 × UInt32))
    (hg : ∀ it ∈ g, ValidItem it) (hline : lines[i.toNat]! = lineOf (g ++ [(rleEnd, 1)]))
    (hsz : ((g ++ [(rleEnd, 1)]).flatMap itemBytes).length < 2 ^ 32) (warns : GrowBuf RLEWarning)
    (runs : GrowBuf (UInt32 × UInt32)) (r : Array (UInt32 × UInt32)) (hrep : runs.Rep r)
    (hr : r.size + g.length + 1 < 2 ^ 31) (sx sy : Int32) (B : ByteArray) (lim p col : UInt32) (c : UInt64) (h : Bool)
    (cP cC : UInt32) :
    ∃ runs' : GrowBuf (UInt32 × UInt32), runs'.Rep (r ++ ((g ++ [(rleEnd, 1)]).map itemRun).toArray) ∧
      parseRLEData lines lines.size.toUInt32 i false B lim p col c h cP cC warns runs sx sy =
        finishRLE warns runs' sx sy := by
  have hB : (lineOf (g ++ [(rleEnd, 1)])).toByteArray.size < 2 ^ 32 := by rw [lineOf_size]; exact hsz
  generalize hBB : (lineOf (g ++ [(rleEnd, 1)])).toByteArray = BB at hB
  have hbytes : BB.data.toList = g.flatMap itemBytes ++ [33] := by
    rw [← hBB, bytes_lineOf, List.flatMap_append]; rfl
  have hBsize : BB.size = (g.flatMap itemBytes).length + 1 := by rw [byteArray_size_eq_length, hbytes]; simp
  rw [parseRLEData]
  simp only [hi, ↓reduceDIte, Bool.false_eq_true, ite_false, hline, hBB]
  obtain ⟨runs', hr', heq⟩ := parseRLEData_items lines lines.size.toUInt32 i hi BB hB warns sx sy g 0 runs r hg
    (by rw [bytesFrom_eq_drop, UInt32.toNat_zero, List.drop_zero, hbytes, List.take_left' rfl])
    (by rw [UInt32.toNat_zero, hBsize]; omega) hrep (by omega)
  have hl32 : (g.flatMap itemBytes).length < 2 ^ 32 := by omega
  rw [heq]
  -- The `!`.
  have hp : (0 + (g.flatMap itemBytes).length.toUInt32).toNat = (g.flatMap itemBytes).length := by
    rw [UInt32.toNat_add, UInt32.toNat_zero, u32_size_toNat hl32, Nat.zero_add, Nat.mod_eq_of_lt hl32]
  have hlt : (0 + (g.flatMap itemBytes).length.toUInt32).toNat < BB.size := by rw [hp]; omega
  have hyes : 0 + (g.flatMap itemBytes).length.toUInt32 < BB.size.toUInt32 := by rw [u32_lt_size_iff hB]; exact hlt
  have hget : BB.get! (0 + (g.flatMap itemBytes).length.toUInt32).toNat = 33 := by
    rw [hp, byteArray_get!_eq (by omega)]
    have : BB.data.toList[(g.flatMap itemBytes).length]'(by rw [hbytes]; simp) = 33 := by simp [hbytes]
    rw [← this, Array.getElem_toList]; rfl
  rw [parseRLEData]
  simp only [hi, ↓reduceDIte, ite_true, hyes]
  rw [decodeCharAt_ascii BB _ _ (by rw [hget]; decide), hget]
  have hnext : ¬ (0 + (g.flatMap itemBytes).length.toUInt32 + 1) < BB.size.toUInt32 := by
    rw [UInt32.lt_iff_toNat_lt, u32_size_toNat hB, UInt32.toNat_add, hp, UInt32.toNat_one,
      Nat.mod_eq_of_lt (by omega)]; omega
  have hlastl : ¬ i + 1 < lines.size.toUInt32 := by
    rw [UInt32.lt_iff_toNat_lt, u32_size_toNat hL, UInt32.toNat_add]; simp; omega
  simp only [show ((33 : UInt8).toUInt32 : UInt32) = 33 from rfl, show ((48 : UInt32) ≤ 33) = False from by decide,
    decide_false, Bool.false_and, Bool.false_eq_true, ite_false, beq_self_eq_true, ite_true, hnext, hlastl]
  refine ⟨runs'.push (0, 1), ?_, rfl⟩
  have := GrowBuf.rep_push hr' (0, 1) (by simp; omega)
  simpa [itemRun_end, Array.append_assoc] using this

theorem parseRLEData_groups (lines : Array String) (hL : lines.size < 2 ^ 31) (warns : GrowBuf RLEWarning)
    (sx sy : Int32) (last : List (UInt8 × UInt32)) (hlastv : ∀ it ∈ last, ValidItem it)
    (hlastsz : ((last ++ [(rleEnd, 1)]).flatMap itemBytes).length < 2 ^ 32) :
    ∀ (Gs : List (List (UInt8 × UInt32))) (i : Nat) (runs : GrowBuf (UInt32 × UInt32)) (r : Array (UInt32 × UInt32))
      (B : ByteArray) (lim p col : UInt32) (c : UInt64) (h : Bool) (cP cC : UInt32),
      lines.toList.drop i = (Gs ++ [last ++ [(rleEnd, 1)]]).map lineOf → i + Gs.length + 1 = lines.size →
      (∀ g ∈ Gs, ∀ it ∈ g, ValidItem it) → (∀ g ∈ Gs, (g.flatMap itemBytes).length < 2 ^ 32) → runs.Rep r →
      r.size + (Gs.flatten ++ last).length + 1 < 2 ^ 31 →
      ∃ runs' : GrowBuf (UInt32 × UInt32),
        runs'.Rep (r ++ ((Gs.flatten ++ last ++ [(rleEnd, 1)]).map itemRun).toArray) ∧
        parseRLEData lines lines.size.toUInt32 i.toUInt32 false B lim p col c h cP cC warns runs sx sy =
          finishRLE warns runs' sx sy := by
  have hL32 : lines.size < 2 ^ 32 := by omega
  intro Gs
  induction Gs with
  | nil =>
    intro i runs r B lim p col c h cP cC hsplit hlen _ _ hrep hr
    have hiU : i.toUInt32.toNat = i := u32_size_toNat (by omega)
    have hline : lines[i.toUInt32.toNat]! = lineOf (last ++ [(rleEnd, 1)]) := by
      rw [hiU, show i = i + 0 from rfl, array_getElem!_of_drop lines i 0 _ [] (by simpa using hsplit) (by simp)]
      simp
    obtain ⟨runs', hr', heq⟩ := parseRLEData_last_line lines hL32 i.toUInt32 (by rw [u32_lt_size_iff hL32, hiU]; omega)
      (by rw [hiU]; simpa using hlen) last hlastv hline hlastsz warns runs r hrep (by simpa using hr) sx sy B lim p col
      c h cP cC
    exact ⟨runs', by simpa [List.append_assoc] using hr', heq⟩
  | cons g Gs ih =>
    intro i runs r B lim p col c h cP cC hsplit hlen hval hsz hrep hr
    have hiU : i.toUInt32.toNat = i := u32_size_toNat (by simp at hlen; omega)
    have hline : lines[i.toUInt32.toNat]! = lineOf g := by
      rw [hiU, show i = i + 0 from rfl, array_getElem!_of_drop lines i 0 [lineOf g] _ (by rw [hsplit]; rfl) (by simp)]
      rfl
    obtain ⟨runs', B', lim', hr', heq⟩ := parseRLEData_line lines i.toUInt32
      (by rw [u32_lt_size_iff hL32, hiU]; simp at hlen; omega) g (hval g (by simp)) hline (hsz g (by simp)) warns
      runs r hrep (by simp at hr; omega) sx sy B lim p col c h cP cC
    rw [heq]
    have hnext : i.toUInt32 + 1 = (i + 1).toUInt32 := by
      apply UInt32.toNat_inj.mp; rw [UInt32.toNat_add, hiU, u32_size_toNat (by simp at hlen; omega)]; simp
      simp at hlen; omega
    rw [hnext]
    obtain ⟨runs'', hr'', heq'⟩ := ih (i + 1) runs' _ B' lim' 0 0 0 false 0 0
      (by rw [← List.drop_drop, hsplit]; simp) (by simp at hlen; omega)
      (fun g' hg' => hval g' (by simp [hg'])) (fun g' hg' => hsz g' (by simp [hg'])) hr' (by simp at hr ⊢; omega)
    exact ⟨runs'', by simpa [Array.append_assoc, List.append_assoc] using hr'', heq'⟩

/-! ## Header lines -/

theorem bytes_rleOffsetLine (x y : Int32) :
    (formatRLEHeader x y 0 0)[0]!.toByteArray.data.toList =
      [35, 82, 32] ++ (toString x).toByteArray.data.toList ++ 32 :: (toString y).toByteArray.data.toList := by
  show ("#R " ++ toString x ++ " " ++ toString y).toByteArray.data.toList = _
  simp only [String.toByteArray_append, byteArray_append_toList, List.append_assoc]
  rfl

theorem toString_int32_ne_nil' (x : Int32) : (toString x).toByteArray.data.toList ≠ [] := by
  rw [bytes_toString_int32]
  have := (natDigitBytes_spec x.toInt.natAbs).2.2
  split <;> simp_all

/-- Every top-left coordinate line parses back to its coordinates. -/
theorem parseRLEOffset_format (x y : Int32) :
    parseRLEOffset (formatRLEHeader x y 0 0)[0]!.toByteArray = some ⟨x, y⟩ := by
  generalize hX : (toString x).toByteArray.data.toList = X
  generalize hY : (toString y).toByteArray.data.toList = Y
  have hL := bytes_rleOffsetLine x y
  rw [hX, hY] at hL
  have hXlen : X.length ≤ 11 := hX ▸ bytes_toString_int32_length x
  have hYlen : Y.length ≤ 11 := hY ▸ bytes_toString_int32_length y
  have hYne : Y ≠ [] := hY ▸ toString_int32_ne_nil' y
  rw [byteArray_eq_of_toList hL]
  generalize hLL : [35, 82, 32] ++ X ++ 32 :: Y = L
  have hLlen : L.length = X.length + Y.length + 4 := by rw [← hLL]; simp; omega
  have hsize : (⟨L.toArray⟩ : ByteArray).size = L.length := size_of_list L
  have hB32 : (⟨L.toArray⟩ : ByteArray).size < 2 ^ 32 := by omega
  have hlimit : (⟨L.toArray⟩ : ByteArray).size.toUInt32.toNat = L.length := by rw [u32_size_toNat hB32, hsize]
  have hget : ∀ k, k < L.length → (⟨L.toArray⟩ : ByteArray).get! k = L[k]! := get!_of_list L
  have hidx : ∀ k, k ≤ L.length → k.toUInt32.toNat = k := fun k hk => u32_size_toNat (by omega)
  unfold parseRLEOffset
  have h3 : ¬ (⟨L.toArray⟩ : ByteArray).size.toUInt32 < 3 := by rw [UInt32.lt_iff_toNat_lt, hlimit]; simp; omega
  have g0 : (⟨L.toArray⟩ : ByteArray).get! 0 = 35 := by rw [hget 0 (by omega)]; subst hLL; rfl
  have g1 : (⟨L.toArray⟩ : ByteArray).get! 1 = 82 := by rw [hget 1 (by omega)]; subst hLL; rfl
  have g2 : (⟨L.toArray⟩ : ByteArray).get! 2 = 32 := by rw [hget 2 (by omega)]; subst hLL; rfl
  simp only [h3, decide_false, g0, g1, g2, bne_self_eq_false, Bool.or_false, Bool.false_and, Bool.false_eq_true,
    ite_false]
  -- The first number.
  have hx : parseInt32At ⟨L.toArray⟩ 3 (⟨L.toArray⟩ : ByteArray).size.toUInt32 =
      some ⟨x, (3 + X.length).toUInt32⟩ := by
    have hp := parseInt32Spec_toString x (32 :: Y) (by intro z hz; simp at hz; subst hz; decide)
    rw [hX] at hp
    rw [parseInt32At_spec _ hB32 3 (by simp; omega), show (3 : UInt32).toNat = 3 from rfl, bytesFrom_of_list,
      ← hLL, show List.drop 3 ([35, 82, 32] ++ X ++ 32 :: Y) = X ++ 32 :: Y by simp, hp, Option.map_some]
    congr 2
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_add, hidx _ (by omega), hidx _ (by omega)]; simp; omega
  rw [hx]
  simp only
  have hlt : (3 + X.length).toUInt32 < (⟨L.toArray⟩ : ByteArray).size.toUInt32 := by
    rw [UInt32.lt_iff_toNat_lt, hidx _ (by omega), hlimit]; omega
  have hsp : (⟨L.toArray⟩ : ByteArray).get! (3 + X.length).toUInt32.toNat = 32 := by
    rw [hidx _ (by omega), hget _ (by omega), ← hLL, getElem!_pos _ _ (by simp; omega)]
    rw [List.getElem_append_right (by simp; omega)]
    simp [show 3 + X.length - (X.length + 1 + 1 + 1) = 0 by omega]
  simp only [hlt, decide_true, hsp, beq_self_eq_true, Bool.and_self, ite_true]
  -- The second number.
  have hs2 : (3 + X.length).toUInt32 + 1 = (4 + X.length).toUInt32 := by
    apply UInt32.toNat_inj.mp; rw [UInt32.toNat_add, hidx _ (by omega), hidx _ (by omega)]; simp; omega
  rw [hs2]
  have hy : parseInt32At ⟨L.toArray⟩ (4 + X.length).toUInt32 (⟨L.toArray⟩ : ByteArray).size.toUInt32 =
      some ⟨y, (⟨L.toArray⟩ : ByteArray).size.toUInt32⟩ := by
    rw [parseInt32At_spec _ hB32 _ (by rw [hidx _ (by omega), hsize]; omega), hidx _ (by omega), bytesFrom_of_list]
    have : L.drop (4 + X.length) = (toString y).toByteArray.data.toList ++ [] := by
      rw [← hLL, List.append_nil, hY, show 4 + X.length = (X.length + 1) + 3 by omega]
      simp only [List.cons_append, List.nil_append, List.drop_succ_cons]
      rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
        show X.length + 1 - X.length = 1 by omega]
      rfl
    have hp := parseInt32Spec_toString y [] (by simp)
    rw [this, hp, Option.map_some, hY]
    congr 2
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_add, hidx _ (by omega), hlimit, u32_size_toNat (by omega)]; omega
  rw [hy]
  simp

/-- One step of `parseRLEHeader`: skips spaces and expects `c`. -/
def rleExpect (bytes : ByteArray) (p : UInt32) (c : UInt8) : Option UInt32 :=
  let q := skipSpaces bytes p bytes.size.toUInt32
  if q < bytes.size.toUInt32 && bytes.get! q.toNat == c then some (q + 1) else none

/-- One step of `parseRLEHeader`: skips spaces and expects a number. -/
def rleExpectNum (bytes : ByteArray) (p : UInt32) : Option UInt32 :=
  match parseUInt32At bytes (skipSpaces bytes p bytes.size.toUInt32) bytes.size.toUInt32 with
  | some r => some r.next
  | none => none

theorem parseRLEHeader_eq (bytes : ByteArray) : parseRLEHeader bytes =
    match rleExpect bytes 0 120 >>= (rleExpect bytes · 61) >>= rleExpectNum bytes >>= (rleExpect bytes · 44) >>=
        (rleExpect bytes · 121) >>= (rleExpect bytes · 61) >>= rleExpectNum bytes with
    | none => 2
    | some p =>
      let limit := bytes.size.toUInt32
      let q := skipSpaces bytes p limit
      if q == limit then 0
      else
        match rleExpect bytes q 44 with
        | none => 2
        | some p1 =>
          let r := skipSpaces bytes p1 limit
          if r + 4 <= limit && limit - r >= 4 && isLetterByte (bytes.get! r.toNat) 114 &&
              isLetterByte (bytes.get! (r + 1).toNat) 117 && isLetterByte (bytes.get! (r + 2).toNat) 108 &&
              isLetterByte (bytes.get! (r + 3).toNat) 101 then
            match rleExpect bytes (r + 4) 61 with
            | none => 2
            | some p2 => checkRLERule bytes p2 limit
          else 2 := rfl

theorem rleExpect_list (L : List UInt8) (hL : L.length < 2 ^ 32) (p : UInt32) (v m : Nat) (hp : p.toNat = v)
    (c : UInt8) (rest : List UInt8) (hsplit : L.drop v = List.replicate m 32 ++ c :: rest)
    (hc : isSpaceByte c = false) :
    rleExpect ⟨L.toArray⟩ p c = some (v + m + 1).toUInt32 := by
  have hlen := congrArg List.length hsplit
  simp only [List.length_drop, List.length_append, List.length_replicate, List.length_cons] at hlen
  unfold rleExpect
  have hv : v ≤ L.length := by
    by_cases h : v ≤ L.length
    · exact h
    · rw [List.drop_eq_nil_of_le (by omega)] at hsplit; simp at hsplit
  rw [skipSpaces_list L hL p v m hp hv (c :: rest) hsplit (by intro y hy; simp at hy; subst hy; exact hc)]
  have hlt : (v + m).toUInt32 < (⟨L.toArray⟩ : ByteArray).size.toUInt32 := by
    rw [UInt32.lt_iff_toNat_lt, u32_size_toNat (by omega), size_of_list, u32_size_toNat hL]; omega
  have hget : (⟨L.toArray⟩ : ByteArray).get! (v + m).toUInt32.toNat = c := by
    rw [u32_size_toNat (by omega), get!_of_list L _ (by omega)]
    have : L[v + m]? = some c := by
      rw [← List.getElem?_drop, hsplit, List.getElem?_append_right (by simp)]; simp
    rw [getElem!_def, this]
  simp only [hlt, decide_true, hget, beq_self_eq_true, Bool.and_self, ite_true, Option.some.injEq]
  apply UInt32.toNat_inj.mp; rw [UInt32.toNat_add, u32_size_toNat (by omega), u32_size_toNat (by omega)]; simp; omega

theorem rleExpectNum_list (L : List UInt8) (hL : L.length < 2 ^ 32) (p : UInt32) (v m : Nat) (hp : p.toNat = v)
    (n : UInt32) (rest : List UInt8) (hsplit : L.drop v = List.replicate m 32 ++ (natDigitBytes n.toNat ++ rest))
    (hrest : ∀ y, rest.head? = some y → isDigitByte y = false) :
    rleExpectNum ⟨L.toArray⟩ p = some (v + m + (natDigitBytes n.toNat).length).toUInt32 := by
  have hlen := congrArg List.length hsplit
  simp only [List.length_drop, List.length_append, List.length_replicate] at hlen
  have hsz : (⟨L.toArray⟩ : ByteArray).size < 2 ^ 32 := by rw [size_of_list]; exact hL
  unfold rleExpectNum
  obtain ⟨hd, -, hne⟩ := natDigitBytes_spec n.toNat
  have hfirst : ∀ y, (natDigitBytes n.toNat ++ rest).head? = some y → isSpaceByte y = false := by
    intro y hy
    cases hD : natDigitBytes n.toNat with
    | nil => exact absurd hD hne
    | cons z zs =>
      rw [hD] at hy; simp at hy; subst hy
      exact isDigitByte_not_space ((isDigitByte_iff _).mpr (hd _ (by rw [hD]; simp)))
  have hv : v ≤ L.length := by
    by_cases h : v ≤ L.length
    · exact h
    · rw [List.drop_eq_nil_of_le (by omega)] at hsplit
      cases hD : natDigitBytes n.toNat with
      | nil => exact absurd hD hne
      | cons _ _ => rw [hD] at hsplit; simp at hsplit
  rw [skipSpaces_list L hL p v m hp hv _ hsplit hfirst]
  rw [parseUInt32At_digits _ hsz _ n rest (by
    rw [bytesFrom_of_list, u32_size_toNat (by omega), ← List.drop_drop, hsplit, List.drop_left']; simp) hrest]
  simp only [Option.some.injEq]
  apply UInt32.toNat_inj.mp; rw [UInt32.toNat_add, u32_size_toNat (by omega), u32_size_toNat (by omega),
    u32_size_toNat (by omega)]; omega

theorem checkRLERule_skip (B : ByteArray) (p p' lim : UInt32) (h : skipSpaces B p lim = skipSpaces B p' lim) :
    checkRLERule B p lim = checkRLERule B p' lim := by
  unfold checkRLERule; rw [h]

theorem bytes_rleSizeLine (w h : UInt32) :
    (formatRLEHeader 0 0 w h)[1]!.toByteArray.data.toList =
      [120, 32, 61, 32] ++ (natDigitBytes w.toNat ++ ([44, 32, 121, 32, 61, 32] ++ (natDigitBytes h.toNat ++
        [44, 32, 114, 117, 108, 101, 32, 61, 32, 66, 51, 47, 83, 50, 51]))) := by
  show ("x = " ++ toString w.toNat ++ ", y = " ++ toString h.toNat ++ ", rule = B3/S23").toByteArray.data.toList = _
  simp only [String.toByteArray_append, byteArray_append_toList, Nat.toString_eq_repr, bytes_natRepr,
    List.append_assoc]
  rfl

/-- The size line written by the serializer is a valid header with Conway's rules. -/
theorem parseRLEHeader_sizeLine (minX minY : Int32) (w h : UInt32) :
    parseRLEHeader (formatRLEHeader minX minY w h)[1]!.toByteArray = 0 := by
  have hsame : (formatRLEHeader minX minY w h)[1]! = (formatRLEHeader 0 0 w h)[1]! := rfl
  rw [hsame, byteArray_eq_of_toList (bytes_rleSizeLine w h)]
  have hW := natDigitBytes_length_le w.toNat (by have := UInt32.toNat_lt w; omega)
  have hH := natDigitBytes_length_le h.toNat (by have := UInt32.toNat_lt h; omega)
  have hWd := natDigitBytes_digits w.toNat
  have hHd := natDigitBytes_digits h.toNat
  generalize hWW : natDigitBytes w.toNat = W at hW hWd ⊢
  generalize hHH : natDigitBytes h.toNat = H at hH hHd ⊢
  generalize hLL : [120, 32, 61, 32] ++ (W ++ ([44, 32, 121, 32, 61, 32] ++ (H ++
        [44, 32, 114, 117, 108, 101, 32, 61, 32, 66, 51, 47, 83, 50, 51]))) = L
  have hLlen : L.length = W.length + H.length + 25 := by rw [← hLL]; simp; omega
  have hL : L.length < 2 ^ 32 := by omega
  have hidx : ∀ k, k ≤ L.length → k.toUInt32.toNat = k := fun k hk => u32_size_toNat (by omega)
  generalize hT : ([44, 32, 114, 117, 108, 101, 32, 61, 32, 66, 51, 47, 83, 50, 51] : List UInt8) = T at hLL
  have hR1 : L.drop (4 + W.length) = [44, 32, 121, 32, 61, 32] ++ (H ++ T) := by
    rw [← hLL, ← List.drop_drop]; simp
  have hR2 : L.drop (10 + W.length + H.length) = T := by
    rw [show 10 + W.length + H.length = (4 + W.length) + (6 + H.length) by omega, ← List.drop_drop, hR1]
    rw [← List.drop_drop]; simp
  have hdrop : ∀ k j (R : List UInt8), L.drop k = R → L.drop (k + j) = R.drop j := by
    intro k j R h; rw [← List.drop_drop, h]
  rw [parseRLEHeader_eq]
  have nd44 : isDigitByte 44 = false := by decide
  -- "x = w, y = h"
  rw [rleExpect_list L hL 0 0 0 rfl 120 _ (by rw [← hLL]; rfl) (by decide)]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [rleExpect_list L hL _ 1 1 (hidx _ (by omega)) 61 _ (by rw [← hLL]; rfl) (by decide)]
  simp only [Option.bind_some]
  rw [rleExpectNum_list L hL _ 3 1 (hidx _ (by omega)) w ([44, 32, 121, 32, 61, 32] ++ (H ++ T))
    (by rw [← hLL, hWW]; rfl) (by intro y hy; simp at hy; subst hy; exact nd44)]
  simp only [Option.bind_some, hWW]
  rw [rleExpect_list L hL _ (3 + 1 + W.length) 0 (hidx _ (by omega)) 44 _
    (by rw [show 3 + 1 + W.length = 4 + W.length by omega, hR1]; rfl) (by decide)]
  simp only [Option.bind_some]
  rw [rleExpect_list L hL _ (3 + 1 + W.length + 0 + 1) 1 (hidx _ (by omega)) 121 _
    (by rw [show 3 + 1 + W.length + 0 + 1 = 4 + W.length + 1 by omega, hdrop _ 1 _ hR1]; rfl) (by decide)]
  simp only [Option.bind_some]
  rw [rleExpect_list L hL _ (3 + 1 + W.length + 0 + 1 + 1 + 1) 1 (hidx _ (by omega)) 61 _
    (by rw [show 3 + 1 + W.length + 0 + 1 + 1 + 1 = 4 + W.length + 3 by omega, hdrop _ 3 _ hR1]; rfl) (by decide)]
  simp only [Option.bind_some]
  rw [rleExpectNum_list L hL _ (3 + 1 + W.length + 0 + 1 + 1 + 1 + 1 + 1) 1 (hidx _ (by omega)) h T
    (by rw [show 3 + 1 + W.length + 0 + 1 + 1 + 1 + 1 + 1 = 4 + W.length + 5 by omega, hdrop _ 5 _ hR1, hHH]; rfl)
    (by intro y hy; rw [← hT] at hy; simp at hy; subst hy; exact nd44)]
  simp only [hHH]
  -- ", rule = B3/S23"
  have hq := skipSpaces_list L hL (3 + 1 + W.length + 0 + 1 + 1 + 1 + 1 + 1 + 1 + H.length).toUInt32
    (10 + W.length + H.length) 0 (by rw [hidx _ (by omega)]; omega) (by omega) T (by
      rw [hR2]; rfl) (by intro y hy; rw [← hT] at hy; simp at hy; subst hy; decide)
  rw [hq]
  have hsz : (⟨L.toArray⟩ : ByteArray).size = L.length := size_of_list L
  have hlim : (⟨L.toArray⟩ : ByteArray).size.toUInt32.toNat = W.length + H.length + 25 := by
    rw [hsz, u32_size_toNat hL, hLlen]
  have hTd : ∀ j, L.drop (10 + W.length + H.length + j) = T.drop j := fun j => hdrop _ j _ hR2
  have hne : ¬ ((10 + W.length + H.length + 0).toUInt32 == (⟨L.toArray⟩ : ByteArray).size.toUInt32) = true := by
    intro h; have := congrArg UInt32.toNat (beq_iff_eq.mp h); rw [hlim, hidx _ (by omega)] at this; omega
  rw [ite_eq_right hne]
  rw [rleExpect_list L hL _ (10 + W.length + H.length + 0) 0 (hidx _ (by omega)) 44 _
    (by rw [hTd 0, ← hT]; rfl) (by decide)]
  simp only
  have hr := skipSpaces_list L hL (10 + W.length + H.length + 0 + 0 + 1).toUInt32
    (10 + W.length + H.length + 1) 1 (by rw [hidx _ (by omega)]) (by omega) _ (by rw [hTd 1, ← hT]; rfl)
    (by intro y hy; simp at hy; subst hy; decide)
  rw [hr]
  have hget : ∀ j, j < 15 → (⟨L.toArray⟩ : ByteArray).get! (10 + W.length + H.length + j) = T[j]! := by
    intro j hj
    rw [get!_of_list L _ (by omega)]
    rw [getElem!_def, getElem!_def, ← List.getElem?_drop, hR2]
  have h0 : (10 + W.length + H.length + 1 + 1).toUInt32.toNat = 10 + W.length + H.length + 2 := hidx _ (by omega)
  have hpk : ∀ k : UInt32, k.toNat ≤ 13 → ((10 + W.length + H.length + 1 + 1).toUInt32 + k).toNat =
      10 + W.length + H.length + (2 + k.toNat) := by
    intro k hk; rw [UInt32.toNat_add, h0, Nat.mod_eq_of_lt (by omega)]; omega
  have c1 : ((10 + W.length + H.length + 1 + 1).toUInt32 + 4 ≤ (⟨L.toArray⟩ : ByteArray).size.toUInt32) := by
    rw [UInt32.le_iff_toNat_le, hpk 4 (by decide), hlim]; simp; omega
  have c2 : (⟨L.toArray⟩ : ByteArray).size.toUInt32 - (10 + W.length + H.length + 1 + 1).toUInt32 ≥ 4 := by
    rw [ge_iff_le, UInt32.le_iff_toNat_le, UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, h0, hlim]; omega),
      h0, hlim]; simp; omega
  have g0 := hget 2 (by omega)
  have g1 := hget 3 (by omega)
  have g2 := hget 4 (by omega)
  have g3 := hget 5 (by omega)
  rw [← hT] at g0 g1 g2 g3
  rw [show 10 + W.length + H.length + 2 = (10 + W.length + H.length + 1 + 1).toUInt32.toNat by rw [h0]] at g0
  rw [show 10 + W.length + H.length + 3 = ((10 + W.length + H.length + 1 + 1).toUInt32 + 1).toNat by
    rw [hpk 1 (by decide)]; simp] at g1
  rw [show 10 + W.length + H.length + 4 = ((10 + W.length + H.length + 1 + 1).toUInt32 + 2).toNat by
    rw [hpk 2 (by decide)]; simp] at g2
  rw [show 10 + W.length + H.length + 5 = ((10 + W.length + H.length + 1 + 1).toUInt32 + 3).toNat by
    rw [hpk 3 (by decide)]; simp] at g3
  simp only [c1, c2, decide_true, g0, g1, g2, g3, Bool.true_and, Bool.and_true]
  rw [ite_eq_left (by decide)]
  rw [rleExpect_list L hL _ (10 + W.length + H.length + 6) 1 (by rw [hpk 4 (by decide)]; simp) 61 _
    (by rw [hTd 6, ← hT]; rfl) (by decide)]
  simp only
  -- The rule, after one space.
  have hs1 := skipSpaces_list L hL (10 + W.length + H.length + 6 + 1 + 1).toUInt32 (10 + W.length + H.length + 8) 1
    (by rw [hidx _ (by omega)]) (by omega) _ (by rw [hTd 8, ← hT]; rfl) (by intro y hy; simp at hy; subst hy; decide)
  have hs2 := skipSpaces_list L hL (10 + W.length + H.length + 9).toUInt32 (10 + W.length + H.length + 9) 0
    (by rw [hidx _ (by omega)]) (by omega) _ (by rw [hTd 9, ← hT]; rfl) (by intro y hy; simp at hy; subst hy; decide)
  rw [checkRLERule_skip _ _ (10 + W.length + H.length + 9).toUInt32 _ (by rw [hs1, hs2])]
  have hsplitL : L = L.take (10 + W.length + H.length + 9) ++ 66 :: ([51] ++ 47 :: 83 :: [50, 51]) := by
    conv => lhs; rw [← List.take_append_drop (10 + W.length + H.length + 9) L]
    rw [hTd 9, ← hT]; rfl
  have htl : (L.take (10 + W.length + H.length + 9)).length = 10 + W.length + H.length + 9 := by
    rw [List.length_take]; omega
  rw [hsplitL]
  rw [show (10 + W.length + H.length + 9).toUInt32 = (L.take (10 + W.length + H.length + 9)).length.toUInt32 by
    rw [htl]]
  rw [checkRLERule_letters _ [51] [50, 51] 66 83 (Or.inl rfl) (Or.inl rfl) (by simp) (by simp) (by decide) (by decide)
    (by rw [htl]; simp; omega)]
  rw [ite_eq_left (by decide)]

/-! ## Round trip -/

theorem itemBytes_length_le (it : UInt8 × UInt32) : (itemBytes it).length ≤ 11 := by
  unfold itemBytes
  split
  · simp
  · have := natDigitBytes_length_le it.2.toNat (by have := UInt32.toNat_lt it.2; omega)
    simp; omega

theorem flatMap_itemBytes_length (g : List (UInt8 × UInt32)) : (g.flatMap itemBytes).length ≤ 11 * g.length := by
  induction g with
  | nil => simp
  | cons it g ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have := itemBytes_length_le it; omega

theorem length_le_flatten {α : Type} (Gs : List (List α)) (h : ∀ g ∈ Gs, g ≠ []) : Gs.length ≤ Gs.flatten.length := by
  induction Gs with
  | nil => simp
  | cons g Gs ih =>
    simp only [List.length_cons, List.flatten_cons, List.length_append]
    have h1 := h g (by simp)
    have h2 := ih (fun g' hg' => h g' (by simp [hg']))
    have : g.length ≠ 0 := by simpa using h1
    omega

/-- The grid that `serializeRLE` reads items from. -/
def rleGrid (cells : Array (UInt32 × UInt32)) (minX minY : Int32) (w h : UInt32) : AsciiBytes :=
  fillGrid cells minX minY w h rleAlive (by decide) 0 cells.size.toUInt32
    (AsciiBytes.replicate (w * h) rleDead (by decide))

theorem serializeRLE_spec (cells : Array (UInt32 × UInt32)) (minX maxX minY maxY : Int32) (w h : UInt32)
    (hW : (maxX - minX + 1).toUInt32 = w) (hH : (maxY - minY + 1).toUInt32 = h)
    (hne : cells.size ≠ 0) (hcs : cells.size < 2 ^ 31) (hw : 1 ≤ w.toNat)
    (hwh : 64 * (w.toNat * h.toNat) < 2 ^ 31) :
    ∃ (Gs : List (List (UInt8 × UInt32))) (last : List (UInt8 × UInt32)) (re : UInt32),
      (serializeRLE cells minX maxX minY maxY).toList =
        (formatRLEHeader minX minY w h)[0]! :: (formatRLEHeader minX minY w h)[1]! ::
          (Gs ++ [last ++ [(rleEnd, 1)]]).map lineOf ∧
      (∀ g ∈ Gs, g ≠ []) ∧ (∀ g ∈ Gs, ∀ it ∈ g, ValidItem it) ∧ (∀ it ∈ last, ValidItem it) ∧
      (Gs.flatten ++ last).length ≤ 4 * (w.toNat * h.toNat) ∧
      RunsEq minX (((Gs.flatten ++ last) ++ pendItems rleDead 0 re).map itemRun)
        ((rawItems (rleGrid cells minX minY w h) w.toNat (w.toNat * h.toNat)).map itemRun) := by
  have hT : (w * h).toNat = w.toNat * h.toNat := by rw [UInt32.toNat_mul, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨hgs, hgget⟩ := fillGrid_replicate_spec cells minX minY w h rleAlive rleDead (by decide) (by decide)
    (by omega) (by omega)
  have hg : ∀ k, k < (w * h).toNat → (rleGrid cells minX minY w h).1[k]! = rleDead ∨
      (rleGrid cells minX minY w h).1[k]! = rleAlive := by
    intro k hk
    unfold rleGrid; rw [hgget k (by omega)]; split <;> simp
  obtain ⟨a', re, hrep, heq, hval, hsz⟩ := gridItems_spec minX (rleGrid cells minX minY w h) w (w * h)
    (by unfold rleGrid; rw [hgs, hT]) (by omega) (by rw [hT, Nat.mul_mod_right]) hg
    _ 0 rleDead 0 0 GrowBuf.empty #[] rfl (by simp) GrowBuf.rep_empty (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp [pendItems, rawItems]; exact RunsEq.refl _ _)
  have hser : serializeRLE cells minX maxX minY maxY =
      (wrapRLEItems ((gridItems (rleGrid cells minX minY w h) w (w * h) 0 rleDead 0 0 GrowBuf.empty).toArray.push
          (rleEnd, 1)) ((gridItems (rleGrid cells minX minY w h) w (w * h) 0 rleDead 0 0 GrowBuf.empty).toArray.push
          (rleEnd, 1)).size.toUInt32 0 "" 0
        (GrowBuf.empty.push (formatRLEHeader minX minY w h)[0]! |>.push (formatRLEHeader minX minY w h)[1]!)).toArray := by
    unfold serializeRLE
    rw [ite_eq_right (by simp [Nat.toUInt32]; rw [UInt32.ofNat_eq_iff_mod_eq_toNat]; simp; omega)]
    subst hW hH; rfl
  rw [hser, hrep.2.2.2]
  have ho := GrowBuf.rep_push (GrowBuf.rep_push (GrowBuf.rep_empty (α := String))
    (formatRLEHeader minX minY w h)[0]! (by decide)) (formatRLEHeader minX minY w h)[1]! (by simp)
  obtain ⟨groups, hgne, hflat, hrep2⟩ := wrapRLEItems_spec (a'.push (rleEnd, 1)) (by simp; omega) _ 0 [] 0 _ _ rfl
    (by simp) (by simp) (by simp) ho (by simp; omega)
  have e := hrep2.2.2.2
  simp only [show lineOf [] = "" from rfl, show (0 : Nat).toUInt32 = 0 from rfl] at e
  rw [e]
  have hfl : groups.flatten = a'.toList ++ [(rleEnd, 1)] := by simpa using hflat
  rcases List.eq_nil_or_concat groups with hg0 | ⟨Gs, gl, rfl⟩
  · subst hg0; simp at hfl
  rcases List.eq_nil_or_concat gl with hgl | ⟨last, x, rfl⟩
  · exact absurd hgl (hgne _ (by simp))
  simp only [List.concat_eq_append, List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
    ← List.append_assoc] at hfl
  obtain ⟨hA, hx⟩ := List.append_inj' hfl rfl
  simp only [List.cons.injEq, and_true] at hx; subst hx
  refine ⟨Gs, last, re, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · intro g hg; exact hgne g (by simp [hg])
  · intro g hg it hit; exact hval it (by rw [← hA]; simp; exact Or.inl ⟨g, hg, hit⟩)
  · intro it hit; exact hval it (by rw [← hA]; simp [hit])
  · rw [hA, hT] at *; simpa using hsz
  · rw [hA, ← hT]; exact heq

theorem deserializeRLE_lines (L : Array String) (minX minY : Int32) (w h : UInt32)
    (Gs : List (List (UInt8 × UInt32))) (last : List (UInt8 × UInt32))
    (hL : L.toList = (formatRLEHeader minX minY w h)[0]! :: (formatRLEHeader minX minY w h)[1]! ::
          (Gs ++ [last ++ [(rleEnd, 1)]]).map lineOf)
    (hne : ∀ g ∈ Gs, g ≠ []) (hv : ∀ g ∈ Gs, ∀ it ∈ g, ValidItem it) (hlv : ∀ it ∈ last, ValidItem it)
    (hlen : (Gs.flatten ++ last).length < 2 ^ 27) :
    ∃ runs' : GrowBuf (UInt32 × UInt32), runs'.Rep (((Gs.flatten ++ last ++ [(rleEnd, 1)]).map itemRun).toArray) ∧
      deserializeRLE L = finishRLE GrowBuf.empty runs' minX minY := by
  have hGs := length_le_flatten Gs hne
  have hfl : Gs.flatten.length + last.length < 2 ^ 27 := by simpa using hlen
  have hsize : L.size = Gs.length + 3 := by rw [← Array.length_toList, hL]; simp
  have hL31 : L.size < 2 ^ 31 := by omega
  have hb0 := byteArray_eq_of_toList (bytes_rleOffsetLine minX minY)
  have hb1 := byteArray_eq_of_toList (bytes_rleSizeLine w h)
  have h0 : (formatRLEHeader minX minY w h)[0]! = (formatRLEHeader minX minY 0 0)[0]! := rfl
  have h1 : (formatRLEHeader minX minY w h)[1]! = (formatRLEHeader 0 0 w h)[1]! := rfl
  obtain ⟨l⟩ := L
  simp only at hL
  subst hL
  rw [h0, h1] at hsize hL31 ⊢
  generalize hrest : (Gs ++ [last ++ [(rleEnd, 1)]]).map lineOf = rest at hsize hL31
  generalize hA : (formatRLEHeader minX minY 0 0)[0]! :: (formatRLEHeader 0 0 w h)[1]! :: rest = A at hsize hL31
  unfold deserializeRLE
  rw [ite_eq_right (by rw [beq_iff_eq, ← UInt32.toNat_inj, u32_size_toNat (by omega), UInt32.toNat_zero]; omega)]
  rw [parseRLEComments]
  rw [dite_eq_left_of_eq_true (by rw [eq_iff_iff, iff_true, u32_lt_size_iff (by omega), UInt32.toNat_zero]; omega)]
  have hA0 : (Array.mk A)[(0 : UInt32).toNat]! = (formatRLEHeader minX minY 0 0)[0]! := by
    subst hA; rfl
  have hA1 : (Array.mk A)[(0 + 1 : UInt32).toNat]! = (formatRLEHeader 0 0 w h)[1]! := by
    subst hA; rfl
  have c0 : ((formatRLEHeader minX minY 0 0)[0]!.toByteArray.size.toUInt32 != 0 &&
      (formatRLEHeader minX minY 0 0)[0]!.toByteArray.get! 0 == 35) = true := by
    rw [hb0, size_of_list, get!_of_list _ 0 (by simp)]
    have := bytes_toString_int32_length minX
    have := bytes_toString_int32_length minY
    have hne : ([35, 82, 32] ++ (toString minX).toByteArray.data.toList ++
        32 :: (toString minY).toByteArray.data.toList).length.toUInt32 ≠ 0 := by
      rw [ne_eq, ← UInt32.toNat_inj, u32_size_toNat (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)]
      simp
    rw [Bool.and_eq_true, bne_iff_ne]; exact ⟨hne, by simp⟩
  have c1 : ((formatRLEHeader 0 0 w h)[1]!.toByteArray.size.toUInt32 != 0 &&
      (formatRLEHeader 0 0 w h)[1]!.toByteArray.get! 0 == 35) = false := by
    rw [hb1, get!_of_list _ 0 (by simp)]
    simp
  simp only [hA0, c0, ite_true, parseRLEOffset_format, Bool.false_eq_true, ite_false]
  rw [parseRLEComments]
  rw [dite_eq_left_of_eq_true (by
    rw [eq_iff_iff, iff_true, u32_lt_size_iff (by omega), UInt32.toNat_add, UInt32.toNat_zero, UInt32.toNat_one]
    omega)]
  have hps : parseRLEHeader (formatRLEHeader 0 0 w h)[1]!.toByteArray = 0 := parseRLEHeader_sizeLine 0 0 w h
  simp only [hA1, c1, hps, Bool.false_eq_true, ite_false, bne_self_eq_false]
  have hl1 := flatMap_itemBytes_length (last ++ [(rleEnd, 1)])
  rw [List.length_append, List.length_singleton] at hl1
  obtain ⟨runs', hr, hp⟩ := parseRLEData_groups (Array.mk A) (by omega) GrowBuf.empty minX minY last hlv
    (by omega) Gs 2 GrowBuf.empty #[] (formatRLEHeader 0 0 w h)[1]!.toByteArray 0 0 0 0 false 0 0
    (by rw [← hA, ← hrest]; rfl) (by omega) hv
    (fun g hg => by
      have := flatMap_itemBytes_length g
      have := (List.sublist_flatten_of_mem hg).length_le
      omega)
    GrowBuf.rep_empty (by simp only [List.length_append, Array.size_empty] at hlen ⊢; omega)
  refine ⟨runs', by simpa using hr, ?_⟩
  exact hp

theorem decodeRuns_pend (sx x y : Int32) (re : UInt32) :
    decodeRuns sx ((pendItems rleDead 0 re).map itemRun) x y = [] := by
  unfold pendItems; split <;> simp [decodeRuns, itemRun_rowEnd]

theorem flatMap_length_le_one {α β : Type} (L : List α) (f : α → List β) (hf : ∀ x, (f x).length ≤ 1) :
    (L.flatMap f).length ≤ L.length := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have := hf x; omega

theorem gridCells_length_le (g : AsciiBytes) (W : Nat) (minX minY : Int32) (k : Nat) :
    (gridCells g W minX minY k).length ≤ k := by
  unfold gridCells
  have := flatMap_length_le_one (List.range k) _ (fun j => by
    show (if g.1[j]! = rleAlive then [(minX + (j % W).toUInt32.toInt32, minY + (j / W).toUInt32.toInt32)]
      else []).length ≤ 1
    split <;> simp)
  simpa using this

/-- The cells that `deserializeRLE` gives for serialized cells: the alive cells of the grid. -/
theorem rle_round_trip_grid (cells : Array (UInt32 × UInt32)) (minX maxX minY maxY : Int32) (w h : UInt32)
    (hW : (maxX - minX + 1).toUInt32 = w) (hH : (maxY - minY + 1).toUInt32 = h)
    (hne : cells.size ≠ 0) (hcs : cells.size < 2 ^ 31) (hw : 1 ≤ w.toNat)
    (hwh : 64 * (w.toNat * h.toNat) < 2 ^ 31) :
    deserializeRLE (serializeRLE cells minX maxX minY maxY) =
      ⟨0, "", 0, 0, #[], (gridCells (rleGrid cells minX minY w h) w.toNat minX minY (w.toNat * h.toNat)).toArray⟩ := by
  obtain ⟨Gs, last, re, hL, hgne, hv, hlv, hlen, heq⟩ :=
    serializeRLE_spec cells minX maxX minY maxY w h hW hH hne hcs hw hwh
  obtain ⟨runs', hr, hd⟩ := deserializeRLE_lines _ minX minY w h Gs last hL hgne hv hlv (by omega)
  rw [hd]
  unfold finishRLE
  rw [hr.2.2.2]
  dsimp only
  obtain ⟨hgs, hgget⟩ := fillGrid_replicate_spec cells minX minY w h rleAlive rleDead (by decide) (by decide)
    (by omega) (by omega)
  have hbytes : ∀ j, j < (rleGrid cells minX minY w h).1.size →
      (rleGrid cells minX minY w h).1[j]! = rleDead ∨ (rleGrid cells minX minY w h).1[j]! = rleAlive := by
    intro j hj
    unfold rleGrid at hj ⊢; rw [hgs] at hj; rw [hgget j hj]; split <;> simp
  have hdec : decodeRuns minX ((Gs.flatten ++ last ++ [(rleEnd, 1)]).map itemRun) minX minY =
      gridCells (rleGrid cells minX minY w h) w.toNat minX minY (w.toNat * h.toNat) := by
    have h1 := (heq minX minY).1
    rw [List.map_append, decodeRuns_append, decodeRuns_pend, List.append_nil] at h1
    rw [List.map_append, decodeRuns_append, h1]
    have h2 := (rawItems_decode (rleGrid cells minX minY w h) w.toNat hw minX minY hbytes (w.toNat * h.toNat)
      (by unfold rleGrid; omega)).1
    rw [h2]
    simp [decodeRuns, itemRun_end]
  have hRs : (((Gs.flatten ++ last ++ [(rleEnd, 1)]).map itemRun).toArray).size < 2 ^ 32 := by
    simp only [List.size_toArray, List.length_map, List.length_append, List.length_singleton] at hlen ⊢; omega
  have hex := expandRuns_spec (((Gs.flatten ++ last ++ [(rleEnd, 1)]).map itemRun).toArray) hRs minX _ 0 minX minY
    GrowBuf.empty #[] rfl (by simp) GrowBuf.rep_empty (by
      simp only [List.drop_zero, hdec, Array.size_empty, Nat.zero_add]
      have := gridCells_length_le (rleGrid cells minX minY w h) w.toNat minX minY (w.toNat * h.toNat)
      omega)
  have e := hex.2.2.2
  simp only [show (0 : Nat).toUInt32 = 0 from rfl, List.drop_zero, hdec,
    Array.empty_append] at e
  rw [e, GrowBuf.rep_empty.2.2.2]

theorem int32_box_cell (minX minY : Int32) (c : Int32 × Int32) (col r : Nat) (hc : (c.1 - minX).toUInt32.toNat = col)
    (hr : (c.2 - minY).toUInt32.toNat = r) :
    (minX + col.toUInt32.toInt32, minY + r.toUInt32.toInt32) = c := by
  have h1 : col.toUInt32 = (c.1 - minX).toUInt32 :=
    UInt32.toNat_inj.mp (by rw [u32_size_toNat (by have := UInt32.toNat_lt (c.1 - minX).toUInt32; omega), hc])
  have h2 : r.toUInt32 = (c.2 - minY).toUInt32 :=
    UInt32.toNat_inj.mp (by rw [u32_size_toNat (by have := UInt32.toNat_lt (c.2 - minY).toUInt32; omega), hr])
  rw [h1, h2, Int32.toInt32_toUInt32, Int32.toInt32_toUInt32, Int32.add_comm minX, Int32.sub_add_cancel,
    Int32.add_comm minY, Int32.sub_add_cancel]

/-- The alive cells of the grid are exactly the cells inside it. -/
theorem mem_gridCells_rleGrid (cells : Array (Int32 × Int32)) (minX minY : Int32) (w h : UInt32) (hw : 1 ≤ w.toNat)
    (hwh : w.toNat * h.toNat < 2 ^ 32) (hcs : cells.size < 2 ^ 32) (q : Int32 × Int32) :
    q ∈ gridCells (rleGrid (cells.map cellBits) minX minY w h) w.toNat minX minY (w.toNat * h.toNat) ↔
      ∃ c ∈ cells, (gridIndex minX minY w h c).isSome ∧ q = c := by
  obtain ⟨hgs, hgget⟩ := fillGrid_replicate_spec (cells.map cellBits) minX minY w h rleAlive rleDead (by decide)
    (by decide) (by simp; omega) hwh
  unfold gridCells
  simp only [List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨j, hj, hq⟩
    split at hq
    · rename_i hal
      simp only [List.mem_singleton] at hq; subst hq
      unfold rleGrid at hal; rw [hgget j hj] at hal
      split at hal
      · rename_i hex
        obtain ⟨cb, hcb, hidx⟩ := hex
        obtain ⟨cell, hcell, rfl⟩ := Array.mem_map.mp hcb
        simp only [cellBits, Int32.toInt32_toUInt32] at hidx
        have hj' : j = (j / w.toNat) * w.toNat + j % w.toNat := (Nat.div_add_mod' j w.toNat).symm
        rw [hj'] at hidx
        obtain ⟨-, -, hrr, hcc⟩ := (gridIndex_eq_iff (Nat.mod_lt _ (by omega))).mp hidx
        exact ⟨cell, hcell, by rw [hidx]; rfl, int32_box_cell minX minY cell _ _ hcc hrr⟩
      · simp [rleDead, rleAlive] at hal
    · simp at hq
  · rintro ⟨c, hq, hsome, rfl⟩
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hsome
    have hklt := gridIndex_lt hk
    refine ⟨k, hklt, ?_⟩
    have hal : (rleGrid (cells.map cellBits) minX minY w h).1[k]! = rleAlive := by
      unfold rleGrid
      rw [hgget k hklt, ite_eq_left ⟨cellBits q, Array.mem_map_of_mem hq, by
        simp only [cellBits, Int32.toInt32_toUInt32]; exact hk⟩]
    simp only [hal, ite_true, List.mem_singleton]
    unfold gridIndex at hk
    split at hk
    · rename_i hin
      simp only [Option.some.injEq] at hk
      subst hk
      have hx := UInt32.lt_iff_toNat_lt.mp hin.1
      have h1 : ((q.2 - minY).toUInt32.toNat * w.toNat + (q.1 - minX).toUInt32.toNat) / w.toNat =
          (q.2 - minY).toUInt32.toNat := by
        rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hx, Nat.add_zero]
      have h2 : ((q.2 - minY).toUInt32.toNat * w.toNat + (q.1 - minX).toUInt32.toNat) % w.toNat =
          (q.1 - minX).toUInt32.toNat := by
        rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hx]
      exact (int32_box_cell minX minY q _ _ h2.symm h1.symm).symm
    · simp at hk

/--
Round trip: deserializing serialized cells succeeds with no warnings, and the alive cells are exactly the cells
inside the bounding box, at their own coordinates.
-/
theorem rle_round_trip (cells : Array (Int32 × Int32)) (minX maxX minY maxY : Int32)
    (hne : cells.size ≠ 0) (hcs : cells.size < 2 ^ 31)
    (hw : 1 ≤ (maxX - minX + 1).toUInt32.toNat)
    (hwh : 64 * ((maxX - minX + 1).toUInt32.toNat * (maxY - minY + 1).toUInt32.toNat) < 2 ^ 31) :
    (deserializeRLE (serializeRLE (cells.map cellBits) minX maxX minY maxY)).status = 0 ∧
      (deserializeRLE (serializeRLE (cells.map cellBits) minX maxX minY maxY)).warnings = #[] ∧
      ∀ q, q ∈ (deserializeRLE (serializeRLE (cells.map cellBits) minX maxX minY maxY)).cells ↔
        ∃ c ∈ cells, (gridIndex minX minY (maxX - minX + 1).toUInt32 (maxY - minY + 1).toUInt32 c).isSome ∧ q = c := by
  generalize hW : (maxX - minX + 1).toUInt32 = w at hw hwh
  generalize hH : (maxY - minY + 1).toUInt32 = h at hwh
  rw [rle_round_trip_grid (cells.map cellBits) minX maxX minY maxY w h hW hH (by simpa using hne) (by simpa using hcs)
    hw hwh]
  refine ⟨rfl, rfl, fun q => ?_⟩
  rw [List.mem_toArray]
  exact mem_gridCells_rleGrid cells minX minY w h hw (by omega) (by omega) q

/-- Round trip for cells inside their bounding box: deserializing gives exactly the cells, with no warnings. -/
theorem rle_round_trip_box (cells : Array (Int32 × Int32)) (minX maxX minY maxY : Int32)
    (hne : cells.size ≠ 0) (hcs : cells.size < 2 ^ 31)
    (hbox : ∀ c ∈ cells, minX.toInt ≤ c.1.toInt ∧ c.1.toInt ≤ maxX.toInt ∧
      minY.toInt ≤ c.2.toInt ∧ c.2.toInt ≤ maxY.toInt)
    (hsize : 64 * ((maxX.toInt - minX.toInt + 1) * (maxY.toInt - minY.toInt + 1)) < 2 ^ 31) :
    (deserializeRLE (serializeRLE (cells.map cellBits) minX maxX minY maxY)).status = 0 ∧
      (deserializeRLE (serializeRLE (cells.map cellBits) minX maxX minY maxY)).warnings = #[] ∧
      ∀ q, q ∈ (deserializeRLE (serializeRLE (cells.map cellBits) minX maxX minY maxY)).cells ↔ q ∈ cells := by
  obtain ⟨c0, hc0⟩ : ∃ c, c ∈ cells := ⟨cells[0]'(by omega), Array.getElem_mem _⟩
  obtain ⟨hx1, hx2, hy1, hy2⟩ := hbox c0 hc0
  have hw1 : 1 ≤ maxX.toInt - minX.toInt + 1 := by omega
  have hh1 : 1 ≤ maxY.toInt - minY.toInt + 1 := by omega
  have hprod : (maxX.toInt - minX.toInt + 1) * (maxY.toInt - minY.toInt + 1) < 2 ^ 31 := by omega
  have hw : maxX.toInt - minX.toInt + 1 < 2 ^ 31 := by
    have : (maxX.toInt - minX.toInt + 1) * 1 ≤ (maxX.toInt - minX.toInt + 1) * (maxY.toInt - minY.toInt + 1) :=
      Int.mul_le_mul_of_nonneg_left hh1 (by omega)
    omega
  have hh : maxY.toInt - minY.toInt + 1 < 2 ^ 31 := by
    have : 1 * (maxY.toInt - minY.toInt + 1) ≤ (maxX.toInt - minX.toInt + 1) * (maxY.toInt - minY.toInt + 1) :=
      Int.mul_le_mul_of_nonneg_right hw1 (by omega)
    omega
  have hW := boxSize_toNat minX maxX (by omega) hw
  have hH := boxSize_toNat minY maxY (by omega) hh
  have hwh : 64 * ((maxX - minX + 1).toUInt32.toNat * (maxY - minY + 1).toUInt32.toNat) < 2 ^ 31 := by
    have : ((64 * ((maxX - minX + 1).toUInt32.toNat * (maxY - minY + 1).toUInt32.toNat) : Nat) : Int) < 2 ^ 31 := by
      rw [Int.natCast_mul, Int.natCast_mul, hW, hH]; exact hsize
    omega
  obtain ⟨hst, hwarn, hcells⟩ := rle_round_trip cells minX maxX minY maxY hne hcs (by omega) hwh
  refine ⟨hst, hwarn, fun q => ?_⟩
  rw [hcells]
  constructor
  · rintro ⟨c, hc, -, rfl⟩; exact hc
  · intro hq
    obtain ⟨hx1, hx2, hy1, hy2⟩ := hbox q hq
    exact ⟨q, hq, gridIndex_isSome_of_mem_box minX maxX minY maxY q hx1 hx2 hy1 hy2 hw hh, rfl⟩

end Algorithm
