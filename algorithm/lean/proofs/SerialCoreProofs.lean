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

import Algorithm.SerialCore

namespace Algorithm

/-! ## GrowBuf -/

theorem u32_size_toNat' {n : Nat} (hn : n < 2 ^ 32) : n.toUInt32.toNat = n := by
  rw [Nat.toUInt32, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hn]

/-- `b` holds exactly the elements of `a`. -/
def GrowBuf.Rep (b : GrowBuf α) (a : Array α) : Prop :=
  b.size.toNat = a.size ∧ a.size ≤ b.data.size ∧ b.data.size ≤ 2 * a.size + 1 ∧ b.toArray = a

theorem GrowBuf.rep_empty : (GrowBuf.empty : GrowBuf α).Rep #[] := by
  simp [GrowBuf.Rep, GrowBuf.empty, GrowBuf.toArray]

theorem copyPrefix_spec [Inhabited α] (src : Array α) (n : UInt32) :
    ∀ (m : Nat) (i : UInt32) (dst : Array α), n.toNat - i.toNat = m → n.toNat ≤ dst.size →
      (copyPrefix src n i dst).size = dst.size ∧
      ∀ (k : Nat) (hk : k < dst.size),
        (copyPrefix src n i dst)[k]! = if i.toNat ≤ k ∧ k < n.toNat then src[k]! else dst[k] := by
  intro m
  induction m with
  | zero =>
    intro i dst hm hd
    have hnot : ¬ i < n := by rw [UInt32.lt_iff_toNat_lt]; omega
    rw [copyPrefix]
    simp only [hnot, ↓reduceDIte, true_and]
    intro k hk
    rw [getElem!_pos dst k hk, ite_eq_right (by omega)]
  | succ m ih =>
    intro i dst hm hd
    have hlt : i < n := by rw [UInt32.lt_iff_toNat_lt]; omega
    have hsucc : (i + 1).toNat = i.toNat + 1 := by
      rw [UInt32.toNat_add]; have := UInt32.toNat_lt n; simp only [UInt32.toNat_one]; omega
    rw [copyPrefix]
    simp only [hlt, ↓reduceDIte]
    have hd' : n.toNat ≤ (dst.set! i.toNat src[i.toNat]!).size := by simp; omega
    obtain ⟨ihs, ihg⟩ := ih (i + 1) _ (by omega) hd'
    refine ⟨by rw [ihs]; simp, fun k hk => ?_⟩
    rw [ihg k (by simp; omega), hsucc]
    simp only [Array.set!_eq_setIfInBounds]
    by_cases hki : k = i.toNat
    · subst hki
      have := UInt32.lt_iff_toNat_lt.mp hlt
      simp only [Array.getElem_setIfInBounds_self]
      rw [ite_eq_right (by omega), ite_eq_left ⟨Nat.le_refl _, this⟩]
    · rw [Array.getElem_setIfInBounds_ne hk (Ne.symm hki)]
      by_cases hr : i.toNat + 1 ≤ k ∧ k < n.toNat
      · rw [ite_eq_left hr, ite_eq_left ⟨by omega, hr.2⟩]
      · rw [ite_eq_right hr]
        by_cases hr2 : i.toNat ≤ k ∧ k < n.toNat
        · omega
        · rw [ite_eq_right hr2]

theorem GrowBuf.rep_push {b : GrowBuf α} {a : Array α} (h : b.Rep a) (x : α) (hs : a.size + 1 < 2 ^ 31) :
    (b.push x).Rep (a.push x) := by
  obtain ⟨hsz, hle, hcap, harr⟩ := h
  have hcap32 : b.data.size < 2 ^ 32 := by omega
  have hsucc : (b.size + 1).toNat = a.size + 1 := by
    rw [UInt32.toNat_add, hsz]; simp; omega
  have hlt_iff : b.size < b.data.size.toUInt32 ↔ a.size < b.data.size := by
    rw [UInt32.lt_iff_toNat_lt, hsz, Nat.toUInt32, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hcap32]
  unfold GrowBuf.toArray at harr
  unfold GrowBuf.push
  split
  · rename_i hlt
    have hlt' := hlt_iff.mp hlt
    refine ⟨by simpa using hsucc, by simp; omega, by simp; omega, ?_⟩
    simp only [GrowBuf.toArray, hsucc, hsz]
    apply Array.ext
    · simp; omega
    · intro i hi1 hi2
      have hi2' : i < a.size + 1 := by simpa using hi2
      simp only [Array.getElem_extract, Nat.zero_add, Array.set!_eq_setIfInBounds, Array.getElem_push]
      split
      · rename_i hia
        rw [Array.getElem_setIfInBounds_ne (by omega) (show a.size ≠ i by omega)]
        subst harr
        simp
      · rename_i hia
        have : i = a.size := by omega
        subst this
        simp
  · rename_i hlt
    have heq : a.size = b.data.size := by have := mt hlt_iff.mpr hlt; omega
    have hcapn : (b.data.size.toUInt32).toNat = b.data.size := u32_size_toNat' hcap32
    have hnew : (2 * b.data.size.toUInt32 + 1).toNat = 2 * b.data.size + 1 := by
      rw [UInt32.toNat_add, UInt32.toNat_mul, hcapn]; simp; omega
    dsimp only
    letI : Inhabited α := ⟨x⟩
    have hcp := copyPrefix_spec b.data b.data.size.toUInt32 _ 0
      (Array.replicate (2 * b.data.size.toUInt32 + 1).toNat x) rfl (by simp [hnew]; omega)
    generalize hg : copyPrefix b.data b.data.size.toUInt32 0
      (Array.replicate (2 * b.data.size.toUInt32 + 1).toNat x) = g at hcp ⊢
    obtain ⟨hgs, hgg⟩ := hcp
    simp only [Array.size_replicate, hnew] at hgs hgg
    refine ⟨by simpa using hsucc, by simp only [Array.size_push]; omega, by simp only [Array.size_push]; omega, ?_⟩
    simp only [GrowBuf.toArray, hsucc]
    apply Array.ext
    · simp; omega
    · intro k hk1 hk2
      have hk2' : k < a.size + 1 := by simpa using hk2
      simp only [Array.getElem_extract, Nat.zero_add]
      have := hgg k (by omega)
      rw [getElem!_pos g k (by omega), hcapn] at this
      rw [this, Array.getElem_push]
      by_cases hka : k < a.size
      · rw [ite_eq_left ⟨Nat.zero_le _, by omega⟩, dite_eq_left hka, getElem!_pos b.data k (by omega)]
        subst harr
        simp only [Array.getElem_extract, Nat.zero_add]
      · rw [ite_eq_right (by omega), dite_eq_right hka]
        simp

/-! ## U64Buf -/

theorem copyU64_eq (src : Array UInt64) (n : UInt32) :
    ∀ (m : Nat) (i : UInt32) (dst : Array UInt64), n.toNat - i.toNat = m →
      copyU64 src n i dst = copyPrefix src n i dst := by
  intro m
  induction m with
  | zero =>
    intro i dst hm
    have hnot : ¬ i < n := by rw [UInt32.lt_iff_toNat_lt]; omega
    rw [copyU64, copyPrefix]
    simp only [hnot, ↓reduceDIte]
  | succ m ih =>
    intro i dst hm
    have hlt : i < n := by rw [UInt32.lt_iff_toNat_lt]; omega
    have hsucc : (i + 1).toNat = i.toNat + 1 := by
      rw [UInt32.toNat_add]; have := UInt32.toNat_lt n; simp only [UInt32.toNat_one]; omega
    rw [copyU64, copyPrefix]
    simp only [hlt, ↓reduceDIte]
    exact ih (i + 1) _ (by omega)

/-- `b` holds exactly the elements of `a`. -/
def U64Buf.Rep (b : U64Buf) (a : Array UInt64) : Prop :=
  b[0]!.toNat = a.size ∧ a.size < b.size ∧ b.size < 2 ^ 32 ∧ U64Buf.toArray b = a

theorem U64Buf.rep_empty : U64Buf.Rep U64Buf.empty #[] := by
  refine ⟨?_, by simp [U64Buf.empty], by simp [U64Buf.empty], ?_⟩
  · simp [U64Buf.empty]
  · simp [U64Buf.empty, U64Buf.toArray]

theorem U64Buf.toArray_of_rep {b : U64Buf} {a : Array UInt64} (h : U64Buf.Rep b a) : U64Buf.toArray b = a :=
  h.2.2.2

theorem U64Buf.rep_push {b : U64Buf} {a : Array UInt64} (h : U64Buf.Rep b a) (x : UInt64)
    (hs : a.size + 1 < 2 ^ 31) : U64Buf.Rep (U64Buf.push b x) (a.push x) := by
  obtain ⟨h0, hlt, hb32, harr⟩ := h
  have hn : (b[0]!.toUInt32 + 1).toNat = a.size + 1 := by
    rw [UInt32.toNat_add, UInt64.toNat_toUInt32, h0]; simp; omega
  have hn64 : ((b[0]!.toUInt32 + 1).toUInt64).toNat = a.size + 1 := by
    rw [UInt32.toNat_toUInt64, hn]
  have hbsz : b.size.toUInt32.toNat = b.size := u32_size_toNat' hb32
  -- The elements of `b` after element 0.
  have helem : ∀ k (hk : k < a.size), b[k + 1]! = a[k] := by
    intro k hk
    have hsz : (U64Buf.toArray b).size = a.size := by rw [harr]
    have hk' : k < (U64Buf.toArray b).size := by omega
    have : a[k] = (U64Buf.toArray b)[k] := by simp only [harr]
    rw [this]
    simp only [U64Buf.toArray, Array.getElem_extract]
    simp only [U64Buf.toArray, Array.size_extract] at hk'
    rw [getElem!_pos b (k + 1) (by omega)]
    congr 1; omega
  unfold U64Buf.push
  dsimp only
  generalize hN : b[0]!.toUInt32 + 1 = N at hn hn64
  have hN32 : N.toUInt64.toUInt32 = N := by
    apply UInt32.toNat_inj.mp; rw [UInt64.toNat_toUInt32, UInt32.toNat_toUInt64]; have := UInt32.toNat_lt N; omega
  have hN1 : (N + 1).toNat = a.size + 2 := by rw [UInt32.toNat_add, hn]; simp; omega
  split
  · rename_i hcap
    rw [UInt32.lt_iff_toNat_lt, hn, hbsz] at hcap
    simp only [Array.set!_eq_setIfInBounds]
    have h0' : ((b.setIfInBounds N.toNat x).setIfInBounds 0 N.toUInt64)[0]! = N.toUInt64 := by
      rw [getElem!_pos _ 0 (by simp; omega)]; simp
    refine ⟨by rw [h0', hn64, Array.size_push], by simp; omega, by simp; omega, ?_⟩
    simp only [U64Buf.toArray, h0', hN32, hN1]
    apply Array.ext
    · simp; omega
    · intro k hk1 hk2
      have hk2' : k < a.size + 1 := by simpa using hk2
      simp only [Array.getElem_extract, Array.getElem_push]
      rw [Array.getElem_setIfInBounds_ne (by simp; omega) (by omega)]
      by_cases hka : k < a.size
      · rw [Array.getElem_setIfInBounds_ne (by omega) (by omega), dite_eq_left hka]
        have := helem k hka
        rw [getElem!_pos b (k + 1) (by omega)] at this
        rw [← this]; congr 1; omega
      · rw [dite_eq_right hka]
        have : k = a.size := by omega
        subst this
        rw [Array.getElem_setIfInBounds (by first | omega | (simp; omega)), ite_eq_left (by omega)]
  · rename_i hcap
    rw [UInt32.lt_iff_toNat_lt, hn, hbsz] at hcap
    have heq : b.size = a.size + 1 := by omega
    have hnew : (2 * b.size.toUInt32 + 1).toNat = 2 * b.size + 1 := by
      rw [UInt32.toNat_add, UInt32.toNat_mul, hbsz]; simp; omega
    rw [copyU64_eq _ _ _ 0 _ rfl]
    have hcp := copyPrefix_spec b b.size.toUInt32 _ 0
      (Array.replicate (2 * b.size.toUInt32 + 1).toNat 0) rfl (by simp [hnew, hbsz]; omega)
    generalize hg : copyPrefix b b.size.toUInt32 0 (Array.replicate (2 * b.size.toUInt32 + 1).toNat 0) = g at hcp ⊢
    obtain ⟨hgs, hgg⟩ := hcp
    simp only [Array.size_replicate, hnew, hbsz] at hgs hgg
    simp only [Array.set!_eq_setIfInBounds]
    have h0' : ((g.setIfInBounds N.toNat x).setIfInBounds 0 N.toUInt64)[0]! = N.toUInt64 := by
      rw [getElem!_pos _ 0 (by simp; omega)]; simp
    refine ⟨by rw [h0', hn64, Array.size_push], by simp; omega, by simp; omega, ?_⟩
    simp only [U64Buf.toArray, h0', hN32, hN1]
    apply Array.ext
    · simp; omega
    · intro k hk1 hk2
      have hk2' : k < a.size + 1 := by simpa using hk2
      simp only [Array.getElem_extract, Array.getElem_push]
      rw [Array.getElem_setIfInBounds_ne (by simp; omega) (by omega)]
      by_cases hka : k < a.size
      · rw [Array.getElem_setIfInBounds_ne (by omega) (by omega), dite_eq_left hka]
        have := hgg (1 + k) (by omega)
        rw [getElem!_pos g (1 + k) (by omega), ite_eq_left ⟨Nat.zero_le _, by omega⟩] at this
        rw [this]
        have := helem k hka
        rw [show 1 + k = k + 1 by omega, this]
      · rw [dite_eq_right hka]
        have : k = a.size := by omega
        subst this
        rw [Array.getElem_setIfInBounds (by first | omega | (simp; omega)), ite_eq_left (by omega)]

/-! ## Cell keys -/

theorem cellKey_toNat (x y : UInt32) : (cellKey x y).toNat = x.toNat * 2 ^ 32 + y.toNat := by
  have hx := UInt32.toNat_lt x
  have hy := UInt32.toNat_lt y
  have hmask : (y.toUInt64 &&& 0xFFFFFFFF).toNat = y.toNat := by
    rw [UInt64.toNat_and, UInt32.toNat_toUInt64, show (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hy]
  simp only [cellKey, UInt64.toNat_add, UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64, Nat.shiftLeft_eq, hmask]
  simp
  omega

theorem keyX_cellKey (x y : UInt32) : cellKeyX (cellKey x y) = x := by
  apply UInt32.toNat_inj.mp
  have hy := UInt32.toNat_lt y
  have hx := UInt32.toNat_lt x
  simp only [cellKeyX, UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, cellKey_toNat, Nat.shiftRight_eq_div_pow]
  simp
  omega

theorem keyY_cellKey (x y : UInt32) : cellKeyY (cellKey x y) = y := by
  apply UInt32.toNat_inj.mp
  have hy := UInt32.toNat_lt y
  simp only [cellKeyY, UInt64.toNat_toUInt32, cellKey_toNat]
  omega

theorem cellKey_keys (k : UInt64) : cellKey (cellKeyX k) (cellKeyY k) = k := by
  apply UInt64.toNat_inj.mp
  have hk := UInt64.toNat_lt k
  rw [cellKey_toNat]
  simp only [cellKeyX, cellKeyY, UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  simp
  omega

theorem cellBits_inj {c d : Int32 × Int32} (h : cellBits c = cellBits d) : c = d := by
  have h1 := congrArg cellKeyX h
  have h2 := congrArg cellKeyY h
  simp only [cellBits, keyX_cellKey, keyY_cellKey] at h1 h2
  have e1 : c.1 = d.1 := by
    have := congrArg UInt32.toInt32 h1; simpa using this
  have e2 : c.2 = d.2 := by
    have := congrArg UInt32.toInt32 h2; simpa using this
  exact Prod.ext e1 e2

@[simp] theorem keyX_cellBits (c : Int32 × Int32) : cellKeyX (cellBits c) = c.1.toUInt32 := keyX_cellKey _ _

@[simp] theorem keyY_cellBits (c : Int32 × Int32) : cellKeyY (cellBits c) = c.2.toUInt32 := keyY_cellKey _ _

theorem cellBits_mem_map {c : Int32 × Int32} {l : List (Int32 × Int32)} : cellBits c ∈ l.map cellBits ↔ c ∈ l := by
  constructor
  · intro h
    obtain ⟨d, hd, he⟩ := List.mem_map.mp h
    rwa [cellBits_inj he] at hd
  · exact List.mem_map_of_mem

/-! ## Byte views -/

/-- The bytes of `b` from position `p` on. -/
def bytesFrom (b : ByteArray) (p : Nat) : List UInt8 := b.data.toList.drop p

theorem bytesFrom_of_lt {b : ByteArray} {p : Nat} (h : p < b.size) :
    bytesFrom b p = b[p] :: bytesFrom b (p + 1) := by
  unfold bytesFrom
  have h' : p < b.data.toList.length := by rw [Array.length_toList]; exact h
  rw [List.drop_eq_getElem_cons h', Array.getElem_toList]
  rfl

theorem bytesFrom_of_ge {b : ByteArray} {p : Nat} (h : b.size ≤ p) : bytesFrom b p = [] := by
  unfold bytesFrom
  simp only [List.drop_eq_nil_iff, Array.length_toList]
  exact h

theorem byteArray_get!_eq {b : ByteArray} {p : Nat} (h : p < b.size) : b.get! p = b[p] := by
  obtain ⟨bs⟩ := b
  unfold ByteArray.get!
  have h' : p < bs.size := h
  simp only
  rw [getElem!_pos bs p h']
  rfl

theorem u32_toNat_succ {p : UInt32} {n : Nat} (hp : p.toNat < n) (hn : n < 2 ^ 32) :
    (p + 1).toNat = p.toNat + 1 := by
  rw [UInt32.toNat_add]; simp; omega

theorem u32_size_toNat {n : Nat} (hn : n < 2 ^ 32) : n.toUInt32.toNat = n := by
  rw [Nat.toUInt32, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hn]

theorem u32_lt_size_iff {p : UInt32} {n : Nat} (hn : n < 2 ^ 32) : p < n.toUInt32 ↔ p.toNat < n := by
  rw [UInt32.lt_iff_toNat_lt, u32_size_toNat hn]

/-! ## Digit scanning -/

/-- One step of `scanDigits`, which stops growing past 2^32. -/
def satStep (acc : Nat) (x : UInt8) : Nat := if acc > 4294967296 then acc else acc * 10 + (x.toNat - 48)

theorem satStep_le {acc : Nat} {x : UInt8} (ha : acc ≤ 42949672969) (hx : isDigitByte x = true) :
    satStep acc x ≤ 42949672969 := by
  simp only [isDigitByte, Bool.and_eq_true, decide_eq_true_eq] at hx
  have : x.toNat ≤ 57 := hx.2
  unfold satStep; split <;> omega

theorem foldl_satStep_le (ds : List UInt8) (hds : ∀ x ∈ ds, isDigitByte x = true) :
    ∀ acc, acc ≤ 42949672969 → ds.foldl satStep acc ≤ 42949672969 := by
  induction ds with
  | nil => intro acc h; exact h
  | cons x xs ih =>
    intro acc h
    exact ih (fun y hy => hds y (by simp [hy])) _ (satStep_le h (hds x (by simp)))

theorem scanDigits_spec (b : ByteArray) (hb : b.size < 2 ^ 32) :
    ∀ (n : Nat) (p : UInt32) (acc : UInt64), b.size - p.toNat = n → p.toNat ≤ b.size →
      acc.toNat ≤ 42949672969 →
      (scanDigits b b.size.toUInt32 p acc).1.toNat =
          p.toNat + ((bytesFrom b p.toNat).takeWhile isDigitByte).length ∧
      (scanDigits b b.size.toUInt32 p acc).2.toNat =
          ((bytesFrom b p.toNat).takeWhile isDigitByte).foldl satStep acc.toNat := by
  intro n
  induction n with
  | zero =>
    intro p acc hn hp ha
    have hge : b.size ≤ p.toNat := by omega
    have hnot : ¬ p < b.size.toUInt32 := by rw [u32_lt_size_iff hb]; omega
    rw [scanDigits]
    simp only [hnot, ↓reduceDIte, bytesFrom_of_ge hge]
    simp
  | succ n ih =>
    intro p acc hn hp ha
    have hlt : p.toNat < b.size := by omega
    have hsucc := u32_toNat_succ hlt hb
    have hyes : p < b.size.toUInt32 := by rw [u32_lt_size_iff hb]; omega
    rw [scanDigits]
    simp only [hyes, ↓reduceDIte, bytesFrom_of_lt hlt, byteArray_get!_eq hlt]
    by_cases hd : isDigitByte b[p.toNat] = true
    · simp only [hd, ite_true, List.takeWhile_cons_of_pos hd, List.length_cons, List.foldl_cons]
      have hstep : (if acc > 4294967296 then acc else acc * 10 + (b[p.toNat].toUInt64 - 48)).toNat =
          satStep acc.toNat b[p.toNat] := by
        simp only [isDigitByte, Bool.and_eq_true, decide_eq_true_eq] at hd
        have h1 : 48 ≤ b[p.toNat].toNat := hd.1
        have h2 : b[p.toNat].toNat ≤ 57 := hd.2
        unfold satStep
        by_cases hgt : acc > 4294967296
        · have : acc.toNat > 4294967296 := hgt
          simp [hgt, this]
        · have : ¬ acc.toNat > 4294967296 := hgt
          simp only [hgt, this, ite_false]
          rw [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_sub_of_le _ _ (by
            rw [UInt64.le_iff_toNat_le]; simp; omega)]
          simp; omega
      have hacc' := hstep ▸ satStep_le ha hd
      have := ih (p + 1) _ (by omega) (by omega) hacc'
      rw [hsucc, hstep] at this
      rw [this.1, this.2]
      exact ⟨by omega, rfl⟩
    · simp only [hd, Bool.false_eq_true, ite_false, List.takeWhile_cons_of_neg hd]
      simp

/-- The value of a list of decimal digit bytes. -/
def digitsValue (ds : List UInt8) : Nat := ds.foldl (fun a x => a * 10 + (x.toNat - 48)) 0

theorem foldl_digit_ge (ds : List UInt8) : ∀ a, a ≤ ds.foldl (fun a x => a * 10 + (x.toNat - 48)) a := by
  induction ds with
  | nil => intro a; exact Nat.le_refl a
  | cons x xs ih =>
    intro a
    have : a ≤ a * 10 + (x.toNat - 48) := by omega
    exact Nat.le_trans this (ih _)

theorem foldl_satStep_saturated (ds : List UInt8) : ∀ a, 4294967296 < a → ds.foldl satStep a = a := by
  induction ds with
  | nil => intro a _; rfl
  | cons x xs ih =>
    intro a ha
    rw [List.foldl_cons, show satStep a x = a by simp [satStep, ha], ih a ha]

/-- The saturating fold agrees with the exact value up to 2^32 and stays above it past that. -/
theorem foldl_satStep_eq (ds : List UInt8) : ∀ a, a ≤ 4294967296 →
    (ds.foldl (fun a x => a * 10 + (x.toNat - 48)) a ≤ 4294967296 →
      ds.foldl satStep a = ds.foldl (fun a x => a * 10 + (x.toNat - 48)) a) ∧
    (4294967296 < ds.foldl (fun a x => a * 10 + (x.toNat - 48)) a → 4294967296 < ds.foldl satStep a) := by
  induction ds with
  | nil => intro a _; simp
  | cons x xs ih =>
    intro a ha
    have hstep : satStep a x = a * 10 + (x.toNat - 48) := by
      simp only [satStep, show ¬ (a > 4294967296) by omega, ite_false]
    simp only [List.foldl_cons, hstep]
    by_cases hle : a * 10 + (x.toNat - 48) ≤ 4294967296
    · exact ih _ hle
    · have hsat := foldl_satStep_saturated xs (a * 10 + (x.toNat - 48)) (by omega)
      have hge := foldl_digit_ge xs (a * 10 + (x.toNat - 48))
      rw [hsat]
      exact ⟨fun h => by omega, fun _ => by omega⟩

/-- What `parseInt32At` reads from a list of bytes: the value and the number of bytes. -/
def parseInt32Spec (l : List UInt8) : Option (Int32 × Nat) :=
  if l.head? = some 45 then
    let ds := l.tail.takeWhile isDigitByte
    if ds = [] ∨ 2 ^ 31 < digitsValue ds then none
    else some (Int32.ofInt (-(digitsValue ds : Int)), ds.length + 1)
  else
    let ds := l.takeWhile isDigitByte
    if ds = [] ∨ 2 ^ 31 ≤ digitsValue ds then none
    else some (Int32.ofNat (digitsValue ds), ds.length)

theorem u64_toUInt32_toInt32 (v : UInt64) :
    v.toUInt32.toInt32 = Int32.ofNat v.toNat := by
  have : v.toUInt32 = UInt32.ofNat v.toNat := by
    apply UInt32.toNat_inj.mp
    rw [UInt64.toNat_toUInt32, UInt32.toNat_ofNat']
  rw [this, UInt32.toInt32_ofNat']

theorem int32_zero_sub_ofNat (n : Nat) (h : n ≤ 2 ^ 31) :
    (0 : Int32) - Int32.ofNat n = Int32.ofInt (-(n : Int)) := by
  apply Int32.toInt_inj.mp
  rw [Int32.toInt_ofInt, Int32.toInt_sub, Int32.toInt_zero, Int32.toInt_ofNat']
  simp only [Int32.size]
  by_cases hlt : n < 2 ^ 31
  · rw [Int.bmod_eq_of_le (n := (n : Int)) (by omega) (by omega), Int.zero_sub]
  · have : n = 2 ^ 31 := by omega
    subst this
    decide

theorem takeWhile_all {l : List UInt8} : ∀ x ∈ l.takeWhile isDigitByte, isDigitByte x = true := by
  intro x hx
  have := List.all_takeWhile (p := isDigitByte) (l := l)
  rw [List.all_eq_true] at this
  exact this x hx

theorem length_bytesFrom (b : ByteArray) (p : Nat) : (bytesFrom b p).length = b.size - p := by
  rw [bytesFrom, List.length_drop, Array.length_toList]
  rfl

/-- `scanDigits` from `p` with nothing accumulated yet: its end and value. -/
theorem scanDigits_zero (b : ByteArray) (hb : b.size < 2 ^ 32) (p : UInt32) (hp : p.toNat ≤ b.size) :
    let ds := (bytesFrom b p.toNat).takeWhile isDigitByte
    (scanDigits b b.size.toUInt32 p 0).1.toNat = p.toNat + ds.length ∧
    (ds.foldl (fun a x => a * 10 + (x.toNat - 48)) 0 ≤ 4294967296 →
      (scanDigits b b.size.toUInt32 p 0).2.toNat = digitsValue ds) ∧
    (4294967296 < digitsValue ds → 4294967296 < (scanDigits b b.size.toUInt32 p 0).2.toNat) := by
  have h := scanDigits_spec b hb _ p 0 rfl hp (by simp)
  have h2 := foldl_satStep_eq ((bytesFrom b p.toNat).takeWhile isDigitByte) 0 (by omega)
  simp only [UInt64.toNat_zero] at h
  refine ⟨h.1, fun hle => ?_, fun hgt => ?_⟩
  · rw [h.2, h2.1 hle]; rfl
  · rw [h.2]; exact h2.2 hgt

theorem parseInt32At_spec (b : ByteArray) (hb : b.size < 2 ^ 32) (pos : UInt32) (hp : pos.toNat ≤ b.size) :
    parseInt32At b pos b.size.toUInt32 =
      (parseInt32Spec (bytesFrom b pos.toNat)).map (fun r => ⟨r.1, pos + r.2.toUInt32⟩) := by
  unfold parseInt32At parseInt32Spec
  have hlenL := length_bytesFrom b pos.toNat
  by_cases hneg : pos < b.size.toUInt32 && b.get! pos.toNat == 45
  · -- A leading minus sign.
    have hlt : pos.toNat < b.size := by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hneg
      exact (u32_lt_size_iff hb).mp hneg.1
    have h45 : b[pos.toNat] = 45 := by
      simp only [Bool.and_eq_true, beq_iff_eq] at hneg
      rw [← byteArray_get!_eq hlt]; exact hneg.2
    have hL := bytesFrom_of_lt hlt
    have hsucc := u32_toNat_succ hlt hb
    obtain ⟨he, hv1, hv2⟩ := scanDigits_zero b hb (pos + 1) (by omega)
    rw [hsucc] at he hv1 hv2
    simp only [hneg, ite_true, hL, List.head?_cons, h45, List.tail_cons]
    generalize hds : (bytesFrom b (pos.toNat + 1)).takeWhile isDigitByte = ds at he hv1 hv2
    have hdslen : ds.length ≤ b.size - (pos.toNat + 1) := by
      rw [← hds, ← length_bytesFrom]; exact (List.takeWhile_sublist _).length_le
    generalize hsc : scanDigits b b.size.toUInt32 (pos + 1) 0 = sc at he hv1 hv2
    obtain ⟨e, v⟩ := sc
    simp only at he hv1 hv2 ⊢
    by_cases hnil : ds = []
    · subst hnil
      have : e = pos + 1 := by apply UInt32.toNat_inj.mp; rw [he, hsucc]; rfl
      simp [this]
    · have hne : ¬ (e == pos + 1) = true := by
        intro h
        have := congrArg UInt32.toNat (beq_iff_eq.mp h)
        rw [he, hsucc] at this
        exact hnil (List.length_eq_zero_iff.mp (by omega))
      simp only [hne, Bool.false_eq_true, ite_false, hnil, false_or]
      have hepos : pos + (ds.length + 1).toUInt32 = e := by
        apply UInt32.toNat_inj.mp
        rw [UInt32.toNat_add, he, u32_size_toNat (by omega)]
        omega
      by_cases hbig : 2 ^ 31 < digitsValue ds
      · have hv : ¬ v ≤ 2147483648 := by
          rw [UInt64.le_iff_toNat_le]
          by_cases hsat : 4294967296 < digitsValue ds
          · have := hv2 hsat; simp; omega
          · rw [hv1 (by simpa [digitsValue] using (show digitsValue ds ≤ 4294967296 by omega))]; simp; omega
        simp [hv, hbig]
      · have hvle : v.toNat = digitsValue ds :=
          hv1 (by simpa [digitsValue] using (show digitsValue ds ≤ 4294967296 by omega))
        have hv : v ≤ 2147483648 := by rw [UInt64.le_iff_toNat_le]; simp; omega
        simp only [hv, ite_true, hbig, ite_false, Option.map_some, hepos]
        rw [u64_toUInt32_toInt32 v, hvle, int32_zero_sub_ofNat _ (by omega)]
  · -- No minus sign.
    have hnot45 : (bytesFrom b pos.toNat).head? ≠ some 45 := by
      intro h
      apply hneg
      by_cases hlt : pos.toNat < b.size
      · rw [bytesFrom_of_lt hlt] at h
        simp only [List.head?_cons, Option.some.injEq] at h
        simp [(u32_lt_size_iff hb).mpr hlt, byteArray_get!_eq hlt, h]
      · rw [bytesFrom_of_ge (by omega)] at h; simp at h
    simp only [hneg, Bool.false_eq_true, ite_false, hnot45]
    obtain ⟨he, hv1, hv2⟩ := scanDigits_zero b hb pos hp
    generalize hds : (bytesFrom b pos.toNat).takeWhile isDigitByte = ds at he hv1 hv2
    have hdslen : ds.length ≤ b.size - pos.toNat := by
      rw [← hds, ← length_bytesFrom]; exact (List.takeWhile_sublist _).length_le
    generalize hsc : scanDigits b b.size.toUInt32 pos 0 = sc at he hv1 hv2
    obtain ⟨e, v⟩ := sc
    simp only at he hv1 hv2 ⊢
    by_cases hnil : ds = []
    · subst hnil
      have : e = pos := by apply UInt32.toNat_inj.mp; rw [he]; rfl
      simp [this]
    · have hne : ¬ (e == pos) = true := by
        intro h
        have := congrArg UInt32.toNat (beq_iff_eq.mp h)
        rw [he] at this
        exact hnil (List.length_eq_zero_iff.mp (by omega))
      simp only [hne, Bool.false_eq_true, ite_false, hnil, false_or]
      have hepos : pos + ds.length.toUInt32 = e := by
        apply UInt32.toNat_inj.mp
        rw [UInt32.toNat_add, he, u32_size_toNat (by omega)]
        omega
      by_cases hbig : 2 ^ 31 ≤ digitsValue ds
      · have hv : ¬ v ≤ 2147483647 := by
          rw [UInt64.le_iff_toNat_le]
          by_cases hsat : 4294967296 < digitsValue ds
          · have := hv2 hsat; simp; omega
          · rw [hv1 (by simpa [digitsValue] using (show digitsValue ds ≤ 4294967296 by omega))]; simp; omega
        simp [hv, hbig]
      · have hvle : v.toNat = digitsValue ds :=
          hv1 (by simpa [digitsValue] using (show digitsValue ds ≤ 4294967296 by omega))
        have hv : v ≤ 2147483647 := by rw [UInt64.le_iff_toNat_le]; simp; omega
        simp only [hv, ite_true, hbig, ite_false, Option.map_some, hepos]
        rw [show uint32ToInt32 v.toUInt32 = v.toUInt32.toInt32 from rfl, u64_toUInt32_toInt32 v, hvle]

/-! ## Decimal formatting -/

/-- The ASCII bytes of the decimal digits of `n`. -/
def natDigitBytes (n : Nat) : List UInt8 := (Nat.toDigits 10 n).map (fun c => c.toNat.toUInt8)

theorem digitsValue_append_single (ds : List UInt8) (d : UInt8) :
    digitsValue (ds ++ [d]) = digitsValue ds * 10 + (d.toNat - 48) := by
  simp [digitsValue, List.foldl_append]

theorem natDigitBytes_spec : ∀ n, (∀ y ∈ natDigitBytes n, 48 ≤ y.toNat ∧ y.toNat ≤ 57) ∧
    digitsValue (natDigitBytes n) = n ∧ natDigitBytes n ≠ [] := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    have hdig : ∀ k, k < 10 → (Nat.digitChar k).toNat.toUInt8.toNat = 48 + k := by
      intro k hk
      rw [Nat.toNat_digitChar_of_lt_ten hk]
      simp; omega
    unfold natDigitBytes
    rw [Nat.toDigits_eq_ite (by omega)]
    split
    · rename_i hlt
      simp only [List.map_cons, List.map_nil, List.mem_singleton, forall_eq, hdig n hlt, digitsValue,
        List.foldl_cons, List.foldl_nil, ne_eq, reduceCtorEq, not_false_eq_true, and_true]
      omega
    · rename_i hge
      obtain ⟨h1, h2, h3⟩ := ih (n / 10) (by omega)
      unfold natDigitBytes at h1 h2 h3
      rw [List.map_append, List.map_cons, List.map_nil, digitsValue_append_single, h2,
        hdig (n % 10) (by omega)]
      refine ⟨?_, by omega, by simp⟩
      intro y hy
      rw [List.mem_append, List.mem_singleton] at hy
      rcases hy with hy | rfl
      · exact h1 y hy
      · rw [hdig (n % 10) (by omega)]; omega

theorem utf8EncodeChar_ascii (c : Char) (hc : c.toNat < 128) :
    String.utf8EncodeChar c = [c.toNat.toUInt8] := by
  have : c.val.toNat = c.toNat := rfl
  simp only [String.utf8EncodeChar, this, show c.toNat ≤ 0x7f by omega, ite_true]

theorem toByteArray_ofList_ascii (cs : List Char) (h : ∀ c ∈ cs, c.toNat < 128) :
    (String.ofList cs).toByteArray.data.toList = cs.map (fun c => c.toNat.toUInt8) := by
  rw [String.toByteArray_ofList, List.utf8Encode]
  simp only
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [List.flatMap_cons, utf8EncodeChar_ascii c (h c (by simp)), List.map_cons,
      ih (fun d hd => h d (by simp [hd]))]
    rfl

theorem toDigits_ascii (n : Nat) : ∀ c ∈ Nat.toDigits 10 n, c.toNat < 128 := by
  intro c hc
  have := Nat.isDigit_of_mem_toDigits (by omega) (by omega) hc
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at this
  have h2 : c.val ≤ '9'.val := this.2
  have : c.val.toNat ≤ 57 := by rw [UInt32.le_iff_toNat_le] at h2; exact h2
  exact Nat.lt_of_le_of_lt this (by decide)

theorem bytes_natRepr (n : Nat) : n.repr.toByteArray.data.toList = natDigitBytes n := by
  rw [Nat.repr_eq_ofList_toDigits, toByteArray_ofList_ascii _ (toDigits_ascii n)]
  rfl

theorem byteArray_append_toList (a b : ByteArray) : (a ++ b).data.toList = a.data.toList ++ b.data.toList := by
  rw [ByteArray.data_append, Array.toList_append]

/-- The bytes of `toString x` for an `Int32`. -/
theorem bytes_toString_int32 (x : Int32) :
    (toString x).toByteArray.data.toList =
      (if x.toInt < 0 then [45] else []) ++ natDigitBytes x.toInt.natAbs := by
  show (toString x.toInt).toByteArray.data.toList = _
  rw [Int.toString_eq_repr, Int.repr_eq_ite]
  split
  · rename_i h
    simp only [show ¬ (x.toInt < 0) by omega, ite_false, List.nil_append, bytes_natRepr]
    congr 1; omega
  · rename_i h
    simp only [show x.toInt < 0 by omega, ite_true, String.toByteArray_append, byteArray_append_toList,
      bytes_natRepr]
    have hm : (-x.toInt).toNat = x.toInt.natAbs := by omega
    rw [hm]
    rfl

theorem isDigitByte_iff (y : UInt8) : isDigitByte y = true ↔ 48 ≤ y.toNat ∧ y.toNat ≤ 57 := by
  simp only [isDigitByte, Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le]
  rfl

theorem takeWhile_digits_append (ds rest : List UInt8) (hds : ∀ y ∈ ds, isDigitByte y = true)
    (hrest : ∀ y, rest.head? = some y → isDigitByte y = false) :
    (ds ++ rest).takeWhile isDigitByte = ds := by
  rw [List.takeWhile_append_of_pos hds]
  cases rest with
  | nil => simp
  | cons y ys =>
    have : ¬ isDigitByte y = true := by simp [hrest y rfl]
    simp [List.takeWhile_cons_of_neg this]

theorem natDigitBytes_digits (n : Nat) : ∀ y ∈ natDigitBytes n, isDigitByte y = true :=
  fun y hy => (isDigitByte_iff y).mpr ((natDigitBytes_spec n).1 y hy)

/-- Parsing the bytes of `toString x`, followed by anything that doesn't start with a digit, gives back `x`. -/
theorem parseInt32Spec_toString (x : Int32) (rest : List UInt8)
    (hrest : ∀ y, rest.head? = some y → isDigitByte y = false) :
    parseInt32Spec ((toString x).toByteArray.data.toList ++ rest) =
      some (x, (toString x).toByteArray.data.toList.length) := by
  have hrange := Int32.le_toInt x
  have hrange2 := Int32.toInt_lt x
  obtain ⟨hd, hv, hne⟩ := natDigitBytes_spec x.toInt.natAbs
  have htw := takeWhile_digits_append _ rest (natDigitBytes_digits x.toInt.natAbs) hrest
  rw [bytes_toString_int32]
  unfold parseInt32Spec
  by_cases hneg : x.toInt < 0
  · simp only [hneg, ite_true, List.cons_append, List.nil_append, List.head?_cons, List.tail_cons, htw,
      hne, false_or, List.length_cons]
    have hval : digitsValue (natDigitBytes x.toInt.natAbs) = x.toInt.natAbs := hv
    rw [hval]
    have hle : ¬ 2 ^ 31 < x.toInt.natAbs := by
      have : x.toInt.natAbs ≤ 2147483648 := by omega
      omega
    simp only [hle, ite_false, Option.some.injEq, Prod.mk.injEq, and_true]
    apply Int32.toInt_inj.mp
    rw [Int32.toInt_ofInt, Int.bmod_eq_of_le (by simp [Int32.size]; omega) (by simp [Int32.size]; omega)]
    omega
  · simp only [hneg, ite_false, List.nil_append]
    obtain ⟨y, ys, hy⟩ : ∃ y ys, natDigitBytes x.toInt.natAbs = y :: ys := by
      cases h : natDigitBytes x.toInt.natAbs with
      | nil => exact absurd h hne
      | cons y ys => exact ⟨y, ys, rfl⟩
    have hy45 : y ≠ 45 := by
      have := hd y (by rw [hy]; simp)
      intro h; subst h; simp at this
    have hhead : (natDigitBytes x.toInt.natAbs ++ rest).head? ≠ some 45 := by
      rw [hy]; simp [hy45]
    simp only [hhead, ite_false, htw, hne, false_or]
    have hval : digitsValue (natDigitBytes x.toInt.natAbs) = x.toInt.natAbs := hv
    rw [hval]
    have hle : ¬ 2 ^ 31 ≤ x.toInt.natAbs := by omega
    simp only [hle, ite_false, Option.some.injEq, Prod.mk.injEq, and_true]
    apply Int32.toInt_inj.mp
    rw [Int32.toInt_ofNat_of_lt (by omega)]
    omega

/-! ## Spaces -/

theorem skipSpaces_spec (b : ByteArray) (hb : b.size < 2 ^ 32) :
    ∀ (n : Nat) (p : UInt32), b.size - p.toNat = n → p.toNat ≤ b.size →
      (skipSpaces b p b.size.toUInt32).toNat = p.toNat + ((bytesFrom b p.toNat).takeWhile isSpaceByte).length := by
  intro n
  induction n with
  | zero =>
    intro p hn hp
    have hge : b.size ≤ p.toNat := by omega
    have hnot : ¬ p < b.size.toUInt32 := by rw [u32_lt_size_iff hb]; omega
    rw [skipSpaces]
    simp [hnot, bytesFrom_of_ge hge]
  | succ n ih =>
    intro p hn hp
    have hlt : p.toNat < b.size := by omega
    have hsucc := u32_toNat_succ hlt hb
    have hyes : p < b.size.toUInt32 := by rw [u32_lt_size_iff hb]; omega
    rw [skipSpaces]
    simp only [hyes, ↓reduceDIte, bytesFrom_of_lt hlt, byteArray_get!_eq hlt]
    by_cases hs : isSpaceByte b[p.toNat] = true
    · simp only [hs, ite_true, List.takeWhile_cons_of_pos hs, List.length_cons]
      rw [ih (p + 1) (by omega) (by omega), hsucc]
      omega
    · simp [hs, List.takeWhile_cons_of_neg hs]

/-- `skipSpaces` when the bytes at `p` don't start with a space. -/
theorem skipSpaces_of_not_space (b : ByteArray) (hb : b.size < 2 ^ 32) (p : UInt32) (hp : p.toNat ≤ b.size)
    (hns : ∀ y, (bytesFrom b p.toNat).head? = some y → isSpaceByte y = false) :
    skipSpaces b p b.size.toUInt32 = p := by
  apply UInt32.toNat_inj.mp
  rw [skipSpaces_spec b hb _ p rfl hp]
  cases h : bytesFrom b p.toNat with
  | nil => simp
  | cons y ys =>
    have : ¬ isSpaceByte y = true := by simp [hns y (by simp [h])]
    simp [List.takeWhile_cons_of_neg this]

theorem bytesFrom_eq_drop (b : ByteArray) (p : Nat) : bytesFrom b p = b.data.toList.drop p := rfl

theorem byteArray_size_eq_length (b : ByteArray) : b.size = b.data.toList.length := by
  rw [Array.length_toList]; rfl

theorem natDigitBytes_length_le (n : Nat) (h : n < 10 ^ 10) : (natDigitBytes n).length ≤ 10 := by
  unfold natDigitBytes
  rw [List.length_map]
  exact (Nat.length_toDigits_le_iff (by omega) (by omega)).mpr h

theorem bytes_toString_int32_length (x : Int32) : (toString x).toByteArray.data.toList.length ≤ 11 := by
  rw [bytes_toString_int32]
  have := Int32.le_toInt x
  have := Int32.toInt_lt x
  have h := natDigitBytes_length_le x.toInt.natAbs (by omega)
  split <;> simp <;> omega

theorem bytes_toString_int32_head (x : Int32) :
    ∀ y, (toString x).toByteArray.data.toList.head? = some y → isSpaceByte y = false ∧ (y = 45 ∨ isDigitByte y) := by
  intro y hy
  rw [bytes_toString_int32] at hy
  obtain ⟨hd, -, hne⟩ := natDigitBytes_spec x.toInt.natAbs
  split at hy
  · simp at hy; subst hy; decide
  · simp only [List.nil_append] at hy
    cases h : natDigitBytes x.toInt.natAbs with
    | nil => exact absurd h hne
    | cons z zs =>
      rw [h] at hy
      simp only [List.head?_cons, Option.some.injEq] at hy
      subst hy
      have := hd z (by rw [h]; simp)
      refine ⟨?_, Or.inr ((isDigitByte_iff z).mpr this)⟩
      have h1 : z ≠ 32 := by intro hz; subst hz; simp at this
      have h2 : z ≠ 9 := by intro hz; subst hz; simp at this
      have h3 : z ≠ 13 := by intro hz; subst hz; simp at this
      simp [isSpaceByte, h1, h2, h3]

/-! ## Grids -/

/-- The row-major index of a cell in the `w` by `h` box at (`minX`, `minY`), if it is inside. -/
def gridIndex (minX minY : Int32) (w h : UInt32) (c : Int32 × Int32) : Option Nat :=
  if (c.1 - minX).toUInt32 < w ∧ (c.2 - minY).toUInt32 < h then
    some ((c.2 - minY).toUInt32.toNat * w.toNat + (c.1 - minX).toUInt32.toNat)
  else none

/-- A grid index decomposes uniquely into a row and a column. -/
theorem gridIndex_eq_iff {minX minY : Int32} {w h : UInt32} {c : Int32 × Int32} {r col : Nat} (hcol : col < w.toNat) :
    gridIndex minX minY w h c = some (r * w.toNat + col) ↔
      (c.1 - minX).toUInt32 < w ∧ (c.2 - minY).toUInt32 < h ∧
        (c.2 - minY).toUInt32.toNat = r ∧ (c.1 - minX).toUInt32.toNat = col := by
  unfold gridIndex
  constructor
  · intro hk
    split at hk
    · rename_i hin
      simp only [Option.some.injEq] at hk
      have hx := UInt32.lt_iff_toNat_lt.mp hin.1
      have h1 : ((c.2 - minY).toUInt32.toNat * w.toNat + (c.1 - minX).toUInt32.toNat) / w.toNat =
          (c.2 - minY).toUInt32.toNat := by
        rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hx, Nat.add_zero]
      have h2 : ((c.2 - minY).toUInt32.toNat * w.toNat + (c.1 - minX).toUInt32.toNat) % w.toNat =
          (c.1 - minX).toUInt32.toNat := by
        rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hx]
      have h3 : (r * w.toNat + col) / w.toNat = r := by
        rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hcol, Nat.add_zero]
      have h4 : (r * w.toNat + col) % w.toNat = col := by
        rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hcol]
      rw [hk] at h1 h2
      exact ⟨hin.1, hin.2, h1.symm.trans h3, h2.symm.trans h4⟩
    · simp at hk
  · rintro ⟨hx, hy, rfl, rfl⟩
    rw [ite_eq_left ⟨hx, hy⟩]

theorem gridIndex_lt {minX minY : Int32} {w h : UInt32} {c : Int32 × Int32} {k : Nat}
    (hk : gridIndex minX minY w h c = some k) : k < w.toNat * h.toNat := by
  unfold gridIndex at hk
  split at hk
  · rename_i hin
    simp only [Option.some.injEq] at hk
    subst hk
    have h1 := UInt32.lt_iff_toNat_lt.mp hin.1
    have h2 := UInt32.lt_iff_toNat_lt.mp hin.2
    have : ((c.2 - minY).toUInt32.toNat + 1) * w.toNat ≤ h.toNat * w.toNat := Nat.mul_le_mul_right _ h2
    rw [Nat.mul_comm w.toNat]
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  · simp at hk

open Classical in
theorem fillGrid_spec (cells : Array UInt64) (minX minY : Int32) (w h : UInt32) (alive : UInt8)
    (ha : alive < 128) (hwh : w.toNat * h.toNat < 2 ^ 32) (hc : cells.size < 2 ^ 32) :
    ∀ (n : Nat) (i : UInt32) (g : AsciiBytes), cells.size - i.toNat = n → i.toNat ≤ cells.size →
      g.1.size = w.toNat * h.toNat →
      (fillGrid cells minX minY w h alive ha i cells.size.toUInt32 g).1.size = g.1.size ∧
      ∀ (k : Nat) (hk : k < g.1.size),
        (fillGrid cells minX minY w h alive ha i cells.size.toUInt32 g).1[k]! =
          if ∃ j, i.toNat ≤ j ∧ ∃ (hj : j < cells.size),
              gridIndex minX minY w h ((cellKeyX cells[j]).toInt32, (cellKeyY cells[j]).toInt32) = some k then alive
          else g.1[k] := by
  intro n
  induction n with
  | zero =>
    intro i g hn hi hg
    have hnot : ¬ i < cells.size.toUInt32 := by rw [u32_lt_size_iff hc]; omega
    rw [fillGrid]
    simp only [hnot, ↓reduceDIte, true_and]
    intro k hk
    rw [getElem!_pos g.1 k hk]
    have : ¬ ∃ j, i.toNat ≤ j ∧ ∃ (hj : j < cells.size),
        gridIndex minX minY w h ((cellKeyX cells[j]).toInt32, (cellKeyY cells[j]).toInt32) = some k := by
      rintro ⟨j, hj1, hj2, -⟩; omega
    simp [this]
  | succ n ih =>
    intro i g hn hi hg
    have hlt : i.toNat < cells.size := by omega
    have hyes : i < cells.size.toUInt32 := by rw [u32_lt_size_iff hc]; exact hlt
    have hsucc := u32_toNat_succ hlt hc
    rw [fillGrid]
    simp only [hyes, ↓reduceDIte, getElem!_pos cells i.toNat hlt]
    generalize hc' : cells[i.toNat] = cb
    generalize hx : (cellKeyX cb).toInt32 = x
    generalize hy : (cellKeyY cb).toInt32 = y
    -- The grid after this cell.
    generalize hg' : (if (x - minX).toUInt32 < w && (y - minY).toUInt32 < h then
      g.set ((y - minY).toUInt32 * w + (x - minX).toUInt32) alive ha else g) = g'
    have hg'size : g'.1.size = g.1.size := by
      rw [← hg']; split <;> simp [AsciiBytes.set]
    have hg'get : ∀ (k : Nat) (hk : k < g.1.size), g'.1[k]! =
        if gridIndex minX minY w h (x, y) = some k then alive else g.1[k] := by
      intro k hk
      rw [← hg']
      unfold gridIndex
      by_cases hin : (x - minX).toUInt32 < w ∧ (y - minY).toUInt32 < h
      · have hin' : ((x - minX).toUInt32 < w && (y - minY).toUInt32 < h) = true := by
          rw [Bool.and_eq_true]; exact ⟨decide_eq_true hin.1, decide_eq_true hin.2⟩
        rw [ite_eq_left hin', ite_eq_left hin]
        have h1 := UInt32.lt_iff_toNat_lt.mp hin.1
        have h2 := UInt32.lt_iff_toNat_lt.mp hin.2
        have hidx : ((y - minY).toUInt32 * w + (x - minX).toUInt32).toNat =
            (y - minY).toUInt32.toNat * w.toNat + (x - minX).toUInt32.toNat := by
          have : ((y - minY).toUInt32.toNat + 1) * w.toNat ≤ h.toNat * w.toNat := Nat.mul_le_mul_right _ h2
          rw [Nat.add_mul, Nat.one_mul] at this
          have hwh' : h.toNat * w.toNat < 2 ^ 32 := by rw [Nat.mul_comm]; exact hwh
          rw [UInt32.toNat_add, UInt32.toNat_mul]
          rw [Nat.mod_eq_of_lt (a := (y - minY).toUInt32.toNat * w.toNat) (by omega)]
          rw [Nat.mod_eq_of_lt (by omega)]
        simp only [AsciiBytes.set, hidx, Option.some.injEq]
        by_cases hkk : (y - minY).toUInt32.toNat * w.toNat + (x - minX).toUInt32.toNat = k
        · subst hkk
          rw [ByteArray.getElem!_set!_self _ _ _ hk, ite_eq_left rfl]
        · rw [ByteArray.getElem!_set!_ne _ _ _ _ hkk, getElem!_pos g.1 k hk, ite_eq_right hkk]
      · have hin' : ((x - minX).toUInt32 < w && (y - minY).toUInt32 < h) = false := by
          simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
          by_cases hx : (x - minX).toUInt32 < w
          · exact Or.inr (fun hy => hin ⟨hx, hy⟩)
          · exact Or.inl hx
        rw [ite_eq_right (by rw [hin']; exact Bool.false_ne_true), ite_eq_right hin, getElem!_pos g.1 k hk]
        simp
    obtain ⟨ihs, ihg⟩ := ih (i + 1) g' (by omega) (by omega) (by rw [hg'size, hg])
    refine ⟨by rw [ihs, hg'size], fun k hk => ?_⟩
    rw [ihg k (by rw [hg'size]; exact hk), hsucc]
    have hk' : k < g'.1.size := by rw [hg'size]; exact hk
    by_cases hlater : ∃ j, i.toNat + 1 ≤ j ∧ ∃ (hj : j < cells.size),
        gridIndex minX minY w h ((cellKeyX cells[j]).toInt32, (cellKeyY cells[j]).toInt32) = some k
    · have : ∃ j, i.toNat ≤ j ∧ ∃ (hj : j < cells.size),
          gridIndex minX minY w h ((cellKeyX cells[j]).toInt32, (cellKeyY cells[j]).toInt32) = some k := by
        obtain ⟨j, hj1, hj2⟩ := hlater; exact ⟨j, by omega, hj2⟩
      simp [hlater, this]
    · simp only [hlater, ite_false]
      have hgk : g'.1[k] = g'.1[k]! := (getElem!_pos g'.1 k hk').symm
      rw [hgk, hg'get k hk]
      by_cases hthis : gridIndex minX minY w h (x, y) = some k
      · have : ∃ j, i.toNat ≤ j ∧ ∃ (hj : j < cells.size),
            gridIndex minX minY w h ((cellKeyX cells[j]).toInt32, (cellKeyY cells[j]).toInt32) = some k :=
          ⟨i.toNat, Nat.le_refl _, hlt, by rw [hc']; simp only [hx, hy]; exact hthis⟩
        simp [hthis, this]
      · have : ¬ ∃ j, i.toNat ≤ j ∧ ∃ (hj : j < cells.size),
            gridIndex minX minY w h ((cellKeyX cells[j]).toInt32, (cellKeyY cells[j]).toInt32) = some k := by
          rintro ⟨j, hj1, hj2, hj3⟩
          by_cases hji : j = i.toNat
          · subst hji; rw [hc'] at hj3; simp only [hx, hy] at hj3; exact hthis hj3
          · exact hlater ⟨j, by omega, hj2, hj3⟩
        simp [hthis, this]

theorem gridRows_spec (g : AsciiBytes) (w h : UInt32) (hh : h.toNat < 2 ^ 31) :
    ∀ (n : Nat) (r : UInt32) (acc : GrowBuf String) (a : Array String), h.toNat - r.toNat = n →
      r.toNat ≤ h.toNat → acc.Rep a → a.size + (h.toNat - r.toNat) < 2 ^ 31 →
      (gridRows g w h r acc).Rep
        (a ++ ((List.range' r.toNat (h.toNat - r.toNat)).map
          (fun k => g.toStringRange (k.toUInt32 * w) (k.toUInt32 * w + w))).toArray) := by
  intro n
  induction n with
  | zero =>
    intro r acc a hn hr hrep ha
    have hnot : ¬ r < h := by rw [UInt32.lt_iff_toNat_lt]; omega
    rw [gridRows]
    simp only [hnot, ↓reduceDIte, hn, List.range'_zero, List.map_nil]
    simpa using hrep
  | succ n ih =>
    intro r acc a hn hr hrep ha
    have hlt : r < h := by rw [UInt32.lt_iff_toNat_lt]; omega
    have hsucc : (r + 1).toNat = r.toNat + 1 := by rw [UInt32.toNat_add]; simp; omega
    rw [gridRows]
    simp only [hlt, ↓reduceDIte]
    have := ih (r + 1) _ _ (by omega) (by omega)
      (GrowBuf.rep_push hrep (g.toStringRange (r * w) (r * w + w)) (by omega)) (by simp; omega)
    rw [hsucc] at this
    rw [show h.toNat - r.toNat = (h.toNat - (r.toNat + 1)) + 1 by omega, List.range'_succ, List.map_cons]
    have hr' : r.toNat.toUInt32 = r := by apply UInt32.toNat_inj.mp; rw [u32_size_toNat (by omega)]
    simpa [hr', Array.append_assoc] using this

/-! ## Bounding boxes -/

theorem int32_toUInt32_toNat_of_nonneg (x : Int32) (hx : 0 ≤ x.toInt) : (x.toUInt32.toNat : Int) = x.toInt := by
  have h0 : (0 : Int32) ≤ x := by rw [Int32.le_iff_toInt_le]; simpa using hx
  rw [Int32.toNat_toUInt32_of_le h0, Int32.toInt_eq_toNatClampNeg h0]

theorem int32_sub_toInt (a b : Int32) (h1 : -2 ^ 31 ≤ a.toInt - b.toInt) (h2 : a.toInt - b.toInt < 2 ^ 31) :
    (a - b).toInt = a.toInt - b.toInt := by
  rw [Int32.toInt_sub, Int.bmod_eq_of_le (by omega) (by omega)]

theorem int32_sub_add_one_toInt (a b : Int32) (h1 : 0 ≤ a.toInt - b.toInt) (h2 : a.toInt - b.toInt + 1 < 2 ^ 31) :
    (a - b + 1).toInt = a.toInt - b.toInt + 1 := by
  rw [Int32.toInt_add, int32_sub_toInt a b (by omega) (by omega), Int32.toInt_one,
    Int.bmod_eq_of_le (by omega) (by omega)]

/-- The width of the box from `lo` to `hi`. -/
theorem boxSize_toNat (lo hi : Int32) (h1 : lo.toInt ≤ hi.toInt) (h2 : hi.toInt - lo.toInt + 1 < 2 ^ 31) :
    ((hi - lo + 1).toUInt32.toNat : Int) = hi.toInt - lo.toInt + 1 := by
  rw [int32_toUInt32_toNat_of_nonneg _ (by rw [int32_sub_add_one_toInt hi lo (by omega) h2]; omega),
    int32_sub_add_one_toInt hi lo (by omega) h2]

/-- The offset of `x` in the box from `lo` to `hi`. -/
theorem boxOffset_toNat (lo hi x : Int32) (h1 : lo.toInt ≤ x.toInt) (h2 : x.toInt ≤ hi.toInt)
    (h3 : hi.toInt - lo.toInt + 1 < 2 ^ 31) :
    ((x - lo).toUInt32.toNat : Int) = x.toInt - lo.toInt := by
  rw [int32_toUInt32_toNat_of_nonneg _ (by rw [int32_sub_toInt x lo (by omega) (by omega)]; omega),
    int32_sub_toInt x lo (by omega) (by omega)]

/-- A cell inside the box has a grid index. -/
theorem gridIndex_isSome_of_mem_box (minX maxX minY maxY : Int32) (c : Int32 × Int32)
    (hx1 : minX.toInt ≤ c.1.toInt) (hx2 : c.1.toInt ≤ maxX.toInt) (hy1 : minY.toInt ≤ c.2.toInt)
    (hy2 : c.2.toInt ≤ maxY.toInt) (hw : maxX.toInt - minX.toInt + 1 < 2 ^ 31)
    (hh : maxY.toInt - minY.toInt + 1 < 2 ^ 31) :
    (gridIndex minX minY (maxX - minX + 1).toUInt32 (maxY - minY + 1).toUInt32 c).isSome := by
  have hW := boxSize_toNat minX maxX (by omega) hw
  have hH := boxSize_toNat minY maxY (by omega) hh
  have hdx := boxOffset_toNat minX maxX c.1 hx1 hx2 hw
  have hdy := boxOffset_toNat minY maxY c.2 hy1 hy2 hh
  unfold gridIndex
  rw [ite_eq_left ⟨UInt32.lt_iff_toNat_lt.mpr (by omega), UInt32.lt_iff_toNat_lt.mpr (by omega)⟩]
  rfl

/-! ## Digit sets -/

/-- The digit set of `ds` as a bit mask, as `scanDigitSet` accumulates it. -/
def digitMaskStep (m : UInt32) (d : UInt8) : UInt32 := m ||| ((1 : UInt32) <<< (d.toUInt32 - 48))

theorem getLsbD_digitMaskStep (m : UInt32) (d : UInt8) (hd : isDigitByte d = true) (k : Nat) (hk : k < 32) :
    (digitMaskStep m d).toBitVec.getLsbD k = (m.toBitVec.getLsbD k || decide (d.toNat - 48 = k)) := by
  obtain ⟨h1, h2⟩ := (isDigitByte_iff d).mp hd
  have hs : (d.toUInt32 - 48).toNat = d.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]; simp
  unfold digitMaskStep
  simp only [UInt32.toBitVec_or, BitVec.getLsbD_or, UInt32.toBitVec_shiftLeft]
  congr 1
  rw [BitVec.shiftLeft_eq', BitVec.getLsbD_shiftLeft]
  generalize hN : ((d.toUInt32 - 48).toBitVec % 32).toNat = N
  have hn : N = d.toNat - 48 := by
    rw [← hN, BitVec.toNat_umod]
    have : (d.toUInt32 - 48).toBitVec.toNat = (d.toUInt32 - 48).toNat := rfl
    rw [this, hs]; simp; omega
  subst hn
  simp only [UInt32.toBitVec_one, BitVec.getLsbD_one]
  by_cases hkd : d.toNat - 48 = k
  · subst hkd; simp; omega
  · simp only [hkd, decide_false]
    by_cases hlt : k < d.toNat - 48
    · simp [hlt]
    · have : k - (d.toNat - 48) ≠ 0 := by omega
      simp [this]

theorem getLsbD_foldl_digitMaskStep (ds : List UInt8) (hds : ∀ d ∈ ds, isDigitByte d = true) :
    ∀ (m : UInt32) (k : Nat), k < 32 →
      (ds.foldl digitMaskStep m).toBitVec.getLsbD k = (m.toBitVec.getLsbD k || ds.any (fun d => d.toNat - 48 = k)) := by
  induction ds with
  | nil => intro m k _; simp
  | cons d ds ih =>
    intro m k hk
    rw [List.foldl_cons, ih (fun d' hd' => hds d' (by simp [hd'])) _ k hk,
      getLsbD_digitMaskStep m d (hds d (by simp)) k hk, List.any_cons]
    cases m.toBitVec.getLsbD k <;> cases decide (d.toNat - 48 = k) <;> simp

theorem digitMask_eq_iff (ds : List UInt8) (hds : ∀ d ∈ ds, isDigitByte d = true) (target : UInt32) :
    ds.foldl digitMaskStep 0 = target ↔
      ∀ k, k < 32 → ds.any (fun d => d.toNat - 48 = k) = target.toBitVec.getLsbD k := by
  constructor
  · intro h k hk
    rw [← h, getLsbD_foldl_digitMaskStep ds hds 0 k hk]
    simp
  · intro h
    apply UInt32.toBitVec_inj.mp
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    rw [getLsbD_foldl_digitMaskStep ds hds 0 k hk, ← h k hk]
    simp

theorem any_digit_iff (ds : List UInt8) (k : Nat) :
    ds.any (fun d => d.toNat - 48 = k) = true ↔ ∃ d ∈ ds, d.toNat - 48 = k := by
  simp

theorem bits_survival23 : ∀ k, k < 32 → survival23Mask.toBitVec.getLsbD k = (k = 2 || k = 3) := by
  decide

theorem bits_birth3 : ∀ k, k < 32 → birth3Mask.toBitVec.getLsbD k = decide (k = 3) := by
  decide

/-- A digit mask is the survival mask of Conway's rules exactly when the digits are 2s and 3s with both. -/
theorem digitMask_eq_survival23 (ds : List UInt8) (hds : ∀ d ∈ ds, isDigitByte d = true) :
    ds.foldl digitMaskStep 0 = survival23Mask ↔ (∀ d ∈ ds, d = 50 ∨ d = 51) ∧ 50 ∈ ds ∧ 51 ∈ ds := by
  rw [digitMask_eq_iff ds hds]
  have hd10 : ∀ d ∈ ds, d.toNat - 48 < 10 := fun d hd => by
    have := (isDigitByte_iff d).mp (hds d hd); omega
  have hval : ∀ d ∈ ds, 48 ≤ d.toNat := fun d hd => ((isDigitByte_iff d).mp (hds d hd)).1
  constructor
  · intro h
    have hk : ∀ k, k < 32 → ((∃ d ∈ ds, d.toNat - 48 = k) ↔ (k = 2 ∨ k = 3)) := by
      intro k hk
      have := h k hk
      rw [bits_survival23 k hk] at this
      rw [← any_digit_iff, this]
      simp
    refine ⟨fun d hd => ?_, ?_, ?_⟩
    · have := (hk (d.toNat - 48) (by have := hd10 d hd; omega)).mp ⟨d, hd, rfl⟩
      have h48 := hval d hd
      rcases this with h | h
      · left; apply UInt8.toNat_inj.mp; simp; omega
      · right; apply UInt8.toNat_inj.mp; simp; omega
    · obtain ⟨d, hd, hk2⟩ := (hk 2 (by omega)).mpr (Or.inl rfl)
      have : d = 50 := by apply UInt8.toNat_inj.mp; have := hval d hd; simp; omega
      exact this ▸ hd
    · obtain ⟨d, hd, hk3⟩ := (hk 3 (by omega)).mpr (Or.inr rfl)
      have : d = 51 := by apply UInt8.toNat_inj.mp; have := hval d hd; simp; omega
      exact this ▸ hd
  · rintro ⟨hall, h50, h51⟩ k hk
    rw [bits_survival23 k hk]
    by_cases h23 : k = 2 ∨ k = 3
    · have : ds.any (fun d => d.toNat - 48 = k) = true := by
        rw [any_digit_iff]
        rcases h23 with rfl | rfl
        · exact ⟨50, h50, by decide⟩
        · exact ⟨51, h51, by decide⟩
      rw [this]; rcases h23 with rfl | rfl <;> rfl
    · have : ds.any (fun d => d.toNat - 48 = k) = false := by
        apply Bool.eq_false_iff.mpr
        rw [ne_eq, any_digit_iff]
        rintro ⟨d, hd, hdk⟩
        rcases hall d hd with rfl | rfl <;> simp at hdk <;> omega
      rw [this]
      have h2 : k ≠ 2 := fun h => h23 (Or.inl h)
      have h3 : k ≠ 3 := fun h => h23 (Or.inr h)
      simp [h2, h3]

/-- A digit mask is the birth mask of Conway's rules exactly when the digits are all 3s, and there are some. -/
theorem digitMask_eq_birth3 (ds : List UInt8) (hds : ∀ d ∈ ds, isDigitByte d = true) :
    ds.foldl digitMaskStep 0 = birth3Mask ↔ (∀ d ∈ ds, d = 51) ∧ 51 ∈ ds := by
  rw [digitMask_eq_iff ds hds]
  have hd10 : ∀ d ∈ ds, d.toNat - 48 < 10 := fun d hd => by
    have := (isDigitByte_iff d).mp (hds d hd); omega
  have hval : ∀ d ∈ ds, 48 ≤ d.toNat := fun d hd => ((isDigitByte_iff d).mp (hds d hd)).1
  constructor
  · intro h
    have hk : ∀ k, k < 32 → ((∃ d ∈ ds, d.toNat - 48 = k) ↔ k = 3) := by
      intro k hk
      have := h k hk
      rw [bits_birth3 k hk] at this
      rw [← any_digit_iff, this]
      simp
    refine ⟨fun d hd => ?_, ?_⟩
    · have := (hk (d.toNat - 48) (by have := hd10 d hd; omega)).mp ⟨d, hd, rfl⟩
      apply UInt8.toNat_inj.mp; have := hval d hd; simp; omega
    · obtain ⟨d, hd, hk3⟩ := (hk 3 (by omega)).mpr rfl
      have : d = 51 := by apply UInt8.toNat_inj.mp; have := hval d hd; simp; omega
      exact this ▸ hd
  · rintro ⟨hall, h51⟩ k hk
    rw [bits_birth3 k hk]
    by_cases h3 : k = 3
    · subst h3
      have : ds.any (fun d => d.toNat - 48 = 3) = true := by rw [any_digit_iff]; exact ⟨51, h51, by decide⟩
      rw [this]; rfl
    · have : ds.any (fun d => d.toNat - 48 = k) = false := by
        apply Bool.eq_false_iff.mpr
        rw [ne_eq, any_digit_iff]
        rintro ⟨d, hd, hdk⟩
        rw [hall d hd] at hdk; simp at hdk; omega
      rw [this]; simp [h3]

theorem scanDigitSet_spec (b : ByteArray) (hb : b.size < 2 ^ 32) :
    ∀ (n : Nat) (p : UInt32) (m : UInt32), b.size - p.toNat = n → p.toNat ≤ b.size →
      (scanDigitSet b b.size.toUInt32 p m).1.toNat =
          p.toNat + ((bytesFrom b p.toNat).takeWhile isDigitByte).length ∧
      (scanDigitSet b b.size.toUInt32 p m).2 =
          ((bytesFrom b p.toNat).takeWhile isDigitByte).foldl digitMaskStep m := by
  intro n
  induction n with
  | zero =>
    intro p m hn hp
    have hge : b.size ≤ p.toNat := by omega
    have hnot : ¬ p < b.size.toUInt32 := by rw [u32_lt_size_iff hb]; omega
    rw [scanDigitSet]
    simp [hnot, bytesFrom_of_ge hge]
  | succ n ih =>
    intro p m hn hp
    have hlt : p.toNat < b.size := by omega
    have hsucc := u32_toNat_succ hlt hb
    have hyes : p < b.size.toUInt32 := by rw [u32_lt_size_iff hb]; omega
    rw [scanDigitSet]
    simp only [hyes, ↓reduceDIte, bytesFrom_of_lt hlt, byteArray_get!_eq hlt]
    by_cases hd : isDigitByte b[p.toNat] = true
    · simp only [hd, ite_true, List.takeWhile_cons_of_pos hd, List.length_cons, List.foldl_cons]
      have := ih (p + 1) (m ||| ((1 : UInt32) <<< (b[p.toNat].toUInt32 - 48))) (by omega) (by omega)
      rw [hsucc] at this
      rw [this.1, this.2]
      exact ⟨by omega, rfl⟩
    · simp [hd, List.takeWhile_cons_of_neg hd]

/-! ## Byte arrays from lists -/

theorem byteArray_getElem_of_list (L : List UInt8) (k : Nat) (hk : k < L.length) :
    (⟨L.toArray⟩ : ByteArray)[k]'(by show k < L.toArray.size; simpa using hk) = L[k] := by
  show L.toArray[k] = L[k]
  simp

theorem bytesFrom_of_list (L : List UInt8) (k : Nat) : bytesFrom ⟨L.toArray⟩ k = L.drop k := by
  simp [bytesFrom]

theorem size_of_list (L : List UInt8) : (⟨L.toArray⟩ : ByteArray).size = L.length := by
  show L.toArray.size = L.length
  simp

theorem not_digit_47 : isDigitByte 47 = false := by decide

/-- The bytes of a list, read with `get!`. -/
theorem get!_of_list (L : List UInt8) (k : Nat) (hk : k < L.length) : (⟨L.toArray⟩ : ByteArray).get! k = L[k]! := by
  rw [byteArray_get!_eq (by rw [size_of_list]; exact hk), getElem!_pos L k hk]
  exact byteArray_getElem_of_list L k hk

/-- A byte array is the bytes of its list. -/
theorem byteArray_eq_of_toList {b : ByteArray} {L : List UInt8} (h : b.data.toList = L) : b = ⟨L.toArray⟩ := by
  obtain ⟨⟨l⟩⟩ := b
  simp only at h
  subst h
  rfl

/-! ## Filled grids -/

open Classical in
/-- What a grid of `dead` holds after filling the cells with `alive`. -/
theorem fillGrid_replicate_spec (cells : Array UInt64) (minX minY : Int32) (w h : UInt32)
    (alive dead : UInt8) (ha : alive < 128) (hd : dead < 128) (hcs : cells.size < 2 ^ 32)
    (hwh : w.toNat * h.toNat < 2 ^ 32) :
    (fillGrid cells minX minY w h alive ha 0 cells.size.toUInt32 (AsciiBytes.replicate (w * h) dead hd)).1.size =
        w.toNat * h.toNat ∧
      ∀ (k : Nat), k < w.toNat * h.toNat →
        (fillGrid cells minX minY w h alive ha 0 cells.size.toUInt32 (AsciiBytes.replicate (w * h) dead hd)).1[k]! =
          if ∃ c ∈ cells, gridIndex minX minY w h ((cellKeyX c).toInt32, (cellKeyY c).toInt32) = some k then alive else dead := by
  have hsz : (AsciiBytes.replicate (w * h) dead hd).1.size = w.toNat * h.toNat := by
    simp [AsciiBytes.replicate, ByteArray.size, UInt32.toNat_mul, Nat.mod_eq_of_lt hwh]
  have := fillGrid_spec cells minX minY w h alive ha hwh hcs _ 0 _ rfl (by simp) hsz
  refine ⟨by rw [this.1, hsz], fun k hk => ?_⟩
  rw [this.2 k (by rw [hsz]; exact hk)]
  have hinit : (AsciiBytes.replicate (w * h) dead hd).1[k]'(by rw [hsz]; exact hk) = dead := by
    simp [AsciiBytes.replicate, ByteArray.getElem_eq_getElem_data]
  rw [hinit]
  congr 1
  apply propext
  constructor
  · rintro ⟨j, -, hj, hk⟩; exact ⟨cells[j], Array.getElem_mem hj, hk⟩
  · rintro ⟨c, hc, hk⟩
    obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem hc
    exact ⟨j, by simp, hj, hk⟩

/-- The rows of a grid, as `gridRows` writes them after `init`. -/
theorem gridRows_eq (g : AsciiBytes) (w h : UInt32) (hh : h.toNat + 2 < 2 ^ 31) (init : String) :
    (gridRows g w h 0 (GrowBuf.empty.push init)).toArray =
      #[init] ++ ((List.range h.toNat).map (fun k => g.toStringRange (k.toUInt32 * w) (k.toUInt32 * w + w))).toArray := by
  have h1 := GrowBuf.rep_push (GrowBuf.rep_empty (α := String)) init (by decide)
  have := gridRows_spec g w h (by omega) _ 0 _ _ rfl (by simp) h1 (by simp; omega)
  rw [this.2.2.2, UInt32.toNat_zero, Nat.sub_zero, ← List.range_eq_range']
  rfl

/-- Grid row `r` as bytes. -/
theorem toStringRange_row (g : AsciiBytes) (w h : UInt32) (hg : g.1.size = w.toNat * h.toNat)
    (hwh : w.toNat * h.toNat < 2 ^ 32) (r : Nat) (hr : r < h.toNat) :
    (g.toStringRange (r.toUInt32 * w) (r.toUInt32 * w + w)).toByteArray.size = w.toNat ∧
      ∀ c, c < w.toNat → (g.toStringRange (r.toUInt32 * w) (r.toUInt32 * w + w)).toByteArray[c]! =
        g.1[r * w.toNat + c]! := by
  have hle : (r + 1) * w.toNat ≤ h.toNat * w.toNat := Nat.mul_le_mul_right _ (by omega)
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm h.toNat] at hle
  have hh32 := UInt32.toNat_lt h
  have h1 : (r.toUInt32 * w).toNat = r * w.toNat := by
    rw [UInt32.toNat_mul, u32_size_toNat (by omega), Nat.mod_eq_of_lt (by omega)]
  have h2 : (r.toUInt32 * w + w).toNat = r * w.toNat + w.toNat := by
    rw [UInt32.toNat_add, h1, Nat.mod_eq_of_lt (by omega)]
  have hb : (g.toStringRange (r.toUInt32 * w) (r.toUInt32 * w + w)).toByteArray =
      g.1.extract (r * w.toNat) (r * w.toNat + w.toNat) := by
    show g.1.extract _ _ = _
    rw [h1, h2]
  rw [hb]
  refine ⟨by rw [ByteArray.size_extract, hg]; omega, fun c hc => ?_⟩
  have hcs : c < (g.1.extract (r * w.toNat) (r * w.toNat + w.toNat)).size := by
    rw [ByteArray.size_extract, hg]; omega
  rw [getElem!_pos _ c hcs, ByteArray.getElem_extract, getElem!_pos g.1 _ (by rw [hg]; omega)]

theorem array_getElem!_of_drop {α : Type} [Inhabited α] (L : Array α) (i k : Nat) (l rest : List α)
    (h : L.toList.drop i = l ++ rest) (hk : k < l.length) : L[i + k]! = l[k]! := by
  have : L.toList[i + k]? = l[k]? := by
    rw [← List.getElem?_drop, h, List.getElem?_append_left hk]
  rw [getElem!_def, getElem!_def]
  simp only [Array.getElem?_toList] at this
  rw [this]

/-- `parseUInt32At` reads back the decimal digits of a `UInt32`. -/
theorem parseUInt32At_digits (b : ByteArray) (hb : b.size < 2 ^ 32) (pos : UInt32) (n : UInt32) (rest : List UInt8)
    (hsplit : bytesFrom b pos.toNat = natDigitBytes n.toNat ++ rest)
    (hrest : ∀ y, rest.head? = some y → isDigitByte y = false) :
    parseUInt32At b pos b.size.toUInt32 = some ⟨n, pos + (natDigitBytes n.toNat).length.toUInt32⟩ := by
  have hlen := congrArg List.length hsplit
  rw [length_bytesFrom, List.length_append] at hlen
  have hp : pos.toNat ≤ b.size := by
    by_cases h : pos.toNat ≤ b.size
    · exact h
    exfalso
    rw [bytesFrom_of_ge (by omega)] at hsplit
    have := (natDigitBytes_spec n.toNat).2.2
    cases hD : natDigitBytes n.toNat with
    | nil => exact this hD
    | cons _ _ => rw [hD] at hsplit; simp at hsplit
  obtain ⟨he, hv1, -⟩ := scanDigits_zero b hb pos hp
  rw [hsplit, takeWhile_digits_append _ _ (natDigitBytes_digits n.toNat) hrest] at he hv1
  obtain ⟨-, hv, hne⟩ := natDigitBytes_spec n.toNat
  have hv' : (scanDigits b b.size.toUInt32 pos 0).2.toNat = n.toNat := by
    rw [hv1 (by unfold digitsValue at hv; rw [hv]; have := UInt32.toNat_lt n; omega), hv]
  unfold parseUInt32At
  have hDlen : 0 < (natDigitBytes n.toNat).length := List.length_pos_iff.mpr hne
  have hne' : ¬ ((scanDigits b b.size.toUInt32 pos 0).1 == pos) = true := by
    intro h; have := congrArg UInt32.toNat (beq_iff_eq.mp h); omega
  have hle : (scanDigits b b.size.toUInt32 pos 0).2 ≤ 4294967295 := by
    rw [UInt64.le_iff_toNat_le, hv']; have := UInt32.toNat_lt n; simp; omega
  simp only [hne', Bool.false_eq_true, ite_false, hle, ite_true, Option.some.injEq]
  congr 1
  · apply UInt32.toNat_inj.mp; rw [UInt64.toNat_toUInt32, hv']; have := UInt32.toNat_lt n; omega
  · apply UInt32.toNat_inj.mp; rw [he, UInt32.toNat_add, u32_size_toNat (by omega)]; omega

theorem isDigitByte_not_space {y : UInt8} (h : isDigitByte y = true) : isSpaceByte y = false := by
  have := (isDigitByte_iff y).mp h
  have h1 : y ≠ 32 := by intro h; subst h; simp at this
  have h2 : y ≠ 9 := by intro h; subst h; simp at this
  have h3 : y ≠ 13 := by intro h; subst h; simp at this
  simp [isSpaceByte, h1, h2, h3]

/-- The position after the digits of a list, as `scanDigitSet` reads them. -/
theorem skipSpaces_list (L : List UInt8) (hL : L.length < 2 ^ 32) (p : UInt32) (v m : Nat) (hp : p.toNat = v)
    (hv : v ≤ L.length) (rest : List UInt8) (hsplit : L.drop v = List.replicate m 32 ++ rest)
    (hrest : ∀ y, rest.head? = some y → isSpaceByte y = false) :
    skipSpaces ⟨L.toArray⟩ p (⟨L.toArray⟩ : ByteArray).size.toUInt32 = (v + m).toUInt32 := by
  have hsz : (⟨L.toArray⟩ : ByteArray).size < 2 ^ 32 := by rw [size_of_list]; exact hL
  have hs := size_of_list L
  have hlen := congrArg List.length hsplit
  simp only [List.length_drop, List.length_append, List.length_replicate] at hlen
  apply UInt32.toNat_inj.mp
  rw [skipSpaces_spec _ hsz _ p rfl (by rw [hp, size_of_list]; omega), hp, bytesFrom_of_list, hsplit,
    u32_size_toNat (by omega)]
  have : (List.replicate m (32 : UInt8) ++ rest).takeWhile isSpaceByte = List.replicate m 32 := by
    rw [List.takeWhile_append_of_pos (by intro a ha; rw [List.eq_of_mem_replicate ha]; decide)]
    cases rest with
    | nil => simp
    | cons y ys =>
      have : ¬ isSpaceByte y = true := by simp [hrest y rfl]
      simp [List.takeWhile_cons_of_neg this]
  rw [this, List.length_replicate]

end Algorithm
