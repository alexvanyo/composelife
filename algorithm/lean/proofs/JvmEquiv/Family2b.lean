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

import JvmBytecode
import proofs.JvmEquiv.Infra
import proofs.JvmEquiv.FlatInfra
import proofs.JvmEquiv.HeapInfra

namespace Algorithm.JvmVerification
open Algorithm.JvmBytecode

/-! ### Family 2b: SerialCore (skipSpaces, decodeCharAt, scanDigits, scanDigitSet, parseUInt32At, parseInt32At) -/

private theorem jvmHeap_set_set {H : Jvm.JvmHeap AlgExt} {a : Nat} {x y : Jvm.HeapObj AlgExt} :
    (H.set a x).set a y = H.set a y := by
  simp only [Jvm.JvmHeap.set]
  split
  · next h =>
    have h1 : a < (H.objects.set a x).size := by simp [Array.size_set, h]
    simp only [h1, ↓reduceDIte, Array.set_set]
  · next h => simp only

private theorem compareUnsigned_slt_zero (a b : UInt32) :
    (if a == b then (0 : UInt32) else if a < b then 4294967295 else 1).toBitVec.slt 0#32 = decide (a < b) := by
  by_cases h1 : a == b
  · have hab : a = b := LawfulBEq.eq_of_beq h1; subst hab; simp
  · by_cases h2 : a < b <;> simp [h1, h2]

private theorem compareUnsigned_sge_zero (a b : UInt32) :
    (0#32).sle (if a == b then (0 : UInt32) else if a < b then 4294967295 else 1).toBitVec = decide (b ≤ a) := by
  by_cases h1 : a == b
  · have hab : a = b := LawfulBEq.eq_of_beq h1; subst hab; simp
  · by_cases h2 : a < b
    · have hn : ¬(b ≤ a) := by
        rw [UInt32.le_iff_toNat_le]; have := UInt32.lt_iff_toNat_lt.mp h2; omega
      simp [h1, h2, hn]
    · have hl : b ≤ a := by
        rw [UInt32.le_iff_toNat_le]; rw [UInt32.lt_iff_toNat_lt] at h2; omega
      simp [h1, h2, hl]

private theorem compareUnsigned64_slt_zero (a b : UInt64) :
    (if a == b then (0 : UInt32) else if a < b then 4294967295 else 1).toBitVec.slt 0#32 = decide (a < b) := by
  by_cases h1 : a == b
  · have hab : a = b := LawfulBEq.eq_of_beq h1; subst hab; simp
  · by_cases h2 : a < b <;> simp [h1, h2]

private theorem compareUnsigned64_sle_zero (a b : UInt64) :
    (if a == b then (0 : UInt32) else if a < b then 4294967295 else 1).toBitVec.sle 0#32 = decide (a ≤ b) := by
  by_cases h1 : a == b
  · have hab : a = b := LawfulBEq.eq_of_beq h1; subst hab; simp
  · by_cases h2 : a < b
    · have hl : a ≤ b := UInt64.le_of_lt h2; simp [h1, h2, hl]
    · have hn : ¬(a ≤ b) := by
        intro hle
        have hab : a = b := UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq (by
          have hle' : a.toBitVec.toNat ≤ b.toBitVec.toNat := UInt64.le_iff_toNat_le.mp hle
          have hlt' : ¬(a.toBitVec.toNat < b.toBitVec.toNat) := fun h => h2 (UInt64.lt_iff_toNat_lt.mpr h)
          exact Nat.le_antisymm hle' (Nat.le_of_not_lt hlt')))
        exact h1 (beq_iff_eq.mpr hab)
      simp [h1, h2, hn]

private theorem u8_signExt_eq_32 (b : UInt8) :
    (UInt32.ofBitVec (BitVec.signExtend 32 b.toBitVec) == 32) = (b == 32) := by revert b; decide

private theorem u8_signExt_eq_9 (b : UInt8) :
    (UInt32.ofBitVec (BitVec.signExtend 32 b.toBitVec) == 9) = (b == 9) := by revert b; decide

private theorem u8_signExt_eq_13 (b : UInt8) :
    (UInt32.ofBitVec (BitVec.signExtend 32 b.toBitVec) == 13) = (b == 13) := by revert b; decide

private theorem u8_signExt_eq_45 (b : UInt8) :
    (UInt32.ofBitVec (BitVec.signExtend 32 b.toBitVec) == 45) = (b == 45) := by revert b; decide

private theorem u8_signExt_and255 (b : UInt8) :
    (UInt32.ofBitVec (BitVec.signExtend 32 b.toBitVec) &&& 255) = b.toUInt32 := by
  revert b; decide

private theorem u8_signExt64_and255 (b : UInt8) :
    (UInt64.ofBitVec (BitVec.signExtend 64 (UInt32.ofBitVec (BitVec.signExtend 32 b.toBitVec)).toBitVec) &&& 255) =
      b.toUInt64 := by
  revert b; decide

private theorem intrinsicsCompare_48_sle (b : UInt8) :
    (if (48 : UInt32) == UInt32.ofBitVec (BitVec.signExtend 32 b.toBitVec) &&& 255 then (0 : UInt32)
     else if (48 : UInt32).toBitVec.slt (UInt32.ofBitVec (BitVec.signExtend 32 b.toBitVec) &&& 255).toBitVec then
       4294967295
     else 1).toBitVec.sle 0#32 = decide (48 ≤ b) := by
  revert b; decide

private theorem intrinsicsCompare_57_sle (b : UInt8) :
    (if UInt32.ofBitVec (BitVec.signExtend 32 b.toBitVec) &&& 255 == 57 then (0 : UInt32)
     else if (UInt32.ofBitVec (BitVec.signExtend 32 b.toBitVec) &&& 255).toBitVec.slt (57 : UInt32).toBitVec then
       4294967295
     else 1).toBitVec.sle 0#32 = decide (b ≤ 57) := by
  revert b; decide

private theorem u8_signExt_and255_sub48 (b : UInt8) :
    (UInt32.ofBitVec (BitVec.signExtend 32 b.toBitVec) &&& 255) - 48 = b.toUInt32 - 48 := by
  revert b; decide

private theorem u8_sub48_and31 {b : UInt8} (h48 : 48 ≤ b) (h57 : b ≤ 57) :
    (b.toUInt32 - 48) &&& 31 = b.toUInt32 - 48 := by
  revert b h48 h57; decide

private theorem getElem_eq_byteArray_getBang (elems : Array UInt8) {k : Nat} (hk : k < elems.size) :
    elems[k] = (⟨elems⟩ : ByteArray).get! k := by
  simp [ByteArray.get!, hk]

/-! ### skipSpaces (+ _1.._2) -/

private theorem skipSpaces_loop : ∀ (m fuel : Nat)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (addr : Nat) (elems : Array UInt8)
    (locs : Nat → JvmVal) (pos limit : UInt32)
    (_ : jh.get? addr = some (.byteArray elems))
    (_ : limit.toNat ≤ elems.size)
    (_ : limit.toNat < 2 ^ 31)
    (_ : limit.toNat - pos.toNat ≤ m)
    (_ : (limit.toNat - pos.toNat) * 45 + 20 ≤ fuel),
    runJvmValFast fuel f_Algorithm_skipSpaces_prog 0 f_Algorithm_skipSpaces_prog
      ⟨0, [], setLocal (setLocal (setLocal locs 0 (.heapRef addr)) 1 (.i32 pos)) 2 (.i32 limit), jh, hp⟩ =
      some (.i32 (Algorithm.skipSpaces ⟨elems⟩ pos limit))
  | 0, fuel, jh, hp, addr, elems, locs, pos, limit, hget, hlim, hlim31, hm, hfuel => by
    have hge : ¬(pos < limit) := by
      intro hlt; have := UInt32.lt_iff_toNat_lt.mp hlt; omega
    have hcu : (if pos == limit then (0 : UInt32) else if pos < limit then 4294967295 else 1).toBitVec.slt 0#32 =
        false := by
      rw [compareUnsigned_slt_zero]; exact decide_eq_false hge
    conv => rhs; rw [Algorithm.skipSpaces]; simp only [hge, ↓reduceDIte]
    split_val_fuel 20; heap_step_blk f_Algorithm_skipSpaces_prog
    rw [hcu]; simp only [Bool.false_eq_true, ↓reduceIte]; rfl
  | m + 1, fuel, jh, hp, addr, elems, locs, pos, limit, hget, hlim, hlim31, hm, hfuel => by
    by_cases hlt : pos < limit
    · have hlt_nat : pos.toNat < limit.toNat := UInt32.lt_iff_toNat_lt.mp hlt
      have hpos_lt : pos.toNat < elems.size := by omega
      have hpos_slt : pos.toBitVec.slt 0#32 = false := u32_slt_zero_of_lt_2_31 (by omega)
      have hpos1_nat : (pos + 1).toNat = pos.toNat + 1 := by
        rw [UInt32.toNat_add, UInt32.toNat_one]; exact Nat.mod_eq_of_lt (by omega)
      have hcu : (if pos == limit then (0 : UInt32) else if pos < limit then 4294967295 else 1).toBitVec.slt 0#32 =
          true := by
        rw [compareUnsigned_slt_zero]; exact decide_eq_true hlt
      have hb_eq : elems[pos.toNat] = (⟨elems⟩ : ByteArray).get! pos.toNat := getElem_eq_byteArray_getBang elems hpos_lt
      conv => rhs; rw [Algorithm.skipSpaces]; simp only [hlt, ↓reduceDIte, ← hb_eq]
      split_val_fuel 45; heap_step_blk f_Algorithm_skipSpaces_prog
      rw [hcu]; simp only [↓reduceIte]
      heap_step_blk f_Algorithm_skipSpaces_prog
      rw [runJvmValFast_baload hget hpos_slt hpos_lt]
      heap_step_blk f_Algorithm_skipSpaces_prog
      rw [u8_signExt_eq_32]
      by_cases h32 : elems[pos.toNat] == 32
      · simp only [h32, Bool.true_or, ↓reduceIte, Algorithm.isSpaceByte]
        heap_step_blk f_Algorithm_skipSpaces_prog
        exact skipSpaces_loop m _ jh hp addr elems _ (pos + 1) limit
          hget hlim hlim31 (by omega) (by simp only [Nat.add_eq]; omega)
      · have h32f : (elems[pos.toNat] == 32) = false := Bool.eq_false_iff.mpr h32
        simp only [h32f, Bool.false_eq_true, ↓reduceIte]
        heap_step_blk f_Algorithm_skipSpaces_prog
        rw [u8_signExt_eq_9]
        by_cases h9 : elems[pos.toNat] == 9
        · simp only [h32f, h9, Bool.false_or, Bool.true_or, ↓reduceIte, Algorithm.isSpaceByte]
          heap_step_blk f_Algorithm_skipSpaces_prog
          exact skipSpaces_loop m _ jh hp addr elems _ (pos + 1) limit
            hget hlim hlim31 (by omega) (by simp only [Nat.add_eq]; omega)
        · have h9f : (elems[pos.toNat] == 9) = false := Bool.eq_false_iff.mpr h9
          simp only [h9f, Bool.false_eq_true, ↓reduceIte]
          heap_step_blk f_Algorithm_skipSpaces_prog
          rw [u8_signExt_eq_13]
          by_cases h13 : elems[pos.toNat] == 13
          · simp only [h32f, h9f, h13, Bool.false_or, ↓reduceIte, Algorithm.isSpaceByte]
            heap_step_blk f_Algorithm_skipSpaces_prog
            exact skipSpaces_loop m _ jh hp addr elems _ (pos + 1) limit
              hget hlim hlim31 (by omega) (by simp only [Nat.add_eq]; omega)
          · have h13f : (elems[pos.toNat] == 13) = false := Bool.eq_false_iff.mpr h13
            simp only [h13f, h32f, h9f, Bool.false_or, Bool.false_eq_true, ↓reduceIte, Algorithm.isSpaceByte]
            rfl
    · have hcu : (if pos == limit then (0 : UInt32) else if pos < limit then 4294967295 else 1).toBitVec.slt 0#32 =
          false := by
        rw [compareUnsigned_slt_zero]; exact decide_eq_false hlt
      conv => rhs; rw [Algorithm.skipSpaces]; simp only [hlt, ↓reduceDIte]
      split_val_fuel 20; heap_step_blk f_Algorithm_skipSpaces_prog
      rw [hcu]; simp only [Bool.false_eq_true, ↓reduceIte]; rfl

theorem skipSpaces_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (addr : Nat) (elems : Array UInt8)
    (pos limit : UInt32) (hget : jh.get? addr = some (.byteArray elems))
    (hlim : limit.toNat ≤ elems.size) (hlim31 : limit.toNat < 2 ^ 31) :
    runJvm ((limit.toNat - pos.toNat) * 45 + 20) f_Algorithm_skipSpaces_prog
      ⟨0, [], setLocal (setLocal (setLocal (fun _ => .null) 0 (.heapRef addr)) 1 (.i32 pos)) 2 (.i32 limit), jh, hp⟩ =
      some (.i32 (Algorithm.skipSpaces ⟨elems⟩ pos limit)) := by
  apply runJvm_of_runJvmValFast0 _ _ _ _ rfl
  exact skipSpaces_loop (limit.toNat - pos.toNat) _ jh hp addr elems _ pos limit
    hget hlim hlim31 (Nat.le_refl _) (Nat.le_refl _)

theorem skipSpaces_1_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (addr : Nat) (elems : Array UInt8)
    (pos limit : UInt32) (hget : jh.get? addr = some (.byteArray elems))
    (hlim : limit.toNat ≤ elems.size) (hlim31 : limit.toNat < 2 ^ 31) :
    runJvm ((limit.toNat - pos.toNat) * 45 + 20) f_Algorithm_skipSpaces_1_prog
      ⟨0, [], setLocal (setLocal (setLocal (fun _ => .null) 0 (.heapRef addr)) 1 (.i32 pos)) 2 (.i32 limit), jh, hp⟩ =
      some (.i32 (Algorithm.skipSpaces ⟨elems⟩ pos limit)) := by
  rw [show f_Algorithm_skipSpaces_1_prog = f_Algorithm_skipSpaces_prog from rfl]
  exact skipSpaces_equiv jh hp addr elems pos limit hget hlim hlim31

theorem skipSpaces_2_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (addr : Nat) (elems : Array UInt8)
    (pos limit : UInt32) (hget : jh.get? addr = some (.byteArray elems))
    (hlim : limit.toNat ≤ elems.size) (hlim31 : limit.toNat < 2 ^ 31) :
    runJvm ((limit.toNat - pos.toNat) * 45 + 20) f_Algorithm_skipSpaces_2_prog
      ⟨0, [], setLocal (setLocal (setLocal (fun _ => .null) 0 (.heapRef addr)) 1 (.i32 pos)) 2 (.i32 limit), jh, hp⟩ =
      some (.i32 (Algorithm.skipSpaces ⟨elems⟩ pos limit)) := by
  rw [show f_Algorithm_skipSpaces_2_prog = f_Algorithm_skipSpaces_prog from rfl]
  exact skipSpaces_equiv jh hp addr elems pos limit hget hlim hlim31

/-! ### scanDigits (+ _1.._3) -/

private theorem scanDigits_loop : ∀ (m fuel : Nat)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (addr : Nat) (elems : Array UInt8)
    (locs : Nat → JvmVal) (limit p : UInt32) (acc : UInt64)
    (_ : jh.get? addr = some (.byteArray elems))
    (_ : limit.toNat ≤ elems.size)
    (_ : limit.toNat < 2 ^ 31)
    (_ : limit.toNat - p.toNat ≤ m)
    (_ : (limit.toNat - p.toNat) * 80 + 30 ≤ fuel),
    let r := Algorithm.scanDigits ⟨elems⟩ limit p acc
    runJvmValFast fuel f_Algorithm_scanDigits_prog 0 f_Algorithm_scanDigits_prog
      ⟨0, [], setLocal (setLocal (setLocal (setLocal locs 0 (.heapRef addr)) 1 (.i32 limit)) 2 (.i32 p))
        3 (.i64 acc), jh, hp⟩ =
      some (.pair (.boxedUInt r.1) (.boxedULong r.2))
  | 0, fuel, jh, hp, addr, elems, locs, limit, p, acc, hget, hlim, hlim31, hm, hfuel => by
    have hge : ¬(p < limit) := by
      intro hlt; have := UInt32.lt_iff_toNat_lt.mp hlt; omega
    have hcu : (if p == limit then (0 : UInt32) else if p < limit then 4294967295 else 1).toBitVec.slt 0#32 =
        false := by
      rw [compareUnsigned_slt_zero]; exact decide_eq_false hge
    dsimp only; rw [Algorithm.scanDigits]; simp only [hge, ↓reduceDIte]
    split_val_fuel 30; heap_step_blk f_Algorithm_scanDigits_prog
    rw [hcu]; simp only [Bool.false_eq_true, ↓reduceIte]
    heap_step_blk f_Algorithm_scanDigits_prog
  | m + 1, fuel, jh, hp, addr, elems, locs, limit, p, acc, hget, hlim, hlim31, hm, hfuel => by
    dsimp only
    by_cases hlt : p < limit
    · have hlt_nat : p.toNat < limit.toNat := UInt32.lt_iff_toNat_lt.mp hlt
      have hp_lt : p.toNat < elems.size := by omega
      have hp_slt : p.toBitVec.slt 0#32 = false := u32_slt_zero_of_lt_2_31 (by omega)
      have hp1_nat : (p + 1).toNat = p.toNat + 1 := by
        rw [UInt32.toNat_add, UInt32.toNat_one]; exact Nat.mod_eq_of_lt (by omega)
      have hcu : (if p == limit then (0 : UInt32) else if p < limit then 4294967295 else 1).toBitVec.slt 0#32 =
          true := by
        rw [compareUnsigned_slt_zero]; exact decide_eq_true hlt
      have hb_eq : elems[p.toNat] = (⟨elems⟩ : ByteArray).get! p.toNat := getElem_eq_byteArray_getBang elems hp_lt
      rw [Algorithm.scanDigits]; simp only [hlt, ↓reduceDIte, ← hb_eq]
      split_val_fuel 80; heap_step_blk f_Algorithm_scanDigits_prog
      rw [hcu]; simp only [↓reduceIte]
      heap_step_blk f_Algorithm_scanDigits_prog
      rw [runJvmValFast_baload hget hp_slt hp_lt]
      heap_step_blk f_Algorithm_scanDigits_prog
      rw [show (48 &&& 255 : UInt32) = 48 from rfl, intrinsicsCompare_48_sle]
      by_cases h48 : 48 ≤ elems[p.toNat]
      · simp only [h48, decide_true, ↓reduceIte]
        heap_step_blk f_Algorithm_scanDigits_prog
        rw [show (57 &&& 255 : UInt32) = 57 from rfl, intrinsicsCompare_57_sle]
        by_cases h57 : elems[p.toNat] ≤ 57
        · have hdig : Algorithm.isDigitByte elems[p.toNat] = true := by
            simp [Algorithm.isDigitByte, h48, h57]
          simp only [h57, decide_true, hdig, ↓reduceIte]
          heap_step_blk f_Algorithm_scanDigits_prog
          rw [compareUnsigned64_slt_zero]
          by_cases hgt : 4294967296 < acc
          · simp only [hgt, decide_true, ↓reduceIte]
            heap_step_blk f_Algorithm_scanDigits_prog
            exact scanDigits_loop m _ jh hp addr elems _ limit (p + 1) acc
              hget hlim hlim31 (by omega) (by simp only [Nat.add_eq]; omega)
          · simp only [hgt, decide_false, Bool.false_eq_true, ↓reduceIte]
            heap_step_blk f_Algorithm_scanDigits_prog
            rw [u8_signExt64_and255]
            exact scanDigits_loop m _ jh hp addr elems _ limit (p + 1)
              (acc * 10 + (elems[p.toNat].toUInt64 - 48)) hget hlim hlim31
              (by omega) (by simp only [Nat.add_eq]; omega)
        · have hdig : Algorithm.isDigitByte elems[p.toNat] = false := by
            simp [Algorithm.isDigitByte, h57]
          simp only [h57, decide_false, Bool.false_eq_true, hdig, ↓reduceIte]
          heap_step_blk f_Algorithm_scanDigits_prog
      · have hdig : Algorithm.isDigitByte elems[p.toNat] = false := by
          simp [Algorithm.isDigitByte, h48]
        simp only [h48, decide_false, Bool.false_eq_true, hdig, ↓reduceIte]
        heap_step_blk f_Algorithm_scanDigits_prog
    · have hcu : (if p == limit then (0 : UInt32) else if p < limit then 4294967295 else 1).toBitVec.slt 0#32 =
          false := by
        rw [compareUnsigned_slt_zero]; exact decide_eq_false hlt
      rw [Algorithm.scanDigits]; simp only [hlt, ↓reduceDIte]
      split_val_fuel 30; heap_step_blk f_Algorithm_scanDigits_prog
      rw [hcu]; simp only [Bool.false_eq_true, ↓reduceIte]
      heap_step_blk f_Algorithm_scanDigits_prog

theorem scanDigits_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (addr : Nat) (elems : Array UInt8)
    (limit p : UInt32) (acc : UInt64) (hget : jh.get? addr = some (.byteArray elems))
    (hlim : limit.toNat ≤ elems.size) (hlim31 : limit.toNat < 2 ^ 31) :
    let r := Algorithm.scanDigits ⟨elems⟩ limit p acc
    runJvm ((limit.toNat - p.toNat) * 80 + 30) f_Algorithm_scanDigits_prog
      ⟨0, [], setLocal (setLocal (setLocal (setLocal (fun _ => .null) 0 (.heapRef addr)) 1 (.i32 limit)) 2 (.i32 p))
        3 (.i64 acc), jh, hp⟩ =
      some (.pair (.boxedUInt r.1) (.boxedULong r.2)) := by
  apply runJvm_of_runJvmValFast0 _ _ _ _ rfl
  exact scanDigits_loop (limit.toNat - p.toNat) _ jh hp addr elems _ limit p acc
    hget hlim hlim31 (Nat.le_refl _) (Nat.le_refl _)

theorem scanDigits_1_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (addr : Nat) (elems : Array UInt8)
    (limit p : UInt32) (acc : UInt64) (hget : jh.get? addr = some (.byteArray elems))
    (hlim : limit.toNat ≤ elems.size) (hlim31 : limit.toNat < 2 ^ 31) :
    let r := Algorithm.scanDigits ⟨elems⟩ limit p acc
    runJvm ((limit.toNat - p.toNat) * 80 + 30) f_Algorithm_scanDigits_1_prog
      ⟨0, [], setLocal (setLocal (setLocal (setLocal (fun _ => .null) 0 (.heapRef addr)) 1 (.i32 limit)) 2 (.i32 p))
        3 (.i64 acc), jh, hp⟩ =
      some (.pair (.boxedUInt r.1) (.boxedULong r.2)) := by
  rw [show f_Algorithm_scanDigits_1_prog = f_Algorithm_scanDigits_prog from rfl]
  exact scanDigits_equiv jh hp addr elems limit p acc hget hlim hlim31

theorem scanDigits_2_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (addr : Nat) (elems : Array UInt8)
    (limit p : UInt32) (acc : UInt64) (hget : jh.get? addr = some (.byteArray elems))
    (hlim : limit.toNat ≤ elems.size) (hlim31 : limit.toNat < 2 ^ 31) :
    let r := Algorithm.scanDigits ⟨elems⟩ limit p acc
    runJvm ((limit.toNat - p.toNat) * 80 + 30) f_Algorithm_scanDigits_2_prog
      ⟨0, [], setLocal (setLocal (setLocal (setLocal (fun _ => .null) 0 (.heapRef addr)) 1 (.i32 limit)) 2 (.i32 p))
        3 (.i64 acc), jh, hp⟩ =
      some (.pair (.boxedUInt r.1) (.boxedULong r.2)) := by
  rw [show f_Algorithm_scanDigits_2_prog = f_Algorithm_scanDigits_prog from rfl]
  exact scanDigits_equiv jh hp addr elems limit p acc hget hlim hlim31

theorem scanDigits_3_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (addr : Nat) (elems : Array UInt8)
    (limit p : UInt32) (acc : UInt64) (hget : jh.get? addr = some (.byteArray elems))
    (hlim : limit.toNat ≤ elems.size) (hlim31 : limit.toNat < 2 ^ 31) :
    let r := Algorithm.scanDigits ⟨elems⟩ limit p acc
    runJvm ((limit.toNat - p.toNat) * 80 + 30) f_Algorithm_scanDigits_3_prog
      ⟨0, [], setLocal (setLocal (setLocal (setLocal (fun _ => .null) 0 (.heapRef addr)) 1 (.i32 limit)) 2 (.i32 p))
        3 (.i64 acc), jh, hp⟩ =
      some (.pair (.boxedUInt r.1) (.boxedULong r.2)) := by
  rw [show f_Algorithm_scanDigits_3_prog = f_Algorithm_scanDigits_prog from rfl]
  exact scanDigits_equiv jh hp addr elems limit p acc hget hlim hlim31

/-! ### scanDigitSet (+ _1) -/

private theorem scanDigitSet_loop : ∀ (m fuel : Nat)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (addr : Nat) (elems : Array UInt8)
    (locs : Nat → JvmVal) (limit p mask : UInt32)
    (_ : jh.get? addr = some (.byteArray elems))
    (_ : limit.toNat ≤ elems.size)
    (_ : limit.toNat < 2 ^ 31)
    (_ : limit.toNat - p.toNat ≤ m)
    (_ : (limit.toNat - p.toNat) * 75 + 30 ≤ fuel),
    let r := Algorithm.scanDigitSet ⟨elems⟩ limit p mask
    runJvmValFast fuel f_Algorithm_scanDigitSet_prog 0 f_Algorithm_scanDigitSet_prog
      ⟨0, [], setLocal (setLocal (setLocal (setLocal locs 0 (.heapRef addr)) 1 (.i32 limit)) 2 (.i32 p))
        3 (.i32 mask), jh, hp⟩ =
      some (.pair (.boxedUInt r.1) (.boxedUInt r.2))
  | 0, fuel, jh, hp, addr, elems, locs, limit, p, mask, hget, hlim, hlim31, hm, hfuel => by
    have hge : ¬(p < limit) := by
      intro hlt; have := UInt32.lt_iff_toNat_lt.mp hlt; omega
    have hcu : (if p == limit then (0 : UInt32) else if p < limit then 4294967295 else 1).toBitVec.slt 0#32 =
        false := by
      rw [compareUnsigned_slt_zero]; exact decide_eq_false hge
    dsimp only; rw [Algorithm.scanDigitSet]; simp only [hge, ↓reduceDIte]
    split_val_fuel 30; heap_step_blk f_Algorithm_scanDigitSet_prog
    rw [hcu]; simp only [Bool.false_eq_true, ↓reduceIte]
    heap_step_blk f_Algorithm_scanDigitSet_prog
  | m + 1, fuel, jh, hp, addr, elems, locs, limit, p, mask, hget, hlim, hlim31, hm, hfuel => by
    dsimp only
    by_cases hlt : p < limit
    · have hlt_nat : p.toNat < limit.toNat := UInt32.lt_iff_toNat_lt.mp hlt
      have hp_lt : p.toNat < elems.size := by omega
      have hp_slt : p.toBitVec.slt 0#32 = false := u32_slt_zero_of_lt_2_31 (by omega)
      have hp1_nat : (p + 1).toNat = p.toNat + 1 := by
        rw [UInt32.toNat_add, UInt32.toNat_one]; exact Nat.mod_eq_of_lt (by omega)
      have hcu : (if p == limit then (0 : UInt32) else if p < limit then 4294967295 else 1).toBitVec.slt 0#32 =
          true := by
        rw [compareUnsigned_slt_zero]; exact decide_eq_true hlt
      have hb_eq : elems[p.toNat] = (⟨elems⟩ : ByteArray).get! p.toNat := getElem_eq_byteArray_getBang elems hp_lt
      rw [Algorithm.scanDigitSet]; simp only [hlt, ↓reduceDIte, ← hb_eq]
      split_val_fuel 75; heap_step_blk f_Algorithm_scanDigitSet_prog
      rw [hcu]; simp only [↓reduceIte]
      heap_step_blk f_Algorithm_scanDigitSet_prog
      rw [runJvmValFast_baload hget hp_slt hp_lt]
      heap_step_blk f_Algorithm_scanDigitSet_prog
      rw [show (48 &&& 255 : UInt32) = 48 from rfl, intrinsicsCompare_48_sle]
      by_cases h48 : 48 ≤ elems[p.toNat]
      · simp only [h48, decide_true, ↓reduceIte]
        heap_step_blk f_Algorithm_scanDigitSet_prog
        rw [show (57 &&& 255 : UInt32) = 57 from rfl, intrinsicsCompare_57_sle]
        by_cases h57 : elems[p.toNat] ≤ 57
        · have hdig : Algorithm.isDigitByte elems[p.toNat] = true := by
            simp [Algorithm.isDigitByte, h48, h57]
          simp only [h57, decide_true, hdig, ↓reduceIte]
          heap_step_blk f_Algorithm_scanDigitSet_prog
          rw [u8_signExt_and255_sub48, u8_sub48_and31 h48 h57]
          exact scanDigitSet_loop m _ jh hp addr elems _ limit (p + 1)
            (mask ||| (1 : UInt32) <<< (elems[p.toNat].toUInt32 - 48)) hget hlim hlim31
            (by omega) (by simp only [Nat.add_eq]; omega)
        · have hdig : Algorithm.isDigitByte elems[p.toNat] = false := by
            simp [Algorithm.isDigitByte, h57]
          simp only [h57, decide_false, Bool.false_eq_true, hdig, ↓reduceIte]
          heap_step_blk f_Algorithm_scanDigitSet_prog
      · have hdig : Algorithm.isDigitByte elems[p.toNat] = false := by
          simp [Algorithm.isDigitByte, h48]
        simp only [h48, decide_false, Bool.false_eq_true, hdig, ↓reduceIte]
        heap_step_blk f_Algorithm_scanDigitSet_prog
    · have hcu : (if p == limit then (0 : UInt32) else if p < limit then 4294967295 else 1).toBitVec.slt 0#32 =
          false := by
        rw [compareUnsigned_slt_zero]; exact decide_eq_false hlt
      rw [Algorithm.scanDigitSet]; simp only [hlt, ↓reduceDIte]
      split_val_fuel 30; heap_step_blk f_Algorithm_scanDigitSet_prog
      rw [hcu]; simp only [Bool.false_eq_true, ↓reduceIte]
      heap_step_blk f_Algorithm_scanDigitSet_prog

theorem scanDigitSet_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (addr : Nat) (elems : Array UInt8)
    (limit p mask : UInt32) (hget : jh.get? addr = some (.byteArray elems))
    (hlim : limit.toNat ≤ elems.size) (hlim31 : limit.toNat < 2 ^ 31) :
    let r := Algorithm.scanDigitSet ⟨elems⟩ limit p mask
    runJvm ((limit.toNat - p.toNat) * 75 + 30) f_Algorithm_scanDigitSet_prog
      ⟨0, [], setLocal (setLocal (setLocal (setLocal (fun _ => .null) 0 (.heapRef addr)) 1 (.i32 limit)) 2 (.i32 p))
        3 (.i32 mask), jh, hp⟩ =
      some (.pair (.boxedUInt r.1) (.boxedUInt r.2)) := by
  apply runJvm_of_runJvmValFast0 _ _ _ _ rfl
  exact scanDigitSet_loop (limit.toNat - p.toNat) _ jh hp addr elems _ limit p mask
    hget hlim hlim31 (Nat.le_refl _) (Nat.le_refl _)

theorem scanDigitSet_1_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (addr : Nat) (elems : Array UInt8)
    (limit p mask : UInt32) (hget : jh.get? addr = some (.byteArray elems))
    (hlim : limit.toNat ≤ elems.size) (hlim31 : limit.toNat < 2 ^ 31) :
    let r := Algorithm.scanDigitSet ⟨elems⟩ limit p mask
    runJvm ((limit.toNat - p.toNat) * 75 + 30) f_Algorithm_scanDigitSet_1_prog
      ⟨0, [], setLocal (setLocal (setLocal (setLocal (fun _ => .null) 0 (.heapRef addr)) 1 (.i32 limit)) 2 (.i32 p))
        3 (.i32 mask), jh, hp⟩ =
      some (.pair (.boxedUInt r.1) (.boxedUInt r.2)) := by
  rw [show f_Algorithm_scanDigitSet_1_prog = f_Algorithm_scanDigitSet_prog from rfl]
  exact scanDigitSet_equiv jh hp addr elems limit p mask hget hlim hlim31

/-! ### decodeCharAt (+ _1.._2) -/

private def decodeCharAtProg (cls : String) : List JvmInstr :=
  [.nop, .nop, .aload 0, .iload 1, .baload, .invokestatic "kotlin/UByte" "constructor-impl" "(B)B",
   .iconst 255, .iand, .invokestatic "kotlin/UInt" "constructor-impl" "(I)I", .istore 3,
   .iload 3, .iconst 128, .invokestatic "java/lang/Integer" "compareUnsigned" "(II)I", .iflt 181,
   .iconst 0, .istore 4, .iload 3, .iconst 224, .iand,
   .invokestatic "kotlin/UInt" "constructor-impl" "(I)I", .iconst 192, .if_icmpne 56,
   .iconst 1, .iload 2, .iload 1, .isub,
   .invokestatic "kotlin/UInt" "constructor-impl" "(I)I",
   .invokestatic "java/lang/Integer" "compareUnsigned" "(II)I", .ifge 56,
   .iload 3, .iconst 31, .iand, .invokestatic "kotlin/UInt" "constructor-impl" "(I)I",
   .iconst 6, .ishl, .invokestatic "kotlin/UInt" "constructor-impl" "(I)I", .istore 5,
   .iload 1, .aload 0, .iconst 1, .invokestatic cls "f_Algorithm_decodeCharAt___lam__0-Mv_zs3U" "(I[BI)I",
   .istore 6, .newClass "kotlin/Pair", .dup, .iload 5, .iload 6, .ior,
   .invokestatic "kotlin/UInt" "constructor-impl" "(I)I",
   .invokestatic "kotlin/UInt" "box-impl" "(I)Lkotlin/UInt;",
   .iload 1, .iconst 2, .iadd, .invokestatic "kotlin/UInt" "constructor-impl" "(I)I",
   .invokestatic "kotlin/UInt" "box-impl" "(I)Lkotlin/UInt;",
   .invokespecial "kotlin/Pair" "<init>" "(Ljava/lang/Object;Ljava/lang/Object;)V", .areturn,
   .iload 3, .iconst 240, .iand, .invokestatic "kotlin/UInt" "constructor-impl" "(I)I",
   .iconst 224, .if_icmpeq 65, .iconst 240, .istore 4, .goto 115,
   .iconst 2, .iload 2, .iload 1, .isub,
   .invokestatic "kotlin/UInt" "constructor-impl" "(I)I",
   .invokestatic "java/lang/Integer" "compareUnsigned" "(II)I", .iflt 75,
   .iconst 240, .istore 4, .goto 115,
   .iload 3, .iconst 15, .iand, .invokestatic "kotlin/UInt" "constructor-impl" "(I)I",
   .iconst 12, .ishl, .invokestatic "kotlin/UInt" "constructor-impl" "(I)I", .istore 5,
   .iload 1, .aload 0, .iconst 1, .invokestatic cls "f_Algorithm_decodeCharAt___lam__0-Mv_zs3U" "(I[BI)I",
   .istore 6, .iload 5, .iload 6, .iconst 6, .ishl,
   .invokestatic "kotlin/UInt" "constructor-impl" "(I)I", .ior,
   .invokestatic "kotlin/UInt" "constructor-impl" "(I)I", .istore 7,
   .iload 1, .aload 0, .iconst 2, .invokestatic cls "f_Algorithm_decodeCharAt___lam__0-Mv_zs3U" "(I[BI)I",
   .istore 8, .newClass "kotlin/Pair", .dup, .iload 7, .iload 8, .ior,
   .invokestatic "kotlin/UInt" "constructor-impl" "(I)I",
   .invokestatic "kotlin/UInt" "box-impl" "(I)Lkotlin/UInt;",
   .iload 1, .iconst 3, .iadd, .invokestatic "kotlin/UInt" "constructor-impl" "(I)I",
   .invokestatic "kotlin/UInt" "box-impl" "(I)Lkotlin/UInt;",
   .invokespecial "kotlin/Pair" "<init>" "(Ljava/lang/Object;Ljava/lang/Object;)V", .areturn,
   .iload 3, .iconst 248, .iand, .invokestatic "kotlin/UInt" "constructor-impl" "(I)I",
   .iload 4, .if_icmpne 192,
   .iconst 3, .iload 2, .iload 1, .isub,
   .invokestatic "kotlin/UInt" "constructor-impl" "(I)I",
   .invokestatic "java/lang/Integer" "compareUnsigned" "(II)I", .ifge 192,
   .iload 3, .iconst 7, .iand, .invokestatic "kotlin/UInt" "constructor-impl" "(I)I",
   .iconst 18, .ishl, .invokestatic "kotlin/UInt" "constructor-impl" "(I)I", .istore 5,
   .iload 1, .aload 0, .iconst 1, .invokestatic cls "f_Algorithm_decodeCharAt___lam__0-Mv_zs3U" "(I[BI)I",
   .istore 6, .iload 5, .iload 6, .iconst 12, .ishl,
   .invokestatic "kotlin/UInt" "constructor-impl" "(I)I", .ior,
   .invokestatic "kotlin/UInt" "constructor-impl" "(I)I", .istore 7,
   .iload 1, .aload 0, .iconst 2, .invokestatic cls "f_Algorithm_decodeCharAt___lam__0-Mv_zs3U" "(I[BI)I",
   .istore 8, .iload 7, .iload 8, .iconst 6, .ishl,
   .invokestatic "kotlin/UInt" "constructor-impl" "(I)I", .ior,
   .invokestatic "kotlin/UInt" "constructor-impl" "(I)I", .istore 9,
   .iload 1, .aload 0, .iconst 3, .invokestatic cls "f_Algorithm_decodeCharAt___lam__0-Mv_zs3U" "(I[BI)I",
   .istore 10, .newClass "kotlin/Pair", .dup, .iload 9, .iload 10, .ior,
   .invokestatic "kotlin/UInt" "constructor-impl" "(I)I",
   .invokestatic "kotlin/UInt" "box-impl" "(I)Lkotlin/UInt;",
   .iload 1, .iconst 4, .iadd, .invokestatic "kotlin/UInt" "constructor-impl" "(I)I",
   .invokestatic "kotlin/UInt" "box-impl" "(I)Lkotlin/UInt;",
   .invokespecial "kotlin/Pair" "<init>" "(Ljava/lang/Object;Ljava/lang/Object;)V", .areturn,
   .newClass "kotlin/Pair", .dup, .iload 3, .invokestatic "kotlin/UInt" "box-impl" "(I)Lkotlin/UInt;",
   .iload 1, .iconst 1, .iadd, .invokestatic "kotlin/UInt" "constructor-impl" "(I)I",
   .invokestatic "kotlin/UInt" "box-impl" "(I)Lkotlin/UInt;",
   .invokespecial "kotlin/Pair" "<init>" "(Ljava/lang/Object;Ljava/lang/Object;)V", .areturn,
   .newClass "kotlin/Pair", .dup, .iload 3, .invokestatic "kotlin/UInt" "box-impl" "(I)Lkotlin/UInt;",
   .iload 1, .iconst 1, .iadd, .invokestatic "kotlin/UInt" "constructor-impl" "(I)I",
   .invokestatic "kotlin/UInt" "box-impl" "(I)Lkotlin/UInt;",
   .invokespecial "kotlin/Pair" "<init>" "(Ljava/lang/Object;Ljava/lang/Object;)V", .areturn]

private theorem decodeCharAt_pc120 (cls : String)
    (hcls : cls = "Life105LeanKt" ∨ cls = "Life106LeanKt" ∨ cls = "MacroCellLeanKt" ∨
      cls = "PlaintextLeanKt" ∨ cls = "RleLeanKt")
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (addr : Nat) (elems : Array UInt8)
    (locs : Nat → JvmVal) (p limit b0 : UInt32) (fuel : Nat) (hfuel : 60 ≤ fuel)
    (hget : jh.get? addr = some (.byteArray elems))
    (hlt : p < limit) (hlim : limit.toNat ≤ elems.size) (hlim31 : limit.toNat < 2 ^ 31)
    (hl0 : locs 0 = .heapRef addr) (hl1 : locs 1 = .i32 p) (hl2 : locs 2 = .i32 limit)
    (hl3 : locs 3 = .i32 b0) :
    (if (!b0 &&& 248 == 240) = true then
      runJvmValFast fuel (decodeCharAtProg cls) 192 ((decodeCharAtProg cls).drop 192)
        ⟨192, [], setLocal locs 4 (.i32 240), jh, hp⟩
    else
      runJvmValFast fuel (decodeCharAtProg cls) 121 ((decodeCharAtProg cls).drop 121)
        ⟨121, [], setLocal locs 4 (.i32 240), jh, hp⟩) =
      let cont (k : UInt32) := ((⟨elems⟩ : ByteArray).get! (p + k).toNat).toUInt32 &&& 0x3F
      let r :=
        if b0 &&& 0xF8 == 0xF0 && limit - p > 3 then
          (((b0 &&& 0x07) <<< 18) ||| (cont 1 <<< 12) ||| (cont 2 <<< 6) ||| cont 3, p + 4)
        else (b0, p + 1)
      some (.pair (.boxedUInt r.1) (.boxedUInt r.2)) := by
  obtain ⟨fk1, rfl⟩ : ∃ fk1, fuel = fk1 + 60 := ⟨fuel - 60, (Nat.sub_add_cancel hfuel).symm⟩
  have hp_nat : p.toNat < limit.toNat := UInt32.lt_iff_toNat_lt.mp hlt
  have hsub : (limit - p).toNat = limit.toNat - p.toNat := UInt32.toNat_sub_of_le _ _ (UInt32.le_of_lt hlt)
  dsimp only
  by_cases hmask : b0 &&& 0xF8 = 0xF0
  · have hmbeq : (b0 &&& 248 == 240) = true := beq_iff_eq.mpr hmask
    simp only [hmbeq, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    heap_step_blk (decodeCharAtProg cls)
    simp only [hl2, hl1, Jvm.JvmVal.asI32]; rw [compareUnsigned_sge_zero]
    by_cases hlen : (3 : UInt32) < limit - p
    · have hlen_nat : 3 < limit.toNat - p.toNat := by
        have := UInt32.lt_iff_toNat_lt.mp hlen
        rw [show (3 : UInt32).toNat = 3 from rfl] at this; omega
      have hle_f : decide (limit - p ≤ 3) = false := decide_eq_false (by
        rw [UInt32.le_iff_toNat_le, show (3 : UInt32).toNat = 3 from rfl]; omega)
      have hlt_t : decide (limit - p > 3) = true := decide_eq_true hlen
      simp only [hle_f, Bool.false_eq_true, hlt_t, Bool.true_and, ↓reduceIte]
      have hp1 : (p + 1).toNat = p.toNat + 1 := by
        rw [UInt32.toNat_add, show (1 : UInt32).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
      have hp2 : (p + 2).toNat = p.toNat + 2 := by
        rw [UInt32.toNat_add, show (2 : UInt32).toNat = 2 from rfl, Nat.mod_eq_of_lt (by omega)]
      have hp3 : (p + 3).toNat = p.toNat + 3 := by
        rw [UInt32.toNat_add, show (3 : UInt32).toNat = 3 from rfl, Nat.mod_eq_of_lt (by omega)]
      have hk1s : (p + 1).toBitVec.slt 0#32 = false := u32_slt_zero_of_lt_2_31 (by omega)
      have hk1l : (p + 1).toNat < elems.size := by omega
      have hk2s : (p + 2).toBitVec.slt 0#32 = false := u32_slt_zero_of_lt_2_31 (by omega)
      have hk2l : (p + 2).toNat < elems.size := by omega
      have hk3s : (p + 3).toBitVec.slt 0#32 = false := u32_slt_zero_of_lt_2_31 (by omega)
      have hk3l : (p + 3).toNat < elems.size := by omega
      heap_step_blk (decodeCharAtProg cls); dsimp only
      rw [hl1, hl0]
      rw [runJvmValFast_invokestatic_step
        (stepStatic_decodeCharAtLam_heap (k := .i32 1) (p := .i32 p) hcls hget hk1s hk1l)]
      heap_step_blk (decodeCharAtProg cls); dsimp only
      rw [hl1, hl0]
      rw [runJvmValFast_invokestatic_step
        (stepStatic_decodeCharAtLam_heap (k := .i32 2) (p := .i32 p) hcls hget hk2s hk2l)]
      heap_step_blk (decodeCharAtProg cls); dsimp only
      rw [hl1, hl0]
      rw [runJvmValFast_invokestatic_step
        (stepStatic_decodeCharAtLam_heap (k := .i32 3) (p := .i32 p) hcls hget hk3s hk3l)]
      heap_step_blk (decodeCharAtProg cls)
      simp only [hl3, hl1, Jvm.JvmVal.asI32, ByteArray.get!,
        getElem!_pos elems (p + 1).toNat hk1l, getElem!_pos elems (p + 2).toNat hk2l,
        getElem!_pos elems (p + 3).toNat hk3l,
        show (18 &&& 31 : UInt32) = 18 from rfl,
        show (12 &&& 31 : UInt32) = 12 from rfl,
        show (6 &&& 31 : UInt32) = 6 from rfl]
    · have hle : limit - p ≤ 3 := by
        rw [UInt32.le_iff_toNat_le]; rw [UInt32.lt_iff_toNat_lt] at hlen; omega
      have hlt_f : decide (limit - p > 3) = false := decide_eq_false hlen
      simp only [hle, decide_true, hlt_f, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
      heap_step_blk (decodeCharAtProg cls)
      simp only [hl3, hl1]; rfl
  · have hneq : (b0 &&& 248 == 240) = false := beq_false_of_ne hmask
    simp only [hneq, Bool.not_false, Bool.false_eq_true, Bool.false_and, ↓reduceIte]
    heap_step_blk (decodeCharAtProg cls)
    simp only [hl3, hl1]; rfl

private theorem decodeCharAt_pc56 (cls : String)
    (hcls : cls = "Life105LeanKt" ∨ cls = "Life106LeanKt" ∨ cls = "MacroCellLeanKt" ∨
      cls = "PlaintextLeanKt" ∨ cls = "RleLeanKt")
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (addr : Nat) (elems : Array UInt8)
    (locs : Nat → JvmVal) (p limit b0 : UInt32) (fuel : Nat) (hfuel : 100 ≤ fuel)
    (hget : jh.get? addr = some (.byteArray elems))
    (hlt : p < limit) (hlim : limit.toNat ≤ elems.size) (hlim31 : limit.toNat < 2 ^ 31)
    (hl0 : locs 0 = .heapRef addr) (hl1 : locs 1 = .i32 p) (hl2 : locs 2 = .i32 limit)
    (hl3 : locs 3 = .i32 b0) :
    runJvmValFast fuel (decodeCharAtProg cls) 56 ((decodeCharAtProg cls).drop 56)
      ⟨56, [], locs, jh, hp⟩ =
      let cont (k : UInt32) := ((⟨elems⟩ : ByteArray).get! (p + k).toNat).toUInt32 &&& 0x3F
      let r :=
        if b0 &&& 0xF0 == 0xE0 && limit - p > 2 then
          (((b0 &&& 0x0F) <<< 12) ||| (cont 1 <<< 6) ||| cont 2, p + 3)
        else if b0 &&& 0xF8 == 0xF0 && limit - p > 3 then
          (((b0 &&& 0x07) <<< 18) ||| (cont 1 <<< 12) ||| (cont 2 <<< 6) ||| cont 3, p + 4)
        else (b0, p + 1)
      some (.pair (.boxedUInt r.1) (.boxedUInt r.2)) := by
  obtain ⟨fk, rfl⟩ : ∃ fk, fuel = fk + 100 := ⟨fuel - 100, (Nat.sub_add_cancel hfuel).symm⟩
  have hp_nat : p.toNat < limit.toNat := UInt32.lt_iff_toNat_lt.mp hlt
  have hsub : (limit - p).toNat = limit.toNat - p.toNat := UInt32.toNat_sub_of_le _ _ (UInt32.le_of_lt hlt)
  dsimp only
  heap_step_blk (decodeCharAtProg cls)
  simp only [hl3, Jvm.JvmVal.asI32]
  by_cases hm3 : b0 &&& 240 = 224
  · simp only [show (b0 &&& 240 == 224) = true from beq_iff_eq.mpr hm3, ↓reduceIte]
    heap_step_blk (decodeCharAtProg cls)
    simp only [hl2, hl1, Jvm.JvmVal.asI32]; rw [compareUnsigned_slt_zero]
    by_cases hl3len : 2 < limit - p
    · have hl3_nat : 2 < limit.toNat - p.toNat := by
        have := UInt32.lt_iff_toNat_lt.mp hl3len
        rw [show (2 : UInt32).toNat = 2 from rfl] at this; omega
      have hp1 : (p + 1).toNat = p.toNat + 1 := by
        rw [UInt32.toNat_add, show (1 : UInt32).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
      have hp2 : (p + 2).toNat = p.toNat + 2 := by
        rw [UInt32.toNat_add, show (2 : UInt32).toNat = 2 from rfl, Nat.mod_eq_of_lt (by omega)]
      have hk1s : (p + 1).toBitVec.slt 0#32 = false := u32_slt_zero_of_lt_2_31 (by omega)
      have hk1l : (p + 1).toNat < elems.size := by omega
      have hk2s : (p + 2).toBitVec.slt 0#32 = false := u32_slt_zero_of_lt_2_31 (by omega)
      have hk2l : (p + 2).toNat < elems.size := by omega
      simp only [hl3len, decide_true, Bool.true_and, ↓reduceIte]
      heap_step_blk (decodeCharAtProg cls); dsimp only
      rw [hl1, hl0]
      rw [runJvmValFast_invokestatic_step
        (stepStatic_decodeCharAtLam_heap (k := .i32 1) (p := .i32 p) hcls hget hk1s hk1l)]
      heap_step_blk (decodeCharAtProg cls); dsimp only
      rw [hl1, hl0]
      rw [runJvmValFast_invokestatic_step
        (stepStatic_decodeCharAtLam_heap (k := .i32 2) (p := .i32 p) hcls hget hk2s hk2l)]
      heap_step_blk (decodeCharAtProg cls)
      simp only [hl3, hl1, Jvm.JvmVal.asI32, ByteArray.get!,
        getElem!_pos elems (p + 1).toNat hk1l, getElem!_pos elems (p + 2).toNat hk2l,
        show (12 &&& 31 : UInt32) = 12 from rfl,
        show (6 &&& 31 : UInt32) = 6 from rfl]
    · simp only [hl3len, decide_false, Bool.false_eq_true, Bool.true_and, ↓reduceIte]
      heap_step_blk (decodeCharAtProg cls)
      simp only [hl3, Jvm.JvmVal.asI32, ByteArray.get!]
      exact decodeCharAt_pc120 cls hcls jh hp addr elems _ p limit b0 _
        (by simp only [nat_add_eq_add]; omega) hget hlt hlim hlim31 hl0 hl1 hl2 hl3
  · have hneq : (b0 &&& 240 == 224) = false := beq_false_of_ne hm3
    simp only [hneq, Bool.false_eq_true, Bool.false_and, ↓reduceIte]
    heap_step_blk (decodeCharAtProg cls)
    simp only [hl3, Jvm.JvmVal.asI32, ByteArray.get!]
    exact decodeCharAt_pc120 cls hcls jh hp addr elems _ p limit b0 _
      (by simp only [nat_add_eq_add]; omega) hget hlt hlim hlim31 hl0 hl1 hl2 hl3

private theorem decodeCharAt_spec (cls : String)
    (hcls : cls = "Life105LeanKt" ∨ cls = "Life106LeanKt" ∨ cls = "MacroCellLeanKt" ∨
      cls = "PlaintextLeanKt" ∨ cls = "RleLeanKt")
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (addr : Nat) (elems : Array UInt8)
    (p limit : UInt32) (hget : jh.get? addr = some (.byteArray elems))
    (hlt : p < limit) (hlim : limit.toNat ≤ elems.size) (hlim31 : limit.toNat < 2 ^ 31) :
    let r := Algorithm.decodeCharAt ⟨elems⟩ p limit
    runJvm 150 (decodeCharAtProg cls)
      ⟨0, [], setLocal (setLocal (setLocal (fun _ => .null) 0 (.heapRef addr)) 1 (.i32 p)) 2 (.i32 limit), jh, hp⟩ =
      some (.pair (.boxedUInt r.1) (.boxedUInt r.2)) := by
  have hp_nat : p.toNat < limit.toNat := UInt32.lt_iff_toNat_lt.mp hlt
  have hp_lt : p.toNat < elems.size := by omega
  have hp_slt : p.toBitVec.slt 0#32 = false := u32_slt_zero_of_lt_2_31 (by omega)
  have hsub : (limit - p).toNat = limit.toNat - p.toNat := UInt32.toNat_sub_of_le _ _ (UInt32.le_of_lt hlt)
  have hb_eq : elems[p.toNat] = (⟨elems⟩ : ByteArray).get! p.toNat := getElem_eq_byteArray_getBang elems hp_lt
  apply runJvm_of_runJvmValFast0 _ _ _ _ rfl
  rw [Algorithm.decodeCharAt]; simp only [← hb_eq]
  split_val_fuel 150; heap_step_blk (decodeCharAtProg cls)
  rw [runJvmValFast_baload hget hp_slt hp_lt]
  heap_step_blk (decodeCharAtProg cls)
  rw [u8_signExt_and255, compareUnsigned_slt_zero]
  by_cases h1 : elems[p.toNat].toUInt32 < 128
  · simp only [h1, decide_true, ↓reduceIte]
    heap_step_blk (decodeCharAtProg cls)
  · simp only [h1, decide_false, Bool.false_eq_true, ↓reduceIte]
    heap_step_blk (decodeCharAtProg cls)
    by_cases hm2 : elems[p.toNat].toUInt32 &&& 224 = 192
    · simp only [show (elems[p.toNat].toUInt32 &&& 224 == 192) = true from beq_iff_eq.mpr hm2,
        Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      heap_step_blk (decodeCharAtProg cls)
      rw [compareUnsigned_sge_zero]
      by_cases hl2 : 1 < limit - p
      · have hl2_nat : 1 < limit.toNat - p.toNat := by
          have := UInt32.lt_iff_toNat_lt.mp hl2
          rw [show (1 : UInt32).toNat = 1 from rfl] at this; omega
        have hp1 : (p + 1).toNat = p.toNat + 1 := by
          rw [UInt32.toNat_add, show (1 : UInt32).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
        have hk1s : (p + 1).toBitVec.slt 0#32 = false := u32_slt_zero_of_lt_2_31 (by omega)
        have hk1l : (p + 1).toNat < elems.size := by omega
        have hle_f : decide (limit - p ≤ 1) = false := decide_eq_false (by
          rw [UInt32.le_iff_toNat_le, show (1 : UInt32).toNat = 1 from rfl]; omega)
        have hl2_t : decide (limit - p > 1) = true := decide_eq_true hl2
        simp only [hle_f, Bool.false_eq_true, hl2_t, Bool.true_and, ↓reduceIte]
        heap_step_blk (decodeCharAtProg cls); dsimp only
        rw [runJvmValFast_invokestatic_step
          (stepStatic_decodeCharAtLam_heap (k := .i32 1) (p := .i32 p) hcls hget hk1s hk1l)]
        heap_step_blk (decodeCharAtProg cls)
        simp only [ByteArray.get!, getElem!_pos elems (p + 1).toNat hk1l,
          show (6 &&& 31 : UInt32) = 6 from rfl]
      · have hle : limit - p ≤ 1 := by
          rw [UInt32.le_iff_toNat_le]; rw [UInt32.lt_iff_toNat_lt] at hl2
          rw [show (1 : UInt32).toNat = 1 from rfl] at hl2 ⊢; omega
        have hl2_f : decide (limit - p > 1) = false := decide_eq_false hl2
        simp only [hle, decide_true, hl2_f, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
        refine decodeCharAt_pc56 cls hcls jh hp addr elems _ p limit elems[p.toNat].toUInt32 _ (by omega)
          hget hlt hlim hlim31 ?_ ?_ ?_ ?_
        all_goals rfl
    · have hneq : (elems[p.toNat].toUInt32 &&& 224 == 192) = false := beq_false_of_ne hm2
      simp only [hneq, Bool.not_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      refine decodeCharAt_pc56 cls hcls jh hp addr elems _ p limit elems[p.toNat].toUInt32 _ (by omega)
        hget hlt hlim hlim31 ?_ ?_ ?_ ?_
      all_goals rfl

theorem decodeCharAt_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (addr : Nat) (elems : Array UInt8)
    (p limit : UInt32) (hget : jh.get? addr = some (.byteArray elems))
    (hlt : p < limit) (hlim : limit.toNat ≤ elems.size) (hlim31 : limit.toNat < 2 ^ 31) :
    let r := Algorithm.decodeCharAt ⟨elems⟩ p limit
    runJvm 150 f_Algorithm_decodeCharAt_prog
      ⟨0, [], setLocal (setLocal (setLocal (fun _ => .null) 0 (.heapRef addr)) 1 (.i32 p)) 2 (.i32 limit), jh, hp⟩ =
      some (.pair (.boxedUInt r.1) (.boxedUInt r.2)) := by
  rw [show f_Algorithm_decodeCharAt_prog = decodeCharAtProg "MacroCellLeanKt" from rfl]
  exact decodeCharAt_spec "MacroCellLeanKt" (by simp) jh hp addr elems p limit hget hlt hlim hlim31

theorem decodeCharAt_1_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (addr : Nat) (elems : Array UInt8)
    (p limit : UInt32) (hget : jh.get? addr = some (.byteArray elems))
    (hlt : p < limit) (hlim : limit.toNat ≤ elems.size) (hlim31 : limit.toNat < 2 ^ 31) :
    let r := Algorithm.decodeCharAt ⟨elems⟩ p limit
    runJvm 150 f_Algorithm_decodeCharAt_1_prog
      ⟨0, [], setLocal (setLocal (setLocal (fun _ => .null) 0 (.heapRef addr)) 1 (.i32 p)) 2 (.i32 limit), jh, hp⟩ =
      some (.pair (.boxedUInt r.1) (.boxedUInt r.2)) := by
  rw [show f_Algorithm_decodeCharAt_1_prog = decodeCharAtProg "PlaintextLeanKt" from rfl]
  exact decodeCharAt_spec "PlaintextLeanKt" (by simp) jh hp addr elems p limit hget hlt hlim hlim31

theorem decodeCharAt_2_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (addr : Nat) (elems : Array UInt8)
    (p limit : UInt32) (hget : jh.get? addr = some (.byteArray elems))
    (hlt : p < limit) (hlim : limit.toNat ≤ elems.size) (hlim31 : limit.toNat < 2 ^ 31) :
    let r := Algorithm.decodeCharAt ⟨elems⟩ p limit
    runJvm 150 f_Algorithm_decodeCharAt_2_prog
      ⟨0, [], setLocal (setLocal (setLocal (fun _ => .null) 0 (.heapRef addr)) 1 (.i32 p)) 2 (.i32 limit), jh, hp⟩ =
      some (.pair (.boxedUInt r.1) (.boxedUInt r.2)) := by
  rw [show f_Algorithm_decodeCharAt_2_prog = decodeCharAtProg "RleLeanKt" from rfl]
  exact decodeCharAt_spec "RleLeanKt" (by simp) jh hp addr elems p limit hget hlt hlim hlim31

/-! ### Option helpers for ParsedUInt32 / ParsedInt32 -/

private theorem jvmHeap_set_push_2_0 (H : Jvm.JvmHeap AlgExt) :
    let a0 : Array (Jvm.JvmVal AlgExt) := Array.replicate 2 .null
    let H0 := (H.alloc (.objArray "java/lang/Object" a0)).2
    let H1 := H0.set H.objects.size (.objArray "java/lang/Object" (a0.set 0 (.boxedInt 1) (by simp [a0])))
    H1 = (H.alloc (.objArray "java/lang/Object" #[.boxedInt 1, .null])).2 := by
  simp only [Jvm.JvmHeap.set, Jvm.JvmHeap.alloc, Array.size_push, Nat.lt_add_one, ↓reduceDIte]
  congr 1; apply Array.ext (by simp)
  intro k hk1 hk2
  simp only [Array.size_set, Array.size_push] at hk1 hk2
  simp only [Array.getElem_set, Array.getElem_push]
  split
  · next heq => subst heq; simp [Array.replicate, Array.set]
  · next hne =>
    have hklt : k < H.objects.size := by omega
    simp [hklt]

private theorem array6_set_eq (v1 v5 : JvmVal) :
    let a0 : Array (Jvm.JvmVal AlgExt) := Array.replicate 6 .null
    let a1 : Array (Jvm.JvmVal AlgExt) := a0.set 0 (.boxedInt 0) (by simp [a0])
    let a2 : Array (Jvm.JvmVal AlgExt) := a1.set 1 v1 (by simp [a1, a0])
    let a3 : Array (Jvm.JvmVal AlgExt) := a2.set 2 .null (by simp [a2, a1, a0])
    let a4 : Array (Jvm.JvmVal AlgExt) := a3.set 3 .null (by simp [a3, a2, a1, a0])
    let a5 : Array (Jvm.JvmVal AlgExt) := a4.set 4 .null (by simp [a4, a3, a2, a1, a0])
    let a6 : Array (Jvm.JvmVal AlgExt) := a5.set 5 v5 (by simp [a5, a4, a3, a2, a1, a0])
    a6 = #[.boxedInt 0, v1, .null, .null, .null, v5] := by
  simp [Array.replicate, Array.set]

private theorem jvmHeap_set6_push (H : Jvm.JvmHeap AlgExt) (v1 v5 : JvmVal) :
    let a0 : Array (Jvm.JvmVal AlgExt) := Array.replicate 6 .null
    let a1 : Array (Jvm.JvmVal AlgExt) := a0.set 0 (.boxedInt 0) (by simp [a0])
    let a2 : Array (Jvm.JvmVal AlgExt) := a1.set 1 v1 (by simp [a1, a0])
    let a3 : Array (Jvm.JvmVal AlgExt) := a2.set 2 .null (by simp [a2, a1, a0])
    let a4 : Array (Jvm.JvmVal AlgExt) := a3.set 3 .null (by simp [a3, a2, a1, a0])
    let a5 : Array (Jvm.JvmVal AlgExt) := a4.set 4 .null (by simp [a4, a3, a2, a1, a0])
    let a6 : Array (Jvm.JvmVal AlgExt) := a5.set 5 v5 (by simp [a5, a4, a3, a2, a1, a0])
    let H0 := (H.alloc (.objArray "java/lang/Object" a0)).2
    let H1 := H0.set H.objects.size (.objArray "java/lang/Object" a1)
    let H2 := H1.set H.objects.size (.objArray "java/lang/Object" a2)
    let H3 := H2.set H.objects.size (.objArray "java/lang/Object" a3)
    let H4 := H3.set H.objects.size (.objArray "java/lang/Object" a4)
    let H5 := H4.set H.objects.size (.objArray "java/lang/Object" a5)
    let H6 := H5.set H.objects.size (.objArray "java/lang/Object" a6)
    H6 = (H.alloc (.objArray "java/lang/Object" #[.boxedInt 0, v1, .null, .null, .null, v5])).2 := by
  dsimp only
  simp only [jvmHeap_set_set]
  rw [array6_set_eq v1 v5]
  simp only [Jvm.JvmHeap.set, Jvm.JvmHeap.alloc, Array.size_push, Nat.lt_add_one, ↓reduceDIte]
  congr 1; apply Array.ext (by simp)
  intro k hk1 hk2
  simp only [Array.size_set, Array.size_push] at hk1 hk2
  simp only [Array.getElem_set, Array.getElem_push]
  split
  · next heq => subst heq; simp
  · next hne =>
    have hklt : k < H.objects.size := by omega
    simp [hklt]

private theorem jvmHeap_alloc2_set1 (H : Jvm.JvmHeap AlgExt) (v1 v5 : JvmVal) :
    let H1 := (H.alloc (.objArray "java/lang/Object" #[.boxedInt 1, .null])).2
    let H2 := (H1.alloc (.objArray "java/lang/Object" #[.boxedInt 0, v1, .null, .null, .null, v5])).2
    let a2 : Array (Jvm.JvmVal AlgExt) := #[.boxedInt 1, .null]
    H2.set H.objects.size (.objArray "java/lang/Object" (a2.set 1 (.heapRef (H.objects.size + 1)) (by simp [a2]))) =
      { objects := (H.objects.push (.objArray "java/lang/Object" #[.boxedInt 1, .heapRef (H.objects.size + 1)])).push
          (.objArray "java/lang/Object" #[.boxedInt 0, v1, .null, .null, .null, v5]), statics := H.statics } := by
  simp only [Jvm.JvmHeap.set, Jvm.JvmHeap.alloc, Array.size_push]
  have hlt : H.objects.size < H.objects.size + 1 + 1 := by omega
  simp only [hlt, ↓reduceDIte]
  congr 1; apply Array.ext (by simp)
  intro k hk1 hk2
  simp only [Array.size_set, Array.size_push] at hk1 hk2
  simp only [Array.getElem_set, Array.getElem_push]
  split
  · next heq =>
    subst heq
    simp [Nat.lt_add_one, Array.set]
  · next hne =>
    by_cases hklt : k < H.objects.size + 1
    · have hklt0 : k < H.objects.size := by omega
      simp [hklt, hklt0]
    · simp [hklt]

private theorem jvmHeap_set1_0 (H : Jvm.JvmHeap AlgExt) :
    let a0 : Array (Jvm.JvmVal AlgExt) := Array.replicate 1 .null
    let H0 := (H.alloc (.objArray "java/lang/Object" a0)).2
    H0.set H.objects.size (.objArray "java/lang/Object" (a0.set 0 (.boxedInt 0) (by simp [a0]))) =
      (H.alloc (.objArray "java/lang/Object" #[.boxedInt 0])).2 := by
  simp only [Jvm.JvmHeap.set, Jvm.JvmHeap.alloc, Array.size_push, Nat.lt_add_one, ↓reduceDIte]
  congr 1; apply Array.ext (by simp)
  intro k hk1 hk2
  simp only [Array.size_set, Array.size_push] at hk1 hk2
  simp only [Array.getElem_set, Array.getElem_push]
  split
  · next heq => subst heq; simp [Array.replicate, Array.set]
  · next hne =>
    have hklt : k < H.objects.size := by omega
    simp [hklt]

private theorem jvmHeap_set1_u32_0 (H : Jvm.JvmHeap AlgExt)
    (h : (0 : UInt32).toNat < (Array.replicate 1 (JvmVal.null : Jvm.JvmVal AlgExt)).size) :
    ((H.alloc (.objArray "java/lang/Object" (Array.replicate 1 .null))).2).set H.objects.size
      (.objArray "java/lang/Object" ((Array.replicate 1 (JvmVal.null : Jvm.JvmVal AlgExt)).set
        (0 : UInt32).toNat (.boxedInt 0) h)) =
      (H.alloc (.objArray "java/lang/Object" #[.boxedInt 0])).2 := jvmHeap_set1_0 H

private theorem u32_zero_sub_toInt32 (x : UInt32) : ((0 : Int32) - x.toInt32).toUInt32 = 0 - x := by
  cases x with | ofBitVec b => rfl

/-! ### parseUInt32At (+ _1) -/

private def parseUInt32AtProg (cls : String) : List JvmInstr :=
  [.aload 0, .iload 2, .iload 1, .lconst 0,
   .invokestatic cls "f_Algorithm_scanDigits-G4XTHLI" "([BIIJ)Lkotlin/Pair;",
   .astore 3, .aload 3, .invokevirtual "kotlin/Pair" "getFirst" "()Ljava/lang/Object;",
   .checkcast "kotlin/UInt", .invokevirtual "kotlin/UInt" "unbox-impl" "()I", .istore 4,
   .aload 3, .invokevirtual "kotlin/Pair" "getSecond" "()Ljava/lang/Object;",
   .checkcast "kotlin/ULong", .invokevirtual "kotlin/ULong" "unbox-impl" "()J", .lstore 5,
   .iload 4, .iload 1, .if_icmpeq 83,
   .lload 5, .lconst 4294967295, .invokestatic "java/lang/Long" "compareUnsigned" "(JJ)I", .ifle 35,
   .iconst 1, .anewarray "java/lang/Object", .astore 8,
   .aload 8, .iconst 0, .iconst 0, .invokestatic "java/lang/Integer" "valueOf" "(I)Ljava/lang/Integer;",
   .aastore, .aload 8, .astore 7, .aload 7, .areturn,
   .iconst 2, .anewarray "java/lang/Object", .astore 8,
   .aload 8, .iconst 0, .iconst 1, .invokestatic "java/lang/Integer" "valueOf" "(I)Ljava/lang/Integer;",
   .aastore, .aload 8, .iconst 1,
   .iconst 6, .anewarray "java/lang/Object", .astore 9,
   .aload 9, .iconst 0, .iconst 0, .invokestatic "java/lang/Integer" "valueOf" "(I)Ljava/lang/Integer;",
   .aastore, .aload 9, .iconst 1, .lload 5, .l2i,
   .invokestatic "kotlin/UInt" "constructor-impl" "(I)I",
   .invokestatic "kotlin/UInt" "box-impl" "(I)Lkotlin/UInt;", .aastore,
   .aload 9, .iconst 2, .aconstNull, .aastore,
   .aload 9, .iconst 3, .aconstNull, .aastore,
   .aload 9, .iconst 4, .aconstNull, .aastore,
   .aload 9, .iconst 5, .iload 4,
   .invokestatic "kotlin/UInt" "box-impl" "(I)Lkotlin/UInt;", .aastore,
   .aload 9, .aastore, .aload 8, .astore 7, .aload 7, .areturn,
   .iconst 1, .anewarray "java/lang/Object", .astore 8,
   .aload 8, .iconst 0, .iconst 0, .invokestatic "java/lang/Integer" "valueOf" "(I)Ljava/lang/Integer;",
   .aastore, .aload 8, .astore 7, .aload 7, .areturn]

private theorem parseUInt32At_pc18 (cls : String)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (locs : Nat → JvmVal) (pos e : UInt32) (v : UInt64)
    (_hl1 : locs 1 = .i32 pos) (hl4 : locs 4 = .i32 e) (hl5 : locs 5 = .i64 v) :
    let res : Option Algorithm.ParsedUInt32 :=
      if e == pos then none
      else if v ≤ 4294967295 then some ⟨v.toUInt32, e⟩ else none
    let jhAfter := match res with
      | none => (jh.alloc (.objArray "java/lang/Object" #[.boxedInt 0])).2
      | some p =>
        { objects := (jh.objects.push (.objArray "java/lang/Object" #[.boxedInt 1, .heapRef (jh.objects.size + 1)])).push
            (.objArray "java/lang/Object" #[.boxedInt 0, .boxedUInt p.val, .null, .null, .null, .boxedUInt p.next]),
          statics := jh.statics }
    ∃ st', (if (e == pos) = true then
        runJvmResFast 101 (parseUInt32AtProg cls) 83 ((parseUInt32AtProg cls).drop 83) ⟨83, [], locs, jh, hp⟩
      else
        runJvmResFast 101 (parseUInt32AtProg cls) 19 ((parseUInt32AtProg cls).drop 19) ⟨19, [], locs, jh, hp⟩) =
      some (.heapRef jh.objects.size, st') ∧ st'.jvmHeap = jhAfter := by
  have ha0 : (jh.alloc (.objArray "java/lang/Object" (Array.replicate 1 .null))).2.get? jh.objects.size =
      some (.objArray "java/lang/Object" (Array.replicate 1 .null)) := jvmHeap_get?_alloc_self _ _
  by_cases heq : e = pos
  · have hbeq : (e == pos) = true := beq_iff_eq.mpr heq
    exact ⟨_, by
      simp only [hbeq, ↓reduceIte]
      heap_step_blk (parseUInt32AtProg cls)
      rw [runJvmResFast_anewarray_obj (by decide), show (1 : UInt32).toNat = 1 from rfl]
      heap_step_blk (parseUInt32AtProg cls)
      rw [runJvmResFast_aastore (idx := 0) ha0 (by decide) (by decide)]
      rw [runJvmResFast_stepResHeapChunk 120]
      (conv => lhs; arg 1; jvm_whnf_blk)
      rw [afterResBlockChunk_done], by
      simp only [hbeq, ↓reduceIte]; exact jvmHeap_set1_u32_0 jh _⟩
  · have hbne : (e == pos) = false := beq_false_of_ne heq
    by_cases hle : v ≤ 4294967295
    · let jh0 := (jh.alloc (.objArray "java/lang/Object" (Array.replicate 2 .null))).2
      have h2_0 : jh0.get? jh.objects.size = some (.objArray "java/lang/Object" (Array.replicate 2 .null)) :=
        jvmHeap_get?_alloc_self _ _
      let jh1 := jh0.set jh.objects.size (.objArray "java/lang/Object"
        ((Array.replicate 2 (JvmVal.null : Jvm.JvmVal AlgExt)).set 0 (.boxedInt 1) (by decide)))
      have h1eq : jh1 = (jh.alloc (.objArray "java/lang/Object" #[.boxedInt 1, .null])).2 := jvmHeap_set_push_2_0 jh
      have hsz1 : jh1.objects.size = jh.objects.size + 1 := by rw [h1eq]; simp [Jvm.JvmHeap.alloc]
      let a6_0 : Array (Jvm.JvmVal AlgExt) := Array.replicate 6 .null
      let a6_1 : Array (Jvm.JvmVal AlgExt) := a6_0.set 0 (.boxedInt 0) (by simp [a6_0])
      let a6_2 : Array (Jvm.JvmVal AlgExt) := a6_1.set 1 (.boxedUInt v.toUInt32) (by simp [a6_1, a6_0])
      let a6_3 : Array (Jvm.JvmVal AlgExt) := a6_2.set 2 .null (by simp [a6_2, a6_1, a6_0])
      let a6_4 : Array (Jvm.JvmVal AlgExt) := a6_3.set 3 .null (by simp [a6_3, a6_2, a6_1, a6_0])
      let a6_5 : Array (Jvm.JvmVal AlgExt) := a6_4.set 4 .null (by simp [a6_4, a6_3, a6_2, a6_1, a6_0])
      let a6_6 : Array (Jvm.JvmVal AlgExt) := a6_5.set 5 (.boxedUInt e) (by simp [a6_5, a6_4, a6_3, a6_2, a6_1, a6_0])
      let k0 := (jh1.alloc (.objArray "java/lang/Object" a6_0)).2
      have hk0 : k0.get? (jh.objects.size + 1) = some (.objArray "java/lang/Object" a6_0) := by
        simpa [k0, hsz1] using jvmHeap_get?_alloc_self jh1 (.objArray "java/lang/Object" a6_0)
      let k1 := k0.set (jh.objects.size + 1) (.objArray "java/lang/Object" a6_1)
      have hk1 : k1.get? (jh.objects.size + 1) = some (.objArray "java/lang/Object" a6_1) := jvmHeap_get?_set_self hk0
      let k2 := k1.set (jh.objects.size + 1) (.objArray "java/lang/Object" a6_2)
      have hk2 : k2.get? (jh.objects.size + 1) = some (.objArray "java/lang/Object" a6_2) := jvmHeap_get?_set_self hk1
      let k3 := k2.set (jh.objects.size + 1) (.objArray "java/lang/Object" a6_3)
      have hk3 : k3.get? (jh.objects.size + 1) = some (.objArray "java/lang/Object" a6_3) := jvmHeap_get?_set_self hk2
      let k4 := k3.set (jh.objects.size + 1) (.objArray "java/lang/Object" a6_4)
      have hk4 : k4.get? (jh.objects.size + 1) = some (.objArray "java/lang/Object" a6_4) := jvmHeap_get?_set_self hk3
      let k5 := k4.set (jh.objects.size + 1) (.objArray "java/lang/Object" a6_5)
      have hk5 : k5.get? (jh.objects.size + 1) = some (.objArray "java/lang/Object" a6_5) := jvmHeap_get?_set_self hk4
      let k6 := k5.set (jh.objects.size + 1) (.objArray "java/lang/Object" a6_6)
      have hk6_eq : k6 = ((jh.alloc (.objArray "java/lang/Object" #[.boxedInt 1, .null])).2.alloc
          (.objArray "java/lang/Object" #[.boxedInt 0, .boxedUInt v.toUInt32, .null, .null, .null, .boxedUInt e])).2 := by
        dsimp only [k6, k5, k4, k3, k2, k1, k0, a6_6, a6_5, a6_4, a6_3, a6_2, a6_1, a6_0]
        rw [← h1eq, ← hsz1]
        exact jvmHeap_set6_push jh1 (.boxedUInt v.toUInt32) (.boxedUInt e)
      have hk6_get : k6.get? jh.objects.size = some (.objArray "java/lang/Object" #[.boxedInt 1, .null]) := by
        rw [hk6_eq]
        have hlt0 : jh.objects.size < ((jh.alloc (.objArray "java/lang/Object" #[.boxedInt 1, .null])).2).objects.size := by
          simp [Jvm.JvmHeap.alloc]
        rw [jvmHeap_get?_alloc_lt _ _ hlt0]
        exact jvmHeap_get?_alloc_self _ _
      exact ⟨_, by
        simp only [hbne, Bool.false_eq_true, ↓reduceIte]
        heap_step_blk (parseUInt32AtProg cls)
        simp only [hl5, Jvm.JvmVal.asI64]; rw [compareUnsigned64_sle_zero]
        simp only [hle, decide_true, ↓reduceIte]
        heap_step_blk (parseUInt32AtProg cls)
        rw [runJvmResFast_anewarray_obj (by decide), show (2 : UInt32).toNat = 2 from rfl]
        change runJvmResFast _ _ _ _ ⟨_, _, _, jh0, hp⟩ = _
        heap_step_blk (parseUInt32AtProg cls)
        rw [runJvmResFast_aastore (idx := 0) h2_0 (by decide) (by decide)]
        change runJvmResFast _ _ _ _ ⟨_, _, _, jh1, hp⟩ = _
        heap_step_blk (parseUInt32AtProg cls)
        rw [runJvmResFast_anewarray_obj (by decide), show (6 : UInt32).toNat = 6 from rfl]
        rw [hsz1]; change runJvmResFast _ _ _ _ ⟨_, _, _, k0, hp⟩ = _
        heap_step_blk (parseUInt32AtProg cls)
        rw [runJvmResFast_aastore (idx := 0) hk0 (by decide) (by decide)]
        change runJvmResFast _ _ _ _ ⟨_, _, _, k1, hp⟩ = _
        heap_step_blk (parseUInt32AtProg cls)
        rw [hl5, runJvmResFast_aastore (idx := 1) hk1 (by decide) (by simp [a6_1, a6_0])]
        change runJvmResFast _ _ _ _ ⟨_, _, _, k2, hp⟩ = _
        heap_step_blk (parseUInt32AtProg cls)
        rw [runJvmResFast_aastore (idx := 2) hk2 (by decide) (by simp [a6_2, a6_1, a6_0])]
        change runJvmResFast _ _ _ _ ⟨_, _, _, k3, hp⟩ = _
        heap_step_blk (parseUInt32AtProg cls)
        rw [runJvmResFast_aastore (idx := 3) hk3 (by decide) (by simp [a6_3, a6_2, a6_1, a6_0])]
        change runJvmResFast _ _ _ _ ⟨_, _, _, k4, hp⟩ = _
        heap_step_blk (parseUInt32AtProg cls)
        rw [runJvmResFast_aastore (idx := 4) hk4 (by decide) (by simp [a6_4, a6_3, a6_2, a6_1, a6_0])]
        change runJvmResFast _ _ _ _ ⟨_, _, _, k5, hp⟩ = _
        heap_step_blk (parseUInt32AtProg cls)
        rw [hl4, runJvmResFast_aastore (idx := 5) hk5 (by decide) (by simp [a6_5, a6_4, a6_3, a6_2, a6_1, a6_0])]
        change runJvmResFast _ _ _ _ ⟨_, _, _, k6, hp⟩ = _
        heap_step_blk (parseUInt32AtProg cls)
        rw [runJvmResFast_aastore (idx := 1) hk6_get (by decide) (by decide)]
        rw [runJvmResFast_stepResHeapChunk 120]
        (conv => lhs; arg 1; jvm_whnf_blk)
        rw [afterResBlockChunk_done], by
        simp only [hbne, hle, Bool.false_eq_true, ↓reduceIte]
        rw [hk6_eq]
        exact jvmHeap_alloc2_set1 jh (.boxedUInt v.toUInt32) (.boxedUInt e)⟩
    · exact ⟨_, by
        simp only [hbne, Bool.false_eq_true, ↓reduceIte]
        heap_step_blk (parseUInt32AtProg cls)
        simp only [hl5, Jvm.JvmVal.asI64]; rw [compareUnsigned64_sle_zero]
        simp only [hle, decide_false, Bool.false_eq_true, ↓reduceIte]
        heap_step_blk (parseUInt32AtProg cls)
        rw [runJvmResFast_anewarray_obj (by decide), show (1 : UInt32).toNat = 1 from rfl]
        heap_step_blk (parseUInt32AtProg cls)
        rw [runJvmResFast_aastore (idx := 0) ha0 (by decide) (by decide)]
        rw [runJvmResFast_stepResHeapChunk 120]
        (conv => lhs; arg 1; jvm_whnf_blk)
        rw [afterResBlockChunk_done], by
        simp only [hbne, hle, Bool.false_eq_true, ↓reduceIte]
        exact jvmHeap_set1_u32_0 jh _⟩

private theorem parseUInt32At_spec (cls : String)
    (hcls : cls = "Life105LeanKt" ∨ cls = "Life106LeanKt" ∨ cls = "MacroCellLeanKt" ∨
      cls = "PlaintextLeanKt" ∨ cls = "RleLeanKt")
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (addr : Nat) (elems : Array UInt8)
    (pos limit : UInt32) (hget : jh.get? addr = some (.byteArray elems)) :
    let res := Algorithm.parseUInt32At ⟨elems⟩ pos limit
    let jhAfter := match res with
      | none => (jh.alloc (.objArray "java/lang/Object" #[.boxedInt 0])).2
      | some p =>
        { objects := (jh.objects.push (.objArray "java/lang/Object" #[.boxedInt 1, .heapRef (jh.objects.size + 1)])).push
            (.objArray "java/lang/Object" #[.boxedInt 0, .boxedUInt p.val, .null, .null, .null, .boxedUInt p.next]),
          statics := jh.statics }
    ∃ st', runJvmRes 120 (parseUInt32AtProg cls)
      ⟨0, [], setLocal (setLocal (setLocal (fun _ => .null) 0 (.heapRef addr)) 1 (.i32 pos)) 2 (.i32 limit), jh, hp⟩ =
      some (.heapRef jh.objects.size, st') ∧ st'.jvmHeap = jhAfter := by
  let r := Algorithm.scanDigits ⟨elems⟩ limit pos 0
  let locs0 := setLocal (setLocal (setLocal (fun _ => (.null : JvmVal)) 0 (.heapRef addr)) 1 (.i32 pos)) 2 (.i32 limit)
  let locs16 := setLocal (setLocal (setLocal locs0 3 (.pair (.boxedUInt r.1) (.boxedULong r.2)))
    4 (.i32 r.1)) 5 (.i64 r.2)
  obtain ⟨st', hrun, hst⟩ := parseUInt32At_pc18 cls jh hp locs16 pos r.1 r.2 rfl rfl rfl
  refine ⟨st', ?_, by rw [hst, Algorithm.parseUInt32At]⟩
  apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
  split_res_fuel 20; heap_step_blk (parseUInt32AtProg cls)
  rw [runJvmResFast_invokestatic_step (stepStatic_scanDigits_heap hcls hget)]
  heap_step_blk (parseUInt32AtProg cls)
  rw [runJvmResFast_checkcast_boxedUInt (Or.inl rfl)]
  heap_step_blk (parseUInt32AtProg cls)
  rw [runJvmResFast_checkcast_boxedULong (Or.inl rfl)]
  heap_step_blk (parseUInt32AtProg cls)
  exact hrun

theorem parseUInt32At_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (addr : Nat) (elems : Array UInt8)
    (pos limit : UInt32) (hget : jh.get? addr = some (.byteArray elems)) :
    let res := Algorithm.parseUInt32At ⟨elems⟩ pos limit
    let jhAfter := match res with
      | none => (jh.alloc (.objArray "java/lang/Object" #[.boxedInt 0])).2
      | some p =>
        { objects := (jh.objects.push (.objArray "java/lang/Object" #[.boxedInt 1, .heapRef (jh.objects.size + 1)])).push
            (.objArray "java/lang/Object" #[.boxedInt 0, .boxedUInt p.val, .null, .null, .null, .boxedUInt p.next]),
          statics := jh.statics }
    ∃ st', runJvmRes 120 f_Algorithm_parseUInt32At_prog
      ⟨0, [], setLocal (setLocal (setLocal (fun _ => .null) 0 (.heapRef addr)) 1 (.i32 pos)) 2 (.i32 limit), jh, hp⟩ =
      some (.heapRef jh.objects.size, st') ∧ st'.jvmHeap = jhAfter := by
  rw [show f_Algorithm_parseUInt32At_prog = parseUInt32AtProg "MacroCellLeanKt" from rfl]
  exact parseUInt32At_spec "MacroCellLeanKt" (by simp) jh hp addr elems pos limit hget

theorem parseUInt32At_1_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (addr : Nat) (elems : Array UInt8)
    (pos limit : UInt32) (hget : jh.get? addr = some (.byteArray elems)) :
    let res := Algorithm.parseUInt32At ⟨elems⟩ pos limit
    let jhAfter := match res with
      | none => (jh.alloc (.objArray "java/lang/Object" #[.boxedInt 0])).2
      | some p =>
        { objects := (jh.objects.push (.objArray "java/lang/Object" #[.boxedInt 1, .heapRef (jh.objects.size + 1)])).push
            (.objArray "java/lang/Object" #[.boxedInt 0, .boxedUInt p.val, .null, .null, .null, .boxedUInt p.next]),
          statics := jh.statics }
    ∃ st', runJvmRes 120 f_Algorithm_parseUInt32At_1_prog
      ⟨0, [], setLocal (setLocal (setLocal (fun _ => .null) 0 (.heapRef addr)) 1 (.i32 pos)) 2 (.i32 limit), jh, hp⟩ =
      some (.heapRef jh.objects.size, st') ∧ st'.jvmHeap = jhAfter := by
  rw [show f_Algorithm_parseUInt32At_1_prog = parseUInt32AtProg "RleLeanKt" from rfl]
  exact parseUInt32At_spec "RleLeanKt" (by simp) jh hp addr elems pos limit hget

/-! ### parseInt32At (+ _1.._2) -/

private def parseInt32AtProg (cls : String) : List JvmInstr :=
  [.iconst 0, .istore 3, .iconst 0, .istore 4, .iload 1, .iload 2,
   .invokestatic "java/lang/Integer" "compareUnsigned" "(II)I", .iflt 13,
   .iconst 0, .istore 3, .iload 1, .istore 4, .goto 33,
   .aload 0, .iload 1, .baload, .invokestatic "kotlin/UByte" "constructor-impl" "(B)B",
   .iconst 45, .if_icmpeq 24,
   .iconst 0, .istore 3, .iload 1, .istore 4, .goto 33,
   .iload 1, .iconst 1, .iadd, .invokestatic "kotlin/UInt" "constructor-impl" "(I)I",
   .istore 5, .iconst 1, .istore 3, .iload 5, .istore 4,
   .aload 0, .iload 2, .iload 4, .lconst 0,
   .invokestatic cls "f_Algorithm_scanDigits-G4XTHLI" "([BIIJ)Lkotlin/Pair;",
   .astore 5, .aload 5, .invokevirtual "kotlin/Pair" "getFirst" "()Ljava/lang/Object;",
   .checkcast "kotlin/UInt", .invokevirtual "kotlin/UInt" "unbox-impl" "()I", .istore 6,
   .aload 5, .invokevirtual "kotlin/Pair" "getSecond" "()Ljava/lang/Object;",
   .checkcast "kotlin/ULong", .invokevirtual "kotlin/ULong" "unbox-impl" "()J", .lstore 7,
   .iload 6, .iload 4, .if_icmpeq 187,
   .iload 3, .ifne 121,
   .lload 7, .lconst 2147483647, .invokestatic "java/lang/Long" "compareUnsigned" "(JJ)I", .ifle 70,
   .iconst 1, .anewarray "java/lang/Object", .astore 10,
   .aload 10, .iconst 0, .iconst 0, .invokestatic "java/lang/Integer" "valueOf" "(I)Ljava/lang/Integer;",
   .aastore, .aload 10, .astore 9, .aload 9, .areturn,
   .lload 7, .l2i, .invokestatic "kotlin/UInt" "constructor-impl" "(I)I",
   .invokestatic cls "f_Algorithm_uint32ToInt32-WZ4Q5Ns" "(I)I", .istore 9,
   .iconst 2, .anewarray "java/lang/Object", .astore 11,
   .aload 11, .iconst 0, .iconst 1, .invokestatic "java/lang/Integer" "valueOf" "(I)Ljava/lang/Integer;",
   .aastore, .aload 11, .iconst 1,
   .iconst 6, .anewarray "java/lang/Object", .astore 12,
   .aload 12, .iconst 0, .iconst 0, .invokestatic "java/lang/Integer" "valueOf" "(I)Ljava/lang/Integer;",
   .aastore, .aload 12, .iconst 1, .iload 9, .invokestatic "java/lang/Integer" "valueOf" "(I)Ljava/lang/Integer;",
   .aastore, .aload 12, .iconst 2, .aconstNull, .aastore,
   .aload 12, .iconst 3, .aconstNull, .aastore,
   .aload 12, .iconst 4, .aconstNull, .aastore,
   .aload 12, .iconst 5, .iload 6, .invokestatic "kotlin/UInt" "box-impl" "(I)Lkotlin/UInt;",
   .aastore, .aload 12, .aastore, .aload 11, .astore 10, .aload 10, .areturn,
   .lload 7, .lconst 2147483648, .invokestatic "java/lang/Long" "compareUnsigned" "(JJ)I", .ifle 137,
   .iconst 1, .anewarray "java/lang/Object", .astore 10,
   .aload 10, .iconst 0, .iconst 0, .invokestatic "java/lang/Integer" "valueOf" "(I)Ljava/lang/Integer;",
   .aastore, .aload 10, .astore 9, .aload 9, .areturn,
   .iconst 2, .anewarray "java/lang/Object", .astore 10,
   .aload 10, .iconst 0, .iconst 1, .invokestatic "java/lang/Integer" "valueOf" "(I)Ljava/lang/Integer;",
   .aastore, .aload 10, .iconst 1,
   .iconst 6, .anewarray "java/lang/Object", .astore 11,
   .aload 11, .iconst 0, .iconst 0, .invokestatic "java/lang/Integer" "valueOf" "(I)Ljava/lang/Integer;",
   .aastore, .aload 11, .iconst 1, .iconst 0, .lload 7, .l2i,
   .invokestatic "kotlin/UInt" "constructor-impl" "(I)I", .isub,
   .invokestatic "java/lang/Integer" "valueOf" "(I)Ljava/lang/Integer;",
   .aastore, .aload 11, .iconst 2, .aconstNull, .aastore,
   .aload 11, .iconst 3, .aconstNull, .aastore,
   .aload 11, .iconst 4, .aconstNull, .aastore,
   .aload 11, .iconst 5, .iload 6, .invokestatic "kotlin/UInt" "box-impl" "(I)Lkotlin/UInt;",
   .aastore, .aload 11, .aastore, .aload 10, .astore 9, .aload 9, .areturn,
   .iconst 1, .anewarray "java/lang/Object", .astore 10,
   .aload 10, .iconst 0, .iconst 0, .invokestatic "java/lang/Integer" "valueOf" "(I)Ljava/lang/Integer;",
   .aastore, .aload 10, .astore 9, .aload 9, .areturn]

private theorem parseInt32At_pc52 (cls : String)
    (hcls : cls = "Life105LeanKt" ∨ cls = "Life106LeanKt" ∨ cls = "MacroCellLeanKt" ∨
      cls = "PlaintextLeanKt" ∨ cls = "RleLeanKt")
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (locs : Nat → JvmVal)
    (start e : UInt32) (v : UInt64) (isNeg : Bool) (fuel : Nat) (hfuel : 80 ≤ fuel)
    (hl3 : locs 3 = .i32 (if isNeg then 1 else 0)) (_hl4 : locs 4 = .i32 start)
    (hl6 : locs 6 = .i32 e) (hl7 : locs 7 = .i64 v) :
    let res : Option Algorithm.ParsedInt32 :=
      if e == start then none
      else if isNeg then
        if v ≤ 2147483648 then some ⟨(0 : Int32) - v.toUInt32.toInt32, e⟩ else none
      else if v ≤ 2147483647 then some ⟨Algorithm.uint32ToInt32 v.toUInt32, e⟩ else none
    let jhAfter := match res with
      | none => (jh.alloc (.objArray "java/lang/Object" #[.boxedInt 0])).2
      | some p =>
        { objects := (jh.objects.push (.objArray "java/lang/Object" #[.boxedInt 1, .heapRef (jh.objects.size + 1)])).push
            (.objArray "java/lang/Object"
              #[.boxedInt 0, .boxedInt p.val.toUInt32, .null, .null, .null, .boxedUInt p.next]),
          statics := jh.statics }
    ∃ st', (if (e == start) = true then
        runJvmResFast fuel (parseInt32AtProg cls) 187 ((parseInt32AtProg cls).drop 187) ⟨187, [], locs, jh, hp⟩
      else
        runJvmResFast fuel (parseInt32AtProg cls) 52 ((parseInt32AtProg cls).drop 52) ⟨52, [], locs, jh, hp⟩) =
      some (.heapRef jh.objects.size, st') ∧ st'.jvmHeap = jhAfter := by
  obtain ⟨fk, rfl⟩ : ∃ fk, fuel = fk + 80 := ⟨fuel - 80, (Nat.sub_add_cancel hfuel).symm⟩
  have ha0 : (jh.alloc (.objArray "java/lang/Object" (Array.replicate 1 .null))).2.get? jh.objects.size =
      some (.objArray "java/lang/Object" (Array.replicate 1 .null)) := jvmHeap_get?_alloc_self _ _
  by_cases heq : e = start
  · have hbeq : (e == start) = true := beq_iff_eq.mpr heq
    exact ⟨_, by
      simp only [hbeq, ↓reduceIte]
      heap_step_blk (parseInt32AtProg cls)
      rw [runJvmResFast_anewarray_obj (by decide), show (1 : UInt32).toNat = 1 from rfl]
      heap_step_blk (parseInt32AtProg cls)
      rw [runJvmResFast_aastore (idx := 0) ha0 (by decide) (by decide)]
      rw [runJvmResFast_stepResHeapChunk 120]
      (conv => lhs; arg 1; jvm_whnf_blk)
      rw [afterResBlockChunk_done], by
      simp only [hbeq, ↓reduceIte]; exact jvmHeap_set1_u32_0 jh _⟩
  · have hbne : (e == start) = false := beq_false_of_ne heq
    cases isNeg
    · dsimp only [Bool.false_eq_true, ↓reduceIte] at hl3 ⊢
      by_cases hle : v ≤ 2147483647
      · let jh0 := (jh.alloc (.objArray "java/lang/Object" (Array.replicate 2 .null))).2
        have h2_0 : jh0.get? jh.objects.size = some (.objArray "java/lang/Object" (Array.replicate 2 .null)) :=
          jvmHeap_get?_alloc_self _ _
        let jh1 := jh0.set jh.objects.size (.objArray "java/lang/Object"
          ((Array.replicate 2 (JvmVal.null : Jvm.JvmVal AlgExt)).set 0 (.boxedInt 1) (by decide)))
        have h1eq : jh1 = (jh.alloc (.objArray "java/lang/Object" #[.boxedInt 1, .null])).2 := jvmHeap_set_push_2_0 jh
        have hsz1 : jh1.objects.size = jh.objects.size + 1 := by rw [h1eq]; simp [Jvm.JvmHeap.alloc]
        let a6_0 : Array (Jvm.JvmVal AlgExt) := Array.replicate 6 .null
        let a6_1 : Array (Jvm.JvmVal AlgExt) := a6_0.set 0 (.boxedInt 0) (by simp [a6_0])
        let a6_2 : Array (Jvm.JvmVal AlgExt) := a6_1.set 1 (.boxedInt v.toUInt32) (by simp [a6_1, a6_0])
        let a6_3 : Array (Jvm.JvmVal AlgExt) := a6_2.set 2 .null (by simp [a6_2, a6_1, a6_0])
        let a6_4 : Array (Jvm.JvmVal AlgExt) := a6_3.set 3 .null (by simp [a6_3, a6_2, a6_1, a6_0])
        let a6_5 : Array (Jvm.JvmVal AlgExt) := a6_4.set 4 .null (by simp [a6_4, a6_3, a6_2, a6_1, a6_0])
        let a6_6 : Array (Jvm.JvmVal AlgExt) := a6_5.set 5 (.boxedUInt e) (by simp [a6_5, a6_4, a6_3, a6_2, a6_1, a6_0])
        let k0 := (jh1.alloc (.objArray "java/lang/Object" a6_0)).2
        have hk0 : k0.get? (jh.objects.size + 1) = some (.objArray "java/lang/Object" a6_0) := by
          simpa [k0, hsz1] using jvmHeap_get?_alloc_self jh1 (.objArray "java/lang/Object" a6_0)
        let k1 := k0.set (jh.objects.size + 1) (.objArray "java/lang/Object" a6_1)
        have hk1 : k1.get? (jh.objects.size + 1) = some (.objArray "java/lang/Object" a6_1) := jvmHeap_get?_set_self hk0
        let k2 := k1.set (jh.objects.size + 1) (.objArray "java/lang/Object" a6_2)
        have hk2 : k2.get? (jh.objects.size + 1) = some (.objArray "java/lang/Object" a6_2) := jvmHeap_get?_set_self hk1
        let k3 := k2.set (jh.objects.size + 1) (.objArray "java/lang/Object" a6_3)
        have hk3 : k3.get? (jh.objects.size + 1) = some (.objArray "java/lang/Object" a6_3) := jvmHeap_get?_set_self hk2
        let k4 := k3.set (jh.objects.size + 1) (.objArray "java/lang/Object" a6_4)
        have hk4 : k4.get? (jh.objects.size + 1) = some (.objArray "java/lang/Object" a6_4) := jvmHeap_get?_set_self hk3
        let k5 := k4.set (jh.objects.size + 1) (.objArray "java/lang/Object" a6_5)
        have hk5 : k5.get? (jh.objects.size + 1) = some (.objArray "java/lang/Object" a6_5) := jvmHeap_get?_set_self hk4
        let k6 := k5.set (jh.objects.size + 1) (.objArray "java/lang/Object" a6_6)
        have hk6_eq : k6 = ((jh.alloc (.objArray "java/lang/Object" #[.boxedInt 1, .null])).2.alloc
            (.objArray "java/lang/Object" #[.boxedInt 0, .boxedInt v.toUInt32, .null, .null, .null, .boxedUInt e])).2 := by
          dsimp only [k6, k5, k4, k3, k2, k1, k0, a6_6, a6_5, a6_4, a6_3, a6_2, a6_1, a6_0]
          rw [← h1eq, ← hsz1]
          exact jvmHeap_set6_push jh1 (.boxedInt v.toUInt32) (.boxedUInt e)
        have hk6_get : k6.get? jh.objects.size = some (.objArray "java/lang/Object" #[.boxedInt 1, .null]) := by
          rw [hk6_eq]
          have hlt0 : jh.objects.size < ((jh.alloc (.objArray "java/lang/Object" #[.boxedInt 1, .null])).2).objects.size := by
            simp [Jvm.JvmHeap.alloc]
          rw [jvmHeap_get?_alloc_lt _ _ hlt0]
          exact jvmHeap_get?_alloc_self _ _
        exact ⟨_, by
          simp only [hbne, Bool.false_eq_true, ↓reduceIte]
          heap_step_blk (parseInt32AtProg cls)
          simp only [hl3, Jvm.JvmVal.asI32, show (!((0 : UInt32) == 0)) = false from rfl,
            Bool.false_eq_true, ↓reduceIte]
          heap_step_blk (parseInt32AtProg cls)
          simp only [hl7, Jvm.JvmVal.asI64]; rw [compareUnsigned64_sle_zero]
          simp only [hle, decide_true, ↓reduceIte]
          heap_step_blk (parseInt32AtProg cls)
          rw [runJvmResFast_invokestatic_step (stepStatic_uint32ToInt32 hcls)]
          heap_step_blk (parseInt32AtProg cls)
          rw [runJvmResFast_anewarray_obj (by decide), show (2 : UInt32).toNat = 2 from rfl]
          change runJvmResFast _ _ _ _ ⟨_, _, _, jh0, hp⟩ = _
          heap_step_blk (parseInt32AtProg cls)
          rw [runJvmResFast_aastore (idx := 0) h2_0 (by decide) (by decide)]
          change runJvmResFast _ _ _ _ ⟨_, _, _, jh1, hp⟩ = _
          heap_step_blk (parseInt32AtProg cls)
          rw [runJvmResFast_anewarray_obj (by decide), show (6 : UInt32).toNat = 6 from rfl]
          rw [hsz1]; change runJvmResFast _ _ _ _ ⟨_, _, _, k0, hp⟩ = _
          heap_step_blk (parseInt32AtProg cls)
          rw [runJvmResFast_aastore (idx := 0) hk0 (by decide) (by decide)]
          change runJvmResFast _ _ _ _ ⟨_, _, _, k1, hp⟩ = _
          heap_step_blk (parseInt32AtProg cls)
          rw [hl7, runJvmResFast_aastore (idx := 1) hk1 (by decide) (by simp [a6_1, a6_0])]
          change runJvmResFast _ _ _ _ ⟨_, _, _, k2, hp⟩ = _
          heap_step_blk (parseInt32AtProg cls)
          rw [runJvmResFast_aastore (idx := 2) hk2 (by decide) (by simp [a6_2, a6_1, a6_0])]
          change runJvmResFast _ _ _ _ ⟨_, _, _, k3, hp⟩ = _
          heap_step_blk (parseInt32AtProg cls)
          rw [runJvmResFast_aastore (idx := 3) hk3 (by decide) (by simp [a6_3, a6_2, a6_1, a6_0])]
          change runJvmResFast _ _ _ _ ⟨_, _, _, k4, hp⟩ = _
          heap_step_blk (parseInt32AtProg cls)
          rw [runJvmResFast_aastore (idx := 4) hk4 (by decide) (by simp [a6_4, a6_3, a6_2, a6_1, a6_0])]
          change runJvmResFast _ _ _ _ ⟨_, _, _, k5, hp⟩ = _
          heap_step_blk (parseInt32AtProg cls)
          rw [hl6, runJvmResFast_aastore (idx := 5) hk5 (by decide) (by simp [a6_5, a6_4, a6_3, a6_2, a6_1, a6_0])]
          change runJvmResFast _ _ _ _ ⟨_, _, _, k6, hp⟩ = _
          heap_step_blk (parseInt32AtProg cls)
          rw [runJvmResFast_aastore (idx := 1) hk6_get (by decide) (by decide)]
          rw [runJvmResFast_stepResHeapChunk 120]
          (conv => lhs; arg 1; jvm_whnf_blk)
          rw [afterResBlockChunk_done], by
          simp only [hbne, hle, Bool.false_eq_true, ↓reduceIte, Algorithm.uint32ToInt32]
          have hto : v.toUInt32.toInt32.toUInt32 = v.toUInt32 := rfl
          rw [hto, hk6_eq]
          exact jvmHeap_alloc2_set1 jh (.boxedInt v.toUInt32) (.boxedUInt e)⟩
      · exact ⟨_, by
          simp only [hbne, Bool.false_eq_true, ↓reduceIte]
          heap_step_blk (parseInt32AtProg cls)
          simp only [hl3, Jvm.JvmVal.asI32, show (!((0 : UInt32) == 0)) = false from rfl,
            Bool.false_eq_true, ↓reduceIte]
          heap_step_blk (parseInt32AtProg cls)
          simp only [hl7, Jvm.JvmVal.asI64]; rw [compareUnsigned64_sle_zero]
          simp only [hle, decide_false, Bool.false_eq_true, ↓reduceIte]
          heap_step_blk (parseInt32AtProg cls)
          rw [runJvmResFast_anewarray_obj (by decide), show (1 : UInt32).toNat = 1 from rfl]
          heap_step_blk (parseInt32AtProg cls)
          rw [runJvmResFast_aastore (idx := 0) ha0 (by decide) (by decide)]
          rw [runJvmResFast_stepResHeapChunk 120]
          (conv => lhs; arg 1; jvm_whnf_blk)
          rw [afterResBlockChunk_done], by
          simp only [hbne, hle, Bool.false_eq_true, ↓reduceIte]
          exact jvmHeap_set1_u32_0 jh _⟩
    · dsimp only [↓reduceIte] at hl3 ⊢
      by_cases hle : v ≤ 2147483648
      · let jh0 := (jh.alloc (.objArray "java/lang/Object" (Array.replicate 2 .null))).2
        have h2_0 : jh0.get? jh.objects.size = some (.objArray "java/lang/Object" (Array.replicate 2 .null)) :=
          jvmHeap_get?_alloc_self _ _
        let jh1 := jh0.set jh.objects.size (.objArray "java/lang/Object"
          ((Array.replicate 2 (JvmVal.null : Jvm.JvmVal AlgExt)).set 0 (.boxedInt 1) (by decide)))
        have h1eq : jh1 = (jh.alloc (.objArray "java/lang/Object" #[.boxedInt 1, .null])).2 := jvmHeap_set_push_2_0 jh
        have hsz1 : jh1.objects.size = jh.objects.size + 1 := by rw [h1eq]; simp [Jvm.JvmHeap.alloc]
        let outV : UInt32 := 0 - v.toUInt32
        let a6_0 : Array (Jvm.JvmVal AlgExt) := Array.replicate 6 .null
        let a6_1 : Array (Jvm.JvmVal AlgExt) := a6_0.set 0 (.boxedInt 0) (by simp [a6_0])
        let a6_2 : Array (Jvm.JvmVal AlgExt) := a6_1.set 1 (.boxedInt outV) (by simp [a6_1, a6_0])
        let a6_3 : Array (Jvm.JvmVal AlgExt) := a6_2.set 2 .null (by simp [a6_2, a6_1, a6_0])
        let a6_4 : Array (Jvm.JvmVal AlgExt) := a6_3.set 3 .null (by simp [a6_3, a6_2, a6_1, a6_0])
        let a6_5 : Array (Jvm.JvmVal AlgExt) := a6_4.set 4 .null (by simp [a6_4, a6_3, a6_2, a6_1, a6_0])
        let a6_6 : Array (Jvm.JvmVal AlgExt) := a6_5.set 5 (.boxedUInt e) (by simp [a6_5, a6_4, a6_3, a6_2, a6_1, a6_0])
        let k0 := (jh1.alloc (.objArray "java/lang/Object" a6_0)).2
        have hk0 : k0.get? (jh.objects.size + 1) = some (.objArray "java/lang/Object" a6_0) := by
          simpa [k0, hsz1] using jvmHeap_get?_alloc_self jh1 (.objArray "java/lang/Object" a6_0)
        let k1 := k0.set (jh.objects.size + 1) (.objArray "java/lang/Object" a6_1)
        have hk1 : k1.get? (jh.objects.size + 1) = some (.objArray "java/lang/Object" a6_1) := jvmHeap_get?_set_self hk0
        let k2 := k1.set (jh.objects.size + 1) (.objArray "java/lang/Object" a6_2)
        have hk2 : k2.get? (jh.objects.size + 1) = some (.objArray "java/lang/Object" a6_2) := jvmHeap_get?_set_self hk1
        let k3 := k2.set (jh.objects.size + 1) (.objArray "java/lang/Object" a6_3)
        have hk3 : k3.get? (jh.objects.size + 1) = some (.objArray "java/lang/Object" a6_3) := jvmHeap_get?_set_self hk2
        let k4 := k3.set (jh.objects.size + 1) (.objArray "java/lang/Object" a6_4)
        have hk4 : k4.get? (jh.objects.size + 1) = some (.objArray "java/lang/Object" a6_4) := jvmHeap_get?_set_self hk3
        let k5 := k4.set (jh.objects.size + 1) (.objArray "java/lang/Object" a6_5)
        have hk5 : k5.get? (jh.objects.size + 1) = some (.objArray "java/lang/Object" a6_5) := jvmHeap_get?_set_self hk4
        let k6 := k5.set (jh.objects.size + 1) (.objArray "java/lang/Object" a6_6)
        have hk6_eq : k6 = ((jh.alloc (.objArray "java/lang/Object" #[.boxedInt 1, .null])).2.alloc
            (.objArray "java/lang/Object" #[.boxedInt 0, .boxedInt outV, .null, .null, .null, .boxedUInt e])).2 := by
          dsimp only [k6, k5, k4, k3, k2, k1, k0, a6_6, a6_5, a6_4, a6_3, a6_2, a6_1, a6_0]
          rw [← h1eq, ← hsz1]
          exact jvmHeap_set6_push jh1 (.boxedInt outV) (.boxedUInt e)
        have hk6_get : k6.get? jh.objects.size = some (.objArray "java/lang/Object" #[.boxedInt 1, .null]) := by
          rw [hk6_eq]
          have hlt0 : jh.objects.size < ((jh.alloc (.objArray "java/lang/Object" #[.boxedInt 1, .null])).2).objects.size := by
            simp [Jvm.JvmHeap.alloc]
          rw [jvmHeap_get?_alloc_lt _ _ hlt0]
          exact jvmHeap_get?_alloc_self _ _
        exact ⟨_, by
          simp only [hbne, Bool.false_eq_true, ↓reduceIte]
          heap_step_blk (parseInt32AtProg cls)
          simp only [hl3, Jvm.JvmVal.asI32, show (!((1 : UInt32) == 0)) = true from rfl, ↓reduceIte]
          heap_step_blk (parseInt32AtProg cls)
          simp only [hl7, Jvm.JvmVal.asI64]; rw [compareUnsigned64_sle_zero]
          simp only [hle, decide_true, ↓reduceIte]
          heap_step_blk (parseInt32AtProg cls)
          rw [runJvmResFast_anewarray_obj (by decide), show (2 : UInt32).toNat = 2 from rfl]
          change runJvmResFast _ _ _ _ ⟨_, _, _, jh0, hp⟩ = _
          heap_step_blk (parseInt32AtProg cls)
          rw [runJvmResFast_aastore (idx := 0) h2_0 (by decide) (by decide)]
          change runJvmResFast _ _ _ _ ⟨_, _, _, jh1, hp⟩ = _
          heap_step_blk (parseInt32AtProg cls)
          rw [runJvmResFast_anewarray_obj (by decide), show (6 : UInt32).toNat = 6 from rfl]
          rw [hsz1]; change runJvmResFast _ _ _ _ ⟨_, _, _, k0, hp⟩ = _
          heap_step_blk (parseInt32AtProg cls)
          rw [runJvmResFast_aastore (idx := 0) hk0 (by decide) (by decide)]
          change runJvmResFast _ _ _ _ ⟨_, _, _, k1, hp⟩ = _
          heap_step_blk (parseInt32AtProg cls)
          rw [hl7, runJvmResFast_aastore (idx := 1) hk1 (by decide) (by simp [a6_1, a6_0])]
          change runJvmResFast _ _ _ _ ⟨_, _, _, k2, hp⟩ = _
          heap_step_blk (parseInt32AtProg cls)
          rw [runJvmResFast_aastore (idx := 2) hk2 (by decide) (by simp [a6_2, a6_1, a6_0])]
          change runJvmResFast _ _ _ _ ⟨_, _, _, k3, hp⟩ = _
          heap_step_blk (parseInt32AtProg cls)
          rw [runJvmResFast_aastore (idx := 3) hk3 (by decide) (by simp [a6_3, a6_2, a6_1, a6_0])]
          change runJvmResFast _ _ _ _ ⟨_, _, _, k4, hp⟩ = _
          heap_step_blk (parseInt32AtProg cls)
          rw [runJvmResFast_aastore (idx := 4) hk4 (by decide) (by simp [a6_4, a6_3, a6_2, a6_1, a6_0])]
          change runJvmResFast _ _ _ _ ⟨_, _, _, k5, hp⟩ = _
          heap_step_blk (parseInt32AtProg cls)
          rw [hl6, runJvmResFast_aastore (idx := 5) hk5 (by decide) (by simp [a6_5, a6_4, a6_3, a6_2, a6_1, a6_0])]
          change runJvmResFast _ _ _ _ ⟨_, _, _, k6, hp⟩ = _
          heap_step_blk (parseInt32AtProg cls)
          rw [runJvmResFast_aastore (idx := 1) hk6_get (by decide) (by decide)]
          rw [runJvmResFast_stepResHeapChunk 120]
          (conv => lhs; arg 1; jvm_whnf_blk)
          rw [afterResBlockChunk_done], by
          simp only [hbne, hle, Bool.false_eq_true, ↓reduceIte]
          rw [u32_zero_sub_toInt32 v.toUInt32, hk6_eq]
          exact jvmHeap_alloc2_set1 jh (.boxedInt outV) (.boxedUInt e)⟩
      · exact ⟨_, by
          simp only [hbne, Bool.false_eq_true, ↓reduceIte]
          heap_step_blk (parseInt32AtProg cls)
          simp only [hl3, Jvm.JvmVal.asI32, show (!((1 : UInt32) == 0)) = true from rfl, ↓reduceIte]
          heap_step_blk (parseInt32AtProg cls)
          simp only [hl7, Jvm.JvmVal.asI64]; rw [compareUnsigned64_sle_zero]
          simp only [hle, decide_false, Bool.false_eq_true, ↓reduceIte]
          heap_step_blk (parseInt32AtProg cls)
          rw [runJvmResFast_anewarray_obj (by decide), show (1 : UInt32).toNat = 1 from rfl]
          heap_step_blk (parseInt32AtProg cls)
          rw [runJvmResFast_aastore (idx := 0) ha0 (by decide) (by decide)]
          rw [runJvmResFast_stepResHeapChunk 120]
          (conv => lhs; arg 1; jvm_whnf_blk)
          rw [afterResBlockChunk_done], by
          simp only [hbne, hle, Bool.false_eq_true, ↓reduceIte]
          exact jvmHeap_set1_u32_0 jh _⟩

private theorem parseInt32At_pc37 (cls : String)
    (hcls : cls = "Life105LeanKt" ∨ cls = "Life106LeanKt" ∨ cls = "MacroCellLeanKt" ∨
      cls = "PlaintextLeanKt" ∨ cls = "RleLeanKt")
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (addr : Nat) (elems : Array UInt8)
    (locs : Nat → JvmVal) (limit start : UInt32) (isNeg : Bool) (fuel : Nat)
    (hget : jh.get? addr = some (.byteArray elems))
    (hl3 : locs 3 = .i32 (if isNeg then 1 else 0)) (hl4 : locs 4 = .i32 start)
    (hfuel : 120 ≤ fuel) :
    let r := Algorithm.scanDigits ⟨elems⟩ limit start 0
    let res : Option Algorithm.ParsedInt32 :=
      if r.1 == start then none
      else if isNeg then
        if r.2 ≤ 2147483648 then some ⟨(0 : Int32) - r.2.toUInt32.toInt32, r.1⟩ else none
      else if r.2 ≤ 2147483647 then some ⟨Algorithm.uint32ToInt32 r.2.toUInt32, r.1⟩ else none
    let jhAfter := match res with
      | none => (jh.alloc (.objArray "java/lang/Object" #[.boxedInt 0])).2
      | some p =>
        { objects := (jh.objects.push (.objArray "java/lang/Object" #[.boxedInt 1, .heapRef (jh.objects.size + 1)])).push
            (.objArray "java/lang/Object"
              #[.boxedInt 0, .boxedInt p.val.toUInt32, .null, .null, .null, .boxedUInt p.next]),
          statics := jh.statics }
    ∃ st', runJvmResFast fuel (parseInt32AtProg cls) 37 ((parseInt32AtProg cls).drop 37)
        ⟨37, [.i64 0, .i32 start, .i32 limit, .heapRef addr], locs, jh, hp⟩ =
      some (.heapRef jh.objects.size, st') ∧ st'.jvmHeap = jhAfter := by
  let r := Algorithm.scanDigits ⟨elems⟩ limit start 0
  let locs49 := setLocal (setLocal (setLocal locs 5 (.pair (.boxedUInt r.1) (.boxedULong r.2)))
    6 (.i32 r.1)) 7 (.i64 r.2)
  obtain ⟨fk, rfl⟩ : ∃ fk, fuel = fk + 120 := ⟨fuel - 120, (Nat.sub_add_cancel hfuel).symm⟩
  obtain ⟨st', hrun, hst⟩ := parseInt32At_pc52 cls hcls jh hp locs49 start r.1 r.2 isNeg (fk + 105) (by omega)
    (by simp [locs49, setLocal, hl3]) (by simp [locs49, setLocal, hl4]) rfl rfl
  refine ⟨st', ?_, hst⟩
  rw [show (parseInt32AtProg cls).drop 37 =
    .invokestatic cls "f_Algorithm_scanDigits-G4XTHLI" "([BIIJ)Lkotlin/Pair;" :: (parseInt32AtProg cls).drop 38 from rfl]
  rw [runJvmResFast_invokestatic_step (stepStatic_scanDigits_heap hcls hget)]
  heap_step_blk (parseInt32AtProg cls)
  rw [runJvmResFast_checkcast_boxedUInt (Or.inl rfl)]
  heap_step_blk (parseInt32AtProg cls)
  rw [runJvmResFast_checkcast_boxedULong (Or.inl rfl)]
  heap_step_blk (parseInt32AtProg cls)
  simp only [hl4, Jvm.JvmVal.asI32]
  exact hrun

private theorem parseInt32At_spec (cls : String)
    (hcls : cls = "Life105LeanKt" ∨ cls = "Life106LeanKt" ∨ cls = "MacroCellLeanKt" ∨
      cls = "PlaintextLeanKt" ∨ cls = "RleLeanKt")
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (addr : Nat) (elems : Array UInt8)
    (pos limit : UInt32) (hget : jh.get? addr = some (.byteArray elems))
    (hlim : limit.toNat ≤ elems.size) (hlim31 : limit.toNat < 2 ^ 31) :
    let res := Algorithm.parseInt32At ⟨elems⟩ pos limit
    let jhAfter := match res with
      | none => (jh.alloc (.objArray "java/lang/Object" #[.boxedInt 0])).2
      | some p =>
        { objects := (jh.objects.push (.objArray "java/lang/Object" #[.boxedInt 1, .heapRef (jh.objects.size + 1)])).push
            (.objArray "java/lang/Object"
              #[.boxedInt 0, .boxedInt p.val.toUInt32, .null, .null, .null, .boxedUInt p.next]),
          statics := jh.statics }
    ∃ st', runJvmRes 160 (parseInt32AtProg cls)
      ⟨0, [], setLocal (setLocal (setLocal (fun _ => .null) 0 (.heapRef addr)) 1 (.i32 pos)) 2 (.i32 limit), jh, hp⟩ =
      some (.heapRef jh.objects.size, st') ∧ st'.jvmHeap = jhAfter := by
  dsimp only; rw [Algorithm.parseInt32At]
  by_cases hlt : pos < limit
  · have hlt_nat : pos.toNat < limit.toNat := UInt32.lt_iff_toNat_lt.mp hlt
    have hp_lt : pos.toNat < elems.size := by omega
    have hp_slt : pos.toBitVec.slt 0#32 = false := u32_slt_zero_of_lt_2_31 (by omega)
    let b := elems[pos.toNat]'hp_lt
    have hb_eq : b = (⟨elems⟩ : ByteArray).get! pos.toNat := getElem_eq_byteArray_getBang elems hp_lt
    have hcu : (if pos == limit then (0 : UInt32) else if pos < limit then 4294967295 else 1).toBitVec.slt 0#32 =
        true := by
      rw [compareUnsigned_slt_zero]; exact decide_eq_true hlt
    by_cases h45 : elems[pos.toNat] == 45
    · have his : (decide (pos < limit) && ((⟨elems⟩ : ByteArray).get! pos.toNat == 45)) = true := by
        simp [hlt, ← hb_eq, b, h45]
      let locs33 : Nat → JvmVal := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
        (fun _ => (.null : JvmVal)) 0 (.heapRef addr)) 1 (.i32 pos)) 2 (.i32 limit)) 3 (.i32 0)) 4 (.i32 0))
        5 (.i32 (pos + 1))) 3 (.i32 1) |> fun f => setLocal f 4 (.i32 (pos + 1))
      obtain ⟨st', hrun, hst⟩ := parseInt32At_pc37 cls hcls jh hp addr elems locs33 limit (pos + 1) true 133
        hget rfl rfl (by decide)
      exact ⟨st', by
        apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
        split_res_fuel 40; heap_step_blk (parseInt32AtProg cls)
        rw [hcu]; simp only [↓reduceIte]
        heap_step_blk (parseInt32AtProg cls)
        rw [runJvmResFast_baload hget hp_slt hp_lt]
        heap_step_blk (parseInt32AtProg cls)
        rw [u8_signExt_eq_45, h45]; simp only [↓reduceIte]
        heap_step_blk (parseInt32AtProg cls)
        exact hrun, by
        simp only [his, ↓reduceIte]; exact hst⟩
    · have h45f : (elems[pos.toNat] == 45) = false := Bool.eq_false_iff.mpr h45
      have his : (decide (pos < limit) && ((⟨elems⟩ : ByteArray).get! pos.toNat == 45)) = false := by
        simp [← hb_eq, b, h45f]
      let locs33 : Nat → JvmVal := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
        (fun _ => (.null : JvmVal)) 0 (.heapRef addr)) 1 (.i32 pos)) 2 (.i32 limit)) 3 (.i32 0)) 4 (.i32 0))
        3 (.i32 0) |> fun f => setLocal f 4 (.i32 pos)
      obtain ⟨st', hrun, hst⟩ := parseInt32At_pc37 cls hcls jh hp addr elems locs33 limit pos false 137
        hget rfl rfl (by decide)
      exact ⟨st', by
        apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
        split_res_fuel 40; heap_step_blk (parseInt32AtProg cls)
        rw [hcu]; simp only [↓reduceIte]
        heap_step_blk (parseInt32AtProg cls)
        rw [runJvmResFast_baload hget hp_slt hp_lt]
        heap_step_blk (parseInt32AtProg cls)
        rw [u8_signExt_eq_45, h45f]; simp only [Bool.false_eq_true, ↓reduceIte]
        heap_step_blk (parseInt32AtProg cls)
        exact hrun, by
        simp only [his, Bool.false_eq_true, ↓reduceIte]; exact hst⟩
  · have his : (decide (pos < limit) && ((⟨elems⟩ : ByteArray).get! pos.toNat == 45)) = false := by
      simp [hlt]
    have hcu : (if pos == limit then (0 : UInt32) else if pos < limit then 4294967295 else 1).toBitVec.slt 0#32 =
        false := by
      rw [compareUnsigned_slt_zero]; exact decide_eq_false hlt
    let locs33 : Nat → JvmVal := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
      (fun _ => (.null : JvmVal)) 0 (.heapRef addr)) 1 (.i32 pos)) 2 (.i32 limit)) 3 (.i32 0)) 4 (.i32 0))
      3 (.i32 0) |> fun f => setLocal f 4 (.i32 pos)
    obtain ⟨st', hrun, hst⟩ := parseInt32At_pc37 cls hcls jh hp addr elems locs33 limit pos false 143
      hget rfl rfl (by decide)
    exact ⟨st', by
      apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
      split_res_fuel 40; heap_step_blk (parseInt32AtProg cls)
      rw [hcu]; simp only [Bool.false_eq_true, ↓reduceIte]
      heap_step_blk (parseInt32AtProg cls)
      exact hrun, by
      simp only [his, Bool.false_eq_true, ↓reduceIte]; exact hst⟩

theorem parseInt32At_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (addr : Nat) (elems : Array UInt8)
    (pos limit : UInt32) (hget : jh.get? addr = some (.byteArray elems))
    (hlim : limit.toNat ≤ elems.size) (hlim31 : limit.toNat < 2 ^ 31) :
    let res := Algorithm.parseInt32At ⟨elems⟩ pos limit
    let jhAfter := match res with
      | none => (jh.alloc (.objArray "java/lang/Object" #[.boxedInt 0])).2
      | some p =>
        { objects := (jh.objects.push (.objArray "java/lang/Object" #[.boxedInt 1, .heapRef (jh.objects.size + 1)])).push
            (.objArray "java/lang/Object"
              #[.boxedInt 0, .boxedInt p.val.toUInt32, .null, .null, .null, .boxedUInt p.next]),
          statics := jh.statics }
    ∃ st', runJvmRes 160 f_Algorithm_parseInt32At_prog
      ⟨0, [], setLocal (setLocal (setLocal (fun _ => .null) 0 (.heapRef addr)) 1 (.i32 pos)) 2 (.i32 limit), jh, hp⟩ =
      some (.heapRef jh.objects.size, st') ∧ st'.jvmHeap = jhAfter := by
  rw [show f_Algorithm_parseInt32At_prog = parseInt32AtProg "Life105LeanKt" from rfl]
  exact parseInt32At_spec "Life105LeanKt" (by simp) jh hp addr elems pos limit hget hlim hlim31

theorem parseInt32At_1_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (addr : Nat) (elems : Array UInt8)
    (pos limit : UInt32) (hget : jh.get? addr = some (.byteArray elems))
    (hlim : limit.toNat ≤ elems.size) (hlim31 : limit.toNat < 2 ^ 31) :
    let res := Algorithm.parseInt32At ⟨elems⟩ pos limit
    let jhAfter := match res with
      | none => (jh.alloc (.objArray "java/lang/Object" #[.boxedInt 0])).2
      | some p =>
        { objects := (jh.objects.push (.objArray "java/lang/Object" #[.boxedInt 1, .heapRef (jh.objects.size + 1)])).push
            (.objArray "java/lang/Object"
              #[.boxedInt 0, .boxedInt p.val.toUInt32, .null, .null, .null, .boxedUInt p.next]),
          statics := jh.statics }
    ∃ st', runJvmRes 160 f_Algorithm_parseInt32At_1_prog
      ⟨0, [], setLocal (setLocal (setLocal (fun _ => .null) 0 (.heapRef addr)) 1 (.i32 pos)) 2 (.i32 limit), jh, hp⟩ =
      some (.heapRef jh.objects.size, st') ∧ st'.jvmHeap = jhAfter := by
  rw [show f_Algorithm_parseInt32At_1_prog = parseInt32AtProg "Life106LeanKt" from rfl]
  exact parseInt32At_spec "Life106LeanKt" (by simp) jh hp addr elems pos limit hget hlim hlim31

theorem parseInt32At_2_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (addr : Nat) (elems : Array UInt8)
    (pos limit : UInt32) (hget : jh.get? addr = some (.byteArray elems))
    (hlim : limit.toNat ≤ elems.size) (hlim31 : limit.toNat < 2 ^ 31) :
    let res := Algorithm.parseInt32At ⟨elems⟩ pos limit
    let jhAfter := match res with
      | none => (jh.alloc (.objArray "java/lang/Object" #[.boxedInt 0])).2
      | some p =>
        { objects := (jh.objects.push (.objArray "java/lang/Object" #[.boxedInt 1, .heapRef (jh.objects.size + 1)])).push
            (.objArray "java/lang/Object"
              #[.boxedInt 0, .boxedInt p.val.toUInt32, .null, .null, .null, .boxedUInt p.next]),
          statics := jh.statics }
    ∃ st', runJvmRes 160 f_Algorithm_parseInt32At_2_prog
      ⟨0, [], setLocal (setLocal (setLocal (fun _ => .null) 0 (.heapRef addr)) 1 (.i32 pos)) 2 (.i32 limit), jh, hp⟩ =
      some (.heapRef jh.objects.size, st') ∧ st'.jvmHeap = jhAfter := by
  rw [show f_Algorithm_parseInt32At_2_prog = parseInt32AtProg "RleLeanKt" from rfl]
  exact parseInt32At_spec "RleLeanKt" (by simp) jh hp addr elems pos limit hget hlim hlim31

end Algorithm.JvmVerification
