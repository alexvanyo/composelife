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

import Jvm.Semantics
import Jvm.FastExec

namespace Jvm

/-! ### Generic Arithmetic, Option, Ite, Heap, and String Lemmas -/

theorem nat_add_eq_add (a b : Nat) : Nat.add a b = a + b := rfl

theorem option_map_ite {α β : Type} (f : α → β) (c : Prop) [Decidable c] (t e : Option α) :
    (if c then t else e).map f = if c then t.map f else e.map f := by
  split <;> rfl

theorem option_map_some' {α β : Type} (f : α → β) (x : α) :
    Option.map f (some x) = some (f x) := rfl

theorem option_map_none' {α β : Type} (f : α → β) :
    Option.map f none = none := rfl

theorem ite_bool_eq_true_left {α : Type} {b : Bool} (h : b = true) (t e : α) :
    (if b = true then t else e) = t := by
  simp [h]

theorem ite_bool_eq_true_right {α : Type} {b : Bool} (h : b = false) (t e : α) :
    (if b = true then t else e) = e := by
  simp [h]

theorem eq_of_ite_branches {α : Type} {c : Prop} [Decidable c] {t e rhs : α}
    (ht : c → t = rhs) (he : ¬c → e = rhs) : (if c then t else e) = rhs := by
  by_cases h : c <;> simp [h, ht, he]

theorem ui32_beq_0_0 : ((0 : UInt32) == 0) = true := rfl
theorem ui32_beq_1_0 : ((1 : UInt32) == 0) = false := rfl

theorem beq_false_of_ne' {α : Type} [BEq α] [LawfulBEq α] {a b : α} (h : a ≠ b) :
    (a == b) = false :=
  beq_false_of_ne h

theorem bne_true_of_ne' {α : Type} [BEq α] [LawfulBEq α] {a b : α} (h : a ≠ b) :
    (a != b) = true := by
  simp [bne, beq_false_of_ne h]

/-! ### Polymorphic `JvmHeap` Lemmas -/

theorem jvmHeap_get?_some_lt {Ext : Type} {h : JvmHeap Ext} {addr : Nat} {obj : HeapObj Ext}
    (hg : h.get? addr = some obj) : addr < h.objects.size := by
  simp only [JvmHeap.get?] at hg
  exact (Array.getElem?_eq_some_iff.mp hg).1

theorem jvmHeap_get?_alloc_self {Ext : Type} (h : JvmHeap Ext) (obj : HeapObj Ext) :
    (h.alloc obj).2.get? h.objects.size = some obj := by
  simp [JvmHeap.alloc, JvmHeap.get?]

theorem jvmHeap_get?_alloc_old {Ext : Type} (h : JvmHeap Ext) (obj : HeapObj Ext)
    {a : Nat} (hlt : a < h.objects.size) :
    (h.alloc obj).2.get? a = h.get? a := by
  simp [JvmHeap.alloc, JvmHeap.get?, Array.getElem?_push, hlt, Nat.ne_of_lt hlt]

theorem jvmHeap_alloc_fst_lt {Ext : Type} (h : JvmHeap Ext) (obj : HeapObj Ext) :
    (h.alloc obj).1 < (h.alloc obj).2.objects.size := by
  simp [JvmHeap.alloc]

theorem jvmHeap_get?_set_self {Ext : Type} {h : JvmHeap Ext} {a : Nat} {v w : HeapObj Ext}
    (hg : h.get? a = some v) : (h.set a w).get? a = some w := by
  have hlt : a < h.objects.size := jvmHeap_get?_some_lt hg
  simp [JvmHeap.set, JvmHeap.get?, hlt]

theorem jvmHeap_get?_set_ne {Ext : Type} (h : JvmHeap Ext) {a b : Nat}
    (obj : HeapObj Ext) (hne : a ≠ b) :
    (h.set b obj).get? a = h.get? a := by
  simp only [JvmHeap.set, JvmHeap.get?]
  split
  · simp [Array.getElem?_set_ne, Ne.symm hne]
  · rfl

/-! ### JVM BitVec, UInt8/UInt32/Int32/UInt64, Float, and String Helpers -/

theorem int32_toUInt32_toBitVec (x : Int32) : x.toUInt32.toBitVec = x.toBitVec := by
  cases x; rfl

theorem int32_slt_zero (x : Int32) :
    (0#32).slt x.toUInt32.toBitVec = decide ((0 : Int32) < x) := by
  rw [int32_toUInt32_toBitVec]
  by_cases h : (0 : Int32) < x
  · have : (0#32).slt x.toBitVec = true := by simpa [Int32.lt_iff_toBitVec_slt] using h
    simp [h, this]
  · have : (0#32).slt x.toBitVec = false := by
      rw [Bool.eq_false_iff]; intro hslt
      exact h (by simpa [Int32.lt_iff_toBitVec_slt] using hslt)
    simp [h, this]

theorem int32_toUInt32_add (x y : Int32) :
    x.toUInt32 + y.toUInt32 = (x + y).toUInt32 := by
  rcases x with ⟨⟨a⟩⟩; rcases y with ⟨⟨b⟩⟩; rfl

theorem int32_toUInt32_sub (x y : Int32) :
    x.toUInt32 - y.toUInt32 = (x - y).toUInt32 := by
  rcases x with ⟨⟨a⟩⟩; rcases y with ⟨⟨b⟩⟩; rfl

theorem int32_beq_toUInt32 (x y : Int32) :
    (x.toUInt32 == y.toUInt32) = (x == y) := by
  by_cases h : x = y
  · subst h; simp
  · have hne : x.toUInt32 ≠ y.toUInt32 := by
      intro heq; apply h; cases x; cases y; cases heq; rfl
    rw [beq_false_of_ne hne, beq_false_of_ne h]

theorem ui32_slt_zero_of_lt (n : Nat) (hlt : n < 2 ^ 31) :
    (UInt32.ofNat n).toBitVec.slt 0#32 = false := by
  rw [BitVec.slt_eq_ult, BitVec.msb_zero]
  have hm : (UInt32.ofNat n).toBitVec.msb = false := by
    rw [BitVec.msb_eq_toNat]
    have ht : (UInt32.ofNat n).toBitVec.toNat = n := by
      change (UInt32.ofNat n).toNat = n
      exact Nat.mod_eq_of_lt (by omega)
    rw [ht]
    exact decide_eq_false (by omega)
  simp [hm, BitVec.ult]

theorem ui32_ofNat_toNat_of_lt (n : Nat) (hlt : n < 2 ^ 31) :
    (UInt32.ofNat n).toNat = n :=
  Nat.mod_eq_of_lt (by omega)

theorem u32_slt_zero_of_lt_2_31 {x : UInt32} (hx : x.toNat < 2 ^ 31) :
    x.toBitVec.slt 0#32 = false := by
  simp only [BitVec.slt, BitVec.toInt_zero]
  have h1 : x.toBitVec.toInt = ↑x.toNat := by
    rw [BitVec.toInt_eq_toNat_cond]
    split
    · rfl
    · simp only [UInt32.toNat] at hx; omega
  rw [h1]
  exact decide_eq_false (by omega)

theorem u32_slt_zero_of_lt {a b : UInt32} (hab : a < b) (hb : b.toNat ≤ 2 ^ 31) :
    a.toBitVec.slt 0#32 = false :=
  u32_slt_zero_of_lt_2_31 (Nat.lt_of_lt_of_le (UInt32.lt_iff_toNat_lt.mp hab) hb)

theorem u32_toInt_eq_toNat {x : UInt32} (hx : x.toNat < 2 ^ 31) :
    x.toBitVec.toInt = ↑x.toNat := by
  rw [BitVec.toInt_eq_toNat_cond]
  split
  · rfl
  · simp only [UInt32.toNat] at hx; omega

theorem ui32_add1_toNat {a b : UInt32} (h : a < b) :
    (a + 1).toNat = a.toNat + 1 := by
  have h1 := UInt32.lt_iff_toNat_lt.mp h
  have h2 := UInt32.toNat_lt b
  rw [UInt32.toNat_add, UInt32.toNat_one]
  exact Nat.mod_eq_of_lt (by omega)

theorem u32_shl1_add1_eq {n : Nat} :
    (UInt32.ofNat n <<< 1) + 1 = 2 * UInt32.ofNat n + 1 := by
  refine congrArg (· + 1) ?_
  apply UInt32.eq_of_toBitVec_eq; apply BitVec.eq_of_toNat_eq
  change (UInt32.ofNat n <<< 1).toNat = (2 * UInt32.ofNat n).toNat
  rw [UInt32.toNat_shiftLeft, UInt32.toNat_mul]
  rw [show (1 : UInt32).toNat % 32 = 1 from by decide]
  rw [show (2 : UInt32).toNat = 2 from by decide]
  rw [Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_comm]

theorem ui32_toNat_add_1 (a : UInt32) : (a + 1).toNat = (a.toNat + 1) % 4294967296 :=
  UInt32.toNat_add a 1

theorem ui32_toNat_add_2 (a : UInt32) : (a + 2).toNat = (a.toNat + 2) % 4294967296 :=
  UInt32.toNat_add a 2

theorem ui32_toNat_add_3 (a : UInt32) : (a + 3).toNat = (a.toNat + 3) % 4294967296 :=
  UInt32.toNat_add a 3

theorem ui32_toNat_add_4 (a : UInt32) : (a + 4).toNat = (a.toNat + 4) % 4294967296 :=
  UInt32.toNat_add a 4

theorem lcmp_eq_zero (a b : UInt64) (c : Bool) :
    ((if (a == b) = true then (0 : UInt32) else if c = true then 4294967295 else 1) = 0) ↔ a = b := by
  by_cases h : a = b <;> cases c <;> simp [h]

private def allU8From (p : UInt8 → Bool) (lo : Nat) : Nat → Bool
  | 0 => p (UInt8.ofNat lo)
  | d + 1 => allU8From p lo d && allU8From p (lo + (1 <<< d)) d

private theorem allU8From_sound (p : UInt8 → Bool) (lo d : Nat) (h : allU8From p lo d = true)
    (k : Nat) (hk : k < 1 <<< d) : p (UInt8.ofNat (lo + k)) = true := by
  induction d generalizing lo k with
  | zero =>
    have hk0 : k = 0 := by omega
    subst hk0
    simpa [allU8From] using h
  | succ d ih =>
    simp only [allU8From, Bool.and_eq_true] at h
    have hpow : 1 <<< (d + 1) = (1 <<< d) + (1 <<< d) := by
      simp [Nat.shiftLeft_eq, Nat.pow_succ, Nat.mul_two]
    by_cases hk' : k < 1 <<< d
    · exact ih lo h.1 k hk'
    · have hk2 : k - (1 <<< d) < 1 <<< d := by omega
      have hadd : lo + k = lo + (1 <<< d) + (k - (1 <<< d)) := by omega
      rw [hadd]
      exact ih (lo + (1 <<< d)) h.2 (k - (1 <<< d)) hk2

private theorem ui8_forall_bool {p : UInt8 → Bool} (h : allU8From p 0 8 = true) (b : UInt8) :
    p b = true := by
  have hb := allU8From_sound p 0 8 h b.toNat b.toBitVec.isLt
  simpa [UInt8.ofNat_toNat] using hb

private local instance {p : UInt8 → Prop} [DecidablePred p] : Decidable (∀ b : UInt8, p b) :=
  decidable_of_iff (allU8From (fun b => decide (p b)) 0 8 = true)
    ⟨fun h b => of_decide_eq_true (ui8_forall_bool h b),
     fun h => by
       have hall : ∀ lo d, (∀ k < 1 <<< d, decide (p (UInt8.ofNat (lo + k))) = true) →
           allU8From (fun b => decide (p b)) lo d = true := by
         intro lo d hspec
         induction d generalizing lo with
         | zero => exact hspec 0 (by omega)
         | succ d ih =>
           simp only [allU8From, Bool.and_eq_true]
           refine ⟨ih lo (fun k hk => hspec k (by omega)),
                   ih (lo + (1 <<< d)) (fun k hk => ?_)⟩
           simpa [Nat.add_assoc] using hspec ((1 <<< d) + k) (by
             have hpow : 1 <<< (d + 1) = (1 <<< d) + (1 <<< d) := by
               simp [Nat.shiftLeft_eq, Nat.pow_succ, Nat.mul_two]
             omega)
       exact hall 0 8 (fun k _ => by simpa [Nat.zero_add] using decide_eq_true (h (UInt8.ofNat k)))⟩

theorem u8_sext_eq_zero (b : UInt8) : (b.toInt8.toInt32.toUInt32 = 0) ↔ b = 0 := by revert b; decide
theorem u8_sext_eq_one (b : UInt8) : (b.toInt8.toInt32.toUInt32 = 1) ↔ b = 1 := by revert b; decide
theorem u8_sext_eq_five (b : UInt8) : (b.toInt8.toInt32.toUInt32 = 5) ↔ b = 5 := by revert b; decide
theorem u8_sext_eq_six (b : UInt8) : (b.toInt8.toInt32.toUInt32 = 6) ↔ b = 6 := by revert b; decide
theorem u8_sext_eq_seven (b : UInt8) : (b.toInt8.toInt32.toUInt32 = 7) ↔ b = 7 := by revert b; decide

theorem u8_sub1_u32_jvm (b : UInt8) :
    ({ toBitVec := BitVec.setWidth 8 (BitVec.signExtend 32
        (BitVec.setWidth 8 ((BitVec.setWidth 32 b.toBitVec &&& 255#32) - 1#32))) } : UInt8) = b - 1 := by
  revert b; decide

theorem u8_sub1_sext_jvm (b : UInt8) :
    ({ toBitVec := BitVec.setWidth 8 (BitVec.signExtend 32
        (BitVec.setWidth 8 ((b.toInt8.toInt32.toUInt32.toBitVec &&& 255#32) - 1#32))) } : UInt8) = b - 1 := by
  revert b; decide

theorem u8_sub2_sext_jvm (b : UInt8) :
    ({ toBitVec := BitVec.setWidth 8 (BitVec.signExtend 32
        (BitVec.setWidth 8 ((b.toInt8.toInt32.toUInt32.toBitVec &&& 255#32) - 2#32))) } : UInt8) = b - 2 := by
  revert b; decide

theorem u8_add1_sext_jvm (b : UInt8) :
    ({ toBitVec := BitVec.setWidth 8 (BitVec.signExtend 32
        (BitVec.setWidth 8 ((b.toInt8.toInt32.toUInt32.toBitVec &&& 255#32) + 1#32))) } : UInt8) = b + 1 := by
  revert b; decide

theorem u8_add2_sext_jvm (b : UInt8) :
    ({ toBitVec := BitVec.setWidth 8 (BitVec.signExtend 32
        (BitVec.setWidth 8 ((b.toInt8.toInt32.toUInt32.toBitVec &&& 255#32) + 2#32))) } : UInt8) = b + 2 := by
  revert b; decide

theorem u8_and255_sext_jvm (b : UInt8) :
    (b.toInt8.toInt32.toUInt32 &&& 255) = b.toUInt32 := by
  revert b; decide

theorem u8_sub1_and255_u32 (b : UInt8) :
    UInt32.ofBitVec ((b.toInt8.toInt32.toUInt32.toBitVec &&& 255#32) - 1#32) = b.toUInt32 - 1 := by
  revert b; decide

theorem u8_sub5_and255_u32 (b : UInt8) :
    UInt32.ofBitVec ((b.toInt8.toInt32.toUInt32.toBitVec &&& 255#32) - 5#32) = b.toUInt32 - 5 := by
  revert b; decide

theorem u8_sub1_sub5_and255_u32 (b : UInt8) :
    UInt32.ofBitVec (((b.toInt8.toInt32.toUInt32.toBitVec &&& 255#32) - 1#32) - 5#32) = (b.toUInt32 - 1) - 5 := by
  revert b; decide

theorem u8_ext_u32 (b : UInt8) :
    UInt32.ofBitVec (BitVec.setWidth 32 b.toBitVec) = b.toUInt32 := rfl

theorem u8_sext_toUInt8 (b : UInt8) :
    b.toInt8.toInt32.toUInt32.toUInt8 = b := by
  revert b; decide

theorem u8_sub1_u32_exact (b : UInt8) :
    ({ toBitVec := BitVec.signExtend 32 (BitVec.setWidth 8 (b.toUInt32 - 1).toBitVec) } : UInt32).toUInt8 = b - 1 := by
  revert b; decide

theorem u8_sub2_u32_exact (b : UInt8) :
    ({ toBitVec := BitVec.signExtend 32 (BitVec.setWidth 8 (b.toUInt32 - 2).toBitVec) } : UInt32).toUInt8 = b - 2 := by
  revert b; decide

theorem u8_add1_u32_exact (b : UInt8) :
    ({ toBitVec := BitVec.signExtend 32 (BitVec.setWidth 8 (b.toUInt32 + 1).toBitVec) } : UInt32).toUInt8 = b + 1 := by
  revert b; decide

theorem u8_add2_u32_exact (b : UInt8) :
    ({ toBitVec := BitVec.signExtend 32 (BitVec.setWidth 8 (b.toUInt32 + 2).toBitVec) } : UInt32).toUInt8 = b + 2 := by
  revert b; decide

theorem compareUnsigned_slt_zero (a b : UInt32) :
    (if a == b then (0 : UInt32) else if a < b then 4294967295 else 1).toBitVec.slt 0#32 = decide (a < b) := by
  by_cases h1 : a == b
  · have hab : a = b := LawfulBEq.eq_of_beq h1; subst hab; simp
  · by_cases h2 : a < b <;> simp [h1, h2]

theorem compareUnsigned_eq_zero (a b : UInt32) :
    ((if a == b then (0 : UInt32) else if a < b then 4294967295 else 1) = 0) ↔ a = b := by
  by_cases h1 : a == b <;> by_cases h2 : a < b <;> simp [h1, h2]
  · exact LawfulBEq.eq_of_beq h1
  · exact LawfulBEq.eq_of_beq h1
  · exact fun heq => by subst heq; simp at h1
  · exact fun heq => by subst heq; simp at h1

theorem compareUnsigned64_sge' (a b : UInt64) :
    (0#32).sle (if a == b then (0 : UInt32) else if a < b then 4294967295 else 1).toBitVec = decide (b ≤ a) := by
  by_cases h1 : a == b
  · have hab : a = b := LawfulBEq.eq_of_beq h1; subst hab; simp
  · by_cases h2 : a < b
    · have hlt' : ¬(b ≤ a) := Nat.not_le_of_gt h2
      simp [h1, h2, hlt']
    · have hle' : b ≤ a := Nat.le_of_not_lt h2
      simp [h1, h2, hle']

def dcmpgVal (a b : Float) : UInt32 :=
  if a < b then 4294967295 else if a == b then 0 else 1

theorem dcmpg_slt_zero (a b : Float) :
    (if (a < b) = true then (4294967295 : UInt32) else if (a == b) = true then 0 else 1).toBitVec.slt 0#32 =
      decide (a < b) := by
  by_cases hlt : a < b <;> by_cases heq : (a == b) = true <;> simp [hlt, heq]

theorem dcmpg_sle_zero (a b : Float) :
    (if (a < b) = true then (4294967295 : UInt32) else if (a == b) = true then 0 else 1).toBitVec.sle 0#32 =
      decide (a ≤ b) := by
  rw [float_le_eq_lt_or_beq]
  by_cases hlt : a < b <;> by_cases heq : (a == b) = true <;> simp [hlt, heq]

theorem i32ToDecimalString_eq_toString (v : UInt32) :
    i32ToDecimalString v = toString v.toInt32 := by
  simp only [i32ToDecimalString, toString]
  have hi : v.toInt32.toInt =
      if v < 0x80000000 then (v.toNat : Int) else (v.toNat : Int) - 2 ^ 32 := by
    have h1 : v.toInt32.toInt = v.toBitVec.toInt := rfl
    rw [h1, BitVec.toInt]
    change (if 2 * v.toNat < 2 ^ 32 then (v.toNat : Int) else (v.toNat : Int) - 2 ^ 32) = _
    by_cases h : v < 0x80000000
    · have hlt : v.toNat < 2 ^ 31 := by
        have : (0x80000000 : UInt32).toNat = 2 ^ 31 := rfl
        rw [UInt32.lt_iff_toNat_lt, this] at h; exact h
      have h2 : 2 * v.toNat < 2 ^ 32 := by omega
      simp [h, h2]
    · have hge : ¬(v.toNat < 2 ^ 31) := by
        have : (0x80000000 : UInt32).toNat = 2 ^ 31 := rfl
        rw [UInt32.lt_iff_toNat_lt, this] at h; exact h
      have h2 : ¬(2 * v.toNat < 2 ^ 32) := by omega
      simp [h, h2]
  by_cases h : v < 0x80000000
  · simp [h, hi]
    exact (Int.toNat_of_nonneg (Int.natCast_nonneg _)).symm ▸ by
      change v.toNat.repr = Int.repr (Int.ofNat v.toNat); simp [Int.repr]
  · have hvlt : v.toNat < 2 ^ 32 := UInt32.toNat_lt v
    have hge : 2 ^ 31 ≤ v.toNat := by
      have : (0x80000000 : UInt32).toNat = 2 ^ 31 := rfl
      rw [UInt32.lt_iff_toNat_lt, this] at h; omega
    have hneg : (v.toNat : Int) - 2 ^ 32 = Int.negSucc (2 ^ 32 - v.toNat - 1) := by omega
    have hsuc : (2 ^ 32 - v.toNat - 1).succ = 0x100000000 - v.toNat := by omega
    simp only [h, ↓reduceIte] at hi
    rw [hi, hneg]
    simp only [h, ↓reduceIte, Int.repr, hsuc]

/-! ### Polymorphic Chunk & Branch Evaluation Lemmas -/

class HasDefaultIsZero {Ext Heap : Type} (hooks : JvmHooks Ext Heap) : Prop where
  isZero?_eq : hooks.isZero? = fun v => v.asI32?.map (· == 0)

section GenericFast

variable {Ext Heap : Type} (hooks : JvmHooks Ext Heap)

theorem afterBlockChunk_cont (f pc : Nat) (is : List JvmInstr) (st : JvmState Ext Heap) (prog : List JvmInstr) :
    afterBlockChunk hooks (.cont f pc is st) prog = runJvmValFast hooks f prog pc is st := rfl

theorem afterBlockChunk_jump (f pc : Nat) (stk : List (JvmVal Ext)) (locs : Nat → JvmVal Ext)
    (jh : JvmHeap Ext) (hp : Heap) (prog : List JvmInstr) :
    afterBlockChunk hooks (.jump f ⟨pc, stk, locs, jh, hp⟩) prog =
      runJvmValFast hooks f prog pc (prog.drop pc) ⟨pc, stk, locs, jh, hp⟩ := rfl

theorem afterBlockChunk_done (res : Option (JvmVal Ext)) (prog : List JvmInstr) :
    afterBlockChunk hooks (.done res) prog = res := rfl

theorem afterResBlockChunk_cont (f pc : Nat) (is : List JvmInstr) (st : JvmState Ext Heap) (prog : List JvmInstr) :
    afterResBlockChunk hooks (.cont f pc is st) prog = runJvmResFast hooks f prog pc is st := rfl

theorem afterResBlockChunk_jump (f pc : Nat) (stk : List (JvmVal Ext)) (locs : Nat → JvmVal Ext)
    (jh : JvmHeap Ext) (hp : Heap) (prog : List JvmInstr) :
    afterResBlockChunk hooks (.jump f ⟨pc, stk, locs, jh, hp⟩) prog =
      runJvmResFast hooks f prog pc (prog.drop pc) ⟨pc, stk, locs, jh, hp⟩ := rfl

theorem afterResBlockChunk_done (res : Option (JvmVal Ext × JvmState Ext Heap)) (prog : List JvmInstr) :
    afterResBlockChunk hooks (.done res) prog = res := rfl

theorem evalBranchInstrCons_ifeq [HasDefaultIsZero hooks]
    (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : UInt32) (s : List (JvmVal Ext)) (locs : Nat → JvmVal Ext)
    (jh : JvmHeap Ext) (hp : Heap) :
    evalBranchInstrCons hooks f1 prog pc (.ifeq target) rest ⟨pc0, .i32 v :: s, locs, jh, hp⟩ =
      if v == 0 then
        runJvmValFast hooks f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmValFast hooks f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ := by
  simp [evalBranchInstrCons, isBranchInstr, dispatchBranch, HasDefaultIsZero.isZero?_eq (hooks := hooks)]

theorem evalBranchInstrCons_ifeq_bool [HasDefaultIsZero hooks]
    (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (b : Bool) (s : List (JvmVal Ext)) (locs : Nat → JvmVal Ext)
    (jh : JvmHeap Ext) (hp : Heap) :
    evalBranchInstrCons hooks f1 prog pc (.ifeq target) rest ⟨pc0, .bool b :: s, locs, jh, hp⟩ =
      if !b then
        runJvmValFast hooks f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmValFast hooks f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ := by
  simp [evalBranchInstrCons, isBranchInstr, dispatchBranch, HasDefaultIsZero.isZero?_eq (hooks := hooks)]

theorem evalBranchInstrCons_ifne [HasDefaultIsZero hooks]
    (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : UInt32) (s : List (JvmVal Ext)) (locs : Nat → JvmVal Ext)
    (jh : JvmHeap Ext) (hp : Heap) :
    evalBranchInstrCons hooks f1 prog pc (.ifne target) rest ⟨pc0, .i32 v :: s, locs, jh, hp⟩ =
      if !(v == 0) then
        runJvmValFast hooks f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmValFast hooks f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ := by
  simp [evalBranchInstrCons, isBranchInstr, dispatchBranch, HasDefaultIsZero.isZero?_eq (hooks := hooks)]

theorem evalBranchInstrCons_ifne_bool [HasDefaultIsZero hooks]
    (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (b : Bool) (s : List (JvmVal Ext)) (locs : Nat → JvmVal Ext)
    (jh : JvmHeap Ext) (hp : Heap) :
    evalBranchInstrCons hooks f1 prog pc (.ifne target) rest ⟨pc0, .bool b :: s, locs, jh, hp⟩ =
      if b then
        runJvmValFast hooks f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmValFast hooks f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ := by
  simp [evalBranchInstrCons, isBranchInstr, dispatchBranch, HasDefaultIsZero.isZero?_eq (hooks := hooks)]
  cases b <;> simp

theorem evalBranchInstrCons_iflt (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : UInt32) (s : List (JvmVal Ext)) (locs : Nat → JvmVal Ext)
    (jh : JvmHeap Ext) (hp : Heap) :
    evalBranchInstrCons hooks f1 prog pc (.iflt target) rest ⟨pc0, .i32 v :: s, locs, jh, hp⟩ =
      if v.toBitVec.slt 0#32 then
        runJvmValFast hooks f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmValFast hooks f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ := by
  simp [evalBranchInstrCons, isBranchInstr, dispatchBranch]

theorem evalBranchInstrCons_ifle (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : UInt32) (s : List (JvmVal Ext)) (locs : Nat → JvmVal Ext)
    (jh : JvmHeap Ext) (hp : Heap) :
    evalBranchInstrCons hooks f1 prog pc (.ifle target) rest ⟨pc0, .i32 v :: s, locs, jh, hp⟩ =
      if v.toBitVec.sle 0#32 then
        runJvmValFast hooks f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmValFast hooks f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ := by
  simp [evalBranchInstrCons, isBranchInstr, dispatchBranch]

theorem evalBranchInstrCons_ifgt (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : UInt32) (s : List (JvmVal Ext)) (locs : Nat → JvmVal Ext)
    (jh : JvmHeap Ext) (hp : Heap) :
    evalBranchInstrCons hooks f1 prog pc (.ifgt target) rest ⟨pc0, .i32 v :: s, locs, jh, hp⟩ =
      if (0#32).slt v.toBitVec then
        runJvmValFast hooks f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmValFast hooks f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ := by
  simp [evalBranchInstrCons, isBranchInstr, dispatchBranch]

theorem evalBranchInstrCons_ifge (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : UInt32) (s : List (JvmVal Ext)) (locs : Nat → JvmVal Ext)
    (jh : JvmHeap Ext) (hp : Heap) :
    evalBranchInstrCons hooks f1 prog pc (.ifge target) rest ⟨pc0, .i32 v :: s, locs, jh, hp⟩ =
      if (0#32).sle v.toBitVec then
        runJvmValFast hooks f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmValFast hooks f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ := by
  simp [evalBranchInstrCons, isBranchInstr, dispatchBranch]

theorem evalBranchInstrCons_ifnull (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : JvmVal Ext) (s : List (JvmVal Ext)) (locs : Nat → JvmVal Ext)
    (jh : JvmHeap Ext) (hp : Heap) :
    evalBranchInstrCons hooks f1 prog pc (.ifnull target) rest ⟨pc0, v :: s, locs, jh, hp⟩ =
      if v.isNull then runJvmValFast hooks f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmValFast hooks f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ := by
  simp [evalBranchInstrCons, isBranchInstr, dispatchBranch]

theorem evalBranchInstrCons_ifnonnull (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : JvmVal Ext) (s : List (JvmVal Ext)) (locs : Nat → JvmVal Ext)
    (jh : JvmHeap Ext) (hp : Heap) :
    evalBranchInstrCons hooks f1 prog pc (.ifnonnull target) rest ⟨pc0, v :: s, locs, jh, hp⟩ =
      if !v.isNull then runJvmValFast hooks f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmValFast hooks f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ := by
  simp [evalBranchInstrCons, isBranchInstr, dispatchBranch]

theorem evalBranchInstrCons_if_icmpeq (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (b a : UInt32) (s : List (JvmVal Ext)) (locs : Nat → JvmVal Ext)
    (jh : JvmHeap Ext) (hp : Heap) :
    evalBranchInstrCons hooks f1 prog pc (.if_icmpeq target) rest ⟨pc0, .i32 b :: .i32 a :: s, locs, jh, hp⟩ =
      if a == b then runJvmValFast hooks f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmValFast hooks f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ := by
  simp [evalBranchInstrCons, isBranchInstr, dispatchBranch]

theorem evalBranchInstrCons_if_icmpne (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (b a : UInt32) (s : List (JvmVal Ext)) (locs : Nat → JvmVal Ext)
    (jh : JvmHeap Ext) (hp : Heap) :
    evalBranchInstrCons hooks f1 prog pc (.if_icmpne target) rest ⟨pc0, .i32 b :: .i32 a :: s, locs, jh, hp⟩ =
      if !(a == b) then runJvmValFast hooks f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmValFast hooks f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ := by
  simp [evalBranchInstrCons, isBranchInstr, dispatchBranch]

theorem evalBranchInstrCons_if_icmplt (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (b a : UInt32) (s : List (JvmVal Ext)) (locs : Nat → JvmVal Ext)
    (jh : JvmHeap Ext) (hp : Heap) :
    evalBranchInstrCons hooks f1 prog pc (.if_icmplt target) rest ⟨pc0, .i32 b :: .i32 a :: s, locs, jh, hp⟩ =
      if a.toBitVec.slt b.toBitVec then
        runJvmValFast hooks f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmValFast hooks f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ := by
  simp [evalBranchInstrCons, isBranchInstr, dispatchBranch]

theorem evalBranchInstrCons_if_icmpge (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (b a : UInt32) (s : List (JvmVal Ext)) (locs : Nat → JvmVal Ext)
    (jh : JvmHeap Ext) (hp : Heap) :
    evalBranchInstrCons hooks f1 prog pc (.if_icmpge target) rest ⟨pc0, .i32 b :: .i32 a :: s, locs, jh, hp⟩ =
      if b.toBitVec.sle a.toBitVec then
        runJvmValFast hooks f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmValFast hooks f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ := by
  simp [evalBranchInstrCons, isBranchInstr, dispatchBranch]

theorem evalBranchInstrCons_if_icmpgt (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (b a : UInt32) (s : List (JvmVal Ext)) (locs : Nat → JvmVal Ext)
    (jh : JvmHeap Ext) (hp : Heap) :
    evalBranchInstrCons hooks f1 prog pc (.if_icmpgt target) rest ⟨pc0, .i32 b :: .i32 a :: s, locs, jh, hp⟩ =
      if b.toBitVec.slt a.toBitVec then
        runJvmValFast hooks f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmValFast hooks f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ := by
  simp [evalBranchInstrCons, isBranchInstr, dispatchBranch]

theorem evalBranchInstrCons_if_icmple (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (b a : UInt32) (s : List (JvmVal Ext)) (locs : Nat → JvmVal Ext)
    (jh : JvmHeap Ext) (hp : Heap) :
    evalBranchInstrCons hooks f1 prog pc (.if_icmple target) rest ⟨pc0, .i32 b :: .i32 a :: s, locs, jh, hp⟩ =
      if a.toBitVec.sle b.toBitVec then
        runJvmValFast hooks f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmValFast hooks f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ := by
  simp [evalBranchInstrCons, isBranchInstr, dispatchBranch]

theorem evalBranchInstrCons_tableswitch (f1 : Nat) (prog : List JvmInstr) (pc : Nat)
    (low : Int32) (targets : List Nat) (defaultTarget : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (key : UInt32) (s : List (JvmVal Ext)) (locs : Nat → JvmVal Ext)
    (jh : JvmHeap Ext) (hp : Heap) :
    evalBranchInstrCons hooks f1 prog pc (.tableswitch low targets defaultTarget) rest
        ⟨pc0, .i32 key :: s, locs, jh, hp⟩ =
      let target := tableswitchTarget key low targets defaultTarget
      runJvmValFast hooks f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩ := by
  simp [evalBranchInstrCons, isBranchInstr, dispatchBranch]

theorem evalBranchInstrCons_lookupswitch (f1 : Nat) (prog : List JvmInstr) (pc : Nat)
    (cases : List (Int32 × Nat)) (defaultTarget : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (key : UInt32) (s : List (JvmVal Ext)) (locs : Nat → JvmVal Ext)
    (jh : JvmHeap Ext) (hp : Heap) :
    evalBranchInstrCons hooks f1 prog pc (.lookupswitch cases defaultTarget) rest
        ⟨pc0, .i32 key :: s, locs, jh, hp⟩ =
      let target := lookupswitchTarget key cases defaultTarget
      runJvmValFast hooks f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩ := by
  simp [evalBranchInstrCons, isBranchInstr, dispatchBranch]

theorem evalBranchInstrCons_goto (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (stk : List (JvmVal Ext)) (locs : Nat → JvmVal Ext)
    (jh : JvmHeap Ext) (hp : Heap) :
    evalBranchInstrCons hooks f1 prog pc (.goto target) rest ⟨pc0, stk, locs, jh, hp⟩ =
      runJvmValFast hooks f1 prog target (prog.drop target) ⟨target, stk, locs, jh, hp⟩ := rfl

theorem evalResBranchInstrCons_ifeq [HasDefaultIsZero hooks]
    (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : UInt32) (s : List (JvmVal Ext)) (locs : Nat → JvmVal Ext)
    (jh : JvmHeap Ext) (hp : Heap) :
    evalResBranchInstrCons hooks f1 prog pc (.ifeq target) rest ⟨pc0, .i32 v :: s, locs, jh, hp⟩ =
      if v == 0 then
        runJvmResFast hooks f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmResFast hooks f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ := by
  simp [evalResBranchInstrCons, isBranchInstr, dispatchBranch, HasDefaultIsZero.isZero?_eq (hooks := hooks)]

theorem evalResBranchInstrCons_ifeq_bool [HasDefaultIsZero hooks]
    (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (b : Bool) (s : List (JvmVal Ext)) (locs : Nat → JvmVal Ext)
    (jh : JvmHeap Ext) (hp : Heap) :
    evalResBranchInstrCons hooks f1 prog pc (.ifeq target) rest ⟨pc0, .bool b :: s, locs, jh, hp⟩ =
      if !b then
        runJvmResFast hooks f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmResFast hooks f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ := by
  simp [evalResBranchInstrCons, isBranchInstr, dispatchBranch, HasDefaultIsZero.isZero?_eq (hooks := hooks)]

theorem evalResBranchInstrCons_ifne [HasDefaultIsZero hooks]
    (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : UInt32) (s : List (JvmVal Ext)) (locs : Nat → JvmVal Ext)
    (jh : JvmHeap Ext) (hp : Heap) :
    evalResBranchInstrCons hooks f1 prog pc (.ifne target) rest ⟨pc0, .i32 v :: s, locs, jh, hp⟩ =
      if !(v == 0) then
        runJvmResFast hooks f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmResFast hooks f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ := by
  simp [evalResBranchInstrCons, isBranchInstr, dispatchBranch, HasDefaultIsZero.isZero?_eq (hooks := hooks)]

theorem evalResBranchInstrCons_ifne_bool [HasDefaultIsZero hooks]
    (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (b : Bool) (s : List (JvmVal Ext)) (locs : Nat → JvmVal Ext)
    (jh : JvmHeap Ext) (hp : Heap) :
    evalResBranchInstrCons hooks f1 prog pc (.ifne target) rest ⟨pc0, .bool b :: s, locs, jh, hp⟩ =
      if b then
        runJvmResFast hooks f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmResFast hooks f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ := by
  simp [evalResBranchInstrCons, isBranchInstr, dispatchBranch, HasDefaultIsZero.isZero?_eq (hooks := hooks)]
  cases b <;> simp

theorem evalResBranchInstrCons_iflt (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : UInt32) (s : List (JvmVal Ext)) (locs : Nat → JvmVal Ext)
    (jh : JvmHeap Ext) (hp : Heap) :
    evalResBranchInstrCons hooks f1 prog pc (.iflt target) rest ⟨pc0, .i32 v :: s, locs, jh, hp⟩ =
      if v.toBitVec.slt 0#32 then
        runJvmResFast hooks f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmResFast hooks f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ := by
  simp [evalResBranchInstrCons, isBranchInstr, dispatchBranch]

theorem evalResBranchInstrCons_ifle (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : UInt32) (s : List (JvmVal Ext)) (locs : Nat → JvmVal Ext)
    (jh : JvmHeap Ext) (hp : Heap) :
    evalResBranchInstrCons hooks f1 prog pc (.ifle target) rest ⟨pc0, .i32 v :: s, locs, jh, hp⟩ =
      if v.toBitVec.sle 0#32 then
        runJvmResFast hooks f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmResFast hooks f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ := by
  simp [evalResBranchInstrCons, isBranchInstr, dispatchBranch]

theorem evalResBranchInstrCons_ifgt (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : UInt32) (s : List (JvmVal Ext)) (locs : Nat → JvmVal Ext)
    (jh : JvmHeap Ext) (hp : Heap) :
    evalResBranchInstrCons hooks f1 prog pc (.ifgt target) rest ⟨pc0, .i32 v :: s, locs, jh, hp⟩ =
      if (0#32).slt v.toBitVec then
        runJvmResFast hooks f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmResFast hooks f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ := by
  simp [evalResBranchInstrCons, isBranchInstr, dispatchBranch]

theorem evalResBranchInstrCons_ifge (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : UInt32) (s : List (JvmVal Ext)) (locs : Nat → JvmVal Ext)
    (jh : JvmHeap Ext) (hp : Heap) :
    evalResBranchInstrCons hooks f1 prog pc (.ifge target) rest ⟨pc0, .i32 v :: s, locs, jh, hp⟩ =
      if (0#32).sle v.toBitVec then
        runJvmResFast hooks f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmResFast hooks f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ := by
  simp [evalResBranchInstrCons, isBranchInstr, dispatchBranch]

theorem evalResBranchInstrCons_ifnull (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : JvmVal Ext) (s : List (JvmVal Ext)) (locs : Nat → JvmVal Ext)
    (jh : JvmHeap Ext) (hp : Heap) :
    evalResBranchInstrCons hooks f1 prog pc (.ifnull target) rest ⟨pc0, v :: s, locs, jh, hp⟩ =
      if v.isNull then runJvmResFast hooks f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmResFast hooks f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ := by
  simp [evalResBranchInstrCons, isBranchInstr, dispatchBranch]

theorem evalResBranchInstrCons_ifnonnull (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : JvmVal Ext) (s : List (JvmVal Ext)) (locs : Nat → JvmVal Ext)
    (jh : JvmHeap Ext) (hp : Heap) :
    evalResBranchInstrCons hooks f1 prog pc (.ifnonnull target) rest ⟨pc0, v :: s, locs, jh, hp⟩ =
      if !v.isNull then runJvmResFast hooks f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmResFast hooks f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ := by
  simp [evalResBranchInstrCons, isBranchInstr, dispatchBranch]

theorem evalResBranchInstrCons_if_icmpeq (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (b a : UInt32) (s : List (JvmVal Ext)) (locs : Nat → JvmVal Ext)
    (jh : JvmHeap Ext) (hp : Heap) :
    evalResBranchInstrCons hooks f1 prog pc (.if_icmpeq target) rest ⟨pc0, .i32 b :: .i32 a :: s, locs, jh, hp⟩ =
      if a == b then runJvmResFast hooks f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmResFast hooks f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ := by
  simp [evalResBranchInstrCons, isBranchInstr, dispatchBranch]

theorem evalResBranchInstrCons_if_icmpne (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (b a : UInt32) (s : List (JvmVal Ext)) (locs : Nat → JvmVal Ext)
    (jh : JvmHeap Ext) (hp : Heap) :
    evalResBranchInstrCons hooks f1 prog pc (.if_icmpne target) rest ⟨pc0, .i32 b :: .i32 a :: s, locs, jh, hp⟩ =
      if !(a == b) then runJvmResFast hooks f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmResFast hooks f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ := by
  simp [evalResBranchInstrCons, isBranchInstr, dispatchBranch]

theorem evalResBranchInstrCons_if_icmplt (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (b a : UInt32) (s : List (JvmVal Ext)) (locs : Nat → JvmVal Ext)
    (jh : JvmHeap Ext) (hp : Heap) :
    evalResBranchInstrCons hooks f1 prog pc (.if_icmplt target) rest ⟨pc0, .i32 b :: .i32 a :: s, locs, jh, hp⟩ =
      if a.toBitVec.slt b.toBitVec then
        runJvmResFast hooks f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmResFast hooks f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ := by
  simp [evalResBranchInstrCons, isBranchInstr, dispatchBranch]

theorem evalResBranchInstrCons_if_icmpge (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (b a : UInt32) (s : List (JvmVal Ext)) (locs : Nat → JvmVal Ext)
    (jh : JvmHeap Ext) (hp : Heap) :
    evalResBranchInstrCons hooks f1 prog pc (.if_icmpge target) rest ⟨pc0, .i32 b :: .i32 a :: s, locs, jh, hp⟩ =
      if b.toBitVec.sle a.toBitVec then
        runJvmResFast hooks f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmResFast hooks f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ := by
  simp [evalResBranchInstrCons, isBranchInstr, dispatchBranch]

theorem evalResBranchInstrCons_if_icmpgt (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (b a : UInt32) (s : List (JvmVal Ext)) (locs : Nat → JvmVal Ext)
    (jh : JvmHeap Ext) (hp : Heap) :
    evalResBranchInstrCons hooks f1 prog pc (.if_icmpgt target) rest ⟨pc0, .i32 b :: .i32 a :: s, locs, jh, hp⟩ =
      if b.toBitVec.slt a.toBitVec then
        runJvmResFast hooks f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmResFast hooks f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ := by
  simp [evalResBranchInstrCons, isBranchInstr, dispatchBranch]

theorem evalResBranchInstrCons_if_icmple (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (b a : UInt32) (s : List (JvmVal Ext)) (locs : Nat → JvmVal Ext)
    (jh : JvmHeap Ext) (hp : Heap) :
    evalResBranchInstrCons hooks f1 prog pc (.if_icmple target) rest ⟨pc0, .i32 b :: .i32 a :: s, locs, jh, hp⟩ =
      if a.toBitVec.sle b.toBitVec then
        runJvmResFast hooks f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmResFast hooks f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ := by
  simp [evalResBranchInstrCons, isBranchInstr, dispatchBranch]

theorem evalResBranchInstrCons_tableswitch (f1 : Nat) (prog : List JvmInstr) (pc : Nat)
    (low : Int32) (targets : List Nat) (defaultTarget : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (key : UInt32) (s : List (JvmVal Ext)) (locs : Nat → JvmVal Ext)
    (jh : JvmHeap Ext) (hp : Heap) :
    evalResBranchInstrCons hooks f1 prog pc (.tableswitch low targets defaultTarget) rest
        ⟨pc0, .i32 key :: s, locs, jh, hp⟩ =
      let target := tableswitchTarget key low targets defaultTarget
      runJvmResFast hooks f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩ := by
  simp [evalResBranchInstrCons, isBranchInstr, dispatchBranch]

theorem evalResBranchInstrCons_lookupswitch (f1 : Nat) (prog : List JvmInstr) (pc : Nat)
    (cases : List (Int32 × Nat)) (defaultTarget : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (key : UInt32) (s : List (JvmVal Ext)) (locs : Nat → JvmVal Ext)
    (jh : JvmHeap Ext) (hp : Heap) :
    evalResBranchInstrCons hooks f1 prog pc (.lookupswitch cases defaultTarget) rest
        ⟨pc0, .i32 key :: s, locs, jh, hp⟩ =
      let target := lookupswitchTarget key cases defaultTarget
      runJvmResFast hooks f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩ := by
  simp [evalResBranchInstrCons, isBranchInstr, dispatchBranch]

theorem evalResBranchInstrCons_goto (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (stk : List (JvmVal Ext)) (locs : Nat → JvmVal Ext)
    (jh : JvmHeap Ext) (hp : Heap) :
    evalResBranchInstrCons hooks f1 prog pc (.goto target) rest ⟨pc0, stk, locs, jh, hp⟩ =
      runJvmResFast hooks f1 prog target (prog.drop target) ⟨target, stk, locs, jh, hp⟩ := rfl

/-! ### Generic Fuel, Single-Instruction, Array, Cast, and Stdlib Stepping Lemmas -/

theorem runJvmValFast_split_fuel (m : Nat) {k : Nat}
    (prog : List JvmInstr) (pc : Nat) (instrs : List JvmInstr) (st : JvmState Ext Heap)
    (hk : m ≤ k) :
    runJvmValFast hooks k prog pc instrs st =
      runJvmValFast hooks ((k - m) + m) prog pc instrs st := by
  rw [Nat.sub_add_cancel hk]

theorem runJvmResFast_split_fuel (m : Nat) {k : Nat}
    (prog : List JvmInstr) (pc : Nat) (instrs : List JvmInstr) (st : JvmState Ext Heap)
    (hk : m ≤ k) :
    runJvmResFast hooks k prog pc instrs st =
      runJvmResFast hooks ((k - m) + m) prog pc instrs st := by
  rw [Nat.sub_add_cancel hk]

theorem runJvmValFast_step_of_stepInstr {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {instr : JvmInstr} {rest : List JvmInstr} {st st' : JvmState Ext Heap}
    (hbr : isBranchInstr instr = false)
    (hno : ¬(instr = .i2l ∧ ∃ r', rest = .lconst 4294967295 :: .land :: r'))
    (hs : stepInstr hooks instr { st with pc := pc } = .inl (some st'))
    (hpc : st'.pc = pc + 1) :
    runJvmValFast hooks (f + 1) prog pc (instr :: rest) st =
      runJvmValFast hooks f prog (pc + 1) rest st' := by
  rw [runJvmValFast_step_nonbranch hooks f prog pc instr rest st hbr hno, hs]
  simp [hpc]

theorem runJvmResFast_step_of_stepInstr {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {instr : JvmInstr} {rest : List JvmInstr} {st st' : JvmState Ext Heap}
    (hbr : isBranchInstr instr = false)
    (hno : ¬(instr = .i2l ∧ ∃ r', rest = .lconst 4294967295 :: .land :: r'))
    (hs : stepInstr hooks instr { st with pc := pc } = .inl (some st'))
    (hpc : st'.pc = pc + 1) :
    runJvmResFast hooks (f + 1) prog pc (instr :: rest) st =
      runJvmResFast hooks f prog (pc + 1) rest st' := by
  rw [runJvmResFast_step_nonbranch hooks f prog pc instr rest st hbr hno, hs]
  simp [hpc]

theorem runJvmValFast_invokestatic_step {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {cls method desc : String} {rest : List JvmInstr} {pc0 : Nat} {stk stk' : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh jh' : JvmHeap Ext} {hp hp' : Heap}
    (hs : stepInvokeStaticGeneric hooks ⟨pc, stk, locs, jh, hp⟩ cls method desc =
      .inl (some ⟨pc + 1, stk', locs, jh', hp'⟩)) :
    runJvmValFast hooks (f + 1) prog pc (.invokestatic cls method desc :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      runJvmValFast hooks f prog (pc + 1) rest ⟨pc + 1, stk', locs, jh', hp'⟩ :=
  runJvmValFast_step_of_stepInstr hooks rfl (by simp)
    (by unfold stepInstr; simpa using hs) rfl

theorem runJvmResFast_invokestatic_step {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {cls method desc : String} {rest : List JvmInstr} {pc0 : Nat} {stk stk' : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh jh' : JvmHeap Ext} {hp hp' : Heap}
    (hs : stepInvokeStaticGeneric hooks ⟨pc, stk, locs, jh, hp⟩ cls method desc =
      .inl (some ⟨pc + 1, stk', locs, jh', hp'⟩)) :
    runJvmResFast hooks (f + 1) prog pc (.invokestatic cls method desc :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      runJvmResFast hooks f prog (pc + 1) rest ⟨pc + 1, stk', locs, jh', hp'⟩ :=
  runJvmResFast_step_of_stepInstr hooks rfl (by simp)
    (by unfold stepInstr; simpa using hs) rfl

theorem runJvmValFast_invokevirtual_step {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {cls method desc : String} {rest : List JvmInstr} {pc0 : Nat} {stk stk' : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh jh' : JvmHeap Ext} {hp hp' : Heap}
    (hs : stepInvokeVirtualGeneric hooks ⟨pc, stk, locs, jh, hp⟩ cls method desc =
      .inl (some ⟨pc + 1, stk', locs, jh', hp'⟩)) :
    runJvmValFast hooks (f + 1) prog pc (.invokevirtual cls method desc :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      runJvmValFast hooks f prog (pc + 1) rest ⟨pc + 1, stk', locs, jh', hp'⟩ :=
  runJvmValFast_step_of_stepInstr hooks rfl (by simp)
    (by unfold stepInstr; simpa using hs) rfl

theorem runJvmResFast_invokevirtual_step {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {cls method desc : String} {rest : List JvmInstr} {pc0 : Nat} {stk stk' : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh jh' : JvmHeap Ext} {hp hp' : Heap}
    (hs : stepInvokeVirtualGeneric hooks ⟨pc, stk, locs, jh, hp⟩ cls method desc =
      .inl (some ⟨pc + 1, stk', locs, jh', hp'⟩)) :
    runJvmResFast hooks (f + 1) prog pc (.invokevirtual cls method desc :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      runJvmResFast hooks f prog (pc + 1) rest ⟨pc + 1, stk', locs, jh', hp'⟩ :=
  runJvmResFast_step_of_stepInstr hooks rfl (by simp)
    (by unfold stepInstr; simpa using hs) rfl

theorem runJvmValFast_invokespecial_step {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {cls method desc : String} {rest : List JvmInstr} {pc0 : Nat} {stk stk' : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh jh' : JvmHeap Ext} {hp hp' : Heap}
    (hs : stepInvokeSpecialGeneric hooks ⟨pc, stk, locs, jh, hp⟩ cls method desc =
      .inl (some ⟨pc + 1, stk', locs, jh', hp'⟩)) :
    runJvmValFast hooks (f + 1) prog pc (.invokespecial cls method desc :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      runJvmValFast hooks f prog (pc + 1) rest ⟨pc + 1, stk', locs, jh', hp'⟩ :=
  runJvmValFast_step_of_stepInstr hooks rfl (by simp)
    (by unfold stepInstr; simpa using hs) rfl

theorem runJvmResFast_invokespecial_step {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {cls method desc : String} {rest : List JvmInstr} {pc0 : Nat} {stk stk' : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh jh' : JvmHeap Ext} {hp hp' : Heap}
    (hs : stepInvokeSpecialGeneric hooks ⟨pc, stk, locs, jh, hp⟩ cls method desc =
      .inl (some ⟨pc + 1, stk', locs, jh', hp'⟩)) :
    runJvmResFast hooks (f + 1) prog pc (.invokespecial cls method desc :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      runJvmResFast hooks f prog (pc + 1) rest ⟨pc + 1, stk', locs, jh', hp'⟩ :=
  runJvmResFast_step_of_stepInstr hooks rfl (by simp)
    (by unfold stepInstr; simpa using hs) rfl

theorem runJvmResFast_invokespecial_pred {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {cls method desc : String} {rest : List JvmInstr} {pc0 : Nat} {stk stk' : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh jh' : JvmHeap Ext} {hp hp' : Heap}
    (hf : 0 < f)
    (hs : stepInvokeSpecialGeneric hooks ⟨pc, stk, locs, jh, hp⟩ cls method desc =
      .inl (some ⟨pc + 1, stk', locs, jh', hp'⟩)) :
    runJvmResFast hooks f prog pc (.invokespecial cls method desc :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      runJvmResFast hooks (f - 1) prog (pc + 1) rest ⟨pc + 1, stk', locs, jh', hp'⟩ := by
  obtain ⟨f1, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hf)
  exact runJvmResFast_invokespecial_step hooks hs

theorem runJvmValFast_invokeinterface_step {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {cls method desc : String} {rest : List JvmInstr} {pc0 : Nat} {stk stk' : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh jh' : JvmHeap Ext} {hp hp' : Heap}
    (hs : stepInvokeInterfaceGeneric hooks ⟨pc, stk, locs, jh, hp⟩ cls method desc =
      .inl (some ⟨pc + 1, stk', locs, jh', hp'⟩)) :
    runJvmValFast hooks (f + 1) prog pc (.invokeinterface cls method desc :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      runJvmValFast hooks f prog (pc + 1) rest ⟨pc + 1, stk', locs, jh', hp'⟩ :=
  runJvmValFast_step_of_stepInstr hooks rfl (by simp)
    (by unfold stepInstr; simpa using hs) rfl

theorem runJvmResFast_invokeinterface_step {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {cls method desc : String} {rest : List JvmInstr} {pc0 : Nat} {stk stk' : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh jh' : JvmHeap Ext} {hp hp' : Heap}
    (hs : stepInvokeInterfaceGeneric hooks ⟨pc, stk, locs, jh, hp⟩ cls method desc =
      .inl (some ⟨pc + 1, stk', locs, jh', hp'⟩)) :
    runJvmResFast hooks (f + 1) prog pc (.invokeinterface cls method desc :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      runJvmResFast hooks f prog (pc + 1) rest ⟨pc + 1, stk', locs, jh', hp'⟩ :=
  runJvmResFast_step_of_stepInstr hooks rfl (by simp)
    (by unfold stepInstr; simpa using hs) rfl

theorem stepInstr_dcmpg {pc : Nat} {a b : Float} {rest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap} :
    stepInstr hooks .dcmpg ⟨pc, .f64 b :: .f64 a :: rest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 (dcmpgVal a b) :: rest, locs, jh, hp⟩) := rfl

theorem stepInstr_arraylength_obj {pc addr : Nat} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    {cls : String} {elems : Array (JvmVal Ext)}
    (hget : jh.get? addr = some (.objArray cls elems)) :
    stepInstr hooks .arraylength ⟨pc, .heapRef addr :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 (UInt32.ofNat elems.size) :: stkRest, locs, jh, hp⟩) := by
  unfold stepInstr
  simp [hget, HeapObj.arrayLength?]

theorem stepInstr_arraylength_byte {pc addr : Nat} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap} {elems : Array UInt8}
    (hget : jh.get? addr = some (.byteArray elems)) :
    stepInstr hooks .arraylength ⟨pc, .heapRef addr :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 (UInt32.ofNat elems.size) :: stkRest, locs, jh, hp⟩) := by
  unfold stepInstr
  simp [hget, HeapObj.arrayLength?]

theorem stepInstr_arraylength_strArr {pc : Nat} {xs : Array String} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap} :
    stepInstr hooks .arraylength ⟨pc, .strArr xs :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 (UInt32.ofNat xs.size) :: stkRest, locs, jh, hp⟩) := rfl

theorem stepInstr_checkcast_objArray {pc addr : Nat} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    {cls targetCls : String} {elems : Array (JvmVal Ext)}
    (hget : jh.get? addr = some (.objArray cls elems))
    (hm : HeapObj.matchesType hooks.isSubtypeOf targetCls (.objArray cls elems) = true) :
    stepInstr hooks (.checkcast targetCls) ⟨pc, .heapRef addr :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .heapRef addr :: stkRest, locs, jh, hp⟩) := by
  unfold stepInstr
  simp [evalCheckCast, JvmHeap.checkCast, JvmHeap.checkInstanceOf, hget, hm]

theorem stepInvokeSpecial_pair_init {pc : Nat} {a b : JvmVal Ext} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap} {desc : String} :
    stepInvokeSpecialGeneric hooks
        ⟨pc, b :: a :: .allocRef "kotlin/Pair" :: .allocRef "kotlin/Pair" :: stkRest, locs, jh, hp⟩
        "kotlin/Pair" "<init>" desc =
      .inl (some ⟨pc + 1, .pair a b :: stkRest, locs, jh, hp⟩) := rfl

theorem stepInvokeVirtual_pair_getFirst {pc : Nat} {a b : JvmVal Ext} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap} {desc : String} :
    stepInvokeVirtualGeneric hooks ⟨pc, .pair a b :: stkRest, locs, jh, hp⟩
        "kotlin/Pair" "getFirst" desc =
      .inl (some ⟨pc + 1, a :: stkRest, locs, jh, hp⟩) := rfl

theorem stepInvokeVirtual_pair_getSecond {pc : Nat} {a b : JvmVal Ext} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap} {desc : String} :
    stepInvokeVirtualGeneric hooks ⟨pc, .pair a b :: stkRest, locs, jh, hp⟩
        "kotlin/Pair" "getSecond" desc =
      .inl (some ⟨pc + 1, b :: stkRest, locs, jh, hp⟩) := rfl

theorem stepInvokeVirtual_integer_intValue {pc : Nat} {v : UInt32} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap} {desc : String} :
    stepInvokeVirtualGeneric hooks ⟨pc, .boxedInt v :: stkRest, locs, jh, hp⟩
        "java/lang/Integer" "intValue" desc =
      .inl (some ⟨pc + 1, .i32 v :: stkRest, locs, jh, hp⟩) := rfl

theorem stepInvokeVirtual_number_intValue {pc : Nat} {v : UInt32} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap} {desc : String} :
    stepInvokeVirtualGeneric hooks ⟨pc, .boxedInt v :: stkRest, locs, jh, hp⟩
        "java/lang/Number" "intValue" desc =
      .inl (some ⟨pc + 1, .i32 v :: stkRest, locs, jh, hp⟩) := rfl

theorem stepInvokeVirtual_uint_unbox {pc : Nat} {v : UInt32} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap} {desc : String} :
    stepInvokeVirtualGeneric hooks ⟨pc, .boxedUInt v :: stkRest, locs, jh, hp⟩
        "kotlin/UInt" "unbox-impl" desc =
      .inl (some ⟨pc + 1, .i32 v :: stkRest, locs, jh, hp⟩) := rfl

theorem stepInvokeVirtual_ulong_unbox {pc : Nat} {v : UInt64} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap} {desc : String} :
    stepInvokeVirtualGeneric hooks ⟨pc, .boxedULong v :: stkRest, locs, jh, hp⟩
        "kotlin/ULong" "unbox-impl" desc =
      .inl (some ⟨pc + 1, .i64 v :: stkRest, locs, jh, hp⟩) := rfl

theorem stepInvokeStatic_uint_ctor {pc : Nat} {stk : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap} :
    stepInvokeStaticGeneric hooks ⟨pc, stk, locs, jh, hp⟩
        "kotlin/UInt" "constructor-impl" "(I)I" =
      .inl (some ⟨pc + 1, stk, locs, jh, hp⟩) := rfl

theorem stepInvokeStatic_uint_box {pc : Nat} {v : UInt32} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap} :
    stepInvokeStaticGeneric hooks ⟨pc, .i32 v :: stkRest, locs, jh, hp⟩
        "kotlin/UInt" "box-impl" "(I)Lkotlin/UInt;" =
      .inl (some ⟨pc + 1, .boxedUInt v :: stkRest, locs, jh, hp⟩) := rfl

theorem stepInvokeStatic_ulong_ctor {pc : Nat} {stk : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap} :
    stepInvokeStaticGeneric hooks ⟨pc, stk, locs, jh, hp⟩
        "kotlin/ULong" "constructor-impl" "(J)J" =
      .inl (some ⟨pc + 1, stk, locs, jh, hp⟩) := rfl

theorem stepInvokeStatic_ulong_box {pc : Nat} {v : UInt64} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap} :
    stepInvokeStaticGeneric hooks ⟨pc, .i64 v :: stkRest, locs, jh, hp⟩
        "kotlin/ULong" "box-impl" "(J)Lkotlin/ULong;" =
      .inl (some ⟨pc + 1, .boxedULong v :: stkRest, locs, jh, hp⟩) := rfl

theorem stepInvokeStatic_ubyte_ctor {pc : Nat} {stk : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap} :
    stepInvokeStaticGeneric hooks ⟨pc, stk, locs, jh, hp⟩
        "kotlin/UByte" "constructor-impl" "(B)B" =
      .inl (some ⟨pc + 1, stk, locs, jh, hp⟩) := rfl

theorem stepInvokeStatic_integer_valueOf {pc : Nat} {v : UInt32} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap} :
    stepInvokeStaticGeneric hooks ⟨pc, .i32 v :: stkRest, locs, jh, hp⟩
        "java/lang/Integer" "valueOf" "(I)Ljava/lang/Integer;" =
      .inl (some ⟨pc + 1, .boxedInt v :: stkRest, locs, jh, hp⟩) := rfl

theorem stepInvokeStatic_integer_compareUnsigned {pc : Nat} {b a : UInt32} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap} :
    stepInvokeStaticGeneric hooks ⟨pc, .i32 b :: .i32 a :: stkRest, locs, jh, hp⟩
        "java/lang/Integer" "compareUnsigned" "(II)I" =
      .inl (some ⟨pc + 1,
        .i32 (if a == b then 0 else if a < b then 4294967295 else 1) :: stkRest,
        locs, jh, hp⟩) := rfl

theorem stepInvokeStatic_integer_divideUnsigned {pc : Nat} {b a : UInt32} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap} (hb : (b == 0) = false) :
    stepInvokeStaticGeneric hooks ⟨pc, .i32 b :: .i32 a :: stkRest, locs, jh, hp⟩
        "java/lang/Integer" "divideUnsigned" "(II)I" =
      .inl (some ⟨pc + 1, .i32 (a / b) :: stkRest, locs, jh, hp⟩) := by
  simp [stepInvokeStaticGeneric, hb]

theorem stepInvokeStatic_long_compareUnsigned {pc : Nat} {b a : UInt64} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap} :
    stepInvokeStaticGeneric hooks ⟨pc, .i64 b :: .i64 a :: stkRest, locs, jh, hp⟩
        "java/lang/Long" "compareUnsigned" "(JJ)I" =
      .inl (some ⟨pc + 1,
        .i32 (if a == b then 0 else if a < b then 4294967295 else 1) :: stkRest,
        locs, jh, hp⟩) := rfl

theorem stepInvokeStatic_intrinsics_compare {pc : Nat} {b a : UInt32} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap} :
    stepInvokeStaticGeneric hooks ⟨pc, .i32 b :: .i32 a :: stkRest, locs, jh, hp⟩
        "kotlin/jvm/internal/Intrinsics" "compare" "(II)I" =
      .inl (some ⟨pc + 1,
        .i32 (if a == b then 0
              else if a.toBitVec.slt b.toBitVec then 4294967295 else 1) :: stkRest,
        locs, jh, hp⟩) := rfl

theorem stepInvokeStatic_intrinsics_checkNotNull {pc : Nat} {msg obj : JvmVal Ext} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap} (hnull : obj.isNull = false) :
    stepInvokeStaticGeneric hooks ⟨pc, msg :: obj :: stkRest, locs, jh, hp⟩
        "kotlin/jvm/internal/Intrinsics" "checkNotNull" "(Ljava/lang/Object;Ljava/lang/String;)V" =
      .inl (some ⟨pc + 1, stkRest, locs, jh, hp⟩) := by
  simp [stepInvokeStaticGeneric, hnull]

theorem stepInvokeStatic_intrinsics_checkNotNullParam {pc : Nat} {msg obj : JvmVal Ext} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap} (hnull : obj.isNull = false) :
    stepInvokeStaticGeneric hooks ⟨pc, msg :: obj :: stkRest, locs, jh, hp⟩
        "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter" "(Ljava/lang/Object;Ljava/lang/String;)V" =
      .inl (some ⟨pc + 1, stkRest, locs, jh, hp⟩) := by
  simp [stepInvokeStaticGeneric, hnull]

theorem stepInvokeStatic_intrinsics_checkNotNullExpr {pc : Nat} {msg obj : JvmVal Ext} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap} (hnull : obj.isNull = false) :
    stepInvokeStaticGeneric hooks ⟨pc, msg :: obj :: stkRest, locs, jh, hp⟩
        "kotlin/jvm/internal/Intrinsics" "checkNotNullExpressionValue" "(Ljava/lang/Object;Ljava/lang/String;)V" =
      .inl (some ⟨pc + 1, stkRest, locs, jh, hp⟩) := by
  simp [stepInvokeStaticGeneric, hnull]

theorem stepInvokeStatic_strings_encodeToByteArray {pc : Nat} {s : String} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap} :
    stepInvokeStaticGeneric hooks ⟨pc, .str s :: stkRest, locs, jh, hp⟩
        "kotlin/text/StringsKt" "encodeToByteArray" "(Ljava/lang/String;)[B" =
      .inl (some ⟨pc + 1, .heapRef jh.objects.size :: stkRest, locs,
        (jh.alloc (.byteArray s.toUTF8.data)).2, hp⟩) := rfl

theorem stepInvokeStatic_string_valueOf_int {pc : Nat} {v : UInt32} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap} :
    stepInvokeStaticGeneric hooks ⟨pc, .i32 v :: stkRest, locs, jh, hp⟩
        "java/lang/String" "valueOf" "(I)Ljava/lang/String;" =
      .inl (some ⟨pc + 1, .str (i32ToDecimalString v) :: stkRest, locs, jh, hp⟩) := rfl

theorem stepInvokeStatic_arrays_copyOf_obj {pc : Nat} {newLen : UInt32} {addr : Nat} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    {elemCls : String} {elems : Array (JvmVal Ext)}
    (hslt : newLen.toBitVec.slt 0#32 = false)
    (hget : jh.get? addr = some (.objArray elemCls elems)) :
    stepInvokeStaticGeneric hooks ⟨pc, .i32 newLen :: .heapRef addr :: stkRest, locs, jh, hp⟩
        "java/util/Arrays" "copyOf" "([Ljava/lang/Object;I)[Ljava/lang/Object;" =
      let copied := Array.ofFn (n := newLen.toNat)
        (fun i => if h : i.val < elems.size then elems[i.val] else .null)
      .inl (some ⟨pc + 1, .heapRef jh.objects.size :: stkRest, locs,
        (jh.alloc (.objArray elemCls copied)).2, hp⟩) := by
  simp only [stepInvokeStaticGeneric, JvmVal.asI32?_i32, hslt, hget, JvmHeap.alloc]
  rfl

/-! ### Direct `runJvmValFast` / `runJvmResFast` Non-Branch & Branch Helpers -/

theorem runJvmValFast_baload {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {idx : UInt32} {addr : Nat} {stkRest : List (JvmVal Ext)} {rest : List JvmInstr} {pc0 : Nat}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap} {elems : Array UInt8}
    (hget : jh.get? addr = some (.byteArray elems))
    (hslt : idx.toBitVec.slt 0#32 = false) (hlt : idx.toNat < elems.size) :
    runJvmValFast hooks (f + 1) prog pc (.baload :: rest)
        ⟨pc0, .i32 idx :: .heapRef addr :: stkRest, locs, jh, hp⟩ =
      runJvmValFast hooks f prog (pc + 1) rest
        ⟨pc + 1, .i32 (UInt32.ofBitVec (BitVec.signExtend 32 elems[idx.toNat].toBitVec)) :: stkRest,
          locs, jh, hp⟩ :=
  runJvmValFast_step_of_stepInstr hooks rfl (by simp)
    (stepInstr_baload hooks hget hslt hlt) rfl

theorem runJvmResFast_baload {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {idx : UInt32} {addr : Nat} {stkRest : List (JvmVal Ext)} {rest : List JvmInstr} {pc0 : Nat}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap} {elems : Array UInt8}
    (hget : jh.get? addr = some (.byteArray elems))
    (hslt : idx.toBitVec.slt 0#32 = false) (hlt : idx.toNat < elems.size) :
    runJvmResFast hooks (f + 1) prog pc (.baload :: rest)
        ⟨pc0, .i32 idx :: .heapRef addr :: stkRest, locs, jh, hp⟩ =
      runJvmResFast hooks f prog (pc + 1) rest
        ⟨pc + 1, .i32 (UInt32.ofBitVec (BitVec.signExtend 32 elems[idx.toNat].toBitVec)) :: stkRest,
          locs, jh, hp⟩ :=
  runJvmResFast_step_of_stepInstr hooks rfl (by simp)
    (stepInstr_baload hooks hget hslt hlt) rfl

theorem runJvmValFast_aaload {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {idx : UInt32} {addr : Nat} {stkRest : List (JvmVal Ext)} {rest : List JvmInstr} {pc0 : Nat}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap} {cls : String} {elems : Array (JvmVal Ext)}
    (hget : jh.get? addr = some (.objArray cls elems))
    (hslt : idx.toBitVec.slt 0#32 = false) (hlt : idx.toNat < elems.size) :
    runJvmValFast hooks (f + 1) prog pc (.aaload :: rest)
        ⟨pc0, .i32 idx :: .heapRef addr :: stkRest, locs, jh, hp⟩ =
      runJvmValFast hooks f prog (pc + 1) rest ⟨pc + 1, elems[idx.toNat] :: stkRest, locs, jh, hp⟩ :=
  runJvmValFast_step_of_stepInstr hooks rfl (by simp)
    (stepInstr_aaload hooks hget hslt hlt) rfl

theorem runJvmResFast_aaload {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {idx : UInt32} {addr : Nat} {stkRest : List (JvmVal Ext)} {rest : List JvmInstr} {pc0 : Nat}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap} {cls : String} {elems : Array (JvmVal Ext)}
    (hget : jh.get? addr = some (.objArray cls elems))
    (hslt : idx.toBitVec.slt 0#32 = false) (hlt : idx.toNat < elems.size) :
    runJvmResFast hooks (f + 1) prog pc (.aaload :: rest)
        ⟨pc0, .i32 idx :: .heapRef addr :: stkRest, locs, jh, hp⟩ =
      runJvmResFast hooks f prog (pc + 1) rest ⟨pc + 1, elems[idx.toNat] :: stkRest, locs, jh, hp⟩ :=
  runJvmResFast_step_of_stepInstr hooks rfl (by simp)
    (stepInstr_aaload hooks hget hslt hlt) rfl

theorem runJvmResFast_bastore {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {v idx : UInt32} {addr : Nat} {stkRest : List (JvmVal Ext)} {rest : List JvmInstr} {pc0 : Nat}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap} {elems : Array UInt8}
    (hget : jh.get? addr = some (.byteArray elems))
    (hslt : idx.toBitVec.slt 0#32 = false) (hlt : idx.toNat < elems.size) :
    runJvmResFast hooks (f + 1) prog pc (.bastore :: rest)
        ⟨pc0, .i32 v :: .i32 idx :: .heapRef addr :: stkRest, locs, jh, hp⟩ =
      runJvmResFast hooks f prog (pc + 1) rest
        ⟨pc + 1, stkRest, locs, jh.set addr (.byteArray (elems.set idx.toNat v.toUInt8 hlt)), hp⟩ :=
  runJvmResFast_step_of_stepInstr hooks rfl (by simp)
    (stepInstr_bastore hooks hget hslt hlt) rfl

theorem runJvmResFast_newarray_byte {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {n : UInt32} {stkRest : List (JvmVal Ext)} {rest : List JvmInstr} {pc0 : Nat}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    (hslt : n.toBitVec.slt 0#32 = false) :
    runJvmResFast hooks (f + 1) prog pc (.newarray "byte" :: rest)
        ⟨pc0, .i32 n :: stkRest, locs, jh, hp⟩ =
      runJvmResFast hooks f prog (pc + 1) rest
        ⟨pc + 1, .heapRef jh.objects.size :: stkRest, locs,
          (jh.alloc (.byteArray (Array.replicate n.toNat 0))).2, hp⟩ :=
  runJvmResFast_step_of_stepInstr hooks rfl (by simp)
    (stepInstr_newarray_byte hooks hslt) rfl

theorem runJvmResFast_iaload {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {idx : UInt32} {addr : Nat} {stkRest : List (JvmVal Ext)} {rest : List JvmInstr} {pc0 : Nat}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap} {elems : Array UInt32}
    (hget : jh.get? addr = some (.intArray elems))
    (hslt : idx.toBitVec.slt 0#32 = false) (hlt : idx.toNat < elems.size) :
    runJvmResFast hooks (f + 1) prog pc (.iaload :: rest)
        ⟨pc0, .i32 idx :: .heapRef addr :: stkRest, locs, jh, hp⟩ =
      runJvmResFast hooks f prog (pc + 1) rest ⟨pc + 1, .i32 elems[idx.toNat] :: stkRest, locs, jh, hp⟩ :=
  runJvmResFast_step_of_stepInstr hooks rfl (by simp)
    (stepInstr_iaload hooks hget hslt hlt) rfl

theorem runJvmResFast_iastore {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {v idx : UInt32} {addr : Nat} {stkRest : List (JvmVal Ext)} {rest : List JvmInstr} {pc0 : Nat}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap} {elems : Array UInt32}
    (hget : jh.get? addr = some (.intArray elems))
    (hslt : idx.toBitVec.slt 0#32 = false) (hlt : idx.toNat < elems.size) :
    runJvmResFast hooks (f + 1) prog pc (.iastore :: rest)
        ⟨pc0, .i32 v :: .i32 idx :: .heapRef addr :: stkRest, locs, jh, hp⟩ =
      runJvmResFast hooks f prog (pc + 1) rest
        ⟨pc + 1, stkRest, locs, jh.set addr (.intArray (elems.set idx.toNat v hlt)), hp⟩ :=
  runJvmResFast_step_of_stepInstr hooks rfl (by simp)
    (stepInstr_iastore hooks hget hslt hlt) rfl

theorem runJvmResFast_newarray_int {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {n : UInt32} {stkRest : List (JvmVal Ext)} {rest : List JvmInstr} {pc0 : Nat}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    (hslt : n.toBitVec.slt 0#32 = false) :
    runJvmResFast hooks (f + 1) prog pc (.newarray "int" :: rest)
        ⟨pc0, .i32 n :: stkRest, locs, jh, hp⟩ =
      runJvmResFast hooks f prog (pc + 1) rest
        ⟨pc + 1, .heapRef jh.objects.size :: stkRest, locs,
          (jh.alloc (.intArray (Array.replicate n.toNat 0))).2, hp⟩ :=
  runJvmResFast_step_of_stepInstr hooks rfl (by simp)
    (stepInstr_newarray_int hooks hslt) rfl

theorem runJvmResFast_anewarray {f : Nat} {prog : List JvmInstr} {pc : Nat} {cls : String}
    {n : UInt32} {stkRest : List (JvmVal Ext)} {rest : List JvmInstr} {pc0 : Nat}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    (hslt : n.toBitVec.slt 0#32 = false) :
    runJvmResFast hooks (f + 1) prog pc (.anewarray cls :: rest)
        ⟨pc0, .i32 n :: stkRest, locs, jh, hp⟩ =
      runJvmResFast hooks f prog (pc + 1) rest
        ⟨pc + 1, .heapRef jh.objects.size :: stkRest, locs,
          (jh.alloc (.objArray cls (Array.replicate n.toNat .null))).2, hp⟩ :=
  runJvmResFast_step_of_stepInstr hooks rfl (by simp)
    (stepInstr_anewarray hooks cls hslt) rfl

theorem runJvmValFast_arraylength_obj {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {rest : List JvmInstr} {pc0 addr : Nat} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    {cls : String} {elems : Array (JvmVal Ext)}
    (hget : jh.get? addr = some (.objArray cls elems)) :
    runJvmValFast hooks (f + 1) prog pc (.arraylength :: rest)
        ⟨pc0, .heapRef addr :: stkRest, locs, jh, hp⟩ =
      runJvmValFast hooks f prog (pc + 1) rest
        ⟨pc + 1, .i32 (UInt32.ofNat elems.size) :: stkRest, locs, jh, hp⟩ :=
  runJvmValFast_step_of_stepInstr hooks rfl (by simp)
    (stepInstr_arraylength_obj hooks hget) rfl

theorem runJvmResFast_arraylength_obj {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {rest : List JvmInstr} {pc0 addr : Nat} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    {cls : String} {elems : Array (JvmVal Ext)}
    (hget : jh.get? addr = some (.objArray cls elems)) :
    runJvmResFast hooks (f + 1) prog pc (.arraylength :: rest)
        ⟨pc0, .heapRef addr :: stkRest, locs, jh, hp⟩ =
      runJvmResFast hooks f prog (pc + 1) rest
        ⟨pc + 1, .i32 (UInt32.ofNat elems.size) :: stkRest, locs, jh, hp⟩ :=
  runJvmResFast_step_of_stepInstr hooks rfl (by simp)
    (stepInstr_arraylength_obj hooks hget) rfl

theorem runJvmValFast_arraylength_byte {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {rest : List JvmInstr} {pc0 addr : Nat} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap} {elems : Array UInt8}
    (hget : jh.get? addr = some (.byteArray elems)) :
    runJvmValFast hooks (f + 1) prog pc (.arraylength :: rest)
        ⟨pc0, .heapRef addr :: stkRest, locs, jh, hp⟩ =
      runJvmValFast hooks f prog (pc + 1) rest
        ⟨pc + 1, .i32 (UInt32.ofNat elems.size) :: stkRest, locs, jh, hp⟩ :=
  runJvmValFast_step_of_stepInstr hooks rfl (by simp)
    (stepInstr_arraylength_byte hooks hget) rfl

theorem runJvmResFast_arraylength_byte {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {rest : List JvmInstr} {pc0 addr : Nat} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap} {elems : Array UInt8}
    (hget : jh.get? addr = some (.byteArray elems)) :
    runJvmResFast hooks (f + 1) prog pc (.arraylength :: rest)
        ⟨pc0, .heapRef addr :: stkRest, locs, jh, hp⟩ =
      runJvmResFast hooks f prog (pc + 1) rest
        ⟨pc + 1, .i32 (UInt32.ofNat elems.size) :: stkRest, locs, jh, hp⟩ :=
  runJvmResFast_step_of_stepInstr hooks rfl (by simp)
    (stepInstr_arraylength_byte hooks hget) rfl

theorem runJvmValFast_checkcast_objArray {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {rest : List JvmInstr} {pc0 addr : Nat} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    {cls targetCls : String} {elems : Array (JvmVal Ext)}
    (hget : jh.get? addr = some (.objArray cls elems))
    (hm : HeapObj.matchesType hooks.isSubtypeOf targetCls (.objArray cls elems) = true) :
    runJvmValFast hooks (f + 1) prog pc (.checkcast targetCls :: rest)
        ⟨pc0, .heapRef addr :: stkRest, locs, jh, hp⟩ =
      runJvmValFast hooks f prog (pc + 1) rest ⟨pc + 1, .heapRef addr :: stkRest, locs, jh, hp⟩ :=
  runJvmValFast_step_of_stepInstr hooks rfl (by simp)
    (stepInstr_checkcast_objArray hooks hget hm) rfl

theorem runJvmResFast_checkcast_objArray {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {rest : List JvmInstr} {pc0 addr : Nat} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    {cls targetCls : String} {elems : Array (JvmVal Ext)}
    (hget : jh.get? addr = some (.objArray cls elems))
    (hm : HeapObj.matchesType hooks.isSubtypeOf targetCls (.objArray cls elems) = true) :
    runJvmResFast hooks (f + 1) prog pc (.checkcast targetCls :: rest)
        ⟨pc0, .heapRef addr :: stkRest, locs, jh, hp⟩ =
      runJvmResFast hooks f prog (pc + 1) rest ⟨pc + 1, .heapRef addr :: stkRest, locs, jh, hp⟩ :=
  runJvmResFast_step_of_stepInstr hooks rfl (by simp)
    (stepInstr_checkcast_objArray hooks hget hm) rfl

theorem runJvmResFast_goto {f1 pc target : Nat} {prog rest : List JvmInstr}
    {stk : List (JvmVal Ext)} {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap} :
    runJvmResFast hooks (f1 + 1) prog pc (.goto target :: rest) ⟨pc, stk, locs, jh, hp⟩ =
      runJvmResFast hooks f1 prog target (prog.drop target) ⟨target, stk, locs, jh, hp⟩ := by
  rw [runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  simp [evalResBranchInstrCons, isBranchInstr, dispatchBranch]

theorem runJvmResFast_iflt_branch {f1 pc target : Nat} {prog rest : List JvmInstr}
    {x : UInt32} {srest : List (JvmVal Ext)} {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    (h : x.toBitVec.slt 0#32 = true) :
    runJvmResFast hooks (f1 + 1) prog pc (.iflt target :: rest) ⟨pc, .i32 x :: srest, locs, jh, hp⟩ =
      runJvmResFast hooks f1 prog target (prog.drop target) ⟨target, srest, locs, jh, hp⟩ := by
  rw [runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  simp [evalResBranchInstrCons, isBranchInstr, dispatchBranch, h]

theorem runJvmResFast_iflt_fallthrough {f1 pc target : Nat} {prog rest : List JvmInstr}
    {x : UInt32} {srest : List (JvmVal Ext)} {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    (h : x.toBitVec.slt 0#32 = false) :
    runJvmResFast hooks (f1 + 1) prog pc (.iflt target :: rest) ⟨pc, .i32 x :: srest, locs, jh, hp⟩ =
      runJvmResFast hooks f1 prog (pc + 1) rest ⟨pc + 1, srest, locs, jh, hp⟩ := by
  rw [runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  simp [evalResBranchInstrCons, isBranchInstr, dispatchBranch, h]

theorem runJvmResFast_ifle_branch {f1 pc target : Nat} {prog rest : List JvmInstr}
    {x : UInt32} {srest : List (JvmVal Ext)} {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    (h : x.toBitVec.sle 0#32 = true) :
    runJvmResFast hooks (f1 + 1) prog pc (.ifle target :: rest) ⟨pc, .i32 x :: srest, locs, jh, hp⟩ =
      runJvmResFast hooks f1 prog target (prog.drop target) ⟨target, srest, locs, jh, hp⟩ := by
  rw [runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  simp [evalResBranchInstrCons, isBranchInstr, dispatchBranch, h]

theorem runJvmResFast_ifle_fallthrough {f1 pc target : Nat} {prog rest : List JvmInstr}
    {x : UInt32} {srest : List (JvmVal Ext)} {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    (h : x.toBitVec.sle 0#32 = false) :
    runJvmResFast hooks (f1 + 1) prog pc (.ifle target :: rest) ⟨pc, .i32 x :: srest, locs, jh, hp⟩ =
      runJvmResFast hooks f1 prog (pc + 1) rest ⟨pc + 1, srest, locs, jh, hp⟩ := by
  rw [runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  simp [evalResBranchInstrCons, isBranchInstr, dispatchBranch, h]

theorem runJvmResFast_ifeq_branch [HasDefaultIsZero hooks]
    {f1 pc target : Nat} {prog rest : List JvmInstr}
    {x : UInt32} {srest : List (JvmVal Ext)} {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    (h : x = 0) :
    runJvmResFast hooks (f1 + 1) prog pc (.ifeq target :: rest) ⟨pc, .i32 x :: srest, locs, jh, hp⟩ =
      runJvmResFast hooks f1 prog target (prog.drop target) ⟨target, srest, locs, jh, hp⟩ := by
  rw [runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  simp [evalResBranchInstrCons, isBranchInstr, dispatchBranch, HasDefaultIsZero.isZero?_eq (hooks := hooks), h]

theorem runJvmResFast_ifeq_fallthrough [HasDefaultIsZero hooks]
    {f1 pc target : Nat} {prog rest : List JvmInstr}
    {x : UInt32} {srest : List (JvmVal Ext)} {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    (h : (x == 0) = false) :
    runJvmResFast hooks (f1 + 1) prog pc (.ifeq target :: rest) ⟨pc, .i32 x :: srest, locs, jh, hp⟩ =
      runJvmResFast hooks f1 prog (pc + 1) rest ⟨pc + 1, srest, locs, jh, hp⟩ := by
  rw [runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  simp [evalResBranchInstrCons, isBranchInstr, dispatchBranch, HasDefaultIsZero.isZero?_eq (hooks := hooks), h]

theorem runJvmResFast_ifne_branch [HasDefaultIsZero hooks]
    {f1 pc target : Nat} {prog rest : List JvmInstr}
    {x : UInt32} {srest : List (JvmVal Ext)} {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    (h : (x == 0) = false) :
    runJvmResFast hooks (f1 + 1) prog pc (.ifne target :: rest) ⟨pc, .i32 x :: srest, locs, jh, hp⟩ =
      runJvmResFast hooks f1 prog target (prog.drop target) ⟨target, srest, locs, jh, hp⟩ := by
  rw [runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  simp [evalResBranchInstrCons, isBranchInstr, dispatchBranch, HasDefaultIsZero.isZero?_eq (hooks := hooks), h]

theorem runJvmResFast_ifne_fallthrough [HasDefaultIsZero hooks]
    {f1 pc target : Nat} {prog rest : List JvmInstr}
    {x : UInt32} {srest : List (JvmVal Ext)} {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    (h : x = 0) :
    runJvmResFast hooks (f1 + 1) prog pc (.ifne target :: rest) ⟨pc, .i32 x :: srest, locs, jh, hp⟩ =
      runJvmResFast hooks f1 prog (pc + 1) rest ⟨pc + 1, srest, locs, jh, hp⟩ := by
  rw [runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  simp [evalResBranchInstrCons, isBranchInstr, dispatchBranch, HasDefaultIsZero.isZero?_eq (hooks := hooks), h]

theorem runJvmResFast_ifnonnull_branch {f1 pc target : Nat} {prog rest : List JvmInstr}
    {v : JvmVal Ext} {srest : List (JvmVal Ext)} {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    (hnn : v.isNull = false) :
    runJvmResFast hooks (f1 + 1) prog pc (.ifnonnull target :: rest) ⟨pc, v :: srest, locs, jh, hp⟩ =
      runJvmResFast hooks f1 prog target (prog.drop target) ⟨target, srest, locs, jh, hp⟩ := by
  rw [runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  simp [evalResBranchInstrCons, isBranchInstr, dispatchBranch, hnn]

theorem runJvmResFast_ifnonnull_fallthrough {f1 pc target : Nat} {prog rest : List JvmInstr}
    {srest : List (JvmVal Ext)} {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap} :
    runJvmResFast hooks (f1 + 1) prog pc (.ifnonnull target :: rest) ⟨pc, .null :: srest, locs, jh, hp⟩ =
      runJvmResFast hooks f1 prog (pc + 1) rest ⟨pc + 1, srest, locs, jh, hp⟩ := by
  rw [runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  simp [evalResBranchInstrCons, isBranchInstr, dispatchBranch, JvmVal.isNull]

theorem runJvmResFast_if_icmpeq_branch {f1 pc target : Nat} {prog rest : List JvmInstr}
    {a b : UInt32} {srest : List (JvmVal Ext)} {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    (h : a = b) :
    runJvmResFast hooks (f1 + 1) prog pc (.if_icmpeq target :: rest)
        ⟨pc, .i32 b :: .i32 a :: srest, locs, jh, hp⟩ =
      runJvmResFast hooks f1 prog target (prog.drop target) ⟨target, srest, locs, jh, hp⟩ := by
  rw [runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  simp [evalResBranchInstrCons, isBranchInstr, dispatchBranch, h]

theorem runJvmResFast_if_icmpeq_fallthrough {f1 pc target : Nat} {prog rest : List JvmInstr}
    {a b : UInt32} {srest : List (JvmVal Ext)} {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    (h : a ≠ b) :
    runJvmResFast hooks (f1 + 1) prog pc (.if_icmpeq target :: rest)
        ⟨pc, .i32 b :: .i32 a :: srest, locs, jh, hp⟩ =
      runJvmResFast hooks f1 prog (pc + 1) rest ⟨pc + 1, srest, locs, jh, hp⟩ := by
  rw [runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  simp [evalResBranchInstrCons, isBranchInstr, dispatchBranch, h]

theorem runJvmResFast_if_icmpne_branch {f1 pc target : Nat} {prog rest : List JvmInstr}
    {a b : UInt32} {srest : List (JvmVal Ext)} {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    (h : a ≠ b) :
    runJvmResFast hooks (f1 + 1) prog pc (.if_icmpne target :: rest)
        ⟨pc, .i32 b :: .i32 a :: srest, locs, jh, hp⟩ =
      runJvmResFast hooks f1 prog target (prog.drop target) ⟨target, srest, locs, jh, hp⟩ := by
  rw [runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  simp [evalResBranchInstrCons, isBranchInstr, dispatchBranch, h]

theorem runJvmResFast_if_icmpne_fallthrough {f1 pc target : Nat} {prog rest : List JvmInstr}
    {a b : UInt32} {srest : List (JvmVal Ext)} {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    (h : a = b) :
    runJvmResFast hooks (f1 + 1) prog pc (.if_icmpne target :: rest)
        ⟨pc, .i32 b :: .i32 a :: srest, locs, jh, hp⟩ =
      runJvmResFast hooks f1 prog (pc + 1) rest ⟨pc + 1, srest, locs, jh, hp⟩ := by
  rw [runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  simp [evalResBranchInstrCons, isBranchInstr, dispatchBranch, h]

theorem runJvmResFast_if_icmplt_branch {f1 pc target : Nat} {prog rest : List JvmInstr}
    {a b : UInt32} {srest : List (JvmVal Ext)} {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    (h : a.toBitVec.slt b.toBitVec = true) :
    runJvmResFast hooks (f1 + 1) prog pc (.if_icmplt target :: rest)
        ⟨pc, .i32 b :: .i32 a :: srest, locs, jh, hp⟩ =
      runJvmResFast hooks f1 prog target (prog.drop target) ⟨target, srest, locs, jh, hp⟩ := by
  rw [runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  simp [evalResBranchInstrCons, isBranchInstr, dispatchBranch, h]

theorem runJvmResFast_if_icmplt_fallthrough {f1 pc target : Nat} {prog rest : List JvmInstr}
    {a b : UInt32} {srest : List (JvmVal Ext)} {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    (h : a.toBitVec.slt b.toBitVec = false) :
    runJvmResFast hooks (f1 + 1) prog pc (.if_icmplt target :: rest)
        ⟨pc, .i32 b :: .i32 a :: srest, locs, jh, hp⟩ =
      runJvmResFast hooks f1 prog (pc + 1) rest ⟨pc + 1, srest, locs, jh, hp⟩ := by
  rw [runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  simp [evalResBranchInstrCons, isBranchInstr, dispatchBranch, h]

end GenericFast

end Jvm
