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

/-! ### Family 2a: List.isEmpty, GrowBuf, copyPrefix, AsciiBytes, decodeCharAt___lam__0 -/

private theorem jvmHeap_set_set (jh : Jvm.JvmHeap AlgExt) (a : Nat) (w1 w2 : Jvm.HeapObj AlgExt) :
    (jh.set a w1).set a w2 = jh.set a w2 := by
  simp only [Jvm.JvmHeap.set]
  split
  · next h => simp [Array.size_set, h, Array.set_set]
  · simp

private theorem jvmHeap_set_eq_self {jh : Jvm.JvmHeap AlgExt} {a : Nat} {w : Jvm.HeapObj AlgExt}
    (h : jh.get? a = some w) : jh.set a w = jh := by
  simp only [Jvm.JvmHeap.get?, Array.getElem?_eq_some_iff] at h
  rcases h with ⟨hlt, heq⟩
  subst heq
  simp [Jvm.JvmHeap.set, hlt]

private theorem u8_toUInt32_toUInt8 (v : UInt8) : v.toUInt32.toUInt8 = v := by
  revert v; decide

private theorem u8_setWidth_signExtend (v : UInt8) :
    BitVec.setWidth 8 (BitVec.signExtend 32 v.toBitVec) = v.toBitVec := by
  revert v; decide

/-- `List.isEmpty` checks tag `0` (empty) vs `1` (cons) at index `0` of the heap `Object[]` node. -/
theorem listIsEmpty_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (addr : Nat)
    (elems : Array JvmVal) (tag : UInt32)
    (hget : jh.get? addr = some (.objArray "java/lang/Object" elems))
    (h0 : elems[0]? = some (.boxedInt tag))
    (htag : tag = 0 ∨ tag = 1) :
    runJvm 30 f_List_isEmpty___redArg_prog
      ⟨0, [], setLocal (fun _ => .null) 0 (.heapRef addr), jh, hp⟩ =
      some (.i32 (if tag == 0 then 1 else 0)) := by
  have hlt0 : 0 < elems.size := (Array.getElem?_eq_some_iff.mp h0).1
  have he0 : elems[0]'hlt0 = .boxedInt tag := (Array.getElem?_eq_some_iff.mp h0).2
  rcases htag with rfl | rfl
  · have hts : Jvm.tableswitchTarget 0 0 [13, 15] 17 = 13 := by decide
    rw [runJvm_eq_runJvmRes]
    suffices h : ∃ st', runJvmRes 30 f_List_isEmpty___redArg_prog
        ⟨0, [], setLocal (fun _ => .null) 0 (.heapRef addr), jh, hp⟩ =
        some (.i32 1, st') by
      rcases h with ⟨st', h⟩; rw [h]; rfl
    exact ⟨_, by
      apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
      split_res_fuel 10; heap_step_blk f_List_isEmpty___redArg_prog
      split_res_fuel 1; rw [runJvmResFast_checkcast_objArray hget (Or.inl rfl)]
      split_res_fuel 10; heap_step_blk f_List_isEmpty___redArg_prog
      split_res_fuel 1
      rw [runJvmResFast_aaload (idx := 0) hget (by decide) hlt0, show elems[(0 : UInt32).toNat]'hlt0 = .boxedInt 0 from he0]
      split_res_fuel 10; heap_step_blk f_List_isEmpty___redArg_prog
      split_res_fuel 1; rw [runJvmResFast_checkcast_boxedInt (Or.inl rfl)]
      split_res_fuel 10; heap_step_blk f_List_isEmpty___redArg_prog
      rw [hts]; dsimp only; rfl⟩
  · have hts : Jvm.tableswitchTarget 1 0 [13, 15] 17 = 15 := by decide
    rw [runJvm_eq_runJvmRes]
    suffices h : ∃ st', runJvmRes 30 f_List_isEmpty___redArg_prog
        ⟨0, [], setLocal (fun _ => .null) 0 (.heapRef addr), jh, hp⟩ =
        some (.i32 0, st') by
      rcases h with ⟨st', h⟩; rw [h]; rfl
    exact ⟨_, by
      apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
      split_res_fuel 10; heap_step_blk f_List_isEmpty___redArg_prog
      split_res_fuel 1; rw [runJvmResFast_checkcast_objArray hget (Or.inl rfl)]
      split_res_fuel 10; heap_step_blk f_List_isEmpty___redArg_prog
      split_res_fuel 1
      rw [runJvmResFast_aaload (idx := 0) hget (by decide) hlt0, show elems[(0 : UInt32).toNat]'hlt0 = .boxedInt 1 from he0]
      split_res_fuel 10; heap_step_blk f_List_isEmpty___redArg_prog
      split_res_fuel 1; rw [runJvmResFast_checkcast_boxedInt (Or.inl rfl)]
      split_res_fuel 10; heap_step_blk f_List_isEmpty___redArg_prog
      rw [hts]; dsimp only; rfl⟩

private theorem growBufEmpty_core (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (arg0 : JvmVal) :
    let jh1 := (jh.alloc (.objArray "java/lang/Object" #[])).2
    let jh2 := (jh1.alloc (.objArray "java/lang/Object"
      #[.boxedInt 0, .heapRef jh.objects.size, .boxedUInt 0])).2
    ∃ st', runJvmRes 30 f_Algorithm_GrowBuf_empty___redArg_prog
        ⟨0, [], setLocal (fun _ => .null) 0 arg0, jh, hp⟩ =
      some (.heapRef (jh.objects.size + 1), st') ∧ st'.jvmHeap = jh2 := by
  have hrep0 : (Array.replicate 0 JvmVal.null : Array JvmVal) = #[] := rfl
  let jh1 := (jh.alloc (.objArray "java/lang/Object" (Array.replicate (0 : UInt32).toNat .null))).2
  let jh2_0 := (jh1.alloc (.objArray "java/lang/Object" (Array.replicate (3 : UInt32).toNat .null))).2
  let jh2_1 := jh2_0.set jh1.objects.size (.objArray "java/lang/Object"
    ((Array.replicate (3 : UInt32).toNat .null).set 0 (.boxedInt 0)))
  let jh2_2 := jh2_1.set jh1.objects.size (.objArray "java/lang/Object"
    (((Array.replicate (3 : UInt32).toNat .null).set 0 (.boxedInt 0)).set 1 (.heapRef jh.objects.size)))
  have h1 : jh2_0.get? jh1.objects.size =
      some (.objArray "java/lang/Object" (Array.replicate (3 : UInt32).toNat .null)) :=
    jvmHeap_get?_alloc_self _ _
  have h2 : jh2_1.get? jh1.objects.size =
      some (.objArray "java/lang/Object" ((Array.replicate (3 : UInt32).toNat .null).set 0 (.boxedInt 0))) :=
    jvmHeap_get?_set_self h1
  have h3 : jh2_2.get? jh1.objects.size =
      some (.objArray "java/lang/Object"
        (((Array.replicate (3 : UInt32).toNat .null).set 0 (.boxedInt 0)).set 1 (.heapRef jh.objects.size))) :=
    jvmHeap_get?_set_self h2
  have hsz1 : jh1.objects.size = jh.objects.size + 1 := by simp [jh1, Jvm.JvmHeap.alloc]
  exact ⟨_, by
    apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
    split_res_fuel 10; heap_step_blk f_Algorithm_GrowBuf_empty___redArg_prog
    split_res_fuel 1; rw [runJvmResFast_anewarray_obj (by decide)]
    split_res_fuel 10; heap_step_blk f_Algorithm_GrowBuf_empty___redArg_prog
    split_res_fuel 1; rw [runJvmResFast_anewarray_obj (by decide)]
    change runJvmResFast _ _ _ _ ⟨_, _, _, jh2_0, _⟩ = _
    split_res_fuel 10; heap_step_blk f_Algorithm_GrowBuf_empty___redArg_prog
    split_res_fuel 1; rw [runJvmResFast_aastore (idx := 0) h1 (by decide) (by decide)]
    change runJvmResFast _ _ _ _ ⟨_, _, _, jh2_1, _⟩ = _
    split_res_fuel 10; heap_step_blk f_Algorithm_GrowBuf_empty___redArg_prog
    split_res_fuel 1; rw [runJvmResFast_aastore (idx := 1) h2 (by decide) (by decide)]
    change runJvmResFast _ _ _ _ ⟨_, _, _, jh2_2, _⟩ = _
    split_res_fuel 10; heap_step_blk f_Algorithm_GrowBuf_empty___redArg_prog
    split_res_fuel 1; rw [runJvmResFast_aastore (idx := 2) h3 (by decide) (by simp)]
    split_res_fuel 10; heap_step_blk f_Algorithm_GrowBuf_empty___redArg_prog; dsimp only; rw [hsz1], by
    have harr : (((Array.replicate (3 : UInt32).toNat (JvmVal.null : Jvm.JvmVal AlgExt)).set
        (0 : Nat) (JvmVal.boxedInt 0)).set
        (1 : Nat) (Jvm.JvmVal.heapRef jh.objects.size)).set
        (2 : UInt32).toNat (JvmVal.boxedUInt 0) =
        #[JvmVal.boxedInt 0, Jvm.JvmVal.heapRef jh.objects.size, JvmVal.boxedUInt 0] := by
      simp [Array.replicate, Array.set]
    change jh2_2.set (jh.objects.size + 1) _ = _
    dsimp only [jh2_2, jh2_1]
    rw [← hsz1]
    rw [jvmHeap_set_set, jvmHeap_set_set, harr]
    dsimp only [jh2_0, jh1]
    rw [show (Array.replicate (0 : UInt32).toNat JvmVal.null) = #[] from hrep0]
    simp only [Jvm.JvmHeap.set, Jvm.JvmHeap.alloc, Array.size_push, Nat.lt_add_one, ↓reduceDIte]
    congr 1
    apply Array.ext (by simp)
    intro k hk1 hk2
    simp only [Array.size_push, Array.size_set] at hk1 hk2
    simp only [Array.getElem_set, Array.getElem_push, Array.size_push]
    split
    · split <;> first | rfl | omega
    · split <;> first | rfl | omega⟩

/-- `GrowBuf.empty` allocates an empty backing `Object[]` and a 3-element tuple `[0, data, 0u]`. -/
theorem growBufEmpty_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (arg0 : JvmVal) :
    let (_, jh1) := jh.alloc (.objArray "java/lang/Object" #[])
    let (bufAddr, jh2) := jh1.alloc (.objArray "java/lang/Object"
      #[.boxedInt 0, .heapRef jh.objects.size, .boxedUInt 0])
    ∃ st', runJvmRes 30 f_Algorithm_GrowBuf_empty___redArg_prog
        ⟨0, [], setLocal (fun _ => .null) 0 arg0, jh, hp⟩ =
      some (.heapRef bufAddr, st') ∧ st'.jvmHeap = jh2 := by
  simpa [Jvm.JvmHeap.alloc] using growBufEmpty_core jh hp arg0

theorem growBufEmpty_1_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (arg0 : JvmVal) :
    let (_, jh1) := jh.alloc (.objArray "java/lang/Object" #[])
    let (bufAddr, jh2) := jh1.alloc (.objArray "java/lang/Object"
      #[.boxedInt 0, .heapRef jh.objects.size, .boxedUInt 0])
    ∃ st', runJvmRes 30 f_Algorithm_GrowBuf_empty___redArg_1_prog
        ⟨0, [], setLocal (fun _ => .null) 0 arg0, jh, hp⟩ =
      some (.heapRef bufAddr, st') ∧ st'.jvmHeap = jh2 := by
  rw [show f_Algorithm_GrowBuf_empty___redArg_1_prog = f_Algorithm_GrowBuf_empty___redArg_prog from rfl]
  exact growBufEmpty_equiv jh hp arg0

theorem growBufEmpty_2_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (arg0 : JvmVal) :
    let (_, jh1) := jh.alloc (.objArray "java/lang/Object" #[])
    let (bufAddr, jh2) := jh1.alloc (.objArray "java/lang/Object"
      #[.boxedInt 0, .heapRef jh.objects.size, .boxedUInt 0])
    ∃ st', runJvmRes 30 f_Algorithm_GrowBuf_empty___redArg_2_prog
        ⟨0, [], setLocal (fun _ => .null) 0 arg0, jh, hp⟩ =
      some (.heapRef bufAddr, st') ∧ st'.jvmHeap = jh2 := by
  rw [show f_Algorithm_GrowBuf_empty___redArg_2_prog = f_Algorithm_GrowBuf_empty___redArg_prog from rfl]
  exact growBufEmpty_equiv jh hp arg0

theorem growBufEmpty_3_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (arg0 : JvmVal) :
    let (_, jh1) := jh.alloc (.objArray "java/lang/Object" #[])
    let (bufAddr, jh2) := jh1.alloc (.objArray "java/lang/Object"
      #[.boxedInt 0, .heapRef jh.objects.size, .boxedUInt 0])
    ∃ st', runJvmRes 30 f_Algorithm_GrowBuf_empty___redArg_3_prog
        ⟨0, [], setLocal (fun _ => .null) 0 arg0, jh, hp⟩ =
      some (.heapRef bufAddr, st') ∧ st'.jvmHeap = jh2 := by
  rw [show f_Algorithm_GrowBuf_empty___redArg_3_prog = f_Algorithm_GrowBuf_empty___redArg_prog from rfl]
  exact growBufEmpty_equiv jh hp arg0

theorem growBufEmpty_4_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (arg0 : JvmVal) :
    let (_, jh1) := jh.alloc (.objArray "java/lang/Object" #[])
    let (bufAddr, jh2) := jh1.alloc (.objArray "java/lang/Object"
      #[.boxedInt 0, .heapRef jh.objects.size, .boxedUInt 0])
    ∃ st', runJvmRes 30 f_Algorithm_GrowBuf_empty___redArg_4_prog
        ⟨0, [], setLocal (fun _ => .null) 0 arg0, jh, hp⟩ =
      some (.heapRef bufAddr, st') ∧ st'.jvmHeap = jh2 := by
  rw [show f_Algorithm_GrowBuf_empty___redArg_4_prog = f_Algorithm_GrowBuf_empty___redArg_prog from rfl]
  exact growBufEmpty_equiv jh hp arg0

/-! ### copyPrefix -/

private theorem isArrayElemCompat_set_objArray {jh : Jvm.JvmHeap AlgExt} {addr : Nat}
    {arrCls dstCls : String} {elems0 elems1 : Array JvmVal} {v : JvmVal}
    (hget : jh.get? addr = some (.objArray arrCls elems0)) :
    Jvm.isArrayElemCompat algHooks (jh.set addr (.objArray arrCls elems1)) dstCls v =
      Jvm.isArrayElemCompat algHooks jh dstCls v := by
  cases v <;> try rfl
  rename_i a
  simp only [Jvm.isArrayElemCompat, Jvm.JvmVal.isRef]
  by_cases hobj : dstCls == "java/lang/Object"
  · simp [hobj]
  · simp only [hobj, Bool.false_eq_true, ↓reduceIte, Jvm.evalInstanceOf, Jvm.JvmHeap.checkInstanceOf]
    by_cases ha : a = addr
    · subst ha
      rw [jvmHeap_get?_set_self hget, hget]
      rfl
    · rw [jvmHeap_get?_set_ne jh _ ha]

private theorem copyPrefix_loop (rem fuel : Nat) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (inst : JvmVal) (srcAddr dstAddr : Nat) (srcCls dstCls : String)
    (srcElems dstElems : Array JvmVal) (n i : UInt32) (locs : Nat → JvmVal)
    (hne : srcAddr ≠ dstAddr)
    (hsrc : jh.get? srcAddr = some (.objArray srcCls srcElems))
    (hdst : jh.get? dstAddr = some (.objArray dstCls dstElems))
    (hi : i.toNat ≤ n.toNat) (hn : n.toNat ≤ srcElems.size) (hd : n.toNat ≤ dstElems.size)
    (hn31 : n.toNat < 2 ^ 31)
    (hcompat : ∀ (k : Nat) (hk : k < n.toNat), i.toNat ≤ k →
      Jvm.isArrayElemCompat algHooks jh dstCls (srcElems[k]'(by omega)) = true)
    (hrem : n.toNat - i.toNat ≤ rem) (hf : rem * 35 + 15 ≤ fuel) :
    ∃ st', runJvmResFast fuel f_Algorithm_copyPrefix___redArg_prog 0 f_Algorithm_copyPrefix___redArg_prog
        ⟨0, [], setLocal (setLocal (setLocal (setLocal (setLocal locs 0 inst)
          1 (.heapRef srcAddr)) 2 (.i32 n)) 3 (.i32 i)) 4 (.heapRef dstAddr), jh, hp⟩ =
      some (.unit, st') ∧
      st'.jvmHeap = jh.set dstAddr (.objArray dstCls
        (copyObjArrayPrefix srcElems dstElems n i (n.toNat - i.toNat + 1))) := by
  rcases hp with ⟨ar, u64, asc⟩
  induction rem generalizing i dstElems jh fuel locs with
  | zero =>
    have hieq_nat : i.toNat = n.toNat := by omega
    have hieq : i = n := UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hieq_nat)
    subst hieq
    have hcu : (if i == i then (0 : UInt32) else if i < i then 4294967295 else 1) = 0 := by simp
    exact ⟨_, by
      split_res_fuel 10; heap_step_blk f_Algorithm_copyPrefix___redArg_prog
      simp only [hcu, show (0 : UInt32).toBitVec.slt 0#32 = false from by decide, Bool.false_eq_true, ↓reduceIte]
      rfl, by
      have hltf : ¬(i < i) := UInt32.lt_irrefl i
      simp only [copyObjArrayPrefix, hltf, ↓reduceIte]
      exact (jvmHeap_set_eq_self hdst).symm⟩
  | succ rem ih =>
    by_cases hlt : i < n
    · have hiltn : i.toNat < n.toNat := UInt32.lt_iff_toNat_lt.mp hlt
      have hislt : i.toBitVec.slt 0#32 = false := u32_slt_zero_of_lt_2_31 (by omega)
      have hisrc : i.toNat < srcElems.size := by omega
      have hidst : i.toNat < dstElems.size := by omega
      have hi1 : (i + 1).toNat = i.toNat + 1 := ui32_add1_toNat hlt
      have hcu : (if i == n then (0 : UInt32) else if i < n then 4294967295 else 1) = 4294967295 := by
        have hne_bn : (i == n) = false := beq_false_of_ne (by intro h; subst h; exact Nat.lt_irrefl _ hiltn)
        simp [hne_bn, hlt]
      let dst1 := dstElems.set i.toNat srcElems[i.toNat] hidst
      let jh1 := jh.set dstAddr (.objArray dstCls dst1)
      have hsrc1 : jh1.get? srcAddr = some (.objArray srcCls srcElems) := by
        rw [jvmHeap_get?_set_ne jh _ hne]; exact hsrc
      have hdst1 : jh1.get? dstAddr = some (.objArray dstCls dst1) := jvmHeap_get?_set_self hdst
      let locs1 := setLocal (setLocal (setLocal (setLocal (setLocal
        (setLocal (setLocal (setLocal (setLocal (setLocal locs 0 inst)
          1 (.heapRef srcAddr)) 2 (.i32 n)) 3 (.i32 i)) 4 (.heapRef dstAddr))
        5 (.i32 (i + 1))) 6 inst) 7 (.heapRef srcAddr)) 8 (.i32 n)) 9 (.heapRef dstAddr)
      obtain ⟨st', hrun, hst⟩ := ih (fuel - 34) (i := i + 1) (dstElems := dst1) (jh := jh1) (locs := locs1)
        hsrc1 hdst1 (by omega) (by simp only [dst1, Array.size_set]; exact hd)
        (fun k hk hik => by
          dsimp only [jh1]
          rw [isArrayElemCompat_set_objArray hdst]
          exact hcompat k hk (by omega))
        (by omega) (by omega)
      refine ⟨st', ?_, ?_⟩
      · split_res_fuel 34
        heap_step_blk f_Algorithm_copyPrefix___redArg_prog
        simp only [hcu, show (4294967295 : UInt32).toBitVec.slt 0#32 = true from by decide, ↓reduceIte]
        heap_step_blk f_Algorithm_copyPrefix___redArg_prog
        rw [runJvmResFast_aaload hsrc hislt hisrc]
        rw [runJvmResFast_aastore hdst hislt hidst (hcompat i.toNat hiltn (Nat.le_refl _))]
        heap_step_blk f_Algorithm_copyPrefix___redArg_prog
        exact hrun
      · rw [hst]
        have hsub : n.toNat - i.toNat + 1 = (n.toNat - (i + 1).toNat + 1) + 1 := by omega
        conv => rhs; rw [hsub, copyObjArrayPrefix]
        simp only [hlt, ↓reduceIte]
        dsimp only [jh1]
        rw [jvmHeap_set_set]
        congr 3
        apply Array.ext
        · simp [dst1, Array.size_set]
        · intro k hk1 hk2
          simp only [Array.set!_eq_setIfInBounds]
          rw [Array.getElem_setIfInBounds (by simp [dst1] at hk1; exact hk1)]
          simp only [dst1, Array.getElem_set]
          split
          · rw [Array.getElem?_eq_getElem hisrc, Option.getD_some]
          · rfl
    · have hiltn_neg : ¬(i.toNat < n.toNat) := fun h => hlt (UInt32.lt_iff_toNat_lt.mpr h)
      have hieq_nat : i.toNat = n.toNat := by omega
      have hieq : i = n := UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hieq_nat)
      subst hieq
      have hcu : (if i == i then (0 : UInt32) else if i < i then 4294967295 else 1) = 0 := by simp
      exact ⟨_, by
        split_res_fuel 10; heap_step_blk f_Algorithm_copyPrefix___redArg_prog
        simp only [hcu, show (0 : UInt32).toBitVec.slt 0#32 = false from by decide, Bool.false_eq_true, ↓reduceIte]
        rfl, by
        have hltf : ¬(i < i) := UInt32.lt_irrefl i
        simp only [copyObjArrayPrefix, hltf, ↓reduceIte]
        exact (jvmHeap_set_eq_self hdst).symm⟩

theorem copyPrefix_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (inst : JvmVal) (srcAddr dstAddr : Nat) (srcCls dstCls : String)
    (srcElems dstElems : Array JvmVal) (n i : UInt32)
    (hne : srcAddr ≠ dstAddr)
    (hsrc : jh.get? srcAddr = some (.objArray srcCls srcElems))
    (hdst : jh.get? dstAddr = some (.objArray dstCls dstElems))
    (hi : i.toNat ≤ n.toNat) (hn : n.toNat ≤ srcElems.size) (hd : n.toNat ≤ dstElems.size)
    (hn31 : n.toNat < 2 ^ 31)
    (hcompat : ∀ (k : Nat) (hk : k < n.toNat), i.toNat ≤ k →
      Jvm.isArrayElemCompat algHooks jh dstCls (srcElems[k]'(by omega)) = true) :
    ∃ st', runJvmRes (n.toNat * 35 + 20) f_Algorithm_copyPrefix___redArg_prog
        ⟨0, [], setLocal (setLocal (setLocal (setLocal (setLocal (fun _ => .null) 0 inst)
          1 (.heapRef srcAddr)) 2 (.i32 n)) 3 (.i32 i)) 4 (.heapRef dstAddr), jh, hp⟩ =
      some (.unit, st') ∧
      st'.jvmHeap = jh.set dstAddr (.objArray dstCls
        (copyObjArrayPrefix srcElems dstElems n i (n.toNat - i.toNat + 1))) := by
  obtain ⟨st', hrun, hst⟩ := copyPrefix_loop n.toNat (n.toNat * 35 + 20) jh hp inst srcAddr dstAddr
    srcCls dstCls srcElems dstElems n i _ hne hsrc hdst hi hn hd hn31 hcompat (by omega) (by omega)
  refine ⟨st', ?_, hst⟩
  apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
  exact hrun

theorem copyPrefix_1_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (inst : JvmVal) (srcAddr dstAddr : Nat) (srcCls dstCls : String)
    (srcElems dstElems : Array JvmVal) (n i : UInt32)
    (hne : srcAddr ≠ dstAddr)
    (hsrc : jh.get? srcAddr = some (.objArray srcCls srcElems))
    (hdst : jh.get? dstAddr = some (.objArray dstCls dstElems))
    (hi : i.toNat ≤ n.toNat) (hn : n.toNat ≤ srcElems.size) (hd : n.toNat ≤ dstElems.size)
    (hn31 : n.toNat < 2 ^ 31)
    (hcompat : ∀ (k : Nat) (hk : k < n.toNat), i.toNat ≤ k →
      Jvm.isArrayElemCompat algHooks jh dstCls (srcElems[k]'(by omega)) = true) :
    ∃ st', runJvmRes (n.toNat * 35 + 20) f_Algorithm_copyPrefix___redArg_1_prog
        ⟨0, [], setLocal (setLocal (setLocal (setLocal (setLocal (fun _ => .null) 0 inst)
          1 (.heapRef srcAddr)) 2 (.i32 n)) 3 (.i32 i)) 4 (.heapRef dstAddr), jh, hp⟩ =
      some (.unit, st') ∧
      st'.jvmHeap = jh.set dstAddr (.objArray dstCls
        (copyObjArrayPrefix srcElems dstElems n i (n.toNat - i.toNat + 1))) := by
  rw [show f_Algorithm_copyPrefix___redArg_1_prog = f_Algorithm_copyPrefix___redArg_prog from rfl]
  exact copyPrefix_equiv jh hp inst srcAddr dstAddr srcCls dstCls srcElems dstElems n i hne hsrc hdst hi hn hd hn31 hcompat

theorem copyPrefix_2_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (inst : JvmVal) (srcAddr dstAddr : Nat) (srcCls dstCls : String)
    (srcElems dstElems : Array JvmVal) (n i : UInt32)
    (hne : srcAddr ≠ dstAddr)
    (hsrc : jh.get? srcAddr = some (.objArray srcCls srcElems))
    (hdst : jh.get? dstAddr = some (.objArray dstCls dstElems))
    (hi : i.toNat ≤ n.toNat) (hn : n.toNat ≤ srcElems.size) (hd : n.toNat ≤ dstElems.size)
    (hn31 : n.toNat < 2 ^ 31)
    (hcompat : ∀ (k : Nat) (hk : k < n.toNat), i.toNat ≤ k →
      Jvm.isArrayElemCompat algHooks jh dstCls (srcElems[k]'(by omega)) = true) :
    ∃ st', runJvmRes (n.toNat * 35 + 20) f_Algorithm_copyPrefix___redArg_2_prog
        ⟨0, [], setLocal (setLocal (setLocal (setLocal (setLocal (fun _ => .null) 0 inst)
          1 (.heapRef srcAddr)) 2 (.i32 n)) 3 (.i32 i)) 4 (.heapRef dstAddr), jh, hp⟩ =
      some (.unit, st') ∧
      st'.jvmHeap = jh.set dstAddr (.objArray dstCls
        (copyObjArrayPrefix srcElems dstElems n i (n.toNat - i.toNat + 1))) := by
  rw [show f_Algorithm_copyPrefix___redArg_2_prog = f_Algorithm_copyPrefix___redArg_prog from rfl]
  exact copyPrefix_equiv jh hp inst srcAddr dstAddr srcCls dstCls srcElems dstElems n i hne hsrc hdst hi hn hd hn31 hcompat

theorem copyPrefix_3_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (inst : JvmVal) (srcAddr dstAddr : Nat) (srcCls dstCls : String)
    (srcElems dstElems : Array JvmVal) (n i : UInt32)
    (hne : srcAddr ≠ dstAddr)
    (hsrc : jh.get? srcAddr = some (.objArray srcCls srcElems))
    (hdst : jh.get? dstAddr = some (.objArray dstCls dstElems))
    (hi : i.toNat ≤ n.toNat) (hn : n.toNat ≤ srcElems.size) (hd : n.toNat ≤ dstElems.size)
    (hn31 : n.toNat < 2 ^ 31)
    (hcompat : ∀ (k : Nat) (hk : k < n.toNat), i.toNat ≤ k →
      Jvm.isArrayElemCompat algHooks jh dstCls (srcElems[k]'(by omega)) = true) :
    ∃ st', runJvmRes (n.toNat * 35 + 20) f_Algorithm_copyPrefix___redArg_3_prog
        ⟨0, [], setLocal (setLocal (setLocal (setLocal (setLocal (fun _ => .null) 0 inst)
          1 (.heapRef srcAddr)) 2 (.i32 n)) 3 (.i32 i)) 4 (.heapRef dstAddr), jh, hp⟩ =
      some (.unit, st') ∧
      st'.jvmHeap = jh.set dstAddr (.objArray dstCls
        (copyObjArrayPrefix srcElems dstElems n i (n.toNat - i.toNat + 1))) := by
  rw [show f_Algorithm_copyPrefix___redArg_3_prog = f_Algorithm_copyPrefix___redArg_prog from rfl]
  exact copyPrefix_equiv jh hp inst srcAddr dstAddr srcCls dstCls srcElems dstElems n i hne hsrc hdst hi hn hd hn31 hcompat

theorem copyPrefix_4_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (inst : JvmVal) (srcAddr dstAddr : Nat) (srcCls dstCls : String)
    (srcElems dstElems : Array JvmVal) (n i : UInt32)
    (hne : srcAddr ≠ dstAddr)
    (hsrc : jh.get? srcAddr = some (.objArray srcCls srcElems))
    (hdst : jh.get? dstAddr = some (.objArray dstCls dstElems))
    (hi : i.toNat ≤ n.toNat) (hn : n.toNat ≤ srcElems.size) (hd : n.toNat ≤ dstElems.size)
    (hn31 : n.toNat < 2 ^ 31)
    (hcompat : ∀ (k : Nat) (hk : k < n.toNat), i.toNat ≤ k →
      Jvm.isArrayElemCompat algHooks jh dstCls (srcElems[k]'(by omega)) = true) :
    ∃ st', runJvmRes (n.toNat * 35 + 20) f_Algorithm_copyPrefix___redArg_4_prog
        ⟨0, [], setLocal (setLocal (setLocal (setLocal (setLocal (fun _ => .null) 0 inst)
          1 (.heapRef srcAddr)) 2 (.i32 n)) 3 (.i32 i)) 4 (.heapRef dstAddr), jh, hp⟩ =
      some (.unit, st') ∧
      st'.jvmHeap = jh.set dstAddr (.objArray dstCls
        (copyObjArrayPrefix srcElems dstElems n i (n.toNat - i.toNat + 1))) := by
  rw [show f_Algorithm_copyPrefix___redArg_4_prog = f_Algorithm_copyPrefix___redArg_prog from rfl]
  exact copyPrefix_equiv jh hp inst srcAddr dstAddr srcCls dstCls srcElems dstElems n i hne hsrc hdst hi hn hd hn31 hcompat

/-! ### GrowBuf.push (all 5 variants via parameterized program) -/

private def growBufPushProg (cls : String) : List JvmInstr := [
  .aload 0, .ldcStr "null cannot be cast to non-null type kotlin.Array<*>",
  .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull" "(Ljava/lang/Object;Ljava/lang/String;)V",
  .aload 0, .checkcast "[Ljava/lang/Object;", .iconst 1, .aaload, .dup,
  .ldcStr "null cannot be cast to non-null type kotlin.Array<kotlin.Any?>",
  .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull" "(Ljava/lang/Object;Ljava/lang/String;)V",
  .checkcast "[Ljava/lang/Object;", .astore 2,
  .aload 0, .checkcast "[Ljava/lang/Object;", .iconst 2, .aaload, .astore 4,
  .iconst 0, .istore 5, .aload 4, .instanceof "java/lang/Integer", .ifeq 27,
  .aload 4, .checkcast "java/lang/Number", .invokevirtual "java/lang/Number" "intValue" "()I",
  .invokestatic "kotlin/UInt" "constructor-impl" "(I)I", .goto 33,
  .aload 4, .ldcStr "null cannot be cast to non-null type kotlin.UInt",
  .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull" "(Ljava/lang/Object;Ljava/lang/String;)V",
  .aload 4, .checkcast "kotlin/UInt", .invokevirtual "kotlin/UInt" "unbox-impl" "()I", .istore 3,
  .aload 2, .arraylength, .invokestatic "kotlin/UInt" "constructor-impl" "(I)I", .istore 4,
  .iload 3, .iload 4, .invokestatic "java/lang/Integer" "compareUnsigned" "(II)I", .iflt 92,
  .iload 4, .iconst 1, .ishl, .invokestatic "kotlin/UInt" "constructor-impl" "(I)I", .iconst 1, .iadd,
  .invokestatic "kotlin/UInt" "constructor-impl" "(I)I", .anewarray "java/lang/Object", .astore 6,
  .aload 6, .astore 7, .iconst 0, .istore 8, .aload 7, .aload 1, .iconst 0, .iconst 0, .iconst 6, .aconstNull,
  .invokestatic "kotlin/collections/ArraysKt" "fill$default" "([Ljava/lang/Object;Ljava/lang/Object;IIILjava/lang/Object;)V",
  .aload 6, .astore 5, .aload 1, .aload 2, .iload 4, .iconst 0, .aload 5,
  .invokestatic cls "f_Algorithm_copyPrefix___redArg-yOCu0fQ" "(Ljava/lang/Object;[Ljava/lang/Object;II[Ljava/lang/Object;)V",
  .iconst 3, .anewarray "java/lang/Object", .astore 6, .aload 6, .iconst 0, .iconst 0,
  .invokestatic "java/lang/Integer" "valueOf" "(I)Ljava/lang/Integer;", .aastore,
  .aload 6, .iconst 1, .aload 5, .aastore, .aload 6, .iconst 2,
  .iload 3, .iconst 1, .iadd, .invokestatic "kotlin/UInt" "constructor-impl" "(I)I",
  .invokestatic "kotlin/UInt" "box-impl" "(I)Lkotlin/UInt;", .aastore, .aload 6, .areturn,
  .aload 2, .iload 3, .aload 1, .aastore,
  .iconst 3, .anewarray "java/lang/Object", .astore 5, .aload 5, .iconst 0, .iconst 0,
  .invokestatic "java/lang/Integer" "valueOf" "(I)Ljava/lang/Integer;", .aastore,
  .aload 5, .iconst 1, .aload 2, .aastore, .aload 5, .iconst 2,
  .iload 3, .iconst 1, .iadd, .invokestatic "kotlin/UInt" "constructor-impl" "(I)I",
  .invokestatic "kotlin/UInt" "box-impl" "(I)Lkotlin/UInt;", .aastore, .aload 5, .areturn
]

private theorem stepStatic_copyPrefix_heap
    {pc : Nat} {cls : String} {dstAddr srcAddr : Nat} {i n : UInt32} {inst : JvmVal}
    {rest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {srcCls dstCls : String} {srcElems dstElems : Array JvmVal}
    (hcls : cls = "Life105LeanKt" ∨ cls = "Life106LeanKt" ∨ cls = "MacroCellLeanKt" ∨
      cls = "PlaintextLeanKt" ∨ cls = "RleLeanKt")
    (hsrc : jh.get? srcAddr = some (.objArray srcCls srcElems))
    (hdst : jh.get? dstAddr = some (.objArray dstCls dstElems)) :
    stepInvokeStatic ⟨pc, .heapRef dstAddr :: .i32 i :: .i32 n :: .heapRef srcAddr :: inst :: rest, locs, jh, hp⟩
      cls "f_Algorithm_copyPrefix___redArg-yOCu0fQ" "(Ljava/lang/Object;[Ljava/lang/Object;II[Ljava/lang/Object;)V" =
      .inl (some ⟨pc + 1, rest, locs,
        jh.set dstAddr (.objArray dstCls (copyObjArrayPrefix srcElems dstElems n i (n.toNat + 1))),
        hp⟩) := by
  rcases hcls with rfl | rfl | rfl | rfl | rfl <;>
    (refine Eq.trans (b := match jh.get? srcAddr, jh.get? dstAddr with
      | some (.objArray _ se), some (.objArray dc de) =>
        .inl (some ⟨pc + 1, rest, locs,
          jh.set dstAddr (.objArray dc (copyObjArrayPrefix se de n i (n.toNat + 1))), hp⟩)
      | _, _ => .inr none) rfl ?_
     rw [hsrc, hdst])

private theorem jvmHeap_alloc_set_set_push (H : Jvm.JvmHeap AlgExt)
    (a0 a1 a2 : Jvm.HeapObj AlgExt) :
    ((H.alloc a0).2.set H.objects.size a1).set H.objects.size a2 = (H.alloc a2).2 := by
  rw [jvmHeap_set_set]
  simp only [Jvm.JvmHeap.set, Jvm.JvmHeap.alloc, Array.size_push, Nat.lt_add_one, ↓reduceDIte]
  congr 1
  apply Array.ext (by simp)
  intro k hk1 hk2
  simp only [Array.size_set, Array.size_push] at hk1 hk2
  simp only [Array.getElem_set, Array.getElem_push]
  split
  · next heq =>
    split
    · exact absurd heq (by omega)
    · rfl
  · split
    · rfl
    · next hne => omega

private theorem growBufPush_spec (cls : String)
    (hcls : cls = "Life105LeanKt" ∨ cls = "Life106LeanKt" ∨ cls = "MacroCellLeanKt" ∨
      cls = "PlaintextLeanKt" ∨ cls = "RleLeanKt")
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (bufAddr dataAddr : Nat) (bufElems dataElems : Array JvmVal)
    (sz : UInt32) (elem : JvmVal)
    (hbuf : jh.get? bufAddr = some (.objArray "java/lang/Object" bufElems))
    (h1 : bufElems[1]? = some (.heapRef dataAddr))
    (h2 : bufElems[2]? = some (.boxedUInt sz))
    (hdata : jh.get? dataAddr = some (.objArray "java/lang/Object" dataElems))
    (hcap : dataElems.size < 2 ^ 30)
    (hsz : sz.toNat ≤ dataElems.size)
    (helem : elem.isRef = true) :
    let cap : UInt32 := UInt32.ofNat dataElems.size
    let jhAfter :=
      if hlt : sz < cap then
        let dataElems' := dataElems.set sz.toNat elem (by
          have hlt' := UInt32.lt_iff_toNat_lt.mp hlt
          have hmod : (UInt32.ofNat dataElems.size).toNat = dataElems.size := by
            rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
          rw [hmod] at hlt'; exact hlt')
        let jh1 := jh.set dataAddr (.objArray "java/lang/Object" dataElems')
        (jh1.alloc (.objArray "java/lang/Object" #[.boxedInt 0, .heapRef dataAddr, .boxedUInt (sz + 1)])).2
      else
        let newCap := (2 * cap + 1).toNat
        let (_, jh1) := jh.alloc (.objArray "java/lang/Object" (Array.replicate newCap .null))
        let newAddr := jh.objects.size
        let filled := Array.ofFn (n := newCap) fun _ => elem
        let jh2 := jh1.set newAddr (.objArray "java/lang/Object" filled)
        let grown := copyObjArrayPrefix dataElems filled cap 0 (cap.toNat + 1)
        let jh3 := jh2.set newAddr (.objArray "java/lang/Object" grown)
        (jh3.alloc (.objArray "java/lang/Object" #[.boxedInt 0, .heapRef newAddr, .boxedUInt (sz + 1)])).2
    let outAddr := if sz < cap then jh.objects.size else jh.objects.size + 1
    ∃ st', runJvmRes 120 (growBufPushProg cls)
        ⟨0, [], setLocal (setLocal (fun _ => .null) 0 (.heapRef bufAddr)) 1 elem, jh, hp⟩ =
      some (.heapRef outAddr, st') ∧ st'.jvmHeap = jhAfter := by
  have hlt1 : 1 < bufElems.size := (Array.getElem?_eq_some_iff.mp h1).1
  have he1 : bufElems[1]'hlt1 = .heapRef dataAddr := (Array.getElem?_eq_some_iff.mp h1).2
  have hlt2 : 2 < bufElems.size := (Array.getElem?_eq_some_iff.mp h2).1
  have he2 : bufElems[2]'hlt2 = .boxedUInt sz := (Array.getElem?_eq_some_iff.mp h2).2
  have hlt_cap : dataElems.size < 2 ^ 31 := by omega
  have hcap_nat : (UInt32.ofNat dataElems.size).toNat = dataElems.size := by
    rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  have hslt_sz : sz.toBitVec.slt 0#32 = false := u32_slt_zero_of_lt_2_31 (by omega)
  by_cases hlt : sz < UInt32.ofNat dataElems.size
  · have hcu : (if sz == UInt32.ofNat dataElems.size then (0 : UInt32)
        else if sz < UInt32.ofNat dataElems.size then 4294967295 else 1) = 4294967295 := by
      have hne : (sz == UInt32.ofNat dataElems.size) = false :=
        beq_false_of_ne (fun h => by subst h; exact Nat.ne_of_lt (UInt32.lt_iff_toNat_lt.mp hlt) rfl)
      simp [hne, hlt]
    have hslt_92 : (4294967295 : UInt32).toBitVec.slt 0#32 = true := by decide
    have hlt_sz_data : sz.toNat < dataElems.size := by
      have := UInt32.lt_iff_toNat_lt.mp hlt; omega
    let dataElems' := dataElems.set sz.toNat elem hlt_sz_data
    let jh1 := jh.set dataAddr (.objArray "java/lang/Object" dataElems')
    have hsz0 : jh1.objects.size = jh.objects.size := by
      simp only [jh1, Jvm.JvmHeap.set]
      split
      · simp [Array.size_set]
      · rfl
    have ha0 : (jh1.alloc (.objArray "java/lang/Object" (Array.replicate 3 .null))).2.get? jh.objects.size =
        some (.objArray "java/lang/Object" (Array.replicate 3 .null)) := by
      simpa [hsz0] using jvmHeap_get?_alloc_self jh1 (.objArray "java/lang/Object" (Array.replicate 3 .null))
    have ha1 := jvmHeap_get?_set_self ha0 (w := .objArray "java/lang/Object" ((Array.replicate 3 .null).set 0 (.boxedInt 0)))
    have ha2 := jvmHeap_get?_set_self ha1 (w := .objArray "java/lang/Object"
      (((Array.replicate 3 .null).set 0 (.boxedInt 0)).set 1 (.heapRef dataAddr)))
    exact ⟨_, by
      apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
      split_res_fuel 5; heap_step_blk (growBufPushProg cls)
      split_res_fuel 1; rw [runJvmResFast_checkcast_objArray hbuf (Or.inl rfl)]
      split_res_fuel 5; heap_step_blk (growBufPushProg cls)
      split_res_fuel 1; rw [runJvmResFast_aaload (idx := 1) hbuf (by decide) hlt1,
        show bufElems[(1 : UInt32).toNat]'hlt1 = .heapRef dataAddr from he1]
      split_res_fuel 5; heap_step_blk (growBufPushProg cls)
      split_res_fuel 1; rw [runJvmResFast_checkcast_objArray hdata (Or.inl rfl)]
      split_res_fuel 5; heap_step_blk (growBufPushProg cls)
      split_res_fuel 1; rw [runJvmResFast_checkcast_objArray hbuf (Or.inl rfl)]
      split_res_fuel 5; heap_step_blk (growBufPushProg cls)
      split_res_fuel 1; rw [runJvmResFast_aaload (idx := 2) hbuf (by decide) hlt2,
        show bufElems[(2 : UInt32).toNat]'hlt2 = .boxedUInt sz from he2]
      split_res_fuel 5; heap_step_blk (growBufPushProg cls)
      split_res_fuel 1; rw [runJvmResFast_instanceof_boxedUInt_int]
      split_res_fuel 10; heap_step_blk (growBufPushProg cls)
      simp only [beq_self_eq_true, ↓reduceIte]
      heap_step_blk (growBufPushProg cls)
      split_res_fuel 1; rw [runJvmResFast_checkcast_boxedUInt (Or.inl rfl)]
      split_res_fuel 5; heap_step_blk (growBufPushProg cls)
      split_res_fuel 1; rw [runJvmResFast_arraylength_obj hdata]
      split_res_fuel 10; heap_step_blk (growBufPushProg cls)
      simp only [hcu, hslt_92, ↓reduceIte]
      heap_step_blk (growBufPushProg cls)
      split_res_fuel 1; rw [runJvmResFast_aastore hdata hslt_sz hlt_sz_data
        (by cases elem <;> simp_all [Jvm.isArrayElemCompat, Jvm.JvmVal.isRef])]
      heap_step_blk (growBufPushProg cls)
      split_res_fuel 1; rw [runJvmResFast_anewarray_obj (by decide)]
      change runJvmResFast _ _ _ _ ⟨_, _, _, (jh1.alloc _).2, hp⟩ = _
      heap_step_blk (growBufPushProg cls)
      split_res_fuel 1; rw [show (3 : UInt32).toNat = 3 from rfl, hsz0,
        runJvmResFast_aastore (idx := 0) ha0 (by decide) (by decide)]
      change runJvmResFast _ _ _ _ ⟨_, _, _, (jh1.alloc (.objArray "java/lang/Object" (Array.replicate 3 .null))).2.set
        jh.objects.size (.objArray "java/lang/Object" ((Array.replicate 3 .null).set 0 (.boxedInt 0))), hp⟩ = _
      heap_step_blk (growBufPushProg cls)
      split_res_fuel 1; rw [runJvmResFast_aastore (idx := 1) ha1 (by decide) (by decide)]
      change runJvmResFast _ _ _ _ ⟨_, _, _, (((jh1.alloc (.objArray "java/lang/Object" (Array.replicate 3 .null))).2.set
        jh.objects.size (.objArray "java/lang/Object" ((Array.replicate 3 .null).set 0 (.boxedInt 0)))).set
        jh.objects.size (.objArray "java/lang/Object" (((Array.replicate 3 .null).set 0 (.boxedInt 0)).set 1 (.heapRef dataAddr)))), hp⟩ = _
      heap_step_blk (growBufPushProg cls)
      split_res_fuel 1; rw [runJvmResFast_aastore (idx := 2) ha2 (by decide) (by simp)]
      simp only [hlt, ↓reduceIte]; rfl, by
      change (((jh1.alloc (.objArray "java/lang/Object" (Array.replicate 3 .null))).2.set
        jh.objects.size (.objArray "java/lang/Object" ((Array.replicate 3 .null).set 0 (.boxedInt 0)))).set
        jh.objects.size (.objArray "java/lang/Object" (((Array.replicate 3 .null).set 0 (.boxedInt 0)).set 1 (.heapRef dataAddr)))).set
        jh.objects.size (.objArray "java/lang/Object" (((((Array.replicate 3 .null).set 0 (.boxedInt 0)).set 1 (.heapRef dataAddr)).set
          (2 : UInt32).toNat (.boxedUInt (sz + 1))))) = _
      have harr' : ((((Array.replicate 3 (JvmVal.null : Jvm.JvmVal AlgExt)).set 0 (.boxedInt 0)).set 1 (.heapRef dataAddr)).set
          (2 : UInt32).toNat (.boxedUInt (sz + 1))) =
          #[JvmVal.boxedInt 0, Jvm.JvmVal.heapRef dataAddr, JvmVal.boxedUInt (sz + 1)] := by simp [Array.replicate, Array.set]
      have hda_lt : dataAddr < jh.objects.size :=
        (Array.getElem?_eq_some_iff.mp (by simpa [Jvm.JvmHeap.get?] using hdata)).1
      simp only [hlt, ↓reduceDIte, jvmHeap_set_set, harr']
      simp only [jh1, dataElems', Jvm.JvmHeap.set, Jvm.JvmHeap.alloc, hda_lt, ↓reduceDIte,
        Array.size_set, Array.size_push, Nat.lt_add_one]
      congr 1
      apply Array.ext (by simp)
      intro k hk1 hk2
      simp only [Array.size_push, Array.size_set] at hk1 hk2
      simp only [Array.getElem_set, Array.getElem_push, Array.size_set]
      split
      · split <;> first | rfl | omega
      · split <;> first | rfl | omega⟩
  · have hcu_slt : ((if sz == UInt32.ofNat dataElems.size then (0 : UInt32)
        else if sz < UInt32.ofNat dataElems.size then 4294967295 else 1).toBitVec.slt 0#32) = false := by
      simp [hlt]
      split <;> decide
    have hnewcap_lt : ((UInt32.ofNat dataElems.size <<< 1) + 1).toNat < 2 ^ 31 := by
      have hcap32 : dataElems.size < 2 ^ 32 := by omega
      have hshl : (UInt32.ofNat dataElems.size <<< 1).toNat = dataElems.size * 2 := by
        rw [UInt32.toNat_shiftLeft, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hcap32,
          show (1 : UInt32).toNat % 32 = 1 from by decide, Nat.shiftLeft_eq, Nat.pow_one]
        exact Nat.mod_eq_of_lt (by omega)
      rw [UInt32.toNat_add, hshl, UInt32.toNat_one]
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    have hnewcap_eq : ((UInt32.ofNat dataElems.size <<< 1) + 1) =
        2 * UInt32.ofNat dataElems.size + 1 := u32_shl1_add1_eq
    have hslt_newcap : ((UInt32.ofNat dataElems.size <<< 1) + 1).toBitVec.slt 0#32 = false :=
      u32_slt_zero_of_lt_2_31 hnewcap_lt
    let jh1 := (jh.alloc (.objArray "java/lang/Object"
      (Array.replicate ((UInt32.ofNat dataElems.size <<< 1) + 1).toNat .null))).2
    have ha_new : jh1.get? jh.objects.size =
        some (.objArray "java/lang/Object"
          (Array.replicate ((UInt32.ofNat dataElems.size <<< 1) + 1).toNat .null)) :=
      jvmHeap_get?_alloc_self _ _
    let filled := Array.ofFn (n := (Array.replicate ((UInt32.ofNat dataElems.size <<< 1) + 1).toNat
      (JvmVal.null : Jvm.JvmVal AlgExt)).size) fun _ => elem
    let jh2 := jh1.set jh.objects.size (.objArray "java/lang/Object" filled)
    have hda_lt : dataAddr < jh.objects.size :=
      (Array.getElem?_eq_some_iff.mp (by simpa [Jvm.JvmHeap.get?] using hdata)).1
    have hdata1 : jh2.get? dataAddr = some (.objArray "java/lang/Object" dataElems) := by
      have hne_new : dataAddr ≠ jh.objects.size := by omega
      rw [jvmHeap_get?_set_ne _ _ hne_new, jvmHeap_get?_alloc_lt jh _ hda_lt]
      exact hdata
    have ha_filled : jh2.get? jh.objects.size = some (.objArray "java/lang/Object" filled) :=
      jvmHeap_get?_set_self ha_new
    let cap := UInt32.ofNat dataElems.size
    let grown := copyObjArrayPrefix dataElems filled cap 0 (cap.toNat + 1)
    let jh3 := jh2.set jh.objects.size (.objArray "java/lang/Object" grown)
    have hsz1 : jh3.objects.size = jh.objects.size + 1 := by
      simp [jh3, jh2, jh1, Jvm.JvmHeap.set, Jvm.JvmHeap.alloc]
    let arr3_0 : Array (Jvm.JvmVal AlgExt) := Array.replicate 3 .null
    let arr3_1 : Array (Jvm.JvmVal AlgExt) := arr3_0.set 0 (.boxedInt 0) (by decide)
    let arr3_2 : Array (Jvm.JvmVal AlgExt) := arr3_1.set 1 (.heapRef jh.objects.size) (by decide)
    let jb0 := (jh3.alloc (.objArray "java/lang/Object" arr3_0)).2
    have ha3 : jb0.get? (jh.objects.size + 1) =
        some (.objArray "java/lang/Object" arr3_0) := by
      simpa [jb0, hsz1] using jvmHeap_get?_alloc_self jh3 (.objArray "java/lang/Object" arr3_0)
    let jb1 := jb0.set (jh.objects.size + 1) (.objArray "java/lang/Object" arr3_1)
    have ha3_1 : jb1.get? (jh.objects.size + 1) =
        some (.objArray "java/lang/Object" arr3_1) :=
      jvmHeap_get?_set_self ha3
    let jb2 := jb1.set (jh.objects.size + 1) (.objArray "java/lang/Object" arr3_2)
    have ha3_2 : jb2.get? (jh.objects.size + 1) =
        some (.objArray "java/lang/Object" arr3_2) :=
      jvmHeap_get?_set_self ha3_1
    exact ⟨_, by
      apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
      split_res_fuel 5; heap_step_blk (growBufPushProg cls)
      split_res_fuel 1; rw [runJvmResFast_checkcast_objArray hbuf (Or.inl rfl)]
      split_res_fuel 5; heap_step_blk (growBufPushProg cls)
      split_res_fuel 1; rw [runJvmResFast_aaload (idx := 1) hbuf (by decide) hlt1,
        show bufElems[(1 : UInt32).toNat]'hlt1 = .heapRef dataAddr from he1]
      split_res_fuel 5; heap_step_blk (growBufPushProg cls)
      split_res_fuel 1; rw [runJvmResFast_checkcast_objArray hdata (Or.inl rfl)]
      split_res_fuel 5; heap_step_blk (growBufPushProg cls)
      split_res_fuel 1; rw [runJvmResFast_checkcast_objArray hbuf (Or.inl rfl)]
      split_res_fuel 5; heap_step_blk (growBufPushProg cls)
      split_res_fuel 1; rw [runJvmResFast_aaload (idx := 2) hbuf (by decide) hlt2,
        show bufElems[(2 : UInt32).toNat]'hlt2 = .boxedUInt sz from he2]
      split_res_fuel 5; heap_step_blk (growBufPushProg cls)
      split_res_fuel 1; rw [runJvmResFast_instanceof_boxedUInt_int]
      split_res_fuel 10; heap_step_blk (growBufPushProg cls)
      simp only [beq_self_eq_true, ↓reduceIte]
      heap_step_blk (growBufPushProg cls)
      split_res_fuel 1; rw [runJvmResFast_checkcast_boxedUInt (Or.inl rfl)]
      split_res_fuel 5; heap_step_blk (growBufPushProg cls)
      split_res_fuel 1; rw [runJvmResFast_arraylength_obj hdata]
      split_res_fuel 10; heap_step_blk (growBufPushProg cls)
      simp only [hcu_slt, Bool.false_eq_true, ↓reduceIte]
      heap_step_blk (growBufPushProg cls)
      rw [show (1 : UInt32) &&& 31 = 1 from by decide]
      split_res_fuel 1; rw [runJvmResFast_anewarray_obj hslt_newcap]
      heap_step_blk (growBufPushProg cls)
      split_res_fuel 1
      rw [runJvmResFast_invokestatic_step (stepStatic_arraysFillAll_obj ha_new
        (by cases elem <;> simp_all [Jvm.isArrayElemCompat, Jvm.JvmVal.isRef]))]
      heap_step_blk (growBufPushProg cls)
      split_res_fuel 1
      rw [runJvmResFast_invokestatic_step (stepStatic_copyPrefix_heap hcls hdata1 ha_filled)]
      heap_step_blk (growBufPushProg cls)
      split_res_fuel 1; rw [runJvmResFast_anewarray_obj (by decide)]
      change runJvmResFast _ _ _ _ ⟨_, _, _, jb0, hp⟩ = _
      heap_step_blk (growBufPushProg cls)
      split_res_fuel 1
      rw [show (jh2.set jh.objects.size (.objArray "java/lang/Object" (copyObjArrayPrefix dataElems filled cap 0 (cap.toNat + 1)))).objects.size = jh.objects.size + 1 from hsz1]
      rw [runJvmResFast_aastore (idx := 0) ha3 (by decide) (by simp [arr3_0])]
      change runJvmResFast _ _ _ _ ⟨_, _, _, jb1, hp⟩ = _
      heap_step_blk (growBufPushProg cls)
      split_res_fuel 1
      rw [runJvmResFast_aastore (idx := 1) ha3_1 (by decide) (by simp [arr3_1, arr3_0])]
      change runJvmResFast _ _ _ _ ⟨_, _, _, jb2, hp⟩ = _
      heap_step_blk (growBufPushProg cls)
      split_res_fuel 1
      rw [runJvmResFast_aastore (idx := 2) ha3_2 (by decide) (by simp [arr3_2, arr3_1, arr3_0])]
      simp only [hlt, ↓reduceIte]; rfl, by
      have harr : arr3_2.set (2 : UInt32).toNat (.boxedUInt (sz + 1)) (by simp [arr3_2, arr3_1, arr3_0]) =
          #[JvmVal.boxedInt 0, Jvm.JvmVal.heapRef jh.objects.size, JvmVal.boxedUInt (sz + 1)] := by
        simp [arr3_2, arr3_1, arr3_0, Array.replicate, Array.set]
      dsimp only [jb2, jb1, jb0]
      rw [harr, ← hsz1, jvmHeap_set_set, jvmHeap_alloc_set_set_push jh3]
      simp only [hlt, ↓reduceDIte]
      dsimp only [jh3, jh2, jh1, grown, filled, cap]
      rw [Array.size_replicate, hnewcap_eq]⟩

theorem growBufPush_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (bufAddr dataAddr : Nat) (bufElems dataElems : Array JvmVal) (sz : UInt32) (elem : JvmVal)
    (hbuf : jh.get? bufAddr = some (.objArray "java/lang/Object" bufElems))
    (h1 : bufElems[1]? = some (.heapRef dataAddr)) (h2 : bufElems[2]? = some (.boxedUInt sz))
    (hdata : jh.get? dataAddr = some (.objArray "java/lang/Object" dataElems))
    (hcap : dataElems.size < 2 ^ 30) (hsz : sz.toNat ≤ dataElems.size)
    (helem : elem.isRef = true) :
    ∃ st', runJvmRes 120 f_Algorithm_GrowBuf_push___redArg_prog
        ⟨0, [], setLocal (setLocal (fun _ => .null) 0 (.heapRef bufAddr)) 1 elem, jh, hp⟩ =
      some (.heapRef (if sz < UInt32.ofNat dataElems.size then jh.objects.size else jh.objects.size + 1), st') := by
  rw [show f_Algorithm_GrowBuf_push___redArg_prog = growBufPushProg "Life105LeanKt" from rfl]
  rcases growBufPush_spec "Life105LeanKt" (Or.inl rfl) jh hp bufAddr dataAddr bufElems dataElems sz elem hbuf h1 h2 hdata hcap hsz helem with
    ⟨st', h, _⟩
  exact ⟨st', h⟩

theorem growBufPush_1_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (bufAddr dataAddr : Nat) (bufElems dataElems : Array JvmVal) (sz : UInt32) (elem : JvmVal)
    (hbuf : jh.get? bufAddr = some (.objArray "java/lang/Object" bufElems))
    (h1 : bufElems[1]? = some (.heapRef dataAddr)) (h2 : bufElems[2]? = some (.boxedUInt sz))
    (hdata : jh.get? dataAddr = some (.objArray "java/lang/Object" dataElems))
    (hcap : dataElems.size < 2 ^ 30) (hsz : sz.toNat ≤ dataElems.size)
    (helem : elem.isRef = true) :
    ∃ st', runJvmRes 120 f_Algorithm_GrowBuf_push___redArg_1_prog
        ⟨0, [], setLocal (setLocal (fun _ => .null) 0 (.heapRef bufAddr)) 1 elem, jh, hp⟩ =
      some (.heapRef (if sz < UInt32.ofNat dataElems.size then jh.objects.size else jh.objects.size + 1), st') := by
  rw [show f_Algorithm_GrowBuf_push___redArg_1_prog = growBufPushProg "Life106LeanKt" from rfl]
  rcases growBufPush_spec "Life106LeanKt" (Or.inr (Or.inl rfl)) jh hp bufAddr dataAddr bufElems dataElems sz elem hbuf h1 h2 hdata hcap hsz helem with
    ⟨st', h, _⟩
  exact ⟨st', h⟩

theorem growBufPush_2_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (bufAddr dataAddr : Nat) (bufElems dataElems : Array JvmVal) (sz : UInt32) (elem : JvmVal)
    (hbuf : jh.get? bufAddr = some (.objArray "java/lang/Object" bufElems))
    (h1 : bufElems[1]? = some (.heapRef dataAddr)) (h2 : bufElems[2]? = some (.boxedUInt sz))
    (hdata : jh.get? dataAddr = some (.objArray "java/lang/Object" dataElems))
    (hcap : dataElems.size < 2 ^ 30) (hsz : sz.toNat ≤ dataElems.size)
    (helem : elem.isRef = true) :
    ∃ st', runJvmRes 120 f_Algorithm_GrowBuf_push___redArg_2_prog
        ⟨0, [], setLocal (setLocal (fun _ => .null) 0 (.heapRef bufAddr)) 1 elem, jh, hp⟩ =
      some (.heapRef (if sz < UInt32.ofNat dataElems.size then jh.objects.size else jh.objects.size + 1), st') := by
  rw [show f_Algorithm_GrowBuf_push___redArg_2_prog = growBufPushProg "MacroCellLeanKt" from rfl]
  rcases growBufPush_spec "MacroCellLeanKt" (Or.inr (Or.inr (Or.inl rfl))) jh hp bufAddr dataAddr bufElems dataElems sz elem hbuf h1 h2 hdata hcap hsz helem with
    ⟨st', h, _⟩
  exact ⟨st', h⟩

theorem growBufPush_3_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (bufAddr dataAddr : Nat) (bufElems dataElems : Array JvmVal) (sz : UInt32) (elem : JvmVal)
    (hbuf : jh.get? bufAddr = some (.objArray "java/lang/Object" bufElems))
    (h1 : bufElems[1]? = some (.heapRef dataAddr)) (h2 : bufElems[2]? = some (.boxedUInt sz))
    (hdata : jh.get? dataAddr = some (.objArray "java/lang/Object" dataElems))
    (hcap : dataElems.size < 2 ^ 30) (hsz : sz.toNat ≤ dataElems.size)
    (helem : elem.isRef = true) :
    ∃ st', runJvmRes 120 f_Algorithm_GrowBuf_push___redArg_3_prog
        ⟨0, [], setLocal (setLocal (fun _ => .null) 0 (.heapRef bufAddr)) 1 elem, jh, hp⟩ =
      some (.heapRef (if sz < UInt32.ofNat dataElems.size then jh.objects.size else jh.objects.size + 1), st') := by
  rw [show f_Algorithm_GrowBuf_push___redArg_3_prog = growBufPushProg "PlaintextLeanKt" from rfl]
  rcases growBufPush_spec "PlaintextLeanKt" (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) jh hp bufAddr dataAddr bufElems dataElems sz elem hbuf h1 h2 hdata hcap hsz helem with
    ⟨st', h, _⟩
  exact ⟨st', h⟩

theorem growBufPush_4_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (bufAddr dataAddr : Nat) (bufElems dataElems : Array JvmVal) (sz : UInt32) (elem : JvmVal)
    (hbuf : jh.get? bufAddr = some (.objArray "java/lang/Object" bufElems))
    (h1 : bufElems[1]? = some (.heapRef dataAddr)) (h2 : bufElems[2]? = some (.boxedUInt sz))
    (hdata : jh.get? dataAddr = some (.objArray "java/lang/Object" dataElems))
    (hcap : dataElems.size < 2 ^ 30) (hsz : sz.toNat ≤ dataElems.size)
    (helem : elem.isRef = true) :
    ∃ st', runJvmRes 120 f_Algorithm_GrowBuf_push___redArg_4_prog
        ⟨0, [], setLocal (setLocal (fun _ => .null) 0 (.heapRef bufAddr)) 1 elem, jh, hp⟩ =
      some (.heapRef (if sz < UInt32.ofNat dataElems.size then jh.objects.size else jh.objects.size + 1), st') := by
  rw [show f_Algorithm_GrowBuf_push___redArg_4_prog = growBufPushProg "RleLeanKt" from rfl]
  rcases growBufPush_spec "RleLeanKt" (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) jh hp bufAddr dataAddr bufElems dataElems sz elem hbuf h1 h2 hdata hcap hsz helem with
    ⟨st', h, _⟩
  exact ⟨st', h⟩

/-! ### GrowBuf.toArray (+ _1.._4) -/

theorem growBufToArray_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (bufAddr dataAddr : Nat) (bufElems dataElems : Array JvmVal) (sz : UInt32)
    (hbuf : jh.get? bufAddr = some (.objArray "java/lang/Object" bufElems))
    (h1 : bufElems[1]? = some (.heapRef dataAddr))
    (h2 : bufElems[2]? = some (.boxedUInt sz))
    (hdata : jh.get? dataAddr = some (.objArray "java/lang/Object" dataElems))
    (hcap : dataElems.size < 2 ^ 31)
    (hsz : sz.toNat ≤ dataElems.size) :
    let b : Algorithm.GrowBuf JvmVal := ⟨dataElems, sz⟩
    ∃ st', runJvmRes 100 f_Algorithm_GrowBuf_toArray___redArg_prog
        ⟨0, [], setLocal (fun _ => .null) 0 (.heapRef bufAddr), jh, hp⟩ =
      some (.heapRef jh.objects.size, st') ∧
      st'.jvmHeap.get? jh.objects.size = some (.objArray "java/lang/Object" b.toArray) := by
  have hlt1 : 1 < bufElems.size := (Array.getElem?_eq_some_iff.mp h1).1
  have he1 : bufElems[1]'hlt1 = .heapRef dataAddr := (Array.getElem?_eq_some_iff.mp h1).2
  have hlt2 : 2 < bufElems.size := (Array.getElem?_eq_some_iff.mp h2).1
  have he2 : bufElems[2]'hlt2 = .boxedUInt sz := (Array.getElem?_eq_some_iff.mp h2).2
  have hsz_lt : sz.toNat < 2 ^ 31 := by omega
  have hdata_mod : (UInt32.ofNat dataElems.size).toNat = dataElems.size := by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  have hdata_lt : (UInt32.ofNat dataElems.size).toNat < 2 ^ 31 := by omega
  have h0_le : (0 : Int) ≤ (sz.toBitVec.toInt) := by rw [u32_toInt_eq_toNat hsz_lt]; omega
  have h_to : sz.toBitVec.toInt ≤ (dataElems.size : Int) := by rw [u32_toInt_eq_toNat hsz_lt]; omega
  have hc1 : Jvm.coerceInI32 0 0 (UInt32.ofNat dataElems.size) = 0 :=
    coerceInI32_of_bounds (by decide) (by decide) hdata_lt (Nat.zero_le _) (Nat.zero_le _)
  have hc2 : Jvm.coerceInI32 sz 0 (UInt32.ofNat dataElems.size) = sz :=
    coerceInI32_of_bounds hsz_lt (by decide) hdata_lt (Nat.zero_le _) (by omega)
  exact ⟨_, by
    apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
    split_res_fuel 5; heap_step_blk f_Algorithm_GrowBuf_toArray___redArg_prog
    split_res_fuel 1; rw [runJvmResFast_checkcast_objArray hbuf (Or.inl rfl)]
    split_res_fuel 5; heap_step_blk f_Algorithm_GrowBuf_toArray___redArg_prog
    split_res_fuel 1; rw [runJvmResFast_aaload (idx := 1) hbuf (by decide) hlt1,
      show bufElems[(1 : UInt32).toNat]'hlt1 = .heapRef dataAddr from he1]
    split_res_fuel 5; heap_step_blk f_Algorithm_GrowBuf_toArray___redArg_prog
    split_res_fuel 1; rw [runJvmResFast_checkcast_objArray hdata (Or.inl rfl)]
    split_res_fuel 5; heap_step_blk f_Algorithm_GrowBuf_toArray___redArg_prog
    split_res_fuel 1; rw [runJvmResFast_checkcast_objArray hbuf (Or.inl rfl)]
    split_res_fuel 5; heap_step_blk f_Algorithm_GrowBuf_toArray___redArg_prog
    split_res_fuel 1; rw [runJvmResFast_aaload (idx := 1) hbuf (by decide) hlt1,
      show bufElems[(1 : UInt32).toNat]'hlt1 = .heapRef dataAddr from he1]
    split_res_fuel 5; heap_step_blk f_Algorithm_GrowBuf_toArray___redArg_prog
    split_res_fuel 1; rw [runJvmResFast_checkcast_objArray hdata (Or.inl rfl)]
    heap_step_blk f_Algorithm_GrowBuf_toArray___redArg_prog
    split_res_fuel 1; rw [runJvmResFast_arraylength_obj hdata]
    heap_step_blk f_Algorithm_GrowBuf_toArray___redArg_prog
    rw [hc1]
    split_res_fuel 1; rw [runJvmResFast_checkcast_objArray hbuf (Or.inl rfl)]
    heap_step_blk f_Algorithm_GrowBuf_toArray___redArg_prog
    split_res_fuel 1; rw [runJvmResFast_aaload (idx := 2) hbuf (by decide) hlt2,
      show bufElems[(2 : UInt32).toNat]'hlt2 = .boxedUInt sz from he2]
    heap_step_blk f_Algorithm_GrowBuf_toArray___redArg_prog
    split_res_fuel 1; rw [runJvmResFast_instanceof_boxedUInt_int]
    heap_step_blk f_Algorithm_GrowBuf_toArray___redArg_prog
    simp only [beq_self_eq_true, ↓reduceIte]
    heap_step_blk f_Algorithm_GrowBuf_toArray___redArg_prog
    split_res_fuel 1; rw [runJvmResFast_checkcast_boxedUInt (Or.inl rfl)]
    heap_step_blk f_Algorithm_GrowBuf_toArray___redArg_prog
    split_res_fuel 1; rw [runJvmResFast_checkcast_objArray hbuf (Or.inl rfl)]
    heap_step_blk f_Algorithm_GrowBuf_toArray___redArg_prog
    split_res_fuel 1; rw [runJvmResFast_aaload (idx := 1) hbuf (by decide) hlt1,
      show bufElems[(1 : UInt32).toNat]'hlt1 = .heapRef dataAddr from he1]
    heap_step_blk f_Algorithm_GrowBuf_toArray___redArg_prog
    split_res_fuel 1; rw [runJvmResFast_checkcast_objArray hdata (Or.inl rfl)]
    heap_step_blk f_Algorithm_GrowBuf_toArray___redArg_prog
    split_res_fuel 1; rw [runJvmResFast_arraylength_obj hdata]
    heap_step_blk f_Algorithm_GrowBuf_toArray___redArg_prog
    rw [hc1]
    split_res_fuel 1; rw [runJvmResFast_checkcast_objArray hbuf (Or.inl rfl)]
    heap_step_blk f_Algorithm_GrowBuf_toArray___redArg_prog
    split_res_fuel 1; rw [runJvmResFast_aaload (idx := 1) hbuf (by decide) hlt1,
      show bufElems[(1 : UInt32).toNat]'hlt1 = .heapRef dataAddr from he1]
    heap_step_blk f_Algorithm_GrowBuf_toArray___redArg_prog
    split_res_fuel 1; rw [runJvmResFast_checkcast_objArray hdata (Or.inl rfl)]
    heap_step_blk f_Algorithm_GrowBuf_toArray___redArg_prog
    split_res_fuel 1; rw [runJvmResFast_arraylength_obj hdata]
    heap_step_blk f_Algorithm_GrowBuf_toArray___redArg_prog
    rw [hc2]
    split_res_fuel 1
    rw [runJvmResFast_invokestatic_step (stepStatic_arraysCopyOfRange_obj hdata (by decide)
      (show (0 : UInt32).toBitVec.toInt ≤ sz.toBitVec.toInt from h0_le) h_to)]; rfl, by
    rw [jvmHeap_get?_alloc_self]
    simp only [Algorithm.GrowBuf.toArray, Option.some.injEq, Jvm.HeapObj.objArray.injEq, true_and]
    rw [u32_toInt_eq_toNat hsz_lt]
    apply Array.ext
    · simp [Array.size_extract, hsz]
    · intro i hi1 hi2
      simp only [Array.getElem_ofFn, Array.getElem_extract, Nat.zero_add,
        Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
        show (0 : UInt32).toBitVec.toInt.toNat = 0 from by decide]
      simp only [Array.size_ofFn, show (0 : UInt32).toBitVec.toInt.toNat = 0 from by decide,
        Int.toNat_natCast, Nat.sub_zero] at hi1
      rw [Array.getElem?_eq_getElem (by omega), Option.getD_some]⟩

theorem growBufToArray_1_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (bufAddr dataAddr : Nat) (bufElems dataElems : Array JvmVal) (sz : UInt32)
    (hbuf : jh.get? bufAddr = some (.objArray "java/lang/Object" bufElems))
    (h1 : bufElems[1]? = some (.heapRef dataAddr)) (h2 : bufElems[2]? = some (.boxedUInt sz))
    (hdata : jh.get? dataAddr = some (.objArray "java/lang/Object" dataElems))
    (hcap : dataElems.size < 2 ^ 31) (hsz : sz.toNat ≤ dataElems.size) :
    ∃ st', runJvmRes 100 f_Algorithm_GrowBuf_toArray___redArg_1_prog
        ⟨0, [], setLocal (fun _ => .null) 0 (.heapRef bufAddr), jh, hp⟩ =
      some (.heapRef jh.objects.size, st') ∧
      st'.jvmHeap.get? jh.objects.size = some (.objArray "java/lang/Object"
        (Algorithm.GrowBuf.mk dataElems sz).toArray) := by
  rw [show f_Algorithm_GrowBuf_toArray___redArg_1_prog = f_Algorithm_GrowBuf_toArray___redArg_prog from rfl]
  exact growBufToArray_equiv jh hp bufAddr dataAddr bufElems dataElems sz hbuf h1 h2 hdata hcap hsz

theorem growBufToArray_2_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (bufAddr dataAddr : Nat) (bufElems dataElems : Array JvmVal) (sz : UInt32)
    (hbuf : jh.get? bufAddr = some (.objArray "java/lang/Object" bufElems))
    (h1 : bufElems[1]? = some (.heapRef dataAddr)) (h2 : bufElems[2]? = some (.boxedUInt sz))
    (hdata : jh.get? dataAddr = some (.objArray "java/lang/Object" dataElems))
    (hcap : dataElems.size < 2 ^ 31) (hsz : sz.toNat ≤ dataElems.size) :
    ∃ st', runJvmRes 100 f_Algorithm_GrowBuf_toArray___redArg_2_prog
        ⟨0, [], setLocal (fun _ => .null) 0 (.heapRef bufAddr), jh, hp⟩ =
      some (.heapRef jh.objects.size, st') ∧
      st'.jvmHeap.get? jh.objects.size = some (.objArray "java/lang/Object"
        (Algorithm.GrowBuf.mk dataElems sz).toArray) := by
  rw [show f_Algorithm_GrowBuf_toArray___redArg_2_prog = f_Algorithm_GrowBuf_toArray___redArg_prog from rfl]
  exact growBufToArray_equiv jh hp bufAddr dataAddr bufElems dataElems sz hbuf h1 h2 hdata hcap hsz

theorem growBufToArray_3_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (bufAddr dataAddr : Nat) (bufElems dataElems : Array JvmVal) (sz : UInt32)
    (hbuf : jh.get? bufAddr = some (.objArray "java/lang/Object" bufElems))
    (h1 : bufElems[1]? = some (.heapRef dataAddr)) (h2 : bufElems[2]? = some (.boxedUInt sz))
    (hdata : jh.get? dataAddr = some (.objArray "java/lang/Object" dataElems))
    (hcap : dataElems.size < 2 ^ 31) (hsz : sz.toNat ≤ dataElems.size) :
    ∃ st', runJvmRes 100 f_Algorithm_GrowBuf_toArray___redArg_3_prog
        ⟨0, [], setLocal (fun _ => .null) 0 (.heapRef bufAddr), jh, hp⟩ =
      some (.heapRef jh.objects.size, st') ∧
      st'.jvmHeap.get? jh.objects.size = some (.objArray "java/lang/Object"
        (Algorithm.GrowBuf.mk dataElems sz).toArray) := by
  rw [show f_Algorithm_GrowBuf_toArray___redArg_3_prog = f_Algorithm_GrowBuf_toArray___redArg_prog from rfl]
  exact growBufToArray_equiv jh hp bufAddr dataAddr bufElems dataElems sz hbuf h1 h2 hdata hcap hsz

theorem growBufToArray_4_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (bufAddr dataAddr : Nat) (bufElems dataElems : Array JvmVal) (sz : UInt32)
    (hbuf : jh.get? bufAddr = some (.objArray "java/lang/Object" bufElems))
    (h1 : bufElems[1]? = some (.heapRef dataAddr)) (h2 : bufElems[2]? = some (.boxedUInt sz))
    (hdata : jh.get? dataAddr = some (.objArray "java/lang/Object" dataElems))
    (hcap : dataElems.size < 2 ^ 31) (hsz : sz.toNat ≤ dataElems.size) :
    ∃ st', runJvmRes 100 f_Algorithm_GrowBuf_toArray___redArg_4_prog
        ⟨0, [], setLocal (fun _ => .null) 0 (.heapRef bufAddr), jh, hp⟩ =
      some (.heapRef jh.objects.size, st') ∧
      st'.jvmHeap.get? jh.objects.size = some (.objArray "java/lang/Object"
        (Algorithm.GrowBuf.mk dataElems sz).toArray) := by
  rw [show f_Algorithm_GrowBuf_toArray___redArg_4_prog = f_Algorithm_GrowBuf_toArray___redArg_prog from rfl]
  exact growBufToArray_equiv jh hp bufAddr dataAddr bufElems dataElems sz hbuf h1 h2 hdata hcap hsz

/-! ### AsciiBytes.{set, replicate, toStringRange} & decodeCharAt___lam__0 -/

theorem asciiBytesSet_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (addr : Nat) (g : Algorithm.AsciiBytes) (i : UInt32) (v : UInt8) (hv : v < 128)
    (hget : jh.get? addr = some (.byteArray g.1.data))
    (hlen : g.1.size < 2 ^ 31) :
    ∃ st', runJvmRes 20 f_Algorithm_AsciiBytes_set___redArg_prog
        ⟨0, [], setLocal (setLocal (setLocal (fun _ => .null) 0 (.heapRef addr))
          1 (.i32 i)) 2 (.i32 v.toUInt32), jh, hp⟩ =
      some (.unit, st') ∧
      st'.jvmHeap.get? addr = some (.byteArray (g.set i v hv).1.data) := by
  have hdsz : g.1.data.size = g.1.size := rfl
  have hi_nat : i.toNat = i.toBitVec.toNat := rfl
  have hsz_mod : (UInt32.ofNat g.1.data.size).toNat = g.1.data.size := by
    rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  have hlen31 : (UInt32.ofNat g.1.data.size).toNat < 2 ^ 31 := by omega
  by_cases hislt : i.toBitVec.slt 0#32 = true
  · have hisge : ¬(i.toNat < g.1.data.size) := by
      simp only [BitVec.slt, BitVec.toInt_zero] at hislt
      rw [BitVec.toInt_eq_toNat_cond] at hislt
      split at hislt
      · exfalso; simp only [decide_eq_true_eq] at hislt; omega
      · omega
    exact ⟨_, by
      apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
      split_res_fuel 5; heap_step_blk f_Algorithm_AsciiBytes_set___redArg_prog
      simp only [hislt, ↓reduceIte]; rfl, by
      rw [hget]
      congr 2
      simp only [Algorithm.AsciiBytes.set, ByteArray.set!, Array.set!_eq_setIfInBounds]
      apply Array.ext (by simp)
      intro k hk1 hk2
      rw [Array.getElem_setIfInBounds (by simp at hk1; exact hk1)]
      split <;> first | rfl | omega⟩
  · have hif : i.toBitVec.slt 0#32 = false := Bool.eq_false_iff.mpr hislt
    have hi31 : i.toNat < 2 ^ 31 := by
      rw [BitVec.slt, BitVec.toInt_zero, BitVec.toInt_eq_toNat_cond] at hif
      have := i.toBitVec.isLt
      split at hif
      · omega
      · exfalso; simp only [decide_eq_false_iff_not] at hif; omega
    by_cases hle : (UInt32.ofNat g.1.data.size).toBitVec.sle i.toBitVec = true
    · have hisge : ¬(i.toNat < g.1.data.size) := by
        simp only [BitVec.sle, u32_toInt_eq_toNat hi31, u32_toInt_eq_toNat hlen31, decide_eq_true_eq] at hle
        omega
      exact ⟨_, by
        apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
        split_res_fuel 5; heap_step_blk f_Algorithm_AsciiBytes_set___redArg_prog
        simp only [hif, Bool.false_eq_true, ↓reduceIte]
        heap_step_blk f_Algorithm_AsciiBytes_set___redArg_prog
        split_res_fuel 1; rw [runJvmResFast_arraylength_byte hget]
        heap_step_blk f_Algorithm_AsciiBytes_set___redArg_prog
        simp only [hle, ↓reduceIte]; rfl, by
        rw [hget]
        congr 2
        simp only [Algorithm.AsciiBytes.set, ByteArray.set!, Array.set!_eq_setIfInBounds]
        apply Array.ext (by simp)
        intro k hk1 hk2
        rw [Array.getElem_setIfInBounds (by simp at hk1; exact hk1)]
        split <;> first | rfl | omega⟩
    · have hlef : (UInt32.ofNat g.1.data.size).toBitVec.sle i.toBitVec = false := Bool.eq_false_iff.mpr hle
      have hilt : i.toNat < g.1.data.size := by
        simp only [BitVec.sle, u32_toInt_eq_toNat hi31, u32_toInt_eq_toNat hlen31, decide_eq_false_iff_not] at hlef
        omega
      exact ⟨_, by
        apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
        split_res_fuel 5; heap_step_blk f_Algorithm_AsciiBytes_set___redArg_prog
        simp only [hif, Bool.false_eq_true, ↓reduceIte]
        heap_step_blk f_Algorithm_AsciiBytes_set___redArg_prog
        split_res_fuel 1; rw [runJvmResFast_arraylength_byte hget]
        heap_step_blk f_Algorithm_AsciiBytes_set___redArg_prog
        simp only [hlef, Bool.false_eq_true, ↓reduceIte]
        heap_step_blk f_Algorithm_AsciiBytes_set___redArg_prog
        split_res_fuel 1; rw [runJvmResFast_bastore hget hif hilt]; rfl, by
        rw [jvmHeap_get?_set_self hget]
        congr 2
        simp only [Algorithm.AsciiBytes.set, ByteArray.set!, Array.set!_eq_setIfInBounds]
        apply Array.ext (by simp [Array.size_set])
        intro k hk1 hk2
        rw [Array.getElem_setIfInBounds (by simp [Array.size_set] at hk1; exact hk1), Array.getElem_set]
        simp only [u8_toUInt32_toUInt8]⟩

theorem asciiBytesSet_1_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (addr : Nat) (g : Algorithm.AsciiBytes) (i : UInt32) (v : UInt8) (hv : v < 128)
    (hget : jh.get? addr = some (.byteArray g.1.data)) (hlen : g.1.size < 2 ^ 31) :
    ∃ st', runJvmRes 20 f_Algorithm_AsciiBytes_set___redArg_1_prog
        ⟨0, [], setLocal (setLocal (setLocal (fun _ => .null) 0 (.heapRef addr))
          1 (.i32 i)) 2 (.i32 v.toUInt32), jh, hp⟩ =
      some (.unit, st') ∧
      st'.jvmHeap.get? addr = some (.byteArray (g.set i v hv).1.data) := by
  rw [show f_Algorithm_AsciiBytes_set___redArg_1_prog = f_Algorithm_AsciiBytes_set___redArg_prog from rfl]
  exact asciiBytesSet_equiv jh hp addr g i v hv hget hlen

theorem asciiBytesSet_2_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (addr : Nat) (g : Algorithm.AsciiBytes) (i : UInt32) (v : UInt8) (hv : v < 128)
    (hget : jh.get? addr = some (.byteArray g.1.data)) (hlen : g.1.size < 2 ^ 31) :
    ∃ st', runJvmRes 20 f_Algorithm_AsciiBytes_set___redArg_2_prog
        ⟨0, [], setLocal (setLocal (setLocal (fun _ => .null) 0 (.heapRef addr))
          1 (.i32 i)) 2 (.i32 v.toUInt32), jh, hp⟩ =
      some (.unit, st') ∧
      st'.jvmHeap.get? addr = some (.byteArray (g.set i v hv).1.data) := by
  rw [show f_Algorithm_AsciiBytes_set___redArg_2_prog = f_Algorithm_AsciiBytes_set___redArg_prog from rfl]
  exact asciiBytesSet_equiv jh hp addr g i v hv hget hlen

/-! ### AsciiBytes.replicate (+ _1.._2) -/

private theorem asciiReplicate_copy_loop (rem fuel : Nat) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (srcAddr dstAddr : Nat) (n i : UInt32) (v : UInt8) (dst : Array UInt8) (locs : Nat → JvmVal)
    (hne : srcAddr ≠ dstAddr)
    (hsrc : jh.get? srcAddr = some (.byteArray (Array.replicate n.toNat v)))
    (hdst : jh.get? dstAddr = some (.byteArray dst))
    (hdst_sz : dst.size = n.toNat) (hn31 : n.toNat < 2 ^ 31)
    (hi : i.toNat ≤ n.toNat)
    (hpre : ∀ k (hk : k < i.toNat), dst[k]'(by omega) = v)
    (hrem : n.toNat - i.toNat ≤ rem) (hf : rem * 25 + 15 ≤ fuel) :
    ∃ st', runJvmResFast fuel f_Algorithm_AsciiBytes_replicate___redArg_prog 24
        (f_Algorithm_AsciiBytes_replicate___redArg_prog.drop 24)
        ⟨24, [], setLocal (setLocal (setLocal (setLocal (setLocal (setLocal locs 0 (.i32 n))
          1 (.i32 v.toUInt32)) 2 (.heapRef srcAddr)) 3 (.i32 i)) 4 (.i32 n)) 5 (.heapRef dstAddr), jh, hp⟩ =
      some (.heapRef dstAddr, st') ∧
      st'.jvmHeap.get? dstAddr = some (.byteArray (Array.replicate n.toNat v)) := by
  rcases hp with ⟨ar, u64, asc⟩
  induction rem generalizing i dst jh fuel locs with
  | zero =>
    have hieq_nat : i.toNat = n.toNat := by omega
    have hieq : i = n := UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hieq_nat)
    subst hieq
    have hle : i.toBitVec.sle i.toBitVec = true := by simp [BitVec.sle]
    exact ⟨_, by
      split_res_fuel 10; heap_step_blk f_Algorithm_AsciiBytes_replicate___redArg_prog
      simp only [hle, ↓reduceIte]
      rw [nat_add_eq_add]; rfl, by
      rw [hdst]
      congr 2
      apply Array.ext (by rw [Array.size_replicate]; exact hdst_sz)
      intro k hk1 hk2
      simp only [hdst_sz] at hk1
      rw [hpre k (by omega), Array.getElem_replicate]⟩
  | succ rem ih =>
    by_cases hle : n.toBitVec.sle i.toBitVec = true
    · have hige : n.toNat ≤ i.toNat := by
        have hi31 : i.toNat < 2 ^ 31 := by omega
        have hni : n.toBitVec.toInt = n.toNat := u32_toInt_eq_toNat hn31
        have hii : i.toBitVec.toInt = i.toNat := u32_toInt_eq_toNat hi31
        simp only [BitVec.sle, hni, hii, decide_eq_true_eq] at hle
        omega
      exact ⟨_, by
        split_res_fuel 10; heap_step_blk f_Algorithm_AsciiBytes_replicate___redArg_prog
        simp only [hle, ↓reduceIte]
        rw [nat_add_eq_add]; rfl, by
        rw [hdst]
        congr 2
        apply Array.ext (by rw [Array.size_replicate]; exact hdst_sz)
        intro k hk1 hk2
        simp only [hdst_sz] at hk1
        rw [hpre k (by omega), Array.getElem_replicate]⟩
    · have hlef : n.toBitVec.sle i.toBitVec = false := Bool.eq_false_iff.mpr hle
      have hilt : i.toNat < n.toNat := by
        have hi31 : i.toNat < 2 ^ 31 := by omega
        have hni : n.toBitVec.toInt = n.toNat := u32_toInt_eq_toNat hn31
        have hii : i.toBitVec.toInt = i.toNat := u32_toInt_eq_toNat hi31
        simp only [BitVec.sle, hni, hii, decide_eq_false_iff_not] at hlef
        omega
      have hislt : i.toBitVec.slt 0#32 = false := u32_slt_zero_of_lt_2_31 (by omega)
      have hisrc : i.toNat < (Array.replicate n.toNat v).size := by simp [hilt]
      have hidst : i.toNat < dst.size := by omega
      have hb_eq : (UInt32.ofBitVec ((Array.replicate n.toNat v)[i.toNat].toBitVec.signExtend 32)).toUInt8 = v := by
        rw [Array.getElem_replicate]
        apply UInt8.eq_of_toBitVec_eq
        change BitVec.setWidth 8 (BitVec.signExtend 32 v.toBitVec) = v.toBitVec
        exact u8_setWidth_signExtend v
      let dst1 := dst.set i.toNat v hidst
      let jh1 := jh.set dstAddr (.byteArray dst1)
      have hsrc1 : jh1.get? srcAddr = some (.byteArray (Array.replicate n.toNat v)) := by
        rw [jvmHeap_get?_set_ne _ _ hne]; exact hsrc
      have hdst1 : jh1.get? dstAddr = some (.byteArray dst1) := jvmHeap_get?_set_self hdst
      have hi1 : (i + 1).toNat = i.toNat + 1 := ui32_add1_toNat (UInt32.lt_iff_toNat_lt.mpr hilt)
      let locsNext := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal locs 0 (.i32 n))
        1 (.i32 v.toUInt32)) 2 (.heapRef srcAddr)) 3 (.i32 i)) 4 (.i32 n)) 5 (.heapRef dstAddr))
        6 (.i32 i)) 3 (.i32 (i + Int32.toUInt32 1))
      have hlocs_eq : setLocal (setLocal (setLocal (setLocal (setLocal (setLocal locsNext 0 (.i32 n))
          1 (.i32 v.toUInt32)) 2 (.heapRef srcAddr)) 3 (.i32 (i + 1))) 4 (.i32 n)) 5 (.heapRef dstAddr) = locsNext := by
        funext x
        simp only [locsNext, setLocal]
        by_cases h5 : x = 5; · simp [*]
        by_cases h4 : x = 4; · simp [*]
        by_cases h3 : x = 3; · simp [*]; rfl
        by_cases h2 : x = 2; · simp [*]
        by_cases h1 : x = 1; · simp [*]
        by_cases h0 : x = 0; · simp [*]
        simp [*]
      obtain ⟨st', hrun, hst⟩ := ih (fuel - 13) (i := i + 1) (dst := dst1) (jh := jh1) (locs := locsNext)
        hsrc1 hdst1 (by simp only [dst1, Array.size_set]; exact hdst_sz) (by omega)
        (fun k hk => by
          by_cases hki : k = i.toNat
          · subst hki; simp [dst1]
          · dsimp only [dst1]; rw [Array.getElem_set_ne (h := fun h => hki h.symm)]; exact hpre k (by omega))
        (by omega) (by omega)
      refine ⟨st', ?_, hst⟩
      rw [show fuel = (fuel - 13) + 13 from by omega]
      heap_step_blk f_Algorithm_AsciiBytes_replicate___redArg_prog
      simp only [hlef, Bool.false_eq_true, ↓reduceIte]
      heap_step_blk f_Algorithm_AsciiBytes_replicate___redArg_prog
      rw [runJvmResFast_invokestatic_step (stepStatic_ubyteArrayGet hsrc hislt hisrc)]
      heap_step_blk f_Algorithm_AsciiBytes_replicate___redArg_prog
      rw [runJvmResFast_bastore hdst hislt hidst]
      heap_step_blk f_Algorithm_AsciiBytes_replicate___redArg_prog
      simp only [hb_eq] at hrun ⊢
      rw [hlocs_eq] at hrun
      exact hrun

private theorem runJvmResFast_astore_step (f1 : Nat) (prog : List JvmInstr) (pc r : Nat)
    (v : JvmVal) (stk : List JvmVal) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (rest : List JvmInstr) :
    runJvmResFast (f1 + 1) prog pc (.astore r :: rest) ⟨pc, v :: stk, locs, jh, hp⟩ =
      runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, stk, setLocal locs r v, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr algHooks rfl (by simp) rfl rfl

private theorem asciiBytesReplicate_core (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (n : UInt32) (v : UInt8) (hv : v < 128) (hn31 : n.toNat < 2 ^ 31)
    (F : Nat) (hF : n.toNat * 25 + 15 ≤ F) :
    ∃ st', runJvmRes (F + 24) f_Algorithm_AsciiBytes_replicate___redArg_prog
        ⟨0, [], setLocal (setLocal (fun _ => .null) 0 (.i32 n)) 1 (.i32 v.toUInt32), jh, hp⟩ =
      some (.heapRef (jh.objects.size + 1), st') ∧
      st'.jvmHeap.get? (jh.objects.size + 1) =
        some (.byteArray (Algorithm.AsciiBytes.replicate n v hv).1.data) := by
  have hnslt : n.toBitVec.slt 0#32 = false := u32_slt_zero_of_lt_2_31 hn31
  have hn_eq : UInt32.ofNat (Array.replicate n.toNat (0 : UInt8)).size = n := by
    apply UInt32.eq_of_toBitVec_eq; apply BitVec.eq_of_toNat_eq
    change (UInt32.ofNat (Array.replicate n.toNat (0 : UInt8)).size).toNat = n.toBitVec.toNat
    rw [Array.size_replicate, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; rfl
  have ha0 : (jh.alloc (.byteArray (Array.replicate n.toNat 0))).2.get? jh.objects.size =
      some (.byteArray (Array.replicate n.toNat 0)) := jvmHeap_get?_alloc_self _ _
  let jh1 := (jh.alloc (.byteArray (Array.replicate n.toNat 0))).2
  let filled := Array.ofFn (n := (Array.replicate n.toNat (0 : UInt8)).size) fun _ => v.toUInt32.toUInt8
  have hfilled : filled = Array.replicate n.toNat v := by
    apply Array.ext (by simp [filled])
    intro k hk1 hk2
    simp only [filled, Array.getElem_ofFn, Array.getElem_replicate, u8_toUInt32_toUInt8]
  let jh2 := jh1.set jh.objects.size (.byteArray filled)
  have hsrc : jh2.get? jh.objects.size = some (.byteArray (Array.replicate n.toNat v)) := by
    rw [← hfilled]; exact jvmHeap_get?_set_self ha0
  have hlen : UInt32.ofNat (Array.replicate n.toNat v).size = n := by
    rw [Array.size_replicate] at hn_eq ⊢; exact hn_eq
  let jh3 := (jh2.alloc (.byteArray (Array.replicate n.toNat 0))).2
  have hsrc3 : jh3.get? jh.objects.size = some (.byteArray (Array.replicate n.toNat v)) := by
    rw [jvmHeap_get?_alloc_lt jh2 _ (by simp [jh2, jh1, Jvm.JvmHeap.set, Jvm.JvmHeap.alloc])]
    exact hsrc
  have hdst3 : jh3.get? (jh.objects.size + 1) =
      some (.byteArray (Array.replicate n.toNat 0)) := by
    have hsz2 : jh2.objects.size = jh.objects.size + 1 := by simp [jh2, jh1, Jvm.JvmHeap.set, Jvm.JvmHeap.alloc]
    dsimp only [jh3]; rw [← hsz2]; exact jvmHeap_get?_alloc_self _ _
  let initLocs : Nat → JvmVal :=
    setLocal (setLocal (setLocal (setLocal (setLocal (fun _ => (JvmVal.null : Jvm.JvmVal AlgExt))
      0 (.i32 n)) 1 (.i32 v.toUInt32)) 3 (.heapRef jh.objects.size))
      4 (.heapRef jh.objects.size)) 5 (.i32 0)
  obtain ⟨st', hloop, hst⟩ := asciiReplicate_copy_loop n.toNat F jh3 hp
    jh.objects.size (jh.objects.size + 1) n 0 v _ initLocs (by omega) hsrc3 hdst3
    (by simp) hn31 (Nat.zero_le _) (fun k hk => absurd hk (by simp)) (by omega) hF
  refine ⟨st', ?_, ?_⟩
  · apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
    heap_step_blk f_Algorithm_AsciiBytes_replicate___redArg_prog
    rw [runJvmResFast_invokestatic_step (stepStatic_ubyteArrayCtor hnslt)]
    heap_step_blk f_Algorithm_AsciiBytes_replicate___redArg_prog
    rw [runJvmResFast_invokestatic_step (stepStatic_uarraysFillAll_byte ha0)]
    heap_step_blk f_Algorithm_AsciiBytes_replicate___redArg_prog
    have ha1 : jh2.get? jh.objects.size = some (.byteArray filled) := jvmHeap_get?_set_self ha0
    rw [runJvmResFast_invokestatic_step (stepStatic_ubyteArrayGetSize ha1)]
    heap_step_blk f_Algorithm_AsciiBytes_replicate___redArg_prog
    have hlen1 : UInt32.ofNat filled.size = n := by rw [hfilled]; exact hlen
    have hnslt1 : (UInt32.ofNat filled.size).toBitVec.slt 0#32 = false := by rw [hlen1]; exact hnslt
    rw [runJvmResFast_newarray_byte hnslt1]
    change runJvmResFast (F + 1) f_Algorithm_AsciiBytes_replicate___redArg_prog 23
      (.astore 5 :: List.drop 24 f_Algorithm_AsciiBytes_replicate___redArg_prog)
      { pc := 23, stack := [Jvm.JvmVal.heapRef jh2.objects.size], locals := _, jvmHeap := _, heap := _ } = _
    rw [runJvmResFast_astore_step]
    have hsz_eq : jh2.objects.size = jh.objects.size + 1 := by simp [jh2, jh1, Jvm.JvmHeap.set, Jvm.JvmHeap.alloc]
    simp only [hsz_eq, hfilled, hlen]
    have hlocals_match : setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
        (fun _ => (JvmVal.null : Jvm.JvmVal AlgExt)) 0 (.i32 n)) 1 (.i32 v.toUInt32))
        3 (.heapRef jh.objects.size)) 4 (.heapRef jh.objects.size)) 5 (.i32 0))
        2 (.heapRef jh.objects.size)) 3 (.i32 0)) 4 (.i32 n)) 5 (.heapRef (jh.objects.size + 1)) =
        setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
        initLocs 0 (.i32 n)) 1 (.i32 v.toUInt32)) 2 (.heapRef jh.objects.size)) 3 (.i32 0)) 4 (.i32 n)) 5 (.heapRef (jh.objects.size + 1)) := by
      funext x; simp only [initLocs, setLocal]
      by_cases h5 : x = 5; · simp [*]
      by_cases h4 : x = 4; · simp [*]
      by_cases h3 : x = 3; · simp [*]
      by_cases h2 : x = 2; · simp [*]
      by_cases h1 : x = 1; · simp [*]
      by_cases h0 : x = 0; · simp [*]
      simp [*]
    rw [hlocals_match]
    dsimp only [jh3, jh2, jh1] at hloop
    exact hloop
  · simpa [Algorithm.AsciiBytes.replicate] using hst

theorem asciiBytesReplicate_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (n : UInt32) (v : UInt8) (hv : v < 128) (hn31 : n.toNat < 2 ^ 31) :
    ∃ st', runJvmRes (n.toNat * 25 + 60) f_Algorithm_AsciiBytes_replicate___redArg_prog
        ⟨0, [], setLocal (setLocal (fun _ => .null) 0 (.i32 n)) 1 (.i32 v.toUInt32), jh, hp⟩ =
      some (.heapRef (jh.objects.size + 1), st') ∧
      st'.jvmHeap.get? (jh.objects.size + 1) =
        some (.byteArray (Algorithm.AsciiBytes.replicate n v hv).1.data) := by
  rw [show n.toNat * 25 + 60 = (n.toNat * 25 + 36) + 24 from by omega]
  exact asciiBytesReplicate_core jh hp n v hv hn31 (n.toNat * 25 + 36) (by omega)

theorem asciiBytesReplicate_1_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (n : UInt32) (v : UInt8) (hv : v < 128) (hn31 : n.toNat < 2 ^ 31) :
    ∃ st', runJvmRes (n.toNat * 25 + 60) f_Algorithm_AsciiBytes_replicate___redArg_1_prog
        ⟨0, [], setLocal (setLocal (fun _ => .null) 0 (.i32 n)) 1 (.i32 v.toUInt32), jh, hp⟩ =
      some (.heapRef (jh.objects.size + 1), st') ∧
      st'.jvmHeap.get? (jh.objects.size + 1) =
        some (.byteArray (Algorithm.AsciiBytes.replicate n v hv).1.data) := by
  rw [show f_Algorithm_AsciiBytes_replicate___redArg_1_prog = f_Algorithm_AsciiBytes_replicate___redArg_prog from rfl]
  exact asciiBytesReplicate_equiv jh hp n v hv hn31

theorem asciiBytesReplicate_2_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (n : UInt32) (v : UInt8) (hv : v < 128) (hn31 : n.toNat < 2 ^ 31) :
    ∃ st', runJvmRes (n.toNat * 25 + 60) f_Algorithm_AsciiBytes_replicate___redArg_2_prog
        ⟨0, [], setLocal (setLocal (fun _ => .null) 0 (.i32 n)) 1 (.i32 v.toUInt32), jh, hp⟩ =
      some (.heapRef (jh.objects.size + 1), st') ∧
      st'.jvmHeap.get? (jh.objects.size + 1) =
        some (.byteArray (Algorithm.AsciiBytes.replicate n v hv).1.data) := by
  rw [show f_Algorithm_AsciiBytes_replicate___redArg_2_prog = f_Algorithm_AsciiBytes_replicate___redArg_prog from rfl]
  exact asciiBytesReplicate_equiv jh hp n v hv hn31

/-! ### AsciiBytes.toStringRange (+ _1.._2) -/

theorem asciiBytesToStringRange_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (addr : Nat) (g : Algorithm.AsciiBytes) (s e : UInt32)
    (hget : jh.get? addr = some (.byteArray g.1.data))
    (hsle : s.toNat ≤ e.toNat) (hel : e.toNat ≤ g.1.data.size) (hl31 : g.1.data.size < 2 ^ 31) :
    runJvm 60 f_Algorithm_AsciiBytes_toStringRange_prog
      ⟨0, [], setLocal (setLocal (setLocal (fun _ => .null) 0 (.heapRef addr)) 1 (.i32 s)) 2 (.i32 e), jh, hp⟩ =
      some (.str (g.toStringRange s e)) := by
  have hs31 : s.toNat < 2 ^ 31 := by omega
  have he31 : e.toNat < 2 ^ 31 := by omega
  have hdsz : g.1.data.size = g.1.size := rfl
  have hlen_mod : (UInt32.ofNat g.1.data.size).toNat = g.1.data.size := by
    rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  have hlen_lt : (UInt32.ofNat g.1.data.size).toNat < 2 ^ 31 := by rw [hlen_mod]; exact hl31
  have hc1 : Jvm.coerceInI32 s 0 (UInt32.ofNat g.1.data.size) = s := by
    apply coerceInI32_of_bounds hs31 (by decide) hlen_lt (Nat.zero_le _)
    rw [hlen_mod]; exact Nat.le_trans hsle hel
  have hc2 : Jvm.coerceInI32 e s (UInt32.ofNat g.1.data.size) = e := by
    apply coerceInI32_of_bounds he31 hs31 hlen_lt hsle
    rw [hlen_mod]; exact hel
  have h0_le_s : 0 ≤ s.toBitVec.toInt := by rw [u32_toInt_eq_toNat hs31]; omega
  have hs_le_e : s.toBitVec.toInt ≤ e.toBitVec.toInt := by
    rw [u32_toInt_eq_toNat hs31, u32_toInt_eq_toNat he31]; omega
  have he_le_len : e.toBitVec.toInt ≤ (g.1.data.size : Int) := by
    rw [u32_toInt_eq_toNat he31]; omega
  let sliced := Array.ofFn (n := e.toBitVec.toInt.toNat - s.toBitVec.toInt.toNat)
    fun i => g.1.data[s.toBitVec.toInt.toNat + i.val]!
  have hsliced_eq : ByteArray.mk sliced = g.1.extract s.toNat e.toNat := by
    apply ByteArray.ext
    apply Array.ext
    · change sliced.size = (g.1.extract s.toNat e.toNat).data.size
      dsimp only [sliced]
      rw [Array.size_ofFn, ByteArray.size_data, ByteArray.size_extract,
        u32_toInt_eq_toNat hs31, u32_toInt_eq_toNat he31]
      omega
    · intro k hk1 hk2
      have hk1' : k < sliced.size := by simpa [ByteArray.size_data] using hk1
      have hk2' : k < (g.1.extract s.toNat e.toNat).size := by simpa [ByteArray.size_data] using hk2
      show sliced[k]'hk1' = (g.1.extract s.toNat e.toNat)[k]'hk2'
      simp only [sliced, Array.getElem_ofFn]
      rw [ByteArray.getElem_extract, ByteArray.getElem_eq_getElem_data,
        u32_toInt_eq_toNat hs31, Int.toNat_natCast, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_getElem (by
          dsimp only [sliced] at hk1'
          rw [Array.size_ofFn, u32_toInt_eq_toNat hs31, u32_toInt_eq_toNat he31] at hk1'
          omega),
        Option.getD_some]
  have hvalid : (ByteArray.mk sliced).IsValidUTF8 := by
    rw [hsliced_eq]
    apply Algorithm.isValidUTF8_of_allAscii
    intro i hi
    rw [ByteArray.getElem_extract]
    exact g.2 _ _
  have hutf8 : String.fromUTF8? ⟨sliced⟩ = some (g.toStringRange s e) := by
    simp only [String.fromUTF8?, hvalid, ↓reduceDIte]
    congr 1
    simp only [Algorithm.AsciiBytes.toStringRange, Algorithm.asciiString, hsliced_eq, String.fromUTF8]
  rw [runJvm_eq_runJvmRes]
  suffices h : ∃ st', runJvmRes 60 f_Algorithm_AsciiBytes_toStringRange_prog
      ⟨0, [], setLocal (setLocal (setLocal (fun _ => .null) 0 (.heapRef addr)) 1 (.i32 s)) 2 (.i32 e), jh, hp⟩ =
      some (.str (g.toStringRange s e), st') by
    rcases h with ⟨st', h⟩; rw [h]; rfl
  exact ⟨_, by
    apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
    split_res_fuel 10; heap_step_blk f_Algorithm_AsciiBytes_toStringRange_prog
    split_res_fuel 1; rw [runJvmResFast_arraylength_byte hget]
    heap_step_blk f_Algorithm_AsciiBytes_toStringRange_prog
    rw [hc1]
    split_res_fuel 1; rw [runJvmResFast_arraylength_byte hget]
    heap_step_blk f_Algorithm_AsciiBytes_toStringRange_prog
    rw [hc2]
    split_res_fuel 1
    rw [runJvmResFast_invokestatic_step (stepStatic_arraysCopyOfRange_byte hget h0_le_s hs_le_e he_le_len)]
    heap_step_blk f_Algorithm_AsciiBytes_toStringRange_prog
    have ha_sl := jvmHeap_get?_alloc_self jh (.byteArray sliced)
    split_res_fuel 1
    rw [runJvmResFast_invokestatic_step (stepStatic_stringsDecodeToString ha_sl hutf8)]; rfl⟩

theorem asciiBytesToStringRange_1_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (addr : Nat) (g : Algorithm.AsciiBytes) (s e : UInt32)
    (hget : jh.get? addr = some (.byteArray g.1.data))
    (hsle : s.toNat ≤ e.toNat) (hel : e.toNat ≤ g.1.data.size) (hl31 : g.1.data.size < 2 ^ 31) :
    runJvm 60 f_Algorithm_AsciiBytes_toStringRange_1_prog
      ⟨0, [], setLocal (setLocal (setLocal (fun _ => .null) 0 (.heapRef addr)) 1 (.i32 s)) 2 (.i32 e), jh, hp⟩ =
      some (.str (g.toStringRange s e)) := by
  rw [show f_Algorithm_AsciiBytes_toStringRange_1_prog = f_Algorithm_AsciiBytes_toStringRange_prog from rfl]
  exact asciiBytesToStringRange_equiv jh hp addr g s e hget hsle hel hl31

theorem asciiBytesToStringRange_2_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (addr : Nat) (g : Algorithm.AsciiBytes) (s e : UInt32)
    (hget : jh.get? addr = some (.byteArray g.1.data))
    (hsle : s.toNat ≤ e.toNat) (hel : e.toNat ≤ g.1.data.size) (hl31 : g.1.data.size < 2 ^ 31) :
    runJvm 60 f_Algorithm_AsciiBytes_toStringRange_2_prog
      ⟨0, [], setLocal (setLocal (setLocal (fun _ => .null) 0 (.heapRef addr)) 1 (.i32 s)) 2 (.i32 e), jh, hp⟩ =
      some (.str (g.toStringRange s e)) := by
  rw [show f_Algorithm_AsciiBytes_toStringRange_2_prog = f_Algorithm_AsciiBytes_toStringRange_prog from rfl]
  exact asciiBytesToStringRange_equiv jh hp addr g s e hget hsle hel hl31

/-! ### decodeCharAt___lam__0 (+ _1.._2) -/

theorem decodeCharAtLam0_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (addr : Nat) (elems : Array UInt8) (p k : UInt32)
    (hget : jh.get? addr = some (.byteArray elems))
    (hslt : (p + k).toBitVec.slt 0#32 = false)
    (hlt : (p + k).toNat < elems.size) :
    runJvm 30 f_Algorithm_decodeCharAt___lam__0_prog
      ⟨0, [], setLocal (setLocal (setLocal (fun _ => .null) 0 (.i32 p)) 1 (.heapRef addr)) 2 (.i32 k), jh, hp⟩ =
      some (.i32 (elems[(p + k).toNat].toUInt32 &&& 0x3F)) := by
  rw [runJvm_eq_runJvmRes]
  suffices h : ∃ st', runJvmRes 30 f_Algorithm_decodeCharAt___lam__0_prog
      ⟨0, [], setLocal (setLocal (setLocal (fun _ => .null) 0 (.i32 p)) 1 (.heapRef addr)) 2 (.i32 k), jh, hp⟩ =
      some (.i32 (elems[(p + k).toNat].toUInt32 &&& 0x3F), st') by
    rcases h with ⟨st', h⟩; rw [h]; rfl
  exact ⟨_, by
    apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
    split_res_fuel 10; heap_step_blk f_Algorithm_decodeCharAt___lam__0_prog
    split_res_fuel 1; rw [runJvmResFast_baload hget hslt hlt]
    heap_step_blk f_Algorithm_decodeCharAt___lam__0_prog
    rw [u8_signExtend_and_63]⟩

theorem decodeCharAtLam0_1_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (addr : Nat) (elems : Array UInt8) (p k : UInt32)
    (hget : jh.get? addr = some (.byteArray elems))
    (hslt : (p + k).toBitVec.slt 0#32 = false) (hlt : (p + k).toNat < elems.size) :
    runJvm 30 f_Algorithm_decodeCharAt___lam__0_1_prog
      ⟨0, [], setLocal (setLocal (setLocal (fun _ => .null) 0 (.i32 p)) 1 (.heapRef addr)) 2 (.i32 k), jh, hp⟩ =
      some (.i32 (elems[(p + k).toNat].toUInt32 &&& 0x3F)) := by
  rw [show f_Algorithm_decodeCharAt___lam__0_1_prog = f_Algorithm_decodeCharAt___lam__0_prog from rfl]
  exact decodeCharAtLam0_equiv jh hp addr elems p k hget hslt hlt

theorem decodeCharAtLam0_2_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (addr : Nat) (elems : Array UInt8) (p k : UInt32)
    (hget : jh.get? addr = some (.byteArray elems))
    (hslt : (p + k).toBitVec.slt 0#32 = false) (hlt : (p + k).toNat < elems.size) :
    runJvm 30 f_Algorithm_decodeCharAt___lam__0_2_prog
      ⟨0, [], setLocal (setLocal (setLocal (fun _ => .null) 0 (.i32 p)) 1 (.heapRef addr)) 2 (.i32 k), jh, hp⟩ =
      some (.i32 (elems[(p + k).toNat].toUInt32 &&& 0x3F)) := by
  rw [show f_Algorithm_decodeCharAt___lam__0_2_prog = f_Algorithm_decodeCharAt___lam__0_prog from rfl]
  exact decodeCharAtLam0_equiv jh hp addr elems p k hget hslt hlt

end Algorithm.JvmVerification
