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

namespace Algorithm.JvmVerification
open Algorithm.JvmBytecode

/-! ### Heap & Object-Array Stepping Infrastructure for Families 2–6 -/

theorem nat_add_eq_add (a b : Nat) : Nat.add a b = a + b := rfl

theorem runJvmValFast_split_fuel (m : Nat) {k : Nat}
    (prog : List JvmInstr) (pc : Nat) (instrs : List JvmInstr) (st : JvmState)
    (hk : m ≤ k) :
    runJvmValFast k prog pc instrs st = runJvmValFast ((k - m) + m) prog pc instrs st := by
  rw [Nat.sub_add_cancel hk]

theorem runJvmResFast_split_fuel (m : Nat) {k : Nat}
    (prog : List JvmInstr) (pc : Nat) (instrs : List JvmInstr) (st : JvmState)
    (hk : m ≤ k) :
    runJvmResFast k prog pc instrs st = runJvmResFast ((k - m) + m) prog pc instrs st := by
  rw [Nat.sub_add_cancel hk]

open Lean Elab Tactic in
elab "split_val_fuel " n:term : tactic => do
  evalTactic (← `(tactic| rw [runJvmValFast_split_fuel $n]))
  let g1 :: g2 :: rest ← getGoals | throwError "split_val_fuel: expected fuel side goal"
  setGoals [g2]
  evalTactic (← `(tactic| (try simp only [nat_add_eq_add]); omega))
  let rem ← getGoals
  unless rem.isEmpty do throwError "split_val_fuel: omega failed"
  setGoals (g1 :: rest)

open Lean Elab Tactic in
elab "split_res_fuel " n:term : tactic => do
  evalTactic (← `(tactic| rw [runJvmResFast_split_fuel $n]))
  let g1 :: g2 :: rest ← getGoals | throwError "split_res_fuel: expected fuel side goal"
  setGoals [g2]
  evalTactic (← `(tactic| (try simp only [nat_add_eq_add]); omega))
  let rem ← getGoals
  unless rem.isEmpty do throwError "split_res_fuel: omega failed"
  setGoals (g1 :: rest)

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

theorem jvmHeap_get?_alloc_self {Ext : Type} (jh : Jvm.JvmHeap Ext) (obj : Jvm.HeapObj Ext) :
    (jh.alloc obj).2.get? jh.objects.size = some obj := by
  simp [Jvm.JvmHeap.alloc, Jvm.JvmHeap.get?]

theorem jvmHeap_get?_alloc_lt {Ext : Type} (jh : Jvm.JvmHeap Ext) (obj : Jvm.HeapObj Ext)
    {a : Nat} (ha : a < jh.objects.size) :
    (jh.alloc obj).2.get? a = jh.get? a := by
  simp [Jvm.JvmHeap.alloc, Jvm.JvmHeap.get?, Array.getElem?_push, ha, Nat.ne_of_lt ha]

theorem jvmHeap_get?_set_ne {Ext : Type} (jh : Jvm.JvmHeap Ext) {a b : Nat}
    (obj : Jvm.HeapObj Ext) (hne : a ≠ b) :
    (jh.set b obj).get? a = jh.get? a := by
  simp only [Jvm.JvmHeap.set, Jvm.JvmHeap.get?]
  split
  · simp [Array.getElem?_set_ne, Ne.symm hne]
  · rfl

theorem u32_shl1_add1_eq {n : Nat} :
    (UInt32.ofNat n <<< 1) + 1 = 2 * UInt32.ofNat n + 1 := by
  refine congrArg (· + 1) ?_
  apply UInt32.eq_of_toBitVec_eq; apply BitVec.eq_of_toNat_eq
  change (UInt32.ofNat n <<< 1).toNat = (2 * UInt32.ofNat n).toNat
  rw [UInt32.toNat_shiftLeft, UInt32.toNat_mul]
  rw [show (1 : UInt32).toNat % 32 = 1 from by decide]
  rw [show (2 : UInt32).toNat = 2 from by decide]
  rw [Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_comm]

theorem u8_signExtend_and_63 (b : UInt8) :
    (UInt32.ofBitVec (b.toBitVec.signExtend 32) &&& 255) &&& 63 = b.toUInt32 &&& 63 := by
  have h : ∀ w : UInt8, (UInt32.ofBitVec (w.toBitVec.signExtend 32) &&& 255) &&& 63 = w.toUInt32 &&& 63 := by
    decide
  exact h b

theorem coerceInI32_of_bounds {v lo hi : UInt32}
    (hv : v.toNat < 2 ^ 31) (hlo : lo.toNat < 2 ^ 31) (hhi : hi.toNat < 2 ^ 31)
    (h1 : lo.toNat ≤ v.toNat) (h2 : v.toNat ≤ hi.toNat) :
    Jvm.coerceInI32 v lo hi = v := by
  have hslt1 : v.toBitVec.slt lo.toBitVec = false := by
    simp only [BitVec.slt, u32_toInt_eq_toNat hv, u32_toInt_eq_toNat hlo]
    exact decide_eq_false (by omega)
  have hslt2 : hi.toBitVec.slt v.toBitVec = false := by
    simp only [BitVec.slt, u32_toInt_eq_toNat hhi, u32_toInt_eq_toNat hv]
    exact decide_eq_false (by omega)
  simp [Jvm.coerceInI32, hslt1, hslt2]

def isHeapStop : JvmInstr → Bool
  | .invokestatic _ _ _ => true
  | .invokevirtual _ _ _ => true
  | .invokespecial _ _ _ => true
  | .invokeinterface _ _ _ => true
  | .baload => true
  | .aaload => true
  | .bastore => true
  | .aastore => true
  | .newarray _ => true
  | .anewarray _ => true
  | .arraylength => true
  | .checkcast _ => true
  | .instanceof _ => true
  | i => isBranchInstr i

private theorem isBranchInstr_of_isHeapStop_false {i : JvmInstr} (h : isHeapStop i = false) :
    isBranchInstr i = false := by
  cases i <;> simp [isHeapStop, isBranchInstr] at h ⊢

def stepHeapChunk : Nat → Nat → Nat → List JvmInstr → JvmState → BlockChunkRes AlgExt AlgHeap
  | _, 0, _, _, _ => .done none
  | 0, f1 + 1, pc, instrs, st => .cont (f1 + 1) pc instrs st
  | m + 1, f1 + 1, pc, instrs, st =>
    match instrs with
    | [] => .done none
    | instr :: rest =>
      if isHeapStop instr then .cont (f1 + 1) pc (instr :: rest) st
      else match instr with
      | .i2l =>
        match rest with
        | .lconst 4294967295 :: .land :: rest' =>
          match f1 with
          | 0 => .done none
          | f2 + 1 =>
            match f2 with
            | 0 => .done none
            | f3 + 1 =>
              match st.stack with
              | .i32 x :: s =>
                stepHeapChunk m f3 (pc + 3) rest' { st with pc := pc + 3, stack := .i64 x.toUInt64 :: s }
              | _ => .done none
        | _ =>
          match stepInstr instr { st with pc := pc } with
          | .inl (some st') =>
            if st'.pc = pc + 1 then stepHeapChunk m f1 (pc + 1) rest st'
            else .jump f1 st'
          | .inl none => .done none
          | .inr res => .done res
      | _ =>
        match stepInstr instr { st with pc := pc } with
        | .inl (some st') =>
          if st'.pc = pc + 1 then stepHeapChunk m f1 (pc + 1) rest st'
          else .jump f1 st'
        | .inl none => .done none
        | .inr res => .done res

private theorem stepHeapChunk_cons_ne (m f1 pc : Nat) (instr : JvmInstr) (rest : List JvmInstr)
    (st : JvmState) (hno : ¬∃ r', instr = .i2l ∧ rest = .lconst 4294967295 :: .land :: r') :
    stepHeapChunk (m + 1) (f1 + 1) pc (instr :: rest) st =
      if isHeapStop instr then .cont (f1 + 1) pc (instr :: rest) st
      else match stepInstr instr { st with pc := pc } with
      | .inl (some st') =>
        if st'.pc = pc + 1 then stepHeapChunk m f1 (pc + 1) rest st'
        else .jump f1 st'
      | .inl none => .done none
      | .inr res => .done res := by
  cases instr with
  | i2l =>
    cases rest with
    | nil => rfl
    | cons a r1 =>
      cases a <;> try rfl
      case lconst v =>
        by_cases hv : v = 4294967295
        · subst hv
          cases r1 with
          | nil => rfl
          | cons b r2 =>
            cases b <;> try rfl
            exfalso; exact hno ⟨r2, rfl, rfl⟩
        · simp [stepHeapChunk, hv]
  | _ => rfl

private theorem runJvmValFast_stepHeapChunk_aux (m : Nat) (fuel : Nat) (prog : List JvmInstr)
    (pc : Nat) (instrs : List JvmInstr) (st : JvmState) :
    runJvmValFast fuel prog pc instrs st = afterBlockChunk (stepHeapChunk m fuel pc instrs st) prog := by
  induction m generalizing fuel pc instrs st with
  | zero => cases fuel <;> rfl
  | succ m ih =>
    cases fuel with
    | zero => rfl
    | succ f1 =>
      cases instrs with
      | nil => rfl
      | cons instr rest =>
        by_cases hpat : ∃ r', instr = .i2l ∧ rest = .lconst 4294967295 :: .land :: r'
        · rcases hpat with ⟨r', rfl, rfl⟩
          cases f1 with
          | zero => rfl
          | succ f2 =>
            cases f2 with
            | zero => rfl
            | succ f3 =>
              simp only [runJvmValFast, Jvm.runJvmValFast, stepHeapChunk, isHeapStop]
              cases st.stack with
              | nil => rfl
              | cons hd tl => cases hd with | i32 x => exact ih f3 (pc + 3) r' _ | _ => rfl
        · by_cases hst : isHeapStop instr = true
          · rw [stepHeapChunk_cons_ne m f1 pc instr rest st hpat]
            simp only [hst, ↓reduceIte, afterBlockChunk, Jvm.afterBlockChunk, runJvmValFast]
          · have hstf : isHeapStop instr = false := Bool.eq_false_iff.mpr hst
            have hbrf : isBranchInstr instr = false := isBranchInstr_of_isHeapStop_false hstf
            have hno' : ¬(instr = .i2l ∧ ∃ r', rest = .lconst 4294967295 :: .land :: r') :=
              fun ⟨h1, r', h2⟩ => hpat ⟨r', h1, h2⟩
            rw [stepHeapChunk_cons_ne m f1 pc instr rest st hpat,
              runJvmValFast_step_nonbranch f1 prog pc instr rest st hbrf hno']
            simp only [hstf, Bool.false_eq_true, ↓reduceIte]
            cases hstep : stepInstr instr { st with pc := pc } with
            | inl o =>
              cases o with
              | none => rfl
              | some st' =>
                by_cases hpc : st'.pc = pc + 1
                · simp only [hpc, ↓reduceIte]; exact ih f1 (pc + 1) rest st'
                · simp only [hpc, ↓reduceIte, afterBlockChunk, Jvm.afterBlockChunk, runJvmValFast]
            | inr res => cases res <;> rfl

theorem runJvmValFast_stepHeapChunk (maxSteps fuel : Nat) (prog : List JvmInstr) (pc : Nat)
    (instrs : List JvmInstr) (st : JvmState) :
    runJvmValFast fuel prog pc instrs st = afterBlockChunk (stepHeapChunk maxSteps fuel pc instrs st) prog :=
  runJvmValFast_stepHeapChunk_aux maxSteps fuel prog pc instrs st

def stepResHeapChunk : Nat → Nat → Nat → List JvmInstr → JvmState → BlockResChunkRes AlgExt AlgHeap
  | _, 0, _, _, _ => .done none
  | 0, f1 + 1, pc, instrs, st => .cont (f1 + 1) pc instrs st
  | m + 1, f1 + 1, pc, instrs, st =>
    match instrs with
    | [] => .done none
    | instr :: rest =>
      if isHeapStop instr then .cont (f1 + 1) pc (instr :: rest) st
      else match instr with
      | .i2l =>
        match rest with
        | .lconst 4294967295 :: .land :: rest' =>
          match f1 with
          | 0 => .done none
          | f2 + 1 =>
            match f2 with
            | 0 => .done none
            | f3 + 1 =>
              match st.stack with
              | .i32 x :: s =>
                stepResHeapChunk m f3 (pc + 3) rest' { st with pc := pc + 3, stack := .i64 x.toUInt64 :: s }
              | _ => .done none
        | _ =>
          match stepInstr instr { st with pc := pc } with
          | .inl (some st') =>
            if st'.pc = pc + 1 then stepResHeapChunk m f1 (pc + 1) rest st'
            else .jump f1 st'
          | .inl none => .done none
          | .inr (some v) => .done (some (v, { st with pc := pc }))
          | .inr none => .done none
      | _ =>
        match stepInstr instr { st with pc := pc } with
        | .inl (some st') =>
          if st'.pc = pc + 1 then stepResHeapChunk m f1 (pc + 1) rest st'
          else .jump f1 st'
        | .inl none => .done none
        | .inr (some v) => .done (some (v, { st with pc := pc }))
        | .inr none => .done none

private theorem stepResHeapChunk_cons_ne (m f1 pc : Nat) (instr : JvmInstr) (rest : List JvmInstr)
    (st : JvmState) (hno : ¬∃ r', instr = .i2l ∧ rest = .lconst 4294967295 :: .land :: r') :
    stepResHeapChunk (m + 1) (f1 + 1) pc (instr :: rest) st =
      if isHeapStop instr then .cont (f1 + 1) pc (instr :: rest) st
      else match stepInstr instr { st with pc := pc } with
      | .inl (some st') =>
        if st'.pc = pc + 1 then stepResHeapChunk m f1 (pc + 1) rest st'
        else .jump f1 st'
      | .inl none => .done none
      | .inr (some v) => .done (some (v, { st with pc := pc }))
      | .inr none => .done none := by
  cases instr with
  | i2l =>
    cases rest with
    | nil => rfl
    | cons a r1 =>
      cases a <;> try rfl
      case lconst v =>
        by_cases hv : v = 4294967295
        · subst hv
          cases r1 with
          | nil => rfl
          | cons b r2 =>
            cases b <;> try rfl
            exfalso; exact hno ⟨r2, rfl, rfl⟩
        · simp [stepResHeapChunk, hv]
  | _ => rfl

private theorem runJvmResFast_stepResHeapChunk_aux (m : Nat) (fuel : Nat) (prog : List JvmInstr)
    (pc : Nat) (instrs : List JvmInstr) (st : JvmState) :
    runJvmResFast fuel prog pc instrs st = afterResBlockChunk (stepResHeapChunk m fuel pc instrs st) prog := by
  induction m generalizing fuel pc instrs st with
  | zero => cases fuel <;> rfl
  | succ m ih =>
    cases fuel with
    | zero => rfl
    | succ f1 =>
      cases instrs with
      | nil => rfl
      | cons instr rest =>
        by_cases hpat : ∃ r', instr = .i2l ∧ rest = .lconst 4294967295 :: .land :: r'
        · rcases hpat with ⟨r', rfl, rfl⟩
          cases f1 with
          | zero => rfl
          | succ f2 =>
            cases f2 with
            | zero => rfl
            | succ f3 =>
              simp only [runJvmResFast, Jvm.runJvmResFast, stepResHeapChunk, isHeapStop]
              cases st.stack with
              | nil => rfl
              | cons hd tl => cases hd with | i32 x => exact ih f3 (pc + 3) r' _ | _ => rfl
        · by_cases hst : isHeapStop instr = true
          · rw [stepResHeapChunk_cons_ne m f1 pc instr rest st hpat]
            simp only [hst, ↓reduceIte, afterResBlockChunk, Jvm.afterResBlockChunk, runJvmResFast]
          · have hstf : isHeapStop instr = false := Bool.eq_false_iff.mpr hst
            have hbrf : isBranchInstr instr = false := isBranchInstr_of_isHeapStop_false hstf
            have hno' : ¬(instr = .i2l ∧ ∃ r', rest = .lconst 4294967295 :: .land :: r') :=
              fun ⟨h1, r', h2⟩ => hpat ⟨r', h1, h2⟩
            rw [stepResHeapChunk_cons_ne m f1 pc instr rest st hpat,
              runJvmResFast_step_nonbranch f1 prog pc instr rest st hbrf hno']
            simp only [hstf, Bool.false_eq_true, ↓reduceIte]
            cases hstep : stepInstr instr { st with pc := pc } with
            | inl o =>
              cases o with
              | none => rfl
              | some st' =>
                by_cases hpc : st'.pc = pc + 1
                · simp only [hpc, ↓reduceIte]; exact ih f1 (pc + 1) rest st'
                · simp only [hpc, ↓reduceIte, afterResBlockChunk, Jvm.afterResBlockChunk, runJvmResFast]
            | inr res => cases res <;> rfl

theorem runJvmResFast_stepResHeapChunk (maxSteps fuel : Nat) (prog : List JvmInstr) (pc : Nat)
    (instrs : List JvmInstr) (st : JvmState) :
    runJvmResFast fuel prog pc instrs st = afterResBlockChunk (stepResHeapChunk maxSteps fuel pc instrs st) prog :=
  runJvmResFast_stepResHeapChunk_aux maxSteps fuel prog pc instrs st

/-! ### Generic Heap Instruction Stepping Lemmas -/

theorem runJvmResFast_checkcast_objArray {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {rest : List JvmInstr} {pc0 : Nat} {addr : Nat} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {cls : String} {elems : Array JvmVal}
    (hget : jh.get? addr = some (.objArray cls elems))
    (hcls : cls = "java/lang/Object" ∨ cls = "[Ljava/lang/Object;") :
    runJvmResFast (f + 1) prog pc (.checkcast "[Ljava/lang/Object;" :: rest)
        ⟨pc0, .heapRef addr :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .heapRef addr :: stkRest, locs, jh, hp⟩ := by
  have hm : (Jvm.HeapObj.objArray cls elems).matchesType "[Ljava/lang/Object;" = true := by
    rcases hcls with rfl | rfl <;> simp [Jvm.HeapObj.matchesType]
  have hstep : Jvm.stepInstr algHooks (.checkcast "[Ljava/lang/Object;")
      ⟨pc, .heapRef addr :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .heapRef addr :: stkRest, locs, jh, hp⟩) := by
    simp [Jvm.stepInstr, Jvm.JvmHeap.checkCast, Jvm.JvmHeap.checkInstanceOf, hget, hm]
  simp only [runJvmResFast]
  rw [Jvm.runJvmResFast_step_nonbranch algHooks (hbr := rfl) (hno := by simp)]
  simp only [hstep, ↓reduceIte]

theorem runJvmValFast_checkcast_objArray {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {rest : List JvmInstr} {pc0 : Nat} {addr : Nat} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {cls : String} {elems : Array JvmVal}
    (hget : jh.get? addr = some (.objArray cls elems))
    (hcls : cls = "java/lang/Object" ∨ cls = "[Ljava/lang/Object;") :
    runJvmValFast (f + 1) prog pc (.checkcast "[Ljava/lang/Object;" :: rest)
        ⟨pc0, .heapRef addr :: stkRest, locs, jh, hp⟩ =
      runJvmValFast f prog (pc + 1) rest ⟨pc + 1, .heapRef addr :: stkRest, locs, jh, hp⟩ := by
  have hm : (Jvm.HeapObj.objArray cls elems).matchesType "[Ljava/lang/Object;" = true := by
    rcases hcls with rfl | rfl <;> simp [Jvm.HeapObj.matchesType]
  have hstep : Jvm.stepInstr algHooks (.checkcast "[Ljava/lang/Object;")
      ⟨pc, .heapRef addr :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .heapRef addr :: stkRest, locs, jh, hp⟩) := by
    simp [Jvm.stepInstr, Jvm.JvmHeap.checkCast, Jvm.JvmHeap.checkInstanceOf, hget, hm]
  simp only [runJvmValFast]
  rw [Jvm.runJvmValFast_step_nonbranch algHooks (hbr := rfl) (hno := by simp)]
  simp only [hstep, ↓reduceIte]

theorem runJvmResFast_checkcast_boxedInt {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {rest : List JvmInstr} {pc0 : Nat} {v : UInt32} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {cls : String}
    (hcls : cls = "java/lang/Integer" ∨ cls = "java/lang/Number" ∨ cls = "java/lang/Object") :
    runJvmResFast (f + 1) prog pc (.checkcast cls :: rest)
        ⟨pc0, .boxedInt v :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .boxedInt v :: stkRest, locs, jh, hp⟩ := by
  have hstep : Jvm.stepInstr algHooks (.checkcast cls)
      ⟨pc, .boxedInt v :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .boxedInt v :: stkRest, locs, jh, hp⟩) := by
    rcases hcls with rfl | rfl | rfl <;> rfl
  simp only [runJvmResFast]
  rw [Jvm.runJvmResFast_step_nonbranch algHooks (hbr := rfl) (hno := by simp)]
  simp only [hstep, ↓reduceIte]

theorem runJvmValFast_checkcast_boxedInt {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {rest : List JvmInstr} {pc0 : Nat} {v : UInt32} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {cls : String}
    (hcls : cls = "java/lang/Integer" ∨ cls = "java/lang/Number" ∨ cls = "java/lang/Object") :
    runJvmValFast (f + 1) prog pc (.checkcast cls :: rest)
        ⟨pc0, .boxedInt v :: stkRest, locs, jh, hp⟩ =
      runJvmValFast f prog (pc + 1) rest ⟨pc + 1, .boxedInt v :: stkRest, locs, jh, hp⟩ := by
  have hstep : Jvm.stepInstr algHooks (.checkcast cls)
      ⟨pc, .boxedInt v :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .boxedInt v :: stkRest, locs, jh, hp⟩) := by
    rcases hcls with rfl | rfl | rfl <;> rfl
  simp only [runJvmValFast]
  rw [Jvm.runJvmValFast_step_nonbranch algHooks (hbr := rfl) (hno := by simp)]
  simp only [hstep, ↓reduceIte]

theorem runJvmResFast_checkcast_boxedUInt {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {rest : List JvmInstr} {pc0 : Nat} {v : UInt32} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {cls : String}
    (hcls : cls = "kotlin/UInt" ∨ cls = "java/lang/Object") :
    runJvmResFast (f + 1) prog pc (.checkcast cls :: rest)
        ⟨pc0, .boxedUInt v :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .boxedUInt v :: stkRest, locs, jh, hp⟩ := by
  have hstep : Jvm.stepInstr algHooks (.checkcast cls)
      ⟨pc, .boxedUInt v :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .boxedUInt v :: stkRest, locs, jh, hp⟩) := by
    rcases hcls with rfl | rfl <;> rfl
  simp only [runJvmResFast]
  rw [Jvm.runJvmResFast_step_nonbranch algHooks (hbr := rfl) (hno := by simp)]
  simp only [hstep, ↓reduceIte]

theorem runJvmResFast_checkcast_boxedULong {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {rest : List JvmInstr} {pc0 : Nat} {v : UInt64} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {cls : String}
    (hcls : cls = "kotlin/ULong" ∨ cls = "java/lang/Object") :
    runJvmResFast (f + 1) prog pc (.checkcast cls :: rest)
        ⟨pc0, .boxedULong v :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .boxedULong v :: stkRest, locs, jh, hp⟩ := by
  have hstep : Jvm.stepInstr algHooks (.checkcast cls)
      ⟨pc, .boxedULong v :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .boxedULong v :: stkRest, locs, jh, hp⟩) := by
    rcases hcls with rfl | rfl <;> rfl
  simp only [runJvmResFast]
  rw [Jvm.runJvmResFast_step_nonbranch algHooks (hbr := rfl) (hno := by simp)]
  simp only [hstep, ↓reduceIte]

theorem runJvmResFast_instanceof_boxedUInt_int {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {rest : List JvmInstr} {pc0 : Nat} {v : UInt32} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.instanceof "java/lang/Integer" :: rest)
        ⟨pc0, .boxedUInt v :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .i32 0 :: stkRest, locs, jh, hp⟩ := by
  have hstep : Jvm.stepInstr algHooks (.instanceof "java/lang/Integer")
      ⟨pc, .boxedUInt v :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 0 :: stkRest, locs, jh, hp⟩) := rfl
  simp only [runJvmResFast]
  rw [Jvm.runJvmResFast_step_nonbranch algHooks (hbr := rfl) (hno := by simp)]
  simp only [hstep, ↓reduceIte]

theorem runJvmResFast_instanceof_boxedInt_int {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {rest : List JvmInstr} {pc0 : Nat} {v : UInt32} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.instanceof "java/lang/Integer" :: rest)
        ⟨pc0, .boxedInt v :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .i32 1 :: stkRest, locs, jh, hp⟩ := by
  have hstep : Jvm.stepInstr algHooks (.instanceof "java/lang/Integer")
      ⟨pc, .boxedInt v :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 1 :: stkRest, locs, jh, hp⟩) := rfl
  simp only [runJvmResFast]
  rw [Jvm.runJvmResFast_step_nonbranch algHooks (hbr := rfl) (hno := by simp)]
  simp only [hstep, ↓reduceIte]

theorem runJvmResFast_aaload {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {rest : List JvmInstr} {pc0 : Nat} {idx : UInt32} {addr : Nat} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {cls : String} {elems : Array JvmVal}
    (hget : jh.get? addr = some (.objArray cls elems))
    (hslt : idx.toBitVec.slt 0#32 = false) (hlt : idx.toNat < elems.size) :
    runJvmResFast (f + 1) prog pc (.aaload :: rest)
        ⟨pc0, .i32 idx :: .heapRef addr :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, elems[idx.toNat] :: stkRest, locs, jh, hp⟩ := by
  have hstep := Jvm.stepInstr_aaload algHooks (pc := pc) (stkRest := stkRest)
    (locs := locs) (hp := hp) hget hslt hlt
  simp only [runJvmResFast]
  rw [Jvm.runJvmResFast_step_nonbranch algHooks (hbr := rfl) (hno := by simp)]
  simp only [hstep, ↓reduceIte]

theorem runJvmResFast_aastore {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {rest : List JvmInstr} {pc0 : Nat} {val : JvmVal} {idx : UInt32} {addr : Nat} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {cls : String} {elems : Array JvmVal}
    (hget : jh.get? addr = some (.objArray cls elems))
    (hslt : idx.toBitVec.slt 0#32 = false) (hlt : idx.toNat < elems.size) :
    runJvmResFast (f + 1) prog pc (.aastore :: rest)
        ⟨pc0, val :: .i32 idx :: .heapRef addr :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest
        ⟨pc + 1, stkRest, locs, jh.set addr (.objArray cls (elems.set idx.toNat val hlt)), hp⟩ := by
  have hstep := Jvm.stepInstr_aastore algHooks (v := val) (pc := pc) (stkRest := stkRest)
    (locs := locs) (hp := hp) hget hslt hlt
  simp only [runJvmResFast]
  rw [Jvm.runJvmResFast_step_nonbranch algHooks (hbr := rfl) (hno := by simp)]
  simp only [hstep, ↓reduceIte]

theorem runJvmValFast_aastore {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {rest : List JvmInstr} {pc0 : Nat} {val : JvmVal} {idx : UInt32} {addr : Nat} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {cls : String} {elems : Array JvmVal}
    (hget : jh.get? addr = some (.objArray cls elems))
    (hslt : idx.toBitVec.slt 0#32 = false) (hlt : idx.toNat < elems.size) :
    runJvmValFast (f + 1) prog pc (.aastore :: rest)
        ⟨pc0, val :: .i32 idx :: .heapRef addr :: stkRest, locs, jh, hp⟩ =
      runJvmValFast f prog (pc + 1) rest
        ⟨pc + 1, stkRest, locs, jh.set addr (.objArray cls (elems.set idx.toNat val hlt)), hp⟩ := by
  have hstep := Jvm.stepInstr_aastore algHooks (v := val) (pc := pc) (stkRest := stkRest)
    (locs := locs) (hp := hp) hget hslt hlt
  simp only [runJvmValFast]
  rw [Jvm.runJvmValFast_step_nonbranch algHooks (hbr := rfl) (hno := by simp)]
  simp only [hstep, ↓reduceIte]

theorem runJvmResFast_baload {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {rest : List JvmInstr} {pc0 : Nat} {idx : UInt32} {addr : Nat} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {elems : Array UInt8}
    (hget : jh.get? addr = some (.byteArray elems))
    (hslt : idx.toBitVec.slt 0#32 = false) (hlt : idx.toNat < elems.size) :
    runJvmResFast (f + 1) prog pc (.baload :: rest)
        ⟨pc0, .i32 idx :: .heapRef addr :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest
        ⟨pc + 1, .i32 (UInt32.ofBitVec (elems[idx.toNat].toBitVec.signExtend 32)) :: stkRest, locs, jh, hp⟩ := by
  have hstep := Jvm.stepInstr_baload algHooks (pc := pc) (stkRest := stkRest)
    (locs := locs) (hp := hp) hget hslt hlt
  simp only [runJvmResFast]
  rw [Jvm.runJvmResFast_step_nonbranch algHooks (hbr := rfl) (hno := by simp)]
  simp only [hstep, ↓reduceIte]

theorem runJvmResFast_arraylength_obj {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {rest : List JvmInstr} {pc0 : Nat} {addr : Nat} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {cls : String} {elems : Array JvmVal}
    (hget : jh.get? addr = some (.objArray cls elems)) :
    runJvmResFast (f + 1) prog pc (.arraylength :: rest)
        ⟨pc0, .heapRef addr :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest
        ⟨pc + 1, .i32 (UInt32.ofNat elems.size) :: stkRest, locs, jh, hp⟩ := by
  have hstep : Jvm.stepInstr algHooks .arraylength ⟨pc, .heapRef addr :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 (UInt32.ofNat elems.size) :: stkRest, locs, jh, hp⟩) := by
    simp [Jvm.stepInstr, hget, Jvm.HeapObj.arrayLength?]
  simp only [runJvmResFast]
  rw [Jvm.runJvmResFast_step_nonbranch algHooks (hbr := rfl) (hno := by simp)]
  simp only [hstep, ↓reduceIte]

theorem runJvmValFast_arraylength_obj {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {rest : List JvmInstr} {pc0 : Nat} {addr : Nat} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {cls : String} {elems : Array JvmVal}
    (hget : jh.get? addr = some (.objArray cls elems)) :
    runJvmValFast (f + 1) prog pc (.arraylength :: rest)
        ⟨pc0, .heapRef addr :: stkRest, locs, jh, hp⟩ =
      runJvmValFast f prog (pc + 1) rest
        ⟨pc + 1, .i32 (UInt32.ofNat elems.size) :: stkRest, locs, jh, hp⟩ := by
  have hstep : Jvm.stepInstr algHooks .arraylength ⟨pc, .heapRef addr :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 (UInt32.ofNat elems.size) :: stkRest, locs, jh, hp⟩) := by
    simp [Jvm.stepInstr, hget, Jvm.HeapObj.arrayLength?]
  simp only [runJvmValFast]
  rw [Jvm.runJvmValFast_step_nonbranch algHooks (hbr := rfl) (hno := by simp)]
  simp only [hstep, ↓reduceIte]

theorem runJvmResFast_arraylength_byte {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {rest : List JvmInstr} {pc0 : Nat} {addr : Nat} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {elems : Array UInt8}
    (hget : jh.get? addr = some (.byteArray elems)) :
    runJvmResFast (f + 1) prog pc (.arraylength :: rest)
        ⟨pc0, .heapRef addr :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest
        ⟨pc + 1, .i32 (UInt32.ofNat elems.size) :: stkRest, locs, jh, hp⟩ := by
  have hstep : Jvm.stepInstr algHooks .arraylength ⟨pc, .heapRef addr :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 (UInt32.ofNat elems.size) :: stkRest, locs, jh, hp⟩) := by
    simp [Jvm.stepInstr, hget, Jvm.HeapObj.arrayLength?]
  simp only [runJvmResFast]
  rw [Jvm.runJvmResFast_step_nonbranch algHooks (hbr := rfl) (hno := by simp)]
  simp only [hstep, ↓reduceIte]

theorem runJvmValFast_arraylength_byte {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {rest : List JvmInstr} {pc0 : Nat} {addr : Nat} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {elems : Array UInt8}
    (hget : jh.get? addr = some (.byteArray elems)) :
    runJvmValFast (f + 1) prog pc (.arraylength :: rest)
        ⟨pc0, .heapRef addr :: stkRest, locs, jh, hp⟩ =
      runJvmValFast f prog (pc + 1) rest
        ⟨pc + 1, .i32 (UInt32.ofNat elems.size) :: stkRest, locs, jh, hp⟩ := by
  have hstep : Jvm.stepInstr algHooks .arraylength ⟨pc, .heapRef addr :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 (UInt32.ofNat elems.size) :: stkRest, locs, jh, hp⟩) := by
    simp [Jvm.stepInstr, hget, Jvm.HeapObj.arrayLength?]
  simp only [runJvmValFast]
  rw [Jvm.runJvmValFast_step_nonbranch algHooks (hbr := rfl) (hno := by simp)]
  simp only [hstep, ↓reduceIte]

theorem runJvmResFast_anewarray_obj {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {rest : List JvmInstr} {pc0 : Nat} {n : UInt32} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hslt : n.toBitVec.slt 0#32 = false) :
    runJvmResFast (f + 1) prog pc (.anewarray "java/lang/Object" :: rest)
        ⟨pc0, .i32 n :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest
        ⟨pc + 1, .heapRef jh.objects.size :: stkRest, locs,
          (jh.alloc (.objArray "java/lang/Object" (Array.replicate n.toNat .null))).2, hp⟩ := by
  have hstep := Jvm.stepInstr_anewarray algHooks "java/lang/Object" (pc := pc) (stkRest := stkRest)
    (locs := locs) (jh := jh) (hp := hp) hslt
  simp only [runJvmResFast]
  rw [Jvm.runJvmResFast_step_nonbranch algHooks (hbr := rfl) (hno := by simp)]
  simp only [hstep, ↓reduceIte]

/-! ### Additional Static/Virtual Stepping Theorems & Heap Tactics -/

theorem stepStatic_uintBox
    {pc : Nat} {v : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, v :: rest, locs, jh, hp⟩
      "kotlin/UInt" "box-impl" "(I)Lkotlin/UInt;" =
      .inl (some ⟨pc + 1, .boxedUInt v.asI32 :: rest, locs, jh, hp⟩) := rfl

theorem stepVirtual_integer_intValue
    {pc : Nat} {v : UInt32} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeVirtual ⟨pc, .boxedInt v :: rest, locs, jh, hp⟩
      "java/lang/Integer" "intValue" "()I" =
      .inl (some ⟨pc + 1, .i32 v :: rest, locs, jh, hp⟩) := rfl

theorem stepVirtual_number_intValue
    {pc : Nat} {v : UInt32} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeVirtual ⟨pc, .boxedInt v :: rest, locs, jh, hp⟩
      "java/lang/Number" "intValue" "()I" =
      .inl (some ⟨pc + 1, .i32 v :: rest, locs, jh, hp⟩) := rfl

theorem stepVirtual_pair_getFirst
    {pc : Nat} {a b : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeVirtual ⟨pc, .pair a b :: rest, locs, jh, hp⟩
      "kotlin/Pair" "getFirst" "()Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, a :: rest, locs, jh, hp⟩) := rfl

theorem stepVirtual_ulong_unbox
    {pc : Nat} {v : UInt64} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeVirtual ⟨pc, .boxedULong v :: rest, locs, jh, hp⟩
      "kotlin/ULong" "unbox-impl" "()J" =
      .inl (some ⟨pc + 1, .i64 v :: rest, locs, jh, hp⟩) := rfl

theorem stepStatic_arraysFillAll_obj
    {pc : Nat} {handler elem : JvmVal} {addr : Nat} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {cls : String} {elems : Array JvmVal} {desc : String}
    (hget : jh.get? addr = some (.objArray cls elems)) :
    stepInvokeStatic ⟨pc, handler :: .i32 6 :: .i32 0 :: .i32 0 :: elem :: .heapRef addr :: stkRest, locs, jh, hp⟩
      "kotlin/collections/ArraysKt" "fill$default" desc =
      .inl (some ⟨pc + 1, stkRest, locs,
        jh.set addr (.objArray cls (Array.ofFn (n := elems.size) fun _ => elem)), hp⟩) :=
  Jvm.stepInvokeStatic_arraysFillAll_obj algHooks (desc := desc) hget

theorem stepStatic_uarraysFillAll_byte
    {pc : Nat} {handler elem : JvmVal} {addr : Nat} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {elems : Array UInt8} {desc : String}
    (hget : jh.get? addr = some (.byteArray elems)) :
    stepInvokeStatic ⟨pc, handler :: .i32 6 :: .i32 0 :: .i32 0 :: elem :: .heapRef addr :: stkRest, locs, jh, hp⟩
      "kotlin/collections/unsigned/UArraysKt" "fill-WpHrYlw$default" desc =
      .inl (some ⟨pc + 1, stkRest, locs,
        jh.set addr (.byteArray (Array.ofFn (n := elems.size) fun _ => elem.asI32.toUInt8)), hp⟩) :=
  Jvm.stepInvokeStatic_uarraysFillAll_byte algHooks (desc := desc) hget

theorem stepStatic_arraysCopyOfRange_obj
    {pc : Nat} {fromIdx toIdx : UInt32} {addr : Nat} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {cls : String} {elems : Array JvmVal} {desc : String}
    (hget : jh.get? addr = some (.objArray cls elems))
    (h1 : 0 ≤ fromIdx.toBitVec.toInt)
    (h2 : fromIdx.toBitVec.toInt ≤ toIdx.toBitVec.toInt)
    (h3 : toIdx.toBitVec.toInt ≤ elems.size) :
    stepInvokeStatic ⟨pc, .i32 toIdx :: .i32 fromIdx :: .heapRef addr :: stkRest, locs, jh, hp⟩
      "kotlin/collections/ArraysKt" "copyOfRange" desc =
      let f := fromIdx.toBitVec.toInt.toNat
      let n := toIdx.toBitVec.toInt.toNat - f
      let sliced := Array.ofFn (n := n) (fun i => elems[f + i.val]!)
      .inl (some ⟨pc + 1, .heapRef jh.objects.size :: stkRest, locs, (jh.alloc (.objArray cls sliced)).2, hp⟩) :=
  Jvm.stepInvokeStatic_arraysCopyOfRange_obj algHooks (desc := desc) hget h1 h2 h3

theorem stepStatic_arraysCopyOfRange_byte
    {pc : Nat} {fromIdx toIdx : UInt32} {addr : Nat} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {elems : Array UInt8} {desc : String}
    (hget : jh.get? addr = some (.byteArray elems))
    (h1 : 0 ≤ fromIdx.toBitVec.toInt)
    (h2 : fromIdx.toBitVec.toInt ≤ toIdx.toBitVec.toInt)
    (h3 : toIdx.toBitVec.toInt ≤ elems.size) :
    stepInvokeStatic ⟨pc, .i32 toIdx :: .i32 fromIdx :: .heapRef addr :: stkRest, locs, jh, hp⟩
      "kotlin/collections/ArraysKt" "copyOfRange" desc =
      let f := fromIdx.toBitVec.toInt.toNat
      let n := toIdx.toBitVec.toInt.toNat - f
      let sliced := Array.ofFn (n := n) (fun i => elems[f + i.val]!)
      .inl (some ⟨pc + 1, .heapRef jh.objects.size :: stkRest, locs, (jh.alloc (.byteArray sliced)).2, hp⟩) :=
  Jvm.stepInvokeStatic_arraysCopyOfRange_byte algHooks (desc := desc) hget h1 h2 h3

theorem stepStatic_stringsDecodeToString
    {pc : Nat} {addr : Nat} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {elems : Array UInt8} {s : String}
    (hget : jh.get? addr = some (.byteArray elems))
    (hutf8 : String.fromUTF8? ⟨elems⟩ = some s) :
    stepInvokeStatic ⟨pc, .heapRef addr :: stkRest, locs, jh, hp⟩
      "kotlin/text/StringsKt" "decodeToString" "([B)Ljava/lang/String;" =
      .inl (some ⟨pc + 1, .str s :: stkRest, locs, jh, hp⟩) :=
  Jvm.stepInvokeStatic_stringsDecodeToString algHooks hget hutf8

theorem stepStatic_ubyteArrayCtor
    {pc : Nat} {n : UInt32} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hslt : n.toBitVec.slt 0#32 = false) :
    stepInvokeStatic ⟨pc, .i32 n :: stkRest, locs, jh, hp⟩
      "kotlin/UByteArray" "constructor-impl" "(I)[B" =
      .inl (some ⟨pc + 1, .heapRef jh.objects.size :: stkRest, locs,
        (jh.alloc (.byteArray (Array.replicate n.toNat 0))).2, hp⟩) :=
  Jvm.stepInvokeStatic_ubyteArrayCtor algHooks hslt

theorem stepStatic_ubyteArrayGetSize
    {pc : Nat} {addr : Nat} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {elems : Array UInt8}
    (hget : jh.get? addr = some (.byteArray elems)) :
    stepInvokeStatic ⟨pc, .heapRef addr :: stkRest, locs, jh, hp⟩
      "kotlin/UByteArray" "getSize-impl" "([B)I" =
      .inl (some ⟨pc + 1, .i32 (UInt32.ofNat elems.size) :: stkRest, locs, jh, hp⟩) :=
  Jvm.stepInvokeStatic_ubyteArrayGetSize algHooks hget

theorem stepStatic_ubyteArrayGet
    {pc : Nat} {idx : UInt32} {addr : Nat} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {elems : Array UInt8}
    (hget : jh.get? addr = some (.byteArray elems))
    (hslt : idx.toBitVec.slt 0#32 = false) (hlt : idx.toNat < elems.size) :
    stepInvokeStatic ⟨pc, .i32 idx :: .heapRef addr :: stkRest, locs, jh, hp⟩
      "kotlin/UByteArray" "get-w2LRezQ" "([BI)B" =
      .inl (some ⟨pc + 1, .i32 (UInt32.ofBitVec (elems[idx.toNat].toBitVec.signExtend 32)) :: stkRest,
        locs, jh, hp⟩) :=
  Jvm.stepInvokeStatic_ubyteArrayGet algHooks hget hslt hlt

theorem stepStatic_uint32ToInt32
    {pc : Nat} {cls : String} {x : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hcls : cls = "Life105LeanKt" ∨ cls = "Life106LeanKt" ∨ cls = "MacroCellLeanKt" ∨
      cls = "PlaintextLeanKt" ∨ cls = "RleLeanKt") :
    stepInvokeStatic ⟨pc, x :: rest, locs, jh, hp⟩
      cls "f_Algorithm_uint32ToInt32-WZ4Q5Ns" "(I)I" =
      .inl (some ⟨pc + 1, .i32 x.asI32 :: rest, locs, jh, hp⟩) := by
  rcases hcls with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem stepStatic_decodeCharAtLam_heap
    {pc : Nat} {cls : String} {k p : JvmVal} {addr : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {elems : Array UInt8}
    (hcls : cls = "Life105LeanKt" ∨ cls = "Life106LeanKt" ∨ cls = "MacroCellLeanKt" ∨
      cls = "PlaintextLeanKt" ∨ cls = "RleLeanKt")
    (hget : jh.get? addr = some (.byteArray elems))
    (hslt : (p.asI32 + k.asI32).toBitVec.slt 0#32 = false)
    (hlt : (p.asI32 + k.asI32).toNat < elems.size) :
    stepInvokeStatic ⟨pc, k :: .heapRef addr :: p :: rest, locs, jh, hp⟩
      cls "f_Algorithm_decodeCharAt___lam__0-Mv_zs3U" "(I[BI)I" =
      .inl (some ⟨pc + 1, .i32 (elems[(p.asI32 + k.asI32).toNat].toUInt32 &&& 0x3F) :: rest,
        locs, jh, hp⟩) := by
  rcases hcls with rfl | rfl | rfl | rfl | rfl <;>
    (refine Eq.trans (b := match jh.get? addr with
      | some (.byteArray el) =>
        let idx := p.asI32 + k.asI32
        if idx.toBitVec.slt 0#32 then .inr none
        else if _ : idx.toNat < el.size then
          .inl (some ⟨pc + 1, .i32 (el[idx.toNat].toUInt32 &&& 0x3F) :: rest, locs, jh, hp⟩)
        else .inr none
      | _ => .inr none) rfl ?_
     rw [hget]; dsimp only; rw [hslt]
     simp only [Bool.false_eq_true, ↓reduceIte]
     split
     · rfl
     · rename_i hn; exact absurd hlt (by simpa [UInt32.toNat_add] using hn))

theorem stepStatic_scanDigits_heap
    {pc : Nat} {cls : String} {acc p limit : JvmVal} {addr : Nat} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {elems : Array UInt8}
    (hcls : cls = "Life105LeanKt" ∨ cls = "Life106LeanKt" ∨ cls = "MacroCellLeanKt" ∨
      cls = "PlaintextLeanKt" ∨ cls = "RleLeanKt")
    (hget : jh.get? addr = some (.byteArray elems)) :
    stepInvokeStatic ⟨pc, acc :: p :: limit :: .heapRef addr :: rest, locs, jh, hp⟩
      cls "f_Algorithm_scanDigits-G4XTHLI" "([BIIJ)Lkotlin/Pair;" =
      let r := Algorithm.scanDigits ⟨elems⟩ limit.asI32 p.asI32 acc.asI64
      .inl (some ⟨pc + 1, .pair (.boxedUInt r.1) (.boxedULong r.2) :: rest,
        locs, jh, hp⟩) := by
  rcases hcls with rfl | rfl | rfl | rfl | rfl <;>
    (refine Eq.trans (b := match jh.get? addr with
      | some (.byteArray el) =>
        let r := Algorithm.scanDigits ⟨el⟩ limit.asI32 p.asI32 acc.asI64
        .inl (some ⟨pc + 1, .pair (.boxedUInt r.1) (.boxedULong r.2) :: rest, locs, jh, hp⟩)
      | _ => .inr none) rfl ?_
     rw [hget])

/-! ### Branch Cons Lemmas & Automated Heap Block Stepper -/

theorem evalBranchInstrCons_if_icmpge (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (b a : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    evalBranchInstrCons f1 prog pc (.if_icmpge target) rest ⟨pc0, b :: a :: s, locs, jh, hp⟩ =
      if b.asI32.toBitVec.sle a.asI32.toBitVec then
        runJvmValFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmValFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ := rfl

theorem evalResBranchInstrCons_if_icmpge (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (b a : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    evalResBranchInstrCons f1 prog pc (.if_icmpge target) rest ⟨pc0, b :: a :: s, locs, jh, hp⟩ =
      if b.asI32.toBitVec.sle a.asI32.toBitVec then
        runJvmResFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ := rfl

theorem evalBranchInstrCons_if_icmple (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (b a : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    evalBranchInstrCons f1 prog pc (.if_icmple target) rest ⟨pc0, b :: a :: s, locs, jh, hp⟩ =
      if a.asI32.toBitVec.sle b.asI32.toBitVec then
        runJvmValFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmValFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ := rfl

theorem evalResBranchInstrCons_if_icmple (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (b a : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    evalResBranchInstrCons f1 prog pc (.if_icmple target) rest ⟨pc0, b :: a :: s, locs, jh, hp⟩ =
      if a.asI32.toBitVec.sle b.asI32.toBitVec then
        runJvmResFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ := rfl

theorem evalResBranchInstrCons_tableswitch (f1 : Nat) (prog : List JvmInstr) (pc : Nat)
    (low : Int32) (targets : List Nat) (defaultTarget : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (key : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    evalResBranchInstrCons f1 prog pc (.tableswitch low targets defaultTarget) rest
        ⟨pc0, key :: s, locs, jh, hp⟩ =
      let t := Jvm.tableswitchTarget key.asI32 low targets defaultTarget
      runJvmResFast f1 prog t (prog.drop t) ⟨t, s, locs, jh, hp⟩ := rfl

theorem evalBranchInstrCons_tableswitch (f1 : Nat) (prog : List JvmInstr) (pc : Nat)
    (low : Int32) (targets : List Nat) (defaultTarget : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (key : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    evalBranchInstrCons f1 prog pc (.tableswitch low targets defaultTarget) rest
        ⟨pc0, key :: s, locs, jh, hp⟩ =
      let t := Jvm.tableswitchTarget key.asI32 low targets defaultTarget
      runJvmValFast f1 prog t (prog.drop t) ⟨t, s, locs, jh, hp⟩ := rfl

section HeapTactics
open Lean Elab Tactic

private def extractHeapStrLit? (e : Lean.Expr) : Lean.MetaM (Option String) := do
  let ew ← Lean.Meta.whnf e
  match ew.consumeMData with
  | .lit (.strVal s) => return some s
  | _ => return none

private def heapInvokeLookup : Lean.Name → String → String → String → List (Lean.Name × Nat)
  | ``Jvm.JvmInstr.invokestatic, "kotlin/UInt", "box-impl", _ => [(``stepStatic_uintBox, 0)]
  | ``Jvm.JvmInstr.invokevirtual, "java/lang/Integer", "intValue", _ => [(``stepVirtual_integer_intValue, 0)]
  | ``Jvm.JvmInstr.invokevirtual, "java/lang/Number", "intValue", _ => [(``stepVirtual_number_intValue, 0)]
  | ``Jvm.JvmInstr.invokevirtual, "kotlin/Pair", "getFirst", _ => [(``stepVirtual_pair_getFirst, 0)]
  | ``Jvm.JvmInstr.invokevirtual, "kotlin/ULong", "unbox-impl", _ => [(``stepVirtual_ulong_unbox, 0)]
  | _, _, _, _ => []

def tryStepHeapInvoke : TacticM Bool := do
  if ← tryStepFlatInvoke then return true
  let tgt := (← getMainTarget).consumeMData
  let some (_, lhs, _) := tgt.eq? | return false
  let (inner, isMap) := unwrapRunLhs lhs
  let isRes := inner.isAppOfArity ``runJvmResFast 5
  let isVal := inner.isAppOfArity ``runJvmValFast 5
  if !isRes && !isVal then return false
  let instrs ← Lean.Meta.whnf (inner.getArg! 3)
  if !instrs.isAppOfArity ``List.cons 3 then return false
  let instr ← Lean.Meta.whnf (instrs.getArg! 1)
  let some opName := instr.getAppFn.constName? | return false
  if opName != ``Jvm.JvmInstr.invokestatic && opName != ``Jvm.JvmInstr.invokevirtual &&
     opName != ``Jvm.JvmInstr.invokespecial && opName != ``Jvm.JvmInstr.invokeinterface then
    return false
  let args := instr.getAppArgs
  if args.size < 3 then return false
  let (some cls, some method, some desc) :=
    (← extractHeapStrLit? args[0]!, ← extractHeapStrLit? args[1]!, ← extractHeapStrLit? args[2]!) | return false
  let bridgeName :=
    if !isRes then
      if opName == ``Jvm.JvmInstr.invokestatic then ``runJvmValFast_invokestatic_step
      else ``runJvmValFast_invokevirtual_step
    else
      if opName == ``Jvm.JvmInstr.invokestatic then ``runJvmResFast_invokestatic_step
      else ``runJvmResFast_invokevirtual_step
  let bridgeId := Lean.mkIdent bridgeName
  for (thmName, nHyps) in heapInvokeLookup opName cls method desc do
    let thmId := Lean.mkIdent thmName
    let saved ← getGoals
    try
      if isMap then
        if nHyps == 0 then evalTactic (← `(tactic| (conv => lhs; arg 2; rw [$bridgeId ($thmId)])))
        else evalTactic (← `(tactic| (conv => lhs; arg 2; rw [$bridgeId ($thmId rfl)])))
      else
        if nHyps == 0 then evalTactic (← `(tactic| (conv => lhs; rw [$bridgeId ($thmId)])))
        else evalTactic (← `(tactic| (conv => lhs; rw [$bridgeId ($thmId rfl)])))
      evalTactic (← `(tactic| (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)))
      return true
    catch _ => setGoals saved
  return false

def isRunJvmAtHeapNonStop : TacticM Bool := do
  let tgt := (← getMainTarget).consumeMData
  let some (_, lhs, _) := tgt.eq? | return false
  let (inner, _) := unwrapRunLhs lhs
  if inner.isAppOfArity ``runJvmValFast 5 || inner.isAppOfArity ``runJvmResFast 5 then
    let instrs ← Lean.Meta.whnf (inner.getArg! 3)
    if instrs.isAppOfArity ``List.cons 3 then
      let instr := instrs.getArg! 1
      let br ← Lean.Meta.whnf (Lean.mkApp (Lean.mkConst ``isHeapStop) instr)
      return br.isConstOf ``Bool.false
  return false

elab "heap_step_one_chunk" : tactic => do
  let tgt := (← getMainTarget).consumeMData
  let some (_, lhs, _) := tgt.eq? | return ()
  let (inner, isMap) := unwrapRunLhs lhs
  let isRes := inner.isAppOfArity ``runJvmResFast 5
  if isRes then
    evalTactic (← `(tactic| rw [runJvmResFast_stepResHeapChunk 120]))
  else
    evalTactic (← `(tactic| rw [runJvmValFast_stepHeapChunk 120]))
  if !(← getUnsolvedGoals).isEmpty then
    if isMap then
      evalTactic (← `(tactic| (conv => lhs; arg 2; arg 1; jvm_whnf_blk)))
    else
      evalTactic (← `(tactic| (conv => lhs; arg 1; jvm_whnf_blk)))
    let tgt2 := (← getMainTarget).consumeMData
    let some (_, lhs2, _) := tgt2.eq? | return ()
    let (afterApp, _) := unwrapRunLhs lhs2
    let chunkRes := (afterApp.getArg! 0).consumeMData
    if let some cn := chunkRes.getAppFn.constName? then
      if !isRes then
        if cn == ``Jvm.BlockChunkRes.cont then evalTactic (← `(tactic| rw [afterBlockChunk_cont]))
        else if cn == ``Jvm.BlockChunkRes.jump then evalTactic (← `(tactic| rw [afterBlockChunk_jump]))
        else if cn == ``Jvm.BlockChunkRes.done then evalTactic (← `(tactic| rw [afterBlockChunk_done]))
      else
        if cn == ``Jvm.BlockResChunkRes.cont then evalTactic (← `(tactic| rw [afterResBlockChunk_cont]))
        else if cn == ``Jvm.BlockResChunkRes.jump then evalTactic (← `(tactic| rw [afterResBlockChunk_jump]))
        else if cn == ``Jvm.BlockResChunkRes.done then
          evalTactic (← `(tactic| rw [afterResBlockChunk_done]))
          rwOptionMapResult
    if !(← getUnsolvedGoals).isEmpty then
      evalTactic (← `(tactic| (conv => lhs; norm_jvm_locals)))
      evalTactic (← `(tactic| (conv => lhs; jvm_whnf_run_args)))

def rwEvalHeapBranchByInstr (isRes : Bool) (instr : Lean.Expr) : TacticM Unit := do
  let some n := instr.consumeMData.getAppFn.constName? | return ()
  let thm : Option Lean.Name :=
    if !isRes then
      if n == ``Jvm.JvmInstr.if_icmpge then some ``evalBranchInstrCons_if_icmpge
      else if n == ``Jvm.JvmInstr.if_icmple then some ``evalBranchInstrCons_if_icmple
      else if n == ``Jvm.JvmInstr.tableswitch then some ``evalBranchInstrCons_tableswitch
      else none
    else
      if n == ``Jvm.JvmInstr.if_icmpge then some ``evalResBranchInstrCons_if_icmpge
      else if n == ``Jvm.JvmInstr.if_icmple then some ``evalResBranchInstrCons_if_icmple
      else if n == ``Jvm.JvmInstr.tableswitch then some ``evalResBranchInstrCons_tableswitch
      else none
  if let some tn := thm then
    let id := Lean.mkIdent tn
    evalTactic (← `(tactic| try rw [$id:ident]))
  else
    rwEvalBranchByInstr isRes instr

elab "heap_step_nonbranch_chunks" : tactic => do
  for _ in [:400] do
    if (← getUnsolvedGoals).isEmpty then break
    if ← tryStepHeapInvoke then
      continue
    else if ← isRunJvmAtHeapNonStop then
      evalTactic (← `(tactic| heap_step_one_chunk))
    else if ← isRunJvmAtForwardGoto then
      let tgt := (← getMainTarget).consumeMData
      let some (_, lhs, _) := tgt.eq? | break
      let (inner, isMap) := unwrapRunLhs lhs
      let isRes := inner.isAppOfArity ``runJvmResFast 5
      if isRes then
        evalTactic (← `(tactic| rw [runJvmResFast_at_branch_cons (hbr := rfl)]))
      else
        evalTactic (← `(tactic| rw [runJvmValFast_at_branch_cons (hbr := rfl)]))
      if !(← getUnsolvedGoals).isEmpty then
        if isMap then
          evalTactic (← `(tactic| (
            (conv => lhs; arg 2; arg 1; whnf)
            (conv => lhs; arg 2; arg 3; whnf)
            (conv => lhs; arg 2; arg 4; whnf)
            (conv => lhs; arg 2; arg 6; jvm_whnf_blk))))
          let tgt2 := (← getMainTarget).consumeMData
          let some (_, lhs2, _) := tgt2.eq? | break
          let (evalApp, _) := unwrapRunLhs lhs2
          rwEvalHeapBranchByInstr isRes (evalApp.getArg! 3)
          if !(← getUnsolvedGoals).isEmpty then
            evalTactic (← `(tactic| (
              (conv => lhs; try rw [option_map_ite])
              (conv => lhs; norm_jvm_locals; jvm_whnf_run_args))))
        else
          evalTactic (← `(tactic| (
            (conv => lhs; arg 1; whnf)
            (conv => lhs; arg 3; whnf)
            (conv => lhs; arg 4; whnf)
            (conv => lhs; arg 6; jvm_whnf_blk))))
          let tgt2 := (← getMainTarget).consumeMData
          let some (_, lhs2, _) := tgt2.eq? | break
          rwEvalHeapBranchByInstr isRes (lhs2.getArg! 3)
          if !(← getUnsolvedGoals).isEmpty then
            evalTactic (← `(tactic| (conv => lhs; norm_jvm_locals; jvm_whnf_run_args)))
    else
      break

elab "heap_step_branch_tail" : tactic => do
  let tgt := (← getMainTarget).consumeMData
  let some (_, lhs, _) := tgt.eq? | return ()
  let (inner, isMap) := unwrapRunLhs lhs
  let isRes := inner.isAppOfArity ``runJvmResFast 5
  if !isRes && !inner.isAppOfArity ``runJvmValFast 5 then return ()
  if isRes then
    evalTactic (← `(tactic| rw [runJvmResFast_at_branch_cons (hbr := rfl)]))
  else
    evalTactic (← `(tactic| rw [runJvmValFast_at_branch_cons (hbr := rfl)]))
  if !(← getUnsolvedGoals).isEmpty then
    if isMap then
      evalTactic (← `(tactic| (
        (conv => lhs; arg 2; arg 1; whnf)
        (conv => lhs; arg 2; arg 3; whnf)
        (conv => lhs; arg 2; arg 4; whnf)
        (conv => lhs; arg 2; arg 6; jvm_whnf_blk))))
      let tgt2 := (← getMainTarget).consumeMData
      let some (_, lhs2, _) := tgt2.eq? | return ()
      let (evalApp, _) := unwrapRunLhs lhs2
      rwEvalHeapBranchByInstr isRes (evalApp.getArg! 3)
      if !(← getUnsolvedGoals).isEmpty then
        evalTactic (← `(tactic| (
          (conv => lhs; try rw [option_map_ite])
          (conv => lhs; norm_jvm_locals; jvm_whnf_run_args))))
    else
      evalTactic (← `(tactic| (
        (conv => lhs; arg 1; whnf)
        (conv => lhs; arg 3; whnf)
        (conv => lhs; arg 4; whnf)
        (conv => lhs; arg 6; jvm_whnf_blk))))
      let tgt2 := (← getMainTarget).consumeMData
      let some (_, lhs2, _) := tgt2.eq? | return ()
      rwEvalHeapBranchByInstr isRes (lhs2.getArg! 3)
      if !(← getUnsolvedGoals).isEmpty then
        evalTactic (← `(tactic| (conv => lhs; norm_jvm_locals; jvm_whnf_run_args)))

def isRunJvmAtHeapBranch : TacticM Bool := do
  let tgt := (← getMainTarget).consumeMData
  let some (_, lhs, _) := tgt.eq? | return false
  let (inner, _) := unwrapRunLhs lhs
  if inner.isAppOfArity ``runJvmValFast 5 || inner.isAppOfArity ``runJvmResFast 5 then
    let instrs ← Lean.Meta.whnf (inner.getArg! 3)
    if instrs.isAppOfArity ``List.cons 3 then
      let instr := instrs.getArg! 1
      let br ← Lean.Meta.whnf (Lean.mkApp (Lean.mkConst ``isBranchInstr) instr)
      return br.isConstOf ``Bool.true
  return false

elab "heap_step_blk" _prog:term : tactic => do
  evalTactic (← `(tactic| heap_step_nonbranch_chunks))
  if !(← getUnsolvedGoals).isEmpty then
    if ← isRunJvmAtHeapBranch then
      evalTactic (← `(tactic| heap_step_branch_tail))

end HeapTactics

end Algorithm.JvmVerification
