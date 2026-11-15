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
import proofs.JvmEquiv.HeapInfra
import proofs.JvmEquiv.SharedStep

namespace Algorithm.JvmVerification

macro "norm_res_fuel" : tactic =>
  `(tactic| (conv => lhs; try zeta; arg 1; simp only [Nat.succ_eq_add_one, nat_add_eq_add]))

theorem compareUnsigned_slt_zero (a b : UInt32) :
    (if a == b then (0 : UInt32) else if a < b then 4294967295 else 1).toBitVec.slt 0#32 = decide (a < b) := by
  by_cases h1 : a == b
  · have hab : a = b := LawfulBEq.eq_of_beq h1; subst hab; simp
  · by_cases h2 : a < b <;> simp [h1, h2]

theorem runJvmResFast_ifle_branch {f pc tgt : Nat} {prog rest : List JvmInstr}
    {v : UInt32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hv : v.toBitVec.sle 0#32 = true) :
    runJvmResFast (f + 1) prog pc (.ifle tgt :: rest) ⟨pc, .i32 v :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog tgt (prog.drop tgt) ⟨tgt, stk, locs, jh, hp⟩ := by
  conv => lhs; dsimp only [runJvmResFast]; rw [Jvm.runJvmResFast.eq_def]
  simp [runJvmResFast, Jvm.JvmVal.asI32, hv]

theorem runJvmResFast_ifle_fallthrough {f pc tgt : Nat} {prog rest : List JvmInstr}
    {v : UInt32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hv : v.toBitVec.sle 0#32 = false) :
    runJvmResFast (f + 1) prog pc (.ifle tgt :: rest) ⟨pc, .i32 v :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, stk, locs, jh, hp⟩ := by
  conv => lhs; dsimp only [runJvmResFast]; rw [Jvm.runJvmResFast.eq_def]
  simp [runJvmResFast, Jvm.JvmVal.asI32, hv]

theorem runJvmResFast_iflt_branch {f pc tgt : Nat} {prog rest : List JvmInstr}
    {v : UInt32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hv : v.toBitVec.slt 0#32 = true) :
    runJvmResFast (f + 1) prog pc (.iflt tgt :: rest) ⟨pc, .i32 v :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog tgt (prog.drop tgt) ⟨tgt, stk, locs, jh, hp⟩ := by
  conv => lhs; dsimp only [runJvmResFast]; rw [Jvm.runJvmResFast.eq_def]
  simp [runJvmResFast, Jvm.JvmVal.asI32, hv]

theorem runJvmResFast_iflt_fallthrough {f pc tgt : Nat} {prog rest : List JvmInstr}
    {v : UInt32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hv : v.toBitVec.slt 0#32 = false) :
    runJvmResFast (f + 1) prog pc (.iflt tgt :: rest) ⟨pc, .i32 v :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, stk, locs, jh, hp⟩ := by
  conv => lhs; dsimp only [runJvmResFast]; rw [Jvm.runJvmResFast.eq_def]
  simp [runJvmResFast, Jvm.JvmVal.asI32, hv]

theorem runJvmResFast_ifeq_branch {f pc tgt : Nat} {prog rest : List JvmInstr}
    {v : UInt32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hv : v = 0) :
    runJvmResFast (f + 1) prog pc (.ifeq tgt :: rest) ⟨pc, .i32 v :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog tgt (prog.drop tgt) ⟨tgt, stk, locs, jh, hp⟩ := by
  subst hv; conv => lhs; dsimp only [runJvmResFast]; rw [Jvm.runJvmResFast.eq_def]
  simp [runJvmResFast, Jvm.JvmVal.asI32]

theorem runJvmResFast_ifeq_fallthrough {f pc tgt : Nat} {prog rest : List JvmInstr}
    {v : UInt32} {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (h : (v == 0) = false) :
    runJvmResFast (f + 1) prog pc (.ifeq tgt :: rest) ⟨pc, .i32 v :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, stk, locs, jh, hp⟩ := by
  conv => lhs; dsimp only [runJvmResFast]; rw [Jvm.runJvmResFast.eq_def]
  simp [runJvmResFast, Jvm.JvmVal.asI32, h]

theorem runJvmResFast_ifnonnull_branch {f pc tgt : Nat} {prog rest : List JvmInstr}
    {v : JvmVal} {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} (hnn : v.isNull = false) :
    runJvmResFast (f + 1) prog pc (.ifnonnull tgt :: rest) ⟨pc, v :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog tgt (prog.drop tgt) ⟨tgt, stkRest, locs, jh, hp⟩ := by
  rw [runJvmResFast]
  change (if !v.isNull then
      runJvmResFast f prog tgt (prog.drop tgt) ⟨tgt, stkRest, locs, jh, hp⟩
    else
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, stkRest, locs, jh, hp⟩) = _
  simp [hnn]

theorem runJvmResFast_ifnonnull_fallthrough {f pc tgt : Nat} {prog rest : List JvmInstr}
    {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.ifnonnull tgt :: rest) ⟨pc, .null :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, stkRest, locs, jh, hp⟩ := by
  rw [runJvmResFast]
  rfl

theorem runJvmResFast_ifne_branch {f pc tgt : Nat} {prog rest : List JvmInstr}
    {v : UInt32} {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} (hne : v ≠ 0) :
    runJvmResFast (f + 1) prog pc (.ifne tgt :: rest) ⟨pc, .i32 v :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog tgt (prog.drop tgt) ⟨tgt, stkRest, locs, jh, hp⟩ := by
  rw [runJvmResFast]
  change (if !(v == 0) then
      runJvmResFast f prog tgt (prog.drop tgt) ⟨tgt, stkRest, locs, jh, hp⟩
    else
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, stkRest, locs, jh, hp⟩) = _
  have hbeq : (v == 0) = false := beq_false_of_ne hne
  simp [hbeq]

theorem runJvmResFast_ifne_fallthrough {f pc tgt : Nat} {prog rest : List JvmInstr}
    {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.ifne tgt :: rest) ⟨pc, .i32 0 :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, stkRest, locs, jh, hp⟩ := by
  rw [runJvmResFast]
  rfl

theorem runJvmResFast_ifne_bool_branch {f pc tgt : Nat} {prog rest : List JvmInstr}
    {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.ifne tgt :: rest) ⟨pc, .bool true :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog tgt (prog.drop tgt) ⟨tgt, stkRest, locs, jh, hp⟩ := by
  rw [runJvmResFast]
  rfl

theorem runJvmResFast_ifne_bool_fallthrough {f pc tgt : Nat} {prog rest : List JvmInstr}
    {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.ifne tgt :: rest) ⟨pc, .bool false :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, stkRest, locs, jh, hp⟩ := by
  rw [runJvmResFast]
  rfl

theorem runJvmResFast_if_icmpeq_branch {f pc tgt : Nat} {prog rest : List JvmInstr}
    {a b : UInt32} {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} (heq : a = b) :
    runJvmResFast (f + 1) prog pc (.if_icmpeq tgt :: rest) ⟨pc, .i32 b :: .i32 a :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog tgt (prog.drop tgt) ⟨tgt, stkRest, locs, jh, hp⟩ := by
  subst heq
  conv => lhs; dsimp only [runJvmResFast]; rw [Jvm.runJvmResFast.eq_def]
  simp [runJvmResFast, Jvm.JvmVal.asI32]

theorem runJvmResFast_if_icmpeq_fallthrough {f pc tgt : Nat} {prog rest : List JvmInstr}
    {a b : UInt32} {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} (hne : (a == b) = false) :
    runJvmResFast (f + 1) prog pc (.if_icmpeq tgt :: rest) ⟨pc, .i32 b :: .i32 a :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, stkRest, locs, jh, hp⟩ := by
  conv => lhs; dsimp only [runJvmResFast]; rw [Jvm.runJvmResFast.eq_def]
  simp [runJvmResFast, Jvm.JvmVal.asI32, hne]

theorem runJvmResFast_if_icmpne_branch {f pc tgt : Nat} {prog rest : List JvmInstr}
    {a b : UInt32} {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} (hne : (a == b) = false) :
    runJvmResFast (f + 1) prog pc (.if_icmpne tgt :: rest) ⟨pc, .i32 b :: .i32 a :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog tgt (prog.drop tgt) ⟨tgt, stkRest, locs, jh, hp⟩ := by
  conv => lhs; dsimp only [runJvmResFast]; rw [Jvm.runJvmResFast.eq_def]
  simp [runJvmResFast, Jvm.JvmVal.asI32, hne]

theorem runJvmResFast_if_icmpne_fallthrough {f pc tgt : Nat} {prog rest : List JvmInstr}
    {a b : UInt32} {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} (heq : a = b) :
    runJvmResFast (f + 1) prog pc (.if_icmpne tgt :: rest) ⟨pc, .i32 b :: .i32 a :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, stkRest, locs, jh, hp⟩ := by
  subst heq
  conv => lhs; dsimp only [runJvmResFast]; rw [Jvm.runJvmResFast.eq_def]
  simp [runJvmResFast, Jvm.JvmVal.asI32]

theorem runJvmResFast_goto {f pc tgt : Nat} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.goto tgt :: rest) ⟨pc, stk, locs, jh, hp⟩ =
      runJvmResFast f prog tgt (prog.drop tgt) ⟨tgt, stk, locs, jh, hp⟩ := by
  conv => lhs; dsimp only [runJvmResFast]; rw [Jvm.runJvmResFast.eq_def]
  simp [runJvmResFast]

theorem runJvmResFast_arraylength_strArr {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {rest : List JvmInstr} {pc0 : Nat} {xs : Array String} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.arraylength :: rest)
        ⟨pc0, .strArr xs :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest
        ⟨pc + 1, .i32 (UInt32.ofNat xs.size) :: stkRest, locs, jh, hp⟩ := by
  have hstep : Jvm.stepInstr algHooks .arraylength ⟨pc, .strArr xs :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 (UInt32.ofNat xs.size) :: stkRest, locs, jh, hp⟩) := rfl
  simp only [runJvmResFast]
  rw [Jvm.runJvmResFast_step_nonbranch algHooks (hbr := rfl) (hno := by simp)]
  simp only [hstep, ↓reduceIte]

theorem runJvmResFast_arraylength_byteArray {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {rest : List JvmInstr} {pc0 addr : Nat} {elems : Array UInt8} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
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

theorem runJvmResFast_getstatic_step {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {cls fld desc : String} {rest : List JvmInstr} {pc0 : Nat} {v : JvmVal}
    {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hstat : jh.statics = [])
    (hres : algResolveStatic ⟨pc, stkRest, locs, jh, hp⟩ cls fld desc = some v) :
    runJvmResFast (f + 1) prog pc (.getstatic cls fld desc :: rest)
        ⟨pc0, stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest
        ⟨pc + 1, v :: stkRest, locs, jh, hp⟩ := by
  have hgs : jh.getStatic? cls fld = none := by simp [Jvm.JvmHeap.getStatic?, hstat]
  have hstep : Jvm.stepInstr algHooks (.getstatic cls fld desc) ⟨pc, stkRest, locs, jh, hp⟩ =
      Sum.inl (some ⟨pc + 1, v :: stkRest, locs, jh, hp⟩) := by
    simp only [Jvm.stepInstr, hgs, hres]
  simp only [runJvmResFast]
  rw [Jvm.runJvmResFast_step_nonbranch algHooks (hbr := rfl) (hno := by simp)]
  simp only [hstep, ↓reduceIte]

theorem runJvmResFast_checkcast_instance {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {ty cls : String} {rest : List JvmInstr} {pc0 addr : Nat}
    {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hget : (jh.get? addr).bind (fun o => match o with | .instance c _ => some c | _ => none) = some cls)
    (hsub : isSubtypeOf cls ty = true) :
    runJvmResFast (f + 1) prog pc (.checkcast ty :: rest)
        ⟨pc0, .heapRef addr :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest
        ⟨pc + 1, .heapRef addr :: stkRest, locs, jh, hp⟩ := by
  cases hga : jh.get? addr with
  | none => simp [hga] at hget
  | some obj =>
    cases obj with
    | «instance» objCls flds =>
      simp only [hga, Option.bind_some, Option.some.injEq] at hget
      subst hget
      apply runJvmResFast_checkcast_step
      have hmatch : jh.checkInstanceOf ty addr = (ty == objCls || ty == "java/lang/Object") := by
        simp [Jvm.JvmHeap.checkInstanceOf, hga, Jvm.HeapObj.matchesType]
      have hchk : Jvm.stepInstr algHooks (.checkcast ty)
          ⟨pc, .heapRef addr :: stkRest, locs, jh, hp⟩ =
          Sum.inl (some ⟨pc + 1, .heapRef addr :: stkRest, locs, jh, hp⟩) := by
        simp only [Jvm.stepInstr, Jvm.JvmHeap.checkCast, hmatch]
        by_cases hcls : (ty == objCls || ty == "java/lang/Object") = true
        · simp [hcls]
        · simp [hcls, hga]; exact hsub
      exact hchk
    | _ => simp [hga] at hget

theorem runJvmResFast_aaload_strArr {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {rest : List JvmInstr} {pc0 : Nat} {idx : UInt32} {xs : Array String} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hslt : idx.toBitVec.slt 0#32 = false) (hlt : idx.toNat < xs.size) :
    runJvmResFast (f + 1) prog pc (.aaload :: rest)
        ⟨pc0, .i32 idx :: .strArr xs :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .str (xs[idx.toNat]) :: stkRest, locs, jh, hp⟩ := by
  have hstep : Jvm.stepInstr algHooks .aaload ⟨pc, .i32 idx :: .strArr xs :: stkRest, locs, jh, hp⟩ =
      Sum.inl (some ⟨pc + 1, .str (xs[idx.toNat]) :: stkRest, locs, jh, hp⟩) := by
    have hsub : Jvm.stepInstr algHooks .aaload ⟨pc, .i32 idx :: .strArr xs :: stkRest, locs, jh, hp⟩ =
        (if idx.toBitVec.slt 0#32 = true then Sum.inr none
         else if h : idx.toNat < xs.size then
           Sum.inl (some ⟨pc + 1, .str (xs[idx.toNat]) :: stkRest, locs, jh, hp⟩)
         else Sum.inr none) := rfl
    rw [hsub, hslt]
    simp only [Bool.false_eq_true, ↓reduceIte, hlt, ↓reduceDIte]
  simp only [runJvmResFast]
  rw [Jvm.runJvmResFast_step_nonbranch algHooks (hbr := rfl) (hno := by simp)]
  simp only [hstep, ↓reduceIte]

theorem runJvmResFast_baload_byteArray {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {rest : List JvmInstr} {pc0 addr : Nat} {idx : UInt32} {elems : Array UInt8}
    {stkRest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hget : jh.get? addr = some (.byteArray elems))
    (hslt : idx.toBitVec.slt 0#32 = false) (hlt : idx.toNat < elems.size) :
    runJvmResFast (f + 1) prog pc (.baload :: rest)
        ⟨pc0, .i32 idx :: .heapRef addr :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest
        ⟨pc + 1, .i32 (UInt32.ofBitVec (elems[idx.toNat].toBitVec.signExtend 32)) :: stkRest,
          locs, jh, hp⟩ := by
  have hstep := Jvm.stepInstr_baload algHooks (pc := pc) hget hslt hlt (stkRest := stkRest)
    (locs := locs) (hp := hp)
  simp only [runJvmResFast]
  rw [Jvm.runJvmResFast_step_nonbranch algHooks (hbr := rfl) (hno := by simp)]
  simp only [hstep, ↓reduceIte]

end Algorithm.JvmVerification
