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
import JvmSemantics
import proofs.JvmEquiv.Infra
import proofs.JvmEquiv.FlatInfra
import proofs.JvmEquiv.HeapInfra
import proofs.JvmEquiv.SharedStep
import proofs.JvmEquiv.StepExt

namespace Algorithm.JvmVerification

open Algorithm.JvmBytecode

/-! ### Shared local stepping & arithmetic helpers -/

private theorem runJvm_eq_of_runJvmRes {fuel : Nat} {prog : List JvmInstr}
    {st st' : JvmState} {v : JvmVal}
    (h : runJvmRes fuel prog st = some (v, st')) :
    runJvm fuel prog st = some v := by
  rw [runJvm_eq_runJvmRes, h]
  rfl

private theorem list_drop_step {n : Nat} {l : List JvmInstr} {a : JvmInstr} {as : List JvmInstr}
    (h : l.drop n = a :: as) :
    l.drop (n + 1) = as := by
  induction n generalizing l with
  | zero => simp only [List.drop_zero] at h; simp [h]
  | succ n ih =>
    cases l with
    | nil => simp at h
    | cons _ xs => exact ih h

open Lean Elab Tactic in
local elab "step_drop " n:num : tactic => do
  for _ in [:n.getNat] do
    evalTactic (← `(tactic|
      (conv => lhs; arg 4; rw [list_drop_step rfl]; try simp only [Nat.reduceAdd])))

local macro "norm_fuel" : tactic =>
  `(tactic| (
    (conv => lhs; try zeta; arg 1; simp only [Nat.succ_eq_add_one, nat_add_eq_add, Nat.reduceSub, Nat.reduceAdd]);
    (try (conv => lhs; arg 3; simp only [Nat.reduceAdd]))))

private theorem u32_sub1_slt_zero {id : UInt32} (hne : id ≠ 0) (hid31 : id.toNat < 2 ^ 31) :
    (id - 1).toBitVec.slt 0#32 = false := by
  apply u32_slt_zero_of_lt_2_31
  have h1 : 1 ≤ id.toNat := Nat.pos_of_ne_zero (fun h => hne (UInt32.toNat_inj.mp h))
  rw [UInt32.toNat_sub_of_le id 1 (by change (1 : Nat) ≤ id.toNat; exact h1)]
  omega

private theorem lcmp_zero_eq_zero (a : UInt64) :
    ((if a == 0 then (0 : UInt32) else if a.toBitVec.slt 0#64 then 4294967295 else 1) == 0) = (a == 0) := by
  cases a == 0
  · simp; split <;> decide
  · simp

private theorem runJvmResFast_lcmp_zero_ifeq_branch {f pc tgt : Nat} {prog rest : List JvmInstr}
    {a : UInt64} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} (ha : (a == 0) = true) :
    runJvmResFast (f + 1) prog pc (.ifeq tgt :: rest)
        ⟨pc, .i32 (if a == 0 then 0 else if a.toBitVec.slt 0#64 then 4294967295 else 1) :: stk,
          locs, jh, hp⟩ =
      runJvmResFast f prog tgt (prog.drop tgt) ⟨tgt, stk, locs, jh, hp⟩ :=
  runJvmResFast_ifeq_branch (by simp [ha])

private theorem runJvmResFast_lcmp_zero_ifeq_fallthrough {f pc tgt : Nat} {prog rest : List JvmInstr}
    {a : UInt64} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} (ha : (a == 0) = false) :
    runJvmResFast (f + 1) prog pc (.ifeq tgt :: rest)
        ⟨pc, .i32 (if a == 0 then 0 else if a.toBitVec.slt 0#64 then 4294967295 else 1) :: stk,
          locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, stk, locs, jh, hp⟩ :=
  runJvmResFast_ifeq_fallthrough (by rw [lcmp_zero_eq_zero]; exact ha)

private theorem runJvmResFast_step_nonbranch_nonret {f pc : Nat} {prog : List JvmInstr}
    {instr : JvmInstr} {rest : List JvmInstr}
    {pc0 : Nat} {stk stk' : List JvmVal} {locs locs' : Nat → JvmVal}
    {jh jh' : Jvm.JvmHeap AlgExt} {hp hp' : AlgHeap}
    (hbr : Jvm.isBranchInstr instr = false)
    (hi2l : instr ≠ .i2l)
    (hstep : Jvm.stepInstr algHooks instr ⟨pc, stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, stk', locs', jh', hp'⟩)) :
    runJvmResFast (f + 1) prog pc (instr :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, stk', locs', jh', hp'⟩ := by
  simp only [runJvmResFast]
  rw [Jvm.runJvmResFast_step_nonbranch algHooks (hbr := hbr) (hno := fun h => hi2l h.1)]
  simp only [hstep, ↓reduceIte]

local macro "step_op" thm:term : tactic => `(tactic| (
  split_res_fuel 1
  rw [runJvmResFast_step_nonbranch_nonret rfl (by intro h; cases h) $thm]
  norm_res_fuel))

private theorem step_booleanValue
    {pc : Nat} {b : Bool} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    Jvm.stepInstr algHooks (.invokevirtual "java/lang/Boolean" "booleanValue" "()Z")
      ⟨pc, .boxedBool b :: rest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 (if b then 1 else 0) :: rest, locs, jh, hp⟩) := rfl

private theorem step_mcLevel
    {pc : Nat} {m : Algorithm.MacroCell} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    Jvm.stepInstr algHooks (.invokevirtual "com/alexvanyo/composelife/model/MacroCell" "level-pVg5ArA" "()I")
      ⟨pc, .ext (.mc m) :: rest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 m.level :: rest, locs, jh, hp⟩) := rfl

private theorem step_l4_getNw
    {pc : Nat} {h : UInt32} {nw ne sw se : UInt64} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    Jvm.stepInstr algHooks (.invokevirtual "com/alexvanyo/composelife/model/MacroCell$Level4Node"
        "getNw-s-VKNKU" "()J")
      ⟨pc, .ext (.mc (.level4Node h nw ne sw se)) :: rest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i64 nw :: rest, locs, jh, hp⟩) := rfl

private theorem step_l4_getNe
    {pc : Nat} {h : UInt32} {nw ne sw se : UInt64} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    Jvm.stepInstr algHooks (.invokevirtual "com/alexvanyo/composelife/model/MacroCell$Level4Node"
        "getNe-s-VKNKU" "()J")
      ⟨pc, .ext (.mc (.level4Node h nw ne sw se)) :: rest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i64 ne :: rest, locs, jh, hp⟩) := rfl

private theorem step_l4_getSw
    {pc : Nat} {h : UInt32} {nw ne sw se : UInt64} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    Jvm.stepInstr algHooks (.invokevirtual "com/alexvanyo/composelife/model/MacroCell$Level4Node"
        "getSw-s-VKNKU" "()J")
      ⟨pc, .ext (.mc (.level4Node h nw ne sw se)) :: rest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i64 sw :: rest, locs, jh, hp⟩) := rfl

private theorem step_l4_getSe
    {pc : Nat} {h : UInt32} {nw ne sw se : UInt64} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    Jvm.stepInstr algHooks (.invokevirtual "com/alexvanyo/composelife/model/MacroCell$Level4Node"
        "getSe-s-VKNKU" "()J")
      ⟨pc, .ext (.mc (.level4Node h nw ne sw se)) :: rest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i64 se :: rest, locs, jh, hp⟩) := rfl

private theorem step_leafChildClosed0
    {pc : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    Jvm.stepInstr algHooks
      (.invokestatic "MacroCellLeanKt" "f_Algorithm_macrocellLeafChild___closed__0" "()Lkotlin/ULong;")
      ⟨pc, rest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .boxedULong 0 :: rest, locs, jh, hp⟩) := rfl

private theorem step_sl_lam0
    {pc : Nat} {p : JvmVal} {v : UInt64} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    Jvm.stepInstr algHooks
      (.invokestatic "MacroCellLeanKt" "f_Algorithm_macrocellSingleLeaf___lam__0-4PLdz1A"
        "(JLjava/lang/Object;)Z")
      ⟨pc, p :: .i64 v :: rest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 (if v == 0 then 1 else 0) :: rest, locs, jh, hp⟩) := rfl

private theorem step_sl_lam1
    {pc : Nat} {p : JvmVal} {v : UInt64} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    Jvm.stepInstr algHooks
      (.invokestatic "MacroCellLeanKt" "f_Algorithm_macrocellSingleLeaf___lam__1-4PLdz1A"
        "(JLjava/lang/Object;)Z")
      ⟨pc, p :: .i64 v :: rest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 (if v == 0 then 1 else 0) :: rest, locs, jh, hp⟩) := rfl

private theorem step_sl_lam2
    {pc : Nat} {p : JvmVal} {v : UInt64} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    Jvm.stepInstr algHooks
      (.invokestatic "MacroCellLeanKt" "f_Algorithm_macrocellSingleLeaf___lam__2-4PLdz1A"
        "(JLjava/lang/Object;)Z")
      ⟨pc, p :: .i64 v :: rest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 (if v == 0 then 1 else 0) :: rest, locs, jh, hp⟩) := rfl

local macro "norm_drop" : tactic => `(tactic| (
  conv => lhs; arg 4; dsimp only [List.drop]))

private theorem arr3_get1 (a b c : JvmVal) (h : (1 : UInt32).toNat < #[a, b, c].size) :
    (#[a, b, c])[(1 : UInt32).toNat]'h = b := rfl

private theorem arr3_get2 (a b c : JvmVal) (h : (2 : UInt32).toNat < #[a, b, c].size) :
    (#[a, b, c])[(2 : UInt32).toNat]'h = c := rfl

private theorem get?_alloc_self_replicate1 (jh : Jvm.JvmHeap AlgExt) :
    (jh.alloc (.objArray "java/lang/Object" (Array.replicate (1 : UInt32).toNat .null))).2.get?
        jh.objects.size =
      some (.objArray "java/lang/Object" (Array.replicate (1 : UInt32).toNat .null)) := by
  simp [Jvm.JvmHeap.alloc, Jvm.JvmHeap.get?]

local macro "step_alloc1_lam" lam:term : tactic => `(tactic| (
  heap_step_nonbranch_chunks; norm_res_fuel
  split_res_fuel 1
  rw [runJvmResFast_anewarray_obj (by decide)]; norm_res_fuel
  heap_step_nonbranch_chunks; norm_res_fuel
  split_res_fuel 1
  rw [runJvmResFast_aastore (get?_alloc_self_replicate1 _) (by decide) (by decide)]; norm_res_fuel
  heap_step_nonbranch_chunks; norm_res_fuel
  step_op $lam
  heap_step_nonbranch_chunks; norm_res_fuel))

/-! ### macroCellAt -/

theorem macroCellAt_equiv (nodes : Array Algorithm.MacroCell) (i : UInt32)
    (nodesAddr : Nat) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hget : jh.get? nodesAddr = some (.objArray "java/lang/Object"
      (nodes.map (fun m => JvmVal.ext (AlgExt.mc m)))))
    (hi : i.toNat < nodes.size)
    (hi31 : i.toNat < 2 ^ 31) :
    runJvm 70 f_Algorithm_macroCellAt_prog
      ⟨0, [], setLocal (setLocal (fun _ => .null) 0 (.heapRef nodesAddr)) 1 (.i32 i), jh, hp⟩ =
      some (.ext (.mc (Algorithm.macroCellAt nodes i))) := by
  suffices hfast : ∃ st', runJvmResFast 70 f_Algorithm_macroCellAt_prog 0
      f_Algorithm_macroCellAt_prog
      ⟨0, [], setLocal (setLocal (fun _ => .null) 0 (.heapRef nodesAddr)) 1 (.i32 i), jh, hp⟩ =
      some (.ext (.mc (Algorithm.macroCellAt nodes i)), st') from
    let ⟨st', hs⟩ := hfast
    runJvm_eq_of_runJvmRes (runJvmRes_of_runJvmResFast0 70 _ _ _ rfl hs)
  have hslt : i.toBitVec.slt 0#32 = false := u32_slt_zero_of_lt_2_31 hi31
  have hltElems : i.toNat < (nodes.map (fun m => JvmVal.ext (AlgExt.mc m))).size := by
    simpa using hi
  have hElem : (nodes.map (fun m => JvmVal.ext (AlgExt.mc m)))[i.toNat]'hltElems =
      .ext (.mc nodes[i.toNat]) := by simp
  cases hm : nodes[i.toNat] with
  | level4Node h nw ne sw se =>
    apply Exists.intro
    dsimp only [f_Algorithm_macroCellAt_prog]
    heap_step_nonbranch_chunks; norm_res_fuel
    split_res_fuel 1
    rw [runJvmResFast_aaload hget hslt hltElems]; norm_res_fuel; rw [hElem, hm]
    heap_step_nonbranch_chunks; norm_res_fuel
    split_res_fuel 1
    rw [runJvmResFast_checkcast_step (v' := .ext (.mc (.level4Node h nw ne sw se))) rfl]
    norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    split_res_fuel 1
    rw [runJvmResFast_instanceof_step (res := 1) rfl]
    norm_res_fuel
    rw [runJvmResFast_ifeq_fallthrough (v := 1) (by decide)]; norm_res_fuel
    heap_step_nonbranch_chunks
    rw [Algorithm.macroCellAt, getElem!_pos nodes i.toNat hi, hm]
    rfl
  | cellNode h nw ne sw se =>
    apply Exists.intro
    dsimp only [f_Algorithm_macroCellAt_prog]
    heap_step_nonbranch_chunks; norm_res_fuel
    split_res_fuel 1
    rw [runJvmResFast_aaload hget hslt hltElems]; norm_res_fuel; rw [hElem, hm]
    heap_step_nonbranch_chunks; norm_res_fuel
    split_res_fuel 1
    rw [runJvmResFast_checkcast_step (v' := .ext (.mc (.cellNode h nw ne sw se))) rfl]
    norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    split_res_fuel 1
    rw [runJvmResFast_instanceof_step (res := 0) rfl]
    norm_res_fuel
    rw [runJvmResFast_ifeq_branch (v := 0) rfl]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    split_res_fuel 1
    rw [runJvmResFast_instanceof_step (res := 1) rfl]
    norm_res_fuel
    rw [runJvmResFast_ifeq_fallthrough (v := 1) (by decide)]; norm_res_fuel
    heap_step_nonbranch_chunks
    rw [Algorithm.macroCellAt, getElem!_pos nodes i.toNat hi, hm]
    rfl

/-! ### macrocellLeafChild & macrocellCellChild -/

local macro "step_isLeaf_cmp " hisLeaf:ident hisLeafData:ident : tactic =>
  `(tactic| (
  heap_step_nonbranch_chunks; norm_res_fuel
  split_res_fuel 1
  rw [runJvmResFast_checkcast_objArray $hisLeaf (Or.inl rfl)]; norm_res_fuel
  heap_step_nonbranch_chunks; norm_res_fuel
  split_res_fuel 1
  rw [runJvmResFast_aaload $hisLeaf (by decide) (by simp)]; norm_res_fuel
  rw [arr3_get1]
  heap_step_nonbranch_chunks; norm_res_fuel
  split_res_fuel 1
  rw [runJvmResFast_checkcast_objArray $hisLeafData (Or.inl rfl)]; norm_res_fuel
  heap_step_nonbranch_chunks; norm_res_fuel
  split_res_fuel 1
  rw [runJvmResFast_checkcast_objArray $hisLeaf (Or.inl rfl)]; norm_res_fuel
  heap_step_nonbranch_chunks; norm_res_fuel
  split_res_fuel 1
  rw [runJvmResFast_aaload $hisLeaf (by decide) (by simp)]; norm_res_fuel
  rw [arr3_get2]
  heap_step_nonbranch_chunks; norm_res_fuel
  split_res_fuel 1
  rw [runJvmResFast_instanceof_boxedInt_int]; norm_res_fuel
  rw [runJvmResFast_ifeq_fallthrough (v := 1) (by decide)]; norm_res_fuel
  heap_step_nonbranch_chunks; norm_res_fuel
  split_res_fuel 1
  rw [runJvmResFast_checkcast_boxedInt (Or.inr (Or.inl rfl))]; norm_res_fuel
  heap_step_nonbranch_chunks; norm_res_fuel))

local macro "step_isLeaf_bool_head" hisLeafData:ident hslt_sub:ident hlt_isLeafMap:ident : tactic =>
  `(tactic| (
  heap_step_nonbranch_chunks; norm_res_fuel
  split_res_fuel 1
  rw [runJvmResFast_aaload $hisLeafData $hslt_sub $hlt_isLeafMap]; norm_res_fuel))

local macro "step_isLeaf_bool_tail" : tactic =>
  `(tactic| (
  heap_step_nonbranch_chunks; norm_res_fuel
  split_res_fuel 1
  rw [runJvmResFast_checkcast_step rfl]; norm_res_fuel
  step_op step_booleanValue
  simp only [eq_self_iff_true, Bool.false_eq_true, ↓reduceIte]
  heap_step_nonbranch_chunks; norm_res_fuel))

theorem macrocellLeafChild_equiv (leaves : Algorithm.GrowBuf UInt64) (isLeaf : Algorithm.GrowBuf Bool)
    (id : UInt32) (leavesAddr leavesDataAddr isLeafAddr isLeafDataAddr : Nat)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hleaves : jh.get? leavesAddr = some (.objArray "java/lang/Object"
      #[.boxedInt 0, .heapRef leavesDataAddr, .boxedInt leaves.size]))
    (hleavesData : jh.get? leavesDataAddr = some (.objArray "java/lang/Object"
      (leaves.data.map JvmVal.boxedULong)))
    (hisLeaf : jh.get? isLeafAddr = some (.objArray "java/lang/Object"
      #[.boxedInt 0, .heapRef isLeafDataAddr, .boxedInt isLeaf.size]))
    (hisLeafData : jh.get? isLeafDataAddr = some (.objArray "java/lang/Object"
      (isLeaf.data.map (@Jvm.JvmVal.boxedBool AlgExt))))
    (his_le : isLeaf.size.toNat ≤ isLeaf.data.size)
    (hleaves_le : isLeaf.size.toNat ≤ leaves.data.size)
    (hid31 : id.toNat < 2 ^ 31) :
    runJvm 120 f_Algorithm_macrocellLeafChild_prog
      ⟨0, [], setLocal (setLocal (setLocal (fun _ => .null)
        0 (.heapRef leavesAddr)) 1 (.heapRef isLeafAddr)) 2 (.i32 id), jh, hp⟩ =
      some (match Algorithm.macrocellLeafChild leaves isLeaf id with
        | some v => .boxedULong v
        | none => .null) := by
  suffices hfast : ∃ st', runJvmResFast 120 f_Algorithm_macrocellLeafChild_prog 0
      f_Algorithm_macrocellLeafChild_prog
      ⟨0, [], setLocal (setLocal (setLocal (fun _ => .null)
        0 (.heapRef leavesAddr)) 1 (.heapRef isLeafAddr)) 2 (.i32 id), jh, hp⟩ =
      some (match Algorithm.macrocellLeafChild leaves isLeaf id with
        | some v => .boxedULong v
        | none => .null, st') from
    let ⟨st', hs⟩ := hfast
    runJvm_eq_of_runJvmRes (runJvmRes_of_runJvmResFast0 120 _ _ _ rfl hs)
  by_cases hid0 : id = 0
  · subst hid0
    apply Exists.intro
    dsimp only [f_Algorithm_macrocellLeafChild_prog]
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_ifeq_branch (v := 0) rfl]; norm_drop; norm_res_fuel
    step_op step_leafChildClosed0
    heap_step_nonbranch_chunks
    simp [Algorithm.macrocellLeafChild]
    rfl
  · have hid_beq : (id == 0) = false := beq_false_of_ne hid0
    by_cases hgt : id > isLeaf.size
    · apply Exists.intro
      dsimp only [f_Algorithm_macrocellLeafChild_prog]
      heap_step_nonbranch_chunks; norm_res_fuel
      rw [runJvmResFast_ifeq_fallthrough (v := id) (by simp [hid_beq])]; norm_res_fuel
      step_isLeaf_cmp hisLeaf hisLeafData
      rw [runJvmResFast_iflt_branch (v := _) (by rw [compareUnsigned_slt_zero]; simp [hgt])]
      norm_drop; norm_res_fuel
      heap_step_nonbranch_chunks
      simp [Algorithm.macrocellLeafChild, hid_beq, hgt]
      rfl
    · have hle : id ≤ isLeaf.size := Nat.le_of_not_lt hgt
      have hle_nat : id.toNat ≤ isLeaf.size.toNat := UInt32.le_iff_toNat_le.mp hle
      have hslt_sub : (id - 1).toBitVec.slt 0#32 = false := u32_sub1_slt_zero hid0 hid31
      have h1 : 1 ≤ id.toNat := Nat.pos_of_ne_zero (fun h => hid0 (UInt32.toNat_inj.mp h))
      have hsub_nat : (id - 1).toNat = id.toNat - 1 := by
        simp [UInt32.toNat_sub_of_le id 1 (by change 1 ≤ id.toNat; exact h1)]
      have hsub_lt_sz : (id - 1).toNat < isLeaf.size.toNat := by omega
      have hsub_lt_isLeaf : (id - 1).toNat < isLeaf.data.size := Nat.lt_of_lt_of_le hsub_lt_sz his_le
      have hsub_lt_leaves : (id - 1).toNat < leaves.data.size := Nat.lt_of_lt_of_le hsub_lt_sz hleaves_le
      have hlt_isLeafMap : (id - 1).toNat < (isLeaf.data.map (@Jvm.JvmVal.boxedBool AlgExt)).size := by
        simpa using hsub_lt_isLeaf
      have hlt_leavesMap : (id - 1).toNat <
          (leaves.data.map (@Jvm.JvmVal.boxedULong AlgExt)).size := by
        simpa using hsub_lt_leaves
      have hElemB : (isLeaf.data.map (@Jvm.JvmVal.boxedBool AlgExt))[(id - 1).toNat]'hlt_isLeafMap =
          .boxedBool isLeaf.data[(id - 1).toNat] := by simp
      have hElemL : (leaves.data.map (@Jvm.JvmVal.boxedULong AlgExt))[(id - 1).toNat]'hlt_leavesMap =
          .boxedULong leaves.data[(id - 1).toNat] := by simp
      cases hb : isLeaf.data[(id - 1).toNat]
      · apply Exists.intro
        dsimp only [f_Algorithm_macrocellLeafChild_prog]
        heap_step_nonbranch_chunks; norm_res_fuel
        rw [runJvmResFast_ifeq_fallthrough (v := id) (by simp [hid_beq])]; norm_res_fuel
        step_isLeaf_cmp hisLeaf hisLeafData
        rw [runJvmResFast_iflt_fallthrough (v := _) (by rw [compareUnsigned_slt_zero]; simp [hgt])]
        norm_res_fuel
        step_isLeaf_bool_head hisLeafData hslt_sub hlt_isLeafMap
        rw [hElemB, hb]
        step_isLeaf_bool_tail
        rw [runJvmResFast_ifne_fallthrough]; norm_res_fuel
        heap_step_nonbranch_chunks
        simp [Algorithm.macrocellLeafChild, hid_beq, hgt,
          getElem!_pos isLeaf.data (id - 1).toNat hsub_lt_isLeaf, hb]
        rfl
      · apply Exists.intro
        dsimp only [f_Algorithm_macrocellLeafChild_prog]
        heap_step_nonbranch_chunks; norm_res_fuel
        rw [runJvmResFast_ifeq_fallthrough (v := id) (by simp [hid_beq])]; norm_res_fuel
        step_isLeaf_cmp hisLeaf hisLeafData
        rw [runJvmResFast_iflt_fallthrough (v := _) (by rw [compareUnsigned_slt_zero]; simp [hgt])]
        norm_res_fuel
        step_isLeaf_bool_head hisLeafData hslt_sub hlt_isLeafMap
        rw [hElemB, hb]
        step_isLeaf_bool_tail
        rw [runJvmResFast_ifne_branch (v := 1) (by decide)]; norm_drop; norm_res_fuel
        heap_step_nonbranch_chunks; norm_res_fuel
        split_res_fuel 1
        rw [runJvmResFast_checkcast_objArray hleaves (Or.inl rfl)]; norm_res_fuel
        heap_step_nonbranch_chunks; norm_res_fuel
        split_res_fuel 1
        rw [runJvmResFast_aaload hleaves (by decide) (by simp)]; norm_res_fuel
        rw [arr3_get1]
        heap_step_nonbranch_chunks; norm_res_fuel
        split_res_fuel 1
        rw [runJvmResFast_checkcast_objArray hleavesData (Or.inl rfl)]; norm_res_fuel
        heap_step_nonbranch_chunks; norm_res_fuel
        split_res_fuel 1
        rw [runJvmResFast_aaload hleavesData hslt_sub hlt_leavesMap]; norm_res_fuel
        rw [hElemL]
        heap_step_nonbranch_chunks; norm_res_fuel
        split_res_fuel 1
        rw [runJvmResFast_checkcast_boxedULong (Or.inl rfl)]; norm_res_fuel
        heap_step_nonbranch_chunks
        simp [Algorithm.macrocellLeafChild, hid_beq, hgt,
          getElem!_pos isLeaf.data (id - 1).toNat hsub_lt_isLeaf,
          getElem!_pos leaves.data (id - 1).toNat hsub_lt_leaves, hb]
        rfl

private theorem foldlM_map_mc_list (xs : List Algorithm.MacroCell) (acc : Array Algorithm.MacroCell) :
    (xs.map (fun m => JvmVal.ext (AlgExt.mc m))).foldlM
      (fun a v => match v with | .ext (.mc m) => some (a.push m) | _ => none) acc =
      some (acc ++ xs.toArray) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.foldlM_cons]
    dsimp only [bind, Option.bind]
    rw [ih (acc.push x)]
    simp [Array.push]

private theorem foldlM_map_mc (arr : Array Algorithm.MacroCell) :
    (arr.map (fun m => JvmVal.ext (AlgExt.mc m))).foldlM
      (fun a v => match v with | .ext (.mc m) => some (a.push m) | _ => none) #[] =
      some arr := by
  rw [← Array.foldlM_toList, Array.toList_map, foldlM_map_mc_list]
  simp

private theorem step_invokestatic_macroCellAt
    {pc : Nat} {i : UInt32} {nodesDataAddr : Nat} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {nodes : Array Algorithm.MacroCell}
    (hget : jh.get? nodesDataAddr = some (.objArray "java/lang/Object"
      (nodes.map (fun m => JvmVal.ext (AlgExt.mc m))))) :
    Jvm.stepInstr algHooks
      (.invokestatic "MacroCellLeanKt" "f_Algorithm_macroCellAt-Qn1smSk"
        "([Ljava/lang/Object;I)Lcom/alexvanyo/composelife/model/MacroCell;")
      ⟨pc, .i32 i :: .heapRef nodesDataAddr :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .ext (.mc (Algorithm.macroCellAt nodes i)) :: stkRest, locs, jh, hp⟩) := by
  conv => lhs; whnf
  rw [hget]
  dsimp only [Jvm.JvmVal.asI32]
  erw [foldlM_map_mc nodes]

local macro "step_cc_tail" hnodes:ident hnodesData:ident : tactic => `(tactic| (
  split_res_fuel 1
  rw [runJvmResFast_ifne_fallthrough]; norm_res_fuel
  heap_step_nonbranch_chunks; norm_res_fuel
  split_res_fuel 1
  rw [runJvmResFast_checkcast_objArray $hnodes (Or.inl rfl)]; norm_res_fuel
  heap_step_nonbranch_chunks; norm_res_fuel
  split_res_fuel 1
  rw [runJvmResFast_aaload $hnodes (by decide) (by simp)]; norm_res_fuel
  rw [arr3_get1]
  heap_step_nonbranch_chunks; norm_res_fuel
  split_res_fuel 1
  rw [runJvmResFast_checkcast_objArray $hnodesData (Or.inl rfl)]; norm_res_fuel
  heap_step_nonbranch_chunks; norm_res_fuel
  step_op (step_invokestatic_macroCellAt $hnodesData)
  heap_step_nonbranch_chunks; norm_res_fuel
  step_op step_mcLevel
  heap_step_nonbranch_chunks; norm_res_fuel))

theorem macrocellCellChild_equiv (nodes : Algorithm.GrowBuf Algorithm.MacroCell)
    (isLeaf : Algorithm.GrowBuf Bool) (level : UInt32) (emptySub : Algorithm.MacroCell)
    (id : UInt32) (nodesAddr nodesDataAddr isLeafAddr isLeafDataAddr : Nat)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hnodes : jh.get? nodesAddr = some (.objArray "java/lang/Object"
      #[.boxedInt 0, .heapRef nodesDataAddr, .boxedInt nodes.size]))
    (hnodesData : jh.get? nodesDataAddr = some (.objArray "java/lang/Object"
      (nodes.data.map (fun m => JvmVal.ext (AlgExt.mc m)))))
    (hisLeaf : jh.get? isLeafAddr = some (.objArray "java/lang/Object"
      #[.boxedInt 0, .heapRef isLeafDataAddr, .boxedInt isLeaf.size]))
    (hisLeafData : jh.get? isLeafDataAddr = some (.objArray "java/lang/Object"
      (isLeaf.data.map (@Jvm.JvmVal.boxedBool AlgExt))))
    (his_le : isLeaf.size.toNat ≤ isLeaf.data.size)
    (hnodes_le : isLeaf.size.toNat ≤ nodes.data.size)
    (hid31 : id.toNat < 2 ^ 31) :
    runJvm 140 f_Algorithm_macrocellCellChild_prog
      ⟨0, [], setLocal (setLocal (setLocal (setLocal (setLocal (fun _ => .null)
        0 (.heapRef nodesAddr)) 1 (.heapRef isLeafAddr)) 2 (.i32 level))
        3 (.ext (.mc emptySub))) 4 (.i32 id), jh, hp⟩ =
      some (match Algorithm.macrocellCellChild nodes isLeaf level emptySub id with
        | some m => .ext (.mc m)
        | none => .null) := by
  suffices hfast : ∃ st', runJvmResFast 140 f_Algorithm_macrocellCellChild_prog 0
      f_Algorithm_macrocellCellChild_prog
      ⟨0, [], setLocal (setLocal (setLocal (setLocal (setLocal (fun _ => .null)
        0 (.heapRef nodesAddr)) 1 (.heapRef isLeafAddr)) 2 (.i32 level))
        3 (.ext (.mc emptySub))) 4 (.i32 id), jh, hp⟩ =
      some (match Algorithm.macrocellCellChild nodes isLeaf level emptySub id with
        | some m => .ext (.mc m)
        | none => .null, st') from
    let ⟨st', hs⟩ := hfast
    runJvm_eq_of_runJvmRes (runJvmRes_of_runJvmResFast0 140 _ _ _ rfl hs)
  by_cases hid0 : id = 0
  · subst hid0
    apply Exists.intro
    dsimp only [f_Algorithm_macrocellCellChild_prog]
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_ifeq_branch (v := 0) rfl]; norm_drop; norm_res_fuel
    heap_step_nonbranch_chunks
    simp [Algorithm.macrocellCellChild]
    rfl
  · have hid_beq : (id == 0) = false := beq_false_of_ne hid0
    by_cases hgt : id > isLeaf.size
    · apply Exists.intro
      dsimp only [f_Algorithm_macrocellCellChild_prog]
      heap_step_nonbranch_chunks; norm_res_fuel
      rw [runJvmResFast_ifeq_fallthrough (v := id) (by simp [hid_beq])]; norm_res_fuel
      step_isLeaf_cmp hisLeaf hisLeafData
      rw [runJvmResFast_iflt_branch (v := _) (by rw [compareUnsigned_slt_zero]; simp [hgt])]
      norm_drop; norm_res_fuel
      heap_step_nonbranch_chunks
      simp [Algorithm.macrocellCellChild, hid_beq, hgt]
      rfl
    · have hle : id ≤ isLeaf.size := Nat.le_of_not_lt hgt
      have hle_nat : id.toNat ≤ isLeaf.size.toNat := UInt32.le_iff_toNat_le.mp hle
      have hslt_sub : (id - 1).toBitVec.slt 0#32 = false := u32_sub1_slt_zero hid0 hid31
      have h1 : 1 ≤ id.toNat := Nat.pos_of_ne_zero (fun h => hid0 (UInt32.toNat_inj.mp h))
      have hsub_nat : (id - 1).toNat = id.toNat - 1 := by
        simp [UInt32.toNat_sub_of_le id 1 (by change 1 ≤ id.toNat; exact h1)]
      have hsub_lt_sz : (id - 1).toNat < isLeaf.size.toNat := by omega
      have hsub_lt_isLeaf : (id - 1).toNat < isLeaf.data.size := Nat.lt_of_lt_of_le hsub_lt_sz his_le
      have hsub_lt_nodes : (id - 1).toNat < nodes.data.size := Nat.lt_of_lt_of_le hsub_lt_sz hnodes_le
      have hlt_isLeafMap : (id - 1).toNat < (isLeaf.data.map (@Jvm.JvmVal.boxedBool AlgExt)).size := by
        simpa using hsub_lt_isLeaf
      have hElemB : (isLeaf.data.map (@Jvm.JvmVal.boxedBool AlgExt))[(id - 1).toNat]'hlt_isLeafMap =
          .boxedBool isLeaf.data[(id - 1).toNat] := by simp
      cases hb : isLeaf.data[(id - 1).toNat]
      · let e := Algorithm.macroCellAt nodes.data (id - 1)
        by_cases hlvl : (e.level + 1 == level) = true
        · apply Exists.intro
          dsimp only [f_Algorithm_macrocellCellChild_prog]
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_ifeq_fallthrough (v := id) (by simp [hid_beq])]; norm_res_fuel
          step_isLeaf_cmp hisLeaf hisLeafData
          rw [runJvmResFast_iflt_fallthrough (v := _) (by rw [compareUnsigned_slt_zero]; simp [hgt])]
          norm_res_fuel
          step_isLeaf_bool_head hisLeafData hslt_sub hlt_isLeafMap
          rw [hElemB, hb]
          step_isLeaf_bool_tail
          step_cc_tail hnodes hnodesData
          rw [runJvmResFast_if_icmpeq_branch (beq_iff_eq.mp hlvl)]; norm_drop; norm_res_fuel
          heap_step_nonbranch_chunks
          simp [Algorithm.macrocellCellChild, hid_beq, hgt,
            getElem!_pos isLeaf.data (id - 1).toNat hsub_lt_isLeaf, hb, e, hlvl]
          rfl
        · apply Exists.intro
          dsimp only [f_Algorithm_macrocellCellChild_prog]
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_ifeq_fallthrough (v := id) (by simp [hid_beq])]; norm_res_fuel
          step_isLeaf_cmp hisLeaf hisLeafData
          rw [runJvmResFast_iflt_fallthrough (v := _) (by rw [compareUnsigned_slt_zero]; simp [hgt])]
          norm_res_fuel
          step_isLeaf_bool_head hisLeafData hslt_sub hlt_isLeafMap
          rw [hElemB, hb]
          step_isLeaf_bool_tail
          step_cc_tail hnodes hnodesData
          rw [runJvmResFast_if_icmpeq_fallthrough (by simp [e, hlvl])]; norm_res_fuel
          heap_step_nonbranch_chunks
          simp [Algorithm.macrocellCellChild, hid_beq, hgt,
            getElem!_pos isLeaf.data (id - 1).toNat hsub_lt_isLeaf, hb, e, hlvl]
          rfl
      · apply Exists.intro
        dsimp only [f_Algorithm_macrocellCellChild_prog]
        heap_step_nonbranch_chunks; norm_res_fuel
        rw [runJvmResFast_ifeq_fallthrough (v := id) (by simp [hid_beq])]; norm_res_fuel
        step_isLeaf_cmp hisLeaf hisLeafData
        rw [runJvmResFast_iflt_fallthrough (v := _) (by rw [compareUnsigned_slt_zero]; simp [hgt])]
        norm_res_fuel
        step_isLeaf_bool_head hisLeafData hslt_sub hlt_isLeafMap
        rw [hElemB, hb]
        step_isLeaf_bool_tail
        split_res_fuel 1
        rw [runJvmResFast_ifne_branch (v := 1) (by decide)]; norm_drop; norm_res_fuel
        heap_step_nonbranch_chunks
        simp [Algorithm.macrocellCellChild, hid_beq, hgt,
          getElem!_pos isLeaf.data (id - 1).toNat hsub_lt_isLeaf, hb]
        rfl

/-! ### macrocellSingleLeaf -/

local macro "sl_drop" : tactic => `(tactic| (
  conv => lhs; arg 4; dsimp only [f_Algorithm_macrocellSingleLeaf_prog, List.drop]))

private theorem runJvmResFast_ifne_ite_branch {f pc tgt : Nat} {prog rest : List JvmInstr}
    {c : Bool} {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} (hc : c = true) :
    runJvmResFast (f + 1) prog pc (.ifne tgt :: rest)
        ⟨pc, .i32 (if c then 1 else 0) :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog tgt (prog.drop tgt) ⟨tgt, stkRest, locs, jh, hp⟩ := by
  subst hc; exact runJvmResFast_ifne_branch (v := 1) (by decide)

private theorem runJvmResFast_ifne_ite_fallthrough {f pc tgt : Nat} {prog rest : List JvmInstr}
    {c : Bool} {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} (hc : c = false) :
    runJvmResFast (f + 1) prog pc (.ifne tgt :: rest)
        ⟨pc, .i32 (if c then 1 else 0) :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, stkRest, locs, jh, hp⟩ := by
  subst hc; exact runJvmResFast_ifne_fallthrough

private theorem step_sl_l4_prefix {h : UInt32} {nw ne sw se : UInt64}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast 260 f_Algorithm_macrocellSingleLeaf_prog 0
        f_Algorithm_macrocellSingleLeaf_prog
        ⟨0, [], setLocal (fun _ => .null) 0 (.ext (.mc (.level4Node h nw ne sw se))), jh, hp⟩ =
      runJvmResFast 219 f_Algorithm_macrocellSingleLeaf_prog 41
        (f_Algorithm_macrocellSingleLeaf_prog.drop 41)
        ⟨41, [.i32 (if nw == 0 then 0 else if nw.toBitVec.slt 0#64 then 4294967295 else 1)],
          setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
            (setLocal (setLocal (setLocal (setLocal (setLocal (fun _ => .null)
              0 (.ext (.mc (.level4Node h nw ne sw se))))
              1 (.ext (.mc (.level4Node h nw ne sw se))))
              2 (.i64 nw)) 4 (.i64 ne)) 6 (.i64 sw)) 8 (.i64 se))
              10 (.i32 0)) 11 (.i32 0)) 12 (.i32 0)) 13 (.i32 0)) 14 (.i32 0)) 15 (.i32 0))
              16 (.i32 0),
          jh, hp⟩ := by
  conv => lhs; arg 4; dsimp only [f_Algorithm_macrocellSingleLeaf_prog]
  heap_step_nonbranch_chunks; norm_fuel
  split_res_fuel 1
  rw [runJvmResFast_instanceof_step (res := 1) rfl]; norm_fuel
  rw [runJvmResFast_ifeq_fallthrough (v := 1) (by decide)]; norm_fuel
  heap_step_nonbranch_chunks; norm_fuel
  split_res_fuel 1
  rw [runJvmResFast_checkcast_step rfl]; norm_fuel
  step_op step_l4_getNw
  heap_step_nonbranch_chunks; norm_fuel
  split_res_fuel 1
  rw [runJvmResFast_checkcast_step rfl]; norm_fuel
  step_op step_l4_getNe
  heap_step_nonbranch_chunks; norm_fuel
  split_res_fuel 1
  rw [runJvmResFast_checkcast_step rfl]; norm_fuel
  step_op step_l4_getSw
  heap_step_nonbranch_chunks; norm_fuel
  split_res_fuel 1
  rw [runJvmResFast_checkcast_step rfl]; norm_fuel
  step_op step_l4_getSe
  heap_step_nonbranch_chunks; norm_fuel
  conv => rhs; arg 4; dsimp only [f_Algorithm_macrocellSingleLeaf_prog, List.drop]
  rfl

local macro "step_sl_l4" : tactic => `(tactic| (
  rw [step_sl_l4_prefix]
  sl_drop))

local macro "norm_lcmp_zero" : tactic => `(tactic| (
  (conv => lhs; jvm_whnf_run_args)
  (conv => lhs; arg 5; dsimp only [Jvm.JvmVal.asI64])
  (conv => lhs; arg 5; simp only [Nat.add_zero, Nat.succ_eq_add_one, Nat.reduceAdd])
  (try rw [show (0 : UInt64).toBitVec = 0#64 from rfl])))

local macro "step_sl_long_cast" : tactic => `(tactic| (
  heap_step_nonbranch_chunks; norm_res_fuel
  split_res_fuel 1
  rw [runJvmResFast_instanceof_step (res := 0) rfl]; norm_res_fuel
  rw [runJvmResFast_ifeq_branch (v := 0) rfl]; sl_drop; norm_res_fuel
  heap_step_nonbranch_chunks; norm_res_fuel
  norm_lcmp_zero))

theorem macrocellSingleLeaf_equiv (m : Algorithm.MacroCell) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    runJvm 260 f_Algorithm_macrocellSingleLeaf_prog
      ⟨0, [], setLocal (fun _ => .null) 0 (.ext (.mc m)), jh, hp⟩ =
      some (match Algorithm.macrocellSingleLeaf m with
        | some v => .boxedULong v
        | none => .null) := by
  suffices hfast : ∃ st', runJvmResFast 260 f_Algorithm_macrocellSingleLeaf_prog 0
      f_Algorithm_macrocellSingleLeaf_prog
      ⟨0, [], setLocal (fun _ => .null) 0 (.ext (.mc m)), jh, hp⟩ =
      some (match Algorithm.macrocellSingleLeaf m with
        | some v => .boxedULong v
        | none => .null, st') from
    let ⟨st', hs⟩ := hfast
    runJvm_eq_of_runJvmRes (runJvmRes_of_runJvmResFast0 260 _ _ _ rfl hs)
  cases m with
  | cellNode h nw ne sw se =>
    apply Exists.intro
    conv => lhs; arg 4; dsimp only [f_Algorithm_macrocellSingleLeaf_prog]
    heap_step_nonbranch_chunks; norm_res_fuel
    split_res_fuel 1
    rw [runJvmResFast_instanceof_step (res := 0) rfl]; norm_res_fuel
    rw [runJvmResFast_ifeq_branch (v := 0) rfl]; sl_drop; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    split_res_fuel 1
    rw [runJvmResFast_instanceof_step (res := 1) rfl]; norm_res_fuel
    rw [runJvmResFast_ifeq_fallthrough (v := 1) (by decide)]; norm_res_fuel
    heap_step_nonbranch_chunks
    simp [Algorithm.macrocellSingleLeaf]
    rfl
  | level4Node h nw ne sw se =>
    cases hnw : nw == 0
    · cases hne : ne == 0
      · apply Exists.intro
        step_sl_l4
        rw [runJvmResFast_lcmp_zero_ifeq_fallthrough hnw]; norm_res_fuel
        step_alloc1_lam step_sl_lam2
        rw [runJvmResFast_ifne_ite_fallthrough hne]
        norm_res_fuel
        heap_step_nonbranch_chunks; norm_res_fuel
        step_sl_long_cast
        rw [runJvmResFast_lcmp_zero_ifeq_fallthrough hnw]; norm_res_fuel
        heap_step_nonbranch_chunks
        simp [Algorithm.macrocellSingleLeaf, ne_of_beq_false hnw, ne_of_beq_false hne]
        rfl
      · cases hsw : sw == 0
        · apply Exists.intro
          step_sl_l4
          rw [runJvmResFast_lcmp_zero_ifeq_fallthrough hnw]; norm_res_fuel
          step_alloc1_lam step_sl_lam2
          rw [runJvmResFast_ifne_ite_branch hne]; sl_drop; norm_res_fuel
          heap_step_nonbranch_chunks; norm_res_fuel
          step_op step_sl_lam1
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_ifne_ite_fallthrough hsw]
          norm_res_fuel
          heap_step_nonbranch_chunks; norm_res_fuel
          step_sl_long_cast
          rw [runJvmResFast_lcmp_zero_ifeq_fallthrough hnw]; norm_res_fuel
          heap_step_nonbranch_chunks
          simp_all [Algorithm.macrocellSingleLeaf, bne]
          rfl
        · cases hse : se == 0
          · apply Exists.intro
            step_sl_l4
            rw [runJvmResFast_lcmp_zero_ifeq_fallthrough hnw]; norm_res_fuel
            step_alloc1_lam step_sl_lam2
            rw [runJvmResFast_ifne_ite_branch hne]; sl_drop; norm_res_fuel
            heap_step_nonbranch_chunks; norm_res_fuel
            step_op step_sl_lam1
            heap_step_nonbranch_chunks; norm_res_fuel
            rw [runJvmResFast_ifne_ite_branch hsw]; sl_drop; norm_res_fuel
            heap_step_nonbranch_chunks; norm_res_fuel
            step_op step_sl_lam0
            heap_step_nonbranch_chunks; norm_res_fuel
            rw [runJvmResFast_ifne_ite_fallthrough hse]
            norm_res_fuel
            heap_step_nonbranch_chunks; norm_res_fuel
            step_sl_long_cast
            rw [runJvmResFast_lcmp_zero_ifeq_fallthrough hnw]; norm_res_fuel
            heap_step_nonbranch_chunks
            simp_all [Algorithm.macrocellSingleLeaf, bne]
            rfl
          · apply Exists.intro
            step_sl_l4
            norm_lcmp_zero
            rw [runJvmResFast_lcmp_zero_ifeq_fallthrough hnw]; norm_res_fuel
            step_alloc1_lam step_sl_lam2
            rw [runJvmResFast_ifne_ite_branch hne]; sl_drop; norm_res_fuel
            heap_step_nonbranch_chunks; norm_res_fuel
            step_op step_sl_lam1
            heap_step_nonbranch_chunks; norm_res_fuel
            rw [runJvmResFast_ifne_ite_branch hsw]; sl_drop; norm_res_fuel
            heap_step_nonbranch_chunks; norm_res_fuel
            step_op step_sl_lam0
            heap_step_nonbranch_chunks; norm_res_fuel
            rw [runJvmResFast_ifne_ite_branch hse]; sl_drop; norm_res_fuel
            heap_step_nonbranch_chunks
            simp_all [Algorithm.macrocellSingleLeaf, bne]
            rfl
    · cases hne : ne == 0
      · cases hsw : sw == 0
        · apply Exists.intro
          step_sl_l4
          norm_lcmp_zero
          rw [runJvmResFast_lcmp_zero_ifeq_branch hnw]; sl_drop; norm_res_fuel
          step_sl_long_cast
          norm_lcmp_zero
          rw [runJvmResFast_lcmp_zero_ifeq_branch hnw]; sl_drop; norm_res_fuel
          heap_step_nonbranch_chunks; norm_res_fuel
          norm_lcmp_zero
          rw [runJvmResFast_lcmp_zero_ifeq_fallthrough hne]; norm_res_fuel
          heap_step_nonbranch_chunks; norm_res_fuel
          step_alloc1_lam step_sl_lam1
          rw [runJvmResFast_ifne_ite_fallthrough hsw]
          norm_res_fuel
          heap_step_nonbranch_chunks; norm_res_fuel
          step_sl_long_cast
          step_alloc1_lam step_sl_lam2
          rw [runJvmResFast_ifne_ite_fallthrough hne]
          norm_res_fuel
          heap_step_nonbranch_chunks
          simp_all [Algorithm.macrocellSingleLeaf, bne]
          rfl
        · cases hse : se == 0
          · apply Exists.intro
            step_sl_l4
            norm_lcmp_zero
            rw [runJvmResFast_lcmp_zero_ifeq_branch hnw]; sl_drop; norm_res_fuel
            step_sl_long_cast
            norm_lcmp_zero
            rw [runJvmResFast_lcmp_zero_ifeq_branch hnw]; sl_drop; norm_res_fuel
            heap_step_nonbranch_chunks; norm_res_fuel
            norm_lcmp_zero
            rw [runJvmResFast_lcmp_zero_ifeq_fallthrough hne]; norm_res_fuel
            heap_step_nonbranch_chunks; norm_res_fuel
            step_alloc1_lam step_sl_lam1
            rw [runJvmResFast_ifne_ite_branch hsw]; sl_drop; norm_res_fuel
            heap_step_nonbranch_chunks; norm_res_fuel
            step_op step_sl_lam0
            heap_step_nonbranch_chunks; norm_res_fuel
            rw [runJvmResFast_ifne_ite_fallthrough hse]
            norm_res_fuel
            heap_step_nonbranch_chunks; norm_res_fuel
            step_sl_long_cast
            step_alloc1_lam step_sl_lam2
            rw [runJvmResFast_ifne_ite_fallthrough hne]
            norm_res_fuel
            heap_step_nonbranch_chunks
            simp_all [Algorithm.macrocellSingleLeaf, bne]
            rfl
          · apply Exists.intro
            step_sl_l4
            norm_lcmp_zero
            rw [runJvmResFast_lcmp_zero_ifeq_branch hnw]; sl_drop; norm_res_fuel
            step_sl_long_cast
            norm_lcmp_zero
            rw [runJvmResFast_lcmp_zero_ifeq_branch hnw]; sl_drop; norm_res_fuel
            heap_step_nonbranch_chunks; norm_res_fuel
            norm_lcmp_zero
            rw [runJvmResFast_lcmp_zero_ifeq_fallthrough hne]; norm_res_fuel
            heap_step_nonbranch_chunks; norm_res_fuel
            step_alloc1_lam step_sl_lam1
            rw [runJvmResFast_ifne_ite_branch hsw]; sl_drop; norm_res_fuel
            heap_step_nonbranch_chunks; norm_res_fuel
            step_op step_sl_lam0
            heap_step_nonbranch_chunks; norm_res_fuel
            rw [runJvmResFast_ifne_ite_branch hse]; sl_drop; norm_res_fuel
            heap_step_nonbranch_chunks
            simp_all [Algorithm.macrocellSingleLeaf, bne]
            rfl
      · cases hsw : sw == 0
        · cases hse : se == 0
          · apply Exists.intro
            step_sl_l4
            norm_lcmp_zero
            rw [runJvmResFast_lcmp_zero_ifeq_branch hnw]; sl_drop; norm_res_fuel
            step_sl_long_cast
            norm_lcmp_zero
            rw [runJvmResFast_lcmp_zero_ifeq_branch hnw]; sl_drop; norm_res_fuel
            heap_step_nonbranch_chunks; norm_res_fuel
            norm_lcmp_zero
            rw [runJvmResFast_lcmp_zero_ifeq_branch hne]; sl_drop; norm_res_fuel
            heap_step_nonbranch_chunks; norm_res_fuel
            step_sl_long_cast
            step_alloc1_lam step_sl_lam2
            rw [runJvmResFast_ifne_ite_branch hne]; sl_drop; norm_res_fuel
            heap_step_nonbranch_chunks; norm_res_fuel
            norm_lcmp_zero
            rw [runJvmResFast_lcmp_zero_ifeq_fallthrough hsw]; norm_res_fuel
            heap_step_nonbranch_chunks; norm_res_fuel
            step_alloc1_lam step_sl_lam0
            rw [runJvmResFast_ifne_ite_fallthrough hse]
            norm_res_fuel
            heap_step_nonbranch_chunks; norm_res_fuel
            step_sl_long_cast
            step_alloc1_lam step_sl_lam1
            rw [runJvmResFast_ifne_ite_fallthrough hsw]
            norm_res_fuel
            heap_step_nonbranch_chunks
            simp_all [Algorithm.macrocellSingleLeaf, bne]
            rfl
          · apply Exists.intro
            step_sl_l4
            norm_lcmp_zero
            rw [runJvmResFast_lcmp_zero_ifeq_branch hnw]; sl_drop; norm_res_fuel
            step_sl_long_cast
            norm_lcmp_zero
            rw [runJvmResFast_lcmp_zero_ifeq_branch hnw]; sl_drop; norm_res_fuel
            heap_step_nonbranch_chunks; norm_res_fuel
            norm_lcmp_zero
            rw [runJvmResFast_lcmp_zero_ifeq_branch hne]; sl_drop; norm_res_fuel
            heap_step_nonbranch_chunks; norm_res_fuel
            step_sl_long_cast
            step_alloc1_lam step_sl_lam2
            rw [runJvmResFast_ifne_ite_branch hne]; sl_drop; norm_res_fuel
            heap_step_nonbranch_chunks; norm_res_fuel
            norm_lcmp_zero
            rw [runJvmResFast_lcmp_zero_ifeq_fallthrough hsw]; norm_res_fuel
            heap_step_nonbranch_chunks; norm_res_fuel
            step_alloc1_lam step_sl_lam0
            rw [runJvmResFast_ifne_ite_branch hse]; sl_drop; norm_res_fuel
            heap_step_nonbranch_chunks
            simp_all [Algorithm.macrocellSingleLeaf, bne]
            rfl
        · cases hse : se == 0
          · apply Exists.intro
            step_sl_l4
            norm_lcmp_zero
            rw [runJvmResFast_lcmp_zero_ifeq_branch hnw]; sl_drop; norm_res_fuel
            step_sl_long_cast
            norm_lcmp_zero
            rw [runJvmResFast_lcmp_zero_ifeq_branch hnw]; sl_drop; norm_res_fuel
            heap_step_nonbranch_chunks; norm_res_fuel
            norm_lcmp_zero
            rw [runJvmResFast_lcmp_zero_ifeq_branch hne]; sl_drop; norm_res_fuel
            heap_step_nonbranch_chunks; norm_res_fuel
            step_sl_long_cast
            step_alloc1_lam step_sl_lam2
            rw [runJvmResFast_ifne_ite_branch hne]; sl_drop; norm_res_fuel
            heap_step_nonbranch_chunks; norm_res_fuel
            norm_lcmp_zero
            rw [runJvmResFast_lcmp_zero_ifeq_branch hsw]; sl_drop; norm_res_fuel
            heap_step_nonbranch_chunks; norm_res_fuel
            step_sl_long_cast
            step_alloc1_lam step_sl_lam1
            rw [runJvmResFast_ifne_ite_branch hsw]; sl_drop; norm_res_fuel
            heap_step_nonbranch_chunks; norm_res_fuel
            norm_lcmp_zero
            rw [runJvmResFast_lcmp_zero_ifeq_fallthrough hse]; norm_res_fuel
            heap_step_nonbranch_chunks
            simp_all [Algorithm.macrocellSingleLeaf, bne]
            rfl
          · apply Exists.intro
            step_sl_l4
            norm_lcmp_zero
            rw [runJvmResFast_lcmp_zero_ifeq_branch hnw]; sl_drop; norm_res_fuel
            step_sl_long_cast
            norm_lcmp_zero
            rw [runJvmResFast_lcmp_zero_ifeq_branch hnw]; sl_drop; norm_res_fuel
            heap_step_nonbranch_chunks; norm_res_fuel
            norm_lcmp_zero
            rw [runJvmResFast_lcmp_zero_ifeq_branch hne]; sl_drop; norm_res_fuel
            heap_step_nonbranch_chunks; norm_res_fuel
            step_sl_long_cast
            step_alloc1_lam step_sl_lam2
            rw [runJvmResFast_ifne_ite_branch hne]; sl_drop; norm_res_fuel
            heap_step_nonbranch_chunks; norm_res_fuel
            norm_lcmp_zero
            rw [runJvmResFast_lcmp_zero_ifeq_branch hsw]; sl_drop; norm_res_fuel
            heap_step_nonbranch_chunks; norm_res_fuel
            step_sl_long_cast
            step_alloc1_lam step_sl_lam1
            rw [runJvmResFast_ifne_ite_branch hsw]; sl_drop; norm_res_fuel
            heap_step_nonbranch_chunks; norm_res_fuel
            norm_lcmp_zero
            rw [runJvmResFast_lcmp_zero_ifeq_branch hse]; sl_drop; norm_res_fuel
            heap_step_nonbranch_chunks
            simp_all [Algorithm.macrocellSingleLeaf, bne]
            rfl

/-! ### BitVec / Shift / Branch Helpers for macroCellContains & macroCellWithCell -/

private theorem ishl_fin32_eq :
    ∀ k : Fin 32, ((1 : Int32) <<< (UInt32.ofNat k.val).toInt32).toUInt32 =
      (1 : UInt32) <<< ((UInt32.ofNat k.val) &&& 31) := by
  decide

private theorem ishl_u32_eq {b : UInt32} (hb : b.toNat < 32) :
    ((1 : Int32) <<< b.toInt32).toUInt32 = (1 : UInt32) <<< (b &&& 31) := by
  simpa [UInt32.ofNat_toNat] using ishl_fin32_eq ⟨b.toNat, hb⟩

private theorem ui32_toInt32_sub1 {b : UInt32} (_hb32 : b.toNat < 32) :
    b.toInt32 - 1 = (b - 1).toInt32 := by
  simp

private theorem wfd_level {m : Algorithm.MacroCell} {d : Nat} (hm : Algorithm.WFd m d) (hd : d < 32) :
    m.level = UInt32.ofNat d := by
  induction m generalizing d with
  | level4Node => rcases hm with rfl; rfl
  | cellNode h nw ne sw se ih_nw _ _ _ =>
    rcases hm with ⟨h5, hnw, _, _, _⟩
    have ih := ih_nw hnw (by omega)
    simp [Algorithm.MacroCell.level, ih]
    change UInt32.ofNat (d - 1) + UInt32.ofNat 1 = UInt32.ofNat d
    rw [← UInt32.ofNat_add]
    have h4 : d - 1 + 1 = d := by omega
    rw [h4]

private theorem int32_ge_iff_sle (a b : Int32) :
    ¬(a < b) ↔ b.toBitVec.sle a.toBitVec = true := by
  change ¬(a.toBitVec.slt b.toBitVec = true) ↔ b.toBitVec.sle a.toBitVec = true
  simp only [BitVec.slt, BitVec.sle, decide_eq_true_eq]
  omega

private theorem int32_lt_iff_sle_false (a b : Int32) :
    a < b ↔ b.toBitVec.sle a.toBitVec = false := by
  have h := int32_ge_iff_sle a b
  cases hsle : b.toBitVec.sle a.toBitVec
  · exact ⟨fun _ => rfl, fun _ => Classical.byContradiction fun hge =>
      Bool.noConfusion (hsle.symm.trans (h.mp hge))⟩
  · exact ⟨fun ha => absurd ha (h.mpr hsle), fun hf => Bool.noConfusion hf⟩

private theorem int32_not_lt_zero_slt {x : Int32} (hx : ¬(x < 0)) :
    x.toUInt32.toBitVec.slt 0#32 = false := by
  cases hs : x.toUInt32.toBitVec.slt 0#32
  · rfl
  · exfalso; exact hx hs

private theorem int32_decide_ge_true {a b : Int32} (h : ¬(a < b)) : decide (a ≥ b) = true :=
  decide_eq_true ((int32_ge_iff_sle a b).mp h)

private theorem int32_decide_ge_false {a b : Int32} (h : a < b) : decide (a ≥ b) = false := by
  have hsle : b.toBitVec.sle a.toBitVec = false := (int32_lt_iff_sle_false a b).mp h
  exact decide_eq_false (fun hge => Bool.noConfusion (hsle.symm.trans hge))

private theorem int32_sub_toUInt32 (a b : Int32) :
    (a - b).toUInt32 = a.toUInt32 - b.toUInt32 := rfl

private theorem u32_ite_bne_0 (b : Bool) : ((if b then (1 : UInt32) else 0) != 0) = b := by
  cases b <;> decide

private theorem runJvmResFast_if_icmple_branch {f pc tgt : Nat} {prog rest : List JvmInstr}
    {a b : UInt32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} (h : a.toBitVec.sle b.toBitVec = true) :
    runJvmResFast (f + 1) prog pc (.if_icmple tgt :: rest)
        ⟨pc, .i32 b :: .i32 a :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog tgt (prog.drop tgt) ⟨tgt, stk, locs, jh, hp⟩ := by
  conv => lhs; dsimp only [runJvmResFast]; rw [Jvm.runJvmResFast.eq_def]
  simp [runJvmResFast, Jvm.JvmVal.asI32, h]

private theorem runJvmResFast_if_icmple_fallthrough {f pc tgt : Nat} {prog rest : List JvmInstr}
    {a b : UInt32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} (h : a.toBitVec.sle b.toBitVec = false) :
    runJvmResFast (f + 1) prog pc (.if_icmple tgt :: rest)
        ⟨pc, .i32 b :: .i32 a :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, stk, locs, jh, hp⟩ := by
  conv => lhs; dsimp only [runJvmResFast]; rw [Jvm.runJvmResFast.eq_def]
  simp [runJvmResFast, Jvm.JvmVal.asI32, h]

private theorem runJvmResFast_if_icmpge_branch {f pc tgt : Nat} {prog rest : List JvmInstr}
    {a b : UInt32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} (h : b.toBitVec.sle a.toBitVec = true) :
    runJvmResFast (f + 1) prog pc (.if_icmpge tgt :: rest)
        ⟨pc, .i32 b :: .i32 a :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog tgt (prog.drop tgt) ⟨tgt, stk, locs, jh, hp⟩ := by
  conv => lhs; dsimp only [runJvmResFast]; rw [Jvm.runJvmResFast.eq_def]
  simp [runJvmResFast, Jvm.JvmVal.asI32, h]

private theorem runJvmResFast_if_icmpge_fallthrough {f pc tgt : Nat} {prog rest : List JvmInstr}
    {a b : UInt32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} (h : b.toBitVec.sle a.toBitVec = false) :
    runJvmResFast (f + 1) prog pc (.if_icmpge tgt :: rest)
        ⟨pc, .i32 b :: .i32 a :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, stk, locs, jh, hp⟩ := by
  conv => lhs; dsimp only [runJvmResFast]; rw [Jvm.runJvmResFast.eq_def]
  simp [runJvmResFast, Jvm.JvmVal.asI32, h]

private theorem step_cell_getNw
    {pc : Nat} {h : UInt32} {nw ne sw se : Algorithm.MacroCell} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    Jvm.stepInstr algHooks (.invokevirtual "com/alexvanyo/composelife/model/MacroCell$CellNode"
        "getNw" "()Lcom/alexvanyo/composelife/model/MacroCell;")
      ⟨pc, .ext (.mc (.cellNode h nw ne sw se)) :: rest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .ext (.mc nw) :: rest, locs, jh, hp⟩) := rfl

private theorem step_cell_getNe
    {pc : Nat} {h : UInt32} {nw ne sw se : Algorithm.MacroCell} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    Jvm.stepInstr algHooks (.invokevirtual "com/alexvanyo/composelife/model/MacroCell$CellNode"
        "getNe" "()Lcom/alexvanyo/composelife/model/MacroCell;")
      ⟨pc, .ext (.mc (.cellNode h nw ne sw se)) :: rest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .ext (.mc ne) :: rest, locs, jh, hp⟩) := rfl

private theorem step_cell_getSw
    {pc : Nat} {h : UInt32} {nw ne sw se : Algorithm.MacroCell} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    Jvm.stepInstr algHooks (.invokevirtual "com/alexvanyo/composelife/model/MacroCell$CellNode"
        "getSw" "()Lcom/alexvanyo/composelife/model/MacroCell;")
      ⟨pc, .ext (.mc (.cellNode h nw ne sw se)) :: rest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .ext (.mc sw) :: rest, locs, jh, hp⟩) := rfl

private theorem step_cell_getSe
    {pc : Nat} {h : UInt32} {nw ne sw se : Algorithm.MacroCell} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    Jvm.stepInstr algHooks (.invokevirtual "com/alexvanyo/composelife/model/MacroCell$CellNode"
        "getSe" "()Lcom/alexvanyo/composelife/model/MacroCell;")
      ⟨pc, .ext (.mc (.cellNode h nw ne sw se)) :: rest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .ext (.mc se) :: rest, locs, jh, hp⟩) := rfl

private theorem step_leafWithCell
    {pc : Nat} {leaf : UInt64} {x y : UInt32} {isAlive : Bool} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    Jvm.stepInstr algHooks (.invokestatic "MacroCellLeanKt" "f_Algorithm_leafWithCell-9LuH6mI" "(JIIZ)J")
      ⟨pc, .i32 (if isAlive then 1 else 0) :: .i32 y :: .i32 x :: .i64 leaf :: rest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i64 (Algorithm.leafWithCell leaf x y isAlive) :: rest, locs, jh, hp⟩) := by
  have hsub : Jvm.stepInstr algHooks
      (.invokestatic "MacroCellLeanKt" "f_Algorithm_leafWithCell-9LuH6mI" "(JIIZ)J")
      ⟨pc, .i32 (if isAlive then 1 else 0) :: .i32 y :: .i32 x :: .i64 leaf :: rest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1,
        .i64 (Algorithm.leafWithCell leaf x y ((if isAlive then (1 : UInt32) else 0) != 0)) :: rest,
        locs, jh, hp⟩) := rfl
  rw [hsub, u32_ite_bne_0]

private theorem step_macroCellWithCell
    {pc : Nat} {m : Algorithm.MacroCell} {x y : UInt32} {isAlive : Bool} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    Jvm.stepInstr algHooks (.invokestatic "MacroCellLeanKt" "f_Algorithm_macroCellWithCell"
        "(Lcom/alexvanyo/composelife/model/MacroCell;IIZ)Lcom/alexvanyo/composelife/model/MacroCell;")
      ⟨pc, .i32 (if isAlive then 1 else 0) :: .i32 y :: .i32 x :: .ext (.mc m) :: rest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .ext (.mc (Algorithm.macroCellWithCell m x.toInt32 y.toInt32 isAlive)) :: rest,
        locs, jh, hp⟩) := by
  have hsub : Jvm.stepInstr algHooks (.invokestatic "MacroCellLeanKt" "f_Algorithm_macroCellWithCell"
        "(Lcom/alexvanyo/composelife/model/MacroCell;IIZ)Lcom/alexvanyo/composelife/model/MacroCell;")
      ⟨pc, .i32 (if isAlive then 1 else 0) :: .i32 y :: .i32 x :: .ext (.mc m) :: rest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1,
        .ext (.mc (Algorithm.macroCellWithCell m x.toInt32 y.toInt32
          ((if isAlive then (1 : UInt32) else 0) != 0))) :: rest, locs, jh, hp⟩) := rfl
  rw [hsub, u32_ite_bne_0]

private theorem step_leafContains
    {pc : Nat} {leaf : UInt64} {x y : UInt32} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    Jvm.stepInstr algHooks (.invokestatic "MacroCellLeanKt" "f_Algorithm_leafContains-fMEO4hA" "(JII)Z")
      ⟨pc, .i32 y :: .i32 x :: .i64 leaf :: rest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 (if Algorithm.leafContains leaf x y then 1 else 0) :: rest, locs, jh, hp⟩) := rfl

private theorem runJvmResFast_ireturn {f pc : Nat} {prog rest : List JvmInstr}
    {v : JvmVal} {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.ireturn :: rest) ⟨pc, v :: stk, locs, jh, hp⟩ =
      some (v, ⟨pc, v :: stk, locs, jh, hp⟩) := by
  dsimp only [runJvmResFast]; rw [Jvm.runJvmResFast.eq_def]; rfl

private theorem runJvmResFast_iconst0_ireturn {f pc : Nat} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 2) prog pc (.iconst 0 :: .ireturn :: rest) ⟨pc, stk, locs, jh, hp⟩ =
      some (.i32 0, ⟨pc + 1, .i32 0 :: stk, locs, jh, hp⟩) := by
  have h1 : Jvm.stepInstr algHooks (.iconst 0) ⟨pc, stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 0 :: stk, locs, jh, hp⟩) := rfl
  conv => lhs; dsimp only [runJvmResFast]; rw [Jvm.runJvmResFast.eq_def]; simp only [h1]
  rw [Jvm.runJvmResFast.eq_def]; rfl

/-! ### macroCellContains -/

local macro "mcc_drop" : tactic => `(tactic| (
  conv => lhs; arg 4; dsimp only [f_Algorithm_macroCellContains_prog, List.drop]))

local macro "norm_add" : tactic => `(tactic| (
  norm_res_fuel;
  (try (conv => lhs; arg 1; simp only [Nat.add_zero]))))

private theorem stepStatic_checkNotNullParameter_hp
    {pc : Nat} {msg obj : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} (hnull : obj.isNull = false) :
    stepInvokeStatic ⟨pc, msg :: obj :: rest, locs, jh, hp⟩
      "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter" "(Ljava/lang/Object;Ljava/lang/String;)V" =
      .inl (some ⟨pc + 1, rest, locs, jh, hp⟩) := by
  cases hp
  exact stepStatic_checkNotNullParameter hnull

private theorem setLocal_ne_eq {Ext} {locs : Nat → Jvm.JvmVal Ext} {i j : Nat} {v : Jvm.JvmVal Ext}
    (h : decide (j = i) = false) : Jvm.setLocal locs i v j = locs j := by
  dsimp [Jvm.setLocal]; simp [of_decide_eq_false h]

private theorem setLocal_eq_val {Ext} {locs : Nat → Jvm.JvmVal Ext} {i j : Nat} {v : Jvm.JvmVal Ext}
    (h : decide (j = i) = true) : Jvm.setLocal locs i v j = v := by
  dsimp [Jvm.setLocal]; simp [of_decide_eq_true h]

private theorem step1_helper {f' k pc : Nat} {prog : List JvmInstr} {instr : JvmInstr}
    {rest : List JvmInstr} {pc0 : Nat} {stk stk' : List JvmVal} {locs locs' : Nat → JvmVal}
    {jh jh' : Jvm.JvmHeap AlgExt} {hp hp' : AlgHeap}
    (hk : 1 ≤ k)
    (hbr : Jvm.isBranchInstr instr = false) (hi2l : instr ≠ .i2l)
    (hstep : Jvm.stepInstr algHooks instr ⟨pc, stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, stk', locs', jh', hp'⟩)) :
    runJvmResFast (f' + k) prog pc (instr :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      runJvmResFast (f' + (k - 1)) prog (pc + 1) rest ⟨pc + 1, stk', locs', jh', hp'⟩ := by
  rw [show f' + k = (f' + (k - 1)) + 1 from by omega]
  exact runJvmResFast_step_nonbranch_nonret hbr hi2l hstep

local macro "step1" : tactic => `(tactic| (
  rw [step1_helper (by decide) rfl (by intro h; cases h) rfl]
  (try (conv => lhs; arg 5; dsimp only [Jvm.JvmState.pc, Jvm.JvmState.stack, Jvm.JvmState.locals,
    Jvm.JvmState.jvmHeap, Jvm.JvmState.heap, Jvm.JvmVal.asI32]))
  (try (conv => lhs; arg 3; simp only [Nat.reduceAdd]))
  (try (conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd]))
  (repeat (first
    | (conv => lhs; arg 5; arg 2; rw [setLocal_eq_val rfl])
    | (conv => lhs; arg 5; arg 2; rw [setLocal_ne_eq rfl])))
  (try (conv => lhs; arg 1; simp only [Nat.reduceSub, Nat.add_zero]))))

local macro "step1_ex" : tactic => `(tactic| (
  rw [step1_helper (by decide) rfl (by intro h; cases h) rfl]
  (try dsimp only [Jvm.JvmState.pc, Jvm.JvmState.stack, Jvm.JvmState.locals,
    Jvm.JvmState.jvmHeap, Jvm.JvmState.heap, Jvm.JvmVal.asI32])
  (repeat (first
    | rw [setLocal_eq_val rfl]
    | rw [setLocal_ne_eq rfl]))
  (try simp only [Nat.reduceAdd, Nat.reduceSub, Nat.add_zero])))

private theorem step_contains_N_pc39
    (k R2 : Nat) (x y half : Int32)
    (locsMid : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hloc1 : locsMid 1 = .i32 x.toUInt32)
    (hloc5 : locsMid 5 = .i32 half.toUInt32) :
    ∃ k', k ≤ k' ∧
      runJvmResFast (k + (R2 + 7)) f_Algorithm_macroCellContains_prog 32
        (f_Algorithm_macroCellContains_prog.drop 32)
        ⟨32, [.i32 half.toUInt32, .i32 y.toUInt32], locsMid, jh, hp⟩ =
      runJvmResFast (k' + (R2 + 1)) f_Algorithm_macroCellContains_prog 39
        (f_Algorithm_macroCellContains_prog.drop 39)
        ⟨39, [.i32 half.toUInt32, .i32 x.toUInt32],
          setLocal locsMid 6 (.i32 (if decide (y < half) then 1 else 0)), jh, hp⟩ := by
  by_cases hN : y < half
  · have hNsle : half.toUInt32.toBitVec.sle y.toUInt32.toBitVec = false :=
      (int32_lt_iff_sle_false y half).mp hN
    have hNd : decide (y < half) = true := decide_eq_true hN
    refine ⟨k + 0, by omega, ?_⟩
    rw [show k + (R2 + 7) = (k + R2 + 6) + 1 from by omega]
    mcc_drop
    rw [runJvmResFast_if_icmpge_fallthrough hNsle]
    rw [show (32 : Nat) + 1 = 33 from rfl]
    rw [show k + R2 + 6 = (k + R2 + 5) + 1 from by omega]; step1
    rw [show k + R2 + 5 = (k + R2 + 4) + 1 from by omega]
    rw [runJvmResFast_goto]; mcc_drop
    rw [show k + R2 + 4 = (k + R2 + 1) + 3 from by omega]
    step1; step1; step1
    rw [show k + R2 + 1 = k + 0 + (R2 + 1) from by omega]
    conv => rhs; arg 4; dsimp only [f_Algorithm_macroCellContains_prog, List.drop]
    conv => lhs; arg 5; simp only [hloc1, hloc5]
    conv => rhs; arg 5; simp only [hNd, ↓reduceIte]
  · have hNsle : half.toUInt32.toBitVec.sle y.toUInt32.toBitVec = true :=
      (int32_ge_iff_sle y half).mp hN
    have hNd : decide (y < half) = false := decide_eq_false hN
    refine ⟨k + 1, by omega, ?_⟩
    rw [show k + (R2 + 7) = (k + R2 + 6) + 1 from by omega]
    mcc_drop
    rw [runJvmResFast_if_icmpge_branch hNsle]; mcc_drop
    rw [show k + R2 + 6 = (k + 1 + R2 + 1) + 4 from by omega]
    step1; step1; step1; step1
    rw [show k + 1 + R2 + 1 = k + 1 + (R2 + 1) from by omega]
    conv => rhs; arg 4; dsimp only [f_Algorithm_macroCellContains_prog, List.drop]
    conv => lhs; arg 5; simp only [hloc1, hloc5]
    conv => rhs; arg 5; simp only [hNd, Bool.false_eq_true, ↓reduceIte]

private theorem step_contains_W_pc47
    (k R2 : Nat) (m : Algorithm.MacroCell) (x y half : Int32)
    (locsMid : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hloc0 : locsMid 0 = .ext (.mc m)) :
    let locs1 := setLocal (setLocal locsMid 6 (.i32 (if decide (y < half) then 1 else 0)))
      7 (.i32 (if decide (x < half) then 1 else 0))
    ∃ k', k ≤ k' ∧
      runJvmResFast (k + (R2 + 8)) f_Algorithm_macroCellContains_prog 39
        (f_Algorithm_macroCellContains_prog.drop 39)
        ⟨39, [.i32 half.toUInt32, .i32 x.toUInt32],
          setLocal locsMid 6 (.i32 (if decide (y < half) then 1 else 0)), jh, hp⟩ =
      runJvmResFast (k' + (R2 + 1)) f_Algorithm_macroCellContains_prog 47
        (f_Algorithm_macroCellContains_prog.drop 47)
        ⟨47, [.ext (.mc m)], setLocal locs1 8 (.ext (.mc m)), jh, hp⟩ := by
  intro locs1
  by_cases hW : x < half
  · have hWsle : half.toUInt32.toBitVec.sle x.toUInt32.toBitVec = false :=
      (int32_lt_iff_sle_false x half).mp hW
    have hWd : decide (x < half) = true := decide_eq_true hW
    refine ⟨k + 0, by omega, ?_⟩
    mcc_drop
    rw [show k + (R2 + 8) = (k + R2 + 7) + 1 from by omega]
    rw [runJvmResFast_if_icmpge_fallthrough hWsle]
    rw [show (39 : Nat) + 1 = 40 from rfl]
    rw [show k + R2 + 7 = (k + R2 + 6) + 1 from by omega]; step1
    rw [show k + R2 + 6 = (k + R2 + 5) + 1 from by omega]
    rw [runJvmResFast_goto]; mcc_drop
    rw [show k + R2 + 5 = (k + R2 + 1) + 4 from by omega]
    step1; step1; step1; step1
    rw [show k + R2 + 1 = k + 0 + (R2 + 1) from by omega]
    conv => rhs; arg 4; dsimp only [f_Algorithm_macroCellContains_prog, List.drop]
    conv => lhs; arg 5; simp only [hloc0]
    dsimp only [locs1]
    conv => rhs; arg 5; simp only [hWd, ↓reduceIte]
  · have hWsle : half.toUInt32.toBitVec.sle x.toUInt32.toBitVec = true :=
      (int32_ge_iff_sle x half).mp hW
    have hWd : decide (x < half) = false := decide_eq_false hW
    refine ⟨k + 1, by omega, ?_⟩
    mcc_drop
    rw [show k + (R2 + 8) = (k + R2 + 7) + 1 from by omega]
    rw [runJvmResFast_if_icmpge_branch hWsle]; mcc_drop
    rw [show k + R2 + 7 = (k + 1 + R2 + 1) + 5 from by omega]
    step1; step1; step1; step1; step1
    rw [show k + 1 + R2 + 1 = k + 1 + (R2 + 1) from by omega]
    conv => rhs; arg 4; dsimp only [f_Algorithm_macroCellContains_prog, List.drop]
    conv => lhs; arg 5; simp only [hloc0]
    dsimp only [locs1]
    conv => rhs; arg 5; simp only [hWd, Bool.false_eq_true, ↓reduceIte]

private theorem step_contains_in_bounds_pc32
    (f R : Nat) {m : Algorithm.MacroCell} {d : Nat} (hm : Algorithm.WFd m d) (hd : d < 32)
    (x y : Int32) (locsBase : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hx0 : ¬(x < 0)) (hy0 : ¬(y < 0))
    (hxw : x < (1 : Int32) <<< m.level.toInt32) (hyw : y < (1 : Int32) <<< m.level.toInt32) :
    let w : Int32 := (1 : Int32) <<< m.level.toInt32
    let half : Int32 := (1 : Int32) <<< (m.level.toInt32 - 1)
    let locs0 := setLocal (setLocal (setLocal locsBase 0 (.ext (.mc m))) 1 (.i32 x.toUInt32)) 2 (.i32 y.toUInt32)
    let locsMid := setLocal (setLocal (setLocal (setLocal (setLocal locs0
      4 (.ext (.mc m))) 5 (.i32 0)) 3 (.i32 m.level)) 4 (.i32 w.toUInt32)) 5 (.i32 half.toUInt32)
    runJvmResFast (f + (R + 43)) f_Algorithm_macroCellContains_prog 3 (f_Algorithm_macroCellContains_prog.drop 3)
        ⟨3, [], locs0, jh, hp⟩ =
      runJvmResFast (f + (R + 14)) f_Algorithm_macroCellContains_prog 32 (f_Algorithm_macroCellContains_prog.drop 32)
        ⟨32, [.i32 half.toUInt32, .i32 y.toUInt32], locsMid, jh, hp⟩ := by
  intro w half locs0 locsMid
  have hlvl : m.level = UInt32.ofNat d := wfd_level hm hd
  have hm32 : m.level.toNat < 32 := by
    rw [hlvl]; change (BitVec.ofNat 32 d).toNat < 32
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hd
  have hm1_32 : (m.level - 1).toNat < 32 := by
    have hd4 : 4 ≤ d := by
      cases m with | level4Node => exact Nat.le_of_eq hm.symm | cellNode => exact Nat.le_of_lt hm.1
    have hle1 : (1 : UInt32) ≤ m.level := by
      rw [UInt32.le_iff_toNat_le, hlvl]
      change (BitVec.ofNat 32 1).toNat ≤ (BitVec.ofNat 32 d).toNat
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide), Nat.mod_eq_of_lt (by omega)]
      exact Nat.le_trans (by decide) hd4
    rw [UInt32.toNat_sub_of_le m.level 1 hle1]; omega
  have hw_eq : w.toUInt32 = (1 : UInt32) <<< (m.level &&& 31) := ishl_u32_eq hm32
  have hhalf_eq : half.toUInt32 = (1 : UInt32) <<< ((m.level - 1) &&& 31) := by
    change ((1 : Int32) <<< (m.level.toInt32 - 1)).toUInt32 = _
    rw [ui32_toInt32_sub1 hm32]
    exact ishl_u32_eq hm1_32
  have hx0' : x.toUInt32.toBitVec.slt 0#32 = false := int32_not_lt_zero_slt hx0
  have hy0' : y.toUInt32.toBitVec.slt 0#32 = false := int32_not_lt_zero_slt hy0
  have hxw' : w.toUInt32.toBitVec.sle x.toUInt32.toBitVec = false := (int32_lt_iff_sle_false x w).mp hxw
  have hyw' : w.toUInt32.toBitVec.sle y.toUInt32.toBitVec = false := (int32_lt_iff_sle_false y w).mp hyw
  rw [show f + (R + 43) = (f + R + 42) + 1 from by omega]
  dsimp only [locs0]
  mcc_drop; step1
  rw [show f + R + 42 = (f + R + 41) + 1 from by omega]
  rw [runJvmResFast_iflt_fallthrough hx0', show (4 : Nat) + 1 = 5 from rfl]
  rw [show f + R + 41 = (f + R + 40) + 1 from by omega]
  step1; norm_add
  rw [show f + R + 40 = (f + R + 39) + 1 from by omega]
  rw [runJvmResFast_iflt_fallthrough hy0', show (6 : Nat) + 1 = 7 from rfl]
  rw [show f + R + 39 = (f + R + 34) + 5 from by omega]
  step1; step1; step1; step1; step1; norm_add
  rw [show f + R + 34 = (f + R + 33) + 1 from by omega]
  step_op step_mcLevel
  conv => lhs; arg 1; rw [Nat.add_sub_cancel]
  rw [show (12 : Nat) + 1 = 13 from rfl]
  rw [show f + R + 33 = (f + R + 26) + 7 from by omega]
  step1; step1; step1; step1; step1; step1; step1; norm_add
  rw [← hw_eq, show f + R + 26 = (f + R + 25) + 1 from by omega]
  rw [runJvmResFast_if_icmple_fallthrough hxw', show (20 : Nat) + 1 = 21 from rfl]
  rw [show f + R + 25 = (f + R + 23) + 2 from by omega]
  step1; step1; norm_add
  rw [show f + R + 23 = (f + R + 22) + 1 from by omega]
  rw [runJvmResFast_if_icmple_fallthrough hyw', show (23 : Nat) + 1 = 24 from rfl]
  rw [show f + R + 22 = (f + R + 14) + 8 from by omega]
  step1; step1; step1; step1; step1; step1; step1; step1; norm_add
  rw [← hhalf_eq, show f + R + 14 = f + (R + 14) from by omega]
  conv => rhs; arg 4; dsimp only [f_Algorithm_macroCellContains_prog, List.drop]

private theorem step_contains_in_bounds_pc47
    (f R : Nat) {m : Algorithm.MacroCell} {d : Nat} (hm : Algorithm.WFd m d) (hd : d < 32)
    (x y : Int32) (locsBase : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hx0 : ¬(x < 0)) (hy0 : ¬(y < 0))
    (hxw : x < (1 : Int32) <<< m.level.toInt32) (hyw : y < (1 : Int32) <<< m.level.toInt32) :
    let w : Int32 := (1 : Int32) <<< m.level.toInt32
    let half : Int32 := (1 : Int32) <<< (m.level.toInt32 - 1)
    let isNorth : Bool := decide (y < half)
    let isWest : Bool := decide (x < half)
    let locs0 := setLocal (setLocal (setLocal locsBase 0 (.ext (.mc m))) 1 (.i32 x.toUInt32)) 2 (.i32 y.toUInt32)
    let locs1 := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal locs0
      4 (.ext (.mc m))) 5 (.i32 0)) 3 (.i32 m.level)) 4 (.i32 w.toUInt32))
      5 (.i32 half.toUInt32)) 6 (.i32 (if isNorth then 1 else 0))) 7 (.i32 (if isWest then 1 else 0))
    ∃ f', f ≤ f' ∧
      runJvmResFast (f + (R + 43)) f_Algorithm_macroCellContains_prog 3 (f_Algorithm_macroCellContains_prog.drop 3)
        ⟨3, [], locs0, jh, hp⟩ =
      runJvmResFast (f' + (R + 1)) f_Algorithm_macroCellContains_prog 47
        (f_Algorithm_macroCellContains_prog.drop 47)
        ⟨47, [.ext (.mc m)], setLocal locs1 8 (.ext (.mc m)), jh, hp⟩ := by
  intro w half isNorth isWest locs0 locs1
  let locsMid := setLocal (setLocal (setLocal (setLocal (setLocal locs0
    4 (.ext (.mc m))) 5 (.i32 0)) 3 (.i32 m.level)) 4 (.i32 w.toUInt32)) 5 (.i32 half.toUInt32)
  have h0 := step_contains_in_bounds_pc32 f R hm hd x y locsBase jh hp hx0 hy0 hxw hyw
  rcases step_contains_N_pc39 f (R + 7) x y half locsMid jh hp rfl rfl with ⟨k1, hk1, hNrw⟩
  rcases step_contains_W_pc47 k1 R m x y half locsMid jh hp rfl with ⟨k2, hk2, hWrw⟩
  refine ⟨k2, by omega, ?_⟩
  rw [h0, show f + (R + 14) = f + ((R + 7) + 7) from by omega]
  exact hNrw.trans hWrw

private theorem step_contains_oob
    (f : Nat) {m : Algorithm.MacroCell} {d : Nat} (hm : Algorithm.WFd m d) (hd : d < 32)
    (x y : Int32) (locsBase : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hoob : x < 0 ∨ y < 0 ∨ ¬(x < (1 : Int32) <<< m.level.toInt32) ∨
      ¬(y < (1 : Int32) <<< m.level.toInt32)) :
    let locs0 := setLocal (setLocal (setLocal locsBase 0 (.ext (.mc m))) 1 (.i32 x.toUInt32)) 2 (.i32 y.toUInt32)
    ∃ st', runJvmResFast (f + 30) f_Algorithm_macroCellContains_prog 3 (f_Algorithm_macroCellContains_prog.drop 3)
        ⟨3, [], locs0, jh, hp⟩ = some (.i32 0, st') := by
  intro locs0
  have hlvl : m.level = UInt32.ofNat d := wfd_level hm hd
  have hm32 : m.level.toNat < 32 := by
    rw [hlvl]; change (BitVec.ofNat 32 d).toNat < 32
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hd
  have hw_eq : ((1 : Int32) <<< m.level.toInt32).toUInt32 = (1 : UInt32) <<< (m.level &&& 31) :=
    ishl_u32_eq hm32
  let w : Int32 := (1 : Int32) <<< m.level.toInt32
  by_cases hx0 : x < 0
  · have hx0' : x.toUInt32.toBitVec.slt 0#32 = true := hx0
    apply Exists.intro; mcc_drop
    rw [show f + 30 = (f + 29) + 1 from by omega]; heap_step_nonbranch_chunks; norm_add
    rw [show f + 29 = (f + 28) + 1 from by omega]; rw [runJvmResFast_iflt_branch hx0']; mcc_drop
    rw [show f + 28 = (f + 26) + 2 from by omega]; exact runJvmResFast_iconst0_ireturn
  · by_cases hy0 : y < 0
    · have hx0' : x.toUInt32.toBitVec.slt 0#32 = false := int32_not_lt_zero_slt hx0
      have hy0' : y.toUInt32.toBitVec.slt 0#32 = true := hy0
      apply Exists.intro; mcc_drop
      rw [show f + 30 = (f + 29) + 1 from by omega]; heap_step_nonbranch_chunks; norm_add
      rw [show f + 29 = (f + 28) + 1 from by omega]; rw [runJvmResFast_iflt_fallthrough hx0']
      rw [show f + 28 = (f + 27) + 1 from by omega]; heap_step_nonbranch_chunks; norm_add
      rw [show f + 27 = (f + 26) + 1 from by omega]; rw [runJvmResFast_iflt_branch hy0']; mcc_drop
      rw [show f + 26 = (f + 24) + 2 from by omega]; exact runJvmResFast_iconst0_ireturn
    · have hx0' : x.toUInt32.toBitVec.slt 0#32 = false := int32_not_lt_zero_slt hx0
      have hy0' : y.toUInt32.toBitVec.slt 0#32 = false := int32_not_lt_zero_slt hy0
      by_cases hxw : ¬(x < w)
      · have hxw' : w.toUInt32.toBitVec.sle x.toUInt32.toBitVec = true := (int32_ge_iff_sle x w).mp hxw
        apply Exists.intro; mcc_drop
        rw [show f + 30 = (f + 29) + 1 from by omega]; heap_step_nonbranch_chunks; norm_add
        rw [show f + 29 = (f + 28) + 1 from by omega]; rw [runJvmResFast_iflt_fallthrough hx0']
        rw [show f + 28 = (f + 27) + 1 from by omega]; heap_step_nonbranch_chunks; norm_add
        rw [show f + 27 = (f + 26) + 1 from by omega]; rw [runJvmResFast_iflt_fallthrough hy0']
        rw [show f + 26 = (f + 21) + 5 from by omega]; heap_step_nonbranch_chunks; norm_add
        rw [show f + 21 = (f + 20) + 1 from by omega]; step_op step_mcLevel
        rw [show f + 20 = (f + 13) + 7 from by omega]; heap_step_nonbranch_chunks; norm_add
        rw [← hw_eq, show f + 13 = (f + 12) + 1 from by omega]
        rw [runJvmResFast_if_icmple_branch hxw']; mcc_drop
        rw [show f + 12 = (f + 10) + 2 from by omega]; exact runJvmResFast_iconst0_ireturn
      · have hyw : ¬(y < w) := by
          rcases hoob with h | h | h | h <;>
            first | exact absurd h hx0 | exact absurd h hy0 | exact absurd h hxw | exact h
        have hxw' : w.toUInt32.toBitVec.sle x.toUInt32.toBitVec = false :=
          (int32_lt_iff_sle_false x w).mp (Classical.not_not.mp hxw)
        have hyw' : w.toUInt32.toBitVec.sle y.toUInt32.toBitVec = true := (int32_ge_iff_sle y w).mp hyw
        apply Exists.intro; mcc_drop
        rw [show f + 30 = (f + 29) + 1 from by omega]; heap_step_nonbranch_chunks; norm_add
        rw [show f + 29 = (f + 28) + 1 from by omega]; rw [runJvmResFast_iflt_fallthrough hx0']
        rw [show f + 28 = (f + 27) + 1 from by omega]; heap_step_nonbranch_chunks; norm_add
        rw [show f + 27 = (f + 26) + 1 from by omega]; rw [runJvmResFast_iflt_fallthrough hy0']
        rw [show f + 26 = (f + 21) + 5 from by omega]; heap_step_nonbranch_chunks; norm_add
        rw [show f + 21 = (f + 20) + 1 from by omega]; step_op step_mcLevel
        rw [show f + 20 = (f + 13) + 7 from by omega]; heap_step_nonbranch_chunks; norm_add
        rw [← hw_eq, show f + 13 = (f + 12) + 1 from by omega]
        rw [runJvmResFast_if_icmple_fallthrough hxw']
        rw [show f + 12 = (f + 10) + 2 from by omega]; heap_step_nonbranch_chunks; norm_add
        rw [show f + 10 = (f + 9) + 1 from by omega]
        rw [runJvmResFast_if_icmple_branch hyw']; mcc_drop
        rw [show f + 9 = (f + 7) + 2 from by omega]; exact runJvmResFast_iconst0_ireturn

local macro "mcc_norm" : tactic => `(tactic| (
  norm_res_fuel;
  (try (conv => lhs; arg 1; rw [Nat.add_sub_assoc (by decide)]; simp only [Nat.reduceSub]));
  (try (conv => lhs; arg 1; simp only [Nat.add_zero]))))

local macro "mcc_l4_tail" get_thm:ident : tactic => `(tactic| (
  heap_step_nonbranch_chunks; mcc_norm;
  split_res_fuel 1; rw [runJvmResFast_checkcast_step rfl]; mcc_norm;
  step_op $get_thm; mcc_norm;
  heap_step_nonbranch_chunks; mcc_norm;
  step_op step_leafContains; mcc_norm;
  split_res_fuel 1; rw [runJvmResFast_ireturn]))

private theorem macroCellContains_loop (m : Algorithm.MacroCell) :
    ∀ (d f : Nat), Algorithm.WFd m d → d < 32 →
      ∀ (x y : Int32) (locsBase : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap),
    let locs0 := setLocal (setLocal (setLocal locsBase 0 (.ext (.mc m))) 1 (.i32 x.toUInt32)) 2 (.i32 y.toUInt32)
    ∃ st', runJvmResFast (f + (d + 1) * 80) f_Algorithm_macroCellContains_prog 3
        (f_Algorithm_macroCellContains_prog.drop 3) ⟨3, [], locs0, jh, hp⟩ =
      some (.i32 (if Algorithm.macroCellContains m x y then 1 else 0), st') := by
  induction m with
  | level4Node h nw ne sw se =>
    intro d f hm hd x y locsBase jh hp locs0
    rcases hm with rfl
    let w : Int32 := (1 : Int32) <<< (Algorithm.MacroCell.level4Node h nw ne sw se).level.toInt32
    by_cases hoob : x < 0 ∨ y < 0 ∨ ¬(x < w) ∨ ¬(y < w)
    · have hm0 : Algorithm.macroCellContains (.level4Node h nw ne sw se) x y = false := by
        rw [Algorithm.macroCellContains]
        rcases hoob with h1 | h1 | h1 | h1
        · simp [h1]
        · by_cases hx : x < 0 <;> simp [hx, h1]
        · by_cases hx : x < 0 <;> by_cases hy : y < 0 <;> simp [hx, hy, h1, w]
        · by_cases hx : x < 0 <;> by_cases hy : y < 0 <;> by_cases hxw : x < w <;> simp [hx, hy, hxw, h1, w]
      have hm4 : Algorithm.WFd (.level4Node h nw ne sw se) 4 := rfl
      rw [hm0, show f + (4 + 1) * 80 = (f + 370) + 30 from by omega]
      exact step_contains_oob (f + 370) hm4 hd x y locsBase jh hp hoob
    · have hm4 : Algorithm.WFd (.level4Node h nw ne sw se) 4 := rfl
      have hx0 : ¬(x < 0) := fun h1 => hoob (Or.inl h1)
      have hy0 : ¬(y < 0) := fun h1 => hoob (Or.inr (Or.inl h1))
      have hxw_lt : x < w := Classical.not_not.mp fun h1 => hoob (Or.inr (Or.inr (Or.inl h1)))
      have hyw_lt : y < w := Classical.not_not.mp fun h1 => hoob (Or.inr (Or.inr (Or.inr h1)))
      rw [show f + (4 + 1) * 80 = (f + 329) + (28 + 43) from by omega]
      rcases step_contains_in_bounds_pc47 (f + 329) 28 hm4 hd x y locsBase jh hp hx0 hy0 hxw_lt hyw_lt with
        ⟨f', _, hpre⟩
      rw [show f' + (28 + 1) = f' + 29 from by omega] at hpre
      let half : Int32 := (1 : Int32) <<< ((Algorithm.MacroCell.level4Node h nw ne sw se).level.toInt32 - 1)
      let locs47 := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
        (setLocal (setLocal (setLocal locsBase 0 (.ext (.mc (.level4Node h nw ne sw se))))
          1 (.i32 x.toUInt32)) 2 (.i32 y.toUInt32)) 4 (.ext (.mc (.level4Node h nw ne sw se))))
        5 (.i32 0)) 3 (.i32 (Algorithm.MacroCell.level4Node h nw ne sw se).level))
        4 (.i32 w.toUInt32)) 5 (.i32 half.toUInt32))
        6 (.i32 (if decide (y < half) then 1 else 0)))
        7 (.i32 (if decide (x < half) then 1 else 0)))
        8 (.ext (.mc (.level4Node h nw ne sw se)))
      have hhead :
          runJvmResFast (f' + 29) f_Algorithm_macroCellContains_prog 47
            (f_Algorithm_macroCellContains_prog.drop 47)
            ⟨47, [.ext (.mc (.level4Node h nw ne sw se))], locs47, jh, hp⟩ =
          runJvmResFast (f' + 26) f_Algorithm_macroCellContains_prog 50
            (f_Algorithm_macroCellContains_prog.drop 50)
            ⟨50, [.i32 (if decide (y < half) then 1 else 0)], locs47, jh, hp⟩ := by
        mcc_drop
        rw [show f' + 29 = (f' + 28) + 1 from by omega]
        rw [runJvmResFast_instanceof_step (res := 1) rfl]
        rw [show f' + 28 = (f' + 27) + 1 from by omega]
        rw [runJvmResFast_ifeq_fallthrough (v := 1) (by decide)]
        rw [show f' + 27 = (f' + 26) + 1 from by omega]
        heap_step_nonbranch_chunks; norm_add
        conv => rhs; arg 4; dsimp only [f_Algorithm_macroCellContains_prog, List.drop]; rfl
      rw [hpre, hhead]
      have hfx0 : decide (x < 0) = false := decide_eq_false hx0
      have hfy0 : decide (y < 0) = false := decide_eq_false hy0
      have hfxw : decide (x ≥ (1 : Int32) <<< (Algorithm.MacroCell.level4Node h nw ne sw se).level.toInt32) = false :=
        int32_decide_ge_false hxw_lt
      have hfyw : decide (y ≥ (1 : Int32) <<< (Algorithm.MacroCell.level4Node h nw ne sw se).level.toInt32) = false :=
        int32_decide_ge_false hyw_lt
      dsimp only [locs47]
      cases hN : decide (y < half) <;> cases hW : decide (x < half)
      · apply Exists.intro
        rw [show f' + 26 = (f' + 25) + 1 from by omega]
        mcc_drop
        rw [show (if false = true then (1 : UInt32) else 0) = 0 from rfl,
          runJvmResFast_ifne_fallthrough, show (50 : Nat) + 1 = 51 from rfl]
        rw [show f' + 25 = (f' + 24) + 1 from by omega]; heap_step_nonbranch_chunks; norm_add
        conv => lhs; arg 5; dsimp only [Jvm.JvmState.pc, Jvm.JvmState.stack]
        rw [show f' + 24 = (f' + 23) + 1 from by omega]
        rw [runJvmResFast_ifne_fallthrough, show (52 : Nat) + 1 = 53 from rfl]
        mcc_l4_tail step_l4_getSe
        simp only [Algorithm.macroCellContains, hfx0, hfy0, hfxw, hfyw, half, hN, hW,
          int32_sub_toUInt32, Bool.false_or]; rfl
      · apply Exists.intro
        rw [show f' + 26 = (f' + 25) + 1 from by omega]
        mcc_drop
        rw [show (if false = true then (1 : UInt32) else 0) = 0 from rfl,
          runJvmResFast_ifne_fallthrough, show (50 : Nat) + 1 = 51 from rfl]
        rw [show f' + 25 = (f' + 24) + 1 from by omega]; heap_step_nonbranch_chunks; norm_add
        conv => lhs; arg 5; dsimp only [Jvm.JvmState.pc, Jvm.JvmState.stack]
        rw [show f' + 24 = (f' + 23) + 1 from by omega]
        rw [show (if true = true then (1 : UInt32) else 0) = 1 from rfl]
        rw [runJvmResFast_ifne_branch (v := 1) (by decide)]; mcc_drop
        mcc_l4_tail step_l4_getSw
        simp only [Algorithm.macroCellContains, hfx0, hfy0, hfxw, hfyw, half, hN, hW,
          int32_sub_toUInt32, Bool.false_or]; rfl
      · apply Exists.intro
        rw [show f' + 26 = (f' + 25) + 1 from by omega]
        mcc_drop
        rw [show (if true = true then (1 : UInt32) else 0) = 1 from rfl]
        rw [runJvmResFast_ifne_branch (v := 1) (by decide)]; mcc_drop
        rw [show f' + 25 = (f' + 24) + 1 from by omega]; heap_step_nonbranch_chunks; norm_add
        conv => lhs; arg 5; dsimp only [Jvm.JvmState.pc, Jvm.JvmState.stack]
        rw [show f' + 24 = (f' + 23) + 1 from by omega]
        rw [show (if false = true then (1 : UInt32) else 0) = 0 from rfl,
          runJvmResFast_ifne_fallthrough, show (82 : Nat) + 1 = 83 from rfl]
        mcc_l4_tail step_l4_getNe
        simp only [Algorithm.macroCellContains, hfx0, hfy0, hfxw, hfyw, half, hN, hW,
          int32_sub_toUInt32, Bool.false_or]; rfl
      · apply Exists.intro
        rw [show f' + 26 = (f' + 25) + 1 from by omega]
        mcc_drop
        rw [show (if true = true then (1 : UInt32) else 0) = 1 from rfl]
        rw [runJvmResFast_ifne_branch (v := 1) (by decide)]; mcc_drop
        rw [show f' + 25 = (f' + 24) + 1 from by omega]; heap_step_nonbranch_chunks; norm_add
        conv => lhs; arg 5; dsimp only [Jvm.JvmState.pc, Jvm.JvmState.stack]
        rw [show f' + 24 = (f' + 23) + 1 from by omega]
        rw [runJvmResFast_ifne_branch (v := 1) (by decide)]; mcc_drop
        mcc_l4_tail step_l4_getNw
        simp only [Algorithm.macroCellContains, hfx0, hfy0, hfxw, hfyw, half, hN, hW,
          Bool.false_or]; rfl
  | cellNode h nw ne sw se ih_nw ih_ne ih_sw ih_se =>
    intro d f hm hd x y locsBase jh hp locs0
    have hm_c : Algorithm.WFd (.cellNode h nw ne sw se) d := hm
    rcases hm with ⟨hd5, hnw, hne, hsw, hse⟩
    let w : Int32 := (1 : Int32) <<< (Algorithm.MacroCell.cellNode h nw ne sw se).level.toInt32
    by_cases hoob : x < 0 ∨ y < 0 ∨ ¬(x < w) ∨ ¬(y < w)
    · have hm0 : Algorithm.macroCellContains (.cellNode h nw ne sw se) x y = false := by
        rw [Algorithm.macroCellContains]
        rcases hoob with h1 | h1 | h1 | h1
        · simp [h1]
        · by_cases hx : x < 0 <;> simp [hx, h1]
        · by_cases hx : x < 0 <;> by_cases hy : y < 0 <;> simp [hx, hy, h1, w]
        · by_cases hx : x < 0 <;> by_cases hy : y < 0 <;> by_cases hxw : x < w <;> simp [hx, hy, hxw, h1, w]
      rw [hm0, show f + (d + 1) * 80 = (f + d * 80 + 50) + 30 from by omega]
      exact step_contains_oob (f + d * 80 + 50) hm_c hd x y locsBase jh hp hoob
    · have hx0 : ¬(x < 0) := fun h1 => hoob (Or.inl h1)
      have hy0 : ¬(y < 0) := fun h1 => hoob (Or.inr (Or.inl h1))
      have hxw_lt : x < w := Classical.not_not.mp fun h1 => hoob (Or.inr (Or.inr (Or.inl h1)))
      have hyw_lt : y < w := Classical.not_not.mp fun h1 => hoob (Or.inr (Or.inr (Or.inr h1)))
      have hrem : f + (d + 1) * 80 = f + ((d - 1 + 1) * 80 + 37 + 43) := by
        have hd1 : d - 1 + 1 = d := by omega
        rw [hd1]; omega
      rw [hrem]
      rcases step_contains_in_bounds_pc47 f ((d - 1 + 1) * 80 + 37)
          hm_c hd x y locsBase jh hp hx0 hy0 hxw_lt hyw_lt with ⟨f', _, hpre⟩
      rw [show f' + ((d - 1 + 1) * 80 + 37 + 1) = f' + ((d - 1 + 1) * 80 + 38) from by omega] at hpre
      let half : Int32 := (1 : Int32) <<< ((Algorithm.MacroCell.cellNode h nw ne sw se).level.toInt32 - 1)
      have hfxw : decide (x ≥ (1 : Int32) <<< (Algorithm.MacroCell.cellNode h nw ne sw se).level.toInt32) = false :=
        int32_decide_ge_false hxw_lt
      have hfyw : decide (y ≥ (1 : Int32) <<< (Algorithm.MacroCell.cellNode h nw ne sw se).level.toInt32) = false :=
        int32_decide_ge_false hyw_lt
      have hm_simp : Algorithm.macroCellContains (.cellNode h nw ne sw se) x y =
          match decide (y < half), decide (x < half) with
          | true, true => Algorithm.macroCellContains nw x y
          | true, false => Algorithm.macroCellContains ne (x - half) y
          | false, true => Algorithm.macroCellContains sw x (y - half)
          | false, false => Algorithm.macroCellContains se (x - half) (y - half) := by
        rw [Algorithm.macroCellContains]
        simp only [hx0, hy0, hfxw, hfyw]; rfl
      rw [hm_simp]
      have hhead : ∀ (R2 : Nat),
          runJvmResFast (f' + (R2 + 38)) f_Algorithm_macroCellContains_prog 47
            (f_Algorithm_macroCellContains_prog.drop 47)
            ⟨47, [.ext (.mc (.cellNode h nw ne sw se))],
              setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
                (setLocal (setLocal (setLocal locsBase 0 (.ext (.mc (.cellNode h nw ne sw se))))
                  1 (.i32 x.toUInt32)) 2 (.i32 y.toUInt32)) 4 (.ext (.mc (.cellNode h nw ne sw se))))
                5 (.i32 0)) 3 (.i32 (Algorithm.MacroCell.cellNode h nw ne sw se).level))
                4 (.i32 w.toUInt32)) 5 (.i32 half.toUInt32))
                6 (.i32 (if decide (y < half) then 1 else 0)))
                7 (.i32 (if decide (x < half) then 1 else 0)))
                8 (.ext (.mc (.cellNode h nw ne sw se))), jh, hp⟩ =
          runJvmResFast (f' + (R2 + 32)) f_Algorithm_macroCellContains_prog 111
            (f_Algorithm_macroCellContains_prog.drop 111)
            ⟨111, [.i32 (if decide (y < half) then 1 else 0)],
              setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
                (setLocal (setLocal (setLocal locsBase 0 (.ext (.mc (.cellNode h nw ne sw se))))
                  1 (.i32 x.toUInt32)) 2 (.i32 y.toUInt32)) 4 (.ext (.mc (.cellNode h nw ne sw se))))
                5 (.i32 0)) 3 (.i32 (Algorithm.MacroCell.cellNode h nw ne sw se).level))
                4 (.i32 w.toUInt32)) 5 (.i32 half.toUInt32))
                6 (.i32 (if decide (y < half) then 1 else 0)))
                7 (.i32 (if decide (x < half) then 1 else 0)))
                8 (.ext (.mc (.cellNode h nw ne sw se))), jh, hp⟩ := by
        intro R2
        mcc_drop
        rw [show f' + (R2 + 38) = (f' + (R2 + 37)) + 1 from by omega]; rw [runJvmResFast_instanceof_step (res := 0) rfl]
        rw [show f' + (R2 + 37) = (f' + (R2 + 36)) + 1 from by omega]
        rw [runJvmResFast_ifeq_branch (v := 0) rfl]; mcc_drop
        rw [show f' + (R2 + 36) = (f' + (R2 + 35)) + 1 from by omega]; heap_step_nonbranch_chunks; norm_add
        rw [show f' + (R2 + 34) + 1 = (f' + (R2 + 34)) + 1 from rfl]; rw [runJvmResFast_instanceof_step (res := 1) rfl]
        rw [show f' + (R2 + 34) = (f' + (R2 + 33)) + 1 from by omega]
        rw [runJvmResFast_ifeq_fallthrough (v := 1) (by decide)]
        rw [show f' + (R2 + 33) = (f' + (R2 + 32)) + 1 from by omega]; heap_step_nonbranch_chunks; norm_add
        rw [show f' + (R2 + 31) + 1 = f' + (R2 + 32) from by omega]
        conv => rhs; arg 4; dsimp only [f_Algorithm_macroCellContains_prog, List.drop]; rfl
      cases hN : decide (y < half) <;> cases hW : decide (x < half)
      · rcases ih_se (d - 1) (f' + 10) hse (by omega) (x - half) (y - half) _ jh hp with ⟨st', hrec⟩
        refine ⟨st', ?_⟩
        have hN' : (if decide (y < (1 : Int32) <<<
            ((Algorithm.MacroCell.cellNode h nw ne sw se).level.toInt32 - 1)) = true
            then (1 : UInt32) else 0) = 0 := by
          dsimp only [half] at hN; rw [hN]; rfl
        have hW' : (if decide (x < (1 : Int32) <<<
            ((Algorithm.MacroCell.cellNode h nw ne sw se).level.toInt32 - 1)) = true
            then (1 : UInt32) else 0) = 0 := by
          dsimp only [half] at hW; rw [hW]; rfl
        rw [hpre, hhead ((d - 1 + 1) * 80)]; mcc_drop
        rw [show f' + ((d - 1 + 1) * 80 + 32) = (f' + ((d - 1 + 1) * 80 + 31)) + 1 from by omega]
        rw [hN', runJvmResFast_ifne_fallthrough]
        rw [show f' + ((d - 1 + 1) * 80 + 31) = (f' + ((d - 1 + 1) * 80 + 30)) + 1 from by omega]
        heap_step_nonbranch_chunks; norm_add
        rw [hW', runJvmResFast_ifne_fallthrough]
        rw [show f' + ((d - 1 + 1) * 80 + 29) = (f' + ((d - 1 + 1) * 80 + 28)) + 1 from by omega]
        heap_step_nonbranch_chunks; norm_add
        rw [runJvmResFast_checkcast_step rfl]
        rw [show f' + ((d - 1 + 1) * 80 + 27) = (f' + ((d - 1 + 1) * 80 + 26)) + 1 from by omega]
        step_op step_cell_getSe
        rw [show f' + ((d - 1 + 1) * 80 + 26) = (f' + 10 + (d - 1 + 1) * 80 + 1) + 15 from by omega]
        heap_step_one_chunk; norm_add
        rw [runJvmResFast_goto]; mcc_drop
        exact hrec
      · rcases ih_sw (d - 1) (f' + 12) hsw (by omega) x (y - half) _ jh hp with ⟨st', hrec⟩
        refine ⟨st', ?_⟩
        have hN' : (if decide (y < (1 : Int32) <<<
            ((Algorithm.MacroCell.cellNode h nw ne sw se).level.toInt32 - 1)) = true
            then (1 : UInt32) else 0) = 0 := by
          dsimp only [half] at hN; rw [hN]; rfl
        have hW' : (if decide (x < (1 : Int32) <<<
            ((Algorithm.MacroCell.cellNode h nw ne sw se).level.toInt32 - 1)) = true
            then (1 : UInt32) else 0) = 1 := by
          dsimp only [half] at hW; rw [hW]; rfl
        rw [hpre, hhead ((d - 1 + 1) * 80)]; mcc_drop
        rw [show f' + ((d - 1 + 1) * 80 + 32) = (f' + ((d - 1 + 1) * 80 + 31)) + 1 from by omega]
        rw [hN', runJvmResFast_ifne_fallthrough]
        rw [show f' + ((d - 1 + 1) * 80 + 31) = (f' + ((d - 1 + 1) * 80 + 30)) + 1 from by omega]
        heap_step_nonbranch_chunks; norm_add
        rw [hW', runJvmResFast_ifne_branch (v := 1) (by decide)]; mcc_drop
        rw [show f' + ((d - 1 + 1) * 80 + 29) = (f' + ((d - 1 + 1) * 80 + 28)) + 1 from by omega]
        heap_step_nonbranch_chunks; norm_add
        rw [runJvmResFast_checkcast_step rfl]
        rw [show f' + ((d - 1 + 1) * 80 + 27) = (f' + ((d - 1 + 1) * 80 + 26)) + 1 from by omega]
        step_op step_cell_getSw
        rw [show f' + ((d - 1 + 1) * 80 + 26) = (f' + 12 + (d - 1 + 1) * 80 + 1) + 13 from by omega]
        heap_step_one_chunk; norm_add
        rw [runJvmResFast_goto]; mcc_drop
        exact hrec
      · rcases ih_ne (d - 1) (f' + 12) hne (by omega) (x - half) y _ jh hp with ⟨st', hrec⟩
        refine ⟨st', ?_⟩
        have hN' : (if decide (y < (1 : Int32) <<<
            ((Algorithm.MacroCell.cellNode h nw ne sw se).level.toInt32 - 1)) = true
            then (1 : UInt32) else 0) = 1 := by
          dsimp only [half] at hN; rw [hN]; rfl
        have hW' : (if decide (x < (1 : Int32) <<<
            ((Algorithm.MacroCell.cellNode h nw ne sw se).level.toInt32 - 1)) = true
            then (1 : UInt32) else 0) = 0 := by
          dsimp only [half] at hW; rw [hW]; rfl
        rw [hpre, hhead ((d - 1 + 1) * 80)]; mcc_drop
        rw [show f' + ((d - 1 + 1) * 80 + 32) = (f' + ((d - 1 + 1) * 80 + 31)) + 1 from by omega]
        rw [hN', runJvmResFast_ifne_branch (v := 1) (by decide)]; mcc_drop
        rw [show f' + ((d - 1 + 1) * 80 + 31) = (f' + ((d - 1 + 1) * 80 + 30)) + 1 from by omega]
        heap_step_nonbranch_chunks; norm_add
        rw [hW', runJvmResFast_ifne_fallthrough]
        rw [show f' + ((d - 1 + 1) * 80 + 29) = (f' + ((d - 1 + 1) * 80 + 28)) + 1 from by omega]
        heap_step_nonbranch_chunks; norm_add
        rw [runJvmResFast_checkcast_step rfl]
        rw [show f' + ((d - 1 + 1) * 80 + 27) = (f' + ((d - 1 + 1) * 80 + 26)) + 1 from by omega]
        step_op step_cell_getNe
        rw [show f' + ((d - 1 + 1) * 80 + 26) = (f' + 12 + (d - 1 + 1) * 80 + 1) + 13 from by omega]
        heap_step_one_chunk; norm_add
        rw [runJvmResFast_goto]; mcc_drop
        exact hrec
      · rcases ih_nw (d - 1) (f' + 14) hnw (by omega) x y _ jh hp with ⟨st', hrec⟩
        refine ⟨st', ?_⟩
        have hN' : (if decide (y < (1 : Int32) <<<
            ((Algorithm.MacroCell.cellNode h nw ne sw se).level.toInt32 - 1)) = true
            then (1 : UInt32) else 0) = 1 := by
          dsimp only [half] at hN; rw [hN]; rfl
        have hW' : (if decide (x < (1 : Int32) <<<
            ((Algorithm.MacroCell.cellNode h nw ne sw se).level.toInt32 - 1)) = true
            then (1 : UInt32) else 0) = 1 := by
          dsimp only [half] at hW; rw [hW]; rfl
        rw [hpre, hhead ((d - 1 + 1) * 80)]; mcc_drop
        rw [show f' + ((d - 1 + 1) * 80 + 32) = (f' + ((d - 1 + 1) * 80 + 31)) + 1 from by omega]
        rw [hN', runJvmResFast_ifne_branch (v := 1) (by decide)]; mcc_drop
        rw [show f' + ((d - 1 + 1) * 80 + 31) = (f' + ((d - 1 + 1) * 80 + 30)) + 1 from by omega]
        heap_step_nonbranch_chunks; norm_add
        rw [hW', runJvmResFast_ifne_branch (v := 1) (by decide)]; mcc_drop
        rw [show f' + ((d - 1 + 1) * 80 + 29) = (f' + ((d - 1 + 1) * 80 + 28)) + 1 from by omega]
        heap_step_nonbranch_chunks; norm_add
        rw [runJvmResFast_checkcast_step rfl]
        rw [show f' + ((d - 1 + 1) * 80 + 27) = (f' + ((d - 1 + 1) * 80 + 26)) + 1 from by omega]
        step_op step_cell_getNw
        rw [show f' + ((d - 1 + 1) * 80 + 26) = (f' + 14 + (d - 1 + 1) * 80 + 1) + 11 from by omega]
        heap_step_one_chunk; norm_add
        rw [runJvmResFast_goto]; mcc_drop
        exact hrec

theorem macroCellContains_equiv (m : Algorithm.MacroCell) (d : Nat) (hm : Algorithm.WFd m d)
    (hd : d < 32) (x y : Int32) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    runJvm ((d + 1) * 80 + 10) f_Algorithm_macroCellContains_prog
      ⟨0, [], setLocal (setLocal (setLocal (fun _ => .null) 0 (.ext (.mc m)))
        1 (.i32 x.toUInt32)) 2 (.i32 y.toUInt32), jh, hp⟩ =
      some (.i32 (if Algorithm.macroCellContains m x y then 1 else 0)) := by
  suffices hfast : ∃ st', runJvmResFast ((d + 1) * 80 + 10) f_Algorithm_macroCellContains_prog 0
      f_Algorithm_macroCellContains_prog
      ⟨0, [], setLocal (setLocal (setLocal (fun _ => .null) 0 (.ext (.mc m)))
        1 (.i32 x.toUInt32)) 2 (.i32 y.toUInt32), jh, hp⟩ =
      some (.i32 (if Algorithm.macroCellContains m x y then 1 else 0), st') from
    let ⟨st', hs⟩ := hfast
    runJvm_eq_of_runJvmRes (runJvmRes_of_runJvmResFast0 ((d + 1) * 80 + 10) _ _ _ rfl hs)
  rcases macroCellContains_loop m d 7 hm hd x y (fun _ => .null) jh hp with
    ⟨st', hloop⟩
  refine ⟨st', ?_⟩
  rw [show (d + 1) * 80 + 10 = (7 + (d + 1) * 80 + 1) + 2 from by omega]
  conv => lhs; arg 4; dsimp only [f_Algorithm_macroCellContains_prog]
  heap_step_one_chunk; norm_add
  step_op (stepStatic_checkNotNullParameter_hp rfl)
  dsimp only [f_Algorithm_macroCellContains_prog, List.drop] at hloop
  exact hloop

/-! ### macroCellWithCell -/

local macro "mcw_drop" : tactic => `(tactic| (
  conv => lhs; arg 4; dsimp only [f_Algorithm_macroCellWithCell_prog, List.drop]))

local macro "mcw_norm" : tactic => `(tactic| (
  norm_res_fuel;
  (try (conv => lhs; arg 1; rw [Nat.add_sub_assoc (by decide)]; simp only [Nat.reduceSub]));
  (try (conv => lhs; arg 1; simp only [Nat.add_zero]))))

local macro "mcw_l4_tail" : tactic => `(tactic| (
  split_res_fuel 1; rw [runJvmResFast_checkcast_step rfl]; mcw_norm;
  step_op step_l4_getNw; heap_step_nonbranch_chunks; mcw_norm;
  split_res_fuel 1; rw [runJvmResFast_checkcast_step rfl]; mcw_norm;
  step_op step_l4_getNe; heap_step_nonbranch_chunks; mcw_norm;
  split_res_fuel 1; rw [runJvmResFast_checkcast_step rfl]; mcw_norm;
  step_op step_l4_getSw; heap_step_nonbranch_chunks; mcw_norm;
  split_res_fuel 1; rw [runJvmResFast_checkcast_step rfl]; mcw_norm;
  step_op step_l4_getSe; heap_step_nonbranch_chunks; mcw_norm;
  step_op step_leafWithCell; heap_step_nonbranch_chunks))

local macro "mcw_cell_tail" : tactic => `(tactic| (
  split_res_fuel 1; rw [runJvmResFast_checkcast_step rfl]; mcw_norm;
  step_op step_cell_getNw; heap_step_nonbranch_chunks; mcw_norm;
  split_res_fuel 1; rw [runJvmResFast_checkcast_step rfl]; mcw_norm;
  step_op step_cell_getNe; heap_step_nonbranch_chunks; mcw_norm;
  split_res_fuel 1; rw [runJvmResFast_checkcast_step rfl]; mcw_norm;
  step_op step_cell_getSw; heap_step_nonbranch_chunks; mcw_norm;
  split_res_fuel 1; rw [runJvmResFast_checkcast_step rfl]; mcw_norm;
  step_op step_cell_getSe; heap_step_nonbranch_chunks; mcw_norm;
  step_op step_macroCellWithCell; heap_step_nonbranch_chunks))

private theorem step_withCell_N_pc39
    (k R2 : Nat) (x y half : Int32)
    (locsMid : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hloc1 : locsMid 1 = .i32 x.toUInt32)
    (hloc6 : locsMid 6 = .i32 half.toUInt32) :
    ∃ k', k ≤ k' ∧
      runJvmResFast (k + (R2 + 7)) f_Algorithm_macroCellWithCell_prog 32
        (f_Algorithm_macroCellWithCell_prog.drop 32)
        ⟨32, [.i32 half.toUInt32, .i32 y.toUInt32], locsMid, jh, hp⟩ =
      runJvmResFast (k' + (R2 + 1)) f_Algorithm_macroCellWithCell_prog 39
        (f_Algorithm_macroCellWithCell_prog.drop 39)
        ⟨39, [.i32 half.toUInt32, .i32 x.toUInt32],
          setLocal locsMid 7 (.i32 (if decide (y < half) then 1 else 0)), jh, hp⟩ := by
  by_cases hN : y < half
  · have hNsle : half.toUInt32.toBitVec.sle y.toUInt32.toBitVec = false :=
      (int32_lt_iff_sle_false y half).mp hN
    have hNd : decide (y < half) = true := decide_eq_true hN
    refine ⟨k + 0, by omega, ?_⟩
    rw [show k + (R2 + 7) = (k + R2 + 6) + 1 from by omega]
    mcw_drop; rw [runJvmResFast_if_icmpge_fallthrough hNsle]
    rw [show (32 : Nat) + 1 = 33 from rfl]
    rw [show k + R2 + 6 = (k + R2 + 5) + 1 from by omega]; step1
    rw [show k + R2 + 5 = (k + R2 + 4) + 1 from by omega]
    rw [runJvmResFast_goto]; mcw_drop
    rw [show k + R2 + 4 = (k + R2 + 1) + 3 from by omega]
    step1; step1; step1
    rw [show k + R2 + 1 = k + 0 + (R2 + 1) from by omega]
    conv => rhs; arg 4; dsimp only [f_Algorithm_macroCellWithCell_prog, List.drop]
    conv => lhs; arg 5; simp only [hloc1, hloc6]
    conv => rhs; arg 5; simp only [hNd, ↓reduceIte]
  · have hNsle : half.toUInt32.toBitVec.sle y.toUInt32.toBitVec = true :=
      (int32_ge_iff_sle y half).mp hN
    have hNd : decide (y < half) = false := decide_eq_false hN
    refine ⟨k + 1, by omega, ?_⟩
    rw [show k + (R2 + 7) = (k + R2 + 6) + 1 from by omega]
    mcw_drop; rw [runJvmResFast_if_icmpge_branch hNsle]; mcw_drop
    rw [show k + R2 + 6 = (k + 1 + R2 + 1) + 4 from by omega]
    step1; step1; step1; step1
    rw [show k + 1 + R2 + 1 = k + 1 + (R2 + 1) from by omega]
    conv => rhs; arg 4; dsimp only [f_Algorithm_macroCellWithCell_prog, List.drop]
    conv => lhs; arg 5; simp only [hloc1, hloc6]
    conv => rhs; arg 5; simp only [hNd, Bool.false_eq_true, ↓reduceIte]

private theorem step_withCell_W_pc47
    (k R2 : Nat) (m : Algorithm.MacroCell) (x y half : Int32)
    (locsMid : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hloc0 : locsMid 0 = .ext (.mc m)) :
    let locs1 := setLocal (setLocal locsMid 7 (.i32 (if decide (y < half) then 1 else 0)))
      8 (.i32 (if decide (x < half) then 1 else 0))
    ∃ k', k ≤ k' ∧
      runJvmResFast (k + (R2 + 8)) f_Algorithm_macroCellWithCell_prog 39
        (f_Algorithm_macroCellWithCell_prog.drop 39)
        ⟨39, [.i32 half.toUInt32, .i32 x.toUInt32],
          setLocal locsMid 7 (.i32 (if decide (y < half) then 1 else 0)), jh, hp⟩ =
      runJvmResFast (k' + (R2 + 1)) f_Algorithm_macroCellWithCell_prog 47
        (f_Algorithm_macroCellWithCell_prog.drop 47)
        ⟨47, [.ext (.mc m)], setLocal locs1 9 (.ext (.mc m)), jh, hp⟩ := by
  intro locs1
  by_cases hW : x < half
  · have hWsle : half.toUInt32.toBitVec.sle x.toUInt32.toBitVec = false :=
      (int32_lt_iff_sle_false x half).mp hW
    have hWd : decide (x < half) = true := decide_eq_true hW
    refine ⟨k + 0, by omega, ?_⟩
    mcw_drop
    rw [show k + (R2 + 8) = (k + R2 + 7) + 1 from by omega]
    rw [runJvmResFast_if_icmpge_fallthrough hWsle]
    rw [show (39 : Nat) + 1 = 40 from rfl]
    rw [show k + R2 + 7 = (k + R2 + 6) + 1 from by omega]; step1
    rw [show k + R2 + 6 = (k + R2 + 5) + 1 from by omega]
    rw [runJvmResFast_goto]; mcw_drop
    rw [show k + R2 + 5 = (k + R2 + 1) + 4 from by omega]
    step1; step1; step1; step1
    rw [show k + R2 + 1 = k + 0 + (R2 + 1) from by omega]
    conv => rhs; arg 4; dsimp only [f_Algorithm_macroCellWithCell_prog, List.drop]
    conv => lhs; arg 5; simp only [hloc0]
    dsimp only [locs1]
    conv => rhs; arg 5; simp only [hWd, ↓reduceIte]
  · have hWsle : half.toUInt32.toBitVec.sle x.toUInt32.toBitVec = true :=
      (int32_ge_iff_sle x half).mp hW
    have hWd : decide (x < half) = false := decide_eq_false hW
    refine ⟨k + 1, by omega, ?_⟩
    mcw_drop
    rw [show k + (R2 + 8) = (k + R2 + 7) + 1 from by omega]
    rw [runJvmResFast_if_icmpge_branch hWsle]; mcw_drop
    rw [show k + R2 + 7 = (k + 1 + R2 + 1) + 5 from by omega]
    step1; step1; step1; step1; step1
    rw [show k + 1 + R2 + 1 = k + 1 + (R2 + 1) from by omega]
    conv => rhs; arg 4; dsimp only [f_Algorithm_macroCellWithCell_prog, List.drop]
    conv => lhs; arg 5; simp only [hloc0]
    dsimp only [locs1]
    conv => rhs; arg 5; simp only [hWd, Bool.false_eq_true, ↓reduceIte]

private theorem step_withCell_in_bounds_pc32
    (f R : Nat) {m : Algorithm.MacroCell}
    (hm1 : 1 ≤ m.level.toNat) (hm32 : m.level.toNat < 32)
    (x y : Int32) (isAlive : Bool) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hx0 : ¬(x < 0)) (hy0 : ¬(y < 0))
    (hxw : x < (1 : Int32) <<< m.level.toInt32) (hyw : y < (1 : Int32) <<< m.level.toInt32) :
    let w : Int32 := (1 : Int32) <<< m.level.toInt32
    let half : Int32 := (1 : Int32) <<< (m.level.toInt32 - 1)
    let locs0 := setLocal (setLocal (setLocal (setLocal (fun _ => .null) 0 (.ext (.mc m)))
      1 (.i32 x.toUInt32)) 2 (.i32 y.toUInt32)) 3 (.i32 (if isAlive then 1 else 0))
    let locsMid := setLocal (setLocal (setLocal (setLocal (setLocal locs0
      5 (.ext (.mc m))) 6 (.i32 0)) 4 (.i32 m.level)) 5 (.i32 w.toUInt32)) 6 (.i32 half.toUInt32)
    runJvmResFast (f + (R + 46)) f_Algorithm_macroCellWithCell_prog 0 f_Algorithm_macroCellWithCell_prog
        ⟨0, [], locs0, jh, hp⟩ =
      runJvmResFast (f + (R + 14)) f_Algorithm_macroCellWithCell_prog 32
        (f_Algorithm_macroCellWithCell_prog.drop 32)
        ⟨32, [.i32 half.toUInt32, .i32 y.toUInt32], locsMid, jh, hp⟩ := by
  intro w half locs0 locsMid
  have hm1_32 : (m.level - 1).toNat < 32 := by
    have hle1 : (1 : UInt32) ≤ m.level := by
      rw [UInt32.le_iff_toNat_le, UInt32.toNat_ofNat_of_lt (by decide)]; exact hm1
    rw [UInt32.toNat_sub_of_le m.level 1 hle1]; omega
  have hw_eq : w.toUInt32 = (1 : UInt32) <<< (m.level &&& 31) := ishl_u32_eq hm32
  have hhalf_eq : half.toUInt32 = (1 : UInt32) <<< ((m.level - 1) &&& 31) := by
    change ((1 : Int32) <<< (m.level.toInt32 - 1)).toUInt32 = _
    rw [ui32_toInt32_sub1 hm32]
    exact ishl_u32_eq hm1_32
  have hx0' : x.toUInt32.toBitVec.slt 0#32 = false := int32_not_lt_zero_slt hx0
  have hy0' : y.toUInt32.toBitVec.slt 0#32 = false := int32_not_lt_zero_slt hy0
  have hxw' : w.toUInt32.toBitVec.sle x.toUInt32.toBitVec = false := (int32_lt_iff_sle_false x w).mp hxw
  have hyw' : w.toUInt32.toBitVec.sle y.toUInt32.toBitVec = false := (int32_lt_iff_sle_false y w).mp hyw
  rw [show f + (R + 46) = (f + R + 42) + 4 from by omega]
  conv => lhs; arg 4; dsimp only [f_Algorithm_macroCellWithCell_prog]
  heap_step_nonbranch_chunks; norm_add
  rw [show f + R + 42 = (f + R + 41) + 1 from by omega]
  rw [runJvmResFast_iflt_fallthrough hx0', show (4 : Nat) + 1 = 5 from rfl]
  rw [show f + R + 41 = (f + R + 40) + 1 from by omega]
  step1; norm_add
  rw [show f + R + 40 = (f + R + 39) + 1 from by omega]
  rw [runJvmResFast_iflt_fallthrough hy0', show (6 : Nat) + 1 = 7 from rfl]
  rw [show f + R + 39 = (f + R + 34) + 5 from by omega]
  step1; step1; step1; step1; step1; norm_add
  rw [show f + R + 34 = (f + R + 33) + 1 from by omega]
  step_op step_mcLevel
  conv => lhs; arg 1; rw [Nat.add_sub_cancel]
  rw [show (12 : Nat) + 1 = 13 from rfl]
  rw [show f + R + 33 = (f + R + 26) + 7 from by omega]
  step1; step1; step1; step1; step1; step1; step1; norm_add
  rw [← hw_eq, show f + R + 26 = (f + R + 25) + 1 from by omega]
  rw [runJvmResFast_if_icmple_fallthrough hxw', show (20 : Nat) + 1 = 21 from rfl]
  rw [show f + R + 25 = (f + R + 23) + 2 from by omega]
  step1; step1; norm_add
  rw [show f + R + 23 = (f + R + 22) + 1 from by omega]
  rw [runJvmResFast_if_icmple_fallthrough hyw', show (23 : Nat) + 1 = 24 from rfl]
  rw [show f + R + 22 = (f + R + 14) + 8 from by omega]
  step1; step1; step1; step1; step1; step1; step1; step1; norm_add
  rw [← hhalf_eq, show f + R + 14 = f + (R + 14) from by omega]
  conv => rhs; arg 4; dsimp only [f_Algorithm_macroCellWithCell_prog, List.drop]

private theorem step_withCell_in_bounds_pc47
    (f R : Nat) {m : Algorithm.MacroCell}
    (hm1 : 1 ≤ m.level.toNat) (hm32 : m.level.toNat < 32)
    (x y : Int32) (isAlive : Bool) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hx0 : ¬(x < 0)) (hy0 : ¬(y < 0))
    (hxw : x < (1 : Int32) <<< m.level.toInt32) (hyw : y < (1 : Int32) <<< m.level.toInt32) :
    let w : Int32 := (1 : Int32) <<< m.level.toInt32
    let half : Int32 := (1 : Int32) <<< (m.level.toInt32 - 1)
    let isNorth : Bool := decide (y < half)
    let isWest : Bool := decide (x < half)
    let locs0 := setLocal (setLocal (setLocal (setLocal (fun _ => .null) 0 (.ext (.mc m)))
      1 (.i32 x.toUInt32)) 2 (.i32 y.toUInt32)) 3 (.i32 (if isAlive then 1 else 0))
    let locs1 := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal locs0
      5 (.ext (.mc m))) 6 (.i32 0)) 4 (.i32 m.level)) 5 (.i32 w.toUInt32))
      6 (.i32 half.toUInt32)) 7 (.i32 (if isNorth then 1 else 0))) 8 (.i32 (if isWest then 1 else 0))
    ∃ f', f ≤ f' ∧
      runJvmResFast (f + (R + 46)) f_Algorithm_macroCellWithCell_prog 0 f_Algorithm_macroCellWithCell_prog
        ⟨0, [], locs0, jh, hp⟩ =
      runJvmResFast (f' + (R + 1)) f_Algorithm_macroCellWithCell_prog 47
        (f_Algorithm_macroCellWithCell_prog.drop 47)
        ⟨47, [.ext (.mc m)], setLocal locs1 9 (.ext (.mc m)), jh, hp⟩ := by
  intro w half isNorth isWest locs0 locs1
  let locsMid := setLocal (setLocal (setLocal (setLocal (setLocal locs0
    5 (.ext (.mc m))) 6 (.i32 0)) 4 (.i32 m.level)) 5 (.i32 w.toUInt32)) 6 (.i32 half.toUInt32)
  have h0 := step_withCell_in_bounds_pc32 f R hm1 hm32 x y isAlive jh hp hx0 hy0 hxw hyw
  rcases step_withCell_N_pc39 f (R + 7) x y half locsMid jh hp rfl rfl with ⟨k1, hk1, hNrw⟩
  rcases step_withCell_W_pc47 k1 R m x y half locsMid jh hp rfl with ⟨k2, hk2, hWrw⟩
  refine ⟨k2, by omega, ?_⟩
  rw [h0, show f + (R + 14) = f + ((R + 7) + 7) from by omega]
  exact hNrw.trans hWrw

theorem macroCellWithCell_equiv (m : Algorithm.MacroCell)
    (hm1 : 1 ≤ m.level.toNat) (hm32 : m.level.toNat < 32)
    (x y : Int32) (isAlive : Bool) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    runJvm 100 f_Algorithm_macroCellWithCell_prog
      ⟨0, [], setLocal (setLocal (setLocal (setLocal (fun _ => .null)
        0 (.ext (.mc m))) 1 (.i32 x.toUInt32)) 2 (.i32 y.toUInt32))
        3 (.i32 (if isAlive then 1 else 0)), jh, hp⟩ =
      some (.ext (.mc (Algorithm.macroCellWithCell m x y isAlive))) := by
  suffices hfast : ∃ st', runJvmResFast 100 f_Algorithm_macroCellWithCell_prog 0
      f_Algorithm_macroCellWithCell_prog
      ⟨0, [], setLocal (setLocal (setLocal (setLocal (fun _ => .null)
        0 (.ext (.mc m))) 1 (.i32 x.toUInt32)) 2 (.i32 y.toUInt32))
        3 (.i32 (if isAlive then 1 else 0)), jh, hp⟩ =
      some (.ext (.mc (Algorithm.macroCellWithCell m x y isAlive)), st') from
    let ⟨st', hs⟩ := hfast
    runJvm_eq_of_runJvmRes (runJvmRes_of_runJvmResFast0 100 _ _ _ rfl hs)
  have hw_eq : ((1 : Int32) <<< m.level.toInt32).toUInt32 = (1 : UInt32) <<< (m.level &&& 31) :=
    ishl_u32_eq hm32
  let w : Int32 := (1 : Int32) <<< m.level.toInt32
  by_cases hx0 : x < 0
  · have hx0' : x.toUInt32.toBitVec.slt 0#32 = true := hx0
    apply Exists.intro
    conv => lhs; arg 4; dsimp only [f_Algorithm_macroCellWithCell_prog]
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_iflt_branch hx0']; mcw_drop; norm_res_fuel
    heap_step_nonbranch_chunks
    rw [Algorithm.macroCellWithCell]; simp only [hx0]; rfl
  · by_cases hy0 : y < 0
    · have hx0' : x.toUInt32.toBitVec.slt 0#32 = false := int32_not_lt_zero_slt hx0
      have hy0' : y.toUInt32.toBitVec.slt 0#32 = true := hy0
      apply Exists.intro
      conv => lhs; arg 4; dsimp only [f_Algorithm_macroCellWithCell_prog]
      heap_step_nonbranch_chunks; norm_res_fuel
      rw [runJvmResFast_iflt_fallthrough hx0']; norm_res_fuel
      heap_step_nonbranch_chunks; norm_res_fuel
      rw [runJvmResFast_iflt_branch hy0']; mcw_drop; norm_res_fuel
      heap_step_nonbranch_chunks
      rw [Algorithm.macroCellWithCell]; simp only [hx0, hy0]; rfl
    · by_cases hxw : ¬(x < w)
      · have hx0' : x.toUInt32.toBitVec.slt 0#32 = false := int32_not_lt_zero_slt hx0
        have hy0' : y.toUInt32.toBitVec.slt 0#32 = false := int32_not_lt_zero_slt hy0
        have hxw' : w.toUInt32.toBitVec.sle x.toUInt32.toBitVec = true := (int32_ge_iff_sle x w).mp hxw
        apply Exists.intro
        conv => lhs; arg 4; dsimp only [f_Algorithm_macroCellWithCell_prog]
        heap_step_nonbranch_chunks; norm_res_fuel
        rw [runJvmResFast_iflt_fallthrough hx0']; norm_res_fuel
        heap_step_nonbranch_chunks; norm_res_fuel
        rw [runJvmResFast_iflt_fallthrough hy0']; norm_res_fuel
        heap_step_nonbranch_chunks; norm_res_fuel
        step_op step_mcLevel
        heap_step_nonbranch_chunks; norm_res_fuel
        rw [← hw_eq]
        rw [runJvmResFast_if_icmple_branch hxw']; mcw_drop; norm_res_fuel
        heap_step_nonbranch_chunks
        have hxw_d : decide (x ≥ (1 : Int32) <<< m.level.toInt32) = true := int32_decide_ge_true hxw
        rw [Algorithm.macroCellWithCell]
        simp only [hxw_d, Bool.or_true, Bool.true_or, ↓reduceIte]; rfl
      · by_cases hyw : ¬(y < w)
        · have hx0' : x.toUInt32.toBitVec.slt 0#32 = false := int32_not_lt_zero_slt hx0
          have hy0' : y.toUInt32.toBitVec.slt 0#32 = false := int32_not_lt_zero_slt hy0
          have hxw' : w.toUInt32.toBitVec.sle x.toUInt32.toBitVec = false :=
            (int32_lt_iff_sle_false x w).mp (Classical.not_not.mp hxw)
          have hyw' : w.toUInt32.toBitVec.sle y.toUInt32.toBitVec = true := (int32_ge_iff_sle y w).mp hyw
          apply Exists.intro
          conv => lhs; arg 4; dsimp only [f_Algorithm_macroCellWithCell_prog]
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_iflt_fallthrough hx0']; norm_res_fuel
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_iflt_fallthrough hy0']; norm_res_fuel
          heap_step_nonbranch_chunks; norm_res_fuel
          step_op step_mcLevel
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [← hw_eq]
          rw [runJvmResFast_if_icmple_fallthrough hxw']; norm_res_fuel
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_if_icmple_branch hyw']; mcw_drop; norm_res_fuel
          heap_step_nonbranch_chunks
          have hyw_d : decide (y ≥ (1 : Int32) <<< m.level.toInt32) = true := int32_decide_ge_true hyw
          rw [Algorithm.macroCellWithCell]
          simp only [hyw_d, Bool.or_true, ↓reduceIte]; rfl
        · have hxw_lt : x < w := Classical.not_not.mp hxw
          have hyw_lt : y < w := Classical.not_not.mp hyw
          rcases step_withCell_in_bounds_pc47 0 54 hm1 hm32 x y isAlive jh hp hx0 hy0 hxw_lt hyw_lt with
            ⟨f', _, hpre⟩
          let half : Int32 := (1 : Int32) <<< (m.level.toInt32 - 1)
          have hfxw : decide (x ≥ (1 : Int32) <<< m.level.toInt32) = false := int32_decide_ge_false hxw_lt
          have hfyw : decide (y ≥ (1 : Int32) <<< m.level.toInt32) = false := int32_decide_ge_false hyw_lt
          cases m with
          | level4Node h nw ne sw se =>
            let locs47 : Nat → JvmVal := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
              (setLocal (setLocal (setLocal (setLocal (fun _ => .null)
                0 (.ext (.mc (.level4Node h nw ne sw se))))
                1 (.i32 x.toUInt32)) 2 (.i32 y.toUInt32)) 3 (.i32 (if isAlive then 1 else 0)))
              5 (.ext (.mc (.level4Node h nw ne sw se)))) 6 (.i32 0))
              4 (.i32 (Algorithm.MacroCell.level4Node h nw ne sw se).level))
              5 (.i32 w.toUInt32)) 6 (.i32 half.toUInt32))
              7 (.i32 (if decide (y < half) then 1 else 0))
            let locs47' : Nat → JvmVal := setLocal (setLocal locs47
              8 (.i32 (if decide (x < half) then 1 else 0)))
              9 (.ext (.mc (.level4Node h nw ne sw se)))
            have hhead :
                runJvmResFast (f' + (54 + 1)) f_Algorithm_macroCellWithCell_prog 47
                  (f_Algorithm_macroCellWithCell_prog.drop 47)
                  ⟨47, [.ext (.mc (.level4Node h nw ne sw se))], locs47', jh, hp⟩ =
                runJvmResFast (f' + 52) f_Algorithm_macroCellWithCell_prog 50
                  (f_Algorithm_macroCellWithCell_prog.drop 50)
                  ⟨50, [.i32 (if decide (y < half) then 1 else 0)], locs47', jh, hp⟩ := by
              mcw_drop; split_res_fuel 1
              rw [runJvmResFast_instanceof_step (res := 1) rfl, show (47 : Nat) + 1 = 48 from rfl]; mcw_norm
              split_res_fuel 1
              rw [runJvmResFast_ifeq_fallthrough (v := 1) (by decide), show (48 : Nat) + 1 = 49 from rfl]; mcw_norm
              heap_step_nonbranch_chunks; mcw_norm
              conv => lhs; arg 5; dsimp only
              conv => rhs; arg 4; dsimp only [f_Algorithm_macroCellWithCell_prog, List.drop]; rfl
            rw [show (100 : Nat) = 0 + (54 + 46) from by decide, hpre, hhead]
            dsimp only [locs47', locs47]
            cases hN : decide (y < half) <;> cases hW : decide (x < half)
            · apply Exists.intro
              mcw_drop
              rw [show (if false = true then (1 : UInt32) else 0) = 0 from rfl]; split_res_fuel 1
              rw [runJvmResFast_ifne_fallthrough, show (50 : Nat) + 1 = 51 from rfl]; mcw_norm
              heap_step_nonbranch_chunks; mcw_norm
              conv => lhs; arg 5; dsimp only
              split_res_fuel 1
              rw [runJvmResFast_ifne_fallthrough, show (52 : Nat) + 1 = 53 from rfl]; mcw_norm
              heap_step_nonbranch_chunks; mcw_norm
              mcw_l4_tail
              conv => rhs; rw [Algorithm.macroCellWithCell]
              simp only [hx0, hy0, hfxw, hfyw, half, hN, hW,
                int32_sub_toUInt32, decide_false, Bool.false_or]; rfl
            · apply Exists.intro
              mcw_drop
              rw [show (if false = true then (1 : UInt32) else 0) = 0 from rfl]; split_res_fuel 1
              rw [runJvmResFast_ifne_fallthrough, show (50 : Nat) + 1 = 51 from rfl]; mcw_norm
              heap_step_nonbranch_chunks; mcw_norm
              conv => lhs; arg 5; dsimp only
              rw [show (if true = true then (1 : UInt32) else 0) = 1 from rfl]; split_res_fuel 1
              rw [runJvmResFast_ifne_branch (v := 1) (by decide)]; mcw_drop; mcw_norm
              heap_step_nonbranch_chunks; mcw_norm
              mcw_l4_tail
              conv => rhs; rw [Algorithm.macroCellWithCell]
              simp only [hx0, hy0, hfxw, hfyw, half, hN, hW,
                int32_sub_toUInt32, decide_false, Bool.false_or]; rfl
            · apply Exists.intro
              mcw_drop
              rw [show (if true = true then (1 : UInt32) else 0) = 1 from rfl]; split_res_fuel 1
              rw [runJvmResFast_ifne_branch (v := 1) (by decide)]; mcw_drop; mcw_norm
              heap_step_nonbranch_chunks; mcw_norm
              conv => lhs; arg 5; dsimp only
              rw [show (if false = true then (1 : UInt32) else 0) = 0 from rfl]; split_res_fuel 1
              rw [runJvmResFast_ifne_fallthrough, show (120 : Nat) + 1 = 121 from rfl]; mcw_norm
              heap_step_nonbranch_chunks; mcw_norm
              mcw_l4_tail
              conv => rhs; rw [Algorithm.macroCellWithCell]
              simp only [hx0, hy0, hfxw, hfyw, half, hN, hW,
                int32_sub_toUInt32, decide_false, Bool.false_or]; rfl
            · apply Exists.intro
              mcw_drop
              rw [show (if true = true then (1 : UInt32) else 0) = 1 from rfl]; split_res_fuel 1
              rw [runJvmResFast_ifne_branch (v := 1) (by decide)]; mcw_drop; mcw_norm
              heap_step_nonbranch_chunks; mcw_norm
              conv => lhs; arg 5; dsimp only
              split_res_fuel 1
              rw [runJvmResFast_ifne_branch (v := 1) (by decide)]; mcw_drop; mcw_norm
              heap_step_nonbranch_chunks; mcw_norm
              mcw_l4_tail
              conv => rhs; rw [Algorithm.macroCellWithCell]
              simp only [hx0, hy0, hfxw, hfyw, half, hN, hW,
                decide_false, Bool.false_or]; rfl
          | cellNode h nw ne sw se =>
            let locs47 : Nat → JvmVal := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
              (setLocal (setLocal (setLocal (setLocal (fun _ => .null)
                0 (.ext (.mc (.cellNode h nw ne sw se))))
                1 (.i32 x.toUInt32)) 2 (.i32 y.toUInt32)) 3 (.i32 (if isAlive then 1 else 0)))
              5 (.ext (.mc (.cellNode h nw ne sw se)))) 6 (.i32 0))
              4 (.i32 (Algorithm.MacroCell.cellNode h nw ne sw se).level))
              5 (.i32 w.toUInt32)) 6 (.i32 half.toUInt32))
              7 (.i32 (if decide (y < half) then 1 else 0))
            let locs47' : Nat → JvmVal := setLocal (setLocal locs47
              8 (.i32 (if decide (x < half) then 1 else 0)))
              9 (.ext (.mc (.cellNode h nw ne sw se)))
            have hhead :
                runJvmResFast (f' + (54 + 1)) f_Algorithm_macroCellWithCell_prog 47
                  (f_Algorithm_macroCellWithCell_prog.drop 47)
                  ⟨47, [.ext (.mc (.cellNode h nw ne sw se))], locs47', jh, hp⟩ =
                runJvmResFast (f' + 49) f_Algorithm_macroCellWithCell_prog 187
                  (f_Algorithm_macroCellWithCell_prog.drop 187)
                  ⟨187, [.i32 (if decide (y < half) then 1 else 0)], locs47', jh, hp⟩ := by
              mcw_drop; split_res_fuel 1
              rw [runJvmResFast_instanceof_step (res := 0) rfl, show (47 : Nat) + 1 = 48 from rfl]; mcw_norm
              split_res_fuel 1
              rw [runJvmResFast_ifeq_branch (v := 0) rfl]; mcw_drop; mcw_norm
              heap_step_nonbranch_chunks; mcw_norm
              split_res_fuel 1
              rw [runJvmResFast_instanceof_step (res := 1) rfl, show (184 : Nat) + 1 = 185 from rfl]; mcw_norm
              split_res_fuel 1
              rw [runJvmResFast_ifeq_fallthrough (v := 1) (by decide), show (185 : Nat) + 1 = 186 from rfl]; mcw_norm
              heap_step_nonbranch_chunks; mcw_norm
              conv => lhs; arg 5; dsimp only
              conv => rhs; arg 4; dsimp only [f_Algorithm_macroCellWithCell_prog, List.drop]; rfl
            rw [show (100 : Nat) = 0 + (54 + 46) from by decide, hpre, hhead]
            dsimp only [locs47', locs47]
            cases hN : decide (y < half) <;> cases hW : decide (x < half)
            · apply Exists.intro
              mcw_drop
              rw [show (if false = true then (1 : UInt32) else 0) = 0 from rfl]; split_res_fuel 1
              rw [runJvmResFast_ifne_fallthrough, show (187 : Nat) + 1 = 188 from rfl]; mcw_norm
              heap_step_nonbranch_chunks; mcw_norm
              conv => lhs; arg 5; dsimp only
              split_res_fuel 1
              rw [runJvmResFast_ifne_fallthrough, show (189 : Nat) + 1 = 190 from rfl]; mcw_norm
              heap_step_nonbranch_chunks; mcw_norm
              mcw_cell_tail
              conv => rhs; rw [Algorithm.macroCellWithCell]
              simp only [hx0, hy0, hfxw, hfyw, half, hN, hW,
                decide_false, Bool.false_or]; rfl
            · apply Exists.intro
              mcw_drop
              rw [show (if false = true then (1 : UInt32) else 0) = 0 from rfl]; split_res_fuel 1
              rw [runJvmResFast_ifne_fallthrough, show (187 : Nat) + 1 = 188 from rfl]; mcw_norm
              heap_step_nonbranch_chunks; mcw_norm
              conv => lhs; arg 5; dsimp only
              rw [show (if true = true then (1 : UInt32) else 0) = 1 from rfl]; split_res_fuel 1
              rw [runJvmResFast_ifne_branch (v := 1) (by decide)]; mcw_drop; mcw_norm
              heap_step_nonbranch_chunks; mcw_norm
              mcw_cell_tail
              conv => rhs; rw [Algorithm.macroCellWithCell]
              simp only [hx0, hy0, hfxw, hfyw, half, hN, hW,
                decide_false, Bool.false_or]; rfl
            · apply Exists.intro
              mcw_drop
              rw [show (if true = true then (1 : UInt32) else 0) = 1 from rfl]; split_res_fuel 1
              rw [runJvmResFast_ifne_branch (v := 1) (by decide)]; mcw_drop; mcw_norm
              heap_step_nonbranch_chunks; mcw_norm
              conv => lhs; arg 5; dsimp only
              rw [show (if false = true then (1 : UInt32) else 0) = 0 from rfl]; split_res_fuel 1
              rw [runJvmResFast_ifne_fallthrough, show (253 : Nat) + 1 = 254 from rfl]; mcw_norm
              heap_step_nonbranch_chunks; mcw_norm
              mcw_cell_tail
              conv => rhs; rw [Algorithm.macroCellWithCell]
              simp only [hx0, hy0, hfxw, hfyw, half, hN, hW,
                decide_false, Bool.false_or]; rfl
            · apply Exists.intro
              mcw_drop
              rw [show (if true = true then (1 : UInt32) else 0) = 1 from rfl]; split_res_fuel 1
              rw [runJvmResFast_ifne_branch (v := 1) (by decide)]; mcw_drop; mcw_norm
              heap_step_nonbranch_chunks; mcw_norm
              conv => lhs; arg 5; dsimp only
              split_res_fuel 1
              rw [runJvmResFast_ifne_branch (v := 1) (by decide)]; mcw_drop; mcw_norm
              heap_step_nonbranch_chunks; mcw_norm
              mcw_cell_tail
              conv => rhs; rw [Algorithm.macroCellWithCell]
              simp only [hx0, hy0, hfxw, hfyw, half, hN, hW,
                decide_false, Bool.false_or]; rfl

/-! ### MacroCell Deserialization Helpers & Decoders -/

def decodeUIntBox? : JvmVal → Option UInt32
  | .boxedUInt u => some u
  | .boxedInt u => some u
  | _ => none

def decodeOptMCNodeLine (h : Jvm.JvmHeap AlgExt) : JvmVal → Option (Option Algorithm.MCNodeLine)
  | .heapRef addr =>
    match h.get? addr with
    | some (.objArray _ elems) =>
      match (elems[0]? : Option JvmVal) with
      | some (.boxedInt 0) => some none
      | some (.boxedInt 1) =>
        match (elems[1]? : Option JvmVal) with
        | some (.heapRef innerAddr) =>
          match h.get? innerAddr with
          | some (.objArray _ inner) =>
            match inner[1]?.bind decodeUIntBox?, inner[5]?.bind decodeUIntBox?,
                  inner[9]?.bind decodeUIntBox?, inner[13]?.bind decodeUIntBox?,
                  inner[17]?.bind decodeUIntBox?, inner[21]?.bind decodeUIntBox?,
                  inner[25]?.bind decodeUIntBox?, inner[29]?.bind decodeUIntBox?,
                  inner[33]?.bind decodeUIntBox?, inner[37]?.bind decodeUIntBox?,
                  inner[41]?.bind decodeUIntBox?, inner[45]?.bind decodeUIntBox?,
                  inner[49]?.bind decodeUIntBox? with
            | some lv, some nw, some nws, some nwe, some ne, some nes, some nee,
              some sw, some sws, some swe, some se, some ses, some see =>
              some (some ⟨lv, nw, nws, nwe, ne, nes, nee, sw, sws, swe, se, ses, see⟩)
            | _, _, _, _, _, _, _, _, _, _, _, _, _ => none
          | _ => none
        | _ => none
      | _ => none
    | _ => none
  | _ => none

def decodeMacrocellStatus (h : Jvm.JvmHeap AlgExt) : JvmVal → Option Algorithm.MacrocellStatus
  | .allocRef "com/alexvanyo/composelife/model/MacrocellStatus$Ok" => some .ok
  | .allocRef "com/alexvanyo/composelife/model/MacrocellStatus$EmptyFile" => some .emptyFile
  | .heapRef addr =>
    match h.get? addr with
    | some (.instance "com/alexvanyo/composelife/model/MacrocellStatus$InvalidHeader" flds) =>
      match flds.lookup "line" with
      | some (.str s) => some (.invalidHeader s)
      | _ => none
    | some (.instance "com/alexvanyo/composelife/model/MacrocellStatus$UnexpectedInput" flds) =>
      match flds.lookup "input", flds.lookup "lineIndex" with
      | some (.str s), some ln => some (.unexpectedInput s ln.asI32)
      | _, _ => none
    | some (.instance "com/alexvanyo/composelife/model/MacrocellStatus$UnexpectedNodeId" flds) =>
      match flds.lookup "input", flds.lookup "n1", flds.lookup "n2", flds.lookup "n3" with
      | some (.str s), some n1, some n2, some n3 =>
        some (.unexpectedNodeId s n1.asI32 n2.asI32 n3.asI32)
      | _, _, _, _ => none
    | _ => none
  | _ => none

def decodeMacrocellResult (st : JvmState) : JvmVal → Option Algorithm.MacrocellResult
  | .heapRef a =>
    match st.jvmHeap.get? a with
    | some (.instance "com/alexvanyo/composelife/model/MacrocellResult" flds) =>
      match flds.lookup "status", flds.lookup "warnings", flds.lookup "macroCell" with
      | some sv, some (.heapRef wAddr), some (.ext (.mc mc)) =>
        match decodeMacrocellStatus st.jvmHeap sv, st.jvmHeap.get? wAddr with
        | some s, some (.objArray _ warnVals) =>
          (warnVals.toList.mapM (decodeMacrocellWarning st.jvmHeap)).map fun ws =>
            ⟨s, ws.toArray, mc⟩
        | _, _ => none
      | _, _, _ => none
    | _ => none
  | _ => none

/-! ### Heap & Opcode Helpers for Macrocell Deserialization -/

private theorem jvmHeap_set_set {Ext : Type} (jh : Jvm.JvmHeap Ext) (addr : Nat)
    (v w : Jvm.HeapObj Ext) :
    (jh.set addr v).set addr w = jh.set addr w := by
  by_cases h : addr < jh.objects.size
  · have hsz : addr < (jh.objects.set addr v h).size := by simp [h]
    simp only [Jvm.JvmHeap.set, h, ↓reduceDIte, hsz]
    congr 1
    apply Array.ext'
    simp only [Array.toList_set]
    have hk : ∀ (addr : Nat) (l : List (Jvm.HeapObj Ext)), addr < l.length →
        (l.set addr v).set addr w = l.set addr w := by
      intro addr l
      induction l generalizing addr with
      | nil => intro ha; simp at ha
      | cons x xs ih =>
        intro ha
        cases addr with
        | zero => rfl
        | succ k =>
          simp only [List.set_cons_succ]
          congr 1
          exact ih k (Nat.succ_lt_succ_iff.mp ha)
    exact hk addr jh.objects.toList h
  · simp [Jvm.JvmHeap.set, h]

private theorem jvmHeap_get?_set_push_self (jh : Jvm.JvmHeap AlgExt)
    (o o' : Jvm.HeapObj AlgExt) :
    (({ objects := jh.objects.push o, statics := jh.statics } : Jvm.JvmHeap AlgExt).set
        jh.objects.size o').get? jh.objects.size = some o' := by
  have h1 : (jh.alloc o).2.get? jh.objects.size = some o := jvmHeap_get?_alloc_self jh o
  dsimp only [Jvm.JvmHeap.alloc] at h1
  exact jvmHeap_get?_set_self h1

private theorem runJvmResFast_checkNotNull_nonnull {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {rest : List JvmInstr} {pc0 : Nat} {v : JvmVal} {msg : String} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hne : v ≠ .null) :
    runJvmResFast (f + 1) prog pc
        (.invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
          "(Ljava/lang/Object;Ljava/lang/String;)V" :: rest)
        ⟨pc0, .str msg :: v :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, stkRest, locs, jh, hp⟩ := by
  have his : Jvm.JvmVal.isNull v = false := by cases v <;> simp_all [Jvm.JvmVal.isNull]
  have hstep : Jvm.stepInstr algHooks
      (.invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
        "(Ljava/lang/Object;Ljava/lang/String;)V")
      ⟨pc, .str msg :: v :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, stkRest, locs, jh, hp⟩) := by
    simp only [Jvm.stepInstr, Jvm.stepInvokeStaticGeneric, his]
    rfl
  exact step1_helper (f' := f) (k := 1) (by decide) rfl (by intro h; cases h) hstep

private theorem runJvmResFast_areturn {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {rest : List JvmInstr} {pc0 : Nat} {v : JvmVal} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.areturn :: rest) ⟨pc0, v :: stkRest, locs, jh, hp⟩ =
      some (v, ⟨pc, v :: stkRest, locs, jh, hp⟩) := rfl

private theorem runJvmResFast_tableswitch {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {low : Int32} {targets : List Nat} {defT : Nat} {rest : List JvmInstr} {pc0 : Nat}
    {key : JvmVal} {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.tableswitch low targets defT :: rest)
        ⟨pc0, key :: stkRest, locs, jh, hp⟩ =
      let t := Jvm.tableswitchTarget key.asI32 low targets defT
      runJvmResFast f prog t (prog.drop t) ⟨t, stkRest, locs, jh, hp⟩ := by
  conv => lhs; dsimp only [runJvmResFast]; rw [Jvm.runJvmResFast.eq_def]
  simp [runJvmResFast]

private theorem decodeMacrocellStatus_encode (jh : Jvm.JvmHeap AlgExt) (s : Algorithm.MacrocellStatus) :
    let (sv, h1) := match s with
      | .ok => (.allocRef "com/alexvanyo/composelife/model/MacrocellStatus$Ok", jh)
      | .emptyFile => (.allocRef "com/alexvanyo/composelife/model/MacrocellStatus$EmptyFile", jh)
      | .invalidHeader line =>
        let (a, ha) := jh.alloc (.instance "com/alexvanyo/composelife/model/MacrocellStatus$InvalidHeader"
          [("line", .str line)])
        (.heapRef a, ha)
      | .unexpectedInput inp ln =>
        let (a, ha) := jh.alloc (.instance "com/alexvanyo/composelife/model/MacrocellStatus$UnexpectedInput"
          [("input", .str inp), ("lineIndex", .i32 ln)])
        (.heapRef a, ha)
      | .unexpectedNodeId inp n1 n2 n3 =>
        let (a, ha) := jh.alloc (.instance "com/alexvanyo/composelife/model/MacrocellStatus$UnexpectedNodeId"
          [("input", .str inp), ("n1", .i32 n1), ("n2", .i32 n2), ("n3", .i32 n3)])
        (.heapRef a, ha)
    decodeMacrocellStatus h1 sv = some s := by
  cases s with
  | ok => rfl
  | emptyFile => rfl
  | invalidHeader line =>
    dsimp only [decodeMacrocellStatus, Jvm.JvmHeap.alloc, Jvm.JvmHeap.get?]
    simp [List.lookup]
  | unexpectedInput inp ln =>
    dsimp only [decodeMacrocellStatus, Jvm.JvmHeap.alloc, Jvm.JvmHeap.get?]
    simp [List.lookup, Jvm.JvmVal.asI32]
  | unexpectedNodeId inp n1 n2 n3 =>
    dsimp only [decodeMacrocellStatus, Jvm.JvmHeap.alloc, Jvm.JvmHeap.get?]
    simp [List.lookup, Jvm.JvmVal.asI32]

private theorem decodeMacrocellStatus_ext {h1 h2 : Jvm.JvmHeap AlgExt}
    (hext : ∀ a o, h1.get? a = some o → h2.get? a = some o)
    {sv : JvmVal} {s : Algorithm.MacrocellStatus}
    (hd : decodeMacrocellStatus h1 sv = some s) :
    decodeMacrocellStatus h2 sv = some s := by
  cases sv with
  | heapRef addr =>
    dsimp only [decodeMacrocellStatus] at hd ⊢
    cases hget : h1.get? addr with
    | none => simp [hget] at hd
    | some obj =>
      rw [hget] at hd
      rw [hext addr obj hget]
      exact hd
  | allocRef cls =>
    dsimp only [decodeMacrocellStatus] at hd ⊢
    by_cases hOk : cls = "com/alexvanyo/composelife/model/MacrocellStatus$Ok"
    · subst hOk; exact hd
    · by_cases hEf : cls = "com/alexvanyo/composelife/model/MacrocellStatus$EmptyFile"
      · subst hEf; exact hd
      · simp [hOk, hEf] at hd
  | _ => exact hd

private theorem decodeMacrocellWarning_ext {h1 h2 : Jvm.JvmHeap AlgExt}
    (hext : ∀ a o, h1.get? a = some o → h2.get? a = some o)
    {wv : JvmVal} {w : Algorithm.MacrocellWarning}
    (hd : decodeMacrocellWarning h1 wv = some w) :
    decodeMacrocellWarning h2 wv = some w := by
  cases wv with
  | heapRef addr =>
    dsimp only [decodeMacrocellWarning] at hd ⊢
    cases hget : h1.get? addr with
    | none => simp [hget] at hd
    | some obj =>
      rw [hget] at hd
      rw [hext addr obj hget]
      exact hd
  | allocRef cls =>
    dsimp only [decodeMacrocellWarning] at hd ⊢
    by_cases hEf : cls = "com/alexvanyo/composelife/model/MacrocellWarning$EmptyFile"
    · subst hEf; exact hd
    · simp [hEf] at hd
  | _ => exact hd

private theorem decodeMacrocellWarning_encode (jh : Jvm.JvmHeap AlgExt)
    (w : Algorithm.MacrocellWarning) :
    let (wv, h1) := encodeMacrocellWarning jh w
    decodeMacrocellWarning h1 wv = some w := by
  cases w with
  | emptyFile => rfl
  | blankLine ln =>
    dsimp only [encodeMacrocellWarning, decodeMacrocellWarning, Jvm.JvmHeap.alloc, Jvm.JvmHeap.get?]
    simp [List.lookup, Jvm.JvmVal.asI32]
  | unexpectedInput ln col inp =>
    dsimp only [encodeMacrocellWarning, decodeMacrocellWarning, Jvm.JvmHeap.alloc, Jvm.JvmHeap.get?]
    simp [List.lookup, Jvm.JvmVal.asI32]

private theorem encodeMacrocellWarns_foldl (ws : List Algorithm.MacrocellWarning)
    (acc : Array JvmVal) (accWs : List Algorithm.MacrocellWarning)
    (jh : Jvm.JvmHeap AlgExt)
    (hacc : acc.toList.mapM (decodeMacrocellWarning jh) = some accWs) :
    let r := ws.foldl (fun (p : Array JvmVal × Jvm.JvmHeap AlgExt) w =>
      (p.1.push (encodeMacrocellWarning p.2 w).1, (encodeMacrocellWarning p.2 w).2)) (acc, jh)
    r.1.toList.mapM (decodeMacrocellWarning r.2) = some (accWs ++ ws) ∧
      (∀ a o, jh.get? a = some o → r.2.get? a = some o) := by
  induction ws generalizing acc accWs jh with
  | nil =>
    simp only [List.foldl_nil, List.append_nil]
    exact ⟨hacc, fun _ _ h => h⟩
  | cons w rest ih =>
    simp only [List.foldl_cons]
    have hext_w : ∀ a o, jh.get? a = some o → (encodeMacrocellWarning jh w).2.get? a = some o := by
      intro a o ha
      rcases Array.getElem?_eq_some_iff.mp ha with ⟨hlt, _⟩
      cases w with
      | emptyFile => exact ha
      | blankLine ln => exact jvmHeap_get?_alloc_lt jh _ hlt ▸ ha
      | unexpectedInput ln col inp => exact jvmHeap_get?_alloc_lt jh _ hlt ▸ ha
    have hacc' : acc.toList.mapM (decodeMacrocellWarning (encodeMacrocellWarning jh w).2) =
        some accWs := by
      clear ih
      have : ∀ (xs : List JvmVal) (zs : List Algorithm.MacrocellWarning),
          xs.mapM (decodeMacrocellWarning jh) = some zs →
          xs.mapM (decodeMacrocellWarning (encodeMacrocellWarning jh w).2) = some zs := by
        intro xs
        induction xs with
        | nil => intro zs h; exact h
        | cons x xs ihx =>
          intro zs h
          cases hx : decodeMacrocellWarning jh x with
          | none => simp [hx] at h
          | some wx =>
            simp only [List.mapM_cons, hx] at h
            cases hrest : xs.mapM (decodeMacrocellWarning jh) with
            | none => simp [hrest] at h
            | some wxs =>
              simp only [hrest] at h
              injection h with hzs
              subst hzs
              simp only [List.mapM_cons, decodeMacrocellWarning_ext hext_w hx, ihx wxs hrest]
              rfl
      exact this acc.toList accWs hacc
    have hw1 : decodeMacrocellWarning (encodeMacrocellWarning jh w).2 (encodeMacrocellWarning jh w).1 =
        some w := decodeMacrocellWarning_encode jh w
    have hpush : (acc.push (encodeMacrocellWarning jh w).1).toList.mapM
        (decodeMacrocellWarning (encodeMacrocellWarning jh w).2) = some (accWs ++ [w]) := by
      rw [Array.toList_push, List.mapM_append, hacc', List.mapM_cons, hw1, List.mapM_nil]
      rfl
    rcases ih (acc.push (encodeMacrocellWarning jh w).1) (accWs ++ [w])
        (encodeMacrocellWarning jh w).2 hpush with ⟨hfin, hext_rest⟩
    refine ⟨?_, ?_⟩
    · simpa [List.append_assoc] using hfin
    · intro a o ha
      exact hext_rest a o (hext_w a o ha)

theorem decodeMacrocellResult_encode (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (res : Algorithm.MacrocellResult) :
    let enc := encodeMacrocellResult jh res
    decodeMacrocellResult ⟨0, [], fun _ => .null, enc.2, hp⟩ enc.1 = some res := by
  rcases res with ⟨status, warns, mc⟩
  have hstatus : ∀ (sv : JvmVal) (h1 : Jvm.JvmHeap AlgExt),
      decodeMacrocellStatus h1 sv = some status →
      let foldRes := warns.foldl
        (fun (p : Array JvmVal × Jvm.JvmHeap AlgExt) w =>
          (p.1.push (encodeMacrocellWarning p.2 w).1, (encodeMacrocellWarning p.2 w).2))
        (#[], h1)
      let h3 := (foldRes.2.alloc (.objArray "java/lang/Object" foldRes.1)).2
      let h4 := (h3.alloc (.instance "com/alexvanyo/composelife/model/MacrocellResult"
        [("status", sv), ("warnings", .heapRef foldRes.2.objects.size),
         ("macroCell", .ext (.mc mc))])).2
      decodeMacrocellResult ⟨0, [], fun _ => .null, h4, hp⟩ (.heapRef h3.objects.size) =
        some ⟨status, warns, mc⟩ := by
    intro sv h1 hsv1
    have hfl := encodeMacrocellWarns_foldl warns.toList #[] [] h1 rfl
    simp only [Array.foldl_toList, List.nil_append] at hfl
    let foldRes := warns.foldl
      (fun (p : Array JvmVal × Jvm.JvmHeap AlgExt) w =>
        (p.1.push (encodeMacrocellWarning p.2 w).1, (encodeMacrocellWarning p.2 w).2))
      (#[], h1)
    have hwarns : foldRes.1.toList.mapM (decodeMacrocellWarning foldRes.2) = some warns.toList := hfl.1
    have hext1 : ∀ a o, h1.get? a = some o → foldRes.2.get? a = some o := hfl.2
    let h3 := (foldRes.2.alloc (.objArray "java/lang/Object" foldRes.1)).2
    let h4 := (h3.alloc (.instance "com/alexvanyo/composelife/model/MacrocellResult"
      [("status", sv), ("warnings", .heapRef foldRes.2.objects.size),
       ("macroCell", .ext (.mc mc))])).2
    have hext3 : ∀ a o, foldRes.2.get? a = some o → h3.get? a = some o := by
      intro a o ha
      rcases Array.getElem?_eq_some_iff.mp ha with ⟨hlt, _⟩
      exact jvmHeap_get?_alloc_lt _ _ hlt ▸ ha
    have hext4 : ∀ a o, h3.get? a = some o → h4.get? a = some o := by
      intro a o ha
      rcases Array.getElem?_eq_some_iff.mp ha with ⟨hlt, _⟩
      exact jvmHeap_get?_alloc_lt _ _ hlt ▸ ha
    have hsv4 : decodeMacrocellStatus h4 sv = some status :=
      decodeMacrocellStatus_ext (fun a o ha => hext4 a o (hext3 a o (hext1 a o ha))) hsv1
    have hwarns4 : foldRes.1.toList.mapM (decodeMacrocellWarning h4) = some warns.toList := by
      clear hsv1 hsv4 hext1
      have hext34 : ∀ a o, foldRes.2.get? a = some o → h4.get? a = some o :=
        fun a o ha => hext4 a o (hext3 a o ha)
      have : ∀ (xs : List JvmVal) (ws : List Algorithm.MacrocellWarning),
          xs.mapM (decodeMacrocellWarning foldRes.2) = some ws →
          xs.mapM (decodeMacrocellWarning h4) = some ws := by
        intro xs
        induction xs with
        | nil => intro ws h; exact h
        | cons x xs ihx =>
          intro ws h
          cases hx : decodeMacrocellWarning foldRes.2 x with
          | none => simp [hx] at h
          | some wx =>
            simp only [List.mapM_cons, hx] at h
            cases hrest : xs.mapM (decodeMacrocellWarning foldRes.2) with
            | none => simp [hrest] at h
            | some wxs =>
              simp only [hrest] at h
              injection h with hws
              subst hws
              simp only [List.mapM_cons, decodeMacrocellWarning_ext hext34 hx, ihx wxs hrest]
              rfl
      exact this foldRes.1.toList warns.toList hwarns
    have hgetArr : h4.get? foldRes.2.objects.size = some (.objArray "java/lang/Object" foldRes.1) := by
      have h3get : h3.get? foldRes.2.objects.size = some (.objArray "java/lang/Object" foldRes.1) :=
        jvmHeap_get?_alloc_self _ _
      rcases Array.getElem?_eq_some_iff.mp h3get with ⟨hlt, _⟩
      rw [jvmHeap_get?_alloc_lt _ _ hlt, h3get]
    have hgetRes : h4.get? h3.objects.size =
        some (.instance "com/alexvanyo/composelife/model/MacrocellResult"
          [("status", sv), ("warnings", .heapRef foldRes.2.objects.size),
           ("macroCell", .ext (.mc mc))]) :=
      jvmHeap_get?_alloc_self _ _
    have hres_eq : decodeMacrocellResult ⟨0, [], fun _ => .null, h4, hp⟩ (.heapRef h3.objects.size) =
        match decodeMacrocellStatus h4 sv, h4.get? foldRes.2.objects.size with
        | some s, some (.objArray _ warnVals) =>
          (warnVals.toList.mapM (decodeMacrocellWarning h4)).map fun ws =>
            { status := s, warnings := ws.toArray, macroCell := mc }
        | _, _ => none := by
      simp only [decodeMacrocellResult]
      rw [hgetRes]
      rfl
    change decodeMacrocellResult ⟨0, [], fun _ => .null, h4, hp⟩ (.heapRef h3.objects.size) =
      some ⟨status, warns, mc⟩
    rw [hres_eq, hsv4, hgetArr]
    dsimp only
    rw [hwarns4]
    simp
  cases status with
  | ok => exact hstatus _ jh (decodeMacrocellStatus_encode jh .ok)
  | emptyFile => exact hstatus _ jh (decodeMacrocellStatus_encode jh .emptyFile)
  | invalidHeader line =>
    dsimp only [encodeMacrocellResult]
    exact hstatus _ _ (decodeMacrocellStatus_encode jh (.invalidHeader line))
  | unexpectedInput inp ln =>
    dsimp only [encodeMacrocellResult]
    exact hstatus _ _ (decodeMacrocellStatus_encode jh (.unexpectedInput inp ln))
  | unexpectedNodeId inp n1 n2 n3 =>
    dsimp only [encodeMacrocellResult]
    exact hstatus _ _ (decodeMacrocellStatus_encode jh (.unexpectedNodeId inp n1 n2 n3))

/-! ### deserializeMacrocell___closed__0, ___closed__1, ___closed__2 -/

theorem deserializeMacrocell___closed__0_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    let (addr, h') := jh.alloc (.objArray "java/lang/Object" #[])
    ∃ st',
      runJvmRes 10 f_Algorithm_deserializeMacrocell___closed__0_prog
          ⟨0, [], fun _ => .null, jh, hp⟩ =
        some (.heapRef addr, st') ∧
      st'.jvmHeap = h' ∧ st'.heap = hp := by
  have hrun : runJvmRes 10 f_Algorithm_deserializeMacrocell___closed__0_prog
      ⟨0, [], fun _ => .null, jh, hp⟩ =
      some (.heapRef jh.objects.size,
        ⟨2, [.heapRef jh.objects.size], fun _ => .null,
          (jh.alloc (.objArray "java/lang/Object" #[])).2, hp⟩) := by
    apply runJvmRes_of_runJvmResFast0 10 _ _ _ rfl
    rw [show (10 : Nat) = 8 + 2 from rfl]
    dsimp only [f_Algorithm_deserializeMacrocell___closed__0_prog]
    step1
    rw [runJvmResFast_anewarray_obj (by decide)]
    have hrep0 : Array.replicate (0 : UInt32).toNat (JvmVal.null : JvmVal) = #[] := rfl
    rw [hrep0]
    rw [show (8 : Nat) = 7 + 1 from rfl]
    exact runJvmResFast_areturn
  exact ⟨_, hrun, rfl, rfl⟩

theorem deserializeMacrocell___closed__1_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hstat : jh.statics = []) :
    let (_, h1) := jh.alloc (.objArray "java/lang/Object" #[])
    let (_, h2) := h1.alloc (.objArray "java/lang/Object" #[JvmVal.null])
    let h3 := h2.set h1.objects.size (.objArray "java/lang/Object"
      (#[JvmVal.null].set 0 (.allocRef "com/alexvanyo/composelife/model/MacrocellWarning$EmptyFile")
        (by decide)))
    ∃ st',
      runJvmRes 40 f_Algorithm_deserializeMacrocell___closed__1_prog
          ⟨0, [], fun _ => .null, jh, hp⟩ =
        some (.heapRef h1.objects.size, st') ∧
      st'.jvmHeap = h3 ∧ st'.heap = hp := by
  let h1 := (jh.alloc (.objArray "java/lang/Object" #[])).2
  let h2 := (h1.alloc (.objArray "java/lang/Object" #[JvmVal.null])).2
  let h3 := h2.set h1.objects.size (.objArray "java/lang/Object"
    (#[JvmVal.null].set 0 (.allocRef "com/alexvanyo/composelife/model/MacrocellWarning$EmptyFile")
      (by decide)))
  have hrun : runJvmRes 40 f_Algorithm_deserializeMacrocell___closed__1_prog
      ⟨0, [], fun _ => .null, jh, hp⟩ =
      some (.heapRef h1.objects.size,
        ⟨25, [.heapRef h1.objects.size],
          setLocal (setLocal (setLocal (setLocal (setLocal (fun _ => .null)
            0 (.allocRef "com/alexvanyo/composelife/model/MacrocellWarning$EmptyFile"))
            1 (.heapRef jh.objects.size)) 2 (.heapRef h1.objects.size))
            3 (.heapRef h1.objects.size)) 4 (.i32 0),
          h3, hp⟩) := by
    apply runJvmRes_of_runJvmResFast0 40 _ _ _ rfl
    rw [show (40 : Nat) = 10 + 30 from rfl]
    dsimp only [f_Algorithm_deserializeMacrocell___closed__1_prog]
    rw [runJvmResFast_getstatic_step hstat rfl]
    step1; step1
    rw [runJvmResFast_anewarray_obj (by decide)]
    have hrep0 : Array.replicate (0 : UInt32).toNat (JvmVal.null : JvmVal) = #[] := rfl
    rw [hrep0]
    step1; step1; step1
    have hget0 : h1.get? jh.objects.size = some (.objArray "java/lang/Object" #[]) :=
      jvmHeap_get?_alloc_self _ _
    rw [runJvmResFast_arraylength_obj hget0]
    step1; step1
    rw [runJvmResFast_invokestatic_step (stepStatic_arraysCopyOf_obj (by decide) hget0)]
    rw [show (Array.ofFn (n := (UInt32.ofNat (#[] : Array JvmVal).size + 1).toNat) fun i =>
        if h : i.val < (#[] : Array JvmVal).size then (#[] : Array JvmVal)[i.val]
        else (JvmVal.null : JvmVal)) = #[JvmVal.null] from rfl]
    step1; step1; step1; step1; step1; step1; step1; step1; step1; step1
    rw [runJvmResFast_arraylength_obj (by
      rw [jvmHeap_get?_alloc_lt _ _ (by simp [h1, Jvm.JvmHeap.alloc])]
      exact hget0)]
    step1
    rw [show (UInt32.ofNat (#[] : Array JvmVal).size) = 0 from rfl]
    have hget1 : h2.get? h1.objects.size = some (.objArray "java/lang/Object" #[JvmVal.null]) :=
      jvmHeap_get?_alloc_self _ _
    rw [runJvmResFast_aastore hget1 (by decide) (by decide)]
    step1
    exact runJvmResFast_areturn
  exact ⟨_, hrun, rfl, rfl⟩

theorem deserializeMacrocell___closed__2_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hstat : jh.statics = []) :
    ∃ v st',
      runJvmRes 30 f_Algorithm_deserializeMacrocell___closed__2_prog
          ⟨0, [], fun _ => .null, jh, hp⟩ =
        some (v, st') ∧
      decodeMacrocellResult st' v =
        some ⟨.emptyFile, #[.emptyFile], Algorithm.emptyLevel4⟩ ∧
      st'.heap = hp := by
  let enc := encodeMacrocellResult jh ⟨.emptyFile, #[.emptyFile], Algorithm.emptyLevel4⟩
  have hrun : runJvmRes 30 f_Algorithm_deserializeMacrocell___closed__2_prog
      ⟨0, [], fun _ => .null, jh, hp⟩ =
      some (enc.1, ⟨15, [enc.1],
        setLocal (setLocal (fun _ => .null) 0 (.heapRef jh.objects.size)) 1 (.i32 0), enc.2, hp⟩) := by
    apply runJvmRes_of_runJvmResFast0 30 _ _ _ rfl
    rw [show (30 : Nat) = 10 + 20 from rfl]
    dsimp only [f_Algorithm_deserializeMacrocell___closed__2_prog]
    step1; step1; step1; step1
    have hstat1 : ({
        objects := jh.objects.push (Jvm.HeapObj.objArray "java/lang/Object"
          #[JvmVal.allocRef "com/alexvanyo/composelife/model/MacrocellWarning$EmptyFile"]),
        statics := jh.statics } : Jvm.JvmHeap AlgExt).statics = [] := hstat
    rw [runJvmResFast_getstatic_step hstat1 rfl]
    step1; step1; step1; step1; step1
    rw [show (({
        objects := jh.objects.push (Jvm.HeapObj.objArray "java/lang/Object"
          #[JvmVal.allocRef "com/alexvanyo/composelife/model/MacrocellWarning$EmptyFile"]),
        statics := jh.statics } : Jvm.JvmHeap AlgExt).getStatic?
        "MacroCellLeanKt" "EMPTY_LEVEL_4") = none by simp [Jvm.JvmHeap.getStatic?, hstat]]
    dsimp only [Option.getD]
    step1; step1; step1
    rw [runJvmResFast_checkNotNull_nonnull (by intro h; cases h)]
    step1
    exact runJvmResFast_areturn
  refine ⟨_, _, hrun, ?_, rfl⟩
  exact decodeMacrocellResult_encode jh hp ⟨.emptyFile, #[.emptyFile], Algorithm.emptyLevel4⟩

/-! ### deserializeMacrocell -/

private theorem u8_sext_lt128 (b : UInt8) (hb : b.toNat < 128) :
    UInt32.ofBitVec (b.toBitVec.signExtend 32) = b.toUInt32 := by
  revert b hb; decide

private theorem u8_setWidth_sext (b : UInt8) :
    BitVec.setWidth 8 (b.toBitVec.signExtend 32) = b.toBitVec := by
  revert b; decide

private theorem signExtend_eq_u8 (b : UInt8) (k : Nat) (hk : k < 128) :
    (UInt32.ofBitVec (b.toBitVec.signExtend 32) == UInt32.ofNat k) = (b == UInt8.ofNat k) := by
  by_cases h : b = UInt8.ofNat k
  · subst h
    have hlt : (UInt8.ofNat k).toNat < 128 := by
      change (k % 2 ^ 8) < 128; rw [Nat.mod_eq_of_lt (by omega)]; exact hk
    rw [u8_sext_lt128 _ hlt]
    have hu : (UInt8.ofNat k).toUInt32 = UInt32.ofNat k := by
      apply UInt32.eq_of_toBitVec_eq
      apply BitVec.eq_of_toNat_eq
      change (k % 256) = k % 2 ^ 32
      omega
    rw [hu, beq_self_eq_true, beq_self_eq_true]
  · simp only [BEq.beq, decide_eq_false h]
    apply decide_eq_false
    intro heq
    have hbv : b.toBitVec.signExtend 32 = BitVec.ofNat 32 k :=
      congrArg UInt32.toBitVec heq
    have htr := congrArg (BitVec.setWidth 8) hbv
    rw [u8_setWidth_sext] at htr
    have h8 : BitVec.setWidth 8 (BitVec.ofNat 32 k) = BitVec.ofNat 8 k := by
      apply BitVec.eq_of_toNat_eq
      change (k % 2 ^ 32) % 2 ^ 8 = k % 2 ^ 8
      omega
    rw [h8] at htr
    exact h (congrArg UInt8.ofBitVec htr)

private theorem step_deserMC_pre (lines : Array String) (hp : AlgHeap) (f : Nat)
    (hnumF : (lines.size.toUInt32 == 0) = false) (hszPos : 0 < lines.size) :
    let jh0 : Jvm.JvmHeap AlgExt := {}
    let locs0 : Nat → JvmVal := setLocal (fun _ => .null) 0 (.strArr lines)
    let line0 := lines[0]!
    let hBytes := line0.toByteArray
    let h1 := (jh0.alloc (.byteArray hBytes.data)).2
    runJvmResFast (f + 21) f_Algorithm_deserializeMacrocell_prog 0
        f_Algorithm_deserializeMacrocell_prog ⟨0, [], locs0, jh0, hp⟩ =
      runJvmResFast f f_Algorithm_deserializeMacrocell_prog 21
        (f_Algorithm_deserializeMacrocell_prog.drop 21)
        ⟨21, [.i32 hBytes.size.toUInt32],
          setLocal (setLocal (setLocal locs0 1 (.i32 lines.size.toUInt32)) 2 (.str line0))
            3 (.heapRef jh0.objects.size),
          h1, hp⟩ := by
  intro jh0 locs0 line0 hBytes h1
  have hlt0_bv : (0 : UInt32).toBitVec.slt 0#32 = false := by decide
  have hlt0_sz : (0 : UInt32).toNat < lines.size := hszPos
  have hline0_eq : lines[(0 : UInt32).toNat]'hlt0_sz = line0 := by
    simp [line0, getElem!_pos lines 0 hszPos]
  have hgetBytes : h1.get? jh0.objects.size = some (.byteArray hBytes.data) :=
    jvmHeap_get?_alloc_self _ _
  dsimp only [f_Algorithm_deserializeMacrocell_prog]
  step1; step1; step1; step1; step1; step1; step1; step1
  rw [show f + 13 = (f + 12) + 1 from by omega]
  rw [runJvmResFast_ifeq_fallthrough hnumF, show (8 : Nat) + 1 = 9 from rfl]
  step1; step1
  rw [show locs0 0 = .strArr lines from rfl]
  rw [show f + 10 = (f + 9) + 1 from by omega]
  rw [runJvmResFast_aaload_strArr hlt0_bv hlt0_sz, hline0_eq]
  step1; step1; step1; step1; step1
  rw [show f + 4 = (f + 3) + 1 from by omega]
  rw [runJvmResFast_invokestatic_step stepStatic_stringsEncodeToByteArray]
  have henc : String.toUTF8 line0 = hBytes := rfl
  rw [henc]
  step1; step1
  rw [runJvmResFast_arraylength_byteArray hgetBytes]
  rfl

private theorem stepStatic_getEMPTY_LEVEL_4 {pc : Nat} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hstat : jh.getStatic? "MacroCellLeanKt" "EMPTY_LEVEL_4" = none) :
    stepInvokeStatic ⟨pc, rest, locs, jh, hp⟩
        "MacroCellLeanKt" "getEMPTY_LEVEL_4"
        "()Lcom/alexvanyo/composelife/model/MacroCell$Level4Node;" =
      .inl (some ⟨pc + 1, .ext (.mc Algorithm.emptyLevel4) :: rest, locs, jh, hp⟩) := by
  have h : stepInvokeStatic ⟨pc, rest, locs, jh, hp⟩
      "MacroCellLeanKt" "getEMPTY_LEVEL_4"
      "()Lcom/alexvanyo/composelife/model/MacroCell$Level4Node;" =
      .inl (some ⟨pc + 1, (jh.getStatic? "MacroCellLeanKt" "EMPTY_LEVEL_4").getD
        (.ext (.mc Algorithm.emptyLevel4)) :: rest, locs, jh, hp⟩) := rfl
  rw [h, hstat]
  rfl

private theorem stepStatic_compareUnsigned {pc : Nat} {a b : UInt32} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .i32 b :: .i32 a :: rest, locs, jh, hp⟩
        "java/lang/Integer" "compareUnsigned" "(II)I" =
      .inl (some ⟨pc + 1,
        .i32 (if a == b then 0 else if a < b then 4294967295 else 1) :: rest,
        locs, jh, hp⟩) := rfl

private theorem step_deserMC_invalid (line0 : String) (h1 : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (f : Nat) (stk : List JvmVal) (locs : Nat → JvmVal) (hloc2 : locs 2 = .str line0)
    (hstat : h1.getStatic? "MacroCellLeanKt" "EMPTY_LEVEL_4" = none) :
    runJvmResFast (f + 25) f_Algorithm_deserializeMacrocell_prog 78
        (f_Algorithm_deserializeMacrocell_prog.drop 78) ⟨78, stk, locs, h1, hp⟩ =
      let enc := encodeMacrocellResult h1 ⟨.invalidHeader line0, #[], Algorithm.emptyLevel4⟩
      some (enc.1, ⟨98, enc.1 :: stk,
        setLocal (setLocal (setLocal locs 4 (.heapRef h1.objects.size))
          5 (.heapRef (h1.alloc (.instance
            "com/alexvanyo/composelife/model/MacrocellStatus$InvalidHeader"
            [("line", .str line0)])).2.objects.size))
          7 (.i32 0),
        enc.2, hp⟩) := by
  dsimp only [f_Algorithm_deserializeMacrocell_prog, List.drop]
  step1; step1; step1
  rw [hloc2]
  step1; step1; step1; step1; step1; step1; step1
  have hgetIH : ((h1.alloc (.instance
      "com/alexvanyo/composelife/model/MacrocellStatus$InvalidHeader"
      [("line", .str line0)])).2.alloc (.objArray "java/lang/Object" #[])).2.get?
      h1.objects.size =
      some (.instance "com/alexvanyo/composelife/model/MacrocellStatus$InvalidHeader"
        [("line", .str line0)]) := by
    rw [jvmHeap_get?_alloc_lt _ _ (by simp [Jvm.JvmHeap.alloc])]
    exact jvmHeap_get?_alloc_self _ _
  dsimp only [Jvm.JvmHeap.alloc] at hgetIH
  split_res_fuel 1
  rw [runJvmResFast_checkcast_instance (ty := "com/alexvanyo/composelife/model/MacrocellStatus")
    (by rw [hgetIH]; rfl) rfl]
  rw [show f + 15 - 1 = (f + 11) + 3 from by omega]
  step1; step1; step1
  rw [show f + 11 = (f + 10) + 1 from by omega]
  rw [runJvmResFast_invokestatic_step (stepStatic_getEMPTY_LEVEL_4 (by exact hstat))]
  rw [show f + 10 = (f + 7) + 3 from by omega]
  step1; step1; step1
  split_res_fuel 1
  rw [runJvmResFast_checkNotNull_nonnull (by intro h; cases h)]
  rw [show f + 7 - 1 = (f + 5) + 1 from by omega]
  step1
  rw [show f + 5 = (f + 4) + 1 from by omega]
  exact runJvmResFast_areturn

private def mcNodes? : JvmVal → Option (Algorithm.GrowBuf Algorithm.MacroCell)
  | .ext (.mcGrowBuf b) => some b
  | .ext (.strGrowBuf b) => if b.data.isEmpty && b.size == 0 then some Algorithm.GrowBuf.empty else none
  | _ => none

private def mcLeaves? : JvmVal → Option (Algorithm.GrowBuf UInt64)
  | .ext (.u64GrowBuf b) => some b
  | .ext (.strGrowBuf b) => if b.data.isEmpty && b.size == 0 then some Algorithm.GrowBuf.empty else none
  | _ => none

private def mcIsLeaf? : JvmVal → Option (Algorithm.GrowBuf Bool)
  | .ext (.boolGrowBuf b) => some b
  | .ext (.strGrowBuf b) => if b.data.isEmpty && b.size == 0 then some Algorithm.GrowBuf.empty else none
  | _ => none

private def mcWarns? : JvmVal → Option (Algorithm.GrowBuf Algorithm.MacrocellWarning)
  | .ext (.mcWarnGrowBuf b) => some b
  | .ext (.strGrowBuf b) => if b.data.isEmpty && b.size == 0 then some Algorithm.GrowBuf.empty else none
  | _ => none

private def mcDispatch (pc : Nat) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt)
    (hp : AlgHeap) (warnsVal isLeafVal leavesVal nodesVal leaf y x col p limit
      bytesVal inLeaf i numLines linesVal : JvmVal) (rest : List JvmVal)
    (loopFn : Array String → UInt32 → UInt32 → Bool → ByteArray → UInt32 → UInt32 → UInt32 →
      UInt32 → UInt32 → UInt64 → Algorithm.GrowBuf Algorithm.MacroCell →
      Algorithm.GrowBuf UInt64 → Algorithm.GrowBuf Bool →
      Algorithm.GrowBuf Algorithm.MacrocellWarning → Algorithm.MacrocellResult)
    (encFn : Jvm.JvmHeap AlgExt → Algorithm.MacrocellResult → JvmVal × Jvm.JvmHeap AlgExt) :
    Option JvmState ⊕ Option JvmVal :=
  let st : JvmState := ⟨pc, warnsVal :: isLeafVal :: leavesVal :: nodesVal :: leaf :: y :: x ::
    col :: p :: limit :: bytesVal :: inLeaf :: i :: numLines :: linesVal :: rest, locs, jh, hp⟩
  match decodeStrArray st linesVal, decodeBytes st bytesVal,
      mcNodes? nodesVal, mcLeaves? leavesVal, mcIsLeaf? isLeafVal, mcWarns? warnsVal with
  | some lines', some bytes', some nodes', some leaves', some isLeaf', some warns' =>
    let res := loopFn lines' numLines.asI32 i.asI32 (inLeaf.asI32 != 0)
      bytes' limit.asI32 p.asI32 col.asI32 x.asI32 y.asI32 leaf.asI64 nodes' leaves' isLeaf' warns'
    let (resVal, h') := encFn st.jvmHeap res
    .inl (some { st with pc := st.pc + 1, stack := resVal :: rest, jvmHeap := h' })
  | _, _, _, _, _, _ => .inr none

private theorem stepStatic_mcLoop_match (pc : Nat) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt)
    (hp : AlgHeap) (warnsVal isLeafVal leavesVal nodesVal leaf y x col p limit
      bytesVal inLeaf i numLines linesVal : JvmVal) (rest : List JvmVal) :
    let st : JvmState := ⟨pc, warnsVal :: isLeafVal :: leavesVal :: nodesVal :: leaf :: y :: x ::
      col :: p :: limit :: bytesVal :: inLeaf :: i :: numLines :: linesVal :: rest, locs, jh, hp⟩
    stepInvokeStatic st "MacroCellLeanKt" "f_Algorithm_deserializeMacrocell_loop-ocggIy4"
      ("([Ljava/lang/Object;IIZ[BIIIIIJLjava/lang/Object;Ljava/lang/Object;" ++
        "Ljava/lang/Object;Ljava/lang/Object;)Lcom/alexvanyo/composelife/model/MacrocellResult;") =
      mcDispatch pc locs jh hp warnsVal isLeafVal leavesVal nodesVal leaf y x col p limit
        bytesVal inLeaf i numLines linesVal rest
        Algorithm.deserializeMacrocell.loop encodeMacrocellResult := rfl

private theorem mc_match_elim (pc : Nat) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt)
    (hp : AlgHeap) (warnsVal isLeafVal leavesVal nodesVal leaf y x col p limit
      bytesVal inLeaf i numLines linesVal : JvmVal) (rest : List JvmVal)
    (loopFn : Array String → UInt32 → UInt32 → Bool → ByteArray → UInt32 → UInt32 → UInt32 →
      UInt32 → UInt32 → UInt64 → Algorithm.GrowBuf Algorithm.MacroCell →
      Algorithm.GrowBuf UInt64 → Algorithm.GrowBuf Bool →
      Algorithm.GrowBuf Algorithm.MacrocellWarning → Algorithm.MacrocellResult)
    (encFn : Jvm.JvmHeap AlgExt → Algorithm.MacrocellResult → JvmVal × Jvm.JvmHeap AlgExt)
    {lines : Array String} {bytes : ByteArray}
    {nodes : Algorithm.GrowBuf Algorithm.MacroCell} {leaves : Algorithm.GrowBuf UInt64}
    {isLeaf : Algorithm.GrowBuf Bool} {warns : Algorithm.GrowBuf Algorithm.MacrocellWarning}
    (hl : decodeStrArray ⟨pc, warnsVal :: isLeafVal :: leavesVal :: nodesVal :: leaf :: y :: x ::
      col :: p :: limit :: bytesVal :: inLeaf :: i :: numLines :: linesVal :: rest, locs, jh, hp⟩
      linesVal = some lines)
    (hb : decodeBytes ⟨pc, warnsVal :: isLeafVal :: leavesVal :: nodesVal :: leaf :: y :: x ::
      col :: p :: limit :: bytesVal :: inLeaf :: i :: numLines :: linesVal :: rest, locs, jh, hp⟩
      bytesVal = some bytes)
    (hn : mcNodes? nodesVal = some nodes) (hlf : mcLeaves? leavesVal = some leaves)
    (hil : mcIsLeaf? isLeafVal = some isLeaf) (hw : mcWarns? warnsVal = some warns) :
    mcDispatch pc locs jh hp warnsVal isLeafVal leavesVal nodesVal leaf y x col p limit
        bytesVal inLeaf i numLines linesVal rest loopFn encFn =
      .inl (some ⟨pc + 1,
        (encFn jh (loopFn lines numLines.asI32 i.asI32 (inLeaf.asI32 != 0) bytes limit.asI32
          p.asI32 col.asI32 x.asI32 y.asI32 leaf.asI64 nodes leaves isLeaf warns)).1 :: rest,
        locs,
        (encFn jh (loopFn lines numLines.asI32 i.asI32 (inLeaf.asI32 != 0) bytes limit.asI32
          p.asI32 col.asI32 x.asI32 y.asI32 leaf.asI64 nodes leaves isLeaf warns)).2,
        hp⟩) := by
  dsimp only [mcDispatch]
  rw [hl, hb, hn, hlf, hil, hw]

private theorem mc_enc_state_congr (pc : Nat) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (rest : List JvmVal)
    (encFn : Jvm.JvmHeap AlgExt → Algorithm.MacrocellResult → JvmVal × Jvm.JvmHeap AlgExt)
    (r1 r2 : Algorithm.MacrocellResult) (hr : r1 = r2) :
    (Sum.inl (some ⟨pc + 1, (encFn jh r1).1 :: rest, locs, (encFn jh r1).2, hp⟩) :
      Option JvmState ⊕ Option JvmVal) =
    .inl (some ⟨pc + 1, (encFn jh r2).1 :: rest, locs, (encFn jh r2).2, hp⟩) := by
  subst hr
  rfl

private theorem stepStatic_deserMC_loop_empty {pc : Nat} {lines : Array String}
    {numLines : UInt32} {bytes : ByteArray}
    {rest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hget : jh.get? 0 = some (.byteArray bytes.data)) :
    stepInvokeStatic ⟨pc, .ext (.strGrowBuf Algorithm.GrowBuf.empty) ::
      .ext (.strGrowBuf Algorithm.GrowBuf.empty) ::
      .ext (.strGrowBuf Algorithm.GrowBuf.empty) ::
      .ext (.strGrowBuf Algorithm.GrowBuf.empty) ::
      .i64 0 :: .i32 0 :: .i32 0 :: .i32 0 :: .i32 0 :: .i32 0 ::
      .heapRef 0 :: .i32 0 :: .i32 1 :: .i32 numLines :: .strArr lines :: rest,
      locs, jh, hp⟩
      "MacroCellLeanKt" "f_Algorithm_deserializeMacrocell_loop-ocggIy4"
      ("([Ljava/lang/Object;IIZ[BIIIIIJLjava/lang/Object;Ljava/lang/Object;" ++
        "Ljava/lang/Object;Ljava/lang/Object;)Lcom/alexvanyo/composelife/model/MacrocellResult;") =
      Sum.inl (some ⟨pc + 1,
        (encodeMacrocellResult jh (Algorithm.deserializeMacrocell.loop lines numLines 1 false bytes
          0 0 0 0 0 0 Algorithm.GrowBuf.empty Algorithm.GrowBuf.empty
          Algorithm.GrowBuf.empty Algorithm.GrowBuf.empty)).1 :: rest,
        locs,
        (encodeMacrocellResult jh (Algorithm.deserializeMacrocell.loop lines numLines 1 false bytes
          0 0 0 0 0 0 Algorithm.GrowBuf.empty Algorithm.GrowBuf.empty
          Algorithm.GrowBuf.empty Algorithm.GrowBuf.empty)).2,
        hp⟩) := by
  have hm := stepStatic_mcLoop_match pc locs jh hp
    (.ext (.strGrowBuf Algorithm.GrowBuf.empty))
    (.ext (.strGrowBuf Algorithm.GrowBuf.empty))
    (.ext (.strGrowBuf Algorithm.GrowBuf.empty))
    (.ext (.strGrowBuf Algorithm.GrowBuf.empty))
    (.i64 0) (.i32 0) (.i32 0) (.i32 0) (.i32 0) (.i32 0)
    (.heapRef 0) (.i32 0) (.i32 1) (.i32 numLines) (.strArr lines) rest
  have hdb : decodeBytes ⟨pc, .ext (.strGrowBuf Algorithm.GrowBuf.empty) ::
      .ext (.strGrowBuf Algorithm.GrowBuf.empty) ::
      .ext (.strGrowBuf Algorithm.GrowBuf.empty) ::
      .ext (.strGrowBuf Algorithm.GrowBuf.empty) ::
      .i64 0 :: .i32 0 :: .i32 0 :: .i32 0 :: .i32 0 :: .i32 0 ::
      .heapRef 0 :: .i32 0 :: .i32 1 :: .i32 numLines :: .strArr lines :: rest,
      locs, jh, hp⟩ (.heapRef 0) = some bytes := by
    change (match jh.get? 0 with
      | some (.byteArray elems) => some (⟨elems⟩ : ByteArray) | _ => none) = _
    rw [hget]
  have he := mc_match_elim pc locs jh hp _ _ _ _ (.i64 0) (.i32 0) (.i32 0) (.i32 0) (.i32 0)
    (.i32 0) (.heapRef 0) (.i32 0) (.i32 1) (.i32 numLines) (.strArr lines) rest
    Algorithm.deserializeMacrocell.loop encodeMacrocellResult rfl hdb rfl rfl rfl rfl
  have hbool0 : (((0 : UInt32) != 0)) = false := by decide
  have harg : Algorithm.deserializeMacrocell.loop lines
      (Jvm.JvmVal.asI32 (.i32 numLines : JvmVal))
      (Jvm.JvmVal.asI32 (.i32 1 : JvmVal))
      (Jvm.JvmVal.asI32 (.i32 0 : JvmVal) != 0) bytes
      (Jvm.JvmVal.asI32 (.i32 0 : JvmVal))
      (Jvm.JvmVal.asI32 (.i32 0 : JvmVal))
      (Jvm.JvmVal.asI32 (.i32 0 : JvmVal))
      (Jvm.JvmVal.asI32 (.i32 0 : JvmVal))
      (Jvm.JvmVal.asI32 (.i32 0 : JvmVal))
      (Jvm.JvmVal.asI64 (.i64 0 : JvmVal))
      Algorithm.GrowBuf.empty Algorithm.GrowBuf.empty
      Algorithm.GrowBuf.empty Algorithm.GrowBuf.empty =
      Algorithm.deserializeMacrocell.loop lines numLines 1 false bytes
        0 0 0 0 0 0 Algorithm.GrowBuf.empty Algorithm.GrowBuf.empty
        Algorithm.GrowBuf.empty Algorithm.GrowBuf.empty := by
    dsimp only [Jvm.JvmVal.asI32, Jvm.JvmVal.asI64]
    rw [hbool0]
  exact Eq.trans hm (Eq.trans he (mc_enc_state_congr pc locs jh hp rest encodeMacrocellResult _ _ harg))

private theorem step_deserMC_valid (lines : Array String) (hBytes : ByteArray)
    (h1 : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (f : Nat) (locs : Nat → JvmVal)
    (hl0 : locs 0 = .strArr lines) (hl1 : locs 1 = .i32 lines.size.toUInt32)
    (hl3 : locs 3 = .heapRef 0) (hgetBytes : h1.get? 0 = some (.byteArray hBytes.data)) :
    runJvmResFast (f + 30) f_Algorithm_deserializeMacrocell_prog 49
        (f_Algorithm_deserializeMacrocell_prog.drop 49) ⟨49, [], locs, h1, hp⟩ =
      some ((encodeMacrocellResult h1 (Algorithm.deserializeMacrocell.loop lines
          lines.size.toUInt32 1 false hBytes 0 0 0 0 0 0 Algorithm.GrowBuf.empty
          Algorithm.GrowBuf.empty Algorithm.GrowBuf.empty Algorithm.GrowBuf.empty)).1,
        ⟨77, [(encodeMacrocellResult h1 (Algorithm.deserializeMacrocell.loop lines
            lines.size.toUInt32 1 false hBytes 0 0 0 0 0 0 Algorithm.GrowBuf.empty
            Algorithm.GrowBuf.empty Algorithm.GrowBuf.empty Algorithm.GrowBuf.empty)).1],
          setLocal (setLocal (setLocal (setLocal locs
            4 (.ext (.strGrowBuf Algorithm.GrowBuf.empty)))
            5 (.ext (.strGrowBuf Algorithm.GrowBuf.empty)))
            6 (.ext (.strGrowBuf Algorithm.GrowBuf.empty)))
            7 (.ext (.strGrowBuf Algorithm.GrowBuf.empty)),
          (encodeMacrocellResult h1 (Algorithm.deserializeMacrocell.loop lines
            lines.size.toUInt32 1 false hBytes 0 0 0 0 0 0 Algorithm.GrowBuf.empty
            Algorithm.GrowBuf.empty Algorithm.GrowBuf.empty Algorithm.GrowBuf.empty)).2,
          hp⟩) := by
  dsimp only [f_Algorithm_deserializeMacrocell_prog, List.drop]
  step1
  rw [show f + (30 - 1) = (f + 28) + 1 from by omega]
  rw [runJvmResFast_invokestatic_step (stepStatic_growBufEmpty_heap (Or.inr (Or.inl rfl)))]
  step1; step1
  rw [show f + (28 - 1 - 1) = (f + 25) + 1 from by omega]
  rw [runJvmResFast_invokestatic_step (stepStatic_growBufEmpty_heap (Or.inr (Or.inl rfl)))]
  step1; step1
  rw [show f + (25 - 1 - 1) = (f + 22) + 1 from by omega]
  rw [runJvmResFast_invokestatic_step (stepStatic_growBufEmpty_heap (Or.inr (Or.inl rfl)))]
  step1; step1
  rw [show f + (22 - 1 - 1) = (f + 19) + 1 from by omega]
  rw [runJvmResFast_invokestatic_step (stepStatic_growBufEmpty_heap (Or.inr (Or.inl rfl)))]
  step1; step1; rw [hl0]
  step1; rw [hl1]
  step1; step1
  step1; rw [hl3]
  step1; step1; step1; step1; step1; step1; step1; step1; step1; step1
  have hloop := stepStatic_deserMC_loop_empty (pc := 76) (lines := lines)
    (numLines := lines.size.toUInt32) (bytes := hBytes)
    (rest := []) (locs := setLocal (setLocal (setLocal (setLocal locs
      4 (.ext (.strGrowBuf Algorithm.GrowBuf.empty)))
      5 (.ext (.strGrowBuf Algorithm.GrowBuf.empty)))
      6 (.ext (.strGrowBuf Algorithm.GrowBuf.empty)))
      7 (.ext (.strGrowBuf Algorithm.GrowBuf.empty)))
    (hp := hp) hgetBytes
  rw [show f + (19 - 1 - 1 - 1 - 1 - 1 - 1 - 1 - 1 - 1 - 1 - 1 - 1 - 1 - 1 - 1 - 1) =
    (f + 2) + 1 from by omega]
  change runJvmResFast ((f + 2) + 1) f_Algorithm_deserializeMacrocell_prog 76
    (.invokestatic "MacroCellLeanKt" "f_Algorithm_deserializeMacrocell_loop-ocggIy4"
      ("([Ljava/lang/Object;IIZ[BIIIIIJLjava/lang/Object;Ljava/lang/Object;" ++
        "Ljava/lang/Object;Ljava/lang/Object;)Lcom/alexvanyo/composelife/model/MacrocellResult;") ::
      f_Algorithm_deserializeMacrocell_prog.drop 77) _ = _
  refine Eq.trans (runJvmResFast_invokestatic_step hloop) ?_
  dsimp only [f_Algorithm_deserializeMacrocell_prog, List.drop]
  exact runJvmResFast_areturn

private theorem step_deserMC_lt4 (line0 : String) (h1 : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (f : Nat) (locs : Nat → JvmVal) (hlt4 : line0.toByteArray.size.toUInt32 < 4)
    (hloc2 : locs 2 = .str line0)
    (hstat : h1.getStatic? "MacroCellLeanKt" "EMPTY_LEVEL_4" = none) :
    runJvmResFast (f + 29) f_Algorithm_deserializeMacrocell_prog 21
        (f_Algorithm_deserializeMacrocell_prog.drop 21)
        ⟨21, [.i32 line0.toByteArray.size.toUInt32], locs, h1, hp⟩ =
      let enc := encodeMacrocellResult h1 ⟨.invalidHeader line0, #[], Algorithm.emptyLevel4⟩
      some (enc.1, ⟨98, [enc.1],
        setLocal (setLocal (setLocal locs 4 (.heapRef h1.objects.size))
          5 (.heapRef (h1.alloc (.instance
            "com/alexvanyo/composelife/model/MacrocellStatus$InvalidHeader"
            [("line", .str line0)])).2.objects.size))
          7 (.i32 0),
        enc.2, hp⟩) := by
  dsimp only [f_Algorithm_deserializeMacrocell_prog, List.drop]
  step1; step1
  rw [show f + 27 = (f + 26) + 1 from by omega]
  rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned]
  rw [show f + 26 = (f + 25) + 1 from by omega]
  rw [runJvmResFast_iflt_branch (v := _) (by rw [compareUnsigned_slt_zero]; exact decide_eq_true hlt4)]
  exact step_deserMC_invalid line0 h1 hp f [] locs hloc2 hstat

private theorem step_deserMC_ge4 (hBytes : ByteArray) (h1 : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (f : Nat) (locs : Nat → JvmVal) (hlt4 : ¬hBytes.size.toUInt32 < 4) :
    runJvmResFast (f + 4) f_Algorithm_deserializeMacrocell_prog 21
        (f_Algorithm_deserializeMacrocell_prog.drop 21)
        ⟨21, [.i32 hBytes.size.toUInt32], locs, h1, hp⟩ =
      runJvmResFast f f_Algorithm_deserializeMacrocell_prog 25
        (f_Algorithm_deserializeMacrocell_prog.drop 25) ⟨25, [], locs, h1, hp⟩ := by
  dsimp only [f_Algorithm_deserializeMacrocell_prog, List.drop]
  step1; step1
  rw [show f + 2 = (f + 1) + 1 from by omega]
  rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned]
  rw [runJvmResFast_iflt_fallthrough (v := _) (by rw [compareUnsigned_slt_zero]; exact decide_eq_false hlt4)]

private theorem step_deserMC_byte_ne (line0 : String) (hp : AlgHeap) (f pc_b : Nat)
    (idx expected : UInt32) (he : expected.toNat < 128) (rest' : List JvmInstr)
    (locs' : Nat → JvmVal) (hszGe4 : 4 ≤ line0.toByteArray.size) (hidx : idx.toNat < 4)
    (hl2 : locs' 2 = .str line0) (hl3 : locs' 3 = .heapRef ({} : Jvm.JvmHeap AlgExt).objects.size)
    (hne : (line0.toByteArray.get! idx.toNat == UInt8.ofNat expected.toNat) = false) :
    let h1 := (({} : Jvm.JvmHeap AlgExt).alloc (.byteArray line0.toByteArray.data)).2
    runJvmResFast (f + 32) f_Algorithm_deserializeMacrocell_prog pc_b
        (.aload 3 :: .iconst idx :: .baload ::
          .invokestatic "kotlin/UByte" "constructor-impl" "(B)B" ::
          .iconst expected :: .if_icmpne 78 :: rest')
        ⟨pc_b, [], locs', h1, hp⟩ =
      let enc := encodeMacrocellResult h1 ⟨.invalidHeader line0, #[], Algorithm.emptyLevel4⟩
      some (enc.1, ⟨98, [enc.1],
        setLocal (setLocal (setLocal locs' 4 (.heapRef h1.objects.size))
          5 (.heapRef (h1.alloc (.instance
            "com/alexvanyo/composelife/model/MacrocellStatus$InvalidHeader"
            [("line", .str line0)])).2.objects.size))
          7 (.i32 0),
        enc.2, hp⟩) := by
  intro h1
  let hBytes := line0.toByteArray
  have hgetBytes : h1.get? ({} : Jvm.JvmHeap AlgExt).objects.size = some (.byteArray hBytes.data) :=
    jvmHeap_get?_alloc_self _ _
  have hlt_idx : idx.toNat < hBytes.data.size := by
    have hsz : hBytes.data.size = line0.toByteArray.size := rfl; omega
  have hslt_idx : idx.toBitVec.slt 0#32 = false := u32_slt_zero_of_lt_2_31 (by omega)
  have hgb : hBytes.get! idx.toNat = hBytes.data[idx.toNat]'hlt_idx := by
    change hBytes.data[idx.toNat]! = hBytes.data[idx.toNat]'hlt_idx
    exact getElem!_pos hBytes.data idx.toNat hlt_idx
  change (hBytes.get! idx.toNat == UInt8.ofNat expected.toNat) = false at hne
  rw [hgb] at hne
  have hexp32 : UInt32.ofNat expected.toNat = expected := UInt32.ofNat_toNat
  have hneq : (UInt32.ofBitVec ((hBytes.data[idx.toNat]'hlt_idx).toBitVec.signExtend 32) ==
      expected) = false := by
    rw [← hexp32, signExtend_eq_u8 _ _ he]; exact hne
  rw [show f + 32 = (f + 26) + 6 from by omega]
  step1; rw [hl3]; step1
  split_res_fuel 1
  rw [runJvmResFast_baload hgetBytes hslt_idx hlt_idx]
  rw [show f + 26 + 4 - 1 = (f + 26) + 3 from by omega]
  step1; step1
  split_res_fuel 1
  rw [runJvmResFast_if_icmpne_branch hneq]
  rw [show f + 26 = (f + 1) + 25 from by omega]
  exact step_deserMC_invalid line0 h1 hp (f + 1) [] locs' hl2 rfl

private theorem step_deserMC_byte_eq (hBytes : ByteArray) (hp : AlgHeap) (f pc_b : Nat)
    (idx expected : UInt32) (he : expected.toNat < 128) (rest' : List JvmInstr)
    (locs' : Nat → JvmVal) (hszGe4 : 4 ≤ hBytes.size) (hidx : idx.toNat < 4)
    (hl3 : locs' 3 = .heapRef ({} : Jvm.JvmHeap AlgExt).objects.size)
    (heq : (hBytes.get! idx.toNat == UInt8.ofNat expected.toNat) = true) :
    let h1 := (({} : Jvm.JvmHeap AlgExt).alloc (.byteArray hBytes.data)).2
    runJvmResFast (f + 6) f_Algorithm_deserializeMacrocell_prog pc_b
        (.aload 3 :: .iconst idx :: .baload ::
          .invokestatic "kotlin/UByte" "constructor-impl" "(B)B" ::
          .iconst expected :: .if_icmpne 78 :: rest')
        ⟨pc_b, [], locs', h1, hp⟩ =
      runJvmResFast f f_Algorithm_deserializeMacrocell_prog (pc_b + 6) rest'
        ⟨pc_b + 6, [], locs', h1, hp⟩ := by
  intro h1
  have hgetBytes : h1.get? ({} : Jvm.JvmHeap AlgExt).objects.size = some (.byteArray hBytes.data) :=
    jvmHeap_get?_alloc_self _ _
  have hlt_idx : idx.toNat < hBytes.data.size := by change idx.toNat < hBytes.size; omega
  have hslt_idx : idx.toBitVec.slt 0#32 = false := u32_slt_zero_of_lt_2_31 (by omega)
  have hgb : hBytes.get! idx.toNat = hBytes.data[idx.toNat]'hlt_idx := by
    change hBytes.data[idx.toNat]! = hBytes.data[idx.toNat]'hlt_idx
    exact getElem!_pos hBytes.data idx.toNat hlt_idx
  rw [hgb] at heq
  have hexp32 : UInt32.ofNat expected.toNat = expected := UInt32.ofNat_toNat
  have hveq : UInt32.ofBitVec ((hBytes.data[idx.toNat]'hlt_idx).toBitVec.signExtend 32) =
      expected := by
    have hb := signExtend_eq_u8 (hBytes.data[idx.toNat]'hlt_idx) expected.toNat he
    rw [heq] at hb
    rw [← hexp32]
    exact of_decide_eq_true (by simpa [BEq.beq] using hb)
  step1; rw [hl3]; step1
  split_res_fuel 1
  rw [runJvmResFast_baload hgetBytes hslt_idx hlt_idx]
  rw [show f + 4 - 1 = f + 3 from by omega]
  step1; step1
  split_res_fuel 1
  rw [runJvmResFast_if_icmpne_fallthrough hveq]
  rfl

private theorem deserMC_drop25_49 :
    f_Algorithm_deserializeMacrocell_prog.drop 25 =
      .aload 3 :: .iconst 0 :: .baload ::
        .invokestatic "kotlin/UByte" "constructor-impl" "(B)B" :: .iconst 91 :: .if_icmpne 78 ::
      .aload 3 :: .iconst 1 :: .baload ::
        .invokestatic "kotlin/UByte" "constructor-impl" "(B)B" :: .iconst 77 :: .if_icmpne 78 ::
      .aload 3 :: .iconst 2 :: .baload ::
        .invokestatic "kotlin/UByte" "constructor-impl" "(B)B" :: .iconst 50 :: .if_icmpne 78 ::
      .aload 3 :: .iconst 3 :: .baload ::
        .invokestatic "kotlin/UByte" "constructor-impl" "(B)B" :: .iconst 93 :: .if_icmpne 78 ::
      f_Algorithm_deserializeMacrocell_prog.drop 49 := rfl

private theorem deserMC_drop25_43 :
    f_Algorithm_deserializeMacrocell_prog.drop 25 =
      .aload 3 :: .iconst 0 :: .baload ::
        .invokestatic "kotlin/UByte" "constructor-impl" "(B)B" :: .iconst 91 :: .if_icmpne 78 ::
      .aload 3 :: .iconst 1 :: .baload ::
        .invokestatic "kotlin/UByte" "constructor-impl" "(B)B" :: .iconst 77 :: .if_icmpne 78 ::
      .aload 3 :: .iconst 2 :: .baload ::
        .invokestatic "kotlin/UByte" "constructor-impl" "(B)B" :: .iconst 50 :: .if_icmpne 78 ::
      f_Algorithm_deserializeMacrocell_prog.drop 43 := rfl

private theorem deserMC_drop25_37 :
    f_Algorithm_deserializeMacrocell_prog.drop 25 =
      .aload 3 :: .iconst 0 :: .baload ::
        .invokestatic "kotlin/UByte" "constructor-impl" "(B)B" :: .iconst 91 :: .if_icmpne 78 ::
      .aload 3 :: .iconst 1 :: .baload ::
        .invokestatic "kotlin/UByte" "constructor-impl" "(B)B" :: .iconst 77 :: .if_icmpne 78 ::
      f_Algorithm_deserializeMacrocell_prog.drop 37 := rfl

private theorem deserMC_drop25_31 :
    f_Algorithm_deserializeMacrocell_prog.drop 25 =
      .aload 3 :: .iconst 0 :: .baload ::
        .invokestatic "kotlin/UByte" "constructor-impl" "(B)B" :: .iconst 91 :: .if_icmpne 78 ::
      f_Algorithm_deserializeMacrocell_prog.drop 31 := rfl

private theorem deserMC_empty_case (lines : Array String) (hp : AlgHeap)
    (hnum : (lines.size.toUInt32 == 0) = true) :
    ∃ v st',
      runJvmRes 120 f_Algorithm_deserializeMacrocell_prog
          ⟨0, [], setLocal (fun _ => .null) 0 (.strArr lines), ({} : Jvm.JvmHeap AlgExt), hp⟩ =
        some (v, st') ∧
      decodeMacrocellResult st' v = some (Algorithm.deserializeMacrocell lines) ∧
      st'.heap = hp := by
  let jh0 : Jvm.JvmHeap AlgExt := {}
  let locs0 : Nat → JvmVal := setLocal (fun _ => .null) 0 (.strArr lines)
  have heq : Algorithm.deserializeMacrocell lines = ⟨.emptyFile, #[.emptyFile], Algorithm.emptyLevel4⟩ := by
    simp [Algorithm.deserializeMacrocell, hnum]
  rw [heq]
  let enc := encodeMacrocellResult jh0 ⟨.emptyFile, #[.emptyFile], Algorithm.emptyLevel4⟩
  have hrun : runJvmRes 120 f_Algorithm_deserializeMacrocell_prog ⟨0, [], locs0, jh0, hp⟩ =
      some (enc.1, ⟨100, [enc.1], setLocal locs0 1 (.i32 lines.size.toUInt32), enc.2, hp⟩) := by
    apply runJvmRes_of_runJvmResFast0 120 _ _ _ rfl
    rw [show (120 : Nat) = 100 + 20 from rfl]
    dsimp only [f_Algorithm_deserializeMacrocell_prog]
    step1; step1; step1; step1; step1; step1; step1; step1
    rw [show (100 + 12 : Nat) = 111 + 1 from rfl]
    rw [runJvmResFast_ifeq_branch (by simpa [beq_iff_eq] using hnum)]
    dsimp only [f_Algorithm_deserializeMacrocell_prog, List.drop]
    rw [show (111 : Nat) = 109 + 2 from rfl]
    step1
    exact runJvmResFast_areturn
  exact ⟨_, _, hrun, decodeMacrocellResult_encode jh0 hp ⟨.emptyFile, #[.emptyFile], Algorithm.emptyLevel4⟩, rfl⟩

private theorem deserMC_ih_from21 (lines : Array String) (hp : AlgHeap)
    (hnumF : (lines.size.toUInt32 == 0) = false) (hszPos : 0 < lines.size)
    (hbad : (lines[0]!.toByteArray.size.toUInt32 < 4 || lines[0]!.toByteArray.get! 0 != 91 ||
      lines[0]!.toByteArray.get! 1 != 77 || lines[0]!.toByteArray.get! 2 != 50 ||
      lines[0]!.toByteArray.get! 3 != 93) = true)
    (h21 : let line0 := lines[0]!
      let jh0 : Jvm.JvmHeap AlgExt := {}
      let h1 := (jh0.alloc (.byteArray line0.toByteArray.data)).2
      let locs0 : Nat → JvmVal := setLocal (fun _ => .null) 0 (.strArr lines)
      let locs21 := setLocal (setLocal (setLocal locs0 1 (.i32 lines.size.toUInt32)) 2 (.str line0))
        3 (.heapRef jh0.objects.size)
      let encIH := encodeMacrocellResult h1 ⟨.invalidHeader line0, #[], Algorithm.emptyLevel4⟩
      let locsIH := setLocal (setLocal (setLocal locs21 4 (.heapRef h1.objects.size))
        5 (.heapRef (h1.alloc (.instance
          "com/alexvanyo/composelife/model/MacrocellStatus$InvalidHeader"
          [("line", .str line0)])).2.objects.size))
        7 (.i32 0)
      runJvmResFast 99 f_Algorithm_deserializeMacrocell_prog 21
          (f_Algorithm_deserializeMacrocell_prog.drop 21)
          ⟨21, [.i32 line0.toByteArray.size.toUInt32], locs21, h1, hp⟩ =
        some (encIH.1, ⟨98, [encIH.1], locsIH, encIH.2, hp⟩)) :
    ∃ v st',
      runJvmRes 120 f_Algorithm_deserializeMacrocell_prog
          ⟨0, [], setLocal (fun _ => .null) 0 (.strArr lines), ({} : Jvm.JvmHeap AlgExt), hp⟩ =
        some (v, st') ∧
      decodeMacrocellResult st' v = some (Algorithm.deserializeMacrocell lines) ∧
      st'.heap = hp := by
  let line0 := lines[0]!
  let jh0 : Jvm.JvmHeap AlgExt := {}
  let h1 := (jh0.alloc (.byteArray line0.toByteArray.data)).2
  let ihRes : Algorithm.MacrocellResult := ⟨.invalidHeader line0, #[], Algorithm.emptyLevel4⟩
  have hbadEq : Algorithm.deserializeMacrocell lines = ihRes := by
    dsimp only [Algorithm.deserializeMacrocell]
    rw [show (lines.size.toUInt32 == 0) = false from hnumF]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show (lines[0]!.toByteArray.size.toUInt32 < 4 ||
        lines[0]!.toByteArray.get! 0 != 91 || lines[0]!.toByteArray.get! 1 != 77 ||
        lines[0]!.toByteArray.get! 2 != 50 || lines[0]!.toByteArray.get! 3 != 93) = true from hbad]
    simp [line0, ihRes]
  rw [hbadEq]
  apply Exists.intro
  apply Exists.intro
  refine And.intro ?_ (And.intro ?_ ?_)
  · apply runJvmRes_of_runJvmResFast0 120 _ _ _ rfl
    rw [show (120 : Nat) = 99 + 21 from by omega, step_deserMC_pre lines hp 99 hnumF hszPos]
    exact h21
  · exact decodeMacrocellResult_encode h1 hp ihRes
  · rfl

private theorem decodeMacrocellResult_state_congr {st1 st2 : JvmState} {v1 v2 : JvmVal}
    (hjh : st1.jvmHeap = st2.jvmHeap) (hv : v1 = v2) :
    decodeMacrocellResult st1 v1 = decodeMacrocellResult st2 v2 := by
  cases st1; cases st2; dsimp only at hjh; subst hjh; subst hv; rfl

private theorem mc_equiv_finish
    (prog : List JvmInstr) (st0 : JvmState) (fuel : Nat)
    (enc : JvmVal × Jvm.JvmHeap AlgExt) (hp : AlgHeap) (res : Algorithm.MacrocellResult)
    (hrun : ∃ (pc' : Nat) (stk' : List JvmVal) (locs' : Nat → JvmVal),
      runJvmRes fuel prog st0 = some (enc.1, ⟨pc', stk', locs', enc.2, hp⟩))
    (hdec : decodeMacrocellResult ⟨0, [], fun _ => .null, enc.2, hp⟩ enc.1 = some res) :
    ∃ v st', runJvmRes fuel prog st0 = some (v, st') ∧
      decodeMacrocellResult st' v = some res ∧ st'.heap = hp := by
  rcases hrun with ⟨pc', stk', locs', hrun'⟩
  refine ⟨enc.1, ⟨pc', stk', locs', enc.2, hp⟩, hrun', ?_, rfl⟩
  rw [decodeMacrocellResult_state_congr (st1 := ⟨pc', stk', locs', enc.2, hp⟩)
    (st2 := ⟨0, [], fun _ => .null, enc.2, hp⟩) (v1 := enc.1) (v2 := enc.1) rfl rfl]
  exact hdec

private theorem deserMC_valid_case (lines : Array String) (hp : AlgHeap)
    (hnumF : (lines.size.toUInt32 == 0) = false) (hszPos : 0 < lines.size)
    (hszGe4 : 4 ≤ lines[0]!.toByteArray.size)
    (hlt4 : ¬(lines[0]!.toByteArray.size.toUInt32 < 4))
    (hb0 : lines[0]!.toByteArray.get! 0 == 91) (hb1 : lines[0]!.toByteArray.get! 1 == 77)
    (hb2 : lines[0]!.toByteArray.get! 2 == 50) (hb3 : lines[0]!.toByteArray.get! 3 == 93) :
    ∃ v st',
      runJvmRes 120 f_Algorithm_deserializeMacrocell_prog
          ⟨0, [], setLocal (fun _ => .null) 0 (.strArr lines), ({} : Jvm.JvmHeap AlgExt), hp⟩ =
        some (v, st') ∧
      decodeMacrocellResult st' v = some (Algorithm.deserializeMacrocell lines) ∧
      st'.heap = hp := by
  let line0 := lines[0]!
  let hBytes := line0.toByteArray
  let jh0 : Jvm.JvmHeap AlgExt := {}
  let h1 := (jh0.alloc (.byteArray hBytes.data)).2
  let locs0 : Nat → JvmVal := setLocal (fun _ => .null) 0 (.strArr lines)
  let locs21 := setLocal (setLocal (setLocal locs0 1 (.i32 lines.size.toUInt32)) 2 (.str line0))
    3 (.heapRef jh0.objects.size)
  have hne4d : decide (hBytes.size.toUInt32 < 4) = false := decide_eq_false hlt4
  have hgood : (hBytes.size.toUInt32 < 4 || hBytes.get! 0 != 91 || hBytes.get! 1 != 77 ||
      hBytes.get! 2 != 50 || hBytes.get! 3 != 93) = false := by
    rw [hne4d]
    have h0 : (hBytes.get! 0 != 91) = false := by simp [bne, hb0, hBytes, line0]
    have h1' : (hBytes.get! 1 != 77) = false := by simp [bne, hb1, hBytes, line0]
    have h2 : (hBytes.get! 2 != 50) = false := by simp [bne, hb2, hBytes, line0]
    have h3 : (hBytes.get! 3 != 93) = false := by simp [bne, hb3, hBytes, line0]
    rw [h0, h1', h2, h3]
    rfl
  have hresEq : Algorithm.deserializeMacrocell lines =
      Algorithm.deserializeMacrocell.loop lines lines.size.toUInt32 1 false hBytes
        0 0 0 0 0 0 Algorithm.GrowBuf.empty Algorithm.GrowBuf.empty
        Algorithm.GrowBuf.empty Algorithm.GrowBuf.empty := by
    dsimp only [Algorithm.deserializeMacrocell]
    simp [hnumF, show lines[0]!.toByteArray = hBytes from rfl, hgood, line0]
  rw [hresEq]
  refine mc_equiv_finish f_Algorithm_deserializeMacrocell_prog ⟨0, [], locs0, jh0, hp⟩ 120
    (encodeMacrocellResult h1 _) hp _ ?_ (decodeMacrocellResult_encode h1 hp _)
  apply Exists.intro
  apply Exists.intro
  apply Exists.intro
  apply runJvmRes_of_runJvmResFast0 120 _ _ _ rfl
  rw [show (120 : Nat) = 99 + 21 from by omega, step_deserMC_pre lines hp 99 hnumF hszPos]
  rw [show (99 : Nat) = 95 + 4 from by omega, step_deserMC_ge4 hBytes h1 hp 95 locs21 hlt4]
  rw [deserMC_drop25_49, show (95 : Nat) = (65 + 24) + 6 from by omega]
  rw [step_deserMC_byte_eq hBytes hp (65 + 24) 25 0 91 (by decide) _ locs21 hszGe4 (by decide) rfl hb0]
  rw [show 65 + 24 = (65 + 18) + 6 from by omega]
  rw [step_deserMC_byte_eq hBytes hp (65 + 18) 31 1 77 (by decide) _ locs21 hszGe4 (by decide) rfl hb1]
  rw [show 65 + 18 = (65 + 12) + 6 from by omega]
  rw [step_deserMC_byte_eq hBytes hp (65 + 12) 37 2 50 (by decide) _ locs21 hszGe4 (by decide) rfl hb2]
  rw [show 65 + 12 = (65 + 6) + 6 from by omega]
  rw [step_deserMC_byte_eq hBytes hp (65 + 6) 43 3 93 (by decide) _ locs21 hszGe4 (by decide) rfl hb3]
  rw [show 25 + 6 + 6 + 6 + 6 = 49 from by omega, show (65 + 6 : Nat) = 41 + 30 from by omega]
  exact step_deserMC_valid lines hBytes h1 hp 41 locs21 rfl rfl rfl (jvmHeap_get?_alloc_self _ _)

theorem deserializeMacrocell_equiv (lines : Array String) (hp : AlgHeap) :
    ∃ v st',
      runJvmRes 120 f_Algorithm_deserializeMacrocell_prog
          ⟨0, [], setLocal (fun _ => .null) 0 (.strArr lines), ({} : Jvm.JvmHeap AlgExt), hp⟩ =
        some (v, st') ∧
      decodeMacrocellResult st' v = some (Algorithm.deserializeMacrocell lines) ∧
      st'.heap = hp := by
  by_cases hnum : lines.size.toUInt32 == 0
  · exact deserMC_empty_case lines hp hnum
  · have hnumF : (lines.size.toUInt32 == 0) = false := Bool.eq_false_iff.mpr hnum
    have hne0 : lines.size.toUInt32 ≠ 0 := by simpa [beq_iff_eq] using hnum
    have hszPos : 0 < lines.size := Nat.pos_of_ne_zero (fun hz => hne0 (by simp [hz]))
    let line0 := lines[0]!
    let hBytes := line0.toByteArray
    let h1 := (({} : Jvm.JvmHeap AlgExt).alloc (.byteArray hBytes.data)).2
    let locs21 := setLocal (setLocal (setLocal (setLocal (fun _ => (.null : JvmVal)) 0 (.strArr lines))
      1 (.i32 lines.size.toUInt32)) 2 (.str line0)) 3 (.heapRef ({} : Jvm.JvmHeap AlgExt).objects.size)
    by_cases hlt4 : hBytes.size.toUInt32 < 4
    · exact deserMC_ih_from21 lines hp hnumF hszPos
        (by have ht : decide (lines[0]!.toByteArray.size.toUInt32 < 4) = true := decide_eq_true hlt4
            rw [ht]; rfl)
        (by rw [show (99 : Nat) = 70 + 29 from by omega]; exact step_deserMC_lt4 line0 h1 hp 70 locs21 hlt4 rfl rfl)
    · have hge4 : 4 ≤ hBytes.size.toUInt32.toNat := by
        have hnl := mt UInt32.lt_iff_toNat_lt.mpr hlt4
        simp only [show (4 : UInt32).toNat = 4 from rfl] at hnl; omega
      have hszGe4 : 4 ≤ hBytes.size := by
        have hm : hBytes.size.toUInt32.toNat ≤ hBytes.size := by
          change hBytes.size % 2 ^ 32 ≤ hBytes.size; exact Nat.mod_le _ _
        omega
      have hge4Run : runJvmResFast 99 f_Algorithm_deserializeMacrocell_prog 21
          (f_Algorithm_deserializeMacrocell_prog.drop 21)
          ⟨21, [.i32 hBytes.size.toUInt32], locs21, h1, hp⟩ =
          runJvmResFast 95 f_Algorithm_deserializeMacrocell_prog 25
            (f_Algorithm_deserializeMacrocell_prog.drop 25) ⟨25, [], locs21, h1, hp⟩ := by
        rw [show (99 : Nat) = 95 + 4 from by omega]; exact step_deserMC_ge4 hBytes h1 hp 95 locs21 hlt4
      have hge4Run' := hge4Run
      dsimp only [hBytes, line0, locs21, h1] at hge4Run'
      by_cases hb0 : hBytes.get! 0 == 91
      · by_cases hb1 : hBytes.get! 1 == 77
        · by_cases hb2 : hBytes.get! 2 == 50
          · by_cases hb3 : hBytes.get! 3 == 93
            · exact deserMC_valid_case lines hp hnumF hszPos hszGe4 hlt4 hb0 hb1 hb2 hb3
            · refine deserMC_ih_from21 lines hp hnumF hszPos
                (by have hb : (lines[0]!.toByteArray.get! 3 != 93) = true := by
                      simp [bne, Bool.eq_false_iff.mpr hb3, hBytes, line0]
                    rw [hb]; simp) ?_
              dsimp only
              rw [hge4Run', deserMC_drop25_49, show (95 : Nat) = (65 + 24) + 6 from by omega]
              rw [step_deserMC_byte_eq hBytes hp (65 + 24) 25 0 91 (by decide) _ locs21 hszGe4 (by decide) rfl hb0]
              rw [show 65 + 24 = (65 + 18) + 6 from by omega]
              rw [step_deserMC_byte_eq hBytes hp (65 + 18) 31 1 77 (by decide) _ locs21 hszGe4 (by decide) rfl hb1]
              rw [show 65 + 18 = (65 + 12) + 6 from by omega]
              rw [step_deserMC_byte_eq hBytes hp (65 + 12) 37 2 50 (by decide) _ locs21 hszGe4 (by decide) rfl hb2]
              rw [show 65 + 12 = 45 + 32 from by omega, show 25 + 6 + 6 + 6 = 43 from by omega]
              exact step_deserMC_byte_ne line0 hp 45 43 3 93 (by decide) _ locs21
                hszGe4 (by decide) rfl rfl (Bool.eq_false_iff.mpr hb3)
          · refine deserMC_ih_from21 lines hp hnumF hszPos
              (by have hb : (lines[0]!.toByteArray.get! 2 != 50) = true := by
                    simp [bne, Bool.eq_false_iff.mpr hb2, hBytes, line0]
                  rw [hb]; simp) ?_
            dsimp only
            rw [hge4Run', deserMC_drop25_43, show (95 : Nat) = (65 + 24) + 6 from by omega]
            rw [step_deserMC_byte_eq hBytes hp (65 + 24) 25 0 91 (by decide) _ locs21 hszGe4 (by decide) rfl hb0]
            rw [show 65 + 24 = (65 + 18) + 6 from by omega]
            rw [step_deserMC_byte_eq hBytes hp (65 + 18) 31 1 77 (by decide) _ locs21 hszGe4 (by decide) rfl hb1]
            rw [show 65 + 18 = 51 + 32 from by omega, show 25 + 6 + 6 = 37 from by omega]
            exact step_deserMC_byte_ne line0 hp 51 37 2 50 (by decide) _ locs21
              hszGe4 (by decide) rfl rfl (Bool.eq_false_iff.mpr hb2)
        · refine deserMC_ih_from21 lines hp hnumF hszPos
            (by have hb : (lines[0]!.toByteArray.get! 1 != 77) = true := by
                  simp [bne, Bool.eq_false_iff.mpr hb1, hBytes, line0]
                rw [hb]; simp) ?_
          dsimp only
          rw [hge4Run', deserMC_drop25_37, show (95 : Nat) = (65 + 24) + 6 from by omega]
          rw [step_deserMC_byte_eq hBytes hp (65 + 24) 25 0 91 (by decide) _ locs21 hszGe4 (by decide) rfl hb0]
          rw [show 65 + 24 = 57 + 32 from by omega, show 25 + 6 = 31 from by omega]
          exact step_deserMC_byte_ne line0 hp 57 31 1 77 (by decide) _ locs21
            hszGe4 (by decide) rfl rfl (Bool.eq_false_iff.mpr hb1)
      · refine deserMC_ih_from21 lines hp hnumF hszPos
          (by have hb : (lines[0]!.toByteArray.get! 0 != 91) = true := by
                simp [bne, Bool.eq_false_iff.mpr hb0, hBytes, line0]
              rw [hb]; simp) ?_
        dsimp only
        rw [hge4Run', deserMC_drop25_31, show (95 : Nat) = 63 + 32 from by omega]
        exact step_deserMC_byte_ne line0 hp 63 25 0 91 (by decide) _ locs21
          hszGe4 (by decide) rfl rfl (Bool.eq_false_iff.mpr hb0)

/-! ### parseMCNodeLine -/

private theorem stepStatic_skipSpaces {pc : Nat} {lim pos : JvmVal} {addr : Nat}
    {rest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {elems : Array UInt8} (hget : jh.get? addr = some (.byteArray elems)) :
    stepInvokeStatic ⟨pc, lim :: pos :: .heapRef addr :: rest, locs, jh, hp⟩
      "MacroCellLeanKt" "f_Algorithm_skipSpaces-BltQuoY" "([BII)I" =
      .inl (some ⟨pc + 1, .i32 (Algorithm.skipSpaces ⟨elems⟩ pos.asI32 lim.asI32) :: rest,
        locs, jh, hp⟩) := by
  change (match decodeBytes ⟨pc, lim :: pos :: .heapRef addr :: rest, locs, jh, hp⟩
      (.heapRef addr) with
    | some bytes => Sum.inl (some (⟨pc + 1,
        .i32 (Algorithm.skipSpaces bytes pos.asI32 lim.asI32) :: rest, locs, jh, hp⟩ : JvmState))
    | none => Sum.inr none) = _
  simp only [decodeBytes, hget]

private theorem stepStatic_parseUInt32At {pc : Nat} {lim pos : JvmVal} {addr : Nat}
    {rest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {elems : Array UInt8} (hget : jh.get? addr = some (.byteArray elems)) :
    stepInvokeStatic ⟨pc, lim :: pos :: .heapRef addr :: rest, locs, jh, hp⟩
      "MacroCellLeanKt" "f_Algorithm_parseUInt32At-BltQuoY" "([BII)Ljava/lang/Object;" =
      let optPair := (Algorithm.parseUInt32At ⟨elems⟩ pos.asI32 lim.asI32).map fun r =>
        (.boxedUInt r.val, .boxedUInt r.next)
      let (res, h') := encodeOptScalarPair jh optPair
      .inl (some ⟨pc + 1, res :: rest, locs, h', hp⟩) := by
  change (match decodeBytes ⟨pc, lim :: pos :: .heapRef addr :: rest, locs, jh, hp⟩
      (.heapRef addr) with
    | some bytes =>
      let optPair := (Algorithm.parseUInt32At bytes pos.asI32 lim.asI32).map
        fun (r : ParsedUInt32) => (JvmVal.boxedUInt r.val, JvmVal.boxedUInt r.next)
      let (res, h') := encodeOptScalarPair jh optPair
      Sum.inl (some (⟨pc + 1, res :: rest, locs, h', hp⟩ : JvmState))
    | none => Sum.inr none) = _
  simp only [decodeBytes, hget]

private theorem step_parseMC_none_ret {f pc tmp out : Nat} {rest : List JvmInstr}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    let arr0 := Array.replicate (1 : UInt32).toNat (JvmVal.null : JvmVal)
    let (_, h1) := jh.alloc (.objArray "java/lang/Object" arr0)
    let h2 := h1.set jh.objects.size (.objArray "java/lang/Object"
      (arr0.set (0 : UInt32).toNat (.boxedInt 0) (by decide)))
    runJvmResFast (f + 12) f_Algorithm_parseMCNodeLine_prog pc
        (.iconst 1 :: .anewarray "java/lang/Object" :: .astore tmp :: .aload tmp ::
          .iconst 0 :: .iconst 0 ::
          .invokestatic "java/lang/Integer" "valueOf" "(I)Ljava/lang/Integer;" ::
          .aastore :: .aload tmp :: .astore out :: .aload out :: .areturn :: rest)
        ⟨pc, [], locs, jh, hp⟩ =
      some (.heapRef jh.objects.size,
        ⟨pc + 11, [.heapRef jh.objects.size],
          setLocal (setLocal locs tmp (.heapRef jh.objects.size)) out (.heapRef jh.objects.size),
          h2, hp⟩) := by
  dsimp only
  step1
  rw [runJvmResFast_anewarray_obj (by decide)]
  step1; step1; step1; step1; step1
  dsimp only [setLocal]
  simp only [↓reduceIte]
  have hget : (jh.alloc (.objArray "java/lang/Object"
      (Array.replicate (1 : UInt32).toNat (JvmVal.null : JvmVal)))).2.get? jh.objects.size =
      some (.objArray "java/lang/Object" (Array.replicate (1 : UInt32).toNat (JvmVal.null : JvmVal))) :=
    jvmHeap_get?_alloc_self _ _
  rw [runJvmResFast_aastore hget (by decide) (by simp)]
  step1; step1; step1
  dsimp only [setLocal]; simp only [↓reduceIte]
  exact runJvmResFast_areturn

private theorem step_parseMC_unbox_uint {f pc : Nat} {arrLoc : Nat} {idx : UInt32}
    {tmp1 tmp2 : Nat} {rest : List JvmInstr} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {arrAddr : Nat} {elems : Array JvmVal} {u : UInt32}
    (hne : tmp1 ≠ tmp2)
    (hl : locs arrLoc = .heapRef arrAddr)
    (hget : jh.get? arrAddr = some (.objArray "java/lang/Object" elems))
    (hslt : idx.toBitVec.slt 0#32 = false) (hlt : idx.toNat < elems.size)
    (helem : elems[idx.toNat]'hlt = .boxedUInt u)
    (hdrop : f_Algorithm_parseMCNodeLine_prog.drop (pc + 15) =
      .aload tmp1 :: .ldcStr "null cannot be cast to non-null type kotlin.UInt" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .aload tmp1 :: .checkcast "kotlin/UInt" ::
      .invokevirtual "kotlin/UInt" "unbox-impl" "()I" :: rest) :
    runJvmResFast (f + 16) f_Algorithm_parseMCNodeLine_prog pc
        (.aload arrLoc :: .checkcast "[Ljava/lang/Object;" :: .iconst idx :: .aaload ::
          .astore tmp1 :: .iconst 0 :: .istore tmp2 ::
          .aload tmp1 :: .instanceof "java/lang/Integer" :: .ifeq (pc + 15) ::
          .aload tmp1 :: .checkcast "java/lang/Number" ::
          .invokevirtual "java/lang/Number" "intValue" "()I" ::
          .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" :: .goto (pc + 21) ::
          .aload tmp1 :: .ldcStr "null cannot be cast to non-null type kotlin.UInt" ::
          .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
            "(Ljava/lang/Object;Ljava/lang/String;)V" ::
          .aload tmp1 :: .checkcast "kotlin/UInt" ::
          .invokevirtual "kotlin/UInt" "unbox-impl" "()I" :: rest)
        ⟨pc, stkRest, locs, jh, hp⟩ =
      runJvmResFast f f_Algorithm_parseMCNodeLine_prog (pc + 21) rest
        ⟨pc + 21, .i32 u :: stkRest,
          setLocal (setLocal locs tmp1 (.boxedUInt u)) tmp2 (.i32 0), jh, hp⟩ := by
  step1
  rw [hl]
  rw [runJvmResFast_checkcast_objArray hget (Or.inl rfl)]
  step1
  rw [runJvmResFast_aaload hget hslt hlt, helem]
  step1; step1; step1; step1
  simp only [setLocal, hne, ↓reduceIte]
  rw [runJvmResFast_instanceof_boxedUInt_int]
  rw [runJvmResFast_ifeq_branch rfl, hdrop]
  step1; step1
  simp only [setLocal, hne, ↓reduceIte]
  rw [runJvmResFast_checkNotNull_nonnull (by intro h; cases h)]
  step1
  simp only [setLocal, hne, ↓reduceIte]
  rw [runJvmResFast_checkcast_boxedUInt (Or.inl rfl)]
  step1

private theorem step_parseMC_dispatch_none {f pc : Nat} {resLoc noneT someT defT tmp out : Nat}
    {rest restNone : List JvmInstr} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {outerAddr : Nat}
    (hl : locs resLoc = .heapRef outerAddr)
    (hget : jh.get? outerAddr = some (.objArray "java/lang/Object" #[.boxedInt 0]))
    (hdrop : f_Algorithm_parseMCNodeLine_prog.drop noneT =
      .iconst 1 :: .anewarray "java/lang/Object" :: .astore tmp :: .aload tmp ::
      .iconst 0 :: .iconst 0 ::
      .invokestatic "java/lang/Integer" "valueOf" "(I)Ljava/lang/Integer;" ::
      .aastore :: .aload tmp :: .astore out :: .aload out :: .areturn :: restNone) :
    let arr0 := Array.replicate (1 : UInt32).toNat (JvmVal.null : JvmVal)
    let (_, h1) := jh.alloc (.objArray "java/lang/Object" arr0)
    let h2 := h1.set jh.objects.size (.objArray "java/lang/Object"
      (arr0.set (0 : UInt32).toNat (.boxedInt 0) (by decide)))
    runJvmResFast (f + 25) f_Algorithm_parseMCNodeLine_prog pc
        (.aload resLoc :: .ldcStr "null cannot be cast to non-null type kotlin.Array<*>" ::
          .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
            "(Ljava/lang/Object;Ljava/lang/String;)V" ::
          .aload resLoc :: .checkcast "[Ljava/lang/Object;" :: .iconst 0 :: .aaload ::
          .dup :: .ldcStr "null cannot be cast to non-null type kotlin.Int" ::
          .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
            "(Ljava/lang/Object;Ljava/lang/String;)V" ::
          .checkcast "java/lang/Integer" ::
          .invokevirtual "java/lang/Integer" "intValue" "()I" ::
          .tableswitch 0 [noneT, someT] defT :: rest)
        ⟨pc, [], locs, jh, hp⟩ =
      some (.heapRef jh.objects.size,
        ⟨noneT + 11, [.heapRef jh.objects.size],
          setLocal (setLocal locs tmp (.heapRef jh.objects.size)) out (.heapRef jh.objects.size),
          h2, hp⟩) := by
  dsimp only
  step1; rw [hl]; step1
  rw [runJvmResFast_checkNotNull_nonnull (by intro h; cases h)]
  step1; rw [hl]
  rw [runJvmResFast_checkcast_objArray hget (Or.inl rfl)]
  step1
  rw [runJvmResFast_aaload hget (by decide) (by decide),
    show (#[JvmVal.boxedInt 0])[(0 : UInt32).toNat] = .boxedInt 0 from rfl]
  step1; step1
  rw [runJvmResFast_checkNotNull_nonnull (by intro h; cases h)]
  rw [runJvmResFast_checkcast_boxedInt (Or.inl rfl)]
  rw [runJvmResFast_invokevirtual_step stepVirtual_integer_intValue]
  rw [runJvmResFast_tableswitch,
    show Jvm.tableswitchTarget (JvmVal.i32 0).asI32 0 [noneT, someT] defT = noneT from rfl]
  dsimp only
  rw [hdrop]
  exact step_parseMC_none_ret

private theorem step_parseMC_dispatch_some {f pc : Nat} {resLoc noneT someT defT innerLoc : Nat}
    {rest restSome : List JvmInstr} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {outerAddr innerAddr : Nat}
    (hl : locs resLoc = .heapRef outerAddr)
    (hget : jh.get? outerAddr = some (.objArray "java/lang/Object" #[.boxedInt 1, .heapRef innerAddr]))
    (hdrop : f_Algorithm_parseMCNodeLine_prog.drop someT =
      .aload resLoc :: .checkcast "[Ljava/lang/Object;" :: .iconst 1 :: .aaload ::
      .astore innerLoc :: .aload innerLoc ::
      .ldcStr "null cannot be cast to non-null type kotlin.Array<*>" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
        "(Ljava/lang/Object;Ljava/lang/String;)V" :: restSome) :
    runJvmResFast (f + 21) f_Algorithm_parseMCNodeLine_prog pc
        (.aload resLoc :: .ldcStr "null cannot be cast to non-null type kotlin.Array<*>" ::
          .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
            "(Ljava/lang/Object;Ljava/lang/String;)V" ::
          .aload resLoc :: .checkcast "[Ljava/lang/Object;" :: .iconst 0 :: .aaload ::
          .dup :: .ldcStr "null cannot be cast to non-null type kotlin.Int" ::
          .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
            "(Ljava/lang/Object;Ljava/lang/String;)V" ::
          .checkcast "java/lang/Integer" ::
          .invokevirtual "java/lang/Integer" "intValue" "()I" ::
          .tableswitch 0 [noneT, someT] defT :: rest)
        ⟨pc, [], locs, jh, hp⟩ =
      runJvmResFast f f_Algorithm_parseMCNodeLine_prog (someT + 8) restSome
        ⟨someT + 8, [], setLocal locs innerLoc (.heapRef innerAddr), jh, hp⟩ := by
  step1; rw [hl]; step1
  rw [runJvmResFast_checkNotNull_nonnull (by intro h; cases h)]
  step1; rw [hl]
  rw [runJvmResFast_checkcast_objArray hget (Or.inl rfl)]
  step1
  rw [runJvmResFast_aaload hget (by decide) (by simp),
    show (#[JvmVal.boxedInt 1, .heapRef innerAddr])[(0 : UInt32).toNat] = .boxedInt 1 from rfl]
  step1; step1
  rw [runJvmResFast_checkNotNull_nonnull (by intro h; cases h)]
  rw [runJvmResFast_checkcast_boxedInt (Or.inl rfl)]
  rw [runJvmResFast_invokevirtual_step stepVirtual_integer_intValue]
  rw [runJvmResFast_tableswitch,
    show Jvm.tableswitchTarget (JvmVal.i32 1).asI32 0 [noneT, someT] defT = someT from rfl]
  dsimp only
  rw [hdrop]
  step1; rw [hl]
  rw [runJvmResFast_checkcast_objArray hget (Or.inl rfl)]
  step1
  rw [runJvmResFast_aaload hget (by decide) (by simp),
    show (#[JvmVal.boxedInt 1, .heapRef innerAddr])[(1 : UInt32).toNat] = .heapRef innerAddr from rfl]
  step1; step1; simp only [setLocal]; step1
  rw [runJvmResFast_checkNotNull_nonnull (by intro h; cases h)]

private theorem step_mc_aastore_null3 {f pc : Nat} {k : UInt32} {addr : Nat}
    {rest : List JvmInstr} {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {elems : Array JvmVal}
    (hl30 : locs 30 = .heapRef addr)
    (hget : jh.get? addr = some (.objArray "java/lang/Object" elems))
    (hk2 : k.toNat + 2 < elems.size)
    (hs0 : k.toBitVec.slt 0#32 = false)
    (hs1 : (k + 1).toBitVec.slt 0#32 = false)
    (hs2 : (k + 2).toBitVec.slt 0#32 = false) :
    let h1 : k.toNat < elems.size := by omega
    let elems1 := elems.set k.toNat .null h1
    let h2 : (k + 1).toNat < elems1.size := by simp [elems1]; omega
    let elems2 := elems1.set (k + 1).toNat .null h2
    let h3 : (k + 2).toNat < elems2.size := by simp [elems2, elems1]; omega
    let elems3 := elems2.set (k + 2).toNat .null h3
    runJvmResFast (f + 12) f_Algorithm_parseMCNodeLine_prog pc
        (.aload 30 :: .iconst k :: .aconstNull :: .aastore ::
          .aload 30 :: .iconst (k + 1) :: .aconstNull :: .aastore ::
          .aload 30 :: .iconst (k + 2) :: .aconstNull :: .aastore :: rest)
        ⟨pc, stkRest, locs, jh, hp⟩ =
      runJvmResFast f f_Algorithm_parseMCNodeLine_prog (pc + 12) rest
        ⟨pc + 12, stkRest, locs, jh.set addr (.objArray "java/lang/Object" elems3), hp⟩ := by
  intro h1 elems1 h2 elems2 h3 elems3
  step1; rw [hl30]; step1; step1
  rw [runJvmResFast_aastore hget hs0 h1]
  step1; rw [hl30]; step1; step1
  rw [runJvmResFast_aastore (jvmHeap_get?_set_self hget) hs1 h2, jvmHeap_set_set]
  step1; rw [hl30]; step1; step1
  rw [runJvmResFast_aastore (jvmHeap_get?_set_self hget) hs2 h3, jvmHeap_set_set]

private theorem step_mc_aastore_uint {f pc : Nat} {k : UInt32} {vLoc addr : Nat}
    {rest : List JvmInstr} {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {elems : Array JvmVal} {u : UInt32}
    (hl30 : locs 30 = .heapRef addr)
    (hlv : locs vLoc = .i32 u)
    (hget : jh.get? addr = some (.objArray "java/lang/Object" elems))
    (hs : k.toBitVec.slt 0#32 = false) (hlt : k.toNat < elems.size) :
    runJvmResFast (f + 5) f_Algorithm_parseMCNodeLine_prog pc
        (.aload 30 :: .iconst k :: .iload vLoc ::
          .invokestatic "kotlin/UInt" "box-impl" "(I)Lkotlin/UInt;" :: .aastore :: rest)
        ⟨pc, stkRest, locs, jh, hp⟩ =
      runJvmResFast f f_Algorithm_parseMCNodeLine_prog (pc + 5) rest
        ⟨pc + 5, stkRest, locs,
          jh.set addr (.objArray "java/lang/Object" (elems.set k.toNat (.boxedUInt u) hlt)), hp⟩ := by
  step1; rw [hl30]; step1; step1; rw [hlv]; step1
  rw [runJvmResFast_aastore hget hs hlt]

private theorem step_mc_aastore_uint_sub1 {f pc : Nat} {k : UInt32} {vLoc addr : Nat}
    {rest : List JvmInstr} {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {elems : Array JvmVal} {u : UInt32}
    (hl30 : locs 30 = .heapRef addr)
    (hlv : locs vLoc = .i32 u)
    (hget : jh.get? addr = some (.objArray "java/lang/Object" elems))
    (hs : k.toBitVec.slt 0#32 = false) (hlt : k.toNat < elems.size) :
    runJvmResFast (f + 8) f_Algorithm_parseMCNodeLine_prog pc
        (.aload 30 :: .iconst k :: .iload vLoc :: .iconst 1 :: .isub ::
          .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" ::
          .invokestatic "kotlin/UInt" "box-impl" "(I)Lkotlin/UInt;" :: .aastore :: rest)
        ⟨pc, stkRest, locs, jh, hp⟩ =
      runJvmResFast f f_Algorithm_parseMCNodeLine_prog (pc + 8) rest
        ⟨pc + 8, stkRest, locs,
          jh.set addr (.objArray "java/lang/Object" (elems.set k.toNat (.boxedUInt (u - 1)) hlt)), hp⟩ := by
  step1; rw [hl30]; step1; step1; rw [hlv]; step1; step1; step1; step1
  rw [runJvmResFast_aastore hget hs hlt]

private theorem arr_getElem?_set_ne {α : Type} (arr : Array α) {i j : Nat}
    (v : α) (hj : j < arr.size) (hne : i ≠ j) :
    (arr.set j v hj)[i]? = arr[i]? := by
  rw [Array.getElem?_set_ne hj (Ne.symm hne)]

private theorem arr_getElem?_set_eq {α : Type} (arr : Array α) {j : Nat}
    (v : α) (hj : j < arr.size) :
    (arr.set j v hj)[j]? = some v := by
  simp only [Array.getElem?_eq_getElem (by simp [hj] : j < (arr.set j v hj).size),
    Array.getElem_set_self]

private theorem setLocal_ne {g : Nat → JvmVal} {k i : Nat} {v : JvmVal} (h : i ≠ k) :
    setLocal g k v i = g i := by simp [setLocal, h]

private theorem step_parseMC_stage {f pc qIn resLoc innerLoc valLoc tmp1 tmp2 tmp3 nextLoc qOut
    noneT someT defT : Nat}
    {restNone restSome restAfter : List JvmInstr}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {bytesAddr : Nat} {bytes : ByteArray} {lim qVal : UInt32}
    (hl0 : locs 0 = .heapRef bytesAddr) (hl1 : locs 1 = .i32 lim) (hlq : locs qIn = .i32 qVal)
    (hget : jh.get? bytesAddr = some (.byteArray bytes.data))
    (hprefix : f_Algorithm_parseMCNodeLine_prog.drop pc =
      .aload 0 :: .iload qIn :: .iload 1 ::
      .invokestatic "MacroCellLeanKt" "f_Algorithm_parseUInt32At-BltQuoY"
        "([BII)Ljava/lang/Object;" ::
      .astore resLoc ::
      .aload resLoc :: .ldcStr "null cannot be cast to non-null type kotlin.Array<*>" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .aload resLoc :: .checkcast "[Ljava/lang/Object;" :: .iconst 0 :: .aaload ::
      .dup :: .ldcStr "null cannot be cast to non-null type kotlin.Int" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .checkcast "java/lang/Integer" ::
      .invokevirtual "java/lang/Integer" "intValue" "()I" ::
      .tableswitch 0 [noneT, someT] defT :: restAfter)
    (hdropNone : f_Algorithm_parseMCNodeLine_prog.drop noneT =
      .iconst 1 :: .anewarray "java/lang/Object" :: .astore valLoc :: .aload valLoc ::
      .iconst 0 :: .iconst 0 ::
      .invokestatic "java/lang/Integer" "valueOf" "(I)Ljava/lang/Integer;" ::
      .aastore :: .aload valLoc :: .astore innerLoc :: .aload innerLoc :: .areturn :: restNone)
    (hdropSome : f_Algorithm_parseMCNodeLine_prog.drop someT =
      .aload resLoc :: .checkcast "[Ljava/lang/Object;" :: .iconst 1 :: .aaload ::
      .astore innerLoc :: .aload innerLoc ::
      .ldcStr "null cannot be cast to non-null type kotlin.Array<*>" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .aload innerLoc :: .checkcast "[Ljava/lang/Object;" :: .iconst 1 :: .aaload ::
      .astore tmp1 :: .iconst 0 :: .istore tmp2 ::
      .aload tmp1 :: .instanceof "java/lang/Integer" :: .ifeq (someT + 23) ::
      .aload tmp1 :: .checkcast "java/lang/Number" ::
      .invokevirtual "java/lang/Number" "intValue" "()I" ::
      .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" :: .goto (someT + 29) ::
      .aload tmp1 :: .ldcStr "null cannot be cast to non-null type kotlin.UInt" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .aload tmp1 :: .checkcast "kotlin/UInt" ::
      .invokevirtual "kotlin/UInt" "unbox-impl" "()I" ::
      .istore valLoc ::
      .aload innerLoc :: .checkcast "[Ljava/lang/Object;" :: .iconst 5 :: .aaload ::
      .astore tmp2 :: .iconst 0 :: .istore tmp3 ::
      .aload tmp2 :: .instanceof "java/lang/Integer" :: .ifeq (someT + 45) ::
      .aload tmp2 :: .checkcast "java/lang/Number" ::
      .invokevirtual "java/lang/Number" "intValue" "()I" ::
      .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" :: .goto (someT + 51) ::
      .aload tmp2 :: .ldcStr "null cannot be cast to non-null type kotlin.UInt" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .aload tmp2 :: .checkcast "kotlin/UInt" ::
      .invokevirtual "kotlin/UInt" "unbox-impl" "()I" ::
      .istore nextLoc ::
      .aload 0 :: .iload nextLoc :: .iload 1 ::
      .invokestatic "MacroCellLeanKt" "f_Algorithm_skipSpaces-BltQuoY" "([BII)I" ::
      .istore qOut :: restSome)
    (hdropU1 : f_Algorithm_parseMCNodeLine_prog.drop (someT + 23) =
      .aload tmp1 :: .ldcStr "null cannot be cast to non-null type kotlin.UInt" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .aload tmp1 :: .checkcast "kotlin/UInt" ::
      .invokevirtual "kotlin/UInt" "unbox-impl" "()I" ::
      .istore valLoc ::
      .aload innerLoc :: .checkcast "[Ljava/lang/Object;" :: .iconst 5 :: .aaload ::
      .astore tmp2 :: .iconst 0 :: .istore tmp3 ::
      .aload tmp2 :: .instanceof "java/lang/Integer" :: .ifeq (someT + 45) ::
      .aload tmp2 :: .checkcast "java/lang/Number" ::
      .invokevirtual "java/lang/Number" "intValue" "()I" ::
      .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" :: .goto (someT + 51) ::
      .aload tmp2 :: .ldcStr "null cannot be cast to non-null type kotlin.UInt" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .aload tmp2 :: .checkcast "kotlin/UInt" ::
      .invokevirtual "kotlin/UInt" "unbox-impl" "()I" ::
      .istore nextLoc ::
      .aload 0 :: .iload nextLoc :: .iload 1 ::
      .invokestatic "MacroCellLeanKt" "f_Algorithm_skipSpaces-BltQuoY" "([BII)I" ::
      .istore qOut :: restSome)
    (hdropU2 : f_Algorithm_parseMCNodeLine_prog.drop (someT + 45) =
      .aload tmp2 :: .ldcStr "null cannot be cast to non-null type kotlin.UInt" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .aload tmp2 :: .checkcast "kotlin/UInt" ::
      .invokevirtual "kotlin/UInt" "unbox-impl" "()I" ::
      .istore nextLoc ::
      .aload 0 :: .iload nextLoc :: .iload 1 ::
      .invokestatic "MacroCellLeanKt" "f_Algorithm_skipSpaces-BltQuoY" "([BII)I" ::
      .istore qOut :: restSome)
    (hne0 : resLoc ≠ 0) (hne1 : resLoc ≠ 1)
    (hneq0 : innerLoc ≠ 0) (hneq1 : innerLoc ≠ 1)
    (hneqV0 : valLoc ≠ 0) (hneqV1 : valLoc ≠ 1)
    (hneqT10 : tmp1 ≠ 0) (hneqT11 : tmp1 ≠ 1) (hneqT1I : tmp1 ≠ innerLoc)
    (hneqT20 : tmp2 ≠ 0) (hneqT21 : tmp2 ≠ 1) (hneqT2I : tmp2 ≠ innerLoc)
    (hneqT30 : tmp3 ≠ 0) (hneqT31 : tmp3 ≠ 1) (_hneqT3I : tmp3 ≠ innerLoc)
    (hneqN0 : nextLoc ≠ 0) (hneqN1 : nextLoc ≠ 1)
    (hneqT2V : tmp2 ≠ valLoc) (hneqT3V : tmp3 ≠ valLoc)
    (hneqNV : nextLoc ≠ valLoc) (hneqQV : qOut ≠ valLoc)
    (hneqQN : qOut ≠ nextLoc) (hneqQ0 : qOut ≠ 0) (hneqQ1 : qOut ≠ 1)
    (hneqT12 : tmp1 ≠ tmp2) (hneqT23 : tmp2 ≠ tmp3) (hneqVI : valLoc ≠ innerLoc) :
    match Algorithm.parseUInt32At bytes qVal lim with
    | none =>
      ∃ v st',
        runJvmResFast (f + 65) f_Algorithm_parseMCNodeLine_prog pc
            (f_Algorithm_parseMCNodeLine_prog.drop pc) ⟨pc, [], locs, jh, hp⟩ =
          some (v, st') ∧
        decodeOptMCNodeLine st'.jvmHeap v = some none ∧ st'.heap = hp
    | some r =>
      let qNext := Algorithm.skipSpaces bytes r.next lim
      ∃ jh' locs',
        (∀ a o, jh.get? a = some o → jh'.get? a = some o) ∧
        locs' 0 = .heapRef bytesAddr ∧ locs' 1 = .i32 lim ∧
        locs' valLoc = .i32 r.val ∧ locs' nextLoc = .i32 r.next ∧ locs' qOut = .i32 qNext ∧
        (∀ i, i ≠ resLoc → i ≠ innerLoc → i ≠ tmp1 → i ≠ tmp2 → i ≠ tmp3 →
          i ≠ valLoc → i ≠ nextLoc → i ≠ qOut → locs' i = locs i) ∧
        runJvmResFast (f + 65) f_Algorithm_parseMCNodeLine_prog pc
            (f_Algorithm_parseMCNodeLine_prog.drop pc) ⟨pc, [], locs, jh, hp⟩ =
          runJvmResFast f f_Algorithm_parseMCNodeLine_prog (someT + 57) restSome
            ⟨someT + 57, [], locs', jh', hp⟩ := by
  cases hparse : Algorithm.parseUInt32At bytes qVal lim with
  | none =>
    rw [hprefix]
    step1; dsimp only; rw [hl0]; step1; dsimp only; rw [hlq]; step1; dsimp only; rw [hl1]
    have hsp := stepStatic_parseUInt32At (pc := pc + 3) (lim := .i32 lim) (pos := .i32 qVal)
      (addr := bytesAddr) (rest := []) (locs := locs) (hp := hp) hget
    simp only [Jvm.JvmVal.asI32, hparse, Option.map_none, encodeOptScalarPair] at hsp
    split_res_fuel 1
    rw [runJvmResFast_invokestatic_step hsp]
    rw [show f + (65 - 1 - 1 - 1) - 1 = (f + 36) + 25 from by omega]
    step1
    dsimp only
    rw [show (jh.alloc (.objArray "java/lang/Object" #[.boxedInt 0])).1 = jh.objects.size from rfl]
    have hgetOut : (jh.alloc (.objArray "java/lang/Object" #[.boxedInt 0])).2.get?
        jh.objects.size = some (.objArray "java/lang/Object" #[.boxedInt 0]) :=
      jvmHeap_get?_alloc_self _ _
    rw [show f + 36 + (25 - 1) = (f + 35) + 25 from by omega]
    rw [step_parseMC_dispatch_none (resLoc := resLoc) (noneT := noneT) (someT := someT) (defT := defT)
      (tmp := valLoc) (out := innerLoc) (rest := restAfter)
      (locs := setLocal locs resLoc (.heapRef jh.objects.size))
      (by simp [setLocal]) hgetOut hdropNone]
    refine ⟨_, _, rfl, ?_, rfl⟩
    dsimp only [decodeOptMCNodeLine]
    rw [jvmHeap_get?_set_push_self]
    rfl
  | some r =>
    let qNext := Algorithm.skipSpaces bytes r.next lim
    rw [hprefix]
    step1; dsimp only; rw [hl0]; step1; dsimp only; rw [hlq]; step1; dsimp only; rw [hl1]
    have hsp := stepStatic_parseUInt32At (pc := pc + 3) (lim := .i32 lim) (pos := .i32 qVal)
      (addr := bytesAddr) (rest := []) (locs := locs) (hp := hp) hget
    simp only [Jvm.JvmVal.asI32, hparse, Option.map_some, encodeOptScalarPair] at hsp
    split_res_fuel 1
    rw [runJvmResFast_invokestatic_step hsp]
    rw [show f + (65 - 1 - 1 - 1) - 1 = (f + 40) + 21 from by omega]
    step1
    dsimp only
    let innerArr : Array JvmVal := #[.boxedInt 0, .boxedUInt r.val, .null, .null, .null, .boxedUInt r.next]
    let h1 := (jh.alloc (.objArray "java/lang/Object" innerArr)).2
    let h2 := (h1.alloc (.objArray "java/lang/Object" #[.boxedInt 1, .heapRef jh.objects.size])).2
    have hext : ∀ a o, jh.get? a = some o → h2.get? a = some o := by
      intro a o ha
      rcases Array.getElem?_eq_some_iff.mp ha with ⟨hlt, _⟩
      have hlt1 : a < h1.objects.size := by simp [h1, Jvm.JvmHeap.alloc]; omega
      rw [jvmHeap_get?_alloc_lt _ _ hlt1, jvmHeap_get?_alloc_lt _ _ hlt, ha]
    have hgetOuter : h2.get? h1.objects.size =
        some (.objArray "java/lang/Object" #[.boxedInt 1, .heapRef jh.objects.size]) :=
      jvmHeap_get?_alloc_self _ _
    have hgetInner : h2.get? jh.objects.size = some (.objArray "java/lang/Object" innerArr) := by
      have h1get : h1.get? jh.objects.size = some (.objArray "java/lang/Object" innerArr) :=
        jvmHeap_get?_alloc_self _ _
      have hlt1 : jh.objects.size < h1.objects.size := by simp [h1, Jvm.JvmHeap.alloc]
      rw [jvmHeap_get?_alloc_lt _ _ hlt1, h1get]
    have ha0 : (jh.alloc (.objArray "java/lang/Object"
        #[.boxedInt 0, .boxedUInt r.val, .null, .null, .null, .boxedUInt r.next])).1 =
      jh.objects.size := rfl
    have haf : (h1.alloc (.objArray "java/lang/Object" #[.boxedInt 1, .heapRef jh.objects.size])).1 =
      h1.objects.size := rfl
    rw [ha0, haf]
    rw [show f + 40 + (21 - 1) = (f + 39) + 21 from by omega]
    rw [step_parseMC_dispatch_some (resLoc := resLoc) (noneT := noneT) (someT := someT) (defT := defT)
      (innerLoc := innerLoc) (rest := restAfter) (outerAddr := h1.objects.size)
      (by simp [setLocal]) hgetOuter hdropSome]
    rw [show f + 39 = (f + 23) + 16 from by omega]
    rw [step_parseMC_unbox_uint (pc := someT + 8) (arrLoc := innerLoc) (idx := 1)
      (tmp1 := tmp1) (tmp2 := tmp2) hneqT12 (by simp [setLocal]) hgetInner
      (by decide) (by simp [innerArr]) rfl (by simpa using hdropU1)]
    rw [show someT + 8 + 21 = someT + 29 from by omega]
    step1
    rw [show f + (23 - 1) = (f + 6) + 16 from by omega]
    dsimp only
    rw [step_parseMC_unbox_uint (pc := someT + 30) (arrLoc := innerLoc) (idx := 5)
      (tmp1 := tmp2) (tmp2 := tmp3) hneqT23
      (by rw [setLocal_ne hneqVI.symm, setLocal_ne hneqT2I.symm, setLocal_ne hneqT1I.symm]; simp [setLocal])
      hgetInner (by decide) (by simp [innerArr]) rfl (by simpa using hdropU2)]
    rw [show someT + 30 + 21 = someT + 51 from by omega]
    step1
    step1
    dsimp only
    rw [setLocal_ne hneqN0.symm, setLocal_ne hneqT30.symm, setLocal_ne hneqT20.symm,
      setLocal_ne hneqV0.symm, setLocal_ne hneqT20.symm, setLocal_ne hneqT10.symm,
      setLocal_ne hneq0.symm, setLocal_ne hne0.symm, hl0]
    step1; step1
    dsimp only
    rw [setLocal_ne hneqN1.symm, setLocal_ne hneqT31.symm, setLocal_ne hneqT21.symm,
      setLocal_ne hneqV1.symm, setLocal_ne hneqT21.symm, setLocal_ne hneqT11.symm,
      setLocal_ne hneq1.symm, setLocal_ne hne1.symm, hl1]
    rw [setLocal_eq_val (decide_eq_true rfl)]
    rw [show f + (6 - 1 - 1 - 1 - 1) = (f + 1) + 1 from by omega]
    rw [runJvmResFast_invokestatic_step
      (stepStatic_skipSpaces (pc := someT + 55) (hp := hp) (hext bytesAddr _ hget))]
    step1
    dsimp only [Jvm.JvmVal.asI32]
    rw [show f + (1 - 1) = f from by omega, show someT + 55 + 1 + 1 = someT + 57 from by omega,
      show ({ data := bytes.data } : ByteArray) = bytes from rfl]
    refine ⟨h2, _, hext, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
    · simp [setLocal, hl0, hne0.symm, hneq0.symm, hneqT10.symm, hneqT20.symm, hneqV0.symm,
        hneqT30.symm, hneqN0.symm, hneqQ0.symm]
    · simp [setLocal, hl1, hne1.symm, hneq1.symm, hneqT11.symm, hneqT21.symm, hneqV1.symm,
        hneqT31.symm, hneqN1.symm, hneqQ1.symm]
    · simp [setLocal, hneqT2V.symm, hneqT3V.symm, hneqNV.symm, hneqQV.symm]
    · simp [setLocal, hneqQN.symm]
    · simp [setLocal]
    · intro i hi1 hi2 hi3 hi4 hi5 hi6 hi7 hi8
      simp [setLocal, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8]

private def parseMCStagePrefix (qIn resLoc noneT someT defT : Nat)
    (rest : List JvmInstr) : List JvmInstr :=
  .aload 0 :: .iload qIn :: .iload 1 ::
  .invokestatic "MacroCellLeanKt" "f_Algorithm_parseUInt32At-BltQuoY" "([BII)Ljava/lang/Object;" ::
  .astore resLoc ::
  .aload resLoc :: .ldcStr "null cannot be cast to non-null type kotlin.Array<*>" ::
  .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull" "(Ljava/lang/Object;Ljava/lang/String;)V" ::
  .aload resLoc :: .checkcast "[Ljava/lang/Object;" :: .iconst 0 :: .aaload ::
  .dup :: .ldcStr "null cannot be cast to non-null type kotlin.Int" ::
  .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull" "(Ljava/lang/Object;Ljava/lang/String;)V" ::
  .checkcast "java/lang/Integer" ::
  .invokevirtual "java/lang/Integer" "intValue" "()I" ::
  .tableswitch 0 [noneT, someT] defT :: rest

private def parseMCStageNone (tmp out : Nat) (rest : List JvmInstr) : List JvmInstr :=
  .iconst 1 :: .anewarray "java/lang/Object" :: .astore tmp :: .aload tmp ::
  .iconst 0 :: .iconst 0 ::
  .invokestatic "java/lang/Integer" "valueOf" "(I)Ljava/lang/Integer;" ::
  .aastore :: .aload tmp :: .astore out :: .aload out :: .areturn :: rest

private def parseMCStageSome (resLoc innerLoc tmp1 tmp2 tmp3 valLoc nextLoc qOut someT : Nat)
    (rest : List JvmInstr) : List JvmInstr :=
  .aload resLoc :: .checkcast "[Ljava/lang/Object;" :: .iconst 1 :: .aaload ::
  .astore innerLoc :: .aload innerLoc ::
  .ldcStr "null cannot be cast to non-null type kotlin.Array<*>" ::
  .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull" "(Ljava/lang/Object;Ljava/lang/String;)V" ::
  .aload innerLoc :: .checkcast "[Ljava/lang/Object;" :: .iconst 1 :: .aaload ::
  .astore tmp1 :: .iconst 0 :: .istore tmp2 ::
  .aload tmp1 :: .instanceof "java/lang/Integer" :: .ifeq (someT + 23) ::
  .aload tmp1 :: .checkcast "java/lang/Number" ::
  .invokevirtual "java/lang/Number" "intValue" "()I" ::
  .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" :: .goto (someT + 29) ::
  .aload tmp1 :: .ldcStr "null cannot be cast to non-null type kotlin.UInt" ::
  .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull" "(Ljava/lang/Object;Ljava/lang/String;)V" ::
  .aload tmp1 :: .checkcast "kotlin/UInt" ::
  .invokevirtual "kotlin/UInt" "unbox-impl" "()I" ::
  .istore valLoc ::
  .aload innerLoc :: .checkcast "[Ljava/lang/Object;" :: .iconst 5 :: .aaload ::
  .astore tmp2 :: .iconst 0 :: .istore tmp3 ::
  .aload tmp2 :: .instanceof "java/lang/Integer" :: .ifeq (someT + 45) ::
  .aload tmp2 :: .checkcast "java/lang/Number" ::
  .invokevirtual "java/lang/Number" "intValue" "()I" ::
  .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" :: .goto (someT + 51) ::
  .aload tmp2 :: .ldcStr "null cannot be cast to non-null type kotlin.UInt" ::
  .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull" "(Ljava/lang/Object;Ljava/lang/String;)V" ::
  .aload tmp2 :: .checkcast "kotlin/UInt" ::
  .invokevirtual "kotlin/UInt" "unbox-impl" "()I" ::
  .istore nextLoc ::
  .aload 0 :: .iload nextLoc :: .iload 1 ::
  .invokestatic "MacroCellLeanKt" "f_Algorithm_skipSpaces-BltQuoY" "([BII)I" ::
  .istore qOut :: rest

private def parseMCQuadInstrs (kNull : UInt32) (vLoc sLoc eLoc : Nat)
    (rest : List JvmInstr) : List JvmInstr :=
  .aload 30 :: .iconst kNull :: .aconstNull :: .aastore ::
  .aload 30 :: .iconst (kNull + 1) :: .aconstNull :: .aastore ::
  .aload 30 :: .iconst (kNull + 2) :: .aconstNull :: .aastore ::
  .aload 30 :: .iconst (kNull + 3) :: .iload vLoc ::
  .invokestatic "kotlin/UInt" "box-impl" "(I)Lkotlin/UInt;" :: .aastore ::
  .aload 30 :: .iconst (kNull + 4) :: .aconstNull :: .aastore ::
  .aload 30 :: .iconst (kNull + 5) :: .aconstNull :: .aastore ::
  .aload 30 :: .iconst (kNull + 6) :: .aconstNull :: .aastore ::
  .aload 30 :: .iconst (kNull + 7) :: .iload sLoc ::
  .invokestatic "kotlin/UInt" "box-impl" "(I)Lkotlin/UInt;" :: .aastore ::
  .aload 30 :: .iconst (kNull + 8) :: .aconstNull :: .aastore ::
  .aload 30 :: .iconst (kNull + 9) :: .aconstNull :: .aastore ::
  .aload 30 :: .iconst (kNull + 10) :: .aconstNull :: .aastore ::
  .aload 30 :: .iconst (kNull + 11) :: .iload eLoc :: .iconst 1 :: .isub ::
  .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" ::
  .invokestatic "kotlin/UInt" "box-impl" "(I)Lkotlin/UInt;" :: .aastore :: rest

private theorem parseMC_drop_0 :
    f_Algorithm_parseMCNodeLine_prog.drop 0 =
      .aload 0 :: .ldcStr "bytes" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .aload 0 :: .arraylength :: .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" :: .istore 1 ::
      .aload 0 :: .iconst 0 :: .iload 1 ::
      .invokestatic "MacroCellLeanKt" "f_Algorithm_skipSpaces-BltQuoY" "([BII)I" :: .istore 2 ::
      f_Algorithm_parseMCNodeLine_prog.drop 12 := rfl

private theorem parseMC_drop_12 :
    f_Algorithm_parseMCNodeLine_prog.drop 12 =
      parseMCStagePrefix 2 3 30 42 729 (f_Algorithm_parseMCNodeLine_prog.drop 30) := rfl

private theorem parseMC_drop_30 :
    f_Algorithm_parseMCNodeLine_prog.drop 30 =
      parseMCStageNone 5 4 (f_Algorithm_parseMCNodeLine_prog.drop 42) := rfl

private theorem parseMC_drop_42 :
    f_Algorithm_parseMCNodeLine_prog.drop 42 =
      .aload 3 :: .checkcast "[Ljava/lang/Object;" :: .iconst 1 :: .aaload ::
      .astore 4 :: .aload 4 ::
      .ldcStr "null cannot be cast to non-null type kotlin.Array<*>" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .aload 4 :: .checkcast "[Ljava/lang/Object;" :: .iconst 1 :: .aaload ::
      .astore 6 :: .iconst 0 :: .istore 7 ::
      .aload 6 :: .instanceof "java/lang/Integer" :: .ifeq 65 ::
      .aload 6 :: .checkcast "java/lang/Number" ::
      .invokevirtual "java/lang/Number" "intValue" "()I" ::
      .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" :: .goto 71 ::
      .aload 6 :: .ldcStr "null cannot be cast to non-null type kotlin.UInt" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .aload 6 :: .checkcast "kotlin/UInt" ::
      .invokevirtual "kotlin/UInt" "unbox-impl" "()I" ::
      .istore 5 :: .aload 0 ::
      .aload 4 :: .checkcast "[Ljava/lang/Object;" :: .iconst 5 :: .aaload ::
      .astore 7 :: .iconst 0 :: .istore 8 ::
      .aload 7 :: .instanceof "java/lang/Integer" :: .ifeq 88 ::
      .aload 7 :: .checkcast "java/lang/Number" ::
      .invokevirtual "java/lang/Number" "intValue" "()I" ::
      .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" :: .goto 94 ::
      .aload 7 :: .ldcStr "null cannot be cast to non-null type kotlin.UInt" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .aload 7 :: .checkcast "kotlin/UInt" ::
      .invokevirtual "kotlin/UInt" "unbox-impl" "()I" ::
      .iload 1 :: .invokestatic "MacroCellLeanKt" "f_Algorithm_skipSpaces-BltQuoY" "([BII)I" ::
      .istore 6 :: f_Algorithm_parseMCNodeLine_prog.drop 97 := rfl

private theorem parseMC_drop_65 :
    f_Algorithm_parseMCNodeLine_prog.drop 65 =
      .aload 6 :: .ldcStr "null cannot be cast to non-null type kotlin.UInt" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .aload 6 :: .checkcast "kotlin/UInt" ::
      .invokevirtual "kotlin/UInt" "unbox-impl" "()I" ::
      .istore 5 :: .aload 0 ::
      .aload 4 :: .checkcast "[Ljava/lang/Object;" :: .iconst 5 :: .aaload ::
      .astore 7 :: .iconst 0 :: .istore 8 ::
      .aload 7 :: .instanceof "java/lang/Integer" :: .ifeq 88 ::
      .aload 7 :: .checkcast "java/lang/Number" ::
      .invokevirtual "java/lang/Number" "intValue" "()I" ::
      .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" :: .goto 94 ::
      .aload 7 :: .ldcStr "null cannot be cast to non-null type kotlin.UInt" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .aload 7 :: .checkcast "kotlin/UInt" ::
      .invokevirtual "kotlin/UInt" "unbox-impl" "()I" ::
      .iload 1 :: .invokestatic "MacroCellLeanKt" "f_Algorithm_skipSpaces-BltQuoY" "([BII)I" ::
      .istore 6 :: f_Algorithm_parseMCNodeLine_prog.drop 97 := rfl

private theorem parseMC_drop_88 :
    f_Algorithm_parseMCNodeLine_prog.drop 88 =
      .aload 7 :: .ldcStr "null cannot be cast to non-null type kotlin.UInt" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .aload 7 :: .checkcast "kotlin/UInt" ::
      .invokevirtual "kotlin/UInt" "unbox-impl" "()I" ::
      .iload 1 :: .invokestatic "MacroCellLeanKt" "f_Algorithm_skipSpaces-BltQuoY" "([BII)I" ::
      .istore 6 :: f_Algorithm_parseMCNodeLine_prog.drop 97 := rfl

section
set_option maxRecDepth 4096

private theorem parseMC_drop_97 :
    f_Algorithm_parseMCNodeLine_prog.drop 97 =
      parseMCStagePrefix 6 7 115 127 723 (f_Algorithm_parseMCNodeLine_prog.drop 115) := rfl
private theorem parseMC_drop_115 :
    f_Algorithm_parseMCNodeLine_prog.drop 115 =
      parseMCStageNone 10 9 (f_Algorithm_parseMCNodeLine_prog.drop 127) := rfl
private theorem parseMC_drop_127 :
    f_Algorithm_parseMCNodeLine_prog.drop 127 =
      parseMCStageSome 7 9 11 12 13 10 11 12 127 (f_Algorithm_parseMCNodeLine_prog.drop 184) := rfl

private theorem parseMC_drop_184 :
    f_Algorithm_parseMCNodeLine_prog.drop 184 =
      parseMCStagePrefix 12 13 202 214 717 (f_Algorithm_parseMCNodeLine_prog.drop 202) := rfl
private theorem parseMC_drop_202 :
    f_Algorithm_parseMCNodeLine_prog.drop 202 =
      parseMCStageNone 15 14 (f_Algorithm_parseMCNodeLine_prog.drop 214) := rfl
private theorem parseMC_drop_214 :
    f_Algorithm_parseMCNodeLine_prog.drop 214 =
      parseMCStageSome 13 14 16 17 18 15 16 17 214 (f_Algorithm_parseMCNodeLine_prog.drop 271) := rfl

private theorem parseMC_drop_271 :
    f_Algorithm_parseMCNodeLine_prog.drop 271 =
      parseMCStagePrefix 17 18 289 301 711 (f_Algorithm_parseMCNodeLine_prog.drop 289) := rfl
private theorem parseMC_drop_289 :
    f_Algorithm_parseMCNodeLine_prog.drop 289 =
      parseMCStageNone 20 19 (f_Algorithm_parseMCNodeLine_prog.drop 301) := rfl
private theorem parseMC_drop_301 :
    f_Algorithm_parseMCNodeLine_prog.drop 301 =
      parseMCStageSome 18 19 21 22 23 20 21 22 301 (f_Algorithm_parseMCNodeLine_prog.drop 358) := rfl

private theorem parseMC_drop_358 :
    f_Algorithm_parseMCNodeLine_prog.drop 358 =
      parseMCStagePrefix 22 23 376 388 705 (f_Algorithm_parseMCNodeLine_prog.drop 376) := rfl
private theorem parseMC_drop_376 :
    f_Algorithm_parseMCNodeLine_prog.drop 376 =
      parseMCStageNone 25 24 (f_Algorithm_parseMCNodeLine_prog.drop 388) := rfl
private theorem parseMC_drop_388 :
    f_Algorithm_parseMCNodeLine_prog.drop 388 =
      parseMCStageSome 23 24 26 27 28 25 26 27 388 (f_Algorithm_parseMCNodeLine_prog.drop 445) := rfl

private theorem parseMC_drop_445 :
    f_Algorithm_parseMCNodeLine_prog.drop 445 =
      .iload 27 :: .iload 1 :: .if_icmpeq 460 :: f_Algorithm_parseMCNodeLine_prog.drop 448 := rfl
private theorem parseMC_drop_448 :
    f_Algorithm_parseMCNodeLine_prog.drop 448 =
      parseMCStageNone 29 28 (f_Algorithm_parseMCNodeLine_prog.drop 460) := rfl
private theorem parseMC_drop_460 :
    f_Algorithm_parseMCNodeLine_prog.drop 460 =
      .iconst 2 :: .anewarray "java/lang/Object" :: .astore 29 ::
      .aload 29 :: .iconst 0 :: .iconst 1 ::
      .invokestatic "java/lang/Integer" "valueOf" "(I)Ljava/lang/Integer;" :: .aastore ::
      .aload 29 :: .iconst 1 :: .iconst 50 :: .anewarray "java/lang/Object" :: .astore 30 ::
      .aload 30 :: .iconst 0 :: .iconst 0 ::
      .invokestatic "java/lang/Integer" "valueOf" "(I)Ljava/lang/Integer;" :: .aastore ::
      .aload 30 :: .iconst 1 :: .iload 5 ::
      .invokestatic "kotlin/UInt" "box-impl" "(I)Lkotlin/UInt;" :: .aastore ::
      f_Algorithm_parseMCNodeLine_prog.drop 483 := rfl
private theorem parseMC_drop_483 :
    f_Algorithm_parseMCNodeLine_prog.drop 483 =
      parseMCQuadInstrs 2 10 6 11 (f_Algorithm_parseMCNodeLine_prog.drop 537) := rfl
private theorem parseMC_drop_537 :
    f_Algorithm_parseMCNodeLine_prog.drop 537 =
      parseMCQuadInstrs 14 15 12 16 (f_Algorithm_parseMCNodeLine_prog.drop 591) := rfl
private theorem parseMC_drop_591 :
    f_Algorithm_parseMCNodeLine_prog.drop 591 =
      parseMCQuadInstrs 26 20 17 21 (f_Algorithm_parseMCNodeLine_prog.drop 645) := rfl
private theorem parseMC_drop_645 :
    f_Algorithm_parseMCNodeLine_prog.drop 645 =
      parseMCQuadInstrs 38 25 22 26 (f_Algorithm_parseMCNodeLine_prog.drop 699) := rfl
private theorem parseMC_drop_699 :
    f_Algorithm_parseMCNodeLine_prog.drop 699 =
      .aload 30 :: .aastore :: .aload 29 :: .astore 28 :: .aload 28 :: .areturn ::
      f_Algorithm_parseMCNodeLine_prog.drop 705 := rfl

end

private theorem parseMC_stageSome_drop23 {resLoc innerLoc tmp1 tmp2 tmp3 valLoc nextLoc qOut someT : Nat}
    {rest : List JvmInstr} :
    (parseMCStageSome resLoc innerLoc tmp1 tmp2 tmp3 valLoc nextLoc qOut someT rest).drop 23 =
      .aload tmp1 :: .ldcStr "null cannot be cast to non-null type kotlin.UInt" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .aload tmp1 :: .checkcast "kotlin/UInt" ::
      .invokevirtual "kotlin/UInt" "unbox-impl" "()I" ::
      .istore valLoc ::
      .aload innerLoc :: .checkcast "[Ljava/lang/Object;" :: .iconst 5 :: .aaload ::
      .astore tmp2 :: .iconst 0 :: .istore tmp3 ::
      .aload tmp2 :: .instanceof "java/lang/Integer" :: .ifeq (someT + 45) ::
      .aload tmp2 :: .checkcast "java/lang/Number" ::
      .invokevirtual "java/lang/Number" "intValue" "()I" ::
      .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" :: .goto (someT + 51) ::
      .aload tmp2 :: .ldcStr "null cannot be cast to non-null type kotlin.UInt" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .aload tmp2 :: .checkcast "kotlin/UInt" ::
      .invokevirtual "kotlin/UInt" "unbox-impl" "()I" ::
      .istore nextLoc ::
      .aload 0 :: .iload nextLoc :: .iload 1 ::
      .invokestatic "MacroCellLeanKt" "f_Algorithm_skipSpaces-BltQuoY" "([BII)I" ::
      .istore qOut :: rest := rfl

private theorem parseMC_stageSome_drop45 {resLoc innerLoc tmp1 tmp2 tmp3 valLoc nextLoc qOut someT : Nat}
    {rest : List JvmInstr} :
    (parseMCStageSome resLoc innerLoc tmp1 tmp2 tmp3 valLoc nextLoc qOut someT rest).drop 45 =
      .aload tmp2 :: .ldcStr "null cannot be cast to non-null type kotlin.UInt" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .aload tmp2 :: .checkcast "kotlin/UInt" ::
      .invokevirtual "kotlin/UInt" "unbox-impl" "()I" ::
      .istore nextLoc ::
      .aload 0 :: .iload nextLoc :: .iload 1 ::
      .invokestatic "MacroCellLeanKt" "f_Algorithm_skipSpaces-BltQuoY" "([BII)I" ::
      .istore qOut :: rest := rfl

private theorem step_parseMC_prelude {f : Nat} {bytesAddr : Nat} {bytes : ByteArray}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hget : jh.get? bytesAddr = some (.byteArray bytes.data)) :
    let lim := bytes.size.toUInt32
    let q0 := Algorithm.skipSpaces bytes 0 lim
    let locs0 : Nat → JvmVal := setLocal (fun _ => .null) 0 (.heapRef bytesAddr)
    runJvmResFast (f + 12) f_Algorithm_parseMCNodeLine_prog 0
        (f_Algorithm_parseMCNodeLine_prog.drop 0) ⟨0, [], locs0, jh, hp⟩ =
      runJvmResFast f f_Algorithm_parseMCNodeLine_prog 12
        (f_Algorithm_parseMCNodeLine_prog.drop 12)
        ⟨12, [], setLocal (setLocal locs0 1 (.i32 lim)) 2 (.i32 q0), jh, hp⟩ := by
  intro lim q0 locs0
  rw [parseMC_drop_0]
  step1; dsimp only [locs0, setLocal]
  step1
  simp only [↓reduceIte]
  rw [show f + (12 - 1 - 1) = (f + 9) + 1 from by omega]
  rw [runJvmResFast_invokestatic_step (stepStatic_checkNotNullParameter_hp (obj := .heapRef bytesAddr) rfl)]
  step1
  rw [show f + (9 - 1) = (f + 7) + 1 from by omega]
  rw [runJvmResFast_arraylength_byteArray hget]
  step1; step1; step1
  step1; step1
  rw [show f + (7 - 1 - 1 - 1 - 1 - 1) = (f + 1) + 1 from by omega]
  rw [runJvmResFast_invokestatic_step (stepStatic_skipSpaces (pc := 10)
    (lim := .i32 bytes.data.size.toUInt32) (pos := .i32 0) (addr := bytesAddr)
    (rest := []) (hp := hp) hget)]
  step1
  rfl

private theorem step_parseMC_stage0 {f : Nat} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {bytesAddr : Nat} {bytes : ByteArray}
    {lim q0 : UInt32}
    (hl0 : locs 0 = .heapRef bytesAddr) (hl1 : locs 1 = .i32 lim) (hl2 : locs 2 = .i32 q0)
    (hget : jh.get? bytesAddr = some (.byteArray bytes.data)) :
    match Algorithm.parseUInt32At bytes q0 lim with
    | none =>
      ∃ v st',
        runJvmResFast (f + 63) f_Algorithm_parseMCNodeLine_prog 12
            (f_Algorithm_parseMCNodeLine_prog.drop 12) ⟨12, [], locs, jh, hp⟩ =
          some (v, st') ∧
        decodeOptMCNodeLine st'.jvmHeap v = some none ∧ st'.heap = hp
    | some r0 =>
      let q1 := Algorithm.skipSpaces bytes r0.next lim
      ∃ jh' locs',
        (∀ a o, jh.get? a = some o → jh'.get? a = some o) ∧
        locs' 0 = .heapRef bytesAddr ∧ locs' 1 = .i32 lim ∧
        locs' 5 = .i32 r0.val ∧ locs' 6 = .i32 q1 ∧
        runJvmResFast (f + 63) f_Algorithm_parseMCNodeLine_prog 12
            (f_Algorithm_parseMCNodeLine_prog.drop 12) ⟨12, [], locs, jh, hp⟩ =
          runJvmResFast f f_Algorithm_parseMCNodeLine_prog 97
            (f_Algorithm_parseMCNodeLine_prog.drop 97) ⟨97, [], locs', jh', hp⟩ := by
  cases hparse : Algorithm.parseUInt32At bytes q0 lim with
  | none =>
    rw [parseMC_drop_12]
    dsimp only [parseMCStagePrefix]
    step1; dsimp only; rw [hl0]; step1; dsimp only; rw [hl2]; step1; dsimp only; rw [hl1]
    have hsp := stepStatic_parseUInt32At (pc := 15) (lim := .i32 lim) (pos := .i32 q0)
      (addr := bytesAddr) (rest := []) (locs := locs) (hp := hp) hget
    simp only [Jvm.JvmVal.asI32, hparse, Option.map_none, encodeOptScalarPair] at hsp
    split_res_fuel 1
    rw [runJvmResFast_invokestatic_step hsp]
    rw [show f + (63 - 1 - 1 - 1) - 1 = (f + 34) + 25 from by omega]
    step1; dsimp only
    rw [show (jh.alloc (.objArray "java/lang/Object" #[.boxedInt 0])).1 = jh.objects.size from rfl]
    have hgetOut : (jh.alloc (.objArray "java/lang/Object" #[.boxedInt 0])).2.get?
        jh.objects.size = some (.objArray "java/lang/Object" #[.boxedInt 0]) :=
      jvmHeap_get?_alloc_self _ _
    rw [show f + 34 + (25 - 1) = (f + 33) + 25 from by omega]
    rw [step_parseMC_dispatch_none (resLoc := 3) (noneT := 30) (someT := 42) (defT := 729)
      (tmp := 5) (out := 4) (rest := f_Algorithm_parseMCNodeLine_prog.drop 30)
      (locs := setLocal locs 3 (.heapRef jh.objects.size))
      (by simp [setLocal]) hgetOut (by simpa [parseMCStageNone] using parseMC_drop_30)]
    refine ⟨_, _, rfl, ?_, rfl⟩
    dsimp only [decodeOptMCNodeLine]
    rw [jvmHeap_get?_set_push_self]
    rfl
  | some r0 =>
    let q1 := Algorithm.skipSpaces bytes r0.next lim
    rw [parseMC_drop_12]
    dsimp only [parseMCStagePrefix]
    step1; dsimp only; rw [hl0]; step1; dsimp only; rw [hl2]; step1; dsimp only; rw [hl1]
    have hsp := stepStatic_parseUInt32At (pc := 15) (lim := .i32 lim) (pos := .i32 q0)
      (addr := bytesAddr) (rest := []) (locs := locs) (hp := hp) hget
    simp only [Jvm.JvmVal.asI32, hparse, Option.map_some, encodeOptScalarPair] at hsp
    split_res_fuel 1
    rw [runJvmResFast_invokestatic_step hsp]
    rw [show f + (63 - 1 - 1 - 1) - 1 = (f + 38) + 21 from by omega]
    step1; dsimp only
    let innerArr : Array JvmVal := #[.boxedInt 0, .boxedUInt r0.val, .null, .null, .null, .boxedUInt r0.next]
    let h1 := (jh.alloc (.objArray "java/lang/Object" innerArr)).2
    let h2 := (h1.alloc (.objArray "java/lang/Object" #[.boxedInt 1, .heapRef jh.objects.size])).2
    have hext : ∀ a o, jh.get? a = some o → h2.get? a = some o := by
      intro a o ha
      rcases Array.getElem?_eq_some_iff.mp ha with ⟨hlt, _⟩
      have hlt1 : a < h1.objects.size := by simp [h1, Jvm.JvmHeap.alloc]; omega
      rw [jvmHeap_get?_alloc_lt _ _ hlt1, jvmHeap_get?_alloc_lt _ _ hlt, ha]
    have hgetOuter : h2.get? h1.objects.size =
        some (.objArray "java/lang/Object" #[.boxedInt 1, .heapRef jh.objects.size]) :=
      jvmHeap_get?_alloc_self _ _
    have hgetInner : h2.get? jh.objects.size = some (.objArray "java/lang/Object" innerArr) := by
      have h1get : h1.get? jh.objects.size = some (.objArray "java/lang/Object" innerArr) :=
        jvmHeap_get?_alloc_self _ _
      have hlt1 : jh.objects.size < h1.objects.size := by simp [h1, Jvm.JvmHeap.alloc]
      rw [jvmHeap_get?_alloc_lt _ _ hlt1, h1get]
    have ha0 : (jh.alloc (.objArray "java/lang/Object" innerArr)).1 = jh.objects.size := rfl
    have haf : (h1.alloc (.objArray "java/lang/Object" #[.boxedInt 1, .heapRef jh.objects.size])).1 =
      h1.objects.size := rfl
    rw [ha0, haf]
    rw [show f + 38 + (21 - 1) = (f + 37) + 21 from by omega]
    rw [step_parseMC_dispatch_some (resLoc := 3) (noneT := 30) (someT := 42) (defT := 729)
      (innerLoc := 4) (rest := f_Algorithm_parseMCNodeLine_prog.drop 30) (outerAddr := h1.objects.size)
      (by simp [setLocal]) hgetOuter parseMC_drop_42]
    rw [show f + 37 = (f + 21) + 16 from by omega]
    rw [step_parseMC_unbox_uint (pc := 50) (arrLoc := 4) (idx := 1)
      (tmp1 := 6) (tmp2 := 7) (by decide) (by simp [setLocal]) hgetInner
      (by decide) (by simp [innerArr]) rfl parseMC_drop_65]
    rw [show (50 + 21 : Nat) = 71 from rfl]
    step1; step1
    dsimp only
    rw [setLocal_ne (by decide), setLocal_ne (by decide), setLocal_ne (by decide),
      setLocal_ne (by decide), setLocal_ne (by decide), hl0]
    rw [show f + (21 - 1 - 1) = (f + 3) + 16 from by omega]
    rw [step_parseMC_unbox_uint (pc := 73) (arrLoc := 4) (idx := 5)
      (tmp1 := 7) (tmp2 := 8) (by decide)
      (by rw [setLocal_ne (by decide), setLocal_ne (by decide), setLocal_ne (by decide)]; simp [setLocal])
      hgetInner (by decide) (by simp [innerArr]) rfl parseMC_drop_88]
    rw [show (73 + 21 : Nat) = 94 from rfl]
    step1; dsimp only
    rw [setLocal_ne (by decide), setLocal_ne (by decide), setLocal_ne (by decide),
      setLocal_ne (by decide), setLocal_ne (by decide), setLocal_ne (by decide),
      setLocal_ne (by decide), hl1]
    rw [show f + (3 - 1) = (f + 1) + 1 from by omega]
    rw [runJvmResFast_invokestatic_step
      (stepStatic_skipSpaces (pc := 95) (hp := hp) (hext bytesAddr _ hget))]
    step1
    dsimp only [Jvm.JvmVal.asI32]
    rw [show f + (1 - 1) = f from by omega, show (95 + 1 + 1 : Nat) = 97 from rfl,
      show ({ data := bytes.data } : ByteArray) = bytes from rfl]
    refine ⟨h2, _, hext, ?_, ?_, ?_, ?_, rfl⟩
    · simp [setLocal, hl0]
    · simp [setLocal, hl1]
    · simp [setLocal]
    · simp [setLocal]

private theorem mc_u32_add_toNat {a : UInt32} {j : Nat} (h : a.toNat + j < 2 ^ 32) :
    (a + UInt32.ofNat j).toNat = a.toNat + j := by
  have hj : j % 2 ^ 32 = j := Nat.mod_eq_of_lt (by omega)
  rw [UInt32.toNat_add, UInt32.toNat_ofNat', hj, Nat.mod_eq_of_lt h]

private theorem mc_u32_add_slt_zero {a : UInt32} {j : Nat} (h : a.toNat + j < 2 ^ 31) :
    (a + UInt32.ofNat j).toBitVec.slt 0#32 = false := by
  apply u32_slt_zero_of_lt_2_31
  rw [mc_u32_add_toNat (by omega)]
  omega

private theorem mc_u32_add_add (a : UInt32) (j k : Nat) :
    (a + UInt32.ofNat j) + UInt32.ofNat k = a + UInt32.ofNat (j + k) := by
  have hjk : UInt32.ofNat j + UInt32.ofNat k = UInt32.ofNat (j + k) := by
    apply UInt32.eq_of_toBitVec_eq
    apply BitVec.eq_of_toNat_eq
    change (j % 2 ^ 32 + k % 2 ^ 32) % 2 ^ 32 = (j + k) % 2 ^ 32
    exact (Nat.add_mod j k (2 ^ 32)).symm
  rw [UInt32.add_assoc, hjk]

private theorem mc_ne_add_of_lt {i k d : Nat} (h : i < k) : i ≠ k + d :=
  Nat.ne_of_lt (Nat.lt_of_lt_of_le h (Nat.le_add_right k d))

private theorem mc_add_ne_add {k d1 d2 : Nat} (h : d1 ≠ d2) : k + d1 ≠ k + d2 :=
  fun heq => h (Nat.add_left_cancel heq)

private theorem step_mc_quad_null3_uint {f pc : Nat} {k : UInt32}
    {vLoc innerAddr : Nat} {rest : List JvmInstr} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {elems : Array JvmVal} {vVal : UInt32}
    (hk : k.toNat + 3 < 50)
    (hl30 : locs 30 = .heapRef innerAddr)
    (hlv : locs vLoc = .i32 vVal)
    (hget : jh.get? innerAddr = some (.objArray "java/lang/Object" elems))
    (hsz : elems.size = 50) :
    ∃ elems' : Array JvmVal,
      elems'.size = 50 ∧
      elems'[k.toNat + 3]? = some (.boxedUInt vVal) ∧
      (∀ idx, idx ≠ k.toNat → idx ≠ k.toNat + 1 → idx ≠ k.toNat + 2 → idx ≠ k.toNat + 3 →
        elems'[idx]? = elems[idx]?) ∧
      runJvmResFast (f + 17) f_Algorithm_parseMCNodeLine_prog pc
          (.aload 30 :: .iconst k :: .aconstNull :: .aastore ::
           .aload 30 :: .iconst (k + 1) :: .aconstNull :: .aastore ::
           .aload 30 :: .iconst (k + 2) :: .aconstNull :: .aastore ::
           .aload 30 :: .iconst (k + 3) :: .iload vLoc ::
           .invokestatic "kotlin/UInt" "box-impl" "(I)Lkotlin/UInt;" :: .aastore :: rest)
          ⟨pc, stkRest, locs, jh, hp⟩ =
        runJvmResFast f f_Algorithm_parseMCNodeLine_prog (pc + 17) rest
          ⟨pc + 17, stkRest, locs, jh.set innerAddr (.objArray "java/lang/Object" elems'), hp⟩ := by
  have hk2_32 : k.toNat + 2 < 2 ^ 32 := Nat.lt_trans (Nat.lt_of_succ_lt hk) (by decide : 50 < 2 ^ 32)
  have hk3_31 : k.toNat + 3 < 2 ^ 31 := Nat.lt_trans hk (by decide : 50 < 2 ^ 31)
  have hm1 : (k + 1).toNat = k.toNat + 1 := mc_u32_add_toNat (Nat.lt_of_succ_lt hk2_32)
  have hm2 : (k + 2).toNat = k.toNat + 2 := mc_u32_add_toNat hk2_32
  have hm3 : (k + 3).toNat = k.toNat + 3 := mc_u32_add_toNat (Nat.lt_trans hk3_31 (by decide : 2 ^ 31 < 2 ^ 32))
  have hk0_31 : k.toNat < 2 ^ 31 :=
    Nat.lt_trans (Nat.lt_of_le_of_lt (Nat.le_add_right k.toNat 3) hk) (by decide : 50 < 2 ^ 31)
  have hs0 : k.toBitVec.slt 0#32 = false := u32_slt_zero_of_lt_2_31 hk0_31
  have hs1 : (k + 1).toBitVec.slt 0#32 = false := mc_u32_add_slt_zero (Nat.lt_of_succ_lt (Nat.lt_of_succ_lt hk3_31))
  have hs2 : (k + 2).toBitVec.slt 0#32 = false := mc_u32_add_slt_zero (Nat.lt_of_succ_lt hk3_31)
  have hs3 : (k + 3).toBitVec.slt 0#32 = false := mc_u32_add_slt_zero hk3_31
  have h02 : k.toNat + 2 < elems.size := by rw [hsz]; exact Nat.lt_of_succ_lt hk
  let e1 := (((elems.set k.toNat .null (Nat.lt_trans (Nat.lt_add_of_pos_right (by decide : 0 < 2)) h02)).set
    (k + 1).toNat .null (by rw [Array.size_set, hm1]; exact Nat.lt_of_succ_lt h02)).set
    (k + 2).toNat .null (by rw [Array.size_set, Array.size_set, hm2]; exact h02))
  have hsz1 : e1.size = 50 := by simp only [e1, Array.size_set, hsz]
  have h3 : (k + 3).toNat < e1.size := by rw [hm3, hsz1]; exact hk
  let e2 := e1.set (k + 3).toNat (.boxedUInt vVal) h3
  have hsz2 : e2.size = 50 := by simp only [e2, Array.size_set, hsz1]
  refine ⟨e2, hsz2, ?_, ?_, ?_⟩
  · dsimp only [e2]; rw [← hm3]; exact arr_getElem?_set_eq _ _ _
  · intro idx h0 h1 h2 h3ne
    dsimp only [e2, e1]
    rw [arr_getElem?_set_ne _ _ _ (by rw [hm3]; exact h3ne),
      arr_getElem?_set_ne _ _ _ (by rw [hm2]; exact h2),
      arr_getElem?_set_ne _ _ _ (by rw [hm1]; exact h1),
      arr_getElem?_set_ne _ _ _ h0]
  · rw [show f + 17 = (f + 5) + 12 from rfl]
    rw [step_mc_aastore_null3 hl30 hget h02 hs0 hs1 hs2]
    rw [step_mc_aastore_uint hl30 hlv (jvmHeap_get?_set_self hget) hs3 h3, jvmHeap_set_set]

private theorem step_mc_quad_null3_uint_sub1 {f pc : Nat} {k : UInt32}
    {eLoc innerAddr : Nat} {rest : List JvmInstr} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {elems : Array JvmVal} {eVal : UInt32}
    (hk : k.toNat + 3 < 50)
    (hl30 : locs 30 = .heapRef innerAddr)
    (hle : locs eLoc = .i32 eVal)
    (hget : jh.get? innerAddr = some (.objArray "java/lang/Object" elems))
    (hsz : elems.size = 50) :
    ∃ elems' : Array JvmVal,
      elems'.size = 50 ∧
      elems'[k.toNat + 3]? = some (.boxedUInt (eVal - 1)) ∧
      (∀ idx, idx ≠ k.toNat → idx ≠ k.toNat + 1 → idx ≠ k.toNat + 2 → idx ≠ k.toNat + 3 →
        elems'[idx]? = elems[idx]?) ∧
      runJvmResFast (f + 20) f_Algorithm_parseMCNodeLine_prog pc
          (.aload 30 :: .iconst k :: .aconstNull :: .aastore ::
           .aload 30 :: .iconst (k + 1) :: .aconstNull :: .aastore ::
           .aload 30 :: .iconst (k + 2) :: .aconstNull :: .aastore ::
           .aload 30 :: .iconst (k + 3) :: .iload eLoc :: .iconst 1 :: .isub ::
           .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" ::
           .invokestatic "kotlin/UInt" "box-impl" "(I)Lkotlin/UInt;" :: .aastore :: rest)
          ⟨pc, stkRest, locs, jh, hp⟩ =
        runJvmResFast f f_Algorithm_parseMCNodeLine_prog (pc + 20) rest
          ⟨pc + 20, stkRest, locs, jh.set innerAddr (.objArray "java/lang/Object" elems'), hp⟩ := by
  have hk2_32 : k.toNat + 2 < 2 ^ 32 := Nat.lt_trans (Nat.lt_of_succ_lt hk) (by decide : 50 < 2 ^ 32)
  have hk3_31 : k.toNat + 3 < 2 ^ 31 := Nat.lt_trans hk (by decide : 50 < 2 ^ 31)
  have hm1 : (k + 1).toNat = k.toNat + 1 := mc_u32_add_toNat (Nat.lt_of_succ_lt hk2_32)
  have hm2 : (k + 2).toNat = k.toNat + 2 := mc_u32_add_toNat hk2_32
  have hm3 : (k + 3).toNat = k.toNat + 3 := mc_u32_add_toNat (Nat.lt_trans hk3_31 (by decide : 2 ^ 31 < 2 ^ 32))
  have hk0_31 : k.toNat < 2 ^ 31 :=
    Nat.lt_trans (Nat.lt_of_le_of_lt (Nat.le_add_right k.toNat 3) hk) (by decide : 50 < 2 ^ 31)
  have hs0 : k.toBitVec.slt 0#32 = false := u32_slt_zero_of_lt_2_31 hk0_31
  have hs1 : (k + 1).toBitVec.slt 0#32 = false := mc_u32_add_slt_zero (Nat.lt_of_succ_lt (Nat.lt_of_succ_lt hk3_31))
  have hs2 : (k + 2).toBitVec.slt 0#32 = false := mc_u32_add_slt_zero (Nat.lt_of_succ_lt hk3_31)
  have hs3 : (k + 3).toBitVec.slt 0#32 = false := mc_u32_add_slt_zero hk3_31
  have h02 : k.toNat + 2 < elems.size := by rw [hsz]; exact Nat.lt_of_succ_lt hk
  let e1 := (((elems.set k.toNat .null (Nat.lt_trans (Nat.lt_add_of_pos_right (by decide : 0 < 2)) h02)).set
    (k + 1).toNat .null (by rw [Array.size_set, hm1]; exact Nat.lt_of_succ_lt h02)).set
    (k + 2).toNat .null (by rw [Array.size_set, Array.size_set, hm2]; exact h02))
  have hsz1 : e1.size = 50 := by simp only [e1, Array.size_set, hsz]
  have h3 : (k + 3).toNat < e1.size := by rw [hm3, hsz1]; exact hk
  let e2 := e1.set (k + 3).toNat (.boxedUInt (eVal - 1)) h3
  have hsz2 : e2.size = 50 := by simp only [e2, Array.size_set, hsz1]
  refine ⟨e2, hsz2, ?_, ?_, ?_⟩
  · dsimp only [e2]; rw [← hm3]; exact arr_getElem?_set_eq _ _ _
  · intro idx h0 h1 h2 h3ne
    dsimp only [e2, e1]
    rw [arr_getElem?_set_ne _ _ _ (by rw [hm3]; exact h3ne),
      arr_getElem?_set_ne _ _ _ (by rw [hm2]; exact h2),
      arr_getElem?_set_ne _ _ _ (by rw [hm1]; exact h1),
      arr_getElem?_set_ne _ _ _ h0]
  · rw [show f + 20 = (f + 8) + 12 from rfl]
    rw [step_mc_aastore_null3 hl30 hget h02 hs0 hs1 hs2]
    rw [step_mc_aastore_uint_sub1 hl30 hle (jvmHeap_get?_set_self hget) hs3 h3, jvmHeap_set_set]

private theorem step_parseMC_fill_quad {f pc : Nat} {kNull : UInt32}
    {vLoc sLoc eLoc innerAddr : Nat} {rest : List JvmInstr} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {elems : Array JvmVal} {vVal sVal eVal : UInt32}
    (hk38 : kNull.toNat ≤ 38)
    (hl30 : locs 30 = .heapRef innerAddr)
    (hlv : locs vLoc = .i32 vVal) (hls : locs sLoc = .i32 sVal) (hle : locs eLoc = .i32 eVal)
    (hget : jh.get? innerAddr = some (.objArray "java/lang/Object" elems))
    (hsz : elems.size = 50) :
    ∃ elems' : Array JvmVal,
      elems'.size = 50 ∧
      elems'[kNull.toNat + 3]? = some (.boxedUInt vVal) ∧
      elems'[kNull.toNat + 7]? = some (.boxedUInt sVal) ∧
      elems'[kNull.toNat + 11]? = some (.boxedUInt (eVal - 1)) ∧
      (∀ idx, idx < kNull.toNat → elems'[idx]? = elems[idx]?) ∧
      runJvmResFast (f + 54) f_Algorithm_parseMCNodeLine_prog pc
          (parseMCQuadInstrs kNull vLoc sLoc eLoc rest) ⟨pc, stkRest, locs, jh, hp⟩ =
        runJvmResFast f f_Algorithm_parseMCNodeLine_prog (pc + 54) rest
          ⟨pc + 54, stkRest, locs, jh.set innerAddr (.objArray "java/lang/Object" elems'), hp⟩ := by
  have hk3 : kNull.toNat + 3 < 50 := Nat.lt_of_le_of_lt (Nat.add_le_add_right hk38 3) (by decide)
  rcases step_mc_quad_null3_uint (f := f + 37) (pc := pc) hk3 hl30 hlv hget hsz with
    ⟨e1, hsz1, he1_v, he1_p, hrun1⟩
  have hk4_toNat : (kNull + 4).toNat = kNull.toNat + 4 :=
    mc_u32_add_toNat (Nat.lt_of_le_of_lt (Nat.add_le_add_right hk38 4) (by decide))
  have hk7 : (kNull + 4).toNat + 3 < 50 := by
    rw [hk4_toNat]; exact Nat.lt_of_le_of_lt (Nat.add_le_add_right hk38 7) (by decide)
  rcases step_mc_quad_null3_uint (f := f + 20) (pc := pc + 17) hk7 hl30 hls
      (jvmHeap_get?_set_self hget) hsz1 with
    ⟨e2, hsz2, he2_s, he2_p, hrun2⟩
  have hk8_toNat : (kNull + 8).toNat = kNull.toNat + 8 :=
    mc_u32_add_toNat (Nat.lt_of_le_of_lt (Nat.add_le_add_right hk38 8) (by decide))
  have hk11 : (kNull + 8).toNat + 3 < 50 := by
    rw [hk8_toNat]; exact Nat.lt_of_le_of_lt (Nat.add_le_add_right hk38 11) (by decide)
  rcases step_mc_quad_null3_uint_sub1 (f := f) (pc := pc + 34) hk11 hl30 hle
      (jvmHeap_get?_set_self hget) hsz2 with
    ⟨e3, hsz3, he3_e, he3_p, hrun3⟩
  have h5_eq : (kNull + 4) + 1 = kNull + 5 := mc_u32_add_add kNull 4 1
  have h6_eq : (kNull + 4) + 2 = kNull + 6 := mc_u32_add_add kNull 4 2
  have h7_eq : (kNull + 4) + 3 = kNull + 7 := mc_u32_add_add kNull 4 3
  have h9_eq : (kNull + 8) + 1 = kNull + 9 := mc_u32_add_add kNull 8 1
  have h10_eq : (kNull + 8) + 2 = kNull + 10 := mc_u32_add_add kNull 8 2
  have h11_eq : (kNull + 8) + 3 = kNull + 11 := mc_u32_add_add kNull 8 3
  have hk4_0 : (kNull + 4).toNat = kNull.toNat + 4 := hk4_toNat
  have hk4_1 : (kNull + 4).toNat + 1 = kNull.toNat + 5 := by rw [hk4_toNat, Nat.add_assoc]
  have hk4_2 : (kNull + 4).toNat + 2 = kNull.toNat + 6 := by rw [hk4_toNat, Nat.add_assoc]
  have hk4_3 : (kNull + 4).toNat + 3 = kNull.toNat + 7 := by rw [hk4_toNat, Nat.add_assoc]
  have hk8_0 : (kNull + 8).toNat = kNull.toNat + 8 := hk8_toNat
  have hk8_1 : (kNull + 8).toNat + 1 = kNull.toNat + 9 := by rw [hk8_toNat, Nat.add_assoc]
  have hk8_2 : (kNull + 8).toNat + 2 = kNull.toNat + 10 := by rw [hk8_toNat, Nat.add_assoc]
  have hk8_3 : (kNull + 8).toNat + 3 = kNull.toNat + 11 := by rw [hk8_toNat, Nat.add_assoc]
  refine ⟨e3, hsz3, ?_, ?_, ?_, ?_, ?_⟩
  · rw [he3_p, he2_p, he1_v]
    all_goals (
      try rw [hk8_toNat]
      try rw [hk4_toNat]
      try rw [Nat.add_assoc]
      apply mc_add_ne_add; decide)
  · rw [he3_p, show kNull.toNat + 7 = (kNull + 4).toNat + 3 from by rw [hk4_toNat, Nat.add_assoc], he2_s]
    all_goals (
      try rw [hk8_toNat]
      try rw [Nat.add_assoc]
      apply mc_add_ne_add; decide)
  · rw [show kNull.toNat + 11 = (kNull + 8).toNat + 3 from by rw [hk8_toNat, Nat.add_assoc], he3_e]
  · intro idx hlt
    rw [he3_p, he2_p, he1_p]
    all_goals (
      try rw [hk8_toNat]
      try rw [hk4_toNat]
      try rw [Nat.add_assoc]
      first | (apply Nat.ne_of_lt; exact hlt) | (apply mc_ne_add_of_lt; exact hlt))
  · dsimp only [parseMCQuadInstrs]
    rw [show f + 54 = (f + 37) + 17 from by rw [Nat.add_assoc], hrun1]
    change runJvmResFast (f + 20 + 17) f_Algorithm_parseMCNodeLine_prog (pc + 17)
        (.aload 30 :: .iconst (kNull + 4) :: .aconstNull :: .aastore ::
         .aload 30 :: .iconst (kNull + 5) :: .aconstNull :: .aastore ::
         .aload 30 :: .iconst (kNull + 6) :: .aconstNull :: .aastore ::
         .aload 30 :: .iconst (kNull + 7) :: .iload sLoc ::
         .invokestatic "kotlin/UInt" "box-impl" "(I)Lkotlin/UInt;" :: .aastore :: _) _ = _
    rw [← h5_eq, ← h6_eq, ← h7_eq, hrun2, jvmHeap_set_set]
    change runJvmResFast (f + 20) f_Algorithm_parseMCNodeLine_prog (pc + 17 + 17)
        (.aload 30 :: .iconst (kNull + 8) :: .aconstNull :: .aastore ::
         .aload 30 :: .iconst (kNull + 9) :: .aconstNull :: .aastore ::
         .aload 30 :: .iconst (kNull + 10) :: .aconstNull :: .aastore ::
         .aload 30 :: .iconst (kNull + 11) :: .iload eLoc :: .iconst 1 :: .isub ::
         .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" ::
         .invokestatic "kotlin/UInt" "box-impl" "(I)Lkotlin/UInt;" :: .aastore :: rest) _ = _
    rw [← h9_eq, ← h10_eq, ← h11_eq, hrun3, jvmHeap_set_set]

private theorem mc_outer1_eq
    (h : (0 : UInt32).toNat < (Array.replicate (2 : UInt32).toNat (JvmVal.null : JvmVal)).size) :
    (Array.replicate (2 : UInt32).toNat (JvmVal.null : JvmVal)).set
      (0 : UInt32).toNat (.boxedInt 1) h = #[.boxedInt 1, .null] := rfl

private theorem mc_outer2_eq (v : JvmVal)
    (h : (1 : UInt32).toNat < (#[.boxedInt 1, .null] : Array JvmVal).size) :
    ((#[.boxedInt 1, .null] : Array JvmVal).set (1 : UInt32).toNat v h) = #[.boxedInt 1, v] := rfl

private theorem step_parseMC_alloc_init {f : Nat} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {lv : UInt32} (hl5 : locs 5 = .i32 lv) :
    ∃ (outerAddr innerAddr : Nat) (jh5 : Jvm.JvmHeap AlgExt) (inner2 : Array JvmVal),
      outerAddr ≠ innerAddr ∧
      jh5.get? outerAddr = some (.objArray "java/lang/Object" #[.boxedInt 1, .null]) ∧
      jh5.get? innerAddr = some (.objArray "java/lang/Object" inner2) ∧
      inner2.size = 50 ∧
      inner2[1]? = some (.boxedUInt lv) ∧
      runJvmResFast (f + 23) f_Algorithm_parseMCNodeLine_prog 460
          (f_Algorithm_parseMCNodeLine_prog.drop 460) ⟨460, [], locs, jh, hp⟩ =
        runJvmResFast f f_Algorithm_parseMCNodeLine_prog 483
          (f_Algorithm_parseMCNodeLine_prog.drop 483)
          ⟨483, [.i32 1, .heapRef outerAddr],
            setLocal (setLocal locs 29 (.heapRef outerAddr)) 30 (.heapRef innerAddr), jh5, hp⟩ := by
  rw [parseMC_drop_460]
  step1
  rw [runJvmResFast_anewarray_obj (by decide)]
  step1; step1; step1; step1; step1
  dsimp only [setLocal, Jvm.JvmVal.asI32]; simp only [↓reduceIte]
  have hgetOut0 : (jh.alloc (.objArray "java/lang/Object"
      (Array.replicate (2 : UInt32).toNat (JvmVal.null : JvmVal)))).2.get? jh.objects.size =
      some (.objArray "java/lang/Object" (Array.replicate (2 : UInt32).toNat (JvmVal.null : JvmVal))) :=
    jvmHeap_get?_alloc_self _ _
  rw [runJvmResFast_aastore hgetOut0 (by decide) (by decide), mc_outer1_eq]
  step1; step1; step1
  rw [runJvmResFast_anewarray_obj (by decide)]
  step1; step1; step1; step1; step1
  dsimp only [setLocal, Jvm.JvmVal.asI32]; simp only [↓reduceIte]
  let outer0 := (jh.alloc (.objArray "java/lang/Object"
    (Array.replicate (2 : UInt32).toNat (JvmVal.null : JvmVal)))).2
  let outer1 := outer0.set jh.objects.size (.objArray "java/lang/Object" #[.boxedInt 1, .null])
  let inner0 := Array.replicate (50 : UInt32).toNat (JvmVal.null : JvmVal)
  have h50sz : inner0.size = 50 := Array.size_replicate
  have hs0 : (0 : UInt32).toBitVec.slt 0#32 = false := by decide
  have hlt0 : (0 : UInt32).toNat < inner0.size := by rw [h50sz]; decide
  let h3 := (outer1.alloc (.objArray "java/lang/Object" inner0)).2
  let inner1 := inner0.set (0 : UInt32).toNat (.boxedInt 0) hlt0
  let h4 := h3.set outer1.objects.size (.objArray "java/lang/Object" inner1)
  have hs1 : (1 : UInt32).toBitVec.slt 0#32 = false := by decide
  have hlt1 : (1 : UInt32).toNat < inner1.size := by simp only [inner1, Array.size_set, h50sz]; decide
  let inner2 := inner1.set (1 : UInt32).toNat (.boxedUInt lv) hlt1
  let h5 := h4.set outer1.objects.size (.objArray "java/lang/Object" inner2)
  have hgetIn0 : h3.get? outer1.objects.size = some (.objArray "java/lang/Object" inner0) :=
    jvmHeap_get?_alloc_self _ _
  have hgetIn0' := hgetIn0
  dsimp only [h3, outer1, outer0, inner0] at hgetIn0'
  rw [runJvmResFast_aastore hgetIn0' hs0 hlt0]
  rw [show f + (23 - 1 - 1 - 1 - 1 - 1 - 1 - 1 - 1 - 1 - 1 - 1 - 1 - 1 - 1 - 1 - 1 - 1 - 1) =
    (f + 5) from by omega,
    show 460 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = 478 from rfl]
  have hgetIn1 : h4.get? outer1.objects.size = some (.objArray "java/lang/Object" inner1) :=
    jvmHeap_get?_set_self hgetIn0
  have hl5' : setLocal (setLocal locs 29 (.heapRef jh.objects.size)) 30 (.heapRef outer1.objects.size) 5 =
      .i32 lv := by
    rw [setLocal_ne_eq rfl, setLocal_ne_eq rfl, hl5]
  have hstep := step_mc_aastore_uint (f := f) (pc := 478) (rest := f_Algorithm_parseMCNodeLine_prog.drop 483)
    (stkRest := [.i32 1, .heapRef jh.objects.size]) (hp := hp) (by simp [setLocal]) hl5' hgetIn1 hs1 hlt1
  dsimp only [h4, inner1, h3, outer1, outer0, inner0] at hstep
  rw [hstep, jvmHeap_set_set]
  have hltOut : jh.objects.size < outer1.objects.size := by
    simp [outer1, outer0, Jvm.JvmHeap.set, Jvm.JvmHeap.alloc]
  have hne4 : jh.objects.size ≠ outer1.objects.size := Nat.ne_of_lt hltOut
  refine ⟨jh.objects.size, _, _, inner2, hne4, ?_,
    jvmHeap_get?_set_self hgetIn0, by simp [inner2, inner1, inner0], by simp [inner2, inner1, inner0], rfl⟩
  have hget3 : h3.get? jh.objects.size = some (.objArray "java/lang/Object" #[.boxedInt 1, .null]) := by
    rw [jvmHeap_get?_alloc_lt _ _ hltOut]
    exact jvmHeap_get?_set_self hgetOut0
  dsimp only [h4, h3, outer1, outer0, inner0]
  rw [jvmHeap_get?_set_ne _ _ hne4, hget3]

private theorem step_parseMC_alloc_finish {f outerAddr innerAddr : Nat}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {q4Arr : Array JvmVal}
    {lv nw nws nwe ne nes nee sw sws swe se ses see : UInt32}
    (hne : outerAddr ≠ innerAddr) (hl29 : locs 29 = .heapRef outerAddr)
    (hl30 : locs 30 = .heapRef innerAddr)
    (hgetOut : jh.get? outerAddr = some (.objArray "java/lang/Object" #[.boxedInt 1, .null]))
    (hgetIn : jh.get? innerAddr = some (.objArray "java/lang/Object" q4Arr))
    (hq1 : q4Arr[1]? = some (.boxedUInt lv))
    (hq5 : q4Arr[5]? = some (.boxedUInt nw)) (hq9 : q4Arr[9]? = some (.boxedUInt nws))
    (hq13 : q4Arr[13]? = some (.boxedUInt (nwe - 1)))
    (hq17 : q4Arr[17]? = some (.boxedUInt ne)) (hq21 : q4Arr[21]? = some (.boxedUInt nes))
    (hq25 : q4Arr[25]? = some (.boxedUInt (nee - 1)))
    (hq29 : q4Arr[29]? = some (.boxedUInt sw)) (hq33 : q4Arr[33]? = some (.boxedUInt sws))
    (hq37 : q4Arr[37]? = some (.boxedUInt (swe - 1)))
    (hq41 : q4Arr[41]? = some (.boxedUInt se)) (hq45 : q4Arr[45]? = some (.boxedUInt ses))
    (hq49 : q4Arr[49]? = some (.boxedUInt (see - 1))) :
    ∃ v st',
      runJvmResFast (f + 6) f_Algorithm_parseMCNodeLine_prog 699
          (f_Algorithm_parseMCNodeLine_prog.drop 699)
          ⟨699, [.i32 1, .heapRef outerAddr], locs, jh, hp⟩ = some (v, st') ∧
      decodeOptMCNodeLine st'.jvmHeap v =
        some (some ⟨lv, nw, nws, nwe - 1, ne, nes, nee - 1, sw, sws, swe - 1, se, ses, see - 1⟩) ∧
      st'.heap = hp := by
  rw [parseMC_drop_699]
  step1; dsimp only; rw [hl30]
  rw [runJvmResFast_aastore hgetOut (by decide) (by decide), mc_outer2_eq]
  step1; step1; step1
  dsimp only [setLocal]; simp only [↓reduceIte]
  rw [hl29]
  rw [runJvmResFast_areturn]
  refine ⟨_, _, rfl, ?_, rfl⟩
  dsimp only [decodeOptMCNodeLine]
  rw [jvmHeap_get?_set_self hgetOut]
  have ha0 : (#[.boxedInt 1, .heapRef innerAddr] : Array JvmVal)[0]? = some (.boxedInt 1) := rfl
  have ha1 : (#[.boxedInt 1, .heapRef innerAddr] : Array JvmVal)[1]? = some (.heapRef innerAddr) := rfl
  dsimp only
  rw [ha0, ha1]
  dsimp only
  rw [jvmHeap_get?_set_ne _ _ hne.symm, hgetIn]
  simp only [hq1, hq5, hq9, hq13, hq17, hq21, hq25, hq29, hq33, hq37, hq41, hq45, hq49,
    Option.bind_some, decodeUIntBox?]

private theorem step_parseMC_alloc_result {f : Nat} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {lim lv nw nws nwe ne nes nee sw sws swe se ses see q5 : UInt32}
    (hl1 : locs 1 = .i32 lim) (hl5 : locs 5 = .i32 lv)
    (hl10 : locs 10 = .i32 nw) (hl6 : locs 6 = .i32 nws) (hl11 : locs 11 = .i32 nwe)
    (hl15 : locs 15 = .i32 ne) (hl12 : locs 12 = .i32 nes) (hl16 : locs 16 = .i32 nee)
    (hl20 : locs 20 = .i32 sw) (hl17 : locs 17 = .i32 sws) (hl21 : locs 21 = .i32 swe)
    (hl25 : locs 25 = .i32 se) (hl22 : locs 22 = .i32 ses) (hl26 : locs 26 = .i32 see)
    (hl27 : locs 27 = .i32 q5) :
    ∃ v st',
      runJvmResFast (f + 248) f_Algorithm_parseMCNodeLine_prog 445
          (f_Algorithm_parseMCNodeLine_prog.drop 445) ⟨445, [], locs, jh, hp⟩ =
        some (v, st') ∧
      decodeOptMCNodeLine st'.jvmHeap v =
        some (if q5 == lim then
          some ⟨lv, nw, nws, nwe - 1, ne, nes, nee - 1, sw, sws, swe - 1, se, ses, see - 1⟩
        else none) ∧
      st'.heap = hp := by
  by_cases hq : q5 == lim
  · simp only [hq, ↓reduceIte]
    rw [parseMC_drop_445]
    step1; dsimp only; rw [hl27]; step1; dsimp only; rw [hl1]
    rw [show f + (248 - 1 - 1) = (f + 245) + 1 from by omega]
    rw [runJvmResFast_if_icmpeq_branch (beq_iff_eq.mp hq)]
    rcases step_parseMC_alloc_init (f := f + 222) hl5 with
      ⟨outerAddr, innerAddr, h5, inner2, hne, hgetOut, hgetIn2, hsz2, h1eq, hinitRun⟩
    rw [show f + 245 = (f + 222) + 23 from by omega, hinitRun]
    let locs30 := setLocal (setLocal locs 29 (.heapRef outerAddr)) 30 (.heapRef innerAddr)
    have hl29 : locs30 29 = .heapRef outerAddr := by simp [locs30, setLocal]
    have hl30 : locs30 30 = .heapRef innerAddr := by simp [locs30, setLocal]
    have hneLoc : ∀ k v, k ≠ 29 → k ≠ 30 → locs k = v → locs30 k = v := by
      intro k v h29 h30 hk; simp [locs30, setLocal, h30, h29, hk]
    rcases step_parseMC_fill_quad (f := f + 168) (pc := 483) (kNull := 2) (vLoc := 10)
        (sLoc := 6) (eLoc := 11) (innerAddr := innerAddr)
        (rest := f_Algorithm_parseMCNodeLine_prog.drop 537)
        (stkRest := [.i32 1, .heapRef outerAddr]) (locs := locs30) (jh := h5) (hp := hp)
        (elems := inner2) (by decide) hl30
        (hneLoc 10 _ (by omega) (by omega) hl10)
        (hneLoc 6 _ (by omega) (by omega) hl6)
        (hneLoc 11 _ (by omega) (by omega) hl11) hgetIn2 hsz2 with
      ⟨q1Arr, hq1sz, hq1_5, hq1_9, hq1_13, hq1_lt, hq1Run⟩
    have hq1_1 : q1Arr[1]? = some (.boxedUInt lv) := by rw [hq1_lt 1 (by decide), h1eq]
    rw [parseMC_drop_483, show f + 222 = (f + 168) + 54 from by omega, hq1Run,
      show (483 + 54 : Nat) = 537 from rfl]
    rcases step_parseMC_fill_quad (f := f + 114) (pc := 537) (kNull := 14) (vLoc := 15)
        (sLoc := 12) (eLoc := 16) (innerAddr := innerAddr)
        (rest := f_Algorithm_parseMCNodeLine_prog.drop 591)
        (stkRest := [.i32 1, .heapRef outerAddr]) (locs := locs30)
        (jh := h5.set innerAddr (.objArray "java/lang/Object" q1Arr)) (hp := hp)
        (elems := q1Arr) (by decide) hl30
        (hneLoc 15 _ (by omega) (by omega) hl15)
        (hneLoc 12 _ (by omega) (by omega) hl12)
        (hneLoc 16 _ (by omega) (by omega) hl16) (jvmHeap_get?_set_self hgetIn2) hq1sz with
      ⟨q2Arr, hq2sz, hq2_17, hq2_21, hq2_25, hq2_lt, hq2Run⟩
    rw [parseMC_drop_537, show f + 168 = (f + 114) + 54 from by omega, hq2Run,
      show (537 + 54 : Nat) = 591 from rfl, jvmHeap_set_set]
    rcases step_parseMC_fill_quad (f := f + 60) (pc := 591) (kNull := 26) (vLoc := 20)
        (sLoc := 17) (eLoc := 21) (innerAddr := innerAddr)
        (rest := f_Algorithm_parseMCNodeLine_prog.drop 645)
        (stkRest := [.i32 1, .heapRef outerAddr]) (locs := locs30)
        (jh := h5.set innerAddr (.objArray "java/lang/Object" q2Arr)) (hp := hp)
        (elems := q2Arr) (by decide) hl30
        (hneLoc 20 _ (by omega) (by omega) hl20)
        (hneLoc 17 _ (by omega) (by omega) hl17)
        (hneLoc 21 _ (by omega) (by omega) hl21) (jvmHeap_get?_set_self hgetIn2) hq2sz with
      ⟨q3Arr, hq3sz, hq3_29, hq3_33, hq3_37, hq3_lt, hq3Run⟩
    rw [parseMC_drop_591, show f + 114 = (f + 60) + 54 from by omega, hq3Run,
      show (591 + 54 : Nat) = 645 from rfl, jvmHeap_set_set]
    rcases step_parseMC_fill_quad (f := f + 6) (pc := 645) (kNull := 38) (vLoc := 25)
        (sLoc := 22) (eLoc := 26) (innerAddr := innerAddr)
        (rest := f_Algorithm_parseMCNodeLine_prog.drop 699)
        (stkRest := [.i32 1, .heapRef outerAddr]) (locs := locs30)
        (jh := h5.set innerAddr (.objArray "java/lang/Object" q3Arr)) (hp := hp)
        (elems := q3Arr) (by decide) hl30
        (hneLoc 25 _ (by omega) (by omega) hl25)
        (hneLoc 22 _ (by omega) (by omega) hl22)
        (hneLoc 26 _ (by omega) (by omega) hl26) (jvmHeap_get?_set_self hgetIn2) hq3sz with
      ⟨q4Arr, _hq4sz, hq4_41, hq4_45, hq4_49, hq4_lt, hq4Run⟩
    rw [parseMC_drop_645, show f + 60 = (f + 6) + 54 from by omega, hq4Run,
      show (645 + 54 : Nat) = 699 from rfl, jvmHeap_set_set]
    exact step_parseMC_alloc_finish hne hl29 hl30
      (by rw [jvmHeap_get?_set_ne _ _ hne, hgetOut])
      (jvmHeap_get?_set_self hgetIn2)
      (by rw [hq4_lt 1 (by decide), hq3_lt 1 (by decide), hq2_lt 1 (by decide)]; exact hq1_1)
      (by rw [hq4_lt 5 (by decide), hq3_lt 5 (by decide), hq2_lt 5 (by decide)]; exact hq1_5)
      (by rw [hq4_lt 9 (by decide), hq3_lt 9 (by decide), hq2_lt 9 (by decide)]; exact hq1_9)
      (by rw [hq4_lt 13 (by decide), hq3_lt 13 (by decide), hq2_lt 13 (by decide)]; exact hq1_13)
      (by rw [hq4_lt 17 (by decide), hq3_lt 17 (by decide)]; exact hq2_17)
      (by rw [hq4_lt 21 (by decide), hq3_lt 21 (by decide)]; exact hq2_21)
      (by rw [hq4_lt 25 (by decide), hq3_lt 25 (by decide)]; exact hq2_25)
      (by rw [hq4_lt 29 (by decide)]; exact hq3_29)
      (by rw [hq4_lt 33 (by decide)]; exact hq3_33)
      (by rw [hq4_lt 37 (by decide)]; exact hq3_37)
      hq4_41 hq4_45 hq4_49
  · have hqf : (q5 == lim) = false := Bool.eq_false_iff.mpr hq
    simp only [hqf, Bool.false_eq_true, ↓reduceIte]
    rw [parseMC_drop_445]
    step1; dsimp only; rw [hl27]; step1; dsimp only; rw [hl1]
    rw [show f + (248 - 1 - 1) = (f + 245) + 1 from by omega]
    rw [runJvmResFast_if_icmpeq_fallthrough hqf]
    rw [parseMC_drop_448]
    dsimp only [parseMCStageNone]
    rw [show f + 245 = (f + 233) + 12 from by omega]
    rw [step_parseMC_none_ret]
    refine ⟨_, _, rfl, ?_, rfl⟩
    dsimp only [decodeOptMCNodeLine]
    rw [jvmHeap_get?_set_push_self]
    rfl

private theorem step_parseMC_stage_band {f pc qIn resLoc innerLoc noneT someT defT : Nat}
    {restNone restSome restAfter : List JvmInstr}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {bytesAddr : Nat} {bytes : ByteArray} {lim qVal : UInt32}
    (hl0 : locs 0 = .heapRef bytesAddr) (hl1 : locs 1 = .i32 lim) (hlq : locs qIn = .i32 qVal)
    (hget : jh.get? bytesAddr = some (.byteArray bytes.data))
    (hres : 2 ≤ resLoc) (hband : resLoc < innerLoc)
    (hprefix : f_Algorithm_parseMCNodeLine_prog.drop pc =
      .aload 0 :: .iload qIn :: .iload 1 ::
      .invokestatic "MacroCellLeanKt" "f_Algorithm_parseUInt32At-BltQuoY"
        "([BII)Ljava/lang/Object;" ::
      .astore resLoc ::
      .aload resLoc :: .ldcStr "null cannot be cast to non-null type kotlin.Array<*>" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .aload resLoc :: .checkcast "[Ljava/lang/Object;" :: .iconst 0 :: .aaload ::
      .dup :: .ldcStr "null cannot be cast to non-null type kotlin.Int" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .checkcast "java/lang/Integer" ::
      .invokevirtual "java/lang/Integer" "intValue" "()I" ::
      .tableswitch 0 [noneT, someT] defT :: restAfter)
    (hdropNone : f_Algorithm_parseMCNodeLine_prog.drop noneT =
      .iconst 1 :: .anewarray "java/lang/Object" :: .astore (innerLoc + 1) ::
      .aload (innerLoc + 1) :: .iconst 0 :: .iconst 0 ::
      .invokestatic "java/lang/Integer" "valueOf" "(I)Ljava/lang/Integer;" ::
      .aastore :: .aload (innerLoc + 1) :: .astore innerLoc :: .aload innerLoc :: .areturn ::
      restNone)
    (hdropSome : f_Algorithm_parseMCNodeLine_prog.drop someT =
      parseMCStageSome resLoc innerLoc (innerLoc + 2) (innerLoc + 3) (innerLoc + 4)
        (innerLoc + 1) (innerLoc + 2) (innerLoc + 3) someT restSome) :
    match Algorithm.parseUInt32At bytes qVal lim with
    | none =>
      ∃ v st',
        runJvmResFast (f + 65) f_Algorithm_parseMCNodeLine_prog pc
            (f_Algorithm_parseMCNodeLine_prog.drop pc) ⟨pc, [], locs, jh, hp⟩ =
          some (v, st') ∧
        decodeOptMCNodeLine st'.jvmHeap v = some none ∧ st'.heap = hp
    | some r =>
      let qNext := Algorithm.skipSpaces bytes r.next lim
      ∃ jh' locs',
        (∀ a o, jh.get? a = some o → jh'.get? a = some o) ∧
        locs' 0 = .heapRef bytesAddr ∧ locs' 1 = .i32 lim ∧
        locs' (innerLoc + 1) = .i32 r.val ∧
        locs' (innerLoc + 2) = .i32 r.next ∧
        locs' (innerLoc + 3) = .i32 qNext ∧
        (∀ i, i < resLoc ∨ i > innerLoc + 4 → locs' i = locs i) ∧
        runJvmResFast (f + 65) f_Algorithm_parseMCNodeLine_prog pc
            (f_Algorithm_parseMCNodeLine_prog.drop pc) ⟨pc, [], locs, jh, hp⟩ =
          runJvmResFast f f_Algorithm_parseMCNodeLine_prog (someT + 57) restSome
            ⟨someT + 57, [], locs', jh', hp⟩ := by
  have hs := step_parseMC_stage (f := f) (pc := pc) (qIn := qIn) (resLoc := resLoc)
    (innerLoc := innerLoc) (valLoc := innerLoc + 1) (tmp1 := innerLoc + 2)
    (tmp2 := innerLoc + 3) (tmp3 := innerLoc + 4) (nextLoc := innerLoc + 2)
    (qOut := innerLoc + 3) (noneT := noneT) (someT := someT) (defT := defT)
    (locs := locs) (jh := jh) (hp := hp) hl0 hl1 hlq hget hprefix hdropNone
    hdropSome
    (by rw [← List.drop_drop, hdropSome]; exact parseMC_stageSome_drop23)
    (by rw [← List.drop_drop, hdropSome]; exact parseMC_stageSome_drop45)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  cases h : Algorithm.parseUInt32At bytes qVal lim with
  | none => rw [h] at hs; exact hs
  | some r =>
    rw [h] at hs
    rcases hs with ⟨jh', locs', hext, hl0', hl1', hlv, hln, hlq', hpres, hrun⟩
    refine ⟨jh', locs', hext, hl0', hl1', hlv, hln, hlq', ?_, hrun⟩
    intro i hi
    exact hpres i (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)

theorem parseMCNodeLine_equiv (bytes : ByteArray) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (bytesAddr : Nat) (hget : jh.get? bytesAddr = some (.byteArray bytes.data)) :
    ∃ v st',
      runJvmRes 600 f_Algorithm_parseMCNodeLine_prog
          ⟨0, [], setLocal (fun _ => .null) 0 (.heapRef bytesAddr), jh, hp⟩ =
        some (v, st') ∧
      decodeOptMCNodeLine st'.jvmHeap v = some (Algorithm.parseMCNodeLine bytes) ∧
      st'.heap = hp := by
  let lim := bytes.size.toUInt32
  let q0 := Algorithm.skipSpaces bytes 0 lim
  let locs12 := setLocal (setLocal (setLocal (fun _ => (.null : JvmVal)) 0 (.heapRef bytesAddr))
    1 (.i32 lim)) 2 (.i32 q0)
  have hpre : runJvmResFast ((525 + 63) + 12) f_Algorithm_parseMCNodeLine_prog 0
      (f_Algorithm_parseMCNodeLine_prog.drop 0)
      ⟨0, [], setLocal (fun _ => .null) 0 (.heapRef bytesAddr), jh, hp⟩ =
    runJvmResFast (525 + 63) f_Algorithm_parseMCNodeLine_prog 12
      (f_Algorithm_parseMCNodeLine_prog.drop 12) ⟨12, [], locs12, jh, hp⟩ :=
    step_parseMC_prelude hget
  have hs0 := step_parseMC_stage0 (f := 525) (locs := locs12) (jh := jh) (hp := hp)
    (bytesAddr := bytesAddr) (bytes := bytes) (lim := lim) (q0 := q0)
    (by simp [locs12, setLocal]) (by simp [locs12, setLocal]) (by simp [locs12, setLocal]) hget
  cases h0 : Algorithm.parseUInt32At bytes q0 lim with
  | none =>
    rw [h0] at hs0; dsimp only at hs0
    rcases hs0 with ⟨v, st', hrun0, hdec0, hhp0⟩
    have hmc : Algorithm.parseMCNodeLine bytes = none := by
      dsimp only [Algorithm.parseMCNodeLine]; rw [h0]
    refine ⟨v, st', ?_, ?_, hhp0⟩
    · apply runJvmRes_of_runJvmResFast0 600 _ _ _ rfl
      change runJvmResFast ((525 + 63) + 12) f_Algorithm_parseMCNodeLine_prog 0
        (f_Algorithm_parseMCNodeLine_prog.drop 0) _ = _
      rw [hpre]; exact hrun0
    · rw [hmc]; exact hdec0
  | some r0 =>
    rw [h0] at hs0; dsimp only at hs0
    rcases hs0 with ⟨jh1, locs1, hext1, hl1_0, hl1_1, hl1_5, hl1_6, hrun1⟩
    have hrun01 := hpre.trans hrun1
    let q1 := Algorithm.skipSpaces bytes r0.next lim
    have hs1 := step_parseMC_stage_band (f := 460) (pc := 97) (qIn := 6)
      (resLoc := 7) (innerLoc := 9) (noneT := 115) (someT := 127) (defT := 723)
      (locs := locs1) (jh := jh1) (hp := hp) hl1_0 hl1_1 hl1_6 (hext1 _ _ hget)
      (by omega) (by omega) parseMC_drop_97 parseMC_drop_115 parseMC_drop_127
    cases h1 : Algorithm.parseUInt32At bytes q1 lim with
    | none =>
      dsimp only [q1, lim] at h1; rw [h1] at hs1; dsimp only at hs1
      rcases hs1 with ⟨v, st', hrun1e, hdec1, hhp1⟩
      have hmc : Algorithm.parseMCNodeLine bytes = none := by
        dsimp only [Algorithm.parseMCNodeLine]; rw [h0]; dsimp only; rw [h1]
      refine ⟨v, st', ?_, ?_, hhp1⟩
      · apply runJvmRes_of_runJvmResFast0 600 _ _ _ rfl
        change runJvmResFast ((525 + 63) + 12) f_Algorithm_parseMCNodeLine_prog 0
          (f_Algorithm_parseMCNodeLine_prog.drop 0) _ = _
        rw [hrun01]; exact hrun1e
      · rw [hmc]; exact hdec1
    | some r1 =>
      dsimp only [q1, lim] at h1; rw [h1] at hs1; dsimp only at hs1
      rcases hs1 with ⟨jh2, locs2, hext2, hl2_0, hl2_1, hl2_10, hl2_11, hl2_12, hpres2, hrun2⟩
      have hrun02 := hrun01.trans hrun2
      have hl2_5 : locs2 5 = .i32 r0.val := by rw [hpres2 5 (by omega), hl1_5]
      have hl2_6 : locs2 6 = .i32 q1 := by rw [hpres2 6 (by omega), hl1_6]
      let q2 := Algorithm.skipSpaces bytes r1.next lim
      have hs2 := step_parseMC_stage_band (f := 395) (pc := 184) (qIn := 12)
        (resLoc := 13) (innerLoc := 14) (noneT := 202) (someT := 214) (defT := 717)
        (locs := locs2) (jh := jh2) (hp := hp) hl2_0 hl2_1 hl2_12
        (hext2 _ _ (hext1 _ _ hget)) (by omega) (by omega) parseMC_drop_184 parseMC_drop_202
        parseMC_drop_214
      cases h2 : Algorithm.parseUInt32At bytes q2 lim with
      | none =>
        dsimp only [q2, lim] at h2; rw [h2] at hs2; dsimp only at hs2
        rcases hs2 with ⟨v, st', hrun2e, hdec2, hhp2⟩
        have hmc : Algorithm.parseMCNodeLine bytes = none := by
          dsimp only [Algorithm.parseMCNodeLine]; rw [h0]; dsimp only; rw [h1]; dsimp only; rw [h2]
        refine ⟨v, st', ?_, ?_, hhp2⟩
        · apply runJvmRes_of_runJvmResFast0 600 _ _ _ rfl
          change runJvmResFast ((525 + 63) + 12) f_Algorithm_parseMCNodeLine_prog 0
            (f_Algorithm_parseMCNodeLine_prog.drop 0) _ = _
          rw [hrun02]; exact hrun2e
        · rw [hmc]; exact hdec2
      | some r2 =>
        dsimp only [q2, lim] at h2; rw [h2] at hs2; dsimp only at hs2
        rcases hs2 with ⟨jh3, locs3, hext3, hl3_0, hl3_1, hl3_15, hl3_16, hl3_17, hpres3, hrun3⟩
        have hrun03 := hrun02.trans hrun3
        let q3 := Algorithm.skipSpaces bytes r2.next lim
        have hs3 := step_parseMC_stage_band (f := 330) (pc := 271) (qIn := 17)
          (resLoc := 18) (innerLoc := 19) (noneT := 289) (someT := 301) (defT := 711)
          (locs := locs3) (jh := jh3) (hp := hp) hl3_0 hl3_1 hl3_17
          (hext3 _ _ (hext2 _ _ (hext1 _ _ hget))) (by omega) (by omega) parseMC_drop_271
          parseMC_drop_289 parseMC_drop_301
        cases h3 : Algorithm.parseUInt32At bytes q3 lim with
        | none =>
          dsimp only [q3, lim] at h3; rw [h3] at hs3; dsimp only at hs3
          rcases hs3 with ⟨v, st', hrun3e, hdec3, hhp3⟩
          have hmc : Algorithm.parseMCNodeLine bytes = none := by
            dsimp only [Algorithm.parseMCNodeLine]; rw [h0]; dsimp only; rw [h1]; dsimp only
            rw [h2]; dsimp only; rw [h3]
          refine ⟨v, st', ?_, ?_, hhp3⟩
          · apply runJvmRes_of_runJvmResFast0 600 _ _ _ rfl
            change runJvmResFast ((525 + 63) + 12) f_Algorithm_parseMCNodeLine_prog 0
              (f_Algorithm_parseMCNodeLine_prog.drop 0) _ = _
            rw [hrun03]; exact hrun3e
          · rw [hmc]; exact hdec3
        | some r3 =>
          dsimp only [q3, lim] at h3; rw [h3] at hs3; dsimp only at hs3
          rcases hs3 with ⟨jh4, locs4, hext4, hl4_0, hl4_1, hl4_20, hl4_21, hl4_22, hpres4, hrun4⟩
          have hrun04 := hrun03.trans hrun4
          let q4 := Algorithm.skipSpaces bytes r3.next lim
          have hs4 := step_parseMC_stage_band (f := 265) (pc := 358) (qIn := 22)
            (resLoc := 23) (innerLoc := 24) (noneT := 376) (someT := 388) (defT := 705)
            (locs := locs4) (jh := jh4) (hp := hp) hl4_0 hl4_1 hl4_22
            (hext4 _ _ (hext3 _ _ (hext2 _ _ (hext1 _ _ hget)))) (by omega) (by omega)
            parseMC_drop_358 parseMC_drop_376 parseMC_drop_388
          cases h4 : Algorithm.parseUInt32At bytes q4 lim with
          | none =>
            dsimp only [q4, lim] at h4; rw [h4] at hs4; dsimp only at hs4
            rcases hs4 with ⟨v, st', hrun4e, hdec4, hhp4⟩
            have hmc : Algorithm.parseMCNodeLine bytes = none := by
              dsimp only [Algorithm.parseMCNodeLine]; rw [h0]; dsimp only; rw [h1]; dsimp only
              rw [h2]; dsimp only; rw [h3]; dsimp only; rw [h4]
            refine ⟨v, st', ?_, ?_, hhp4⟩
            · apply runJvmRes_of_runJvmResFast0 600 _ _ _ rfl
              change runJvmResFast ((525 + 63) + 12) f_Algorithm_parseMCNodeLine_prog 0
                (f_Algorithm_parseMCNodeLine_prog.drop 0) _ = _
              rw [hrun04]; exact hrun4e
            · rw [hmc]; exact hdec4
          | some r4 =>
            dsimp only [q4, lim] at h4; rw [h4] at hs4; dsimp only at hs4
            rcases hs4 with ⟨jh5, locs5, _hext5, _hl5_0, hl5_1, hl5_25, hl5_26, hl5_27, hpres5, hrun5⟩
            have hrun05 := hrun04.trans hrun5
            have halloc := step_parseMC_alloc_result (f := 17) (locs := locs5) (jh := jh5) (hp := hp)
              (lim := lim) (lv := r0.val)
              (nw := r1.val) (nws := q1) (nwe := r1.next)
              (ne := r2.val) (nes := q2) (nee := r2.next)
              (sw := r3.val) (sws := q3) (swe := r3.next)
              (se := r4.val) (ses := q4) (see := r4.next)
              (q5 := Algorithm.skipSpaces bytes r4.next lim)
              hl5_1
              (by rw [hpres5 5 (by omega), hpres4 5 (by omega), hpres3 5 (by omega), hl2_5])
              (by rw [hpres5 10 (by omega), hpres4 10 (by omega), hpres3 10 (by omega), hl2_10])
              (by rw [hpres5 6 (by omega), hpres4 6 (by omega), hpres3 6 (by omega), hl2_6])
              (by rw [hpres5 11 (by omega), hpres4 11 (by omega), hpres3 11 (by omega), hl2_11])
              (by rw [hpres5 15 (by omega), hpres4 15 (by omega), hl3_15])
              (by rw [hpres5 12 (by omega), hpres4 12 (by omega), hpres3 12 (by omega), hl2_12])
              (by rw [hpres5 16 (by omega), hpres4 16 (by omega), hl3_16])
              (by rw [hpres5 20 (by omega), hl4_20])
              (by rw [hpres5 17 (by omega), hpres4 17 (by omega), hl3_17])
              (by rw [hpres5 21 (by omega), hl4_21])
              hl5_25
              (by rw [hpres5 22 (by omega), hl4_22])
              hl5_26 hl5_27
            rcases halloc with ⟨v, st', hrunA, hdecA, hhpA⟩
            have hmc : Algorithm.parseMCNodeLine bytes =
                (if (Algorithm.skipSpaces bytes r4.next lim == lim) = true then
                  some ⟨r0.val, r1.val, q1, r1.next - 1, r2.val, q2, r2.next - 1,
                    r3.val, q3, r3.next - 1, r4.val, q4, r4.next - 1⟩
                else none) := by
              dsimp only [Algorithm.parseMCNodeLine]; rw [h0]; dsimp only; rw [h1]; dsimp only
              rw [h2]; dsimp only; rw [h3]; dsimp only; rw [h4]
            refine ⟨v, st', ?_, ?_, hhpA⟩
            · apply runJvmRes_of_runJvmResFast0 600 _ _ _ rfl
              change runJvmResFast ((525 + 63) + 12) f_Algorithm_parseMCNodeLine_prog 0
                (f_Algorithm_parseMCNodeLine_prog.drop 0) _ = _
              rw [hrun05, show (388 + 57 : Nat) = 445 from rfl, show (265 : Nat) = 17 + 248 from by omega]
              exact hrunA
            · rw [hmc]; exact hdecA

end Algorithm.JvmVerification
