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
import proofs.JvmEquiv.Family5a

namespace Algorithm.JvmVerification

open Algorithm.JvmBytecode

private theorem arr3_get1 (a b c : JvmVal) (h : (1 : UInt32).toNat < #[a, b, c].size) :
    (#[a, b, c])[(1 : UInt32).toNat]'h = b := rfl

private theorem arr3_get2 (a b c : JvmVal) (h : (2 : UInt32).toNat < #[a, b, c].size) :
    (#[a, b, c])[(2 : UInt32).toNat]'h = c := rfl


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
  dsimp only
  erw [foldlM_map_mc nodes]


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
    Jvm.JvmState.jvmHeap, Jvm.JvmState.heap, Jvm.JvmVal.asI32?]))
  (try (conv => lhs; arg 3; simp only [Nat.reduceAdd]))
  (try (conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd]))
  (repeat (first
    | (conv => lhs; arg 5; arg 2; rw [setLocal_eq_val rfl])
    | (conv => lhs; arg 5; arg 2; rw [setLocal_ne_eq rfl])))
  (try (conv => lhs; arg 1; simp only [Nat.reduceSub, Nat.add_zero]))))

local macro "step1_ex" : tactic => `(tactic| (
  rw [step1_helper (by decide) rfl (by intro h; cases h) rfl]
  (try dsimp only [Jvm.JvmState.pc, Jvm.JvmState.stack, Jvm.JvmState.locals,
    Jvm.JvmState.jvmHeap, Jvm.JvmState.heap, Jvm.JvmVal.asI32?])
  (repeat (first
    | rw [setLocal_eq_val rfl]
    | rw [setLocal_ne_eq rfl]))
  (try simp only [Nat.reduceAdd, Nat.reduceSub, Nat.add_zero])))


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
  exact Jvm.runJvmResFast_invokestatic_step algHooks
    (Jvm.stepInvokeStatic_intrinsics_checkNotNull algHooks his)

private theorem runJvmResFast_areturn {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {rest : List JvmInstr} {pc0 : Nat} {v : JvmVal} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.areturn :: rest) ⟨pc0, v :: stkRest, locs, jh, hp⟩ =
      some (v, ⟨pc, v :: stkRest, locs, jh, hp⟩) := rfl

private theorem runJvmResFast_tableswitch {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {low : Int32} {targets : List Nat} {defT : Nat} {rest : List JvmInstr} {pc0 : Nat}
    {key : UInt32} {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.tableswitch low targets defT :: rest)
        ⟨pc0, .i32 key :: stkRest, locs, jh, hp⟩ =
      let t := Jvm.tableswitchTarget key low targets defT
      runJvmResFast f prog t (prog.drop t) ⟨t, stkRest, locs, jh, hp⟩ := by
  rw [runJvmResFast_at_branch_cons (hbr := rfl), evalResBranchInstrCons_tableswitch]


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


private theorem setLocal_ne {g : Nat → JvmVal} {k i : Nat} {v : JvmVal} (h : i ≠ k) :
    setLocal g k v i = g i := by simp [setLocal, h]


/-! ### deserializeMacrocell.loop -/

private theorem runJvmResFast_ifgt_branch {f pc tgt : Nat} {prog rest : List JvmInstr}
    {v : UInt32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hv : (0#32 : BitVec 32).slt v.toBitVec = true) :
    runJvmResFast (f + 1) prog pc (.ifgt tgt :: rest) ⟨pc, .i32 v :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog tgt (prog.drop tgt) ⟨tgt, stk, locs, jh, hp⟩ := by
  rw [runJvmResFast_at_branch_cons (hbr := rfl)]
  dsimp only [evalResBranchInstrCons]
  rw [Jvm.evalResBranchInstrCons_ifgt, hv]
  rfl

private theorem runJvmResFast_ifgt_fallthrough {f pc tgt : Nat} {prog rest : List JvmInstr}
    {v : UInt32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hv : (0#32 : BitVec 32).slt v.toBitVec = false) :
    runJvmResFast (f + 1) prog pc (.ifgt tgt :: rest) ⟨pc, .i32 v :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, stk, locs, jh, hp⟩ := by
  rw [runJvmResFast_at_branch_cons (hbr := rfl)]
  dsimp only [evalResBranchInstrCons]
  rw [Jvm.evalResBranchInstrCons_ifgt, hv]
  rfl

private theorem u8_sext_and_255 (b : UInt8) :
    UInt32.ofBitVec (b.toBitVec.signExtend 32) &&& (255 : UInt32) = b.toUInt32 := by
  revert b; decide

private theorem u8_cmp_48_sgt (b : UInt8) :
    ((0#32 : BitVec 32).slt (if (48 : UInt32) == b.toUInt32 then (0 : UInt32)
      else if (48 : UInt32).toBitVec.slt b.toUInt32.toBitVec then 4294967295 else 1).toBitVec) =
    decide (b < 48) := by
  revert b; decide

private theorem u8_cmp_57_sgt (b : UInt8) :
    ((0#32 : BitVec 32).slt (if b.toUInt32 == (57 : UInt32) then (0 : UInt32)
      else if b.toUInt32.toBitVec.slt (57 : UInt32).toBitVec then 4294967295 else 1).toBitVec) =
    decide (57 < b) := by
  revert b; decide

private theorem stepStatic_intrinsicsCompare
    {pc : Nat} {b a : UInt32} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .i32 b :: .i32 a :: rest, locs, jh, hp⟩
      "kotlin/jvm/internal/Intrinsics" "compare" "(II)I" =
      .inl (some ⟨pc + 1,
        .i32 (if a == b then 0
          else if a.toBitVec.slt b.toBitVec then 4294967295 else 1) :: rest,
        locs, jh, hp⟩) := rfl

private theorem stepStatic_growBufPush_mc {pc : Nat} {m : Algorithm.MacroCell} {nv : JvmVal}
    {nodes : Algorithm.GrowBuf Algorithm.MacroCell} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hn : mcNodes? nv = some nodes) :
    stepInvokeStatic ⟨pc, .ext (.mc m) :: nv :: rest, locs, jh, hp⟩
        "MacroCellLeanKt" "f_Algorithm_GrowBuf_push___redArg"
        "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, .ext (.mcGrowBuf (nodes.push m)) :: rest, locs, jh, hp⟩) := by
  cases nv with
  | ext e =>
    cases e with
    | mcGrowBuf b => simp only [mcNodes?, Option.some.injEq] at hn; subst hn; rfl
    | strGrowBuf b =>
      simp only [mcNodes?] at hn
      cases hemp : b.data.isEmpty && b.size == 0
      · simp [hemp] at hn
      · simp only [hemp, ↓reduceIte, Option.some.injEq] at hn
        subst hn
        change (if b.data.isEmpty && b.size == 0 then
            Sum.inl (some (⟨pc + 1, Jvm.JvmVal.ext (AlgExt.mcGrowBuf (Algorithm.GrowBuf.empty.push m)) :: rest,
              locs, jh, hp⟩ : JvmState))
          else Sum.inr none) = _
        simp only [hemp, ↓reduceIte]
    | _ => simp [mcNodes?] at hn
  | _ => simp [mcNodes?] at hn

private theorem stepStatic_growBufPush_u64 {pc : Nat} {x : UInt64} {lv : JvmVal}
    {leaves : Algorithm.GrowBuf UInt64} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hl : mcLeaves? lv = some leaves) :
    stepInvokeStatic ⟨pc, .boxedULong x :: lv :: rest, locs, jh, hp⟩
        "MacroCellLeanKt" "f_Algorithm_GrowBuf_push___redArg"
        "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, .ext (.u64GrowBuf (leaves.push x)) :: rest, locs, jh, hp⟩) := by
  cases lv with
  | ext e =>
    cases e with
    | u64GrowBuf b => simp only [mcLeaves?, Option.some.injEq] at hl; subst hl; rfl
    | strGrowBuf b =>
      simp only [mcLeaves?] at hl
      cases hemp : b.data.isEmpty && b.size == 0
      · simp [hemp] at hl
      · simp only [hemp, ↓reduceIte, Option.some.injEq] at hl
        subst hl
        change (if b.data.isEmpty && b.size == 0 then
            Sum.inl (some (⟨pc + 1, Jvm.JvmVal.ext (AlgExt.u64GrowBuf (Algorithm.GrowBuf.empty.push x)) :: rest,
              locs, jh, hp⟩ : JvmState))
          else Sum.inr none) = _
        simp only [hemp, ↓reduceIte]
    | _ => simp [mcLeaves?] at hl
  | _ => simp [mcLeaves?] at hl

private theorem stepStatic_growBufPush_bool {pc : Nat} {flag : Bool} {bv : JvmVal}
    {isLeaf : Algorithm.GrowBuf Bool} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hb : mcIsLeaf? bv = some isLeaf) :
    stepInvokeStatic ⟨pc, .boxedBool flag :: bv :: rest, locs, jh, hp⟩
        "MacroCellLeanKt" "f_Algorithm_GrowBuf_push___redArg"
        "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, .ext (.boolGrowBuf (isLeaf.push flag)) :: rest, locs, jh, hp⟩) := by
  cases bv with
  | ext e =>
    cases e with
    | boolGrowBuf b => simp only [mcIsLeaf?, Option.some.injEq] at hb; subst hb; rfl
    | strGrowBuf b =>
      simp only [mcIsLeaf?] at hb
      cases hemp : b.data.isEmpty && b.size == 0
      · simp [hemp] at hb
      · simp only [hemp, ↓reduceIte, Option.some.injEq] at hb
        subst hb
        change (if b.data.isEmpty && b.size == 0 then
            Sum.inl (some (⟨pc + 1, Jvm.JvmVal.ext (AlgExt.boolGrowBuf (Algorithm.GrowBuf.empty.push flag)) :: rest,
              locs, jh, hp⟩ : JvmState))
          else Sum.inr none) = _
        simp only [hemp, ↓reduceIte]
    | _ => simp [mcIsLeaf?] at hb
  | _ => simp [mcIsLeaf?] at hb

private theorem stepStatic_growBufPush_mcWarn {pc : Nat} {wv wVal : JvmVal}
    {warns : Algorithm.GrowBuf Algorithm.MacrocellWarning} {w : Algorithm.MacrocellWarning}
    {rest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hw : mcWarns? wv = some warns) (hrle : decodeRLEWarning jh wVal = none)
    (hmc : decodeMacrocellWarning jh wVal = some w) :
    stepInvokeStatic ⟨pc, wVal :: wv :: rest, locs, jh, hp⟩
        "MacroCellLeanKt" "f_Algorithm_GrowBuf_push___redArg"
        "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, .ext (.mcWarnGrowBuf (warns.push w)) :: rest, locs, jh, hp⟩) := by
  cases wv with
  | ext e =>
    cases e with
    | mcWarnGrowBuf b =>
      simp only [mcWarns?, Option.some.injEq] at hw; subst hw
      cases wVal with
      | allocRef s =>
        change (match decodeMacrocellWarning jh (Jvm.JvmVal.allocRef s) with
          | some w => Sum.inl (some (⟨pc + 1, Jvm.JvmVal.ext (AlgExt.mcWarnGrowBuf (b.push w)) :: rest,
              locs, jh, hp⟩ : JvmState))
          | none => Sum.inr none) = _
        rw [hmc]
      | heapRef a =>
        change (match decodeMacrocellWarning jh (Jvm.JvmVal.heapRef a) with
          | some w => Sum.inl (some (⟨pc + 1, Jvm.JvmVal.ext (AlgExt.mcWarnGrowBuf (b.push w)) :: rest,
              locs, jh, hp⟩ : JvmState))
          | none => Sum.inr none) = _
        rw [hmc]
      | _ => simp [decodeMacrocellWarning] at hmc
    | strGrowBuf b =>
      simp only [mcWarns?] at hw
      cases hemp : b.data.isEmpty && b.size == 0
      · simp [hemp] at hw
      · simp only [hemp, ↓reduceIte, Option.some.injEq] at hw
        subst hw
        cases wVal with
        | allocRef s =>
          change (if b.data.isEmpty && b.size == 0 then
              match match decodeRLEWarning jh (Jvm.JvmVal.allocRef s) with
                | some w => some (AlgExt.rleWarnGrowBuf (Algorithm.GrowBuf.empty.push w))
                | none =>
                  match decodeMacrocellWarning jh (Jvm.JvmVal.allocRef s) with
                  | some w => some (AlgExt.mcWarnGrowBuf (Algorithm.GrowBuf.empty.push w))
                  | none => (decodePlaintextWarning jh (Jvm.JvmVal.allocRef s)).map fun w =>
                      AlgExt.ptWarnGrowBuf (Algorithm.GrowBuf.empty.push w) with
              | some e => Sum.inl (some (⟨pc + 1, Jvm.JvmVal.ext e :: rest, locs, jh, hp⟩ : JvmState))
              | none => Sum.inr none
            else Sum.inr none) = _
          simp only [hemp, ↓reduceIte, hrle, hmc]
        | heapRef a =>
          change (if b.data.isEmpty && b.size == 0 then
              match match decodeRLEWarning jh (Jvm.JvmVal.heapRef a) with
                | some w => some (AlgExt.rleWarnGrowBuf (Algorithm.GrowBuf.empty.push w))
                | none =>
                  match decodeMacrocellWarning jh (Jvm.JvmVal.heapRef a) with
                  | some w => some (AlgExt.mcWarnGrowBuf (Algorithm.GrowBuf.empty.push w))
                  | none => (decodePlaintextWarning jh (Jvm.JvmVal.heapRef a)).map fun w =>
                      AlgExt.ptWarnGrowBuf (Algorithm.GrowBuf.empty.push w) with
              | some e => Sum.inl (some (⟨pc + 1, Jvm.JvmVal.ext e :: rest, locs, jh, hp⟩ : JvmState))
              | none => Sum.inr none
            else Sum.inr none) = _
          simp only [hemp, ↓reduceIte, hrle, hmc]
        | _ => simp [decodeMacrocellWarning] at hmc
    | _ => simp [mcWarns?] at hw
  | _ => simp [mcWarns?] at hw

private theorem stepStatic_growBufToArray_mcWarn {pc : Nat}
    {warns : Algorithm.GrowBuf Algorithm.MacrocellWarning} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    let (v, h') := encodeGrowBufArray jh encodeMacrocellWarning warns
    stepInvokeStatic ⟨pc, .ext (.mcWarnGrowBuf warns) :: rest, locs, jh, hp⟩
        "MacroCellLeanKt" "f_Algorithm_GrowBuf_toArray___redArg" "(Ljava/lang/Object;)[Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, v :: rest, locs, h', hp⟩) := rfl

private theorem stepStatic_parseMCNodeLine_none {pc : Nat} {addr : Nat}
    {bytes : ByteArray} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hget : jh.get? addr = some (.byteArray bytes.data))
    (hnone : Algorithm.parseMCNodeLine bytes = none) :
    let (resAddr, h') := jh.alloc (.objArray "java/lang/Object" #[.boxedInt 0])
    stepInvokeStatic ⟨pc, .heapRef addr :: rest, locs, jh, hp⟩
        "MacroCellLeanKt" "f_Algorithm_parseMCNodeLine" "([B)Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, .heapRef resAddr :: rest, locs, h', hp⟩) := by
  change (match decodeBytes ⟨pc, .heapRef addr :: rest, locs, jh, hp⟩ (.heapRef addr) with
    | some bs =>
      match Algorithm.parseMCNodeLine bs with
      | none =>
        let (resAddr, h') := jh.alloc (.objArray "java/lang/Object" #[.boxedInt 0])
        Sum.inl (some (⟨pc + 1, Jvm.JvmVal.heapRef resAddr :: rest, locs, h', hp⟩ : JvmState))
      | some nl =>
        let inner : Array JvmVal := (Array.replicate 50 Jvm.JvmVal.null)
          |>.set! 0 (Jvm.JvmVal.boxedInt 0)
          |>.set! 1 (Jvm.JvmVal.boxedUInt nl.level)
          |>.set! 5 (Jvm.JvmVal.boxedUInt nl.nw)
          |>.set! 9 (Jvm.JvmVal.boxedUInt nl.nwStart)
          |>.set! 13 (Jvm.JvmVal.boxedUInt nl.nwEnd)
          |>.set! 17 (Jvm.JvmVal.boxedUInt nl.ne)
          |>.set! 21 (Jvm.JvmVal.boxedUInt nl.neStart)
          |>.set! 25 (Jvm.JvmVal.boxedUInt nl.neEnd)
          |>.set! 29 (Jvm.JvmVal.boxedUInt nl.sw)
          |>.set! 33 (Jvm.JvmVal.boxedUInt nl.swStart)
          |>.set! 37 (Jvm.JvmVal.boxedUInt nl.swEnd)
          |>.set! 41 (Jvm.JvmVal.boxedUInt nl.se)
          |>.set! 45 (Jvm.JvmVal.boxedUInt nl.seStart)
          |>.set! 49 (Jvm.JvmVal.boxedUInt nl.seEnd)
        let (inAddr, h1) := jh.alloc (.objArray "java/lang/Object" inner)
        let (outAddr, h2) := h1.alloc (.objArray "java/lang/Object" #[.boxedInt 1, .heapRef inAddr])
        Sum.inl (some (⟨pc + 1, Jvm.JvmVal.heapRef outAddr :: rest, locs, h2, hp⟩ : JvmState))
    | none => Sum.inr none) = _
  simp only [decodeBytes, hget]
  have hb : (⟨bytes.data⟩ : ByteArray) = bytes := rfl
  rw [hb, hnone]
  dsimp only [Jvm.JvmHeap.alloc]

private theorem stepStatic_uintCtor5a {pc : Nat} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, stk, locs, jh, hp⟩ "kotlin/UInt" "constructor-impl" "(I)I" =
      .inl (some ⟨pc + 1, stk, locs, jh, hp⟩) := by
  cases hp; rfl

private theorem stepStatic_emptyMacroCellUInt32 {pc : Nat} {lvl : UInt32} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .i32 lvl :: rest, locs, jh, hp⟩
        "MacroCellLeanKt" "f_Algorithm_emptyMacroCellUInt32-WZ4Q5Ns"
        "(I)Lcom/alexvanyo/composelife/model/MacroCell;" =
      .inl (some ⟨pc + 1, .ext (.mc (Algorithm.emptyMacroCellUInt32 lvl)) :: rest, locs, jh, hp⟩) := rfl

private theorem stepStatic_makeCellNode {pc : Nat} {nw ne sw se : Algorithm.MacroCell}
    {rest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .ext (.mc se) :: .ext (.mc sw) :: .ext (.mc ne) :: .ext (.mc nw) :: rest,
        locs, jh, hp⟩
        "MacroCellLeanKt" "f_Algorithm_makeCellNode"
        ("(Lcom/alexvanyo/composelife/model/MacroCell;Lcom/alexvanyo/composelife/model/MacroCell;" ++
         "Lcom/alexvanyo/composelife/model/MacroCell;Lcom/alexvanyo/composelife/model/MacroCell;)" ++
         "Lcom/alexvanyo/composelife/model/MacroCell;") =
      .inl (some ⟨pc + 1, .ext (.mc (Algorithm.makeCellNode nw ne sw se)) :: rest, locs, jh, hp⟩) := rfl

private theorem strGrowBuf_eq_empty {b : Algorithm.GrowBuf String}
    (he : (b.data.isEmpty && b.size == 0) = true) :
    b = Algorithm.GrowBuf.empty := by
  rcases b with ⟨⟨l⟩, s⟩
  cases l with
  | nil =>
    simp only [Bool.and_eq_true, beq_iff_eq] at he
    have hs : s = 0 := he.2
    subst hs; rfl
  | cons _ _ => simp [Array.isEmpty] at he

private theorem stepStatic_macrocellCellChild {pc : Nat} {nv ilv : JvmVal}
    {lvl id : UInt32} {emptySub : Algorithm.MacroCell}
    {nodes : Algorithm.GrowBuf Algorithm.MacroCell} {isLeaf : Algorithm.GrowBuf Bool}
    {rest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hn : mcNodes? nv = some nodes) (hil : mcIsLeaf? ilv = some isLeaf) :
    let res := match Algorithm.macrocellCellChild nodes isLeaf lvl emptySub id with
      | some c => .ext (.mc c)
      | none => .null
    stepInvokeStatic ⟨pc, .i32 id :: .ext (.mc emptySub) :: .i32 lvl :: ilv :: nv :: rest,
        locs, jh, hp⟩
        "MacroCellLeanKt" "f_Algorithm_macrocellCellChild-xsr7cmg"
        ("(Ljava/lang/Object;Ljava/lang/Object;ILcom/alexvanyo/composelife/model/MacroCell;I)" ++
         "Lcom/alexvanyo/composelife/model/MacroCell;") =
      .inl (some ⟨pc + 1, res :: rest, locs, jh, hp⟩) := by
  have hfn : nv = .ext (.mcGrowBuf nodes) ∨
      (nv = .ext (.strGrowBuf Algorithm.GrowBuf.empty) ∧ nodes = Algorithm.GrowBuf.empty) := by
    cases nv with
    | ext e =>
      cases e with
      | mcGrowBuf b => simp only [mcNodes?, Option.some.injEq] at hn; exact Or.inl (by subst hn; rfl)
      | strGrowBuf b =>
        simp only [mcNodes?] at hn
        split at hn
        · next he =>
          simp only [Option.some.injEq] at hn; subst hn
          exact Or.inr ⟨congrArg (JvmVal.ext ∘ AlgExt.strGrowBuf) (strGrowBuf_eq_empty he), rfl⟩
        · cases hn
      | _ => simp [mcNodes?] at hn
    | _ => simp [mcNodes?] at hn
  have hfi : ilv = .ext (.boolGrowBuf isLeaf) ∨
      (ilv = .ext (.strGrowBuf Algorithm.GrowBuf.empty) ∧ isLeaf = Algorithm.GrowBuf.empty) := by
    cases ilv with
    | ext e =>
      cases e with
      | boolGrowBuf b => simp only [mcIsLeaf?, Option.some.injEq] at hil; exact Or.inl (by subst hil; rfl)
      | strGrowBuf b =>
        simp only [mcIsLeaf?] at hil
        split at hil
        · next he =>
          simp only [Option.some.injEq] at hil; subst hil
          exact Or.inr ⟨congrArg (JvmVal.ext ∘ AlgExt.strGrowBuf) (strGrowBuf_eq_empty he), rfl⟩
        · cases hil
      | _ => simp [mcIsLeaf?] at hil
    | _ => simp [mcIsLeaf?] at hil
  rcases hfn with rfl | ⟨rfl, rfl⟩ <;> rcases hfi with rfl | ⟨rfl, rfl⟩ <;> rfl

private theorem stepStatic_macrocellLeafChild {pc : Nat} {lv ilv : JvmVal} {id : UInt32}
    {leaves : Algorithm.GrowBuf UInt64} {isLeaf : Algorithm.GrowBuf Bool}
    {rest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hlv : mcLeaves? lv = some leaves) (hil : mcIsLeaf? ilv = some isLeaf) :
    let res := match Algorithm.macrocellLeafChild leaves isLeaf id with
      | some v => .boxedULong v
      | none => .null
    stepInvokeStatic ⟨pc, .i32 id :: ilv :: lv :: rest, locs, jh, hp⟩
        "MacroCellLeanKt" "f_Algorithm_macrocellLeafChild-jXDDuk8"
        "(Ljava/lang/Object;Ljava/lang/Object;I)Lkotlin/ULong;" =
      .inl (some ⟨pc + 1, res :: rest, locs, jh, hp⟩) := by
  have hfl : lv = .ext (.u64GrowBuf leaves) ∨
      (lv = .ext (.strGrowBuf Algorithm.GrowBuf.empty) ∧ leaves = Algorithm.GrowBuf.empty) := by
    cases lv with
    | ext e =>
      cases e with
      | u64GrowBuf b => simp only [mcLeaves?, Option.some.injEq] at hlv; exact Or.inl (by subst hlv; rfl)
      | strGrowBuf b =>
        simp only [mcLeaves?] at hlv
        split at hlv
        · next he =>
          simp only [Option.some.injEq] at hlv; subst hlv
          exact Or.inr ⟨congrArg (JvmVal.ext ∘ AlgExt.strGrowBuf) (strGrowBuf_eq_empty he), rfl⟩
        · cases hlv
      | _ => simp [mcLeaves?] at hlv
    | _ => simp [mcLeaves?] at hlv
  have hfi : ilv = .ext (.boolGrowBuf isLeaf) ∨
      (ilv = .ext (.strGrowBuf Algorithm.GrowBuf.empty) ∧ isLeaf = Algorithm.GrowBuf.empty) := by
    cases ilv with
    | ext e =>
      cases e with
      | boolGrowBuf b => simp only [mcIsLeaf?, Option.some.injEq] at hil; exact Or.inl (by subst hil; rfl)
      | strGrowBuf b =>
        simp only [mcIsLeaf?] at hil
        split at hil
        · next he =>
          simp only [Option.some.injEq] at hil; subst hil
          exact Or.inr ⟨congrArg (JvmVal.ext ∘ AlgExt.strGrowBuf) (strGrowBuf_eq_empty he), rfl⟩
        · cases hil
      | _ => simp [mcIsLeaf?] at hil
    | _ => simp [mcIsLeaf?] at hil
  rcases hfl with rfl | ⟨rfl, rfl⟩ <;> rcases hfi with rfl | ⟨rfl, rfl⟩ <;> rfl

private theorem stepStatic_ulongBox {pc : Nat} {x : UInt64} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .i64 x :: rest, locs, jh, hp⟩
        "kotlin/ULong" "box-impl" "(J)Lkotlin/ULong;" =
      .inl (some ⟨pc + 1, .boxedULong x :: rest, locs, jh, hp⟩) := rfl

private theorem drop_drop_add {α : Type} (l : List α) (a b : Nat) :
    l.drop (a + b) = (l.drop a).drop b := by
  rw [List.drop_drop, Nat.add_comm]

private def unboxUIntInstrs (pc : Nat) (idx : UInt32) (dst tmp tmp2 : Nat) : List JvmInstr :=
  [.aload 22, .checkcast "[Ljava/lang/Object;", .iconst idx, .aaload,
   .astore tmp, .iconst 0, .istore tmp2,
   .aload tmp, .instanceof "java/lang/Integer", .ifeq (pc + 15),
   .aload tmp, .checkcast "java/lang/Number",
   .invokevirtual "java/lang/Number" "intValue" "()I",
   .invokestatic "kotlin/UInt" "constructor-impl" "(I)I", .goto (pc + 21),
   .aload tmp, .ldcStr "null cannot be cast to non-null type kotlin.UInt",
   .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
     "(Ljava/lang/Object;Ljava/lang/String;)V",
   .aload tmp, .checkcast "kotlin/UInt",
   .invokevirtual "kotlin/UInt" "unbox-impl" "()I", .istore dst]

private def errTailInstrs (statusLoc arrLoc tmpLoc : Nat) : List JvmInstr :=
  [.aload 15,
   .invokestatic "MacroCellLeanKt" "f_Algorithm_GrowBuf_toArray___redArg"
     "(Ljava/lang/Object;)[Ljava/lang/Object;",
   .astore arrLoc,
   .newClass "com/alexvanyo/composelife/model/MacrocellResult", .dup,
   .aload statusLoc, .checkcast "com/alexvanyo/composelife/model/MacrocellStatus",
   .aload arrLoc, .iconst 0, .istore tmpLoc,
   .invokestatic "MacroCellLeanKt" "getEMPTY_LEVEL_4"
     "()Lcom/alexvanyo/composelife/model/MacroCell$Level4Node;",
   .checkcast "com/alexvanyo/composelife/model/MacroCell", .dup,
   .ldcStr "null cannot be cast to non-null type com.alexvanyo.composelife.model.MacroCell",
   .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
     "(Ljava/lang/Object;Ljava/lang/String;)V",
   .invokespecial "com/alexvanyo/composelife/model/MacrocellResult" "<init>"
     ("(Lcom/alexvanyo/composelife/model/MacrocellStatus;" ++
      "[Ljava/lang/Object;Lcom/alexvanyo/composelife/model/MacroCell;)V"),
   .areturn]

private def cellChildInstrs (pc idLoc startLoc endLoc dstLoc errLoc1 errLoc2 errTmp : Nat) :
    List JvmInstr :=
  [.aload 12, .aload 14, .iload 23, .aload 36, .iload idLoc,
   .invokestatic "MacroCellLeanKt" "f_Algorithm_macrocellCellChild-xsr7cmg"
     ("(Ljava/lang/Object;Ljava/lang/Object;ILcom/alexvanyo/composelife/model/MacroCell;I)" ++
      "Lcom/alexvanyo/composelife/model/MacroCell;"),
   .astore dstLoc, .aload dstLoc, .ifnonnull (pc + 36),
   .newClass "com/alexvanyo/composelife/model/MacrocellStatus$UnexpectedNodeId", .dup,
   .aload 16, .checkcast "java/lang/String", .iload 2, .iload startLoc, .iload endLoc, .aconstNull,
   .invokespecial "com/alexvanyo/composelife/model/MacrocellStatus$UnexpectedNodeId" "<init>"
     "(Ljava/lang/String;IIILkotlin/jvm/internal/DefaultConstructorMarker;)V",
   .astore errLoc1] ++ errTailInstrs errLoc1 errLoc2 errTmp

private def leafChildInstrs (pc idLoc startLoc endLoc dstLoc errLoc1 errLoc2 errTmp : Nat) :
    List JvmInstr :=
  [.aload 13, .aload 14, .iload idLoc,
   .invokestatic "MacroCellLeanKt" "f_Algorithm_macrocellLeafChild-jXDDuk8"
     "(Ljava/lang/Object;Ljava/lang/Object;I)Lkotlin/ULong;",
   .astore dstLoc, .aload dstLoc, .ifnonnull (pc + 34),
   .newClass "com/alexvanyo/composelife/model/MacrocellStatus$UnexpectedNodeId", .dup,
   .aload 16, .checkcast "java/lang/String", .iload 2, .iload startLoc, .iload endLoc, .aconstNull,
   .invokespecial "com/alexvanyo/composelife/model/MacrocellStatus$UnexpectedNodeId" "<init>"
     "(Ljava/lang/String;IIILkotlin/jvm/internal/DefaultConstructorMarker;)V",
   .astore errLoc1] ++ errTailInstrs errLoc1 errLoc2 errTmp

private def unboxULongInstrs (pc srcLoc : Nat) : List JvmInstr :=
  [.aload srcLoc, .astore 42, .iconst 0, .istore 43,
   .aload 42, .instanceof "java/lang/Long", .ifeq (pc + 12),
   .aload 42, .checkcast "java/lang/Number",
   .invokevirtual "java/lang/Number" "longValue" "()J",
   .invokestatic "kotlin/ULong" "constructor-impl" "(J)J", .goto (pc + 14),
   .aload 42, .invokevirtual "kotlin/ULong" "unbox-impl" "()J"]

local macro "chunk " n:num : tactic => `(tactic| (
  rw [runJvmResFast_stepResHeapChunk $n]
  (conv in (afterResBlockChunk _ _) => arg 1; jvm_whnf_blk)
  rw [afterResBlockChunk_cont]
  (conv in (runJvmResFast _ _ _ _ _) =>
    norm_jvm_locals
    norm_flat_run
    jvm_whnf_run_args
    arg 1
    simp only [Nat.succ_eq_add_one, nat_add_eq_add, Nat.add_zero, Nat.add_assoc, Nat.reduceAdd])))

section
set_option maxRecDepth 8192

private theorem deserLoop_drop_0 :
    f_Algorithm_deserializeMacrocell_loop_prog.drop 0 =
      .aload 0 :: .ldcStr "lines" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .aload 4 :: .ldcStr "bytes" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      f_Algorithm_deserializeMacrocell_loop_prog.drop 6 := rfl

private theorem deserLoop_drop_6 :
    f_Algorithm_deserializeMacrocell_loop_prog.drop 6 =
      .iload 2 :: .iload 1 ::
      .invokestatic "java/lang/Integer" "compareUnsigned" "(II)I" ::
      .iflt 85 :: f_Algorithm_deserializeMacrocell_loop_prog.drop 10 := rfl

private theorem deserLoop_drop_10 :
    f_Algorithm_deserializeMacrocell_loop_prog.drop 10 =
      .aload 12 :: .ldcStr "null cannot be cast to non-null type kotlin.Array<*>" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .aload 12 :: .checkcast "[Ljava/lang/Object;" ::
      f_Algorithm_deserializeMacrocell_loop_prog.drop 15 := rfl

private theorem deserLoop_drop_15 :
    f_Algorithm_deserializeMacrocell_loop_prog.drop 15 =
      .iconst 1 :: .aaload :: .dup ::
      .ldcStr "null cannot be cast to non-null type kotlin.Array<kotlin.Any?>" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .checkcast "[Ljava/lang/Object;" :: .astore 16 ::
      .aload 12 :: .checkcast "[Ljava/lang/Object;" :: .iconst 2 :: .aaload ::
      .astore 18 :: .iconst 0 :: .istore 19 ::
      .aload 18 :: .instanceof "java/lang/Integer" :: .ifeq 37 ::
      .aload 18 :: .checkcast "java/lang/Number" ::
      .invokevirtual "java/lang/Number" "intValue" "()I" ::
      .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" :: .goto 43 ::
      f_Algorithm_deserializeMacrocell_loop_prog.drop 37 := rfl

private theorem deserLoop_drop_43 :
    f_Algorithm_deserializeMacrocell_loop_prog.drop 43 =
      .istore 17 :: .iload 17 :: .ifeq 66 ::
      .getstatic "com/alexvanyo/composelife/model/MacrocellStatus$Ok" "INSTANCE"
        "Lcom/alexvanyo/composelife/model/MacrocellStatus$Ok;" ::
      .astore 18 :: .aload 15 ::
      .invokestatic "MacroCellLeanKt" "f_Algorithm_GrowBuf_toArray___redArg"
        "(Ljava/lang/Object;)[Ljava/lang/Object;" ::
      .astore 19 :: .aload 16 :: .iload 17 :: .iconst 1 :: .isub ::
      .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" ::
      .invokestatic "MacroCellLeanKt" "f_Algorithm_macroCellAt-Qn1smSk"
        "([Ljava/lang/Object;I)Lcom/alexvanyo/composelife/model/MacroCell;" ::
      .astore 20 ::
      .newClass "com/alexvanyo/composelife/model/MacrocellResult" :: .dup ::
      .aload 18 :: .checkcast "com/alexvanyo/composelife/model/MacrocellStatus" ::
      .aload 19 :: .aload 20 ::
      .invokespecial "com/alexvanyo/composelife/model/MacrocellResult" "<init>"
        ("(Lcom/alexvanyo/composelife/model/MacrocellStatus;" ++
         "[Ljava/lang/Object;Lcom/alexvanyo/composelife/model/MacroCell;)V") ::
      .areturn :: f_Algorithm_deserializeMacrocell_loop_prog.drop 66 := rfl

private theorem deserLoop_drop_66 :
    f_Algorithm_deserializeMacrocell_loop_prog.drop 66 =
      .getstatic "com/alexvanyo/composelife/model/MacrocellStatus$Ok" "INSTANCE"
        "Lcom/alexvanyo/composelife/model/MacrocellStatus$Ok;" ::
      .astore 18 :: .aload 15 ::
      .invokestatic "MacroCellLeanKt" "f_Algorithm_GrowBuf_toArray___redArg"
        "(Ljava/lang/Object;)[Ljava/lang/Object;" ::
      .astore 19 ::
      .newClass "com/alexvanyo/composelife/model/MacrocellResult" :: .dup ::
      .aload 18 :: .checkcast "com/alexvanyo/composelife/model/MacrocellStatus" ::
      .aload 19 :: .iconst 0 :: .istore 21 ::
      .invokestatic "MacroCellLeanKt" "getEMPTY_LEVEL_4"
        "()Lcom/alexvanyo/composelife/model/MacroCell$Level4Node;" ::
      .checkcast "com/alexvanyo/composelife/model/MacroCell" :: .dup ::
      .ldcStr "null cannot be cast to non-null type com.alexvanyo.composelife.model.MacroCell" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .invokespecial "com/alexvanyo/composelife/model/MacrocellResult" "<init>"
        ("(Lcom/alexvanyo/composelife/model/MacrocellStatus;" ++
         "[Ljava/lang/Object;Lcom/alexvanyo/composelife/model/MacroCell;)V") ::
      .areturn :: f_Algorithm_deserializeMacrocell_loop_prog.drop 85 := rfl

private theorem deserLoop_drop_85 :
    f_Algorithm_deserializeMacrocell_loop_prog.drop 85 =
      .iload 3 :: .ifne 1127 :: .aload 0 :: .iload 2 :: .aaload :: .astore 16 ::
      .aload 16 :: .ldcStr "null cannot be cast to non-null type kotlin.String" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .aload 16 :: .checkcast "java/lang/String" ::
      .invokestatic "kotlin/text/StringsKt" "encodeToByteArray" "(Ljava/lang/String;)[B" ::
      .astore 17 :: .aload 17 :: .arraylength ::
      .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" :: .istore 18 ::
      .iload 18 :: .ifeq 992 :: f_Algorithm_deserializeMacrocell_loop_prog.drop 104 := rfl

private theorem deserLoop_drop_104 :
    f_Algorithm_deserializeMacrocell_loop_prog.drop 104 =
      .aload 17 :: .iconst 0 :: .baload ::
      .invokestatic "kotlin/UByte" "constructor-impl" "(B)B" :: .istore 19 ::
      .iload 19 :: .iconst 35 :: .if_icmpeq 944 ::
      .iconst 48 :: .iconst 255 :: .iand :: .iload 19 :: .iconst 255 :: .iand ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "compare" "(II)I" :: .ifgt 1057 ::
      .iload 19 :: .iconst 255 :: .iand :: .iconst 57 :: .iconst 255 :: .iand ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "compare" "(II)I" :: .ifgt 1057 ::
      f_Algorithm_deserializeMacrocell_loop_prog.drop 128 := rfl

private theorem deserLoop_drop_128 :
    f_Algorithm_deserializeMacrocell_loop_prog.drop 128 =
      .aload 17 ::
      .invokestatic "MacroCellLeanKt" "f_Algorithm_parseMCNodeLine" "([B)Ljava/lang/Object;" ::
      .astore 20 :: .aload 20 ::
      .ldcStr "null cannot be cast to non-null type kotlin.Array<*>" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .aload 20 :: .checkcast "[Ljava/lang/Object;" :: .iconst 0 :: .aaload :: .dup ::
      .ldcStr "null cannot be cast to non-null type kotlin.Int" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .checkcast "java/lang/Integer" ::
      .invokevirtual "java/lang/Integer" "intValue" "()I" ::
      .tableswitch 0 [144, 169] 938 ::
      f_Algorithm_deserializeMacrocell_loop_prog.drop 144 := rfl

private theorem deserLoop_drop_144 :
    f_Algorithm_deserializeMacrocell_loop_prog.drop 144 =
      .newClass "com/alexvanyo/composelife/model/MacrocellStatus$UnexpectedInput" :: .dup ::
      .aload 16 :: .checkcast "java/lang/String" :: .iload 2 :: .aconstNull ::
      .invokespecial "com/alexvanyo/composelife/model/MacrocellStatus$UnexpectedInput" "<init>"
        "(Ljava/lang/String;ILkotlin/jvm/internal/DefaultConstructorMarker;)V" ::
      .astore 22 :: .aload 15 ::
      .invokestatic "MacroCellLeanKt" "f_Algorithm_GrowBuf_toArray___redArg"
        "(Ljava/lang/Object;)[Ljava/lang/Object;" ::
      .astore 23 ::
      .newClass "com/alexvanyo/composelife/model/MacrocellResult" :: .dup ::
      .aload 22 :: .checkcast "com/alexvanyo/composelife/model/MacrocellStatus" ::
      .aload 23 :: .iconst 0 :: .istore 25 ::
      .invokestatic "MacroCellLeanKt" "getEMPTY_LEVEL_4"
        "()Lcom/alexvanyo/composelife/model/MacroCell$Level4Node;" ::
      .checkcast "com/alexvanyo/composelife/model/MacroCell" :: .dup ::
      .ldcStr "null cannot be cast to non-null type com.alexvanyo.composelife.model.MacroCell" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .invokespecial "com/alexvanyo/composelife/model/MacrocellResult" "<init>"
        ("(Lcom/alexvanyo/composelife/model/MacrocellStatus;" ++
         "[Ljava/lang/Object;Lcom/alexvanyo/composelife/model/MacroCell;)V") ::
      .areturn :: f_Algorithm_deserializeMacrocell_loop_prog.drop 169 := rfl

private theorem deserLoop_drop_169 :
    f_Algorithm_deserializeMacrocell_loop_prog.drop 169 =
      .aload 20 :: .checkcast "[Ljava/lang/Object;" :: .iconst 1 :: .aaload ::
      .astore 22 :: .aload 22 ::
      .ldcStr "null cannot be cast to non-null type kotlin.Array<*>" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      f_Algorithm_deserializeMacrocell_loop_prog.drop 177 := rfl

private theorem deserLoop_drop_177 :
    f_Algorithm_deserializeMacrocell_loop_prog.drop 177 =
      unboxUIntInstrs 177 1 23 24 25 ++ unboxUIntInstrs 199 5 24 25 26 ++
      unboxUIntInstrs 221 9 25 26 27 ++ unboxUIntInstrs 243 13 26 27 28 ++
      unboxUIntInstrs 265 17 27 28 29 ++ unboxUIntInstrs 287 21 28 29 30 ++
      unboxUIntInstrs 309 25 29 30 31 ++ unboxUIntInstrs 331 29 30 31 32 ++
      unboxUIntInstrs 353 33 31 32 33 ++ unboxUIntInstrs 375 37 32 33 34 ++
      unboxUIntInstrs 397 41 33 34 35 ++ unboxUIntInstrs 419 45 34 35 36 ++
      unboxUIntInstrs 441 49 35 36 37 ++
      f_Algorithm_deserializeMacrocell_loop_prog.drop 463 := rfl

private theorem deserLoop_drop_463 :
    f_Algorithm_deserializeMacrocell_loop_prog.drop 463 =
      .iload 23 :: .iconst 4 ::
      .invokestatic "java/lang/Integer" "compareUnsigned" "(II)I" :: .iflt 937 ::
      .iconst 63 :: .iload 23 ::
      .invokestatic "java/lang/Integer" "compareUnsigned" "(II)I" :: .iflt 936 ::
      .iload 23 :: .iconst 4 :: .if_icmpeq 686 ::
      .iload 23 :: .iconst 1 :: .isub ::
      .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" ::
      .invokestatic "MacroCellLeanKt" "f_Algorithm_emptyMacroCellUInt32-WZ4Q5Ns"
        "(I)Lcom/alexvanyo/composelife/model/MacroCell;" ::
      .astore 36 :: f_Algorithm_deserializeMacrocell_loop_prog.drop 480 := rfl

private theorem deserLoop_drop_480 :
    f_Algorithm_deserializeMacrocell_loop_prog.drop 480 =
      cellChildInstrs 480 24 25 26 37 38 39 41 ++
      cellChildInstrs 516 27 28 29 38 39 40 42 ++
      cellChildInstrs 552 30 31 32 39 40 41 43 ++
      cellChildInstrs 588 33 34 35 40 41 42 44 ++
      f_Algorithm_deserializeMacrocell_loop_prog.drop 624 := rfl

private theorem deserLoop_drop_624 :
    f_Algorithm_deserializeMacrocell_loop_prog.drop 624 =
      .iload 2 :: .iconst 1 :: .iadd ::
      .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" :: .istore 41 ::
      .aload 37 :: .aload 38 :: .aload 39 :: .aload 40 ::
      .invokestatic "MacroCellLeanKt" "f_Algorithm_makeCellNode"
        ("(Lcom/alexvanyo/composelife/model/MacroCell;Lcom/alexvanyo/composelife/model/MacroCell;" ++
         "Lcom/alexvanyo/composelife/model/MacroCell;Lcom/alexvanyo/composelife/model/MacroCell;)" ++
         "Lcom/alexvanyo/composelife/model/MacroCell;") ::
      .astore 42 :: .aload 12 :: .aload 42 ::
      .invokestatic "MacroCellLeanKt" "f_Algorithm_GrowBuf_push___redArg"
        "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" :: .astore 43 ::
      .aload 13 :: .lconst 0 ::
      .invokestatic "kotlin/ULong" "box-impl" "(J)Lkotlin/ULong;" ::
      .invokestatic "MacroCellLeanKt" "f_Algorithm_GrowBuf_push___redArg"
        "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" :: .astore 44 ::
      .aload 14 :: .iconst 0 ::
      .invokestatic "java/lang/Boolean" "valueOf" "(Z)Ljava/lang/Boolean;" ::
      .invokestatic "MacroCellLeanKt" "f_Algorithm_GrowBuf_push___redArg"
        "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" :: .astore 45 ::
      .aload 0 :: .astore 46 :: .iload 1 :: .istore 47 :: .aload 15 :: .astore 48 ::
      .aload 46 :: .astore 0 :: .iload 47 :: .istore 1 :: .iload 41 :: .istore 2 ::
      .iconst 0 :: .istore 3 :: .aload 17 :: .astore 4 :: .iload 18 :: .istore 5 ::
      .iconst 0 :: .istore 6 :: .iconst 0 :: .istore 7 ::
      .iconst 0 :: .istore 8 :: .iconst 0 :: .istore 9 ::
      .lconst 0 :: .lstore 10 :: .aload 43 :: .astore 12 :: .aload 44 :: .astore 13 ::
      .aload 45 :: .astore 14 :: .aload 48 :: .astore 15 :: .goto 6 ::
      f_Algorithm_deserializeMacrocell_loop_prog.drop 686 := rfl

private theorem deserLoop_drop_686 :
    f_Algorithm_deserializeMacrocell_loop_prog.drop 686 =
      leafChildInstrs 686 24 25 26 36 37 38 40 ++
      leafChildInstrs 720 27 28 29 37 38 39 41 ++
      leafChildInstrs 754 30 31 32 38 39 40 42 ++
      leafChildInstrs 788 33 34 35 39 40 41 43 ++
      f_Algorithm_deserializeMacrocell_loop_prog.drop 822 := rfl

private theorem deserLoop_drop_822 :
    f_Algorithm_deserializeMacrocell_loop_prog.drop 822 =
      .iload 2 :: .iconst 1 :: .iadd ::
      .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" :: .istore 40 ::
      unboxULongInstrs 827 36 ++ unboxULongInstrs 841 37 ++
      unboxULongInstrs 855 38 ++ unboxULongInstrs 869 39 ++
      f_Algorithm_deserializeMacrocell_loop_prog.drop 883 := rfl

private theorem deserLoop_drop_883 :
    f_Algorithm_deserializeMacrocell_loop_prog.drop 883 =
      .invokestatic "MacroCellLeanKt" "f_Algorithm_makeLevel4Node-2jIhpxI"
        "(JJJJ)Lcom/alexvanyo/composelife/model/MacroCell;" ::
      .astore 41 :: .aload 12 :: .aload 41 ::
      .invokestatic "MacroCellLeanKt" "f_Algorithm_GrowBuf_push___redArg"
        "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" :: .astore 42 ::
      .aload 13 :: .lconst 0 ::
      .invokestatic "kotlin/ULong" "box-impl" "(J)Lkotlin/ULong;" ::
      .invokestatic "MacroCellLeanKt" "f_Algorithm_GrowBuf_push___redArg"
        "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" :: .astore 43 ::
      .aload 14 :: .iconst 0 ::
      .invokestatic "java/lang/Boolean" "valueOf" "(Z)Ljava/lang/Boolean;" ::
      .invokestatic "MacroCellLeanKt" "f_Algorithm_GrowBuf_push___redArg"
        "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" :: .astore 44 ::
      .aload 0 :: .astore 45 :: .iload 1 :: .istore 46 :: .aload 15 :: .astore 47 ::
      .aload 45 :: .astore 0 :: .iload 46 :: .istore 1 :: .iload 40 :: .istore 2 ::
      .iconst 0 :: .istore 3 :: .aload 17 :: .astore 4 :: .iload 18 :: .istore 5 ::
      .iconst 0 :: .istore 6 :: .iconst 0 :: .istore 7 ::
      .iconst 0 :: .istore 8 :: .iconst 0 :: .istore 9 ::
      .lconst 0 :: .lstore 10 :: .aload 42 :: .astore 12 :: .aload 43 :: .astore 13 ::
      .aload 44 :: .astore 14 :: .aload 47 :: .astore 15 :: .goto 6 ::
      f_Algorithm_deserializeMacrocell_loop_prog.drop 936 := rfl

private theorem deserLoop_drop_936 :
    f_Algorithm_deserializeMacrocell_loop_prog.drop 936 =
      .goto 1102 :: .goto 1102 :: f_Algorithm_deserializeMacrocell_loop_prog.drop 938 := rfl

private theorem deserLoop_drop_937 :
    f_Algorithm_deserializeMacrocell_loop_prog.drop 937 =
      .goto 1102 :: f_Algorithm_deserializeMacrocell_loop_prog.drop 938 := rfl

private theorem deserLoop_drop_1102 :
    f_Algorithm_deserializeMacrocell_loop_prog.drop 1102 =
      .newClass "com/alexvanyo/composelife/model/MacrocellStatus$UnexpectedInput" :: .dup ::
      .aload 16 :: .checkcast "java/lang/String" :: .iload 2 :: .aconstNull ::
      .invokespecial "com/alexvanyo/composelife/model/MacrocellStatus$UnexpectedInput" "<init>"
        "(Ljava/lang/String;ILkotlin/jvm/internal/DefaultConstructorMarker;)V" ::
      .astore 17 :: errTailInstrs 17 18 20 ++
      f_Algorithm_deserializeMacrocell_loop_prog.drop 1127 := rfl

private theorem deserLoop_drop_944 :
    f_Algorithm_deserializeMacrocell_loop_prog.drop 944 =
      .aload 0 :: .astore 20 :: .iload 1 :: .istore 21 ::
      .iload 2 :: .iconst 1 :: .iadd ::
      .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" :: .istore 22 ::
      .aload 12 :: .astore 23 :: .aload 13 :: .astore 24 ::
      .aload 14 :: .astore 25 :: .aload 15 :: .astore 26 ::
      .aload 20 :: .astore 0 :: .iload 21 :: .istore 1 :: .iload 22 :: .istore 2 ::
      .iconst 0 :: .istore 3 :: .aload 17 :: .astore 4 :: .iload 18 :: .istore 5 ::
      .iconst 0 :: .istore 6 :: .iconst 0 :: .istore 7 ::
      .iconst 0 :: .istore 8 :: .iconst 0 :: .istore 9 ::
      .lconst 0 :: .lstore 10 :: .aload 23 :: .astore 12 :: .aload 24 :: .astore 13 ::
      .aload 25 :: .astore 14 :: .aload 26 :: .astore 15 :: .goto 6 ::
      f_Algorithm_deserializeMacrocell_loop_prog.drop 992 := rfl

private theorem deserLoop_drop_992 :
    f_Algorithm_deserializeMacrocell_loop_prog.drop 992 =
      .iload 2 :: .iconst 1 :: .iadd ::
      .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" :: .istore 19 ::
      .aconstNull :: .astore 20 :: .iload 19 :: .iload 1 ::
      .invokestatic "java/lang/Integer" "compareUnsigned" "(II)I" :: .iflt 1006 ::
      .aload 15 :: .astore 20 :: .goto 1016 ::
      f_Algorithm_deserializeMacrocell_loop_prog.drop 1006 := rfl

private theorem deserLoop_drop_1006 :
    f_Algorithm_deserializeMacrocell_loop_prog.drop 1006 =
      .aload 15 :: .newClass "com/alexvanyo/composelife/model/MacrocellWarning$BlankLine" ::
      .dup :: .iload 19 :: .aconstNull ::
      .invokespecial "com/alexvanyo/composelife/model/MacrocellWarning$BlankLine" "<init>"
        "(ILkotlin/jvm/internal/DefaultConstructorMarker;)V" ::
      .invokestatic "MacroCellLeanKt" "f_Algorithm_GrowBuf_push___redArg"
        "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" ::
      .astore 21 :: .aload 21 :: .astore 20 ::
      f_Algorithm_deserializeMacrocell_loop_prog.drop 1016 := rfl

private theorem deserLoop_drop_1016 :
    f_Algorithm_deserializeMacrocell_loop_prog.drop 1016 =
      .aload 0 :: .astore 21 :: .iload 1 :: .istore 22 ::
      .aload 12 :: .astore 23 :: .aload 13 :: .astore 24 :: .aload 14 :: .astore 25 ::
      .aload 21 :: .astore 0 :: .iload 22 :: .istore 1 :: .iload 19 :: .istore 2 ::
      .iconst 0 :: .istore 3 :: .aload 17 :: .astore 4 :: .iload 18 :: .istore 5 ::
      .iconst 0 :: .istore 6 :: .iconst 0 :: .istore 7 ::
      .iconst 0 :: .istore 8 :: .iconst 0 :: .istore 9 ::
      .lconst 0 :: .lstore 10 :: .aload 23 :: .astore 12 :: .aload 24 :: .astore 13 ::
      .aload 25 :: .astore 14 :: .aload 20 :: .astore 15 :: .goto 6 ::
      f_Algorithm_deserializeMacrocell_loop_prog.drop 1057 := rfl

private theorem deserLoop_drop_1057 :
    f_Algorithm_deserializeMacrocell_loop_prog.drop 1057 =
      .aload 0 :: .astore 19 :: .iload 1 :: .istore 20 :: .iload 2 :: .istore 21 ::
      .aload 12 :: .astore 22 :: .aload 13 :: .astore 23 ::
      .aload 14 :: .astore 24 :: .aload 15 :: .astore 25 ::
      .aload 19 :: .astore 0 :: .iload 20 :: .istore 1 :: .iload 21 :: .istore 2 ::
      .iconst 1 :: .istore 3 :: .aload 17 :: .astore 4 :: .iload 18 :: .istore 5 ::
      .iconst 0 :: .istore 6 :: .iconst 0 :: .istore 7 ::
      .iconst 0 :: .istore 8 :: .iconst 0 :: .istore 9 ::
      .lconst 0 :: .lstore 10 :: .aload 22 :: .astore 12 :: .aload 23 :: .astore 13 ::
      .aload 24 :: .astore 14 :: .aload 25 :: .astore 15 :: .goto 6 ::
      f_Algorithm_deserializeMacrocell_loop_prog.drop 1102 := rfl

private theorem deserLoop_drop_1127 :
    f_Algorithm_deserializeMacrocell_loop_prog.drop 1127 =
      .iload 6 :: .iload 5 ::
      .invokestatic "java/lang/Integer" "compareUnsigned" "(II)I" ::
      .iflt 1197 :: f_Algorithm_deserializeMacrocell_loop_prog.drop 1131 := rfl

private theorem deserLoop_drop_1131 :
    f_Algorithm_deserializeMacrocell_loop_prog.drop 1131 =
      .iload 2 :: .iconst 1 :: .iadd ::
      .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" :: .istore 16 ::
      .lload 10 :: .lconst 0 :: .lconst 0 :: .lconst 0 ::
      .invokestatic "MacroCellLeanKt" "f_Algorithm_makeLevel4Node-2jIhpxI"
        "(JJJJ)Lcom/alexvanyo/composelife/model/MacroCell;" :: .astore 17 ::
      .aload 12 :: .aload 17 ::
      .invokestatic "MacroCellLeanKt" "f_Algorithm_GrowBuf_push___redArg"
        "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" :: .astore 18 ::
      .aload 13 :: .lload 10 ::
      .invokestatic "kotlin/ULong" "box-impl" "(J)Lkotlin/ULong;" ::
      .invokestatic "MacroCellLeanKt" "f_Algorithm_GrowBuf_push___redArg"
        "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" :: .astore 19 ::
      .aload 14 :: .iconst 1 ::
      .invokestatic "java/lang/Boolean" "valueOf" "(Z)Ljava/lang/Boolean;" ::
      .invokestatic "MacroCellLeanKt" "f_Algorithm_GrowBuf_push___redArg"
        "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" :: .astore 20 ::
      .aload 0 :: .astore 21 :: .iload 1 :: .istore 22 :: .aload 4 :: .astore 23 ::
      .iload 5 :: .istore 24 :: .aload 15 :: .astore 25 ::
      .aload 21 :: .astore 0 :: .iload 22 :: .istore 1 :: .iload 16 :: .istore 2 ::
      .iconst 0 :: .istore 3 :: .aload 23 :: .astore 4 :: .iload 24 :: .istore 5 ::
      .iconst 0 :: .istore 6 :: .iconst 0 :: .istore 7 ::
      .iconst 0 :: .istore 8 :: .iconst 0 :: .istore 9 ::
      .lconst 0 :: .lstore 10 :: .aload 18 :: .astore 12 :: .aload 19 :: .astore 13 ::
      .aload 20 :: .astore 14 :: .aload 25 :: .astore 15 :: .goto 6 ::
      f_Algorithm_deserializeMacrocell_loop_prog.drop 1197 := rfl

private theorem deserLoop_drop_1197 :
    f_Algorithm_deserializeMacrocell_loop_prog.drop 1197 =
      .aload 4 :: .iload 6 :: .iload 5 ::
      .invokestatic "MacroCellLeanKt" "f_Algorithm_decodeCharAt-BltQuoY" "([BII)Lkotlin/Pair;" ::
      .astore 16 :: .aload 16 ::
      .invokevirtual "kotlin/Pair" "getFirst" "()Ljava/lang/Object;" ::
      .checkcast "kotlin/UInt" ::
      .invokevirtual "kotlin/UInt" "unbox-impl" "()I" :: .istore 17 ::
      .aload 16 :: .invokevirtual "kotlin/Pair" "getSecond" "()Ljava/lang/Object;" ::
      .checkcast "kotlin/UInt" ::
      .invokevirtual "kotlin/UInt" "unbox-impl" "()I" :: .istore 18 ::
      .lconst 0 :: .lstore 19 :: .aconstNull :: .astore 21 ::
      .iload 17 :: .iconst 36 :: .if_icmpeq 1288 ::
      .lconst 0 :: .lstore 22 :: .iload 17 :: .iconst 42 :: .if_icmpeq 1227 ::
      .lload 10 :: .lstore 22 :: .goto 1249 ::
      f_Algorithm_deserializeMacrocell_loop_prog.drop 1227 := rfl

private theorem deserLoop_drop_1219 :
    f_Algorithm_deserializeMacrocell_loop_prog.drop 1219 =
      .lconst 0 :: .lstore 22 :: .iload 17 :: .iconst 42 :: .if_icmpeq 1227 ::
      .lload 10 :: .lstore 22 :: .goto 1249 ::
      f_Algorithm_deserializeMacrocell_loop_prog.drop 1227 := rfl

private theorem deserLoop_drop_1227 :
    f_Algorithm_deserializeMacrocell_loop_prog.drop 1227 =
      .iload 8 :: .iconst 8 ::
      .invokestatic "java/lang/Integer" "compareUnsigned" "(II)I" :: .iflt 1234 ::
      .lload 10 :: .lstore 22 :: .goto 1249 ::
      .iload 9 :: .iconst 8 ::
      .invokestatic "java/lang/Integer" "compareUnsigned" "(II)I" :: .iflt 1241 ::
      .lload 10 :: .lstore 22 :: .goto 1249 ::
      .lload 10 :: .iload 8 :: .iload 9 :: .iconst 1 ::
      .invokestatic "MacroCellLeanKt" "f_Algorithm_leafWithCell-9LuH6mI" "(JIIZ)J" ::
      .lstore 24 :: .lload 24 :: .lstore 22 ::
      f_Algorithm_deserializeMacrocell_loop_prog.drop 1249 := rfl

private theorem deserLoop_drop_1234 :
    f_Algorithm_deserializeMacrocell_loop_prog.drop 1234 =
      .iload 9 :: .iconst 8 ::
      .invokestatic "java/lang/Integer" "compareUnsigned" "(II)I" :: .iflt 1241 ::
      .lload 10 :: .lstore 22 :: .goto 1249 ::
      f_Algorithm_deserializeMacrocell_loop_prog.drop 1241 := rfl

private theorem deserLoop_drop_1241 :
    f_Algorithm_deserializeMacrocell_loop_prog.drop 1241 =
      .lload 10 :: .iload 8 :: .iload 9 :: .iconst 1 ::
      .invokestatic "MacroCellLeanKt" "f_Algorithm_leafWithCell-9LuH6mI" "(JIIZ)J" ::
      .lstore 24 :: .lload 24 :: .lstore 22 ::
      f_Algorithm_deserializeMacrocell_loop_prog.drop 1249 := rfl

private theorem deserLoop_drop_1249 :
    f_Algorithm_deserializeMacrocell_loop_prog.drop 1249 =
      .iload 17 :: .iconst 46 :: .if_icmpeq 1283 ::
      .iload 17 :: .iconst 42 :: .if_icmpeq 1278 ::
      .aload 0 :: .iload 2 :: .aaload :: .astore 24 :: .aload 15 ::
      .newClass "com/alexvanyo/composelife/model/MacrocellWarning$UnexpectedInput" :: .dup ::
      .iload 2 :: .iload 7 :: .aload 24 ::
      .ldcStr "null cannot be cast to non-null type kotlin.String" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .aload 24 :: .checkcast "java/lang/String" :: .aconstNull ::
      .invokespecial "com/alexvanyo/composelife/model/MacrocellWarning$UnexpectedInput" "<init>"
        "(IILjava/lang/String;Lkotlin/jvm/internal/DefaultConstructorMarker;)V" ::
      .invokestatic "MacroCellLeanKt" "f_Algorithm_GrowBuf_push___redArg"
        "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" ::
      .astore 25 :: .lload 22 :: .lstore 19 :: .aload 25 :: .astore 21 :: .goto 1349 ::
      .lload 22 :: .lstore 19 :: .aload 15 :: .astore 21 :: .goto 1349 ::
      .lload 22 :: .lstore 19 :: .aload 15 :: .astore 21 :: .goto 1349 ::
      f_Algorithm_deserializeMacrocell_loop_prog.drop 1288 := rfl

private theorem deserLoop_drop_1278 :
    f_Algorithm_deserializeMacrocell_loop_prog.drop 1278 =
      .lload 22 :: .lstore 19 :: .aload 15 :: .astore 21 :: .goto 1349 ::
      .lload 22 :: .lstore 19 :: .aload 15 :: .astore 21 :: .goto 1349 ::
      f_Algorithm_deserializeMacrocell_loop_prog.drop 1288 := rfl

private theorem deserLoop_drop_1283 :
    f_Algorithm_deserializeMacrocell_loop_prog.drop 1283 =
      .lload 22 :: .lstore 19 :: .aload 15 :: .astore 21 :: .goto 1349 ::
      f_Algorithm_deserializeMacrocell_loop_prog.drop 1288 := rfl

private theorem deserLoop_drop_1288 :
    f_Algorithm_deserializeMacrocell_loop_prog.drop 1288 =
      .aload 0 :: .astore 22 :: .iload 1 :: .istore 23 :: .iload 2 :: .istore 24 ::
      .aload 4 :: .astore 25 :: .iload 5 :: .istore 26 ::
      .iload 7 :: .iconst 1 :: .iadd ::
      .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" :: .istore 27 ::
      .iload 9 :: .iconst 1 :: .iadd ::
      .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" :: .istore 28 ::
      .lload 10 :: .lstore 29 :: .aload 12 :: .astore 31 ::
      .aload 13 :: .astore 32 :: .aload 14 :: .astore 33 :: .aload 15 :: .astore 34 ::
      .aload 22 :: .astore 0 :: .iload 23 :: .istore 1 :: .iload 24 :: .istore 2 ::
      .iconst 1 :: .istore 3 :: .aload 25 :: .astore 4 :: .iload 26 :: .istore 5 ::
      .iload 18 :: .istore 6 :: .iload 27 :: .istore 7 ::
      .iconst 0 :: .istore 8 :: .iload 28 :: .istore 9 :: .lload 29 :: .lstore 10 ::
      .aload 31 :: .astore 12 :: .aload 32 :: .astore 13 ::
      .aload 33 :: .astore 14 :: .aload 34 :: .astore 15 :: .goto 6 ::
      f_Algorithm_deserializeMacrocell_loop_prog.drop 1349 := rfl

private theorem deserLoop_drop_1349 :
    f_Algorithm_deserializeMacrocell_loop_prog.drop 1349 =
      [.aload 0, .astore 22, .iload 1, .istore 23, .iload 2, .istore 24,
       .aload 4, .astore 25, .iload 5, .istore 26,
       .iload 7, .iconst 1, .iadd, .invokestatic "kotlin/UInt" "constructor-impl" "(I)I", .istore 27,
       .iload 8, .iconst 1, .iadd, .invokestatic "kotlin/UInt" "constructor-impl" "(I)I", .istore 28,
       .iload 9, .istore 29, .aload 12, .astore 30, .aload 13, .astore 31, .aload 14, .astore 32,
       .aload 22, .astore 0, .iload 23, .istore 1, .iload 24, .istore 2,
       .iconst 1, .istore 3, .aload 25, .astore 4, .iload 26, .istore 5,
       .iload 18, .istore 6, .iload 27, .istore 7, .iload 28, .istore 8,
       .iload 29, .istore 9, .lload 19, .lstore 10, .aload 30, .astore 12,
       .aload 31, .astore 13, .aload 32, .astore 14, .aload 21, .astore 15, .goto 6] := rfl

end

structure DeserLoopLocs (locs : Nat → JvmVal)
    (lines : Array String) (numLines i : UInt32) (inLeaf : Bool)
    (bytesAddr : Nat) (limit p col x y : UInt32) (leaf : UInt64)
    (nodes : Algorithm.GrowBuf Algorithm.MacroCell)
    (leaves : Algorithm.GrowBuf UInt64)
    (isLeaf : Algorithm.GrowBuf Bool)
    (warns : Algorithm.GrowBuf Algorithm.MacrocellWarning) : Prop where
  h0 : locs 0 = .strArr lines
  h1 : locs 1 = .i32 numLines
  h2 : locs 2 = .i32 i
  h3 : locs 3 = .i32 (if inLeaf then 1 else 0)
  h4 : locs 4 = .heapRef bytesAddr
  h5 : locs 5 = .i32 limit
  h6 : locs 6 = .i32 p
  h7 : locs 7 = .i32 col
  h8 : locs 8 = .i32 x
  h9 : locs 9 = .i32 y
  h10 : locs 10 = .i64 leaf
  h12 : mcNodes? (locs 12) = some nodes
  h13 : mcLeaves? (locs 13) = some leaves
  h14 : mcIsLeaf? (locs 14) = some isLeaf
  h15 : mcWarns? (locs 15) = some warns

private theorem deserLoop_locs_ext {locs : Nat → JvmVal}
    {lines : Array String} {numLines i : UInt32} {inLeaf : Bool}
    {bytesAddr : Nat} {limit p col x y : UInt32} {leaf : UInt64}
    {nodes : Algorithm.GrowBuf Algorithm.MacroCell}
    {leaves : Algorithm.GrowBuf UInt64}
    {isLeaf : Algorithm.GrowBuf Bool}
    {warns : Algorithm.GrowBuf Algorithm.MacrocellWarning} :
    DeserLoopLocs
      (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
        (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal locs
          0 (.strArr lines)) 1 (.i32 numLines)) 2 (.i32 i))
          3 (.i32 (if inLeaf then 1 else 0))) 4 (.heapRef bytesAddr)) 5 (.i32 limit))
          6 (.i32 p)) 7 (.i32 col)) 8 (.i32 x)) 9 (.i32 y)) 10 (.i64 leaf))
          12 (match nodes with | b => .ext (.mcGrowBuf b)))
          13 (.ext (.u64GrowBuf leaves)))
          14 (.ext (.boolGrowBuf isLeaf)))
          15 (.ext (.mcWarnGrowBuf warns)))
      lines numLines i inLeaf bytesAddr limit p col x y leaf nodes leaves isLeaf warns :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem encodeGrowBufArray_get?_ext {α : Type}
    (jh : Jvm.JvmHeap AlgExt)
    (enc : Jvm.JvmHeap AlgExt → α → JvmVal × Jvm.JvmHeap AlgExt)
    (b : Algorithm.GrowBuf α)
    (hmono : ∀ (h : Jvm.JvmHeap AlgExt) (x : α) (a : Nat) (o : Jvm.HeapObj AlgExt),
      h.get? a = some o → (enc h x).2.get? a = some o)
    (a : Nat) (o : Jvm.HeapObj AlgExt) (ha : jh.get? a = some o) :
    (encodeGrowBufArray jh enc b).2.get? a = some o := by
  dsimp only [encodeGrowBufArray]
  have hfold : ∀ (xs : List α) (acc : Array JvmVal) (h : Jvm.JvmHeap AlgExt),
      h.get? a = some o →
      (xs.foldl (fun (p : Array JvmVal × Jvm.JvmHeap AlgExt) x =>
        let r := enc p.2 x; (p.1.push r.1, r.2)) (acc, h)).2.get? a = some o := by
    intro xs
    induction xs with
    | nil => intro acc h hh; exact hh
    | cons x xs ih =>
      intro acc h hh
      exact ih _ _ (hmono h x a o hh)
  have hf : (b.toArray.foldl (fun (p : Array JvmVal × Jvm.JvmHeap AlgExt) x =>
      let r := enc p.2 x; (p.1.push r.1, r.2)) (#[], jh)).2.get? a = some o := by
    rw [← Array.foldl_toList]
    exact hfold b.toArray.toList #[] jh ha
  rcases Array.getElem?_eq_some_iff.mp hf with ⟨hlt, _⟩
  rw [jvmHeap_get?_alloc_lt _ _ hlt, hf]

private theorem encodeGrowBufArray_statics {α : Type}
    (jh : Jvm.JvmHeap AlgExt)
    (enc : Jvm.JvmHeap AlgExt → α → JvmVal × Jvm.JvmHeap AlgExt)
    (b : Algorithm.GrowBuf α)
    (hmono : ∀ (h : Jvm.JvmHeap AlgExt) (x : α), (enc h x).2.statics = h.statics) :
    (encodeGrowBufArray jh enc b).2.statics = jh.statics := by
  dsimp only [encodeGrowBufArray]
  have hfold : ∀ (xs : List α) (acc : Array JvmVal) (h : Jvm.JvmHeap AlgExt),
      (xs.foldl (fun (p : Array JvmVal × Jvm.JvmHeap AlgExt) x =>
        let r := enc p.2 x; (p.1.push r.1, r.2)) (acc, h)).2.statics = h.statics := by
    intro xs
    induction xs with
    | nil => intro acc h; rfl
    | cons x xs ih =>
      intro acc h
      rw [List.foldl_cons, ih _ _, hmono h x]
  have hf : (b.toArray.foldl (fun (p : Array JvmVal × Jvm.JvmHeap AlgExt) x =>
      let r := enc p.2 x; (p.1.push r.1, r.2)) (#[], jh)).2.statics = jh.statics := by
    rw [← Array.foldl_toList]
    exact hfold b.toArray.toList #[] jh
  exact hf

private theorem encodeMCWarn_get?_ext (h : Jvm.JvmHeap AlgExt) (w : Algorithm.MacrocellWarning)
    (a : Nat) (o : Jvm.HeapObj AlgExt) (ha : h.get? a = some o) :
    (encodeMacrocellWarning h w).2.get? a = some o := by
  cases w with
  | emptyFile => exact ha
  | blankLine ln =>
    rcases Array.getElem?_eq_some_iff.mp ha with ⟨hlt, _⟩
    dsimp only [encodeMacrocellWarning]
    rw [jvmHeap_get?_alloc_lt _ _ hlt, ha]
  | unexpectedInput ln col inp =>
    rcases Array.getElem?_eq_some_iff.mp ha with ⟨hlt, _⟩
    dsimp only [encodeMacrocellWarning]
    rw [jvmHeap_get?_alloc_lt _ _ hlt, ha]

private theorem encodeMCWarn_statics (h : Jvm.JvmHeap AlgExt) (w : Algorithm.MacrocellWarning) :
    (encodeMacrocellWarning h w).2.statics = h.statics := by
  cases w <;> rfl

private def AllFuelNoneAt (prog : List JvmInstr) (pc : Nat) (instrs : List JvmInstr)
    (st : JvmState) : Prop :=
  st.pc = pc → prog.drop pc = instrs → ∀ f, runJvmRes f prog st = none

private theorem allFuelNoneAt_step {prog rest : List JvmInstr} {pc : Nat} {instr : JvmInstr}
    {stk stk' : List JvmVal} {locs locs' : Nat → JvmVal}
    {jh jh' : Jvm.JvmHeap AlgExt} {hp hp' : AlgHeap}
    (hnbr : isBranchInstr instr = false)
    (hstep : stepInstr instr ⟨pc, stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, stk', locs', jh', hp'⟩))
    (hnext : AllFuelNoneAt prog (pc + 1) rest ⟨pc + 1, stk', locs', jh', hp'⟩) :
    AllFuelNoneAt prog pc (instr :: rest) ⟨pc, stk, locs, jh, hp⟩ := by
  intro _ hdrop f
  cases f with
  | zero => rfl
  | succ f =>
    have hg : prog[pc]? = some instr := by
      have : (prog.drop pc)[0]? = prog[pc]? := by simp [List.getElem?_drop]
      rw [← this, hdrop]; rfl
    have hdrop1 : prog.drop (pc + 1) = rest := by
      have h1 : (prog.drop pc).drop 1 = prog.drop (pc + 1) := by
        rw [List.drop_drop, Nat.add_comm]
      rw [← h1, hdrop]; rfl
    rw [runJvmRes_nonbranch f prog ⟨pc, stk, locs, jh, hp⟩ instr hg hnbr, hstep]
    exact hnext rfl hdrop1 f

private theorem allFuelNoneAt_iflt_fallthrough {prog rest : List JvmInstr} {pc tgt : Nat}
    {v : UInt32} {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hv : v.toBitVec.slt 0#32 = false)
    (hnext : AllFuelNoneAt prog (pc + 1) rest ⟨pc + 1, stkRest, locs, jh, hp⟩) :
    AllFuelNoneAt prog pc (.iflt tgt :: rest) ⟨pc, .i32 v :: stkRest, locs, jh, hp⟩ := by
  intro _ hdrop f
  cases f with
  | zero => rfl
  | succ f =>
    have hg : prog[pc]? = some (.iflt tgt) := by
      have : (prog.drop pc)[0]? = prog[pc]? := by simp [List.getElem?_drop]
      rw [← this, hdrop]; rfl
    have hdrop1 : prog.drop (pc + 1) = rest := by
      have h1 : (prog.drop pc).drop 1 = prog.drop (pc + 1) := by
        rw [List.drop_drop, Nat.add_comm]
      rw [← h1, hdrop]; rfl
    dsimp only [runJvmRes]
    rw [Jvm.runJvmRes.eq_def]
    simp [hg, Jvm.JvmVal.asI32?, hv]
    exact hnext rfl hdrop1 f

private theorem allFuelNoneAt_checkcast_ext_objArr {prog rest : List JvmInstr} {pc : Nat}
    {e : AlgExt} {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    AllFuelNoneAt prog pc (.checkcast "[Ljava/lang/Object;" :: rest)
      ⟨pc, .ext e :: stkRest, locs, jh, hp⟩ := by
  intro _ hdrop f
  cases f with
  | zero => rfl
  | succ f =>
    have hg : prog[pc]? = some (.checkcast "[Ljava/lang/Object;") := by
      have : (prog.drop pc)[0]? = prog[pc]? := by simp [List.getElem?_drop]
      rw [← this, hdrop]; rfl
    rw [runJvmRes_nonbranch f prog _ (.checkcast "[Ljava/lang/Object;") hg rfl]
    cases e <;> rfl

/-- Exit blocker for `deserializeMacrocell.loop`: when `¬(i < numLines)` and `locs 12`
is an `.ext` GrowBuf value, `checkcast "[Ljava/lang/Object;"` at `pc 14` fails (`= none`). -/
theorem deserializeMacrocell_loop_exit_none (f : Nat) (locs : Nat → JvmVal)
    (lines : Array String) (numLines i : UInt32) (bytesAddr : Nat)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (e : AlgExt)
    (hl0 : locs 0 = .strArr lines) (hl1 : locs 1 = .i32 numLines)
    (hl2 : locs 2 = .i32 i) (hl4 : locs 4 = .heapRef bytesAddr)
    (hl12 : locs 12 = .ext e) (hge : ¬ i < numLines) :
    runJvmRes f f_Algorithm_deserializeMacrocell_loop_prog
        ⟨0, [], locs, jh, hp⟩ = none := by
  have h10 : AllFuelNoneAt f_Algorithm_deserializeMacrocell_loop_prog 10
      (f_Algorithm_deserializeMacrocell_loop_prog.drop 10)
      ⟨10, [], locs, jh, hp⟩ := by
    intro hpc hdrop
    rw [deserLoop_drop_10] at hdrop
    have h14 : AllFuelNoneAt f_Algorithm_deserializeMacrocell_loop_prog 14
        (.checkcast "[Ljava/lang/Object;" :: f_Algorithm_deserializeMacrocell_loop_prog.drop 15)
        ⟨14, [.ext e], locs, jh, hp⟩ := allFuelNoneAt_checkcast_ext_objArr
    have h13 := allFuelNoneAt_step (instr := .aload 12) (stk := []) (locs := locs) (jh := jh) (hp := hp) rfl
      (by dsimp only [stepInstr, Jvm.stepInstr]; rw [hl12]) h14
    have h12 := allFuelNoneAt_step
      (instr := .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
        "(Ljava/lang/Object;Ljava/lang/String;)V")
      (stk := [.str "null cannot be cast to non-null type kotlin.Array<*>", .ext e])
      (locs := locs) (jh := jh) (hp := hp) rfl rfl h13
    have h11 := allFuelNoneAt_step
      (instr := .ldcStr "null cannot be cast to non-null type kotlin.Array<*>")
      (stk := [.ext e]) (locs := locs) (jh := jh) (hp := hp) rfl rfl h12
    have h10' := allFuelNoneAt_step (instr := .aload 12) (stk := []) (locs := locs) (jh := jh) (hp := hp) rfl
      (by dsimp only [stepInstr, Jvm.stepInstr]; rw [hl12]) h11
    exact h10' hpc hdrop
  have h6 : AllFuelNoneAt f_Algorithm_deserializeMacrocell_loop_prog 6
      (f_Algorithm_deserializeMacrocell_loop_prog.drop 6)
      ⟨6, [], locs, jh, hp⟩ := by
    intro hpc hdrop
    rw [deserLoop_drop_6] at hdrop
    have hltF : decide (i < numLines) = false := decide_eq_false hge
    have h9 := allFuelNoneAt_iflt_fallthrough (tgt := 85)
      (v := if i == numLines then 0 else if i < numLines then 4294967295 else 1)
      (by rw [compareUnsigned_slt_zero]; exact hltF) h10
    have h8 := allFuelNoneAt_step (instr := .invokestatic "java/lang/Integer" "compareUnsigned" "(II)I")
      (stk := [.i32 numLines, .i32 i]) (locs := locs) (jh := jh) (hp := hp) rfl
      (by dsimp only [stepInstr]; exact stepStatic_compareUnsigned) h9
    have h7 := allFuelNoneAt_step (instr := .iload 1)
      (stk := [.i32 i]) (locs := locs) (jh := jh) (hp := hp) rfl
      (by dsimp only [stepInstr, Jvm.stepInstr]; rw [hl1]) h8
    have h6' := allFuelNoneAt_step (instr := .iload 2)
      (stk := []) (locs := locs) (jh := jh) (hp := hp) rfl
      (by dsimp only [stepInstr, Jvm.stepInstr]; rw [hl2]) h7
    exact h6' hpc hdrop
  have h0 : AllFuelNoneAt f_Algorithm_deserializeMacrocell_loop_prog 0
      f_Algorithm_deserializeMacrocell_loop_prog ⟨0, [], locs, jh, hp⟩ := by
    intro hpc hdrop
    have hd0 : f_Algorithm_deserializeMacrocell_loop_prog =
        f_Algorithm_deserializeMacrocell_loop_prog.drop 0 := rfl
    rw [hd0, deserLoop_drop_0] at hdrop
    have h5 := allFuelNoneAt_step
      (instr := .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter"
        "(Ljava/lang/Object;Ljava/lang/String;)V")
      (stk := [.str "bytes", .heapRef bytesAddr]) (locs := locs) (jh := jh) (hp := hp) rfl
      (by dsimp only [stepInstr]; exact stepStatic_checkNotNullParameter_hp (obj := .heapRef bytesAddr) rfl) h6
    have h4 := allFuelNoneAt_step (instr := .ldcStr "bytes")
      (stk := [.heapRef bytesAddr]) (locs := locs) (jh := jh) (hp := hp) rfl rfl h5
    have h3 := allFuelNoneAt_step (instr := .aload 4)
      (stk := []) (locs := locs) (jh := jh) (hp := hp) rfl
      (by dsimp only [stepInstr, Jvm.stepInstr]; rw [hl4]) h4
    have h2 := allFuelNoneAt_step
      (instr := .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter"
        "(Ljava/lang/Object;Ljava/lang/String;)V")
      (stk := [.str "lines", .strArr lines]) (locs := locs) (jh := jh) (hp := hp) rfl
      (by dsimp only [stepInstr]; exact stepStatic_checkNotNullParameter_hp (obj := .strArr lines) rfl) h3
    have h1 := allFuelNoneAt_step (instr := .ldcStr "lines")
      (stk := [.strArr lines]) (locs := locs) (jh := jh) (hp := hp) rfl rfl h2
    have h0' := allFuelNoneAt_step (instr := .aload 0)
      (stk := []) (locs := locs) (jh := jh) (hp := hp) rfl
      (by dsimp only [stepInstr, Jvm.stepInstr]; rw [hl0]) h1
    exact h0' hpc hdrop
  exact h0 rfl List.drop_zero f

private theorem step_deserLoop_prelude {f : Nat} {locs : Nat → JvmVal}
    {lines : Array String} {bytesAddr : Nat} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hl0 : locs 0 = .strArr lines) (hl4 : locs 4 = .heapRef bytesAddr) :
    runJvmResFast (f + 6) f_Algorithm_deserializeMacrocell_loop_prog 0
        f_Algorithm_deserializeMacrocell_loop_prog ⟨0, [], locs, jh, hp⟩ =
      runJvmResFast f f_Algorithm_deserializeMacrocell_loop_prog 6
        (f_Algorithm_deserializeMacrocell_loop_prog.drop 6) ⟨6, [], locs, jh, hp⟩ := by
  change runJvmResFast (f + 6) f_Algorithm_deserializeMacrocell_loop_prog 0
      (f_Algorithm_deserializeMacrocell_loop_prog.drop 0) ⟨0, [], locs, jh, hp⟩ = _
  rw [deserLoop_drop_0]
  step1; rw [hl0]
  step1
  rw [show f + 4 = (f + 3) + 1 from by omega]
  rw [runJvmResFast_invokestatic_step (stepStatic_checkNotNullParameter_hp (obj := .strArr lines) rfl)]
  step1; rw [hl4]
  step1
  rw [runJvmResFast_invokestatic_step (stepStatic_checkNotNullParameter_hp (obj := .heapRef bytesAddr) rfl)]

theorem step_deserLoop_test_true {f : Nat} {locs : Nat → JvmVal}
    {numLines i : UInt32} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hl1 : locs 1 = .i32 numLines) (hl2 : locs 2 = .i32 i) (hi : i < numLines) :
    runJvmResFast (f + 4) f_Algorithm_deserializeMacrocell_loop_prog 6
        (f_Algorithm_deserializeMacrocell_loop_prog.drop 6) ⟨6, [], locs, jh, hp⟩ =
      runJvmResFast f f_Algorithm_deserializeMacrocell_loop_prog 85
        (f_Algorithm_deserializeMacrocell_loop_prog.drop 85) ⟨85, [], locs, jh, hp⟩ := by
  rw [deserLoop_drop_6]
  step1; rw [hl2]; step1; rw [hl1]
  rw [show f + 2 = (f + 1) + 1 from by omega]
  rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned]
  rw [runJvmResFast_iflt_branch (by rw [compareUnsigned_slt_zero]; exact decide_eq_true hi)]

private theorem step_deserLoop_read_line {f : Nat} {locs : Nat → JvmVal}
    {lines : Array String} {numLines i : UInt32}
    {bytesAddr : Nat} {limit p col x y : UInt32} {leaf : UInt64}
    {nodes : Algorithm.GrowBuf Algorithm.MacroCell} {leaves : Algorithm.GrowBuf UInt64}
    {isLeaf : Algorithm.GrowBuf Bool} {warns : Algorithm.GrowBuf Algorithm.MacrocellWarning}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hlocs : DeserLoopLocs locs lines numLines i false bytesAddr limit p col x y leaf
      nodes leaves isLeaf warns)
    (hiSz : i.toNat < lines.size) (hibv : i.toBitVec.slt 0#32 = false) :
    let line := lines[i.toNat]
    let lBytes := line.toByteArray
    let newAddr := jh.objects.size
    let jh1 := (jh.alloc (.byteArray lBytes.data)).2
    let locs1 := setLocal (setLocal (setLocal locs 16 (.str line)) 17 (.heapRef newAddr))
      18 (.i32 lBytes.size.toUInt32)
    runJvmResFast (f + 17) f_Algorithm_deserializeMacrocell_loop_prog 85
        (f_Algorithm_deserializeMacrocell_loop_prog.drop 85) ⟨85, [], locs, jh, hp⟩ =
      runJvmResFast f f_Algorithm_deserializeMacrocell_loop_prog 102
        (.iload 18 :: .ifeq 992 :: f_Algorithm_deserializeMacrocell_loop_prog.drop 104)
        ⟨102, [], locs1, jh1, hp⟩ := by
  intro line lBytes newAddr jh1 locs1
  have hgetNew : jh1.get? newAddr = some (.byteArray lBytes.data) :=
    jvmHeap_get?_alloc_self _ _
  rw [deserLoop_drop_85]
  step1; rw [hlocs.h3]; simp only [Bool.false_eq_true, ↓reduceIte]
  rw [show f + 16 = (f + 15) + 1 from by omega]
  rw [runJvmResFast_ifne_fallthrough]
  step1; rw [hlocs.h0]; step1; rw [hlocs.h2]
  rw [show f + 13 = (f + 12) + 1 from by omega]
  rw [runJvmResFast_aaload_strArr hibv hiSz]
  step1; step1; step1
  rw [show f + 9 = (f + 8) + 1 from by omega]
  rw [runJvmResFast_checkNotNull_nonnull (by intro h; cases h)]
  step1; step1
  rw [show f + 6 = (f + 5) + 1 from by omega]
  rw [runJvmResFast_invokestatic_step stepStatic_stringsEncodeToByteArray]
  have henc : String.toUTF8 line = lBytes := rfl
  rw [henc]
  step1; step1
  rw [show f + 3 = (f + 2) + 1 from by omega]
  rw [runJvmResFast_arraylength_byteArray hgetNew]
  step1; step1
  dsimp only [locs1, jh1, newAddr, lBytes, line]
  rfl

private theorem step_deserLoop_blank_tail {locs : Nat → JvmVal}
    {lines : Array String} {numLines newI : UInt32} {bytesAddr : Nat}
    {warnsVal nodesVal leavesVal isLeafVal : JvmVal}
    {nodes : Algorithm.GrowBuf Algorithm.MacroCell} {leaves : Algorithm.GrowBuf UInt64}
    {isLeaf : Algorithm.GrowBuf Bool} {warns : Algorithm.GrowBuf Algorithm.MacrocellWarning}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hl0 : locs 0 = .strArr lines) (hl1 : locs 1 = .i32 numLines) (hl19 : locs 19 = .i32 newI)
    (hl17 : locs 17 = .heapRef bytesAddr) (hl18 : locs 18 = .i32 0)
    (hl12 : locs 12 = nodesVal) (hl13 : locs 13 = leavesVal) (hl14 : locs 14 = isLeafVal)
    (hl20 : locs 20 = warnsVal)
    (hn : mcNodes? nodesVal = some nodes) (hlv : mcLeaves? leavesVal = some leaves)
    (hil : mcIsLeaf? isLeafVal = some isLeaf) (hw : mcWarns? warnsVal = some warns) :
    ∃ locs',
      locs' 15 = warnsVal ∧
      DeserLoopLocs locs' lines numLines newI false bytesAddr 0 0 0 0 0 0
        nodes leaves isLeaf warns ∧
      ∀ f, runJvmResFast (f + 41) f_Algorithm_deserializeMacrocell_loop_prog 1016
          (f_Algorithm_deserializeMacrocell_loop_prog.drop 1016) ⟨1016, [], locs, jh, hp⟩ =
        runJvmResFast f f_Algorithm_deserializeMacrocell_loop_prog 6
          (f_Algorithm_deserializeMacrocell_loop_prog.drop 6) ⟨6, [], locs', jh, hp⟩ := by
  let locs' :=
    setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
      (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
        locs 21 (locs 0)) 22 (locs 1)) 23 (locs 12)) 24 (locs 13)) 25 (locs 14))
        0 (locs 0)) 1 (locs 1)) 2 (locs 19)) 3 (.i32 0)) 4 (locs 17))
        5 (locs 18)) 6 (.i32 0)) 7 (.i32 0)) 8 (.i32 0)) 9 (.i32 0))
        10 (.i64 0)) 12 (locs 12)) 13 (locs 13)) 14 (locs 14)) 15 (locs 20)
  refine ⟨locs', hl20,
    ⟨hl0, hl1, hl19, rfl, hl17, hl18, rfl, rfl, rfl, rfl, rfl,
     by dsimp only [locs']; change mcNodes? (locs 12) = _; rw [hl12]; exact hn,
     by dsimp only [locs']; change mcLeaves? (locs 13) = _; rw [hl13]; exact hlv,
     by dsimp only [locs']; change mcIsLeaf? (locs 14) = _; rw [hl14]; exact hil,
     by dsimp only [locs']; change mcWarns? (locs 20) = _; rw [hl20]; exact hw⟩, ?_⟩
  intro f
  rw [deserLoop_drop_1016]
  rw [show f + 41 = (f + 33) + 8 from by omega]; chunk 8
  rw [show f + 33 = (f + 25) + 8 from by omega]; chunk 8
  rw [show f + 25 = (f + 17) + 8 from by omega]; chunk 8
  rw [show f + 17 = (f + 9) + 8 from by omega]; chunk 8
  rw [show f + 9 = (f + 1) + 8 from by omega]; chunk 8
  rw [runJvmResFast_goto]

private theorem jvmHeap_get?_alloc_mono {jh : Jvm.JvmHeap AlgExt}
    {o1 o : Jvm.HeapObj AlgExt} {a : Nat} (ha : jh.get? a = some o) :
    (jh.alloc o1).2.get? a = some o := by
  rcases Array.getElem?_eq_some_iff.mp ha with ⟨hlt, _⟩
  exact (jvmHeap_get?_alloc_lt jh o1 hlt).trans ha

private theorem u8_sext_eq_35 (b : UInt8) :
    decide (UInt32.ofBitVec (b.toBitVec.signExtend 32) = 35) = decide (b = 35) := by
  by_cases hb : b = 35
  · subst hb; rfl
  · have hs : BitVec.setWidth 8 (b.toBitVec.signExtend 32) = b.toBitVec := by
      revert b; decide
    have hne : UInt32.ofBitVec (b.toBitVec.signExtend 32) ≠ 35 := by
      intro h
      apply hb
      have htr := congrArg (fun u : UInt32 => BitVec.setWidth 8 u.toBitVec) h
      rw [hs] at htr
      have h35 : BitVec.setWidth 8 (UInt32.toBitVec 35) = (35 : UInt8).toBitVec := rfl
      exact congrArg UInt8.ofBitVec (htr.trans h35)
    simp [hb, hne]

private theorem stepStatic_mcLeafWithCell_heap
    {pc : Nat} {isAlive y x : UInt32} {leaf : UInt64} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .i32 isAlive :: .i32 y :: .i32 x :: .i64 leaf :: rest, locs, jh, hp⟩
      "MacroCellLeanKt" "f_Algorithm_leafWithCell-9LuH6mI" "(JIIZ)J" =
      .inl (some ⟨pc + 1, .i64 (Algorithm.leafWithCell leaf x y (isAlive != 0)) :: rest,
        locs, jh, hp⟩) := rfl

theorem step_deserLoop_blank_line {locs : Nat → JvmVal}
    {lines : Array String} {numLines i : UInt32}
    {bytesAddr : Nat} {limit p col x y : UInt32} {leaf : UInt64}
    {nodes : Algorithm.GrowBuf Algorithm.MacroCell} {leaves : Algorithm.GrowBuf UInt64}
    {isLeaf : Algorithm.GrowBuf Bool} {warns : Algorithm.GrowBuf Algorithm.MacrocellWarning}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hlocs : DeserLoopLocs locs lines numLines i false bytesAddr limit p col x y leaf
      nodes leaves isLeaf warns)
    (hiSz : i.toNat < lines.size) (hibv : i.toBitVec.slt 0#32 = false)
    (hzero : lines[i.toNat].toByteArray.size.toUInt32 = 0) :
    ∃ (k : Nat) (locs' : Nat → JvmVal) (jh' : Jvm.JvmHeap AlgExt),
      (∀ a o, jh.get? a = some o → jh'.get? a = some o) ∧
      jh'.statics = jh.statics ∧
      (locs 15 = .ext (.mcWarnGrowBuf warns) →
        locs' 15 = .ext (.mcWarnGrowBuf (if i + 1 < numLines then warns.push (.blankLine (i + 1)) else warns))) ∧
      DeserLoopLocs locs' lines numLines (i + 1) false jh.objects.size 0 0 0 0 0 0
        nodes leaves isLeaf (if i + 1 < numLines then warns.push (.blankLine (i + 1)) else warns) ∧
      ∀ f, runJvmResFast (f + k) f_Algorithm_deserializeMacrocell_loop_prog 85
          (f_Algorithm_deserializeMacrocell_loop_prog.drop 85) ⟨85, [], locs, jh, hp⟩ =
        runJvmResFast f f_Algorithm_deserializeMacrocell_loop_prog 6
          (f_Algorithm_deserializeMacrocell_loop_prog.drop 6) ⟨6, [], locs', jh', hp⟩ := by
  let line := lines[i.toNat]
  let lBytes := line.toByteArray
  let jh1 := (jh.alloc (.byteArray lBytes.data)).2
  have hext1 : ∀ a o, jh.get? a = some o → jh1.get? a = some o :=
    fun _ _ ha => jvmHeap_get?_alloc_mono ha
  by_cases hi1 : i + 1 < numLines
  · simp only [hi1, ↓reduceIte]
    let wAddr := jh1.objects.size
    let jh2 := (jh1.alloc (.instance "com/alexvanyo/composelife/model/MacrocellWarning$BlankLine"
      [("lineIndex", .i32 (i + 1))])).2
    have hext2 : ∀ a o, jh.get? a = some o → jh2.get? a = some o :=
      fun a o ha => jvmHeap_get?_alloc_mono (hext1 a o ha)
    have hgetW : jh2.get? wAddr =
        some (.instance "com/alexvanyo/composelife/model/MacrocellWarning$BlankLine"
          [("lineIndex", .i32 (i + 1))]) := jvmHeap_get?_alloc_self _ _
    have hrle : decodeRLEWarning jh2 (.heapRef wAddr) = none := by
      dsimp only [decodeRLEWarning]; rw [hgetW]; rfl
    have hmcw : decodeMacrocellWarning jh2 (.heapRef wAddr) = some (.blankLine (i + 1)) := by
      dsimp only [decodeMacrocellWarning]; rw [hgetW]; rfl
    have hwPush := stepStatic_growBufPush_mcWarn (pc := 1012)
      (locs := setLocal (setLocal (setLocal (setLocal (setLocal locs 16 (.str line))
        17 (.heapRef jh.objects.size)) 18 (.i32 0)) 19 (.i32 (i + 1))) 20 .null)
      (wv := locs 15) (jh := jh2) (hp := hp) (rest := [])
      hlocs.h15 hrle hmcw
    rcases step_deserLoop_blank_tail (lines := lines) (numLines := numLines)
        (newI := i + 1) (bytesAddr := jh.objects.size)
        (warnsVal := .ext (.mcWarnGrowBuf (warns.push (.blankLine (i + 1)))))
        (nodesVal := locs 12) (leavesVal := locs 13) (isLeafVal := locs 14)
        (nodes := nodes) (leaves := leaves) (isLeaf := isLeaf)
        (warns := warns.push (.blankLine (i + 1)))
        (jh := jh2) (hp := hp)
        (locs := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
          locs 16 (.str line)) 17 (.heapRef jh.objects.size))
          18 (.i32 0)) 19 (.i32 (i + 1))) 20 .null)
          21 (.ext (.mcWarnGrowBuf (warns.push (.blankLine (i + 1))))))
          20 (.ext (.mcWarnGrowBuf (warns.push (.blankLine (i + 1))))))
        (by rw [setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_ne_eq rfl,
          setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_ne_eq rfl]; exact hlocs.h0)
        (by rw [setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_ne_eq rfl,
          setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_ne_eq rfl]; exact hlocs.h1)
        (by rw [setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_eq_val rfl])
        (by rw [setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_ne_eq rfl,
          setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_eq_val rfl])
        (by rw [setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_ne_eq rfl,
          setLocal_ne_eq rfl, setLocal_eq_val rfl])
        (by rw [setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_ne_eq rfl,
          setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_ne_eq rfl])
        (by rw [setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_ne_eq rfl,
          setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_ne_eq rfl])
        (by rw [setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_ne_eq rfl,
          setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_ne_eq rfl])
        (by rw [setLocal_eq_val rfl])
        hlocs.h12 hlocs.h13 hlocs.h14 rfl with ⟨locs', hw15, hdl', htail⟩
    refine ⟨81, locs', jh2, hext2, rfl, fun _ => hw15, hdl', ?_⟩
    intro f
    rw [show f + 81 = (f + 64) + 17 from by omega]
    rw [step_deserLoop_read_line hlocs hiSz hibv]
    step1; simp only [line] at *
    rw [hzero]
    rw [show f + 63 = (f + 62) + 1 from by omega]
    rw [runJvmResFast_ifeq_branch rfl]
    rw [deserLoop_drop_992]
    step1; rw [hlocs.h2]
    step1; step1; step1; step1
    step1; step1
    step1
    step1; rw [hlocs.h1]
    rw [show f + 53 = (f + 52) + 1 from by omega]
    rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned]
    rw [show f + 52 = (f + 51) + 1 from by omega]
    rw [runJvmResFast_iflt_branch (by rw [compareUnsigned_slt_zero]; exact decide_eq_true hi1)]
    rw [deserLoop_drop_1006]
    step1
    step1; step1
    step1
    step1
    rw [show f + 46 = (f + 45) + 1 from by omega]
    step1_ex
    dsimp only [jh2, wAddr, jh1, lBytes, line, Jvm.JvmHeap.alloc] at hwPush htail ⊢
    rw [show f + 45 = (f + 44) + 1 from by omega]
    rw [runJvmResFast_invokestatic_step hwPush]
    step1; step1
    rw [show f + 42 = (f + 41) + 1 from by omega]
    step1
    exact htail f
  · simp only [hi1, ↓reduceIte]
    rcases step_deserLoop_blank_tail (lines := lines) (numLines := numLines)
        (newI := i + 1) (bytesAddr := jh.objects.size)
        (warnsVal := locs 15) (nodesVal := locs 12) (leavesVal := locs 13) (isLeafVal := locs 14)
        (nodes := nodes) (leaves := leaves) (isLeaf := isLeaf) (warns := warns)
        (jh := jh1) (hp := hp)
        (locs := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal locs
          16 (.str line)) 17 (.heapRef jh.objects.size))
          18 (.i32 0)) 19 (.i32 (i + 1))) 20 .null) 20 (locs 15))
        (by rw [setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_ne_eq rfl,
          setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_ne_eq rfl]; exact hlocs.h0)
        (by rw [setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_ne_eq rfl,
          setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_ne_eq rfl]; exact hlocs.h1)
        (by rw [setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_eq_val rfl])
        (by rw [setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_ne_eq rfl,
          setLocal_ne_eq rfl, setLocal_eq_val rfl])
        (by rw [setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_ne_eq rfl,
          setLocal_eq_val rfl])
        (by rw [setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_ne_eq rfl,
          setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_ne_eq rfl])
        (by rw [setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_ne_eq rfl,
          setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_ne_eq rfl])
        (by rw [setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_ne_eq rfl,
          setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_ne_eq rfl])
        (by rw [setLocal_eq_val rfl])
        hlocs.h12 hlocs.h13 hlocs.h14 hlocs.h15 with ⟨locs', hw15, hdl', htail⟩
    refine ⟨74, locs', jh1, hext1, rfl, fun h => hw15.trans h, hdl', ?_⟩
    intro f
    rw [show f + 74 = (f + 57) + 17 from by omega]
    rw [step_deserLoop_read_line hlocs hiSz hibv]
    step1; simp only [line] at *
    rw [hzero]
    rw [show f + 56 = (f + 55) + 1 from by omega]
    rw [runJvmResFast_ifeq_branch rfl]
    rw [deserLoop_drop_992]
    step1; rw [hlocs.h2]
    step1; step1; step1; step1
    step1; step1
    step1
    step1; rw [hlocs.h1]
    rw [show f + 46 = (f + 45) + 1 from by omega]
    rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned]
    rw [show f + 45 = (f + 44) + 1 from by omega]
    rw [runJvmResFast_iflt_fallthrough (by rw [compareUnsigned_slt_zero]; exact decide_eq_false hi1)]
    step1
    step1
    rw [show f + 42 = (f + 41) + 1 from by omega]
    rw [runJvmResFast_goto]
    dsimp only [jh1, lBytes, line] at htail ⊢
    exact htail f

private def nonleafTarget (b0 : UInt8) : Nat :=
  if b0 == 35 then 944 else if b0 < 48 || 57 < b0 then 1057 else 128

private def nonleafDispFuel (b0 : UInt8) : Nat :=
  if b0 == 35 then 27 else if b0 < 48 then 35 else 43

private theorem step_deserLoop_nonleaf_dispatch {f : Nat} {locs : Nat → JvmVal}
    {lines : Array String} {numLines i : UInt32}
    {bytesAddr : Nat} {limit p col x y : UInt32} {leaf : UInt64}
    {nodes : Algorithm.GrowBuf Algorithm.MacroCell} {leaves : Algorithm.GrowBuf UInt64}
    {isLeaf : Algorithm.GrowBuf Bool} {warns : Algorithm.GrowBuf Algorithm.MacrocellWarning}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hlocs : DeserLoopLocs locs lines numLines i false bytesAddr limit p col x y leaf
      nodes leaves isLeaf warns)
    (hiSz : i.toNat < lines.size) (hibv : i.toBitVec.slt 0#32 = false)
    (hnz : lines[i.toNat].toByteArray.size.toUInt32 ≠ 0)
    (hlPos : 0 < lines[i.toNat].toByteArray.data.size) :
    let line := lines[i.toNat]
    let lBytes := line.toByteArray
    let b0 := lBytes.data[0]
    let sb0 := UInt32.ofBitVec (b0.toBitVec.signExtend 32)
    let jh1 := (jh.alloc (.byteArray lBytes.data)).2
    let locs1 := setLocal (setLocal (setLocal (setLocal locs 16 (.str line))
      17 (.heapRef jh.objects.size)) 18 (.i32 lBytes.size.toUInt32)) 19 (.i32 sb0)
    let tgt := nonleafTarget b0
    runJvmResFast (f + nonleafDispFuel b0) f_Algorithm_deserializeMacrocell_loop_prog 85
        (f_Algorithm_deserializeMacrocell_loop_prog.drop 85) ⟨85, [], locs, jh, hp⟩ =
      runJvmResFast f f_Algorithm_deserializeMacrocell_loop_prog tgt
        (f_Algorithm_deserializeMacrocell_loop_prog.drop tgt) ⟨tgt, [], locs1, jh1, hp⟩ := by
  intro line lBytes b0 sb0 jh1 locs1 tgt
  have hgetNew : jh1.get? jh.objects.size = some (.byteArray lBytes.data) :=
    jvmHeap_get?_alloc_self _ _
  have h0b : UInt32.ofBitVec (lBytes.data[(0 : UInt32).toNat].toBitVec.signExtend 32) = sb0 := rfl
  by_cases hb35 : b0 = 35
  · have hfn : nonleafDispFuel b0 = 27 := by simp [nonleafDispFuel, hb35]
    have htn : tgt = 944 := by simp [tgt, nonleafTarget, hb35]
    rw [hfn, htn, show f + 27 = (f + 10) + 17 from by omega]
    rw [step_deserLoop_read_line hlocs hiSz hibv]
    step1
    rw [show f + 9 = (f + 8) + 1 from by omega]
    rw [runJvmResFast_ifeq_fallthrough (beq_false_of_ne hnz)]
    rw [deserLoop_drop_104]
    step1
    step1
    rw [show f + 6 = (f + 5) + 1 from by omega]
    rw [runJvmResFast_baload_byteArray (idx := 0) hgetNew
      (by decide : (0 : UInt32).toBitVec.slt 0#32 = false) (by simpa [lBytes, line] using hlPos)]
    rw [h0b]; step1; step1
    step1; step1
    have heq35 : decide (sb0 = 35) = true := by
      dsimp only [sb0]; rw [u8_sext_eq_35, decide_eq_true hb35]
    exact runJvmResFast_if_icmpeq_branch (of_decide_eq_true heq35)
  · have hb35' : (b0 == 35) = false := beq_false_of_ne hb35
    have heq35 : decide (sb0 = 35) = false := by
      dsimp only [sb0]; rw [u8_sext_eq_35]; exact decide_eq_false hb35
    by_cases hlt48 : b0 < 48
    · have hfn : nonleafDispFuel b0 = 35 := by simp [nonleafDispFuel, hb35', hlt48]
      have htn : tgt = 1057 := by simp [tgt, nonleafTarget, hb35', hlt48]
      rw [hfn, htn, show f + 35 = (f + 18) + 17 from by omega]
      rw [step_deserLoop_read_line hlocs hiSz hibv]
      step1
      rw [show f + 17 = (f + 16) + 1 from by omega]
      rw [runJvmResFast_ifeq_fallthrough (beq_false_of_ne hnz)]
      rw [deserLoop_drop_104]
      step1
      step1
      rw [show f + 14 = (f + 13) + 1 from by omega]
      rw [runJvmResFast_baload_byteArray (idx := 0) hgetNew
        (by decide : (0 : UInt32).toBitVec.slt 0#32 = false) (by simpa [lBytes, line] using hlPos)]
      rw [h0b]; step1; step1
      step1; step1
      rw [show f + 9 = (f + 8) + 1 from by omega]
      rw [runJvmResFast_if_icmpeq_fallthrough heq35]
      step1; step1; step1
      step1
      step1; step1
      rw [u8_sext_and_255]
      rw [show f + 2 = (f + 1) + 1 from by omega]
      rw [runJvmResFast_invokestatic_step stepStatic_intrinsicsCompare]
      exact runJvmResFast_ifgt_branch (by
        rw [show (48 &&& 255 : UInt32) = 48 from rfl, u8_cmp_48_sgt]
        exact decide_eq_true hlt48)
    · have hfn : nonleafDispFuel b0 = 43 := by simp [nonleafDispFuel, hb35', hlt48]
      rw [hfn, show f + 43 = (f + 26) + 17 from by omega]
      rw [step_deserLoop_read_line hlocs hiSz hibv]
      step1
      rw [show f + 25 = (f + 24) + 1 from by omega]
      rw [runJvmResFast_ifeq_fallthrough (beq_false_of_ne hnz)]
      rw [deserLoop_drop_104]
      step1
      step1
      rw [show f + 22 = (f + 21) + 1 from by omega]
      rw [runJvmResFast_baload_byteArray (idx := 0) hgetNew
        (by decide : (0 : UInt32).toBitVec.slt 0#32 = false) (by simpa [lBytes, line] using hlPos)]
      rw [h0b]; step1; step1
      step1; step1
      rw [show f + 17 = (f + 16) + 1 from by omega]
      rw [runJvmResFast_if_icmpeq_fallthrough heq35]
      step1; step1; step1
      step1
      step1; step1
      rw [u8_sext_and_255]
      rw [show f + 10 = (f + 9) + 1 from by omega]
      rw [runJvmResFast_invokestatic_step stepStatic_intrinsicsCompare]
      rw [show f + 9 = (f + 8) + 1 from by omega]
      rw [runJvmResFast_ifgt_fallthrough (by
        rw [show (48 &&& 255 : UInt32) = 48 from rfl, u8_cmp_48_sgt]
        exact decide_eq_false hlt48)]
      step1
      step1; step1
      rw [u8_sext_and_255]
      step1; step1; step1
      rw [show f + 2 = (f + 1) + 1 from by omega]
      rw [runJvmResFast_invokestatic_step stepStatic_intrinsicsCompare]
      by_cases hgt57 : 57 < b0
      · have htn : tgt = 1057 := by simp [tgt, nonleafTarget, hb35', hlt48, hgt57]
        rw [htn]
        exact runJvmResFast_ifgt_branch (by
          rw [show (57 &&& 255 : UInt32) = 57 from rfl, u8_cmp_57_sgt]
          exact decide_eq_true hgt57)
      · have htn : tgt = 128 := by simp [tgt, nonleafTarget, hb35', hlt48, hgt57]
        rw [htn]
        exact runJvmResFast_ifgt_fallthrough (by
          rw [show (57 &&& 255 : UInt32) = 57 from rfl, u8_cmp_57_sgt]
          exact decide_eq_false hgt57)

theorem step_deserLoop_comment_line {locs : Nat → JvmVal}
    {lines : Array String} {numLines i : UInt32}
    {bytesAddr : Nat} {limit p col x y : UInt32} {leaf : UInt64}
    {nodes : Algorithm.GrowBuf Algorithm.MacroCell} {leaves : Algorithm.GrowBuf UInt64}
    {isLeaf : Algorithm.GrowBuf Bool} {warns : Algorithm.GrowBuf Algorithm.MacrocellWarning}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hlocs : DeserLoopLocs locs lines numLines i false bytesAddr limit p col x y leaf
      nodes leaves isLeaf warns)
    (hiSz : i.toNat < lines.size) (hibv : i.toBitVec.slt 0#32 = false)
    (hnz : lines[i.toNat].toByteArray.size.toUInt32 ≠ 0)
    (hlPos : 0 < lines[i.toNat].toByteArray.data.size)
    (hb35 : lines[i.toNat].toByteArray.data[0] = 35) :
    let lineLen := lines[i.toNat].toByteArray.size.toUInt32
    let jh1 := (jh.alloc (.byteArray lines[i.toNat].toByteArray.data)).2
    ∃ locs',
      locs' 15 = locs 15 ∧
      DeserLoopLocs locs' lines numLines (i + 1) false jh.objects.size lineLen 0 0 0 0 0
        nodes leaves isLeaf warns ∧
      ∀ f, runJvmResFast (f + 75) f_Algorithm_deserializeMacrocell_loop_prog 85
          (f_Algorithm_deserializeMacrocell_loop_prog.drop 85) ⟨85, [], locs, jh, hp⟩ =
        runJvmResFast f f_Algorithm_deserializeMacrocell_loop_prog 6
          (f_Algorithm_deserializeMacrocell_loop_prog.drop 6) ⟨6, [], locs', jh1, hp⟩ := by
  intro lineLen jh1
  let locs1 := setLocal (setLocal (setLocal (setLocal locs 16 (.str lines[i.toNat]))
    17 (.heapRef jh.objects.size)) 18 (.i32 lineLen)) 19 (.i32 35)
  let locs' :=
    setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
      (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
        (setLocal (setLocal locs1 20 (locs 0)) 21 (locs 1)) 22 (.i32 (i + 1)))
        23 (locs 12)) 24 (locs 13)) 25 (locs 14)) 26 (locs 15))
        0 (locs 0)) 1 (locs 1)) 2 (.i32 (i + 1))) 3 (.i32 0)) 4 (.heapRef jh.objects.size))
        5 (.i32 lineLen)) 6 (.i32 0)) 7 (.i32 0)) 8 (.i32 0)) 9 (.i32 0))
        10 (.i64 0)) 12 (locs 12)) 13 (locs 13)) 14 (locs 14)) 15 (locs 15)
  refine ⟨locs', rfl,
    ⟨hlocs.h0, hlocs.h1, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
     hlocs.h12, hlocs.h13, hlocs.h14, hlocs.h15⟩, ?_⟩
  intro f
  have hd := step_deserLoop_nonleaf_dispatch (f := f + 48) (jh := jh) (hp := hp)
    hlocs hiSz hibv hnz hlPos
  dsimp only at hd
  rw [hb35] at hd
  have hif35 : nonleafDispFuel 35 = 27 := rfl
  have htg35 : nonleafTarget 35 = 944 := rfl
  have h35 : UInt32.ofBitVec ((35 : UInt8).toBitVec.signExtend 32) = 35 := rfl
  rw [hif35, htg35, h35] at hd
  rw [show f + 75 = (f + 48) + 27 from by omega, hd, deserLoop_drop_944]
  rw [show f + 48 = (f + 43) + 5 from by omega]; chunk 5; rw [hlocs.h2]
  rw [show f + 43 = (f + 41) + 2 from by omega]; chunk 2
  rw [show f + 41 = (f + 40) + 1 from by omega, runJvmResFast_invokestatic_step stepStatic_uintCtor5a]
  rw [show f + 40 = (f + 32) + 8 from by omega]; chunk 8
  rw [show f + 32 = (f + 24) + 8 from by omega]; chunk 8
  rw [show f + 24 = (f + 16) + 8 from by omega]; chunk 8
  rw [show f + 16 = (f + 8) + 8 from by omega]; chunk 8
  rw [show f + 8 = (f + 1) + 7 from by omega]; chunk 7
  rw [runJvmResFast_goto]

private theorem step_deserLoop_nondigit_tail {locs : Nat → JvmVal}
    {lines : Array String} {numLines i lineLen : UInt32} {bytesAddr : Nat}
    {nodes : Algorithm.GrowBuf Algorithm.MacroCell} {leaves : Algorithm.GrowBuf UInt64}
    {isLeaf : Algorithm.GrowBuf Bool} {warns : Algorithm.GrowBuf Algorithm.MacrocellWarning}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hl0 : locs 0 = .strArr lines) (hl1 : locs 1 = .i32 numLines) (hl2 : locs 2 = .i32 i)
    (hl17 : locs 17 = .heapRef bytesAddr) (hl18 : locs 18 = .i32 lineLen)
    (hn : mcNodes? (locs 12) = some nodes) (hlv : mcLeaves? (locs 13) = some leaves)
    (hil : mcIsLeaf? (locs 14) = some isLeaf) (hw : mcWarns? (locs 15) = some warns) :
    ∃ locs',
      locs' 15 = locs 15 ∧
      DeserLoopLocs locs' lines numLines i true bytesAddr lineLen 0 0 0 0 0
        nodes leaves isLeaf warns ∧
      ∀ f, runJvmResFast (f + 45) f_Algorithm_deserializeMacrocell_loop_prog 1057
          (f_Algorithm_deserializeMacrocell_loop_prog.drop 1057) ⟨1057, [], locs, jh, hp⟩ =
        runJvmResFast f f_Algorithm_deserializeMacrocell_loop_prog 6
          (f_Algorithm_deserializeMacrocell_loop_prog.drop 6) ⟨6, [], locs', jh, hp⟩ := by
  let locs' :=
    setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
      (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
        (setLocal (setLocal locs 19 (locs 0)) 20 (locs 1)) 21 (locs 2))
        22 (locs 12)) 23 (locs 13)) 24 (locs 14)) 25 (locs 15))
        0 (locs 0)) 1 (locs 1)) 2 (locs 2)) 3 (.i32 1)) 4 (locs 17))
        5 (locs 18)) 6 (.i32 0)) 7 (.i32 0)) 8 (.i32 0)) 9 (.i32 0))
        10 (.i64 0)) 12 (locs 12)) 13 (locs 13)) 14 (locs 14)) 15 (locs 15)
  refine ⟨locs', rfl,
    ⟨hl0, hl1, hl2, rfl, hl17, hl18, rfl, rfl, rfl, rfl, rfl, hn, hlv, hil, hw⟩, ?_⟩
  intro f
  rw [deserLoop_drop_1057]
  rw [show f + 45 = (f + 37) + 8 from by omega]; chunk 8
  rw [show f + 37 = (f + 29) + 8 from by omega]; chunk 8
  rw [show f + 29 = (f + 21) + 8 from by omega]; chunk 8
  rw [show f + 21 = (f + 13) + 8 from by omega]; chunk 8
  rw [show f + 13 = (f + 5) + 8 from by omega]; chunk 8
  rw [show f + 5 = (f + 1) + 4 from by omega]; chunk 4
  rw [runJvmResFast_goto]

theorem step_deserLoop_nondigit_line {locs : Nat → JvmVal}
    {lines : Array String} {numLines i : UInt32}
    {bytesAddr : Nat} {limit p col x y : UInt32} {leaf : UInt64}
    {nodes : Algorithm.GrowBuf Algorithm.MacroCell} {leaves : Algorithm.GrowBuf UInt64}
    {isLeaf : Algorithm.GrowBuf Bool} {warns : Algorithm.GrowBuf Algorithm.MacrocellWarning}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hlocs : DeserLoopLocs locs lines numLines i false bytesAddr limit p col x y leaf
      nodes leaves isLeaf warns)
    (hiSz : i.toNat < lines.size) (hibv : i.toBitVec.slt 0#32 = false)
    (hnz : lines[i.toNat].toByteArray.size.toUInt32 ≠ 0)
    (hlPos : 0 < lines[i.toNat].toByteArray.data.size)
    (hb35 : lines[i.toNat].toByteArray.data[0] ≠ 35)
    (hnd : lines[i.toNat].toByteArray.data[0] < 48 ∨ (57 : UInt8) < lines[i.toNat].toByteArray.data[0]) :
    let lineLen := lines[i.toNat].toByteArray.size.toUInt32
    let jh1 := (jh.alloc (.byteArray lines[i.toNat].toByteArray.data)).2
    ∃ (k : Nat) (locs' : Nat → JvmVal),
      locs' 15 = locs 15 ∧
      DeserLoopLocs locs' lines numLines i true jh.objects.size lineLen 0 0 0 0 0
        nodes leaves isLeaf warns ∧
      ∀ f, runJvmResFast (f + k) f_Algorithm_deserializeMacrocell_loop_prog 85
          (f_Algorithm_deserializeMacrocell_loop_prog.drop 85) ⟨85, [], locs, jh, hp⟩ =
        runJvmResFast f f_Algorithm_deserializeMacrocell_loop_prog 6
          (f_Algorithm_deserializeMacrocell_loop_prog.drop 6) ⟨6, [], locs', jh1, hp⟩ := by
  intro lineLen jh1
  let b0 := lines[i.toNat].toByteArray.data[0]
  let sb0 := UInt32.ofBitVec (b0.toBitVec.signExtend 32)
  have hb35b : (b0 == 35) = false := beq_false_of_ne hb35
  rcases step_deserLoop_nondigit_tail (lines := lines) (numLines := numLines)
      (i := i) (lineLen := lineLen) (bytesAddr := jh.objects.size)
      (locs := setLocal (setLocal (setLocal (setLocal locs 16 (.str lines[i.toNat]))
        17 (.heapRef jh.objects.size)) 18 (.i32 lineLen)) 19 (.i32 sb0))
      (nodes := nodes) (leaves := leaves) (isLeaf := isLeaf) (warns := warns)
      (jh := jh1) (hp := hp)
      (by rw [setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_ne_eq rfl]; exact hlocs.h0)
      (by rw [setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_ne_eq rfl]; exact hlocs.h1)
      (by rw [setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_ne_eq rfl]; exact hlocs.h2)
      (by rw [setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_eq_val rfl])
      (by rw [setLocal_ne_eq rfl, setLocal_eq_val rfl])
      (by rw [setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_ne_eq rfl]; exact hlocs.h12)
      (by rw [setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_ne_eq rfl]; exact hlocs.h13)
      (by rw [setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_ne_eq rfl]; exact hlocs.h14)
      (by rw [setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_ne_eq rfl]; exact hlocs.h15)
      with ⟨locs', hw15, hdl', htail⟩
  refine ⟨nonleafDispFuel b0 + 45, locs', hw15, hdl', ?_⟩
  intro f
  have hd := step_deserLoop_nonleaf_dispatch (f := f + 45) (jh := jh) (hp := hp)
    hlocs hiSz hibv hnz hlPos
  have hd1 :
      runJvmResFast (f + 45 + nonleafDispFuel b0) f_Algorithm_deserializeMacrocell_loop_prog 85
          (f_Algorithm_deserializeMacrocell_loop_prog.drop 85) ⟨85, [], locs, jh, hp⟩ =
        runJvmResFast (f + 45) f_Algorithm_deserializeMacrocell_loop_prog 1057
          (f_Algorithm_deserializeMacrocell_loop_prog.drop 1057)
          ⟨1057, [], setLocal (setLocal (setLocal (setLocal locs 16 (.str lines[i.toNat]))
            17 (.heapRef jh.objects.size)) 18 (.i32 lineLen)) 19 (.i32 sb0), jh1, hp⟩ := by
    dsimp only [b0] at hb35b
    rcases hnd with hlt | hgt
    · dsimp only [b0, sb0, lineLen, jh1] at hlt ⊢
      simp only [nonleafTarget, hb35b, hlt, decide_true, ↓reduceIte, Bool.true_or] at hd
      exact hd
    · dsimp only [b0, sb0, lineLen, jh1] at hgt ⊢
      simp only [nonleafTarget, hb35b, hgt, decide_true, ↓reduceIte, Bool.or_true] at hd
      exact hd
  rw [show f + (nonleafDispFuel b0 + 45) = (f + 45) + nonleafDispFuel b0 from by omega, hd1]
  exact htail f

private theorem stepStatic_parseMCNodeLine_some {pc : Nat} {addr : Nat}
    {bytes : ByteArray} {nl : Algorithm.MCNodeLine}
    {rest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hget : jh.get? addr = some (.byteArray bytes.data))
    (hsome : Algorithm.parseMCNodeLine bytes = some nl) :
    let inner : Array JvmVal := (Array.replicate 50 .null)
      |>.set! 0 (.boxedInt 0)
      |>.set! 1 (.boxedUInt nl.level)
      |>.set! 5 (.boxedUInt nl.nw)
      |>.set! 9 (.boxedUInt nl.nwStart)
      |>.set! 13 (.boxedUInt nl.nwEnd)
      |>.set! 17 (.boxedUInt nl.ne)
      |>.set! 21 (.boxedUInt nl.neStart)
      |>.set! 25 (.boxedUInt nl.neEnd)
      |>.set! 29 (.boxedUInt nl.sw)
      |>.set! 33 (.boxedUInt nl.swStart)
      |>.set! 37 (.boxedUInt nl.swEnd)
      |>.set! 41 (.boxedUInt nl.se)
      |>.set! 45 (.boxedUInt nl.seStart)
      |>.set! 49 (.boxedUInt nl.seEnd)
    let (inAddr, h1) := jh.alloc (.objArray "java/lang/Object" inner)
    let (outAddr, h2) := h1.alloc (.objArray "java/lang/Object" #[.boxedInt 1, .heapRef inAddr])
    stepInvokeStatic ⟨pc, .heapRef addr :: rest, locs, jh, hp⟩
        "MacroCellLeanKt" "f_Algorithm_parseMCNodeLine" "([B)Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, .heapRef outAddr :: rest, locs, h2, hp⟩) := by
  change (match decodeBytes ⟨pc, .heapRef addr :: rest, locs, jh, hp⟩ (.heapRef addr) with
    | some bs =>
      match Algorithm.parseMCNodeLine bs with
      | none =>
        let (resAddr, h') := jh.alloc (.objArray "java/lang/Object" #[.boxedInt 0])
        Sum.inl (some (⟨pc + 1, Jvm.JvmVal.heapRef resAddr :: rest, locs, h', hp⟩ : JvmState))
      | some nl =>
        let inner : Array JvmVal := (Array.replicate 50 Jvm.JvmVal.null)
          |>.set! 0 (Jvm.JvmVal.boxedInt 0)
          |>.set! 1 (Jvm.JvmVal.boxedUInt nl.level)
          |>.set! 5 (Jvm.JvmVal.boxedUInt nl.nw)
          |>.set! 9 (Jvm.JvmVal.boxedUInt nl.nwStart)
          |>.set! 13 (Jvm.JvmVal.boxedUInt nl.nwEnd)
          |>.set! 17 (Jvm.JvmVal.boxedUInt nl.ne)
          |>.set! 21 (Jvm.JvmVal.boxedUInt nl.neStart)
          |>.set! 25 (Jvm.JvmVal.boxedUInt nl.neEnd)
          |>.set! 29 (Jvm.JvmVal.boxedUInt nl.sw)
          |>.set! 33 (Jvm.JvmVal.boxedUInt nl.swStart)
          |>.set! 37 (Jvm.JvmVal.boxedUInt nl.swEnd)
          |>.set! 41 (Jvm.JvmVal.boxedUInt nl.se)
          |>.set! 45 (Jvm.JvmVal.boxedUInt nl.seStart)
          |>.set! 49 (Jvm.JvmVal.boxedUInt nl.seEnd)
        let (inAddr, h1) := jh.alloc (.objArray "java/lang/Object" inner)
        let (outAddr, h2) := h1.alloc (.objArray "java/lang/Object" #[.boxedInt 1, .heapRef inAddr])
        Sum.inl (some (⟨pc + 1, Jvm.JvmVal.heapRef outAddr :: rest, locs, h2, hp⟩ : JvmState))
    | none => Sum.inr none) = _
  simp only [decodeBytes, hget]
  have hb : (⟨bytes.data⟩ : ByteArray) = bytes := rfl
  rw [hb, hsome]
  dsimp only [Jvm.JvmHeap.alloc]

private theorem stepStatic_mcMakeLevel4Node_heap
    {pc : Nat} {se sw ne nw : UInt64} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .i64 se :: .i64 sw :: .i64 ne :: .i64 nw :: rest, locs, jh, hp⟩
      "MacroCellLeanKt" "f_Algorithm_makeLevel4Node-2jIhpxI"
      "(JJJJ)Lcom/alexvanyo/composelife/model/MacroCell;" =
      .inl (some ⟨pc + 1, .ext (.mc (Algorithm.makeLevel4Node nw ne sw se)) :: rest,
        locs, jh, hp⟩) := rfl

private theorem stepStatic_booleanValueOf {pc : Nat} {b : UInt32} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .i32 b :: rest, locs, jh, hp⟩
      "java/lang/Boolean" "valueOf" "(Z)Ljava/lang/Boolean;" =
      .inl (some ⟨pc + 1, .boxedBool (b != 0) :: rest, locs, jh, hp⟩) := rfl

theorem step_deserLoop_parseNode_none {locs : Nat → JvmVal}
    {lines : Array String} {numLines i : UInt32}
    {bytesAddr : Nat} {limit p col x y : UInt32} {leaf : UInt64}
    {nodes : Algorithm.GrowBuf Algorithm.MacroCell} {leaves : Algorithm.GrowBuf UInt64}
    {isLeaf : Algorithm.GrowBuf Bool} {warns : Algorithm.GrowBuf Algorithm.MacrocellWarning}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hlocs : DeserLoopLocs locs lines numLines i false bytesAddr limit p col x y leaf
      nodes leaves isLeaf warns)
    (hwarnBuf : locs 15 = .ext (.mcWarnGrowBuf warns))
    (hstat : jh.getStatic? "MacroCellLeanKt" "EMPTY_LEVEL_4" = none)
    (hiSz : i.toNat < lines.size) (hibv : i.toBitVec.slt 0#32 = false)
    (hnz : lines[i.toNat].toByteArray.size.toUInt32 ≠ 0)
    (hlPos : 0 < lines[i.toNat].toByteArray.data.size)
    (h48 : ¬ lines[i.toNat].toByteArray.data[0] < 48)
    (h57 : ¬ (57 : UInt8) < lines[i.toNat].toByteArray.data[0])
    (hnone : Algorithm.parseMCNodeLine lines[i.toNat].toByteArray = none) :
    let line := lines[i.toNat]
    let jh1 := (jh.alloc (.byteArray line.toByteArray.data)).2
    let jh2 := (jh1.alloc (.objArray "java/lang/Object" #[.boxedInt 0])).2
    let enc := encodeMacrocellResult jh2 ⟨.unexpectedInput line i, warns.toArray, Algorithm.emptyLevel4⟩
    ∃ locs',
      ∀ f, runJvmResFast (f + 84) f_Algorithm_deserializeMacrocell_loop_prog 85
          (f_Algorithm_deserializeMacrocell_loop_prog.drop 85) ⟨85, [], locs, jh, hp⟩ =
        some (enc.1, ⟨168, [enc.1], locs', enc.2, hp⟩) := by
  intro line jh1 jh2 enc
  have hb35 : line.toByteArray.data[0] ≠ 35 := by
    intro h; rw [h] at h48; exact h48 (by decide)
  have hb35b : (line.toByteArray.data[0] == 35) = false := beq_false_of_ne hb35
  have hgetNew : jh1.get? jh.objects.size = some (.byteArray line.toByteArray.data) :=
    jvmHeap_get?_alloc_self _ _
  have hgetP : jh2.get? jh1.objects.size = some (.objArray "java/lang/Object" #[.boxedInt 0]) :=
    jvmHeap_get?_alloc_self _ _
  dsimp only [jh2, Jvm.JvmHeap.alloc] at hgetP
  let uiObj : Jvm.HeapObj AlgExt :=
    .instance "com/alexvanyo/composelife/model/MacrocellStatus$UnexpectedInput"
      [("input", .str line), ("lineIndex", .i32 i)]
  let jh3 := (jh2.alloc uiObj).2
  have hgetUI3 : jh3.get? jh2.objects.size = some uiObj := jvmHeap_get?_alloc_self _ _
  have hgetUI4 : (encodeGrowBufArray jh3 encodeMacrocellWarning warns).2.get? jh2.objects.size =
      some uiObj :=
    encodeGrowBufArray_get?_ext jh3 encodeMacrocellWarning warns encodeMCWarn_get?_ext
      jh2.objects.size uiObj hgetUI3
  have hgetUI4' : ((encodeGrowBufArray jh3 encodeMacrocellWarning warns).2.get?
      jh2.objects.size).bind
      (fun o => match o with | .instance c _ => some c | _ => none) =
      some "com/alexvanyo/composelife/model/MacrocellStatus$UnexpectedInput" := by
    rw [hgetUI4]; rfl
  have hstat4 : (encodeGrowBufArray jh3 encodeMacrocellWarning warns).2.getStatic?
      "MacroCellLeanKt" "EMPTY_LEVEL_4" = none := by
    dsimp only [Jvm.JvmHeap.getStatic?]
    rw [encodeGrowBufArray_statics jh3 encodeMacrocellWarning warns encodeMCWarn_statics]
    exact hstat
  let locsD := setLocal (setLocal (setLocal (setLocal locs 16 (.str line))
    17 (.heapRef jh.objects.size)) 18 (.i32 line.toByteArray.size.toUInt32))
    19 (.i32 (UInt32.ofBitVec (line.toByteArray.data[0].toBitVec.signExtend 32)))
  let locs' := setLocal (setLocal (setLocal (setLocal locsD 20 (.heapRef jh1.objects.size))
    22 (.heapRef jh2.objects.size)) 23 (encodeGrowBufArray jh3 encodeMacrocellWarning warns).1)
    25 (.i32 0)
  refine ⟨locs', fun f => ?_⟩
  have hd := step_deserLoop_nonleaf_dispatch (f := f + 41) (jh := jh) (hp := hp)
    hlocs hiSz hibv hnz hlPos
  simp only [nonleafDispFuel, nonleafTarget, line, hb35b, h48, h57, decide_false, Bool.false_eq_true,
    Bool.or_false, ↓reduceIte] at hd
  rw [show f + 84 = (f + 41) + 43 from by omega, hd, deserLoop_drop_128]
  step1_ex
  rw [show f + 40 = (f + 39) + 1 from by omega]
  rw [runJvmResFast_invokestatic_step (stepStatic_parseMCNodeLine_none hgetNew hnone)]
  step1_ex; step1_ex; step1_ex
  rw [show f + 36 = (f + 35) + 1 from by omega]
  rw [runJvmResFast_checkNotNull_nonnull (by intro h; cases h)]
  step1_ex
  rw [show f + 34 = (f + 33) + 1 from by omega]
  rw [runJvmResFast_checkcast_objArray hgetP (Or.inl rfl)]
  step1_ex
  rw [show f + 32 = (f + 31) + 1 from by omega]
  rw [runJvmResFast_aaload hgetP (by decide) (by decide)]
  step1_ex; step1_ex
  rw [show f + 29 = (f + 28) + 1 from by omega]
  rw [runJvmResFast_checkNotNull_nonnull (by intro h; cases h)]
  rw [show #[JvmVal.boxedInt 0][UInt32.toNat 0] = JvmVal.boxedInt 0 from rfl]
  rw [show f + 28 = (f + 27) + 1 from by omega]
  rw [runJvmResFast_checkcast_boxedInt (Or.inl rfl)]
  step1_ex
  rw [show f + 26 = (f + 25) + 1 from by omega]
  rw [runJvmResFast_tableswitch]
  rw [show Jvm.tableswitchTarget 0 0 [144, 169] 938 = 144 from by decide]
  dsimp only
  rw [deserLoop_drop_144]
  step1_ex; step1_ex; step1_ex
  step1_ex; step1_ex
  rw [hlocs.h2]
  step1_ex; step1_ex
  step1_ex; step1_ex
  rw [hwarnBuf]
  rw [show f + 16 = (f + 15) + 1 from by omega]
  rw [runJvmResFast_invokestatic_step stepStatic_growBufToArray_mcWarn]
  step1; step1; step1; step1
  (conv in (runJvmResFast _ _ _ _ _) =>
    dsimp only [Jvm.JvmState.pc, Jvm.JvmState.stack, Jvm.JvmState.locals,
      Jvm.JvmState.jvmHeap, Jvm.JvmState.heap]
    norm_jvm_locals
    try simp only [Nat.reduceAdd])
  rw [show f + 11 = (f + 10) + 1 from by omega]
  rw [runJvmResFast_checkcast_instance (ty := "com/alexvanyo/composelife/model/MacrocellStatus")
    (by exact hgetUI4') rfl]
  step1; step1; step1
  (conv in (runJvmResFast _ _ _ _ _) =>
    dsimp only [Jvm.JvmState.pc, Jvm.JvmState.stack, Jvm.JvmState.locals,
      Jvm.JvmState.jvmHeap, Jvm.JvmState.heap]
    norm_jvm_locals
    try simp only [Nat.reduceAdd])
  rw [show f + 7 = (f + 6) + 1 from by omega]
  erw [runJvmResFast_invokestatic_step (stepStatic_getEMPTY_LEVEL_4 hstat4)]
  step1; step1; step1
  (conv in (runJvmResFast _ _ _ _ _) =>
    dsimp only [Jvm.JvmState.pc, Jvm.JvmState.stack, Jvm.JvmState.locals,
      Jvm.JvmState.jvmHeap, Jvm.JvmState.heap]
    norm_jvm_locals
    try simp only [Nat.reduceAdd])
  rw [show f + 3 = (f + 2) + 1 from by omega]
  rw [runJvmResFast_checkNotNull_nonnull (by intro h; cases h)]
  step1
  (conv in (runJvmResFast _ _ _ _ _) =>
    dsimp only [Jvm.JvmState.pc, Jvm.JvmState.stack, Jvm.JvmState.locals,
      Jvm.JvmState.jvmHeap, Jvm.JvmState.heap]
    norm_jvm_locals
    try simp only [Nat.reduceAdd])
  rw [runJvmResFast_areturn]
  rfl

theorem step_deserLoop_leaf_end {locs : Nat → JvmVal}
    {lines : Array String} {numLines i : UInt32}
    {bytesAddr : Nat} {limit p col x y : UInt32} {leaf : UInt64}
    {nodes : Algorithm.GrowBuf Algorithm.MacroCell} {leaves : Algorithm.GrowBuf UInt64}
    {isLeaf : Algorithm.GrowBuf Bool} {warns : Algorithm.GrowBuf Algorithm.MacrocellWarning}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hlocs : DeserLoopLocs locs lines numLines i true bytesAddr limit p col x y leaf
      nodes leaves isLeaf warns)
    (hpGe : ¬ p < limit) :
    ∃ locs',
      locs' 15 = locs 15 ∧
      DeserLoopLocs locs' lines numLines (i + 1) false bytesAddr limit 0 0 0 0 0
        (nodes.push (Algorithm.makeLevel4Node leaf 0 0 0)) (leaves.push leaf) (isLeaf.push true) warns ∧
      ∀ f, runJvmResFast (f + 72) f_Algorithm_deserializeMacrocell_loop_prog 85
          (f_Algorithm_deserializeMacrocell_loop_prog.drop 85) ⟨85, [], locs, jh, hp⟩ =
        runJvmResFast f f_Algorithm_deserializeMacrocell_loop_prog 6
          (f_Algorithm_deserializeMacrocell_loop_prog.drop 6) ⟨6, [], locs', jh, hp⟩ := by
  let mcNode := Algorithm.makeLevel4Node leaf 0 0 0
  let locs' :=
    setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
      (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
        (setLocal (setLocal (setLocal (setLocal (setLocal locs
          16 (.i32 (i + 1))) 17 (.ext (.mc mcNode)))
          18 (.ext (.mcGrowBuf (nodes.push mcNode))))
          19 (.ext (.u64GrowBuf (leaves.push leaf))))
          20 (.ext (.boolGrowBuf (isLeaf.push true))))
          21 (locs 0)) 22 (locs 1)) 23 (locs 4)) 24 (locs 5)) 25 (locs 15))
          0 (locs 0)) 1 (locs 1)) 2 (.i32 (i + 1))) 3 (.i32 0)) 4 (locs 4)) 5 (locs 5))
          6 (.i32 0)) 7 (.i32 0)) 8 (.i32 0)) 9 (.i32 0)) 10 (.i64 0))
          12 (.ext (.mcGrowBuf (nodes.push mcNode))))
          13 (.ext (.u64GrowBuf (leaves.push leaf))))
          14 (.ext (.boolGrowBuf (isLeaf.push true))))
          15 (locs 15)
  refine ⟨locs', rfl,
    ⟨hlocs.h0, hlocs.h1, rfl, rfl, hlocs.h4, hlocs.h5, rfl, rfl, rfl, rfl, rfl,
     rfl, rfl, rfl, hlocs.h15⟩, ?_⟩
  intro f
  rw [deserLoop_drop_85]
  step1_ex; rw [hlocs.h3]
  rw [show f + 71 = (f + 70) + 1 from by omega]
  rw [runJvmResFast_ifne_branch (by decide)]
  rw [deserLoop_drop_1127]
  step1_ex; rw [hlocs.h6]; step1_ex; rw [hlocs.h5]
  rw [show f + 68 = (f + 67) + 1 from by omega]
  rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned]
  rw [show f + 67 = (f + 66) + 1 from by omega]
  rw [runJvmResFast_iflt_fallthrough (by rw [compareUnsigned_slt_zero]; exact decide_eq_false hpGe)]
  rw [deserLoop_drop_1131]
  step1_ex; rw [hlocs.h2]; step1_ex; step1_ex; step1_ex; step1_ex
  step1_ex; rw [hlocs.h10]
  step1_ex; step1_ex; step1_ex
  rw [show f + 57 = (f + 56) + 1 from by omega]
  rw [runJvmResFast_invokestatic_step stepStatic_mcMakeLevel4Node_heap]
  step1_ex
  step1_ex
  step1_ex
  rw [show f + 53 = (f + 52) + 1 from by omega]
  rw [runJvmResFast_invokestatic_step (stepStatic_growBufPush_mc hlocs.h12)]
  step1_ex
  step1_ex
  step1_ex
  rw [hlocs.h10]
  step1_ex
  rw [show f + 48 = (f + 47) + 1 from by omega]
  rw [runJvmResFast_invokestatic_step (stepStatic_growBufPush_u64 hlocs.h13)]
  step1_ex
  step1_ex
  step1_ex
  rw [show f + 44 = (f + 43) + 1 from by omega]
  rw [runJvmResFast_invokestatic_step stepStatic_booleanValueOf]
  rw [show f + 43 = (f + 42) + 1 from by omega]
  rw [runJvmResFast_invokestatic_step (stepStatic_growBufPush_bool hlocs.h14)]
  rw [show f + 42 = (f + 34) + 8 from by omega]; chunk 8
  rw [show f + 34 = (f + 26) + 8 from by omega]; chunk 8
  rw [show f + 26 = (f + 18) + 8 from by omega]; chunk 8
  rw [show f + 18 = (f + 10) + 8 from by omega]; chunk 8
  rw [show f + 10 = (f + 2) + 8 from by omega]; chunk 8
  rw [show f + 2 = (f + 1) + 1 from by omega]; chunk 1
  rw [runJvmResFast_goto]
  have h10 : ((1 : UInt32) != 0) = true := rfl
  rw [h10]

private theorem step_deserLoop_leaf_cont {locs : Nat → JvmVal}
    {lines : Array String} {numLines i : UInt32} {bytesAddr : Nat}
    {limit nextP col x y : UInt32} {leaf : UInt64}
    {nodes : Algorithm.GrowBuf Algorithm.MacroCell} {leaves : Algorithm.GrowBuf UInt64}
    {isLeaf : Algorithm.GrowBuf Bool} {warns : Algorithm.GrowBuf Algorithm.MacrocellWarning}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hl0 : locs 0 = .strArr lines) (hl1 : locs 1 = .i32 numLines) (hl2 : locs 2 = .i32 i)
    (hl4 : locs 4 = .heapRef bytesAddr) (hl5 : locs 5 = .i32 limit)
    (hl7 : locs 7 = .i32 col) (hl8 : locs 8 = .i32 x) (hl9 : locs 9 = .i32 y)
    (hl12 : mcNodes? (locs 12) = some nodes) (hl13 : mcLeaves? (locs 13) = some leaves)
    (hl14 : mcIsLeaf? (locs 14) = some isLeaf)
    (hl18 : locs 18 = .i32 nextP) (hl19 : locs 19 = .i64 leaf)
    (hl21 : mcWarns? (locs 21) = some warns) :
    ∃ locs',
      locs' 15 = locs 21 ∧
      DeserLoopLocs locs' lines numLines i true bytesAddr limit nextP (col + 1) (x + 1) y leaf
        nodes leaves isLeaf warns ∧
      ∀ f, runJvmResFast (f + 59) f_Algorithm_deserializeMacrocell_loop_prog 1349
          (f_Algorithm_deserializeMacrocell_loop_prog.drop 1349) ⟨1349, [], locs, jh, hp⟩ =
        runJvmResFast f f_Algorithm_deserializeMacrocell_loop_prog 6
          (f_Algorithm_deserializeMacrocell_loop_prog.drop 6) ⟨6, [], locs', jh, hp⟩ := by
  let locs' :=
    setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
      (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
        (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal locs
          22 (locs 0)) 23 (locs 1)) 24 (locs 2)) 25 (locs 4)) 26 (locs 5))
          27 (.i32 (col + 1))) 28 (.i32 (x + 1))) 29 (locs 9))
          30 (locs 12)) 31 (locs 13)) 32 (locs 14))
          0 (locs 0)) 1 (locs 1)) 2 (locs 2)) 3 (.i32 1)) 4 (locs 4)) 5 (locs 5))
          6 (locs 18)) 7 (.i32 (col + 1))) 8 (.i32 (x + 1))) 9 (locs 9)) 10 (locs 19))
          12 (locs 12)) 13 (locs 13)) 14 (locs 14)) 15 (locs 21)
  refine ⟨locs', rfl,
    ⟨hl0, hl1, hl2, rfl, hl4, hl5, hl18, rfl, rfl, hl9, hl19, hl12, hl13, hl14, hl21⟩, ?_⟩
  intro f
  rw [deserLoop_drop_1349]
  rw [show f + 59 = (f + 53) + 6 from by omega]; chunk 6
  rw [show f + 53 = (f + 48) + 5 from by omega]; chunk 5; rw [hl7]
  rw [show f + 48 = (f + 46) + 2 from by omega]; chunk 2
  rw [show f + 46 = (f + 45) + 1 from by omega, runJvmResFast_invokestatic_step stepStatic_uintCtor5a]
  rw [show f + 45 = (f + 43) + 2 from by omega]; chunk 2; rw [hl8]
  rw [show f + 43 = (f + 41) + 2 from by omega]; chunk 2
  rw [show f + 41 = (f + 40) + 1 from by omega, runJvmResFast_invokestatic_step stepStatic_uintCtor5a]
  rw [show f + 40 = (f + 32) + 8 from by omega]; chunk 8
  rw [show f + 32 = (f + 24) + 8 from by omega]; chunk 8
  rw [show f + 24 = (f + 16) + 8 from by omega]; chunk 8
  rw [show f + 16 = (f + 8) + 8 from by omega]; chunk 8
  rw [show f + 8 = (f + 1) + 7 from by omega]; chunk 7
  rw [runJvmResFast_goto]

private def leafUpdateFuel (cp x y : UInt32) : Nat :=
  if cp == 42 then
    if x < 8 then
      if y < 8 then 21 else 16
    else 12
  else 8

private theorem step_deserLoop_leaf_update {locs : Nat → JvmVal}
    {cp x y : UInt32} {leaf : UInt64} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hl8 : locs 8 = .i32 x) (hl9 : locs 9 = .i32 y)
    (hl10 : locs 10 = .i64 leaf) (hl17 : locs 17 = .i32 cp) :
    let leaf' := if cp == 42 && x < 8 && y < 8 then Algorithm.leafWithCell leaf x y true else leaf
    ∃ locs',
      locs' 22 = .i64 leaf' ∧
      (∀ s, s < 19 → locs' s = locs s) ∧
      ∀ f, runJvmResFast (f + leafUpdateFuel cp x y) f_Algorithm_deserializeMacrocell_loop_prog 1219
          (.lconst 0 :: .lstore 22 :: .iload 17 :: .iconst 42 :: .if_icmpeq 1227 ::
           .lload 10 :: .lstore 22 :: .goto 1249 :: f_Algorithm_deserializeMacrocell_loop_prog.drop 1227)
          ⟨1219, [], locs, jh, hp⟩ =
        runJvmResFast f f_Algorithm_deserializeMacrocell_loop_prog 1249
          (f_Algorithm_deserializeMacrocell_loop_prog.drop 1249) ⟨1249, [], locs', jh, hp⟩ := by
  intro leaf'
  by_cases h42 : cp = 42
  · have h42b : (cp == 42) = true := beq_iff_eq.mpr h42
    by_cases hx : x < 8
    · by_cases hy : y < 8
      · have hfn : leafUpdateFuel cp x y = 21 := by simp [leafUpdateFuel, h42b, hx, hy]
        have hlf : leaf' = Algorithm.leafWithCell leaf x y true := by
          dsimp only [leaf']; rw [h42b, decide_eq_true hx, decide_eq_true hy]; rfl
        let locs' := setLocal (setLocal (setLocal locs 22 (.i64 0)) 24 (.i64 leaf')) 22 (.i64 leaf')
        refine ⟨locs', rfl, ?_, fun f => ?_⟩
        · intro s hs
          dsimp only [locs']
          rw [setLocal_ne_eq (i := 22) (j := s) (decide_eq_false (by omega)),
            setLocal_ne_eq (i := 24) (j := s) (decide_eq_false (by omega)),
            setLocal_ne_eq (i := 22) (j := s) (decide_eq_false (by omega))]
        · rw [hfn]
          step1_ex; step1_ex; step1_ex; rw [hl17]; step1_ex
          rw [show f + 17 = (f + 16) + 1 from by omega]
          rw [runJvmResFast_if_icmpeq_branch h42, deserLoop_drop_1227]
          step1_ex; rw [hl8]; step1_ex
          rw [show f + 14 = (f + 13) + 1 from by omega]
          rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned]
          rw [show f + 13 = (f + 12) + 1 from by omega]
          rw [runJvmResFast_iflt_branch (by rw [compareUnsigned_slt_zero]; exact decide_eq_true hx),
            deserLoop_drop_1234]
          step1_ex; rw [hl9]; step1_ex
          rw [show f + 10 = (f + 9) + 1 from by omega]
          rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned]
          rw [show f + 9 = (f + 8) + 1 from by omega]
          rw [runJvmResFast_iflt_branch (by rw [compareUnsigned_slt_zero]; exact decide_eq_true hy),
            deserLoop_drop_1241]
          step1_ex; rw [hl10]
          step1_ex; rw [hl8]
          step1_ex; rw [hl9]
          step1_ex
          rw [show f + 4 = (f + 3) + 1 from by omega]
          rw [runJvmResFast_invokestatic_step stepStatic_mcLeafWithCell_heap]
          step1_ex; step1_ex; step1_ex
          dsimp only [locs']; rw [hlf]; rfl
      · have hfn : leafUpdateFuel cp x y = 16 := by simp [leafUpdateFuel, h42b, hx, hy]
        have hlf : leaf' = leaf := by
          dsimp only [leaf']; rw [h42b, decide_eq_true hx, decide_eq_false hy]; rfl
        let locs' := setLocal (setLocal locs 22 (.i64 0)) 22 (.i64 leaf)
        refine ⟨locs', by rw [hlf]; rfl, ?_, fun f => ?_⟩
        · intro s hs
          dsimp only [locs']
          rw [setLocal_ne_eq (i := 22) (j := s) (decide_eq_false (by omega)),
            setLocal_ne_eq (i := 22) (j := s) (decide_eq_false (by omega))]
        · rw [hfn]
          step1_ex; step1_ex; step1_ex; rw [hl17]; step1_ex
          rw [show f + 12 = (f + 11) + 1 from by omega]
          rw [runJvmResFast_if_icmpeq_branch h42, deserLoop_drop_1227]
          step1_ex; rw [hl8]; step1_ex
          rw [show f + 9 = (f + 8) + 1 from by omega]
          rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned]
          rw [show f + 8 = (f + 7) + 1 from by omega]
          rw [runJvmResFast_iflt_branch (by rw [compareUnsigned_slt_zero]; exact decide_eq_true hx),
            deserLoop_drop_1234]
          step1_ex; rw [hl9]; step1_ex
          rw [show f + 5 = (f + 4) + 1 from by omega]
          rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned]
          rw [show f + 4 = (f + 3) + 1 from by omega]
          rw [runJvmResFast_iflt_fallthrough (by rw [compareUnsigned_slt_zero]; exact decide_eq_false hy)]
          step1_ex; rw [hl10]; step1_ex
          rw [runJvmResFast_goto]
    · have hfn : leafUpdateFuel cp x y = 12 := by simp [leafUpdateFuel, h42b, hx]
      have hlf : leaf' = leaf := by
        dsimp only [leaf']; rw [h42b, decide_eq_false hx]; rfl
      let locs' := setLocal (setLocal locs 22 (.i64 0)) 22 (.i64 leaf)
      refine ⟨locs', by rw [hlf]; rfl, ?_, fun f => ?_⟩
      · intro s hs
        dsimp only [locs']
        rw [setLocal_ne_eq (i := 22) (j := s) (decide_eq_false (by omega)),
          setLocal_ne_eq (i := 22) (j := s) (decide_eq_false (by omega))]
      · rw [hfn]
        step1_ex; step1_ex; step1_ex; rw [hl17]; step1_ex
        rw [show f + 8 = (f + 7) + 1 from by omega]
        rw [runJvmResFast_if_icmpeq_branch h42, deserLoop_drop_1227]
        step1_ex; rw [hl8]; step1_ex
        rw [show f + 5 = (f + 4) + 1 from by omega]
        rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned]
        rw [show f + 4 = (f + 3) + 1 from by omega]
        rw [runJvmResFast_iflt_fallthrough (by rw [compareUnsigned_slt_zero]; exact decide_eq_false hx)]
        step1_ex; rw [hl10]; step1_ex
        rw [runJvmResFast_goto]
  · have h42b : (cp == 42) = false := beq_false_of_ne h42
    have hfn : leafUpdateFuel cp x y = 8 := by simp [leafUpdateFuel, h42b]
    have hlf : leaf' = leaf := by dsimp only [leaf']; rw [h42b]; rfl
    let locs' := setLocal (setLocal locs 22 (.i64 0)) 22 (.i64 leaf)
    refine ⟨locs', by rw [hlf]; rfl, ?_, fun f => ?_⟩
    · intro s hs
      dsimp only [locs']
      rw [setLocal_ne_eq (i := 22) (j := s) (decide_eq_false (by omega)),
        setLocal_ne_eq (i := 22) (j := s) (decide_eq_false (by omega))]
    · rw [hfn]
      step1_ex; step1_ex; step1_ex; rw [hl17]; step1_ex
      rw [show f + 4 = (f + 3) + 1 from by omega]
      rw [runJvmResFast_if_icmpeq_fallthrough (decide_eq_false h42)]
      step1_ex; rw [hl10]; step1_ex
      rw [runJvmResFast_goto]

private def leafWarnFuel (cp : UInt32) : Nat :=
  if cp == 46 then 8 else if cp == 42 then 11 else 29

private theorem step_deserLoop_leaf_warn {locs : Nat → JvmVal}
    {lines : Array String} {i col cp : UInt32} {leaf' : UInt64}
    {warns : Algorithm.GrowBuf Algorithm.MacrocellWarning}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hl0 : locs 0 = .strArr lines) (hl2 : locs 2 = .i32 i) (hl7 : locs 7 = .i32 col)
    (hl15 : mcWarns? (locs 15) = some warns) (hl17 : locs 17 = .i32 cp) (hl22 : locs 22 = .i64 leaf')
    (hiSz : i.toNat < lines.size) (hibv : i.toBitVec.slt 0#32 = false) :
    let warns' := if cp != 46 && cp != 42 then warns.push (.unexpectedInput i col lines[i.toNat]) else warns
    ∃ (locs' : Nat → JvmVal) (jh' : Jvm.JvmHeap AlgExt),
      (∀ a o, jh.get? a = some o → jh'.get? a = some o) ∧
      jh'.statics = jh.statics ∧
      (locs 15 = .ext (.mcWarnGrowBuf warns) → locs' 21 = .ext (.mcWarnGrowBuf warns')) ∧
      locs' 19 = .i64 leaf' ∧
      mcWarns? (locs' 21) = some warns' ∧
      (∀ s, s < 19 → locs' s = locs s) ∧
      ∀ f, runJvmResFast (f + leafWarnFuel cp) f_Algorithm_deserializeMacrocell_loop_prog 1249
          (f_Algorithm_deserializeMacrocell_loop_prog.drop 1249) ⟨1249, [], locs, jh, hp⟩ =
        runJvmResFast f f_Algorithm_deserializeMacrocell_loop_prog 1349
          (f_Algorithm_deserializeMacrocell_loop_prog.drop 1349) ⟨1349, [], locs', jh', hp⟩ := by
  intro warns'
  by_cases h46 : cp = 46
  · have h46b : (cp == 46) = true := beq_iff_eq.mpr h46
    have hfn : leafWarnFuel cp = 8 := by simp [leafWarnFuel, h46b]
    have hwn : warns' = warns := by simp [warns', h46]
    let locs' := setLocal (setLocal locs 19 (.i64 leaf')) 21 (locs 15)
    refine ⟨locs', jh, fun _ _ ha => ha, rfl,
      fun h => by dsimp only [locs']; change locs 15 = _; rw [h, hwn],
      rfl,
      by dsimp only [locs']; change mcWarns? (locs 15) = _; rw [hwn]; exact hl15,
      fun s hs => by
        dsimp only [locs']
        rw [setLocal_ne_eq (i := 21) (j := s) (decide_eq_false (by omega)),
          setLocal_ne_eq (i := 19) (j := s) (decide_eq_false (by omega))], ?_⟩
    intro f
    rw [hfn, deserLoop_drop_1249]
    step1_ex; rw [hl17]; step1_ex
    rw [show f + 6 = (f + 5) + 1 from by omega]
    rw [runJvmResFast_if_icmpeq_branch h46, deserLoop_drop_1283]
    step1_ex; rw [hl22]; step1_ex
    step1_ex; step1_ex
    rw [runJvmResFast_goto]
  · have h46b : (cp == 46) = false := beq_false_of_ne h46
    by_cases h42 : cp = 42
    · have h42b : (cp == 42) = true := beq_iff_eq.mpr h42
      have hfn : leafWarnFuel cp = 11 := by simp [leafWarnFuel, h46b, h42b]
      have hwn : warns' = warns := by simp [warns', h42]
      let locs' := setLocal (setLocal locs 19 (.i64 leaf')) 21 (locs 15)
      refine ⟨locs', jh, fun _ _ ha => ha, rfl,
        fun h => by dsimp only [locs']; change locs 15 = _; rw [h, hwn],
        rfl,
        by dsimp only [locs']; change mcWarns? (locs 15) = _; rw [hwn]; exact hl15,
        fun s hs => by
          dsimp only [locs']
          rw [setLocal_ne_eq (i := 21) (j := s) (decide_eq_false (by omega)),
            setLocal_ne_eq (i := 19) (j := s) (decide_eq_false (by omega))], ?_⟩
      intro f
      rw [hfn, deserLoop_drop_1249]
      step1_ex; rw [hl17]; step1_ex
      rw [show f + 9 = (f + 8) + 1 from by omega]
      rw [runJvmResFast_if_icmpeq_fallthrough (decide_eq_false h46)]
      step1_ex; rw [hl17]; step1_ex
      rw [show f + 6 = (f + 5) + 1 from by omega]
      rw [runJvmResFast_if_icmpeq_branch h42, deserLoop_drop_1278]
      step1_ex; rw [hl22]; step1_ex
      step1_ex; step1_ex
      rw [runJvmResFast_goto]
    · have h42b : (cp == 42) = false := beq_false_of_ne h42
      have hfn : leafWarnFuel cp = 29 := by simp [leafWarnFuel, h46b, h42b]
      have hwn : warns' = warns.push (.unexpectedInput i col lines[i.toNat]) := by
        simp [warns', h46, h42]
      let line := lines[i.toNat]
      let wAddr := jh.objects.size
      let jh1 := (jh.alloc (Jvm.HeapObj.instance "com/alexvanyo/composelife/model/MacrocellWarning$UnexpectedInput"
        [("lineIndex", .i32 i), ("columnIndex", .i32 col), ("input", .str line)])).2
      have hext1 : ∀ a o, jh.get? a = some o → jh1.get? a = some o :=
        fun _ _ ha => jvmHeap_get?_alloc_mono ha
      have hgetW : jh1.get? wAddr =
          some (Jvm.HeapObj.instance "com/alexvanyo/composelife/model/MacrocellWarning$UnexpectedInput"
            [("lineIndex", .i32 i), ("columnIndex", .i32 col), ("input", .str line)]) :=
        jvmHeap_get?_alloc_self _ _
      have hrle : decodeRLEWarning jh1 (.heapRef wAddr) = none := by
        dsimp only [decodeRLEWarning]; rw [hgetW]; rfl
      have hmcw : decodeMacrocellWarning jh1 (.heapRef wAddr) =
          some (.unexpectedInput i col line) := by
        dsimp only [decodeMacrocellWarning]; rw [hgetW]; rfl
      let wv' := JvmVal.ext (AlgExt.mcWarnGrowBuf (warns.push (.unexpectedInput i col line)))
      let locs' := setLocal (setLocal (setLocal (setLocal locs 24 (.str line)) 25 wv')
        19 (.i64 leaf')) 21 wv'
      refine ⟨locs', jh1, hext1, rfl,
        fun _ => by rw [hwn]; rfl,
        rfl,
        by rw [hwn]; rfl,
        fun s hs => by
          dsimp only [locs']
          rw [setLocal_ne_eq (i := 21) (j := s) (decide_eq_false (by omega)),
            setLocal_ne_eq (i := 19) (j := s) (decide_eq_false (by omega)),
            setLocal_ne_eq (i := 25) (j := s) (decide_eq_false (by omega)),
            setLocal_ne_eq (i := 24) (j := s) (decide_eq_false (by omega))], ?_⟩
      intro f
      rw [hfn, deserLoop_drop_1249]
      have hwPush := stepStatic_growBufPush_mcWarn (pc := 1271) (wv := locs 15)
        (locs := setLocal locs 24 (.str line)) (jh := jh1) (hp := hp) (rest := [])
        hl15 hrle hmcw
      step1_ex; rw [hl17]; step1_ex
      rw [show f + 27 = (f + 26) + 1 from by omega]
      rw [runJvmResFast_if_icmpeq_fallthrough (decide_eq_false h46)]
      step1_ex; rw [hl17]; step1_ex
      rw [show f + 24 = (f + 23) + 1 from by omega]
      rw [runJvmResFast_if_icmpeq_fallthrough (decide_eq_false h42)]
      step1_ex; rw [hl0]; step1_ex; rw [hl2]
      rw [show f + 21 = (f + 20) + 1 from by omega]
      rw [runJvmResFast_aaload_strArr hibv hiSz]
      step1_ex
      step1_ex; step1_ex; step1_ex
      step1_ex; rw [hl2]
      step1_ex; rw [hl7]
      step1_ex
      step1_ex
      rw [show f + 12 = (f + 11) + 1 from by omega]
      rw [runJvmResFast_checkNotNull_nonnull (by intro h; cases h)]
      step1_ex; step1_ex; step1_ex
      step1_ex
      dsimp only [wAddr, jh1, line, Jvm.JvmHeap.alloc] at hwPush
      rw [show f + 7 = (f + 6) + 1 from by omega]
      rw [runJvmResFast_invokestatic_step hwPush]
      step1_ex
      step1_ex; rw [hl22]; step1_ex
      step1_ex; step1_ex
      rw [runJvmResFast_goto]
      dsimp only [locs', wv', jh1, line]
      rfl

private theorem step_deserLoop_leaf_decode {f : Nat} {locs : Nat → JvmVal}
    {lines : Array String} {numLines i : UInt32}
    {bytesAddr : Nat} {bytesData : Array UInt8} {limit p col x y : UInt32} {leaf : UInt64}
    {nodes : Algorithm.GrowBuf Algorithm.MacroCell} {leaves : Algorithm.GrowBuf UInt64}
    {isLeaf : Algorithm.GrowBuf Bool} {warns : Algorithm.GrowBuf Algorithm.MacrocellWarning}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {r : UInt32 × UInt32}
    (hlocs : DeserLoopLocs locs lines numLines i true bytesAddr limit p col x y leaf
      nodes leaves isLeaf warns)
    (hgetBytes : jh.get? bytesAddr = some (.byteArray bytesData))
    (hpLt : p < limit)
    (hr : Algorithm.decodeCharAt ⟨bytesData⟩ p limit = r) :
    let locs1 := setLocal (setLocal (setLocal (setLocal (setLocal locs 16
      (.pair (.boxedUInt r.1) (.boxedUInt r.2))) 17 (.i32 r.1)) 18 (.i32 r.2)) 19 (.i64 0)) 21 .null
    let tgt := if r.1 == 36 then 1288 else 1219
    runJvmResFast (f + 28) f_Algorithm_deserializeMacrocell_loop_prog 85
        (f_Algorithm_deserializeMacrocell_loop_prog.drop 85) ⟨85, [], locs, jh, hp⟩ =
      runJvmResFast f f_Algorithm_deserializeMacrocell_loop_prog tgt
        (f_Algorithm_deserializeMacrocell_loop_prog.drop tgt) ⟨tgt, [], locs1, jh, hp⟩ := by
  intro locs1 tgt
  rw [deserLoop_drop_85]
  step1; rw [hlocs.h3]
  rw [show f + 27 = (f + 26) + 1 from by omega]
  rw [runJvmResFast_ifne_branch (by decide)]
  rw [deserLoop_drop_1127]
  step1; rw [hlocs.h6]; step1; rw [hlocs.h5]
  rw [show f + 24 = (f + 23) + 1 from by omega]
  rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned]
  rw [show f + 23 = (f + 22) + 1 from by omega]
  rw [runJvmResFast_iflt_branch (by rw [compareUnsigned_slt_zero]; exact decide_eq_true hpLt)]
  rw [deserLoop_drop_1197]
  step1; rw [hlocs.h4]
  step1; rw [hlocs.h6]
  step1; rw [hlocs.h5]
  rw [show f + 19 = (f + 18) + 1 from by omega]
  rw [runJvmResFast_invokestatic_step (stepStatic_decodeCharAt_heap
    (Or.inr (Or.inr (Or.inl rfl))) hgetBytes)]
  rw [hr]
  step1; step1; step1; step1; step1; step1
  step1; step1; step1; step1; step1
  step1; step1; step1; step1
  step1
  rw [show f + 2 = (f + 1) + 1 from by omega]
  step1
  by_cases h36 : r.1 = 36
  · have h36b : (r.1 == 36) = true := beq_iff_eq.mpr h36
    have htgt : tgt = 1288 := by dsimp only [tgt]; rw [h36b]; rfl
    rw [htgt]
    dsimp only [locs1]
    exact runJvmResFast_if_icmpeq_branch h36
  · have h36b : (r.1 == 36) = false := beq_false_of_ne h36
    have htgt : tgt = 1219 := by dsimp only [tgt]; rw [h36b]; rfl
    rw [htgt]
    dsimp only [locs1]
    rw [runJvmResFast_if_icmpeq_fallthrough (decide_eq_false h36)]
    simp only [Nat.reduceAdd]
    rw [deserLoop_drop_1219]

private theorem step_deserLoop_leaf_dollar_tail {locs : Nat → JvmVal}
    {lines : Array String} {numLines i : UInt32} {bytesAddr : Nat}
    {limit nextP col y : UInt32} {leaf : UInt64}
    {nodes : Algorithm.GrowBuf Algorithm.MacroCell} {leaves : Algorithm.GrowBuf UInt64}
    {isLeaf : Algorithm.GrowBuf Bool} {warns : Algorithm.GrowBuf Algorithm.MacrocellWarning}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hl0 : locs 0 = .strArr lines) (hl1 : locs 1 = .i32 numLines) (hl2 : locs 2 = .i32 i)
    (hl4 : locs 4 = .heapRef bytesAddr) (hl5 : locs 5 = .i32 limit)
    (hl7 : locs 7 = .i32 col) (hl9 : locs 9 = .i32 y) (hl10 : locs 10 = .i64 leaf)
    (hl12 : mcNodes? (locs 12) = some nodes) (hl13 : mcLeaves? (locs 13) = some leaves)
    (hl14 : mcIsLeaf? (locs 14) = some isLeaf) (hl15 : mcWarns? (locs 15) = some warns)
    (hl18 : locs 18 = .i32 nextP) :
    ∃ locs',
      locs' 15 = locs 15 ∧
      DeserLoopLocs locs' lines numLines i true bytesAddr limit nextP (col + 1) 0 (y + 1) leaf
        nodes leaves isLeaf warns ∧
      ∀ f, runJvmResFast (f + 61) f_Algorithm_deserializeMacrocell_loop_prog 1288
          (f_Algorithm_deserializeMacrocell_loop_prog.drop 1288) ⟨1288, [], locs, jh, hp⟩ =
        runJvmResFast f f_Algorithm_deserializeMacrocell_loop_prog 6
          (f_Algorithm_deserializeMacrocell_loop_prog.drop 6) ⟨6, [], locs', jh, hp⟩ := by
  let locs' :=
    setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
      (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
        (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal locs
          22 (locs 0)) 23 (locs 1)) 24 (locs 2)) 25 (locs 4)) 26 (locs 5))
          27 (.i32 (col + 1))) 28 (.i32 (y + 1))) 29 (locs 10))
          31 (locs 12)) 32 (locs 13)) 33 (locs 14)) 34 (locs 15))
          0 (locs 0)) 1 (locs 1)) 2 (locs 2)) 3 (.i32 1)) 4 (locs 4)) 5 (locs 5))
          6 (locs 18)) 7 (.i32 (col + 1))) 8 (.i32 0)) 9 (.i32 (y + 1))) 10 (locs 10))
          12 (locs 12)) 13 (locs 13)) 14 (locs 14)) 15 (locs 15)
  refine ⟨locs', rfl,
    ⟨hl0, hl1, hl2, rfl, hl4, hl5, hl18, rfl, rfl, rfl, hl10, hl12, hl13, hl14, hl15⟩, ?_⟩
  intro f
  rw [deserLoop_drop_1288]
  rw [show f + 61 = (f + 55) + 6 from by omega]; chunk 6
  rw [show f + 55 = (f + 50) + 5 from by omega]; chunk 5; rw [hl7]
  rw [show f + 50 = (f + 48) + 2 from by omega]; chunk 2
  rw [show f + 48 = (f + 47) + 1 from by omega, runJvmResFast_invokestatic_step stepStatic_uintCtor5a]
  rw [show f + 47 = (f + 45) + 2 from by omega]; chunk 2; rw [hl9]
  rw [show f + 45 = (f + 43) + 2 from by omega]; chunk 2
  rw [show f + 43 = (f + 42) + 1 from by omega, runJvmResFast_invokestatic_step stepStatic_uintCtor5a]
  rw [show f + 42 = (f + 34) + 8 from by omega]; chunk 8
  rw [show f + 34 = (f + 26) + 8 from by omega]; chunk 8
  rw [show f + 26 = (f + 18) + 8 from by omega]; chunk 8
  rw [show f + 18 = (f + 10) + 8 from by omega]; chunk 8
  rw [show f + 10 = (f + 2) + 8 from by omega]; chunk 8
  rw [show f + 2 = (f + 1) + 1 from by omega]; chunk 1
  rw [runJvmResFast_goto]

theorem step_deserLoop_leaf_char {locs : Nat → JvmVal}
    {lines : Array String} {numLines i : UInt32}
    {bytesAddr : Nat} {bytesData : Array UInt8} {limit p col x y : UInt32} {leaf : UInt64}
    {nodes : Algorithm.GrowBuf Algorithm.MacroCell} {leaves : Algorithm.GrowBuf UInt64}
    {isLeaf : Algorithm.GrowBuf Bool} {warns : Algorithm.GrowBuf Algorithm.MacrocellWarning}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hlocs : DeserLoopLocs locs lines numLines i true bytesAddr limit p col x y leaf
      nodes leaves isLeaf warns)
    (hgetBytes : jh.get? bytesAddr = some (.byteArray bytesData))
    (hpLt : p < limit)
    (hiSz : i.toNat < lines.size) (hibv : i.toBitVec.slt 0#32 = false) :
    let r := Algorithm.decodeCharAt ⟨bytesData⟩ p limit
    let cp := r.1
    if cp == 36 then
      ∃ locs',
        locs' 15 = locs 15 ∧
        DeserLoopLocs locs' lines numLines i true bytesAddr limit r.2 (col + 1) 0 (y + 1) leaf
          nodes leaves isLeaf warns ∧
        ∀ f, runJvmResFast (f + 89) f_Algorithm_deserializeMacrocell_loop_prog 85
            (f_Algorithm_deserializeMacrocell_loop_prog.drop 85) ⟨85, [], locs, jh, hp⟩ =
          runJvmResFast f f_Algorithm_deserializeMacrocell_loop_prog 6
            (f_Algorithm_deserializeMacrocell_loop_prog.drop 6) ⟨6, [], locs', jh, hp⟩
    else
      let leaf' := if cp == 42 && x < 8 && y < 8 then Algorithm.leafWithCell leaf x y true else leaf
      let warns' := if cp != 46 && cp != 42 then warns.push (.unexpectedInput i col lines[i.toNat]) else warns
      ∃ (k : Nat) (locs' : Nat → JvmVal) (jh' : Jvm.JvmHeap AlgExt),
        (∀ a o, jh.get? a = some o → jh'.get? a = some o) ∧
        jh'.statics = jh.statics ∧
        (locs 15 = .ext (.mcWarnGrowBuf warns) → locs' 15 = .ext (.mcWarnGrowBuf warns')) ∧
        DeserLoopLocs locs' lines numLines i true bytesAddr limit r.2 (col + 1) (x + 1) y leaf'
          nodes leaves isLeaf warns' ∧
        ∀ f, runJvmResFast (f + k) f_Algorithm_deserializeMacrocell_loop_prog 85
            (f_Algorithm_deserializeMacrocell_loop_prog.drop 85) ⟨85, [], locs, jh, hp⟩ =
          runJvmResFast f f_Algorithm_deserializeMacrocell_loop_prog 6
            (f_Algorithm_deserializeMacrocell_loop_prog.drop 6) ⟨6, [], locs', jh', hp⟩ := by
  intro r cp
  let locsPre := setLocal (setLocal (setLocal (setLocal (setLocal locs 16
    (.pair (.boxedUInt r.1) (.boxedUInt r.2))) 17 (.i32 r.1)) 18 (.i32 r.2)) 19 (.i64 0)) 21 .null
  have hPre0 : locsPre 0 = .strArr lines := by simpa [locsPre, setLocal] using hlocs.h0
  have hPre1 : locsPre 1 = .i32 numLines := by simpa [locsPre, setLocal] using hlocs.h1
  have hPre2 : locsPre 2 = .i32 i := by simpa [locsPre, setLocal] using hlocs.h2
  have hPre4 : locsPre 4 = .heapRef bytesAddr := by simpa [locsPre, setLocal] using hlocs.h4
  have hPre5 : locsPre 5 = .i32 limit := by simpa [locsPre, setLocal] using hlocs.h5
  have hPre7 : locsPre 7 = .i32 col := by simpa [locsPre, setLocal] using hlocs.h7
  have hPre8 : locsPre 8 = .i32 x := by simpa [locsPre, setLocal] using hlocs.h8
  have hPre9 : locsPre 9 = .i32 y := by simpa [locsPre, setLocal] using hlocs.h9
  have hPre10 : locsPre 10 = .i64 leaf := by simpa [locsPre, setLocal] using hlocs.h10
  have hPre12 : mcNodes? (locsPre 12) = some nodes := by simpa [locsPre, setLocal] using hlocs.h12
  have hPre13 : mcLeaves? (locsPre 13) = some leaves := by simpa [locsPre, setLocal] using hlocs.h13
  have hPre14 : mcIsLeaf? (locsPre 14) = some isLeaf := by simpa [locsPre, setLocal] using hlocs.h14
  have hPre15 : mcWarns? (locsPre 15) = some warns := by simpa [locsPre, setLocal] using hlocs.h15
  have hPre17 : locsPre 17 = .i32 cp := rfl
  have hPre18 : locsPre 18 = .i32 r.2 := rfl
  by_cases h36 : cp = 36
  · have h36b : (cp == 36) = true := beq_iff_eq.mpr h36
    simp only [h36b, ↓reduceIte]
    rcases step_deserLoop_leaf_dollar_tail hPre0 hPre1 hPre2 hPre4 hPre5
        hPre7 hPre9 hPre10 hPre12 hPre13 hPre14 hPre15 hPre18 with ⟨locs', h15', hdl', hTail⟩
    refine ⟨locs', h15', hdl', ?_⟩
    intro f
    have hDec := step_deserLoop_leaf_decode (f := f + 61) (hp := hp) hlocs hgetBytes hpLt rfl
    have htgt : (if r.1 == 36 then 1288 else 1219) = 1288 := by
      dsimp only [cp] at h36b; rw [h36b]; rfl
    rw [htgt] at hDec
    rw [show f + 89 = (f + 61) + 28 from by omega, hDec, hTail]
  · have h36b : (cp == 36) = false := beq_false_of_ne h36
    simp only [h36b]
    let kw := leafWarnFuel cp
    let ku := leafUpdateFuel cp x y
    rcases step_deserLoop_leaf_update (jh := jh) (hp := hp)
        hPre8 hPre9 hPre10 hPre17 with ⟨locsU, hU22, hUpres, hUpd⟩
    rcases step_deserLoop_leaf_warn (hp := hp)
        (by rw [hUpres 0 (by omega)]; exact hPre0)
        (by rw [hUpres 2 (by omega)]; exact hPre2)
        (by rw [hUpres 7 (by omega)]; exact hPre7)
        (by rw [hUpres 15 (by omega)]; exact hPre15)
        (by rw [hUpres 17 (by omega)]; exact hPre17)
        hU22 hiSz hibv with ⟨locsW, jh', hext, hstat', hw15, hW19, hW21, hWpres, hWarn⟩
    rcases step_deserLoop_leaf_cont
        (by rw [hWpres 0 (by omega), hUpres 0 (by omega)]; exact hPre0)
        (by rw [hWpres 1 (by omega), hUpres 1 (by omega)]; exact hPre1)
        (by rw [hWpres 2 (by omega), hUpres 2 (by omega)]; exact hPre2)
        (by rw [hWpres 4 (by omega), hUpres 4 (by omega)]; exact hPre4)
        (by rw [hWpres 5 (by omega), hUpres 5 (by omega)]; exact hPre5)
        (by rw [hWpres 7 (by omega), hUpres 7 (by omega)]; exact hPre7)
        (by rw [hWpres 8 (by omega), hUpres 8 (by omega)]; exact hPre8)
        (by rw [hWpres 9 (by omega), hUpres 9 (by omega)]; exact hPre9)
        (by rw [hWpres 12 (by omega), hUpres 12 (by omega)]; exact hPre12)
        (by rw [hWpres 13 (by omega), hUpres 13 (by omega)]; exact hPre13)
        (by rw [hWpres 14 (by omega), hUpres 14 (by omega)]; exact hPre14)
        (by rw [hWpres 18 (by omega), hUpres 18 (by omega)]; exact hPre18)
        hW19 hW21 (jh := jh') (hp := hp) with ⟨locs', hc15, hdl', hCont⟩
    refine ⟨28 + ku + kw + 59, locs', jh', hext, hstat',
      fun h => hc15.trans (hw15 (by
        rw [hUpres 15 (by omega)]
        dsimp only [locsPre]
        rw [setLocal_ne_eq rfl, setLocal_ne_eq rfl, setLocal_ne_eq rfl,
          setLocal_ne_eq rfl, setLocal_ne_eq rfl]
        exact h)), hdl', ?_⟩
    intro f
    have hDec := step_deserLoop_leaf_decode
      (f := f + 59 + kw + ku) (hp := hp) hlocs hgetBytes hpLt rfl
    have htgt : (if r.1 == 36 then 1288 else 1219) = 1219 := by
      dsimp only [cp] at h36b; rw [h36b]; rfl
    rw [htgt] at hDec
    rw [show f + (28 + ku + kw + 59) = (f + 59 + kw + ku) + 28 from by omega, hDec, deserLoop_drop_1219]
    rw [show f + 59 + kw + ku = (f + 59 + kw) + ku from by omega, hUpd (f + 59 + kw)]
    rw [show f + 59 + kw = (f + 59) + kw from by omega, hWarn (f + 59)]
    exact hCont f

private theorem runJvmResFast_instanceof_boxedULong_long {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {rest : List JvmInstr} {pc0 : Nat} {v : UInt64} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.instanceof "java/lang/Long" :: rest)
        ⟨pc0, .boxedULong v :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .i32 0 :: stkRest, locs, jh, hp⟩ := by
  have hstep : Jvm.stepInstr algHooks (.instanceof "java/lang/Long")
      ⟨pc, .boxedULong v :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 0 :: stkRest, locs, jh, hp⟩) := rfl
  simp only [runJvmResFast]
  rw [Jvm.runJvmResFast_step_nonbranch algHooks (hbr := rfl) (hno := by simp)]
  simp only [hstep, ↓reduceIte]

private theorem step_deserLoop_err_tail {pc statusLoc arrLoc tmpLoc : Nat}
    {rest : List JvmInstr} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {warns : Algorithm.GrowBuf Algorithm.MacrocellWarning} {sAddr : Nat} {cls : String}
    (hdrop : f_Algorithm_deserializeMacrocell_loop_prog.drop pc =
      errTailInstrs statusLoc arrLoc tmpLoc ++ rest)
    (_hs15 : statusLoc ≠ 15) (has : arrLoc ≠ statusLoc)
    (_htp1 : tmpLoc ≠ statusLoc) (_htp2 : tmpLoc ≠ arrLoc)
    (hwarn : locs 15 = .ext (.mcWarnGrowBuf warns))
    (hs : locs statusLoc = .heapRef sAddr)
    (hget : (jh.get? sAddr).bind
        (fun o => match o with | .instance c _ => some c | _ => none) = some cls)
    (hsub : isSubtypeOf cls "com/alexvanyo/composelife/model/MacrocellStatus" = true)
    (hstat : jh.statics = []) :
    let pW := encodeGrowBufArray jh encodeMacrocellWarning warns
    let wVal := pW.1
    let jhW := pW.2
    let mrObj : Jvm.HeapObj AlgExt :=
      .instance "com/alexvanyo/composelife/model/MacrocellResult"
        [("status", .heapRef sAddr), ("warnings", wVal), ("macroCell", .ext (.mc Algorithm.emptyLevel4))]
    let jhFinal := (jhW.alloc mrObj).2
    let resVal := Jvm.JvmVal.heapRef jhW.objects.size
    ∃ locs',
      ∀ f, runJvmResFast (f + 17) f_Algorithm_deserializeMacrocell_loop_prog pc
          (f_Algorithm_deserializeMacrocell_loop_prog.drop pc) ⟨pc, [], locs, jh, hp⟩ =
        some (resVal, ⟨pc + 16, [resVal], locs', jhFinal, hp⟩) := by
  intro pW wVal jhW mrObj jhFinal resVal
  rcases Option.bind_eq_some_iff.mp hget with ⟨sObj, hsObj, hsCls⟩
  have henc := (rfl : encodeGrowBufArray jh encodeMacrocellWarning warns = (wVal, jhW))
  have hjhW_get : jhW.get? sAddr = some sObj := by
    have hg := encodeGrowBufArray_get?_ext jh encodeMacrocellWarning warns encodeMCWarn_get?_ext
      sAddr sObj hsObj
    rw [henc] at hg
    exact hg
  have hjhW_cls : (jhW.get? sAddr).bind
      (fun o => match o with | .instance c _ => some c | _ => none) = some cls := by
    rw [hjhW_get]; exact hsCls
  have hjhW_stat : jhW.getStatic? "MacroCellLeanKt" "EMPTY_LEVEL_4" = none := by
    dsimp only [Jvm.JvmHeap.getStatic?]
    have hs := encodeGrowBufArray_statics jh encodeMacrocellWarning warns encodeMCWarn_statics
    rw [henc] at hs
    rw [hs, hstat]
    rfl
  let locs' := setLocal (setLocal locs arrLoc wVal) tmpLoc (.i32 0)
  refine ⟨locs', fun f => ?_⟩
  rw [hdrop]
  dsimp only [errTailInstrs, List.cons_append, List.nil_append]
  step1
  rw [hwarn]
  rw [show f + 16 = (f + 15) + 1 from by omega]
  rw [runJvmResFast_invokestatic_step stepStatic_growBufToArray_mcWarn]
  dsimp only [wVal, jhW, pW] at *
  step1; step1; step1; step1
  (conv in (runJvmResFast _ _ _ _ _) =>
    dsimp only [Jvm.JvmState.pc, Jvm.JvmState.stack, Jvm.JvmState.locals,
      Jvm.JvmState.jvmHeap, Jvm.JvmState.heap]
    norm_jvm_locals
    try simp only [Nat.reduceAdd])
  rw [setLocal_ne_eq (i := arrLoc) (j := statusLoc) (decide_eq_false has.symm), hs]
  rw [show f + 11 = (f + 10) + 1 from by omega]
  rw [runJvmResFast_checkcast_instance (ty := "com/alexvanyo/composelife/model/MacrocellStatus")
    (by exact hjhW_cls) hsub]
  step1; step1; step1
  (conv in (runJvmResFast _ _ _ _ _) =>
    dsimp only [Jvm.JvmState.pc, Jvm.JvmState.stack, Jvm.JvmState.locals,
      Jvm.JvmState.jvmHeap, Jvm.JvmState.heap]
    norm_jvm_locals
    try simp only [Nat.reduceAdd])
  rw [setLocal_eq_val (decide_eq_true rfl)]
  rw [show f + 7 = (f + 6) + 1 from by omega]
  erw [runJvmResFast_invokestatic_step (stepStatic_getEMPTY_LEVEL_4 hjhW_stat)]
  step1; step1; step1
  (conv in (runJvmResFast _ _ _ _ _) =>
    dsimp only [Jvm.JvmState.pc, Jvm.JvmState.stack, Jvm.JvmState.locals,
      Jvm.JvmState.jvmHeap, Jvm.JvmState.heap]
    norm_jvm_locals
    try simp only [Nat.reduceAdd])
  rw [show f + 3 = (f + 2) + 1 from by omega]
  rw [runJvmResFast_checkNotNull_nonnull (by intro h; cases h)]
  step1
  (conv in (runJvmResFast _ _ _ _ _) =>
    dsimp only [Jvm.JvmState.pc, Jvm.JvmState.stack, Jvm.JvmState.locals,
      Jvm.JvmState.jvmHeap, Jvm.JvmState.heap]
    norm_jvm_locals
    try simp only [Nat.reduceAdd])
  rw [runJvmResFast_areturn]
  rfl

theorem step_deserLoop_exit_some {f : Nat} {locs : Nat → JvmVal}
    {_lines : Array String} {numLines i : UInt32}
    {nodesAddr nodesDataAddr : Nat} {nodes : Algorithm.GrowBuf Algorithm.MacroCell}
    {warns : Algorithm.GrowBuf Algorithm.MacrocellWarning}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hl1 : locs 1 = .i32 numLines) (hl2 : locs 2 = .i32 i)
    (hl12 : locs 12 = .heapRef nodesAddr)
    (hl15 : locs 15 = .ext (.mcWarnGrowBuf warns))
    (hnodes : jh.get? nodesAddr = some (.objArray "java/lang/Object"
      #[.boxedInt 0, .heapRef nodesDataAddr, .boxedInt nodes.size]))
    (hnodesData : jh.get? nodesDataAddr = some (.objArray "java/lang/Object"
      (nodes.data.map (fun m => JvmVal.ext (AlgExt.mc m)))))
    (hstat : jh.statics = [])
    (hge : ¬ i < numLines) :
    let mcRes := if nodes.size == 0 then Algorithm.emptyLevel4 else Algorithm.macroCellAt nodes.data (nodes.size - 1)
    let enc := encodeMacrocellResult jh ⟨.ok, warns.toArray, mcRes⟩
    ∃ pc' locs',
      runJvmResFast (f + (if nodes.size == 0 then 53 else 54)) f_Algorithm_deserializeMacrocell_loop_prog 6
          (f_Algorithm_deserializeMacrocell_loop_prog.drop 6) ⟨6, [], locs, jh, hp⟩ =
        some (enc.1, ⟨pc', [enc.1], locs', enc.2, hp⟩) := by
  intro mcRes enc
  have hltF : decide (i < numLines) = false := decide_eq_false hge
  have h6to10 : ∀ g,
      runJvmResFast (g + 4) f_Algorithm_deserializeMacrocell_loop_prog 6
          (f_Algorithm_deserializeMacrocell_loop_prog.drop 6) ⟨6, [], locs, jh, hp⟩ =
        runJvmResFast g f_Algorithm_deserializeMacrocell_loop_prog 10
          (f_Algorithm_deserializeMacrocell_loop_prog.drop 10) ⟨10, [], locs, jh, hp⟩ := by
    intro g
    rw [deserLoop_drop_6]
    step1; rw [hl2]; step1; rw [hl1]
    rw [show g + 2 = (g + 1) + 1 from by omega]
    rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned]
    exact runJvmResFast_iflt_fallthrough (by rw [compareUnsigned_slt_zero]; exact hltF)
  have h10to43 : ∀ g,
      runJvmResFast (g + 27) f_Algorithm_deserializeMacrocell_loop_prog 10
          (f_Algorithm_deserializeMacrocell_loop_prog.drop 10) ⟨10, [], locs, jh, hp⟩ =
        runJvmResFast g f_Algorithm_deserializeMacrocell_loop_prog 43
          (f_Algorithm_deserializeMacrocell_loop_prog.drop 43)
          ⟨43, [.i32 nodes.size],
            setLocal (setLocal (setLocal locs 16 (.heapRef nodesDataAddr))
              18 (.boxedInt nodes.size)) 19 (.i32 0),
            jh, hp⟩ := by
    intro g
    rw [deserLoop_drop_10]
    step1; rw [hl12]
    step1
    rw [show g + 25 = (g + 24) + 1 from by omega]
    rw [runJvmResFast_checkNotNull_nonnull (by intro h; cases h)]
    step1; rw [hl12]
    rw [show g + 23 = (g + 22) + 1 from by omega]
    rw [runJvmResFast_checkcast_objArray hnodes (Or.inl rfl)]
    rw [deserLoop_drop_15]
    step1
    rw [show g + 21 = (g + 20) + 1 from by omega]
    rw [runJvmResFast_aaload hnodes (by decide) (by simp)]
    simp only [arr3_get1]
    step1; step1
    rw [show g + 18 = (g + 17) + 1 from by omega]
    rw [runJvmResFast_checkNotNull_nonnull (by intro h; cases h)]
    rw [show g + 17 = (g + 16) + 1 from by omega]
    rw [runJvmResFast_checkcast_objArray hnodesData (Or.inl rfl)]
    step1; step1
    (conv in (runJvmResFast _ _ _ _ _) => norm_jvm_locals)
    rw [hl12]
    rw [show g + 14 = (g + 13) + 1 from by omega]
    rw [runJvmResFast_checkcast_objArray hnodes (Or.inl rfl)]
    step1
    rw [show g + 12 = (g + 11) + 1 from by omega]
    rw [runJvmResFast_aaload hnodes (by decide) (by simp)]
    simp only [arr3_get2]
    step1; step1; step1; step1
    rw [show g + 7 = (g + 6) + 1 from by omega]
    rw [runJvmResFast_instanceof_boxedInt_int]
    rw [show g + 6 = (g + 5) + 1 from by omega]
    rw [runJvmResFast_ifeq_fallthrough (by decide)]
    step1
    rw [show g + 4 = (g + 3) + 1 from by omega]
    rw [runJvmResFast_checkcast_boxedInt (Or.inr (Or.inl rfl))]
    step1
    rw [show g + 2 = (g + 1) + 1 from by omega]
    rw [runJvmResFast_invokestatic_step stepStatic_uintCtor5a]
    exact runJvmResFast_goto
  let locs43 := setLocal (setLocal (setLocal locs 16 (.heapRef nodesDataAddr))
    18 (.boxedInt nodes.size)) 19 (.i32 0)
  let pW := encodeGrowBufArray jh encodeMacrocellWarning warns
  have hstatW : pW.2.getStatic? "MacroCellLeanKt" "EMPTY_LEVEL_4" = none := by
    dsimp only [Jvm.JvmHeap.getStatic?, pW]
    rw [encodeGrowBufArray_statics jh encodeMacrocellWarning warns encodeMCWarn_statics, hstat]
    rfl
  by_cases hnz : nodes.size = 0
  · have hnzb : (nodes.size == 0) = true := beq_iff_eq.mpr hnz
    dsimp only [enc, mcRes]
    simp only [hnzb, ↓reduceIte]
    rw [show f + 53 = (f + 49) + 4 from by omega, h6to10]
    rw [show f + 49 = (f + 22) + 27 from by omega, h10to43]
    rw [deserLoop_drop_43]
    step1_ex; step1_ex
    rw [hnz]
    rw [show f + 20 = (f + 19) + 1 from by omega]
    rw [runJvmResFast_ifeq_branch rfl]
    rw [deserLoop_drop_66]
    rw [show f + 19 = (f + 18) + 1 from by omega]
    rw [runJvmResFast_getstatic_step hstat rfl]
    step1_ex; step1_ex; rw [hl15]
    rw [show f + 16 = (f + 15) + 1 from by omega]
    rw [runJvmResFast_invokestatic_step stepStatic_growBufToArray_mcWarn]
    step1_ex; step1_ex; step1_ex; step1_ex
    rw [show f + 11 = (f + 10) + 1 from by omega]
    rw [runJvmResFast_checkcast_step rfl]
    step1_ex; step1_ex; step1_ex
    rw [show f + 7 = (f + 6) + 1 from by omega]
    erw [runJvmResFast_invokestatic_step (stepStatic_getEMPTY_LEVEL_4 hstatW)]
    step1_ex; step1_ex; step1_ex
    rw [show f + 3 = (f + 2) + 1 from by omega]
    rw [runJvmResFast_checkNotNull_nonnull (by intro h; cases h)]
    step1_ex
    rw [runJvmResFast_areturn]
    exact ⟨84, _, rfl⟩
  · have hnzb : (nodes.size == 0) = false := beq_false_of_ne hnz
    dsimp only [enc, mcRes]
    simp only [hnzb, Bool.false_eq_true, ↓reduceIte]
    have hnodesDataW : pW.2.get? nodesDataAddr = some (.objArray "java/lang/Object"
        (nodes.data.map (fun m => JvmVal.ext (AlgExt.mc m)))) :=
      encodeGrowBufArray_get?_ext jh encodeMacrocellWarning warns encodeMCWarn_get?_ext
        nodesDataAddr _ hnodesData
    rw [show f + 54 = (f + 50) + 4 from by omega, h6to10]
    rw [show f + 50 = (f + 23) + 27 from by omega, h10to43]
    rw [deserLoop_drop_43]
    step1_ex; step1_ex
    rw [show f + 21 = (f + 20) + 1 from by omega]
    rw [runJvmResFast_ifeq_fallthrough hnzb]
    rw [show f + 20 = (f + 19) + 1 from by omega]
    rw [runJvmResFast_getstatic_step hstat rfl]
    step1_ex; step1_ex; rw [hl15]
    rw [show f + 17 = (f + 16) + 1 from by omega]
    rw [runJvmResFast_invokestatic_step stepStatic_growBufToArray_mcWarn]
    step1_ex; step1_ex
    step1_ex; step1_ex; step1_ex
    rw [show f + 11 = (f + 10) + 1 from by omega]
    rw [runJvmResFast_invokestatic_step stepStatic_uintCtor5a]
    rw [show f + 10 = (f + 9) + 1 from by omega]
    dsimp only [pW] at hnodesDataW
    erw [runJvmResFast_invokestatic_step (step_invokestatic_macroCellAt hnodesDataW)]
    step1_ex; step1_ex; step1_ex; step1_ex
    rw [show f + 5 = (f + 4) + 1 from by omega]
    rw [runJvmResFast_checkcast_step rfl]
    step1_ex; step1_ex; step1_ex
    rw [runJvmResFast_areturn]
    exact ⟨65, _, rfl⟩

private theorem step_deserLoop_unboxUInt {pc : Nat} {idx u : UInt32} {dst tmp tmp2 : Nat}
    {rest : List JvmInstr} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {innerAddr : Nat} {inner : Array JvmVal}
    (hdrop : f_Algorithm_deserializeMacrocell_loop_prog.drop pc =
      unboxUIntInstrs pc idx dst tmp tmp2 ++ rest)
    (h22 : locs 22 = .heapRef innerAddr)
    (harr : jh.get? innerAddr = some (.objArray "java/lang/Object" inner))
    (hibv : idx.toBitVec.slt 0#32 = false)
    (hidxLt : idx.toNat < inner.size)
    (hidxVal : inner[idx.toNat]'hidxLt = .boxedUInt u)
    (_h22dst : 22 < dst) (hdstTmp : dst < tmp) (hTmpTmp2 : tmp < tmp2) :
    ∃ locs',
      locs' dst = .i32 u ∧
      (∀ s, s < dst → locs' s = locs s) ∧
      ∀ f, runJvmResFast (f + 17) f_Algorithm_deserializeMacrocell_loop_prog pc
          (f_Algorithm_deserializeMacrocell_loop_prog.drop pc) ⟨pc, [], locs, jh, hp⟩ =
        runJvmResFast f f_Algorithm_deserializeMacrocell_loop_prog (pc + 22)
          (f_Algorithm_deserializeMacrocell_loop_prog.drop (pc + 22)) ⟨pc + 22, [], locs', jh, hp⟩ := by
  have hdrop15 : f_Algorithm_deserializeMacrocell_loop_prog.drop (pc + 15) =
      [.aload tmp, .ldcStr "null cannot be cast to non-null type kotlin.UInt",
       .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
         "(Ljava/lang/Object;Ljava/lang/String;)V",
       .aload tmp, .checkcast "kotlin/UInt",
       .invokevirtual "kotlin/UInt" "unbox-impl" "()I", .istore dst] ++ rest := by
    rw [drop_drop_add, hdrop]
    rfl
  have hdrop22 : (unboxUIntInstrs pc idx dst tmp tmp2 ++ rest).drop 22 =
      f_Algorithm_deserializeMacrocell_loop_prog.drop (pc + 22) := by
    rw [drop_drop_add, hdrop]
  let locs' := setLocal (setLocal (setLocal locs tmp (.boxedUInt u)) tmp2 (.i32 0)) dst (.i32 u)
  refine ⟨locs', by dsimp only [locs']; rw [setLocal_eq_val (decide_eq_true rfl)], ?_, fun f => ?_⟩
  · intro s hs
    dsimp only [locs']
    rw [setLocal_ne_eq (i := dst) (j := s) (decide_eq_false (by omega)),
      setLocal_ne_eq (i := tmp2) (j := s) (decide_eq_false (by omega)),
      setLocal_ne_eq (i := tmp) (j := s) (decide_eq_false (by omega))]
  · rw [hdrop]
    dsimp only [unboxUIntInstrs, List.cons_append, List.nil_append]
    step1; rw [h22]
    rw [show f + 16 = (f + 15) + 1 from by omega]
    rw [runJvmResFast_checkcast_objArray harr (Or.inl rfl)]
    step1
    rw [show f + 14 = (f + 13) + 1 from by omega]
    rw [runJvmResFast_aaload harr hibv hidxLt]
    rw [hidxVal]
    step1; step1; step1; step1
    (conv in (runJvmResFast _ _ _ _ _) =>
      dsimp only [Jvm.JvmState.pc, Jvm.JvmState.stack, Jvm.JvmState.locals,
        Jvm.JvmState.jvmHeap, Jvm.JvmState.heap]
      norm_jvm_locals
      try simp only [Nat.reduceAdd])
    have htmp1 : tmp ≠ tmp2 := by omega
    rw [setLocal_ne_eq (i := tmp2) (j := tmp) (decide_eq_false htmp1),
      setLocal_eq_val (decide_eq_true rfl)]
    rw [show f + 9 = (f + 8) + 1 from by omega]
    rw [runJvmResFast_instanceof_boxedUInt_int]
    rw [show f + 8 = (f + 7) + 1 from by omega]
    rw [runJvmResFast_ifeq_branch rfl]
    rw [hdrop15]
    dsimp only [List.cons_append, List.nil_append]
    step1
    (conv in (runJvmResFast _ _ _ _ _) =>
      dsimp only [Jvm.JvmState.pc, Jvm.JvmState.stack, Jvm.JvmState.locals,
        Jvm.JvmState.jvmHeap, Jvm.JvmState.heap]
      norm_jvm_locals
      try simp only [Nat.reduceAdd])
    rw [setLocal_ne_eq (i := tmp2) (j := tmp) (decide_eq_false htmp1),
      setLocal_eq_val (decide_eq_true rfl)]
    step1
    rw [show f + 5 = (f + 4) + 1 from by omega]
    rw [runJvmResFast_checkNotNull_nonnull (by intro h; cases h)]
    step1
    (conv in (runJvmResFast _ _ _ _ _) =>
      dsimp only [Jvm.JvmState.pc, Jvm.JvmState.stack, Jvm.JvmState.locals,
        Jvm.JvmState.jvmHeap, Jvm.JvmState.heap]
      norm_jvm_locals
      try simp only [Nat.reduceAdd])
    rw [setLocal_ne_eq (i := tmp2) (j := tmp) (decide_eq_false htmp1),
      setLocal_eq_val (decide_eq_true rfl)]
    rw [show f + 3 = (f + 2) + 1 from by omega]
    rw [runJvmResFast_checkcast_boxedUInt (Or.inl rfl)]
    step1; step1
    rw [show pc + 15 + 7 = pc + 22 from by omega, drop_drop_add, hdrop]
    change runJvmResFast f f_Algorithm_deserializeMacrocell_loop_prog (pc + 22)
        ((unboxUIntInstrs pc idx dst tmp tmp2 ++ rest).drop 22) _ = _
    rw [hdrop22]

private theorem step_deserLoop_cellChild {pc idLoc startLoc endLoc dstLoc errLoc1 errLoc2 errTmp : Nat}
    {rest : List JvmInstr} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {nodes : Algorithm.GrowBuf Algorithm.MacroCell} {isLeaf : Algorithm.GrowBuf Bool}
    {lvl id startVal endVal i : UInt32} {emptySub : Algorithm.MacroCell}
    {line : String} {warns : Algorithm.GrowBuf Algorithm.MacrocellWarning}
    (hdrop : f_Algorithm_deserializeMacrocell_loop_prog.drop pc =
      cellChildInstrs pc idLoc startLoc endLoc dstLoc errLoc1 errLoc2 errTmp ++ rest)
    (h2 : locs 2 = .i32 i) (h12 : mcNodes? (locs 12) = some nodes)
    (h14 : mcIsLeaf? (locs 14) = some isLeaf)
    (h15 : locs 15 = .ext (.mcWarnGrowBuf warns))
    (h16 : locs 16 = .str line) (h23 : locs 23 = .i32 lvl)
    (h36 : locs 36 = .ext (.mc emptySub))
    (hid : locs idLoc = .i32 id)
    (hstart : locs startLoc = .i32 startVal) (hend : locs endLoc = .i32 endVal)
    (hdst : 36 < dstLoc) (he1 : dstLoc < errLoc1) (he2 : errLoc1 < errLoc2) (het : errLoc2 < errTmp)
    (_hidLt : idLoc < dstLoc) (hsLt : startLoc < dstLoc) (heLt : endLoc < dstLoc)
    (hstat : jh.statics = []) :
    match Algorithm.macrocellCellChild nodes isLeaf lvl emptySub id with
    | some c =>
      ∃ locs',
        locs' dstLoc = .ext (.mc c) ∧
        (∀ s, s < dstLoc → locs' s = locs s) ∧
        ∀ f, runJvmResFast (f + 9) f_Algorithm_deserializeMacrocell_loop_prog pc
            (f_Algorithm_deserializeMacrocell_loop_prog.drop pc) ⟨pc, [], locs, jh, hp⟩ =
          runJvmResFast f f_Algorithm_deserializeMacrocell_loop_prog (pc + 36)
            (f_Algorithm_deserializeMacrocell_loop_prog.drop (pc + 36)) ⟨pc + 36, [], locs', jh, hp⟩
    | none =>
      let enc := encodeMacrocellResult jh
        ⟨.unexpectedNodeId line i startVal endVal, warns.toArray, Algorithm.emptyLevel4⟩
      ∃ pc' locs',
        ∀ f, runJvmResFast (f + 36) f_Algorithm_deserializeMacrocell_loop_prog pc
            (f_Algorithm_deserializeMacrocell_loop_prog.drop pc) ⟨pc, [], locs, jh, hp⟩ =
          some (enc.1, ⟨pc', [enc.1], locs', enc.2, hp⟩) := by
  have hmc := stepStatic_macrocellCellChild (pc := pc + 5) (nv := locs 12) (ilv := locs 14)
    (lvl := lvl) (id := id) (emptySub := emptySub) (rest := []) (locs := locs) (jh := jh) (hp := hp)
    h12 h14
  dsimp only at hmc
  cases hcc : Algorithm.macrocellCellChild nodes isLeaf lvl emptySub id with
  | some c =>
    dsimp only
    rw [hcc] at hmc
    have hdrop36 : (cellChildInstrs pc idLoc startLoc endLoc dstLoc errLoc1 errLoc2 errTmp ++ rest).drop 36 =
        f_Algorithm_deserializeMacrocell_loop_prog.drop (pc + 36) := by
      rw [drop_drop_add, hdrop]
    let locs' := setLocal locs dstLoc (.ext (.mc c))
    refine ⟨locs', by dsimp only [locs']; rw [setLocal_eq_val (decide_eq_true rfl)], ?_, fun f => ?_⟩
    · intro s hs
      dsimp only [locs']
      rw [setLocal_ne_eq (i := dstLoc) (j := s) (decide_eq_false (by omega))]
    · rw [hdrop]
      dsimp only [cellChildInstrs, List.cons_append, List.nil_append]
      step1; step1; step1; rw [h23]; step1; rw [h36]; step1; rw [hid]
      rw [show f + 4 = (f + 3) + 1 from by omega]
      rw [runJvmResFast_invokestatic_step hmc]
      step1; step1
      rw [setLocal_eq_val (decide_eq_true rfl)]
      rw [show f + 1 = f + 1 from rfl]
      rw [runJvmResFast_ifnonnull_branch (by rfl)]
  | none =>
    dsimp only
    rw [hcc] at hmc
    let uniObj : Jvm.HeapObj AlgExt :=
      .instance "com/alexvanyo/composelife/model/MacrocellStatus$UnexpectedNodeId"
        [("input", .str line), ("n1", .i32 i), ("n2", .i32 startVal), ("n3", .i32 endVal)]
    let jh1 := (jh.alloc uniObj).2
    have hdropTail : f_Algorithm_deserializeMacrocell_loop_prog.drop (pc + 19) =
        errTailInstrs errLoc1 errLoc2 errTmp ++ rest := by
      rw [drop_drop_add, hdrop]; rfl
    have hget1 : (jh1.get? jh.objects.size).bind
        (fun o => match o with | .instance c _ => some c | _ => none) =
        some "com/alexvanyo/composelife/model/MacrocellStatus$UnexpectedNodeId" := by
      dsimp only [jh1]; rw [jvmHeap_get?_alloc_self]; rfl
    have htail := step_deserLoop_err_tail (pc := pc + 19)
      (statusLoc := errLoc1) (arrLoc := errLoc2) (tmpLoc := errTmp)
      (rest := rest)
      (locs := setLocal (setLocal locs dstLoc .null) errLoc1 (.heapRef jh.objects.size))
      (jh := jh1) (hp := hp) (warns := warns) (sAddr := jh.objects.size)
      (cls := "com/alexvanyo/composelife/model/MacrocellStatus$UnexpectedNodeId")
      hdropTail (by omega) (by omega) (by omega) (by omega)
      (by rw [setLocal_ne_eq (i := errLoc1) (j := 15) (decide_eq_false (by omega)),
        setLocal_ne_eq (i := dstLoc) (j := 15) (decide_eq_false (by omega)), h15])
      (by rw [setLocal_eq_val (decide_eq_true rfl)])
      hget1 rfl (by dsimp only [jh1, Jvm.JvmHeap.alloc]; exact hstat)
    rcases htail with ⟨locs', htailEq⟩
    dsimp only [jh1, uniObj, Jvm.JvmHeap.alloc] at htailEq
    refine ⟨pc + 19 + 16, locs', fun f => ?_⟩
    rw [hdrop]
    dsimp only [cellChildInstrs, List.cons_append, List.nil_append]
    step1; step1; step1; rw [h23]; step1; rw [h36]; step1; rw [hid]
    rw [show f + 31 = (f + 30) + 1 from by omega]
    rw [runJvmResFast_invokestatic_step hmc]
    step1; step1
    rw [setLocal_eq_val (decide_eq_true rfl)]
    rw [show f + 28 = (f + 27) + 1 from by omega]
    rw [runJvmResFast_ifnonnull_fallthrough]
    step1; step1; step1
    rw [setLocal_ne_eq (i := dstLoc) (j := 16) (decide_eq_false (by omega)), h16]
    step1; step1
    rw [setLocal_ne_eq (i := dstLoc) (j := 2) (decide_eq_false (by omega)), h2]
    step1
    rw [setLocal_ne_eq (i := dstLoc) (j := startLoc) (decide_eq_false (by omega)), hstart]
    step1
    rw [setLocal_ne_eq (i := dstLoc) (j := endLoc) (decide_eq_false (by omega)), hend]
    step1; step1; step1
    (conv in (runJvmResFast _ _ _ _ _) =>
      dsimp only [Jvm.JvmState.pc, Jvm.JvmState.stack, Jvm.JvmState.locals,
        Jvm.JvmState.jvmHeap, Jvm.JvmState.heap]
      norm_jvm_locals
      try simp only [Nat.reduceAdd])
    simp only [Nat.add_assoc, Nat.reduceAdd]
    rw [← hdropTail]
    exact htailEq f

private theorem step_deserLoop_leafChild {pc idLoc startLoc endLoc dstLoc errLoc1 errLoc2 errTmp : Nat}
    {rest : List JvmInstr} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {leaves : Algorithm.GrowBuf UInt64} {isLeaf : Algorithm.GrowBuf Bool}
    {id startVal endVal i : UInt32}
    {line : String} {warns : Algorithm.GrowBuf Algorithm.MacrocellWarning}
    (hdrop : f_Algorithm_deserializeMacrocell_loop_prog.drop pc =
      leafChildInstrs pc idLoc startLoc endLoc dstLoc errLoc1 errLoc2 errTmp ++ rest)
    (h2 : locs 2 = .i32 i) (h13 : mcLeaves? (locs 13) = some leaves)
    (h14 : mcIsLeaf? (locs 14) = some isLeaf)
    (h15 : locs 15 = .ext (.mcWarnGrowBuf warns))
    (h16 : locs 16 = .str line)
    (hid : locs idLoc = .i32 id)
    (hstart : locs startLoc = .i32 startVal) (hend : locs endLoc = .i32 endVal)
    (hdst : 35 < dstLoc) (he1 : dstLoc < errLoc1) (he2 : errLoc1 < errLoc2) (het : errLoc2 < errTmp)
    (_hidLt : idLoc < dstLoc) (hsLt : startLoc < dstLoc) (heLt : endLoc < dstLoc)
    (hstat : jh.statics = []) :
    match Algorithm.macrocellLeafChild leaves isLeaf id with
    | some v =>
      ∃ locs',
        locs' dstLoc = .boxedULong v ∧
        (∀ s, s < dstLoc → locs' s = locs s) ∧
        ∀ f, runJvmResFast (f + 7) f_Algorithm_deserializeMacrocell_loop_prog pc
            (f_Algorithm_deserializeMacrocell_loop_prog.drop pc) ⟨pc, [], locs, jh, hp⟩ =
          runJvmResFast f f_Algorithm_deserializeMacrocell_loop_prog (pc + 34)
            (f_Algorithm_deserializeMacrocell_loop_prog.drop (pc + 34)) ⟨pc + 34, [], locs', jh, hp⟩
    | none =>
      let enc := encodeMacrocellResult jh
        ⟨.unexpectedNodeId line i startVal endVal, warns.toArray, Algorithm.emptyLevel4⟩
      ∃ pc' locs',
        ∀ f, runJvmResFast (f + 34) f_Algorithm_deserializeMacrocell_loop_prog pc
            (f_Algorithm_deserializeMacrocell_loop_prog.drop pc) ⟨pc, [], locs, jh, hp⟩ =
          some (enc.1, ⟨pc', [enc.1], locs', enc.2, hp⟩) := by
  have hml := stepStatic_macrocellLeafChild (pc := pc + 3) (lv := locs 13) (ilv := locs 14)
    (id := id) (rest := []) (locs := locs) (jh := jh) (hp := hp) h13 h14
  dsimp only at hml
  cases hlc : Algorithm.macrocellLeafChild leaves isLeaf id with
  | some v =>
    dsimp only
    rw [hlc] at hml
    have hdrop34 : (leafChildInstrs pc idLoc startLoc endLoc dstLoc errLoc1 errLoc2 errTmp ++ rest).drop 34 =
        f_Algorithm_deserializeMacrocell_loop_prog.drop (pc + 34) := by
      rw [drop_drop_add, hdrop]
    let locs' := setLocal locs dstLoc (.boxedULong v)
    refine ⟨locs', by dsimp only [locs']; rw [setLocal_eq_val (decide_eq_true rfl)], ?_, fun f => ?_⟩
    · intro s hs
      dsimp only [locs']
      rw [setLocal_ne_eq (i := dstLoc) (j := s) (decide_eq_false (by omega))]
    · rw [hdrop]
      dsimp only [leafChildInstrs, List.cons_append, List.nil_append]
      step1; step1; step1; rw [hid]
      rw [show f + 4 = (f + 3) + 1 from by omega]
      rw [runJvmResFast_invokestatic_step hml]
      step1; step1
      rw [setLocal_eq_val (decide_eq_true rfl)]
      rw [runJvmResFast_ifnonnull_branch (by rfl)]
  | none =>
    dsimp only
    rw [hlc] at hml
    let uniObj : Jvm.HeapObj AlgExt :=
      .instance "com/alexvanyo/composelife/model/MacrocellStatus$UnexpectedNodeId"
        [("input", .str line), ("n1", .i32 i), ("n2", .i32 startVal), ("n3", .i32 endVal)]
    let jh1 := (jh.alloc uniObj).2
    have hdropTail : f_Algorithm_deserializeMacrocell_loop_prog.drop (pc + 17) =
        errTailInstrs errLoc1 errLoc2 errTmp ++ rest := by
      rw [drop_drop_add, hdrop]; rfl
    have hget1 : (jh1.get? jh.objects.size).bind
        (fun o => match o with | .instance c _ => some c | _ => none) =
        some "com/alexvanyo/composelife/model/MacrocellStatus$UnexpectedNodeId" := by
      dsimp only [jh1]; rw [jvmHeap_get?_alloc_self]; rfl
    have htail := step_deserLoop_err_tail (pc := pc + 17)
      (statusLoc := errLoc1) (arrLoc := errLoc2) (tmpLoc := errTmp)
      (rest := rest)
      (locs := setLocal (setLocal locs dstLoc .null) errLoc1 (.heapRef jh.objects.size))
      (jh := jh1) (hp := hp) (warns := warns) (sAddr := jh.objects.size)
      (cls := "com/alexvanyo/composelife/model/MacrocellStatus$UnexpectedNodeId")
      hdropTail (by omega) (by omega) (by omega) (by omega)
      (by rw [setLocal_ne_eq (i := errLoc1) (j := 15) (decide_eq_false (by omega)),
        setLocal_ne_eq (i := dstLoc) (j := 15) (decide_eq_false (by omega)), h15])
      (by rw [setLocal_eq_val (decide_eq_true rfl)])
      hget1 rfl (by dsimp only [jh1, Jvm.JvmHeap.alloc]; exact hstat)
    rcases htail with ⟨locs', htailEq⟩
    dsimp only [jh1, uniObj, Jvm.JvmHeap.alloc] at htailEq
    refine ⟨pc + 17 + 16, locs', fun f => ?_⟩
    rw [hdrop]
    dsimp only [leafChildInstrs, List.cons_append, List.nil_append]
    step1; step1; step1; rw [hid]
    rw [show f + 31 = (f + 30) + 1 from by omega]
    rw [runJvmResFast_invokestatic_step hml]
    step1; step1
    rw [setLocal_eq_val (decide_eq_true rfl)]
    rw [show f + 28 = (f + 27) + 1 from by omega]
    rw [runJvmResFast_ifnonnull_fallthrough]
    step1; step1; step1
    rw [setLocal_ne_eq (i := dstLoc) (j := 16) (decide_eq_false (by omega)), h16]
    step1; step1
    rw [setLocal_ne_eq (i := dstLoc) (j := 2) (decide_eq_false (by omega)), h2]
    step1
    rw [setLocal_ne_eq (i := dstLoc) (j := startLoc) (decide_eq_false (by omega)), hstart]
    step1
    rw [setLocal_ne_eq (i := dstLoc) (j := endLoc) (decide_eq_false (by omega)), hend]
    step1; step1; step1
    (conv in (runJvmResFast _ _ _ _ _) =>
      dsimp only [Jvm.JvmState.pc, Jvm.JvmState.stack, Jvm.JvmState.locals,
        Jvm.JvmState.jvmHeap, Jvm.JvmState.heap]
      norm_jvm_locals
      try simp only [Nat.reduceAdd])
    simp only [Nat.add_assoc, Nat.reduceAdd]
    rw [← hdropTail]
    exact htailEq f

private theorem step_deserLoop_unboxULong {pc srcLoc : Nat} {v : UInt64}
    {stk : List JvmVal} {rest : List JvmInstr} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hdrop : f_Algorithm_deserializeMacrocell_loop_prog.drop pc =
      unboxULongInstrs pc srcLoc ++ rest)
    (hsrc : locs srcLoc = .boxedULong v)
    (_hsrcLt : srcLoc < 42) :
    ∃ locs',
      (∀ s, s < 42 → locs' s = locs s) ∧
      ∀ f, runJvmResFast (f + 9) f_Algorithm_deserializeMacrocell_loop_prog pc
          (f_Algorithm_deserializeMacrocell_loop_prog.drop pc) ⟨pc, stk, locs, jh, hp⟩ =
        runJvmResFast f f_Algorithm_deserializeMacrocell_loop_prog (pc + 14)
          (f_Algorithm_deserializeMacrocell_loop_prog.drop (pc + 14))
          ⟨pc + 14, .i64 v :: stk, locs', jh, hp⟩ := by
  have hdrop12 : f_Algorithm_deserializeMacrocell_loop_prog.drop (pc + 12) =
      [.aload 42, .invokevirtual "kotlin/ULong" "unbox-impl" "()J"] ++ rest := by
    rw [drop_drop_add, hdrop]; rfl
  have hdrop14 : (unboxULongInstrs pc srcLoc ++ rest).drop 14 =
      f_Algorithm_deserializeMacrocell_loop_prog.drop (pc + 14) := by
    rw [drop_drop_add, hdrop]
  let locs' := setLocal (setLocal locs 42 (.boxedULong v)) 43 (.i32 0)
  refine ⟨locs', ?_, fun f => ?_⟩
  · intro s hs
    dsimp only [locs']
    rw [setLocal_ne_eq (i := 43) (j := s) (decide_eq_false (by omega)),
      setLocal_ne_eq (i := 42) (j := s) (decide_eq_false (by omega))]
  · rw [hdrop]
    dsimp only [unboxULongInstrs, List.cons_append, List.nil_append]
    step1; rw [hsrc]
    step1; step1; step1; step1
    (conv in (runJvmResFast _ _ _ _ _) =>
      dsimp only [Jvm.JvmState.pc, Jvm.JvmState.stack, Jvm.JvmState.locals,
        Jvm.JvmState.jvmHeap, Jvm.JvmState.heap]
      norm_jvm_locals
      try simp only [Nat.reduceAdd])
    rw [show f + 4 = (f + 3) + 1 from by omega]
    rw [runJvmResFast_instanceof_boxedULong_long]
    rw [show f + 3 = (f + 2) + 1 from by omega]
    rw [runJvmResFast_ifeq_branch rfl]
    rw [hdrop12]
    dsimp only [List.cons_append, List.nil_append]
    step1
    (conv in (runJvmResFast _ _ _ _ _) =>
      dsimp only [Jvm.JvmState.pc, Jvm.JvmState.stack, Jvm.JvmState.locals,
        Jvm.JvmState.jvmHeap, Jvm.JvmState.heap]
      norm_jvm_locals
      try simp only [Nat.reduceAdd])
    rw [runJvmResFast_invokevirtual_step stepVirtual_ulong_unbox]
    rw [show pc + 12 + 2 = pc + 14 from by omega, drop_drop_add, hdrop]
    change runJvmResFast f f_Algorithm_deserializeMacrocell_loop_prog (pc + 14)
        ((unboxULongInstrs pc srcLoc ++ rest).drop 14) _ = _
    rw [hdrop14]

private theorem step_deserLoop_unboxAll13 {innerAddr : Nat}
    {nl : Algorithm.MCNodeLine} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (h22 : locs 22 = .heapRef innerAddr)
    (harr : jh.get? innerAddr = some (Jvm.HeapObj.objArray "java/lang/Object"
      ((((((((((((((Array.replicate 50 JvmVal.null
        |>.set! 0 (.boxedInt 0))
        |>.set! 1 (.boxedUInt nl.level))
        |>.set! 5 (.boxedUInt nl.nw))
        |>.set! 9 (.boxedUInt nl.nwStart))
        |>.set! 13 (.boxedUInt nl.nwEnd))
        |>.set! 17 (.boxedUInt nl.ne))
        |>.set! 21 (.boxedUInt nl.neStart))
        |>.set! 25 (.boxedUInt nl.neEnd))
        |>.set! 29 (.boxedUInt nl.sw))
        |>.set! 33 (.boxedUInt nl.swStart))
        |>.set! 37 (.boxedUInt nl.swEnd))
        |>.set! 41 (.boxedUInt nl.se))
        |>.set! 45 (.boxedUInt nl.seStart))
        |>.set! 49 (.boxedUInt nl.seEnd)))) :
    ∃ locs',
      (∀ s, s < 23 → locs' s = locs s) ∧
      locs' 23 = .i32 nl.level ∧ locs' 24 = .i32 nl.nw ∧
      locs' 25 = .i32 nl.nwStart ∧ locs' 26 = .i32 nl.nwEnd ∧
      locs' 27 = .i32 nl.ne ∧ locs' 28 = .i32 nl.neStart ∧
      locs' 29 = .i32 nl.neEnd ∧ locs' 30 = .i32 nl.sw ∧
      locs' 31 = .i32 nl.swStart ∧ locs' 32 = .i32 nl.swEnd ∧
      locs' 33 = .i32 nl.se ∧ locs' 34 = .i32 nl.seStart ∧
      locs' 35 = .i32 nl.seEnd ∧
      ∀ f, runJvmResFast (f + 221) f_Algorithm_deserializeMacrocell_loop_prog 177
          (f_Algorithm_deserializeMacrocell_loop_prog.drop 177) ⟨177, [], locs, jh, hp⟩ =
        runJvmResFast f f_Algorithm_deserializeMacrocell_loop_prog 463
          (f_Algorithm_deserializeMacrocell_loop_prog.drop 463) ⟨463, [], locs', jh, hp⟩ := by
  have hd0 : f_Algorithm_deserializeMacrocell_loop_prog.drop 177 =
      unboxUIntInstrs 177 1 23 24 25 ++
      (unboxUIntInstrs 199 5 24 25 26 ++ unboxUIntInstrs 221 9 25 26 27 ++
       unboxUIntInstrs 243 13 26 27 28 ++ unboxUIntInstrs 265 17 27 28 29 ++
       unboxUIntInstrs 287 21 28 29 30 ++ unboxUIntInstrs 309 25 29 30 31 ++
       unboxUIntInstrs 331 29 30 31 32 ++ unboxUIntInstrs 353 33 31 32 33 ++
       unboxUIntInstrs 375 37 32 33 34 ++ unboxUIntInstrs 397 41 33 34 35 ++
       unboxUIntInstrs 419 45 34 35 36 ++ unboxUIntInstrs 441 49 35 36 37 ++
       f_Algorithm_deserializeMacrocell_loop_prog.drop 463) := by
    rw [deserLoop_drop_177]; simp only [List.append_assoc]
  rcases step_deserLoop_unboxUInt hd0 h22 harr
      (by decide) (by simp) (by simp; rfl) (by omega) (by omega) (by omega) with ⟨l1, hv23, hp1, hs1⟩
  have hd1 : f_Algorithm_deserializeMacrocell_loop_prog.drop 199 =
      unboxUIntInstrs 199 5 24 25 26 ++
      (unboxUIntInstrs 221 9 25 26 27 ++ unboxUIntInstrs 243 13 26 27 28 ++
       unboxUIntInstrs 265 17 27 28 29 ++ unboxUIntInstrs 287 21 28 29 30 ++
       unboxUIntInstrs 309 25 29 30 31 ++ unboxUIntInstrs 331 29 30 31 32 ++
       unboxUIntInstrs 353 33 31 32 33 ++ unboxUIntInstrs 375 37 32 33 34 ++
       unboxUIntInstrs 397 41 33 34 35 ++ unboxUIntInstrs 419 45 34 35 36 ++
       unboxUIntInstrs 441 49 35 36 37 ++ f_Algorithm_deserializeMacrocell_loop_prog.drop 463) := by
    rw [show (199 : Nat) = 177 + 22 from rfl, drop_drop_add, hd0]; rfl
  rcases step_deserLoop_unboxUInt (locs := l1) hd1 (by rw [hp1 22 (by omega)]; exact h22) harr
      (by decide) (by simp) (by simp; rfl) (by omega) (by omega) (by omega) with ⟨l2, hv24, hp2, hs2⟩
  have hd2 : f_Algorithm_deserializeMacrocell_loop_prog.drop 221 =
      unboxUIntInstrs 221 9 25 26 27 ++
      (unboxUIntInstrs 243 13 26 27 28 ++ unboxUIntInstrs 265 17 27 28 29 ++
       unboxUIntInstrs 287 21 28 29 30 ++ unboxUIntInstrs 309 25 29 30 31 ++
       unboxUIntInstrs 331 29 30 31 32 ++ unboxUIntInstrs 353 33 31 32 33 ++
       unboxUIntInstrs 375 37 32 33 34 ++ unboxUIntInstrs 397 41 33 34 35 ++
       unboxUIntInstrs 419 45 34 35 36 ++ unboxUIntInstrs 441 49 35 36 37 ++
       f_Algorithm_deserializeMacrocell_loop_prog.drop 463) := by
    rw [show (221 : Nat) = 199 + 22 from rfl, drop_drop_add, hd1]; rfl
  rcases step_deserLoop_unboxUInt (locs := l2) hd2 (by rw [hp2 22 (by omega), hp1 22 (by omega)]; exact h22) harr
      (by decide) (by simp) (by simp; rfl) (by omega) (by omega) (by omega) with ⟨l3, hv25, hp3, hs3⟩
  have hd3 : f_Algorithm_deserializeMacrocell_loop_prog.drop 243 =
      unboxUIntInstrs 243 13 26 27 28 ++
      (unboxUIntInstrs 265 17 27 28 29 ++ unboxUIntInstrs 287 21 28 29 30 ++
       unboxUIntInstrs 309 25 29 30 31 ++ unboxUIntInstrs 331 29 30 31 32 ++
       unboxUIntInstrs 353 33 31 32 33 ++ unboxUIntInstrs 375 37 32 33 34 ++
       unboxUIntInstrs 397 41 33 34 35 ++ unboxUIntInstrs 419 45 34 35 36 ++
       unboxUIntInstrs 441 49 35 36 37 ++ f_Algorithm_deserializeMacrocell_loop_prog.drop 463) := by
    rw [show (243 : Nat) = 221 + 22 from rfl, drop_drop_add, hd2]; rfl
  rcases step_deserLoop_unboxUInt (locs := l3) hd3
      (by rw [hp3 22 (by omega), hp2 22 (by omega), hp1 22 (by omega)]; exact h22) harr
      (by decide) (by simp) (by simp; rfl) (by omega) (by omega) (by omega) with ⟨l4, hv26, hp4, hs4⟩
  have hd4 : f_Algorithm_deserializeMacrocell_loop_prog.drop 265 =
      unboxUIntInstrs 265 17 27 28 29 ++
      (unboxUIntInstrs 287 21 28 29 30 ++ unboxUIntInstrs 309 25 29 30 31 ++
       unboxUIntInstrs 331 29 30 31 32 ++ unboxUIntInstrs 353 33 31 32 33 ++
       unboxUIntInstrs 375 37 32 33 34 ++ unboxUIntInstrs 397 41 33 34 35 ++
       unboxUIntInstrs 419 45 34 35 36 ++ unboxUIntInstrs 441 49 35 36 37 ++
       f_Algorithm_deserializeMacrocell_loop_prog.drop 463) := by
    rw [show (265 : Nat) = 243 + 22 from rfl, drop_drop_add, hd3]; rfl
  rcases step_deserLoop_unboxUInt (locs := l4) hd4
      (by rw [hp4 22 (by omega), hp3 22 (by omega), hp2 22 (by omega), hp1 22 (by omega)]; exact h22) harr
      (by decide) (by simp) (by simp; rfl) (by omega) (by omega) (by omega) with ⟨l5, hv27, hp5, hs5⟩
  have hd5 : f_Algorithm_deserializeMacrocell_loop_prog.drop 287 =
      unboxUIntInstrs 287 21 28 29 30 ++
      (unboxUIntInstrs 309 25 29 30 31 ++ unboxUIntInstrs 331 29 30 31 32 ++
       unboxUIntInstrs 353 33 31 32 33 ++ unboxUIntInstrs 375 37 32 33 34 ++
       unboxUIntInstrs 397 41 33 34 35 ++ unboxUIntInstrs 419 45 34 35 36 ++
       unboxUIntInstrs 441 49 35 36 37 ++ f_Algorithm_deserializeMacrocell_loop_prog.drop 463) := by
    rw [show (287 : Nat) = 265 + 22 from rfl, drop_drop_add, hd4]; rfl
  rcases step_deserLoop_unboxUInt (locs := l5) hd5
      (by rw [hp5 22 (by omega), hp4 22 (by omega), hp3 22 (by omega),
        hp2 22 (by omega), hp1 22 (by omega)]; exact h22) harr
      (by decide) (by simp) (by simp; rfl) (by omega) (by omega) (by omega) with ⟨l6, hv28, hp6, hs6⟩
  have hd6 : f_Algorithm_deserializeMacrocell_loop_prog.drop 309 =
      unboxUIntInstrs 309 25 29 30 31 ++
      (unboxUIntInstrs 331 29 30 31 32 ++ unboxUIntInstrs 353 33 31 32 33 ++
       unboxUIntInstrs 375 37 32 33 34 ++ unboxUIntInstrs 397 41 33 34 35 ++
       unboxUIntInstrs 419 45 34 35 36 ++ unboxUIntInstrs 441 49 35 36 37 ++
       f_Algorithm_deserializeMacrocell_loop_prog.drop 463) := by
    rw [show (309 : Nat) = 287 + 22 from rfl, drop_drop_add, hd5]; rfl
  rcases step_deserLoop_unboxUInt (locs := l6) hd6
      (by rw [hp6 22 (by omega), hp5 22 (by omega), hp4 22 (by omega),
        hp3 22 (by omega), hp2 22 (by omega), hp1 22 (by omega)]; exact h22) harr
      (by decide) (by simp) (by simp; rfl) (by omega) (by omega) (by omega) with ⟨l7, hv29, hp7, hs7⟩
  have hd7 : f_Algorithm_deserializeMacrocell_loop_prog.drop 331 =
      unboxUIntInstrs 331 29 30 31 32 ++
      (unboxUIntInstrs 353 33 31 32 33 ++ unboxUIntInstrs 375 37 32 33 34 ++
       unboxUIntInstrs 397 41 33 34 35 ++ unboxUIntInstrs 419 45 34 35 36 ++
       unboxUIntInstrs 441 49 35 36 37 ++ f_Algorithm_deserializeMacrocell_loop_prog.drop 463) := by
    rw [show (331 : Nat) = 309 + 22 from rfl, drop_drop_add, hd6]; rfl
  rcases step_deserLoop_unboxUInt (locs := l7) hd7
      (by rw [hp7 22 (by omega), hp6 22 (by omega), hp5 22 (by omega), hp4 22 (by omega),
        hp3 22 (by omega), hp2 22 (by omega), hp1 22 (by omega)]; exact h22) harr
      (by decide) (by simp) (by simp; rfl) (by omega) (by omega) (by omega) with ⟨l8, hv30, hp8, hs8⟩
  have hd8 : f_Algorithm_deserializeMacrocell_loop_prog.drop 353 =
      unboxUIntInstrs 353 33 31 32 33 ++
      (unboxUIntInstrs 375 37 32 33 34 ++ unboxUIntInstrs 397 41 33 34 35 ++
       unboxUIntInstrs 419 45 34 35 36 ++ unboxUIntInstrs 441 49 35 36 37 ++
       f_Algorithm_deserializeMacrocell_loop_prog.drop 463) := by
    rw [show (353 : Nat) = 331 + 22 from rfl, drop_drop_add, hd7]; rfl
  rcases step_deserLoop_unboxUInt (locs := l8) hd8
      (by rw [hp8 22 (by omega), hp7 22 (by omega), hp6 22 (by omega), hp5 22 (by omega),
        hp4 22 (by omega), hp3 22 (by omega), hp2 22 (by omega), hp1 22 (by omega)]; exact h22) harr
      (by decide) (by simp) (by simp; rfl) (by omega) (by omega) (by omega) with ⟨l9, hv31, hp9, hs9⟩
  have hd9 : f_Algorithm_deserializeMacrocell_loop_prog.drop 375 =
      unboxUIntInstrs 375 37 32 33 34 ++
      (unboxUIntInstrs 397 41 33 34 35 ++ unboxUIntInstrs 419 45 34 35 36 ++
       unboxUIntInstrs 441 49 35 36 37 ++ f_Algorithm_deserializeMacrocell_loop_prog.drop 463) := by
    rw [show (375 : Nat) = 353 + 22 from rfl, drop_drop_add, hd8]; rfl
  rcases step_deserLoop_unboxUInt (locs := l9) hd9
      (by rw [hp9 22 (by omega), hp8 22 (by omega), hp7 22 (by omega), hp6 22 (by omega),
        hp5 22 (by omega), hp4 22 (by omega), hp3 22 (by omega), hp2 22 (by omega),
        hp1 22 (by omega)]; exact h22) harr
      (by decide) (by simp) (by simp; rfl) (by omega) (by omega) (by omega) with ⟨l10, hv32, hp10, hs10⟩
  have hd10 : f_Algorithm_deserializeMacrocell_loop_prog.drop 397 =
      unboxUIntInstrs 397 41 33 34 35 ++
      (unboxUIntInstrs 419 45 34 35 36 ++ unboxUIntInstrs 441 49 35 36 37 ++
       f_Algorithm_deserializeMacrocell_loop_prog.drop 463) := by
    rw [show (397 : Nat) = 375 + 22 from rfl, drop_drop_add, hd9]; rfl
  rcases step_deserLoop_unboxUInt (locs := l10) hd10
      (by rw [hp10 22 (by omega), hp9 22 (by omega), hp8 22 (by omega), hp7 22 (by omega),
        hp6 22 (by omega), hp5 22 (by omega), hp4 22 (by omega), hp3 22 (by omega),
        hp2 22 (by omega), hp1 22 (by omega)]; exact h22) harr
      (by decide) (by simp) (by simp; rfl) (by omega) (by omega) (by omega) with ⟨l11, hv33, hp11, hs11⟩
  have hd11 : f_Algorithm_deserializeMacrocell_loop_prog.drop 419 =
      unboxUIntInstrs 419 45 34 35 36 ++
      (unboxUIntInstrs 441 49 35 36 37 ++ f_Algorithm_deserializeMacrocell_loop_prog.drop 463) := by
    rw [show (419 : Nat) = 397 + 22 from rfl, drop_drop_add, hd10]; rfl
  rcases step_deserLoop_unboxUInt (locs := l11) hd11
      (by rw [hp11 22 (by omega), hp10 22 (by omega), hp9 22 (by omega), hp8 22 (by omega),
        hp7 22 (by omega), hp6 22 (by omega), hp5 22 (by omega), hp4 22 (by omega),
        hp3 22 (by omega), hp2 22 (by omega), hp1 22 (by omega)]; exact h22) harr
      (by decide) (by simp) (by simp; rfl) (by omega) (by omega) (by omega) with ⟨l12, hv34, hp12, hs12⟩
  have hd12 : f_Algorithm_deserializeMacrocell_loop_prog.drop 441 =
      unboxUIntInstrs 441 49 35 36 37 ++ f_Algorithm_deserializeMacrocell_loop_prog.drop 463 := by
    rw [show (441 : Nat) = 419 + 22 from rfl, drop_drop_add, hd11]; rfl
  rcases step_deserLoop_unboxUInt (locs := l12) hd12
      (by rw [hp12 22 (by omega), hp11 22 (by omega), hp10 22 (by omega), hp9 22 (by omega),
        hp8 22 (by omega), hp7 22 (by omega), hp6 22 (by omega), hp5 22 (by omega),
        hp4 22 (by omega), hp3 22 (by omega), hp2 22 (by omega), hp1 22 (by omega)]; exact h22) harr
      (by decide) (by simp) (by simp; rfl) (by omega) (by omega) (by omega) with ⟨l13, hv35, hp13, hs13⟩
  refine ⟨l13, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    rw [hp13 s (by omega), hp12 s (by omega), hp11 s (by omega), hp10 s (by omega),
      hp9 s (by omega), hp8 s (by omega), hp7 s (by omega), hp6 s (by omega),
      hp5 s (by omega), hp4 s (by omega), hp3 s (by omega), hp2 s (by omega), hp1 s (by omega)]
  · rw [hp13 23 (by omega), hp12 23 (by omega), hp11 23 (by omega), hp10 23 (by omega),
      hp9 23 (by omega), hp8 23 (by omega), hp7 23 (by omega), hp6 23 (by omega),
      hp5 23 (by omega), hp4 23 (by omega), hp3 23 (by omega), hp2 23 (by omega), hv23]
  · rw [hp13 24 (by omega), hp12 24 (by omega), hp11 24 (by omega), hp10 24 (by omega),
      hp9 24 (by omega), hp8 24 (by omega), hp7 24 (by omega), hp6 24 (by omega),
      hp5 24 (by omega), hp4 24 (by omega), hp3 24 (by omega), hv24]
  · rw [hp13 25 (by omega), hp12 25 (by omega), hp11 25 (by omega), hp10 25 (by omega),
      hp9 25 (by omega), hp8 25 (by omega), hp7 25 (by omega), hp6 25 (by omega),
      hp5 25 (by omega), hp4 25 (by omega), hv25]
  · rw [hp13 26 (by omega), hp12 26 (by omega), hp11 26 (by omega), hp10 26 (by omega),
      hp9 26 (by omega), hp8 26 (by omega), hp7 26 (by omega), hp6 26 (by omega),
      hp5 26 (by omega), hv26]
  · rw [hp13 27 (by omega), hp12 27 (by omega), hp11 27 (by omega), hp10 27 (by omega),
      hp9 27 (by omega), hp8 27 (by omega), hp7 27 (by omega), hp6 27 (by omega), hv27]
  · rw [hp13 28 (by omega), hp12 28 (by omega), hp11 28 (by omega), hp10 28 (by omega),
      hp9 28 (by omega), hp8 28 (by omega), hp7 28 (by omega), hv28]
  · rw [hp13 29 (by omega), hp12 29 (by omega), hp11 29 (by omega), hp10 29 (by omega),
      hp9 29 (by omega), hp8 29 (by omega), hv29]
  · rw [hp13 30 (by omega), hp12 30 (by omega), hp11 30 (by omega), hp10 30 (by omega),
      hp9 30 (by omega), hv30]
  · rw [hp13 31 (by omega), hp12 31 (by omega), hp11 31 (by omega), hp10 31 (by omega), hv31]
  · rw [hp13 32 (by omega), hp12 32 (by omega), hp11 32 (by omega), hv32]
  · rw [hp13 33 (by omega), hp12 33 (by omega), hv33]
  · rw [hp13 34 (by omega), hv34]
  · exact hv35
  · intro f
    rw [show f + 221 = f + 204 + 17 from by omega, hs1,
      show f + 204 = f + 187 + 17 from by omega, hs2,
      show f + 187 = f + 170 + 17 from by omega, hs3,
      show f + 170 = f + 153 + 17 from by omega, hs4,
      show f + 153 = f + 136 + 17 from by omega, hs5,
      show f + 136 = f + 119 + 17 from by omega, hs6,
      show f + 119 = f + 102 + 17 from by omega, hs7,
      show f + 102 = f + 85 + 17 from by omega, hs8,
      show f + 85 = f + 68 + 17 from by omega, hs9,
      show f + 68 = f + 51 + 17 from by omega, hs10,
      show f + 51 = f + 34 + 17 from by omega, hs11,
      show f + 34 = f + 17 + 17 from by omega, hs12,
      hs13]

private theorem step_deserLoop_unexpectedInput_1102 {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {i : UInt32} {line : String}
    {warns : Algorithm.GrowBuf Algorithm.MacrocellWarning}
    (h2 : locs 2 = .i32 i) (h15 : locs 15 = .ext (.mcWarnGrowBuf warns))
    (h16 : locs 16 = .str line) (hstat : jh.statics = []) :
    let enc := encodeMacrocellResult jh ⟨.unexpectedInput line i, warns.toArray, Algorithm.emptyLevel4⟩
    ∃ pc' locs',
      ∀ f, runJvmResFast (f + 25) f_Algorithm_deserializeMacrocell_loop_prog 1102
          (f_Algorithm_deserializeMacrocell_loop_prog.drop 1102) ⟨1102, [], locs, jh, hp⟩ =
        some (enc.1, ⟨pc', [enc.1], locs', enc.2, hp⟩) := by
  let uiObj : Jvm.HeapObj AlgExt :=
    .instance "com/alexvanyo/composelife/model/MacrocellStatus$UnexpectedInput"
      [("input", .str line), ("lineIndex", .i32 i)]
  let jh1 := (jh.alloc uiObj).2
  have hdropTail : f_Algorithm_deserializeMacrocell_loop_prog.drop 1110 =
      errTailInstrs 17 18 20 ++ f_Algorithm_deserializeMacrocell_loop_prog.drop 1127 := by
    rw [show (1110 : Nat) = 1102 + 8 from rfl, drop_drop_add, deserLoop_drop_1102]
    rfl
  have hget1 : (jh1.get? jh.objects.size).bind
      (fun o => match o with | .instance c _ => some c | _ => none) =
      some "com/alexvanyo/composelife/model/MacrocellStatus$UnexpectedInput" := by
    dsimp only [jh1]; rw [jvmHeap_get?_alloc_self]; rfl
  have htail := step_deserLoop_err_tail (pc := 1110)
    (statusLoc := 17) (arrLoc := 18) (tmpLoc := 20)
    (rest := f_Algorithm_deserializeMacrocell_loop_prog.drop 1127)
    (locs := setLocal locs 17 (.heapRef jh.objects.size))
    (jh := jh1) (hp := hp) (warns := warns) (sAddr := jh.objects.size)
    (cls := "com/alexvanyo/composelife/model/MacrocellStatus$UnexpectedInput")
    hdropTail (by decide) (by decide) (by decide) (by decide)
    (by rw [setLocal_ne_eq (i := 17) (j := 15) (decide_eq_false (by omega)), h15])
    (by rw [setLocal_eq_val rfl])
    hget1 rfl (by dsimp only [jh1, Jvm.JvmHeap.alloc]; exact hstat)
  rcases htail with ⟨locs', htailEq⟩
  dsimp only [jh1, uiObj, Jvm.JvmHeap.alloc] at htailEq
  refine ⟨1110 + 16, locs', fun f => ?_⟩
  rw [deserLoop_drop_1102]
  rw [show f + 25 = (f + 22) + 3 from by omega]; chunk 3; rw [h16]
  rw [show f + 22 = (f + 21) + 1 from by omega]
  erw [runJvmResFast_checkcast_step rfl]
  rw [show f + 21 = (f + 20) + 1 from by omega]; chunk 1; rw [h2]
  rw [show f + 20 = (f + 19) + 1 from by omega]
  erw [runJvmResFast_step_nonbranch_nonret rfl (by intro h; cases h) rfl]
  rw [show f + 19 = (f + 18) + 1 from by omega]
  erw [runJvmResFast_step_nonbranch_nonret rfl (by intro h; cases h) rfl]
  rw [show f + 18 = (f + 17) + 1 from by omega]
  erw [runJvmResFast_step_nonbranch_nonret rfl (by intro h; cases h) rfl]
  dsimp only [jh1, uiObj, Jvm.JvmHeap.alloc]
  rw [show (1107 + 1 + 1 + 1 : Nat) = 1110 from rfl]
  rw [show (errTailInstrs 17 18 20).append (f_Algorithm_deserializeMacrocell_loop_prog.drop 1127) =
    f_Algorithm_deserializeMacrocell_loop_prog.drop 1110 from by rw [hdropTail]; rfl]
  exact htailEq f

private theorem step_deserLoop_parseNode_level4 {locs : Nat → JvmVal}
    {lines : Array String} {numLines i lineLen : UInt32} {bytesAddr : Nat}
    {nodes : Algorithm.GrowBuf Algorithm.MacroCell} {leaves : Algorithm.GrowBuf UInt64}
    {isLeaf : Algorithm.GrowBuf Bool} {warns : Algorithm.GrowBuf Algorithm.MacrocellWarning}
    {nl : Algorithm.MCNodeLine} {line : String} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (h0 : locs 0 = .strArr lines) (h1 : locs 1 = .i32 numLines) (h2 : locs 2 = .i32 i)
    (h12 : mcNodes? (locs 12) = some nodes) (h13 : mcLeaves? (locs 13) = some leaves)
    (h14 : mcIsLeaf? (locs 14) = some isLeaf) (h15 : locs 15 = .ext (.mcWarnGrowBuf warns))
    (h16 : locs 16 = .str line) (h17 : locs 17 = .heapRef bytesAddr) (h18 : locs 18 = .i32 lineLen)
    (h24 : locs 24 = .i32 nl.nw) (h25 : locs 25 = .i32 nl.nwStart) (h26 : locs 26 = .i32 nl.nwEnd)
    (h27 : locs 27 = .i32 nl.ne) (h28 : locs 28 = .i32 nl.neStart) (h29 : locs 29 = .i32 nl.neEnd)
    (h30 : locs 30 = .i32 nl.sw) (h31 : locs 31 = .i32 nl.swStart) (h32 : locs 32 = .i32 nl.swEnd)
    (h33 : locs 33 = .i32 nl.se) (h34 : locs 34 = .i32 nl.seStart) (h35 : locs 35 = .i32 nl.seEnd)
    (hstat : jh.statics = []) :
    match Algorithm.macrocellLeafChild leaves isLeaf nl.nw with
    | none =>
      let enc := encodeMacrocellResult jh
        ⟨.unexpectedNodeId line i nl.nwStart nl.nwEnd, warns.toArray, Algorithm.emptyLevel4⟩
      ∃ pc' locs',
        ∀ f, runJvmResFast (f + 34) f_Algorithm_deserializeMacrocell_loop_prog 686
            (f_Algorithm_deserializeMacrocell_loop_prog.drop 686) ⟨686, [], locs, jh, hp⟩ =
          some (enc.1, ⟨pc', [enc.1], locs', enc.2, hp⟩)
    | some c1 =>
      match Algorithm.macrocellLeafChild leaves isLeaf nl.ne with
      | none =>
        let enc := encodeMacrocellResult jh
          ⟨.unexpectedNodeId line i nl.neStart nl.neEnd, warns.toArray, Algorithm.emptyLevel4⟩
        ∃ pc' locs',
          ∀ f, runJvmResFast (f + 41) f_Algorithm_deserializeMacrocell_loop_prog 686
              (f_Algorithm_deserializeMacrocell_loop_prog.drop 686) ⟨686, [], locs, jh, hp⟩ =
            some (enc.1, ⟨pc', [enc.1], locs', enc.2, hp⟩)
      | some c2 =>
        match Algorithm.macrocellLeafChild leaves isLeaf nl.sw with
        | none =>
          let enc := encodeMacrocellResult jh
            ⟨.unexpectedNodeId line i nl.swStart nl.swEnd, warns.toArray, Algorithm.emptyLevel4⟩
          ∃ pc' locs',
            ∀ f, runJvmResFast (f + 48) f_Algorithm_deserializeMacrocell_loop_prog 686
                (f_Algorithm_deserializeMacrocell_loop_prog.drop 686) ⟨686, [], locs, jh, hp⟩ =
              some (enc.1, ⟨pc', [enc.1], locs', enc.2, hp⟩)
        | some c3 =>
          match Algorithm.macrocellLeafChild leaves isLeaf nl.se with
          | none =>
            let enc := encodeMacrocellResult jh
              ⟨.unexpectedNodeId line i nl.seStart nl.seEnd, warns.toArray, Algorithm.emptyLevel4⟩
            ∃ pc' locs',
              ∀ f, runJvmResFast (f + 55) f_Algorithm_deserializeMacrocell_loop_prog 686
                  (f_Algorithm_deserializeMacrocell_loop_prog.drop 686) ⟨686, [], locs, jh, hp⟩ =
                some (enc.1, ⟨pc', [enc.1], locs', enc.2, hp⟩)
          | some c4 =>
            ∃ locs',
              locs' 15 = .ext (.mcWarnGrowBuf warns) ∧
              DeserLoopLocs locs' lines numLines (i + 1) false bytesAddr lineLen 0 0 0 0 0
                (nodes.push (Algorithm.makeLevel4Node c1 c2 c3 c4)) (leaves.push 0) (isLeaf.push false) warns ∧
              ∀ f, runJvmResFast (f + 122) f_Algorithm_deserializeMacrocell_loop_prog 686
                  (f_Algorithm_deserializeMacrocell_loop_prog.drop 686) ⟨686, [], locs, jh, hp⟩ =
                runJvmResFast f f_Algorithm_deserializeMacrocell_loop_prog 6
                  (f_Algorithm_deserializeMacrocell_loop_prog.drop 6) ⟨6, [], locs', jh, hp⟩ := by
  have hd0 : f_Algorithm_deserializeMacrocell_loop_prog.drop 686 =
      leafChildInstrs 686 24 25 26 36 37 38 40 ++
      (leafChildInstrs 720 27 28 29 37 38 39 41 ++
       leafChildInstrs 754 30 31 32 38 39 40 42 ++
       leafChildInstrs 788 33 34 35 39 40 41 43 ++
       f_Algorithm_deserializeMacrocell_loop_prog.drop 822) := by
    rw [deserLoop_drop_686]; simp only [List.append_assoc]
  have hd1 : f_Algorithm_deserializeMacrocell_loop_prog.drop 720 =
      leafChildInstrs 720 27 28 29 37 38 39 41 ++
      (leafChildInstrs 754 30 31 32 38 39 40 42 ++
       leafChildInstrs 788 33 34 35 39 40 41 43 ++
       f_Algorithm_deserializeMacrocell_loop_prog.drop 822) := by
    rw [show (720 : Nat) = 686 + 34 from rfl, drop_drop_add, hd0]; rfl
  have hd2 : f_Algorithm_deserializeMacrocell_loop_prog.drop 754 =
      leafChildInstrs 754 30 31 32 38 39 40 42 ++
      (leafChildInstrs 788 33 34 35 39 40 41 43 ++
       f_Algorithm_deserializeMacrocell_loop_prog.drop 822) := by
    rw [show (754 : Nat) = 720 + 34 from rfl, drop_drop_add, hd1]; rfl
  have hd3 : f_Algorithm_deserializeMacrocell_loop_prog.drop 788 =
      leafChildInstrs 788 33 34 35 39 40 41 43 ++
      f_Algorithm_deserializeMacrocell_loop_prog.drop 822 := by
    rw [show (788 : Nat) = 754 + 34 from rfl, drop_drop_add, hd2]; rfl
  have hlc0 := step_deserLoop_leafChild (hp := hp) hd0 h2 h13 h14 h15 h16 h24 h25 h26
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hstat
  cases hc0 : Algorithm.macrocellLeafChild leaves isLeaf nl.nw with
  | none =>
    rw [hc0] at hlc0; exact hlc0
  | some c1 =>
    rw [hc0] at hlc0
    rcases hlc0 with ⟨l1, h1_36, hp1, hs1⟩
    have hlc1 := step_deserLoop_leafChild (locs := l1) (hp := hp) hd1
      (by rw [hp1 2 (by omega)]; exact h2) (by rw [hp1 13 (by omega)]; exact h13)
      (by rw [hp1 14 (by omega)]; exact h14) (by rw [hp1 15 (by omega)]; exact h15)
      (by rw [hp1 16 (by omega)]; exact h16) (by rw [hp1 27 (by omega)]; exact h27)
      (by rw [hp1 28 (by omega)]; exact h28) (by rw [hp1 29 (by omega)]; exact h29)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hstat
    cases hc1 : Algorithm.macrocellLeafChild leaves isLeaf nl.ne with
    | none =>
      rw [hc1] at hlc1
      rcases hlc1 with ⟨pc', locs', heq⟩
      refine ⟨pc', locs', fun f => ?_⟩
      rw [show f + 41 = (f + 34) + 7 from by omega, hs1, heq]
    | some c2 =>
      rw [hc1] at hlc1
      rcases hlc1 with ⟨l2, h2_37, hp2, hs2⟩
      have hlc2 := step_deserLoop_leafChild (locs := l2) (hp := hp) hd2
        (by rw [hp2 2 (by omega), hp1 2 (by omega)]; exact h2)
        (by rw [hp2 13 (by omega), hp1 13 (by omega)]; exact h13)
        (by rw [hp2 14 (by omega), hp1 14 (by omega)]; exact h14)
        (by rw [hp2 15 (by omega), hp1 15 (by omega)]; exact h15)
        (by rw [hp2 16 (by omega), hp1 16 (by omega)]; exact h16)
        (by rw [hp2 30 (by omega), hp1 30 (by omega)]; exact h30)
        (by rw [hp2 31 (by omega), hp1 31 (by omega)]; exact h31)
        (by rw [hp2 32 (by omega), hp1 32 (by omega)]; exact h32)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hstat
      cases hc2 : Algorithm.macrocellLeafChild leaves isLeaf nl.sw with
      | none =>
        rw [hc2] at hlc2
        rcases hlc2 with ⟨pc', locs', heq⟩
        refine ⟨pc', locs', fun f => ?_⟩
        rw [show f + 48 = (f + 41) + 7 from by omega, hs1,
          show f + 41 = (f + 34) + 7 from by omega, hs2, heq]
      | some c3 =>
        rw [hc2] at hlc2
        rcases hlc2 with ⟨l3, h3_38, hp3, hs3⟩
        have hlc3 := step_deserLoop_leafChild (locs := l3) (hp := hp) hd3
          (by rw [hp3 2 (by omega), hp2 2 (by omega), hp1 2 (by omega)]; exact h2)
          (by rw [hp3 13 (by omega), hp2 13 (by omega), hp1 13 (by omega)]; exact h13)
          (by rw [hp3 14 (by omega), hp2 14 (by omega), hp1 14 (by omega)]; exact h14)
          (by rw [hp3 15 (by omega), hp2 15 (by omega), hp1 15 (by omega)]; exact h15)
          (by rw [hp3 16 (by omega), hp2 16 (by omega), hp1 16 (by omega)]; exact h16)
          (by rw [hp3 33 (by omega), hp2 33 (by omega), hp1 33 (by omega)]; exact h33)
          (by rw [hp3 34 (by omega), hp2 34 (by omega), hp1 34 (by omega)]; exact h34)
          (by rw [hp3 35 (by omega), hp2 35 (by omega), hp1 35 (by omega)]; exact h35)
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hstat
        cases hc3 : Algorithm.macrocellLeafChild leaves isLeaf nl.se with
        | none =>
          rw [hc3] at hlc3
          rcases hlc3 with ⟨pc', locs', heq⟩
          refine ⟨pc', locs', fun f => ?_⟩
          rw [show f + 55 = (f + 48) + 7 from by omega, hs1,
            show f + 48 = (f + 41) + 7 from by omega, hs2,
            show f + 41 = (f + 34) + 7 from by omega, hs3, heq]
        | some c4 =>
          rw [hc3] at hlc3
          rcases hlc3 with ⟨l4, h4_39, hp4, hs4⟩
          have hl4_0 : l4 0 = .strArr lines := by
            rw [hp4 0 (by omega), hp3 0 (by omega), hp2 0 (by omega), hp1 0 (by omega)]; exact h0
          have hl4_1 : l4 1 = .i32 numLines := by
            rw [hp4 1 (by omega), hp3 1 (by omega), hp2 1 (by omega), hp1 1 (by omega)]; exact h1
          have hl4_2 : l4 2 = .i32 i := by
            rw [hp4 2 (by omega), hp3 2 (by omega), hp2 2 (by omega), hp1 2 (by omega)]; exact h2
          have hl4_12 : mcNodes? (l4 12) = some nodes := by
            rw [hp4 12 (by omega), hp3 12 (by omega), hp2 12 (by omega), hp1 12 (by omega)]; exact h12
          have hl4_13 : mcLeaves? (l4 13) = some leaves := by
            rw [hp4 13 (by omega), hp3 13 (by omega), hp2 13 (by omega), hp1 13 (by omega)]; exact h13
          have hl4_14 : mcIsLeaf? (l4 14) = some isLeaf := by
            rw [hp4 14 (by omega), hp3 14 (by omega), hp2 14 (by omega), hp1 14 (by omega)]; exact h14
          have hl4_15 : l4 15 = .ext (.mcWarnGrowBuf warns) := by
            rw [hp4 15 (by omega), hp3 15 (by omega), hp2 15 (by omega), hp1 15 (by omega)]; exact h15
          have hl4_17 : l4 17 = .heapRef bytesAddr := by
            rw [hp4 17 (by omega), hp3 17 (by omega), hp2 17 (by omega), hp1 17 (by omega)]; exact h17
          have hl4_18 : l4 18 = .i32 lineLen := by
            rw [hp4 18 (by omega), hp3 18 (by omega), hp2 18 (by omega), hp1 18 (by omega)]; exact h18
          have hl4_36 : l4 36 = .boxedULong c1 := by
            rw [hp4 36 (by omega), hp3 36 (by omega), hp2 36 (by omega)]; exact h1_36
          have hl4_37 : l4 37 = .boxedULong c2 := by
            rw [hp4 37 (by omega), hp3 37 (by omega)]; exact h2_37
          have hl4_38 : l4 38 = .boxedULong c3 := by
            rw [hp4 38 (by omega)]; exact h3_38
          have hl4_39 : l4 39 = .boxedULong c4 := h4_39
          have hd827 : f_Algorithm_deserializeMacrocell_loop_prog.drop 827 =
              unboxULongInstrs 827 36 ++
              (unboxULongInstrs 841 37 ++ unboxULongInstrs 855 38 ++ unboxULongInstrs 869 39 ++
               f_Algorithm_deserializeMacrocell_loop_prog.drop 883) := by
            rw [show (827 : Nat) = 822 + 5 from rfl, drop_drop_add, deserLoop_drop_822]
            simp only [List.append_assoc]; rfl
          have hd841 : f_Algorithm_deserializeMacrocell_loop_prog.drop 841 =
              unboxULongInstrs 841 37 ++
              (unboxULongInstrs 855 38 ++ unboxULongInstrs 869 39 ++
               f_Algorithm_deserializeMacrocell_loop_prog.drop 883) := by
            rw [show (841 : Nat) = 827 + 14 from rfl, drop_drop_add, hd827]; rfl
          have hd855 : f_Algorithm_deserializeMacrocell_loop_prog.drop 855 =
              unboxULongInstrs 855 38 ++
              (unboxULongInstrs 869 39 ++ f_Algorithm_deserializeMacrocell_loop_prog.drop 883) := by
            rw [show (855 : Nat) = 841 + 14 from rfl, drop_drop_add, hd841]; rfl
          have hd869 : f_Algorithm_deserializeMacrocell_loop_prog.drop 869 =
              unboxULongInstrs 869 39 ++ f_Algorithm_deserializeMacrocell_loop_prog.drop 883 := by
            rw [show (869 : Nat) = 855 + 14 from rfl, drop_drop_add, hd855]; rfl
          let l5 := setLocal l4 40 (.i32 (i + 1))
          rcases step_deserLoop_unboxULong (locs := l5) (stk := []) hd827
              (by dsimp only [l5]; rw [setLocal_ne_eq (decide_eq_false (by omega)), hl4_36])
              (by omega) with ⟨u1, hpu1, hsu1⟩
          rcases step_deserLoop_unboxULong (locs := u1) (stk := [.i64 c1]) hd841
              (by rw [hpu1 37 (by omega)]; dsimp only [l5]
                  rw [setLocal_ne_eq (decide_eq_false (by omega)), hl4_37])
              (by omega) with ⟨u2, hpu2, hsu2⟩
          rcases step_deserLoop_unboxULong (locs := u2) (stk := [.i64 c2, .i64 c1]) hd855
              (by rw [hpu2 38 (by omega), hpu1 38 (by omega)]; dsimp only [l5]
                  rw [setLocal_ne_eq (decide_eq_false (by omega)), hl4_38])
              (by omega) with ⟨u3, hpu3, hsu3⟩
          rcases step_deserLoop_unboxULong (locs := u3) (stk := [.i64 c3, .i64 c2, .i64 c1]) hd869
              (by rw [hpu3 39 (by omega), hpu2 39 (by omega), hpu1 39 (by omega)]; dsimp only [l5]
                  rw [setLocal_ne_eq (decide_eq_false (by omega)), hl4_39])
              (by omega) with ⟨u4, hpu4, hsu4⟩
          have hu4_0 : u4 0 = .strArr lines := by
            rw [hpu4 0 (by omega), hpu3 0 (by omega), hpu2 0 (by omega), hpu1 0 (by omega)]
            dsimp only [l5]; rw [setLocal_ne_eq (decide_eq_false (by omega)), hl4_0]
          have hu4_1 : u4 1 = .i32 numLines := by
            rw [hpu4 1 (by omega), hpu3 1 (by omega), hpu2 1 (by omega), hpu1 1 (by omega)]
            dsimp only [l5]; rw [setLocal_ne_eq (decide_eq_false (by omega)), hl4_1]
          have hu4_12 : mcNodes? (u4 12) = some nodes := by
            rw [hpu4 12 (by omega), hpu3 12 (by omega), hpu2 12 (by omega), hpu1 12 (by omega)]
            dsimp only [l5]; rw [setLocal_ne_eq (decide_eq_false (by omega)), hl4_12]
          have hu4_13 : mcLeaves? (u4 13) = some leaves := by
            rw [hpu4 13 (by omega), hpu3 13 (by omega), hpu2 13 (by omega), hpu1 13 (by omega)]
            dsimp only [l5]; rw [setLocal_ne_eq (decide_eq_false (by omega)), hl4_13]
          have hu4_14 : mcIsLeaf? (u4 14) = some isLeaf := by
            rw [hpu4 14 (by omega), hpu3 14 (by omega), hpu2 14 (by omega), hpu1 14 (by omega)]
            dsimp only [l5]; rw [setLocal_ne_eq (decide_eq_false (by omega)), hl4_14]
          have hu4_15 : u4 15 = .ext (.mcWarnGrowBuf warns) := by
            rw [hpu4 15 (by omega), hpu3 15 (by omega), hpu2 15 (by omega), hpu1 15 (by omega)]
            dsimp only [l5]; rw [setLocal_ne_eq (decide_eq_false (by omega)), hl4_15]
          have hu4_17 : u4 17 = .heapRef bytesAddr := by
            rw [hpu4 17 (by omega), hpu3 17 (by omega), hpu2 17 (by omega), hpu1 17 (by omega)]
            dsimp only [l5]; rw [setLocal_ne_eq (decide_eq_false (by omega)), hl4_17]
          have hu4_18 : u4 18 = .i32 lineLen := by
            rw [hpu4 18 (by omega), hpu3 18 (by omega), hpu2 18 (by omega), hpu1 18 (by omega)]
            dsimp only [l5]; rw [setLocal_ne_eq (decide_eq_false (by omega)), hl4_18]
          have hu4_40 : u4 40 = .i32 (i + 1) := by
            rw [hpu4 40 (by omega), hpu3 40 (by omega), hpu2 40 (by omega), hpu1 40 (by omega)]
            dsimp only [l5]; rw [setLocal_eq_val (decide_eq_true rfl)]
          let mc4 := Algorithm.makeLevel4Node c1 c2 c3 c4
          let locs' :=
            setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
              (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
                (setLocal (setLocal u4 41 (.ext (.mc mc4)))
                  42 (.ext (.mcGrowBuf (nodes.push mc4))))
                  43 (.ext (.u64GrowBuf (leaves.push 0))))
                  44 (.ext (.boolGrowBuf (isLeaf.push false))))
                  45 (u4 0)) 46 (u4 1)) 47 (u4 15))
                  0 (u4 0)) 1 (u4 1)) 2 (u4 40)) 3 (.i32 0)) 4 (u4 17)) 5 (u4 18))
                  6 (.i32 0)) 7 (.i32 0)) 8 (.i32 0)) 9 (.i32 0)) 10 (.i64 0))
                  12 (.ext (.mcGrowBuf (nodes.push mc4))))
                  13 (.ext (.u64GrowBuf (leaves.push 0))))
                  14 (.ext (.boolGrowBuf (isLeaf.push false))))
                  15 (u4 15)
          refine ⟨locs', hu4_15,
            ⟨hu4_0, hu4_1, hu4_40, rfl, hu4_17, hu4_18, rfl, rfl, rfl, rfl, rfl,
             rfl, rfl, rfl, by dsimp only [locs']; change mcWarns? (u4 15) = _; rw [hu4_15]; rfl⟩, fun f => ?_⟩
          rw [show f + 122 = (f + 115) + 7 from by omega, hs1]
          rw [show f + 115 = (f + 108) + 7 from by omega, hs2]
          rw [show f + 108 = (f + 101) + 7 from by omega, hs3]
          rw [show f + 101 = (f + 94) + 7 from by omega, hs4]
          rw [deserLoop_drop_822]
          rw [show f + 94 = (f + 92) + 2 from by omega]; chunk 2; rw [hl4_2]
          rw [show f + 92 = (f + 91) + 1 from by omega]; chunk 1
          rw [show f + 91 = (f + 90) + 1 from by omega]
          erw [runJvmResFast_invokestatic_step stepStatic_uintCtor5a]
          rw [show f + 90 = (f + 89) + 1 from by omega]; chunk 1
          rw [show (((((unboxULongInstrs 827 36).append (unboxULongInstrs 841 37)).append
                (unboxULongInstrs 855 38)).append (unboxULongInstrs 869 39)).append
                (f_Algorithm_deserializeMacrocell_loop_prog.drop 883)) =
              f_Algorithm_deserializeMacrocell_loop_prog.drop 827 from by
            rw [hd827]; simp only [List.append_assoc]; rfl]
          rw [show f + 89 = (f + 80) + 9 from by omega, hsu1]
          rw [show f + 80 = (f + 71) + 9 from by omega, hsu2]
          rw [show f + 71 = (f + 62) + 9 from by omega, hsu3]
          rw [show f + 62 = (f + 53) + 9 from by omega, hsu4]
          rw [deserLoop_drop_883]
          rw [show f + 53 = (f + 52) + 1 from by omega]
          rw [runJvmResFast_invokestatic_step stepStatic_mcMakeLevel4Node_heap]
          rw [show f + 52 = (f + 49) + 3 from by omega]; chunk 3
          rw [show f + 49 = (f + 48) + 1 from by omega]
          rw [runJvmResFast_invokestatic_step (stepStatic_growBufPush_mc hu4_12)]
          rw [show f + 48 = (f + 45) + 3 from by omega]; chunk 3
          rw [show f + 45 = (f + 44) + 1 from by omega]
          rw [runJvmResFast_invokestatic_step stepStatic_ulongBox]
          rw [show f + 44 = (f + 43) + 1 from by omega]
          rw [runJvmResFast_invokestatic_step (stepStatic_growBufPush_u64 hu4_13)]
          rw [show f + 43 = (f + 40) + 3 from by omega]; chunk 3
          rw [show f + 40 = (f + 39) + 1 from by omega]
          rw [runJvmResFast_invokestatic_step stepStatic_booleanValueOf]
          rw [show f + 39 = (f + 38) + 1 from by omega]
          rw [runJvmResFast_invokestatic_step (stepStatic_growBufPush_bool hu4_14)]
          rw [show f + 38 = (f + 30) + 8 from by omega]; chunk 8
          rw [show f + 30 = (f + 22) + 8 from by omega]; chunk 8
          rw [show f + 22 = (f + 14) + 8 from by omega]; chunk 8
          rw [show f + 14 = (f + 6) + 8 from by omega]; chunk 8
          rw [show f + 6 = (f + 1) + 5 from by omega]; chunk 5
          rw [runJvmResFast_goto]
          have h00 : ((0 : UInt32) != 0) = false := rfl
          rw [h00]

private theorem step_deserLoop_parseNode_cell {locs : Nat → JvmVal}
    {lines : Array String} {numLines i lineLen : UInt32} {bytesAddr : Nat}
    {nodes : Algorithm.GrowBuf Algorithm.MacroCell} {leaves : Algorithm.GrowBuf UInt64}
    {isLeaf : Algorithm.GrowBuf Bool} {warns : Algorithm.GrowBuf Algorithm.MacrocellWarning}
    {nl : Algorithm.MCNodeLine} {line : String} {emptySub : Algorithm.MacroCell}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (h0 : locs 0 = .strArr lines) (h1 : locs 1 = .i32 numLines) (h2 : locs 2 = .i32 i)
    (h12 : mcNodes? (locs 12) = some nodes) (h13 : mcLeaves? (locs 13) = some leaves)
    (h14 : mcIsLeaf? (locs 14) = some isLeaf) (h15 : locs 15 = .ext (.mcWarnGrowBuf warns))
    (h16 : locs 16 = .str line) (h17 : locs 17 = .heapRef bytesAddr) (h18 : locs 18 = .i32 lineLen)
    (h23 : locs 23 = .i32 nl.level)
    (h24 : locs 24 = .i32 nl.nw) (h25 : locs 25 = .i32 nl.nwStart) (h26 : locs 26 = .i32 nl.nwEnd)
    (h27 : locs 27 = .i32 nl.ne) (h28 : locs 28 = .i32 nl.neStart) (h29 : locs 29 = .i32 nl.neEnd)
    (h30 : locs 30 = .i32 nl.sw) (h31 : locs 31 = .i32 nl.swStart) (h32 : locs 32 = .i32 nl.swEnd)
    (h33 : locs 33 = .i32 nl.se) (h34 : locs 34 = .i32 nl.seStart) (h35 : locs 35 = .i32 nl.seEnd)
    (h36 : locs 36 = .ext (.mc emptySub))
    (hstat : jh.statics = []) :
    match Algorithm.macrocellCellChild nodes isLeaf nl.level emptySub nl.nw with
    | none =>
      let enc := encodeMacrocellResult jh
        ⟨.unexpectedNodeId line i nl.nwStart nl.nwEnd, warns.toArray, Algorithm.emptyLevel4⟩
      ∃ pc' locs',
        ∀ f, runJvmResFast (f + 36) f_Algorithm_deserializeMacrocell_loop_prog 480
            (f_Algorithm_deserializeMacrocell_loop_prog.drop 480) ⟨480, [], locs, jh, hp⟩ =
          some (enc.1, ⟨pc', [enc.1], locs', enc.2, hp⟩)
    | some c1 =>
      match Algorithm.macrocellCellChild nodes isLeaf nl.level emptySub nl.ne with
      | none =>
        let enc := encodeMacrocellResult jh
          ⟨.unexpectedNodeId line i nl.neStart nl.neEnd, warns.toArray, Algorithm.emptyLevel4⟩
        ∃ pc' locs',
          ∀ f, runJvmResFast (f + 45) f_Algorithm_deserializeMacrocell_loop_prog 480
              (f_Algorithm_deserializeMacrocell_loop_prog.drop 480) ⟨480, [], locs, jh, hp⟩ =
            some (enc.1, ⟨pc', [enc.1], locs', enc.2, hp⟩)
      | some c2 =>
        match Algorithm.macrocellCellChild nodes isLeaf nl.level emptySub nl.sw with
        | none =>
          let enc := encodeMacrocellResult jh
            ⟨.unexpectedNodeId line i nl.swStart nl.swEnd, warns.toArray, Algorithm.emptyLevel4⟩
          ∃ pc' locs',
            ∀ f, runJvmResFast (f + 54) f_Algorithm_deserializeMacrocell_loop_prog 480
                (f_Algorithm_deserializeMacrocell_loop_prog.drop 480) ⟨480, [], locs, jh, hp⟩ =
              some (enc.1, ⟨pc', [enc.1], locs', enc.2, hp⟩)
        | some c3 =>
          match Algorithm.macrocellCellChild nodes isLeaf nl.level emptySub nl.se with
          | none =>
            let enc := encodeMacrocellResult jh
              ⟨.unexpectedNodeId line i nl.seStart nl.seEnd, warns.toArray, Algorithm.emptyLevel4⟩
            ∃ pc' locs',
              ∀ f, runJvmResFast (f + 63) f_Algorithm_deserializeMacrocell_loop_prog 480
                  (f_Algorithm_deserializeMacrocell_loop_prog.drop 480) ⟨480, [], locs, jh, hp⟩ =
                some (enc.1, ⟨pc', [enc.1], locs', enc.2, hp⟩)
          | some c4 =>
            ∃ locs',
              locs' 15 = .ext (.mcWarnGrowBuf warns) ∧
              DeserLoopLocs locs' lines numLines (i + 1) false bytesAddr lineLen 0 0 0 0 0
                (nodes.push (Algorithm.makeCellNode c1 c2 c3 c4)) (leaves.push 0) (isLeaf.push false) warns ∧
              ∀ f, runJvmResFast (f + 98) f_Algorithm_deserializeMacrocell_loop_prog 480
                  (f_Algorithm_deserializeMacrocell_loop_prog.drop 480) ⟨480, [], locs, jh, hp⟩ =
                runJvmResFast f f_Algorithm_deserializeMacrocell_loop_prog 6
                  (f_Algorithm_deserializeMacrocell_loop_prog.drop 6) ⟨6, [], locs', jh, hp⟩ := by
  have hd0 : f_Algorithm_deserializeMacrocell_loop_prog.drop 480 =
      cellChildInstrs 480 24 25 26 37 38 39 41 ++
      (cellChildInstrs 516 27 28 29 38 39 40 42 ++
       cellChildInstrs 552 30 31 32 39 40 41 43 ++
       cellChildInstrs 588 33 34 35 40 41 42 44 ++
       f_Algorithm_deserializeMacrocell_loop_prog.drop 624) := by
    rw [deserLoop_drop_480]; simp only [List.append_assoc]
  have hd1 : f_Algorithm_deserializeMacrocell_loop_prog.drop 516 =
      cellChildInstrs 516 27 28 29 38 39 40 42 ++
      (cellChildInstrs 552 30 31 32 39 40 41 43 ++
       cellChildInstrs 588 33 34 35 40 41 42 44 ++
       f_Algorithm_deserializeMacrocell_loop_prog.drop 624) := by
    rw [show (516 : Nat) = 480 + 36 from rfl, drop_drop_add, hd0]; rfl
  have hd2 : f_Algorithm_deserializeMacrocell_loop_prog.drop 552 =
      cellChildInstrs 552 30 31 32 39 40 41 43 ++
      (cellChildInstrs 588 33 34 35 40 41 42 44 ++
       f_Algorithm_deserializeMacrocell_loop_prog.drop 624) := by
    rw [show (552 : Nat) = 516 + 36 from rfl, drop_drop_add, hd1]; rfl
  have hd3 : f_Algorithm_deserializeMacrocell_loop_prog.drop 588 =
      cellChildInstrs 588 33 34 35 40 41 42 44 ++
      f_Algorithm_deserializeMacrocell_loop_prog.drop 624 := by
    rw [show (588 : Nat) = 552 + 36 from rfl, drop_drop_add, hd2]; rfl
  have hcc0 := step_deserLoop_cellChild (hp := hp) hd0 h2 h12 h14 h15 h16 h23 h36 h24 h25 h26
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hstat
  cases hc0 : Algorithm.macrocellCellChild nodes isLeaf nl.level emptySub nl.nw with
  | none => rw [hc0] at hcc0; exact hcc0
  | some c1 =>
    rw [hc0] at hcc0
    rcases hcc0 with ⟨l1, h1_37, hp1, hs1⟩
    have hcc1 := step_deserLoop_cellChild (locs := l1) (hp := hp) hd1
      (by rw [hp1 2 (by omega)]; exact h2) (by rw [hp1 12 (by omega)]; exact h12)
      (by rw [hp1 14 (by omega)]; exact h14) (by rw [hp1 15 (by omega)]; exact h15)
      (by rw [hp1 16 (by omega)]; exact h16) (by rw [hp1 23 (by omega)]; exact h23)
      (by rw [hp1 36 (by omega)]; exact h36) (by rw [hp1 27 (by omega)]; exact h27)
      (by rw [hp1 28 (by omega)]; exact h28) (by rw [hp1 29 (by omega)]; exact h29)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hstat
    cases hc1 : Algorithm.macrocellCellChild nodes isLeaf nl.level emptySub nl.ne with
    | none =>
      rw [hc1] at hcc1
      rcases hcc1 with ⟨pc', locs', heq⟩
      refine ⟨pc', locs', fun f => ?_⟩
      rw [show f + 45 = (f + 36) + 9 from by omega, hs1, heq]
    | some c2 =>
      rw [hc1] at hcc1
      rcases hcc1 with ⟨l2, h2_38, hp2, hs2⟩
      have hcc2 := step_deserLoop_cellChild (locs := l2) (hp := hp) hd2
        (by rw [hp2 2 (by omega), hp1 2 (by omega)]; exact h2)
        (by rw [hp2 12 (by omega), hp1 12 (by omega)]; exact h12)
        (by rw [hp2 14 (by omega), hp1 14 (by omega)]; exact h14)
        (by rw [hp2 15 (by omega), hp1 15 (by omega)]; exact h15)
        (by rw [hp2 16 (by omega), hp1 16 (by omega)]; exact h16)
        (by rw [hp2 23 (by omega), hp1 23 (by omega)]; exact h23)
        (by rw [hp2 36 (by omega), hp1 36 (by omega)]; exact h36)
        (by rw [hp2 30 (by omega), hp1 30 (by omega)]; exact h30)
        (by rw [hp2 31 (by omega), hp1 31 (by omega)]; exact h31)
        (by rw [hp2 32 (by omega), hp1 32 (by omega)]; exact h32)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hstat
      cases hc2 : Algorithm.macrocellCellChild nodes isLeaf nl.level emptySub nl.sw with
      | none =>
        rw [hc2] at hcc2
        rcases hcc2 with ⟨pc', locs', heq⟩
        refine ⟨pc', locs', fun f => ?_⟩
        rw [show f + 54 = (f + 45) + 9 from by omega, hs1,
          show f + 45 = (f + 36) + 9 from by omega, hs2, heq]
      | some c3 =>
        rw [hc2] at hcc2
        rcases hcc2 with ⟨l3, h3_39, hp3, hs3⟩
        have hcc3 := step_deserLoop_cellChild (locs := l3) (hp := hp) hd3
          (by rw [hp3 2 (by omega), hp2 2 (by omega), hp1 2 (by omega)]; exact h2)
          (by rw [hp3 12 (by omega), hp2 12 (by omega), hp1 12 (by omega)]; exact h12)
          (by rw [hp3 14 (by omega), hp2 14 (by omega), hp1 14 (by omega)]; exact h14)
          (by rw [hp3 15 (by omega), hp2 15 (by omega), hp1 15 (by omega)]; exact h15)
          (by rw [hp3 16 (by omega), hp2 16 (by omega), hp1 16 (by omega)]; exact h16)
          (by rw [hp3 23 (by omega), hp2 23 (by omega), hp1 23 (by omega)]; exact h23)
          (by rw [hp3 36 (by omega), hp2 36 (by omega), hp1 36 (by omega)]; exact h36)
          (by rw [hp3 33 (by omega), hp2 33 (by omega), hp1 33 (by omega)]; exact h33)
          (by rw [hp3 34 (by omega), hp2 34 (by omega), hp1 34 (by omega)]; exact h34)
          (by rw [hp3 35 (by omega), hp2 35 (by omega), hp1 35 (by omega)]; exact h35)
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hstat
        cases hc3 : Algorithm.macrocellCellChild nodes isLeaf nl.level emptySub nl.se with
        | none =>
          rw [hc3] at hcc3
          rcases hcc3 with ⟨pc', locs', heq⟩
          refine ⟨pc', locs', fun f => ?_⟩
          rw [show f + 63 = (f + 54) + 9 from by omega, hs1,
            show f + 54 = (f + 45) + 9 from by omega, hs2,
            show f + 45 = (f + 36) + 9 from by omega, hs3, heq]
        | some c4 =>
          rw [hc3] at hcc3
          rcases hcc3 with ⟨l4, h4_40, hp4, hs4⟩
          have hl4_0 : l4 0 = .strArr lines := by
            rw [hp4 0 (by omega), hp3 0 (by omega), hp2 0 (by omega), hp1 0 (by omega)]; exact h0
          have hl4_1 : l4 1 = .i32 numLines := by
            rw [hp4 1 (by omega), hp3 1 (by omega), hp2 1 (by omega), hp1 1 (by omega)]; exact h1
          have hl4_2 : l4 2 = .i32 i := by
            rw [hp4 2 (by omega), hp3 2 (by omega), hp2 2 (by omega), hp1 2 (by omega)]; exact h2
          have hl4_12 : mcNodes? (l4 12) = some nodes := by
            rw [hp4 12 (by omega), hp3 12 (by omega), hp2 12 (by omega), hp1 12 (by omega)]; exact h12
          have hl4_13 : mcLeaves? (l4 13) = some leaves := by
            rw [hp4 13 (by omega), hp3 13 (by omega), hp2 13 (by omega), hp1 13 (by omega)]; exact h13
          have hl4_14 : mcIsLeaf? (l4 14) = some isLeaf := by
            rw [hp4 14 (by omega), hp3 14 (by omega), hp2 14 (by omega), hp1 14 (by omega)]; exact h14
          have hl4_15 : l4 15 = .ext (.mcWarnGrowBuf warns) := by
            rw [hp4 15 (by omega), hp3 15 (by omega), hp2 15 (by omega), hp1 15 (by omega)]; exact h15
          have hl4_17 : l4 17 = .heapRef bytesAddr := by
            rw [hp4 17 (by omega), hp3 17 (by omega), hp2 17 (by omega), hp1 17 (by omega)]; exact h17
          have hl4_18 : l4 18 = .i32 lineLen := by
            rw [hp4 18 (by omega), hp3 18 (by omega), hp2 18 (by omega), hp1 18 (by omega)]; exact h18
          have hl4_37 : l4 37 = .ext (.mc c1) := by
            rw [hp4 37 (by omega), hp3 37 (by omega), hp2 37 (by omega)]; exact h1_37
          have hl4_38 : l4 38 = .ext (.mc c2) := by
            rw [hp4 38 (by omega), hp3 38 (by omega)]; exact h2_38
          have hl4_39 : l4 39 = .ext (.mc c3) := by
            rw [hp4 39 (by omega)]; exact h3_39
          have hl4_40 : l4 40 = .ext (.mc c4) := h4_40
          let mcCell := Algorithm.makeCellNode c1 c2 c3 c4
          let locs' :=
            setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
              (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
                (setLocal (setLocal (setLocal l4 41 (.i32 (i + 1))) 42 (.ext (.mc mcCell)))
                  43 (.ext (.mcGrowBuf (nodes.push mcCell))))
                  44 (.ext (.u64GrowBuf (leaves.push 0))))
                  45 (.ext (.boolGrowBuf (isLeaf.push false))))
                  46 (l4 0)) 47 (l4 1)) 48 (l4 15))
                  0 (l4 0)) 1 (l4 1)) 2 (.i32 (i + 1))) 3 (.i32 0)) 4 (l4 17)) 5 (l4 18))
                  6 (.i32 0)) 7 (.i32 0)) 8 (.i32 0)) 9 (.i32 0)) 10 (.i64 0))
                  12 (.ext (.mcGrowBuf (nodes.push mcCell))))
                  13 (.ext (.u64GrowBuf (leaves.push 0))))
                  14 (.ext (.boolGrowBuf (isLeaf.push false))))
                  15 (l4 15)
          refine ⟨locs', by dsimp only [locs']; change l4 15 = _; rw [hl4_15],
            ⟨hl4_0, hl4_1, rfl, rfl, hl4_17, hl4_18, rfl, rfl, rfl, rfl, rfl,
             rfl, rfl, rfl, by dsimp only [locs']; change mcWarns? (l4 15) = _; rw [hl4_15]; rfl⟩,
            fun f => ?_⟩
          rw [show f + 98 = (f + 89) + 9 from by omega, hs1]
          rw [show f + 89 = (f + 80) + 9 from by omega, hs2]
          rw [show f + 80 = (f + 71) + 9 from by omega, hs3]
          rw [show f + 71 = (f + 62) + 9 from by omega, hs4]
          rw [deserLoop_drop_624]
          rw [show f + 62 = (f + 60) + 2 from by omega]; chunk 2; rw [hl4_2]
          rw [show f + 60 = (f + 59) + 1 from by omega]; chunk 1
          rw [show f + 59 = (f + 58) + 1 from by omega]
          rw [runJvmResFast_invokestatic_step stepStatic_uintCtor5a]
          rw [show f + 58 = (f + 53) + 5 from by omega]; chunk 5
          rw [hl4_37, hl4_38, hl4_39, hl4_40]
          rw [show f + 53 = (f + 52) + 1 from by omega]
          rw [runJvmResFast_invokestatic_step stepStatic_makeCellNode]
          rw [show f + 52 = (f + 49) + 3 from by omega]; chunk 3
          rw [show f + 49 = (f + 48) + 1 from by omega]
          rw [runJvmResFast_invokestatic_step (stepStatic_growBufPush_mc hl4_12)]
          rw [show f + 48 = (f + 45) + 3 from by omega]; chunk 3
          rw [show f + 45 = (f + 44) + 1 from by omega]
          rw [runJvmResFast_invokestatic_step stepStatic_ulongBox]
          rw [show f + 44 = (f + 43) + 1 from by omega]
          rw [runJvmResFast_invokestatic_step (stepStatic_growBufPush_u64 hl4_13)]
          rw [show f + 43 = (f + 40) + 3 from by omega]; chunk 3
          rw [show f + 40 = (f + 39) + 1 from by omega]
          rw [runJvmResFast_invokestatic_step stepStatic_booleanValueOf]
          rw [show f + 39 = (f + 38) + 1 from by omega]
          rw [runJvmResFast_invokestatic_step (stepStatic_growBufPush_bool hl4_14)]
          rw [show f + 38 = (f + 30) + 8 from by omega]; chunk 8
          rw [show f + 30 = (f + 22) + 8 from by omega]; chunk 8
          rw [show f + 22 = (f + 14) + 8 from by omega]; chunk 8
          rw [show f + 14 = (f + 6) + 8 from by omega]; chunk 8
          rw [show f + 6 = (f + 1) + 5 from by omega]; chunk 5
          rw [runJvmResFast_goto]
          have h00 : ((0 : UInt32) != 0) = false := rfl
          rw [h00]

def parseNodeStepResult (line : String) (i : UInt32) (nl : Algorithm.MCNodeLine)
    (nodes : Algorithm.GrowBuf Algorithm.MacroCell) (leaves : Algorithm.GrowBuf UInt64)
    (isLeaf : Algorithm.GrowBuf Bool) (warns : Algorithm.GrowBuf Algorithm.MacrocellWarning) :
    (Algorithm.GrowBuf Algorithm.MacroCell × Algorithm.GrowBuf UInt64 × Algorithm.GrowBuf Bool) ⊕
      Algorithm.MacrocellResult :=
  if nl.level < 4 || nl.level > Algorithm.maxMacrocellLevel then
    .inr ⟨.unexpectedInput line i, warns.toArray, Algorithm.emptyLevel4⟩
  else if nl.level == 4 then
    match Algorithm.macrocellLeafChild leaves isLeaf nl.nw with
    | none => .inr ⟨.unexpectedNodeId line i nl.nwStart nl.nwEnd, warns.toArray, Algorithm.emptyLevel4⟩
    | some c1 =>
    match Algorithm.macrocellLeafChild leaves isLeaf nl.ne with
    | none => .inr ⟨.unexpectedNodeId line i nl.neStart nl.neEnd, warns.toArray, Algorithm.emptyLevel4⟩
    | some c2 =>
    match Algorithm.macrocellLeafChild leaves isLeaf nl.sw with
    | none => .inr ⟨.unexpectedNodeId line i nl.swStart nl.swEnd, warns.toArray, Algorithm.emptyLevel4⟩
    | some c3 =>
    match Algorithm.macrocellLeafChild leaves isLeaf nl.se with
    | none => .inr ⟨.unexpectedNodeId line i nl.seStart nl.seEnd, warns.toArray, Algorithm.emptyLevel4⟩
    | some c4 =>
      .inl (nodes.push (Algorithm.makeLevel4Node c1 c2 c3 c4), leaves.push 0, isLeaf.push false)
  else
    let emptySub := Algorithm.emptyMacroCellUInt32 (nl.level - 1)
    match Algorithm.macrocellCellChild nodes isLeaf nl.level emptySub nl.nw with
    | none => .inr ⟨.unexpectedNodeId line i nl.nwStart nl.nwEnd, warns.toArray, Algorithm.emptyLevel4⟩
    | some c1 =>
    match Algorithm.macrocellCellChild nodes isLeaf nl.level emptySub nl.ne with
    | none => .inr ⟨.unexpectedNodeId line i nl.neStart nl.neEnd, warns.toArray, Algorithm.emptyLevel4⟩
    | some c2 =>
    match Algorithm.macrocellCellChild nodes isLeaf nl.level emptySub nl.sw with
    | none => .inr ⟨.unexpectedNodeId line i nl.swStart nl.swEnd, warns.toArray, Algorithm.emptyLevel4⟩
    | some c3 =>
    match Algorithm.macrocellCellChild nodes isLeaf nl.level emptySub nl.se with
    | none => .inr ⟨.unexpectedNodeId line i nl.seStart nl.seEnd, warns.toArray, Algorithm.emptyLevel4⟩
    | some c4 =>
      .inl (nodes.push (Algorithm.makeCellNode c1 c2 c3 c4), leaves.push 0, isLeaf.push false)

theorem parseNodeStepResult_inr_ne_ok {line : String} {i : UInt32} {nl : Algorithm.MCNodeLine}
    {nodes : Algorithm.GrowBuf Algorithm.MacroCell} {leaves : Algorithm.GrowBuf UInt64}
    {isLeaf : Algorithm.GrowBuf Bool} {warns : Algorithm.GrowBuf Algorithm.MacrocellWarning}
    {errRes : Algorithm.MacrocellResult}
    (h : parseNodeStepResult line i nl nodes leaves isLeaf warns = .inr errRes) :
    errRes.status ≠ .ok := by
  dsimp only [parseNodeStepResult] at h
  repeat' split at h
  all_goals first
    | (simp only [Sum.inr.injEq] at h; rw [← h]; intro h0; cases h0)
    | cases h

theorem step_deserLoop_parseNode_some {locs : Nat → JvmVal}
    {lines : Array String} {numLines i : UInt32}
    {bytesAddr : Nat} {limit p col x y : UInt32} {leaf : UInt64}
    {nodes : Algorithm.GrowBuf Algorithm.MacroCell} {leaves : Algorithm.GrowBuf UInt64}
    {isLeaf : Algorithm.GrowBuf Bool} {warns : Algorithm.GrowBuf Algorithm.MacrocellWarning}
    {nl : Algorithm.MCNodeLine} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hlocs : DeserLoopLocs locs lines numLines i false bytesAddr limit p col x y leaf
      nodes leaves isLeaf warns)
    (hwarnBuf : locs 15 = .ext (.mcWarnGrowBuf warns))
    (hstat : jh.statics = [])
    (hiSz : i.toNat < lines.size) (hibv : i.toBitVec.slt 0#32 = false)
    (hnz : lines[i.toNat].toByteArray.size.toUInt32 ≠ 0)
    (hlPos : 0 < lines[i.toNat].toByteArray.data.size)
    (h48 : ¬ lines[i.toNat].toByteArray.data[0] < 48)
    (h57 : ¬ (57 : UInt8) < lines[i.toNat].toByteArray.data[0])
    (hsome : Algorithm.parseMCNodeLine lines[i.toNat].toByteArray = some nl) :
    let line := lines[i.toNat]
    let lineLen := line.toByteArray.size.toUInt32
    let inner : Array JvmVal := (Array.replicate 50 .null)
      |>.set! 0 (.boxedInt 0)
      |>.set! 1 (.boxedUInt nl.level)
      |>.set! 5 (.boxedUInt nl.nw)
      |>.set! 9 (.boxedUInt nl.nwStart)
      |>.set! 13 (.boxedUInt nl.nwEnd)
      |>.set! 17 (.boxedUInt nl.ne)
      |>.set! 21 (.boxedUInt nl.neStart)
      |>.set! 25 (.boxedUInt nl.neEnd)
      |>.set! 29 (.boxedUInt nl.sw)
      |>.set! 33 (.boxedUInt nl.swStart)
      |>.set! 37 (.boxedUInt nl.swEnd)
      |>.set! 41 (.boxedUInt nl.se)
      |>.set! 45 (.boxedUInt nl.seStart)
      |>.set! 49 (.boxedUInt nl.seEnd)
    let jh1 := (jh.alloc (.byteArray line.toByteArray.data)).2
    let jh2 := (jh1.alloc (.objArray "java/lang/Object" inner)).2
    let jh3 := (jh2.alloc (.objArray "java/lang/Object" #[.boxedInt 1, .heapRef jh1.objects.size])).2
    match parseNodeStepResult line i nl nodes leaves isLeaf warns with
    | .inl (nodes', leaves', isLeaf') =>
      ∃ (k : Nat) (locs' : Nat → JvmVal),
        locs' 15 = .ext (.mcWarnGrowBuf warns) ∧
        DeserLoopLocs locs' lines numLines (i + 1) false jh.objects.size lineLen 0 0 0 0 0
          nodes' leaves' isLeaf' warns ∧
        ∀ f, runJvmResFast (f + k) f_Algorithm_deserializeMacrocell_loop_prog 85
            (f_Algorithm_deserializeMacrocell_loop_prog.drop 85) ⟨85, [], locs, jh, hp⟩ =
          runJvmResFast f f_Algorithm_deserializeMacrocell_loop_prog 6
            (f_Algorithm_deserializeMacrocell_loop_prog.drop 6) ⟨6, [], locs', jh3, hp⟩
    | .inr errRes =>
      let enc := encodeMacrocellResult jh3 errRes
      ∃ (k pc' : Nat) (locs' : Nat → JvmVal),
        ∀ f, runJvmResFast (f + k) f_Algorithm_deserializeMacrocell_loop_prog 85
            (f_Algorithm_deserializeMacrocell_loop_prog.drop 85) ⟨85, [], locs, jh, hp⟩ =
          some (enc.1, ⟨pc', [enc.1], locs', enc.2, hp⟩) := by
  intro line lineLen inner jh1 jh2 jh3
  have hb35 : line.toByteArray.data[0] ≠ 35 := by
    intro h; rw [h] at h48; exact h48 (by decide)
  have hb35b : (line.toByteArray.data[0] == 35) = false := beq_false_of_ne hb35
  have hgetNew : jh1.get? jh.objects.size = some (.byteArray line.toByteArray.data) :=
    jvmHeap_get?_alloc_self _ _
  have hgetIn3 : jh3.get? jh1.objects.size = some (.objArray "java/lang/Object" inner) := by
    dsimp only [jh3]; exact jvmHeap_get?_alloc_mono (jvmHeap_get?_alloc_self _ _)
  have hgetOut3 : jh3.get? jh2.objects.size =
      some (.objArray "java/lang/Object" #[.boxedInt 1, .heapRef jh1.objects.size]) :=
    jvmHeap_get?_alloc_self _ _
  have hstat3 : jh3.statics = [] := hstat
  let locsD := setLocal (setLocal (setLocal (setLocal locs 16 (.str line))
    17 (.heapRef jh.objects.size)) 18 (.i32 lineLen))
    19 (.i32 (UInt32.ofBitVec (line.toByteArray.data[0].toBitVec.signExtend 32)))
  let locs169 := setLocal locsD 20 (.heapRef jh2.objects.size)
  let locs177 := setLocal locs169 22 (.heapRef jh1.objects.size)
  have hto463 : ∃ locs463,
      (∀ s, s < 16 → locs463 s = locs s) ∧
      locs463 16 = .str line ∧ locs463 17 = .heapRef jh.objects.size ∧
      locs463 18 = .i32 lineLen ∧ locs463 23 = .i32 nl.level ∧
      locs463 24 = .i32 nl.nw ∧ locs463 25 = .i32 nl.nwStart ∧ locs463 26 = .i32 nl.nwEnd ∧
      locs463 27 = .i32 nl.ne ∧ locs463 28 = .i32 nl.neStart ∧ locs463 29 = .i32 nl.neEnd ∧
      locs463 30 = .i32 nl.sw ∧ locs463 31 = .i32 nl.swStart ∧ locs463 32 = .i32 nl.swEnd ∧
      locs463 33 = .i32 nl.se ∧ locs463 34 = .i32 nl.seStart ∧ locs463 35 = .i32 nl.seEnd ∧
      ∀ g, runJvmResFast (g + 288) f_Algorithm_deserializeMacrocell_loop_prog 85
          (f_Algorithm_deserializeMacrocell_loop_prog.drop 85) ⟨85, [], locs, jh, hp⟩ =
        runJvmResFast g f_Algorithm_deserializeMacrocell_loop_prog 463
          (f_Algorithm_deserializeMacrocell_loop_prog.drop 463) ⟨463, [], locs463, jh3, hp⟩ := by
    rcases step_deserLoop_unboxAll13 (innerAddr := jh1.objects.size)
        (nl := nl) (locs := locs177) (jh := jh3) (hp := hp) (by rfl) hgetIn3 with
      ⟨l463, hp463, hv23, hv24, hv25, hv26, hv27, hv28, hv29, hv30, hv31, hv32, hv33, hv34, hv35, hs463⟩
    refine ⟨l463, fun s hs => by
        rw [hp463 s (by omega)]
        dsimp only [locs177, locs169, locsD]
        rw [setLocal_ne_eq (decide_eq_false (by omega)), setLocal_ne_eq (decide_eq_false (by omega)),
          setLocal_ne_eq (decide_eq_false (by omega)), setLocal_ne_eq (decide_eq_false (by omega)),
          setLocal_ne_eq (decide_eq_false (by omega)), setLocal_ne_eq (decide_eq_false (by omega))],
      by rw [hp463 16 (by omega)]; rfl,
      by rw [hp463 17 (by omega)]; rfl,
      by rw [hp463 18 (by omega)]; rfl,
      hv23, hv24, hv25, hv26, hv27, hv28, hv29, hv30, hv31, hv32, hv33, hv34, hv35, fun g => ?_⟩
    have hd := step_deserLoop_nonleaf_dispatch (f := g + 245) (jh := jh) (hp := hp)
      hlocs hiSz hibv hnz hlPos
    simp only [nonleafDispFuel, nonleafTarget, line, hb35b, h48, h57, decide_false, Bool.false_eq_true,
      Bool.or_false, ↓reduceIte] at hd
    rw [show g + 288 = (g + 245) + 43 from by omega, hd, deserLoop_drop_128]
    step1_ex
    rw [show g + 244 = (g + 243) + 1 from by omega]
    rw [runJvmResFast_invokestatic_step (stepStatic_parseMCNodeLine_some hgetNew hsome)]
    step1_ex; step1_ex; step1_ex
    rw [show g + 240 = (g + 239) + 1 from by omega]
    rw [runJvmResFast_checkNotNull_nonnull (by intro h; cases h)]
    step1_ex
    dsimp only [jh3, jh2, jh1, inner, line, lineLen, Jvm.JvmHeap.alloc] at hgetOut3 hgetIn3 hs463 ⊢
    rw [show g + 238 = (g + 237) + 1 from by omega]
    rw [runJvmResFast_checkcast_objArray hgetOut3 (Or.inl rfl)]
    step1_ex
    rw [show g + 236 = (g + 235) + 1 from by omega]
    rw [runJvmResFast_aaload hgetOut3 (by rfl) (by simp)]
    step1_ex; step1_ex
    rw [show g + 233 = (g + 232) + 1 from by omega]
    rw [runJvmResFast_checkNotNull_nonnull (by intro h; cases h)]
    rw [show #[JvmVal.boxedInt 1, Jvm.JvmVal.heapRef
        (jh.objects.push (Jvm.HeapObj.byteArray lines[i.toNat].toByteArray.data)).size][UInt32.toNat 0] =
      JvmVal.boxedInt 1 from rfl]
    rw [show g + 232 = (g + 231) + 1 from by omega]
    rw [runJvmResFast_checkcast_boxedInt (Or.inl rfl)]
    step1_ex
    rw [show g + 230 = (g + 229) + 1 from by omega]
    rw [runJvmResFast_tableswitch]
    rw [show Jvm.tableswitchTarget 1 0 [144, 169] 938 = 169 from by decide]
    dsimp only
    rw [deserLoop_drop_169]
    step1_ex
    rw [show g + 228 = (g + 227) + 1 from by omega]
    rw [runJvmResFast_checkcast_objArray hgetOut3 (Or.inl rfl)]
    step1_ex
    rw [show g + 226 = (g + 225) + 1 from by omega]
    rw [runJvmResFast_aaload hgetOut3 (by rfl) (by simp)]
    rw [show #[JvmVal.boxedInt 1, Jvm.JvmVal.heapRef
        (jh.objects.push (Jvm.HeapObj.byteArray lines[i.toNat].toByteArray.data)).size][UInt32.toNat 1] =
      Jvm.JvmVal.heapRef
        (jh.objects.push (Jvm.HeapObj.byteArray lines[i.toNat].toByteArray.data)).size from rfl]
    step1_ex; step1_ex; step1_ex
    rw [show g + 222 = (g + 221) + 1 from by omega]
    rw [runJvmResFast_checkNotNull_nonnull (by intro h; cases h)]
    exact hs463 g
  rcases hto463 with ⟨l463, hp463, hl16, hl17, hl18, hl23, hl24, hl25, hl26,
    hl27, hl28, hl29, hl30, hl31, hl32, hl33, hl34, hl35, hrun463⟩
  by_cases hlt4 : nl.level < 4
  · have hspec : parseNodeStepResult line i nl nodes leaves isLeaf warns =
        .inr ⟨.unexpectedInput line i, warns.toArray, Algorithm.emptyLevel4⟩ := by
      simp [parseNodeStepResult, hlt4]
    rw [hspec]
    rcases step_deserLoop_unexpectedInput_1102 (locs := l463) (jh := jh3) (hp := hp)
      (by rw [hp463 2 (by omega)]; exact hlocs.h2)
      (by rw [hp463 15 (by omega)]; exact hwarnBuf) hl16 hstat3 with ⟨pc', locs', heq⟩
    refine ⟨318, pc', locs', fun f => ?_⟩
    rw [show f + 318 = (f + 30) + 288 from by omega, hrun463, deserLoop_drop_463]
    step1; rw [hl23]; step1
    rw [show f + 28 = (f + 27) + 1 from by omega]
    rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned]
    rw [show f + 27 = (f + 26) + 1 from by omega]
    rw [runJvmResFast_iflt_branch (by rw [compareUnsigned_slt_zero]; exact decide_eq_true hlt4)]
    rw [deserLoop_drop_937, show f + 26 = (f + 25) + 1 from by omega, runJvmResFast_goto]
    exact heq f
  · by_cases hgt63 : Algorithm.maxMacrocellLevel < nl.level
    · have hspec : parseNodeStepResult line i nl nodes leaves isLeaf warns =
          .inr ⟨.unexpectedInput line i, warns.toArray, Algorithm.emptyLevel4⟩ := by
        simp [parseNodeStepResult, hlt4, hgt63]
      have hgt63' : (63 : UInt32) < nl.level := hgt63
      rw [hspec]
      rcases step_deserLoop_unexpectedInput_1102 (locs := l463) (jh := jh3) (hp := hp)
        (by rw [hp463 2 (by omega)]; exact hlocs.h2)
        (by rw [hp463 15 (by omega)]; exact hwarnBuf) hl16 hstat3 with ⟨pc', locs', heq⟩
      refine ⟨322, pc', locs', fun f => ?_⟩
      rw [show f + 322 = (f + 34) + 288 from by omega, hrun463, deserLoop_drop_463]
      step1; rw [hl23]; step1
      rw [show f + 32 = (f + 31) + 1 from by omega]
      rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned]
      rw [show f + 31 = (f + 30) + 1 from by omega]
      rw [runJvmResFast_iflt_fallthrough (by rw [compareUnsigned_slt_zero]; exact decide_eq_false hlt4)]
      step1; step1; rw [hl23]
      rw [show f + 28 = (f + 27) + 1 from by omega]
      rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned]
      rw [show f + 27 = (f + 26) + 1 from by omega]
      rw [runJvmResFast_iflt_branch (by rw [compareUnsigned_slt_zero]; exact decide_eq_true hgt63')]
      rw [deserLoop_drop_936, show f + 26 = (f + 25) + 1 from by omega, runJvmResFast_goto]
      exact heq f
    · have hgt63b : (nl.level > Algorithm.maxMacrocellLevel) = false := by simp [hgt63]
      have hgt63c : decide ((63 : UInt32) < nl.level) = false := decide_eq_false hgt63
      have hlt4b : (nl.level < 4) = false := by simp [hlt4]
      have hlt4c : decide (nl.level < 4) = false := decide_eq_false hlt4
      have hto686 : ∀ (h686 : nl.level = 4) g,
          runJvmResFast (g + 299) f_Algorithm_deserializeMacrocell_loop_prog 85
              (f_Algorithm_deserializeMacrocell_loop_prog.drop 85) ⟨85, [], locs, jh, hp⟩ =
            runJvmResFast g f_Algorithm_deserializeMacrocell_loop_prog 686
              (f_Algorithm_deserializeMacrocell_loop_prog.drop 686) ⟨686, [], l463, jh3, hp⟩ := by
        intro heq4 g
        rw [show g + 299 = (g + 11) + 288 from by omega, hrun463, deserLoop_drop_463]
        step1; rw [hl23]; step1
        rw [show g + 9 = (g + 8) + 1 from by omega]
        rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned]
        rw [show g + 8 = (g + 7) + 1 from by omega]
        rw [runJvmResFast_iflt_fallthrough (by rw [compareUnsigned_slt_zero]; exact hlt4c)]
        step1; step1; rw [hl23]
        rw [show g + 5 = (g + 4) + 1 from by omega]
        rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned]
        rw [show g + 4 = (g + 3) + 1 from by omega]
        rw [runJvmResFast_iflt_fallthrough (by rw [compareUnsigned_slt_zero]; exact hgt63c)]
        step1; rw [hl23]; step1
        exact runJvmResFast_if_icmpeq_branch heq4
      by_cases heq4 : nl.level = 4
      · have heq4b : (nl.level == 4) = true := beq_iff_eq.mpr heq4
        have hprefix : parseNodeStepResult line i nl nodes leaves isLeaf warns =
            match Algorithm.macrocellLeafChild leaves isLeaf nl.nw with
            | none => .inr ⟨.unexpectedNodeId line i nl.nwStart nl.nwEnd, warns.toArray, Algorithm.emptyLevel4⟩
            | some c1 =>
              match Algorithm.macrocellLeafChild leaves isLeaf nl.ne with
              | none => .inr ⟨.unexpectedNodeId line i nl.neStart nl.neEnd, warns.toArray, Algorithm.emptyLevel4⟩
              | some c2 =>
                match Algorithm.macrocellLeafChild leaves isLeaf nl.sw with
                | none => .inr ⟨.unexpectedNodeId line i nl.swStart nl.swEnd, warns.toArray, Algorithm.emptyLevel4⟩
                | some c3 =>
                  match Algorithm.macrocellLeafChild leaves isLeaf nl.se with
                  | none =>
                    .inr ⟨.unexpectedNodeId line i nl.seStart nl.seEnd, warns.toArray, Algorithm.emptyLevel4⟩
                  | some c4 =>
                    .inl (nodes.push (Algorithm.makeLevel4Node c1 c2 c3 c4), leaves.push 0, isLeaf.push false) := by
          simp [parseNodeStepResult, hlt4b, hgt63b, heq4b]
        rw [hprefix]
        have hl4 := step_deserLoop_parseNode_level4 (locs := l463) (hp := hp)
          (by rw [hp463 0 (by omega)]; exact hlocs.h0) (by rw [hp463 1 (by omega)]; exact hlocs.h1)
          (by rw [hp463 2 (by omega)]; exact hlocs.h2) (by rw [hp463 12 (by omega)]; exact hlocs.h12)
          (by rw [hp463 13 (by omega)]; exact hlocs.h13) (by rw [hp463 14 (by omega)]; exact hlocs.h14)
          (by rw [hp463 15 (by omega)]; exact hwarnBuf) hl16 hl17 hl18
          hl24 hl25 hl26 hl27 hl28 hl29 hl30 hl31 hl32 hl33 hl34 hl35 hstat3
        cases hc1 : Algorithm.macrocellLeafChild leaves isLeaf nl.nw with
        | none =>
          rw [hc1] at hl4
          rcases hl4 with ⟨pc', locs', heq⟩
          refine ⟨333, pc', locs', fun f => ?_⟩
          rw [show f + 333 = (f + 34) + 299 from by omega, hto686 heq4]; exact heq f
        | some c1 =>
          cases hc2 : Algorithm.macrocellLeafChild leaves isLeaf nl.ne with
          | none =>
            rw [hc1, hc2] at hl4
            rcases hl4 with ⟨pc', locs', heq⟩
            refine ⟨340, pc', locs', fun f => ?_⟩
            rw [show f + 340 = (f + 41) + 299 from by omega, hto686 heq4]; exact heq f
          | some c2 =>
            cases hc3 : Algorithm.macrocellLeafChild leaves isLeaf nl.sw with
            | none =>
              rw [hc1, hc2, hc3] at hl4
              rcases hl4 with ⟨pc', locs', heq⟩
              refine ⟨347, pc', locs', fun f => ?_⟩
              rw [show f + 347 = (f + 48) + 299 from by omega, hto686 heq4]; exact heq f
            | some c3 =>
              cases hc4 : Algorithm.macrocellLeafChild leaves isLeaf nl.se with
              | none =>
                rw [hc1, hc2, hc3, hc4] at hl4
                rcases hl4 with ⟨pc', locs', heq⟩
                refine ⟨354, pc', locs', fun f => ?_⟩
                rw [show f + 354 = (f + 55) + 299 from by omega, hto686 heq4]; exact heq f
              | some c4 =>
                rw [hc1, hc2, hc3, hc4] at hl4
                rcases hl4 with ⟨locs', h15', hdl', heq⟩
                refine ⟨421, locs', h15', hdl', fun f => ?_⟩
                rw [show f + 421 = (f + 122) + 299 from by omega, hto686 heq4]; exact heq f
      · have heq4b : (nl.level == 4) = false := beq_false_of_ne heq4
        let emptySub := Algorithm.emptyMacroCellUInt32 (nl.level - 1)
        let l480 := setLocal l463 36 (.ext (.mc emptySub))
        have hto480 : ∀ g,
            runJvmResFast (g + 305) f_Algorithm_deserializeMacrocell_loop_prog 85
                (f_Algorithm_deserializeMacrocell_loop_prog.drop 85) ⟨85, [], locs, jh, hp⟩ =
              runJvmResFast g f_Algorithm_deserializeMacrocell_loop_prog 480
                (f_Algorithm_deserializeMacrocell_loop_prog.drop 480) ⟨480, [], l480, jh3, hp⟩ := by
          intro g
          rw [show g + 305 = (g + 17) + 288 from by omega, hrun463, deserLoop_drop_463]
          step1; rw [hl23]; step1
          rw [show g + 15 = (g + 14) + 1 from by omega]
          rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned]
          rw [show g + 14 = (g + 13) + 1 from by omega]
          rw [runJvmResFast_iflt_fallthrough (by rw [compareUnsigned_slt_zero]; exact hlt4c)]
          step1; step1; rw [hl23]
          rw [show g + 11 = (g + 10) + 1 from by omega]
          rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned]
          rw [show g + 10 = (g + 9) + 1 from by omega]
          rw [runJvmResFast_iflt_fallthrough (by rw [compareUnsigned_slt_zero]; exact hgt63c)]
          step1; rw [hl23]; step1
          rw [show g + 7 = (g + 6) + 1 from by omega]
          rw [runJvmResFast_if_icmpeq_fallthrough heq4b]
          step1; rw [hl23]; step1; step1
          rw [show g + 3 = (g + 2) + 1 from by omega]
          rw [runJvmResFast_invokestatic_step stepStatic_uintCtor5a]
          rw [show g + 2 = (g + 1) + 1 from by omega]
          rw [runJvmResFast_invokestatic_step stepStatic_emptyMacroCellUInt32]
          step1
        have hprefix : parseNodeStepResult line i nl nodes leaves isLeaf warns =
            match Algorithm.macrocellCellChild nodes isLeaf nl.level emptySub nl.nw with
            | none => .inr ⟨.unexpectedNodeId line i nl.nwStart nl.nwEnd, warns.toArray, Algorithm.emptyLevel4⟩
            | some c1 =>
              match Algorithm.macrocellCellChild nodes isLeaf nl.level emptySub nl.ne with
              | none => .inr ⟨.unexpectedNodeId line i nl.neStart nl.neEnd, warns.toArray, Algorithm.emptyLevel4⟩
              | some c2 =>
                match Algorithm.macrocellCellChild nodes isLeaf nl.level emptySub nl.sw with
                | none => .inr ⟨.unexpectedNodeId line i nl.swStart nl.swEnd, warns.toArray, Algorithm.emptyLevel4⟩
                | some c3 =>
                  match Algorithm.macrocellCellChild nodes isLeaf nl.level emptySub nl.se with
                  | none =>
                    .inr ⟨.unexpectedNodeId line i nl.seStart nl.seEnd, warns.toArray, Algorithm.emptyLevel4⟩
                  | some c4 =>
                    .inl (nodes.push (Algorithm.makeCellNode c1 c2 c3 c4), leaves.push 0, isLeaf.push false) := by
          simp [parseNodeStepResult, hlt4b, hgt63b, heq4b, emptySub]
        rw [hprefix]
        have hp480 : ∀ s, s < 16 → l480 s = locs s := fun s hs => by
          dsimp only [l480]
          rw [setLocal_ne_eq (i := 36) (j := s) (decide_eq_false (by omega))]; exact hp463 s hs
        have hcell := step_deserLoop_parseNode_cell (locs := l480) (hp := hp)
          (by rw [hp480 0 (by omega)]; exact hlocs.h0) (by rw [hp480 1 (by omega)]; exact hlocs.h1)
          (by rw [hp480 2 (by omega)]; exact hlocs.h2) (by rw [hp480 12 (by omega)]; exact hlocs.h12)
          (by rw [hp480 13 (by omega)]; exact hlocs.h13) (by rw [hp480 14 (by omega)]; exact hlocs.h14)
          (by rw [hp480 15 (by omega)]; exact hwarnBuf)
          (by dsimp only [l480]; rw [setLocal_ne_eq rfl]; exact hl16)
          (by dsimp only [l480]; rw [setLocal_ne_eq rfl]; exact hl17)
          (by dsimp only [l480]; rw [setLocal_ne_eq rfl]; exact hl18)
          (by dsimp only [l480]; rw [setLocal_ne_eq rfl]; exact hl23)
          (by dsimp only [l480]; rw [setLocal_ne_eq rfl]; exact hl24)
          (by dsimp only [l480]; rw [setLocal_ne_eq rfl]; exact hl25)
          (by dsimp only [l480]; rw [setLocal_ne_eq rfl]; exact hl26)
          (by dsimp only [l480]; rw [setLocal_ne_eq rfl]; exact hl27)
          (by dsimp only [l480]; rw [setLocal_ne_eq rfl]; exact hl28)
          (by dsimp only [l480]; rw [setLocal_ne_eq rfl]; exact hl29)
          (by dsimp only [l480]; rw [setLocal_ne_eq rfl]; exact hl30)
          (by dsimp only [l480]; rw [setLocal_ne_eq rfl]; exact hl31)
          (by dsimp only [l480]; rw [setLocal_ne_eq rfl]; exact hl32)
          (by dsimp only [l480]; rw [setLocal_ne_eq rfl]; exact hl33)
          (by dsimp only [l480]; rw [setLocal_ne_eq rfl]; exact hl34)
          (by dsimp only [l480]; rw [setLocal_ne_eq rfl]; exact hl35)
          (by dsimp only [l480]; rw [setLocal_eq_val rfl]) hstat3
        cases hc1 : Algorithm.macrocellCellChild nodes isLeaf nl.level emptySub nl.nw with
        | none =>
          rw [hc1] at hcell
          rcases hcell with ⟨pc', locs', heq⟩
          refine ⟨341, pc', locs', fun f => ?_⟩
          rw [show f + 341 = (f + 36) + 305 from by omega, hto480]; exact heq f
        | some c1 =>
          cases hc2 : Algorithm.macrocellCellChild nodes isLeaf nl.level emptySub nl.ne with
          | none =>
            rw [hc1, hc2] at hcell
            rcases hcell with ⟨pc', locs', heq⟩
            refine ⟨350, pc', locs', fun f => ?_⟩
            rw [show f + 350 = (f + 45) + 305 from by omega, hto480]; exact heq f
          | some c2 =>
            cases hc3 : Algorithm.macrocellCellChild nodes isLeaf nl.level emptySub nl.sw with
            | none =>
              rw [hc1, hc2, hc3] at hcell
              rcases hcell with ⟨pc', locs', heq⟩
              refine ⟨359, pc', locs', fun f => ?_⟩
              rw [show f + 359 = (f + 54) + 305 from by omega, hto480]; exact heq f
            | some c3 =>
              cases hc4 : Algorithm.macrocellCellChild nodes isLeaf nl.level emptySub nl.se with
              | none =>
                rw [hc1, hc2, hc3, hc4] at hcell
                rcases hcell with ⟨pc', locs', heq⟩
                refine ⟨368, pc', locs', fun f => ?_⟩
                rw [show f + 368 = (f + 63) + 305 from by omega, hto480]; exact heq f
              | some c4 =>
                rw [hc1, hc2, hc3, hc4] at hcell
                rcases hcell with ⟨locs', h15', hdl', heq⟩
                refine ⟨403, locs', h15', hdl', fun f => ?_⟩
                rw [show f + 403 = (f + 98) + 305 from by omega, hto480]; exact heq f

end Algorithm.JvmVerification
