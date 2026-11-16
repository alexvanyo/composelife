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

import Jvm.Proofs
import Jvm.Tactics
import KotlinJvmBytecode
import theorems.EasingPiecewiseModelTheorems

namespace UiCommon.KotlinJvmVerification

open UiCommon.JvmVerification
open UiCommon.KotlinJvmBytecode
open UiCommon.Model

def isUiStop : JvmInstr → Bool
  | .invokestatic _ _ _ | .invokevirtual _ _ _ | .invokespecial _ _ _ | .invokeinterface _ _ _
  | .invokedynamic _ _ _ | .getstatic _ _ _ | .putstatic _ _ _ | .getfield _ _ _ | .putfield _ _ _
  | .newClass _ | .checkcast _ | .instanceof _ | .idiv | .ldiv | .athrow | .arraylength
  | .areturn | .ireturn | .lreturn | .freturn | .dreturn | .vreturn
  | .ifeq _ | .ifne _ | .iflt _ | .ifle _ | .ifgt _ | .ifge _
  | .ifnull _ | .ifnonnull _ | .if_icmpeq _ | .if_icmpne _ | .if_icmplt _
  | .if_icmpge _ | .if_icmpgt _ | .if_icmple _ | .if_acmpeq _ | .if_acmpne _
  | .goto _ | .tableswitch _ _ _ | .lookupswitch _ _ => true
  | _ => false

section StepTactics

open Lean Elab Tactic Meta

def uiOpaqueConsts : NameSet :=
  NameSet.empty
    |>.insert ``mkUiCommonHooks
    |>.insert ``EasingPiecewiseKt_Easing_prog
    |>.insert ``EasingPiecewiseKt_floorBinarySearch_prog
    |>.insert ``EasingPiecewiseKt_Easing_lambda_3_prog
    |>.insert ``UiCommon.Model.floatCompare
    |>.insert ``UiCommon.Model.putKeyMap
    |>.insert ``sortPairsByKeyframe

def uiInitConsts : List Name :=
  [``initUiJvmState, ``Jvm.initJvmState]

elab "ui_whnf_blk" : conv => withMainContext do
  let lhs ← Lean.Elab.Tactic.Conv.getLhs
  let res ← Jvm.Tactics.withOpaque uiOpaqueConsts
    (Jvm.Tactics.normJvmBlkExpr uiInitConsts (fun _ => pure none) lhs)
  Lean.Elab.Tactic.Conv.changeLhs res

elab "ui_norm_locals" : tactic =>
  Lean.Elab.Tactic.liftMetaTactic fun g => do
    let tgt ← instantiateMVars (← g.getType)
    let res ← Jvm.Tactics.normJvmLocalsExpr uiInitConsts (fun _ => pure none) [] tgt
    return [← g.replaceTargetDefEq res]

elab "ui_norm_run_args" : tactic =>
  Lean.Elab.Tactic.liftMetaTactic fun g => do
    let tgt ← instantiateMVars (← g.getType)
    let normSt := fun s : Expr => do
      let s1 ← Jvm.Tactics.withOpaque uiOpaqueConsts
        (Jvm.Tactics.normJvmBlkExpr uiInitConsts (fun _ => pure none) s)
      if s1.isAppOfArity ``Jvm.JvmState.mk 7 then
        let sa := s1.getAppArgs
        let pcField ← Jvm.Tactics.normJvmNatWith uiOpaqueConsts sa[2]!
        return mkAppN s1.getAppFn #[sa[0]!, sa[1]!, pcField, sa[3]!, sa[4]!, sa[5]!, sa[6]!]
      else
        return s1
    let normRun := fun b : Expr => do
      if b.isAppOfArity ``Jvm.runJvmResFast 8 then
        let ba := b.getAppArgs
        let fuel' ← Jvm.Tactics.withOpaque uiOpaqueConsts (whnf ba[3]!)
        let pc' ← Jvm.Tactics.withOpaque uiOpaqueConsts (whnf ba[5]!)
        let st' ← normSt ba[7]!
        let mut instrs' := ba[6]!
        let mut instrsEq : Option Expr := none
        if instrs'.isAppOfArity ``List.drop 3 then
          let da := instrs'.getAppArgs
          if let some n ← Jvm.Tactics.evalNatLit? da[1]! then
            let (rhs, eqP) ← Jvm.Tactics.fastDropListEq da[2]! n
            instrs' := rhs
            instrsEq := some eqP
        while instrs'.isLet do
          instrs' := instrs'.letBody!.instantiate1 instrs'.letValue!
        let newB := mkAppN b.getAppFn #[ba[0]!, ba[1]!, ba[2]!, fuel', ba[4]!, pc', instrs', st']
        match instrsEq with
        | none => return (newB, none)
        | some eqP =>
          let lam := mkLambda `x .default (← inferType ba[6]!)
            (mkAppN b.getAppFn #[ba[0]!, ba[1]!, ba[2]!, fuel', ba[4]!, pc', Expr.bvar 0, st'])
          let fullEq ← mkCongrArg lam eqP
          let prefixB := mkAppN b.getAppFn #[ba[0]!, ba[1]!, ba[2]!, fuel', ba[4]!, pc', ba[6]!, st']
          let defEq ← mkExpectedTypeHint (← mkEqRefl b) (← mkEq b prefixB)
          return (newB, some (← mkEqTrans defEq fullEq))
      else
        return (b, none)
    if let some (_, lhs, rhs) := tgt.consumeMData.eq? then
      let (lhs', eqOpt) ← normRun lhs
      match eqOpt with
      | none => return [← g.replaceTargetDefEq (← mkEq lhs' rhs)]
      | some eqP =>
        let mvar ← mkFreshExprMVar (← mkEq lhs' rhs)
        g.assign (← mkEqTrans eqP mvar)
        return [mvar.mvarId!]
    return [g]

def isUiNonStop : TacticM Bool := do
  let tgt := (← getMainTarget).consumeMData
  let some (_, lhs, _) := tgt.eq? | return false
  let lhs := lhs.consumeMData
  if lhs.isAppOfArity ``Jvm.runJvmResFast 8 then
    let instrs ← whnf (lhs.getArg! 6)
    if instrs.isAppOfArity ``List.cons 3 then
      let instr := instrs.getArg! 1
      let br ← whnf (mkApp (mkConst ``isUiStop) instr)
      return br.isConstOf ``Bool.false
  return false

def isUiForwardGoto : TacticM Bool := do
  let tgt := (← getMainTarget).consumeMData
  let some (_, lhs, _) := tgt.eq? | return false
  let lhs := lhs.consumeMData
  if lhs.isAppOfArity ``Jvm.runJvmResFast 8 then
    let instrs ← whnf (lhs.getArg! 6)
    if instrs.isAppOfArity ``List.cons 3 then
      let instr ← whnf (instrs.getArg! 1)
      if instr.isAppOfArity ``Jvm.JvmInstr.goto 1 then
        if let (some pcVal, some tgtVal) :=
            (← Jvm.Tactics.evalNatLit? (lhs.getArg! 5), ← Jvm.Tactics.evalNatLit? (instr.getArg! 0)) then
          return pcVal < tgtVal
  return false

elab "ui_step_one_chunk" : tactic => do
  let tgt := (← getMainTarget).consumeMData
  let some (_, lhs, _) := tgt.eq? | return ()
  let lhs := lhs.consumeMData
  if !lhs.isAppOfArity ``Jvm.runJvmResFast 8 then return ()
  evalTactic (← `(tactic| (conv => lhs; tactic => ui_norm_run_args)))
  evalTactic (← `(tactic| rw [Jvm.runJvmResFast_stepBlockChunkWith _ isUiStop 64]))
  if !(← getUnsolvedGoals).isEmpty then
    evalTactic (← `(tactic| (conv => lhs; arg 2; ui_whnf_blk)))
    let tgt2 := (← getMainTarget).consumeMData
    let some (_, lhs2, _) := tgt2.eq? | return ()
    let chunkRes := (lhs2.consumeMData.getArg! 3).consumeMData
    if let some cn := chunkRes.getAppFn.constName? then
      if cn == ``Jvm.BlockResChunkRes.cont then
        evalTactic (← `(tactic| rw [Jvm.afterResBlockChunk_cont]))
      else if cn == ``Jvm.BlockResChunkRes.jump then
        evalTactic (← `(tactic| rw [Jvm.afterResBlockChunk_jump]))
      else if cn == ``Jvm.BlockResChunkRes.done then
        evalTactic (← `(tactic| rw [Jvm.afterResBlockChunk_done]))
    if !(← getUnsolvedGoals).isEmpty then
      evalTactic (← `(tactic| (conv => lhs; tactic => ui_norm_locals)))
      evalTactic (← `(tactic| (conv => lhs; tactic => ui_norm_run_args)))

elab "ui_step_blk" : tactic => do
  for _ in [:40] do
    if (← getUnsolvedGoals).isEmpty then break
    if ← isUiNonStop then
      evalTactic (← `(tactic| ui_step_one_chunk))
    else if ← isUiForwardGoto then
      evalTactic (← `(tactic| (conv => lhs; tactic => ui_norm_run_args)))
      evalTactic (← `(tactic| rw [Jvm.runJvmResFast_at_branch_cons _ (hbr := rfl)]))
      if !(← getUnsolvedGoals).isEmpty then
        evalTactic (← `(tactic| (
          (conv => lhs; arg 2; whnf)
          (conv => lhs; arg 4; whnf)
          (conv => lhs; arg 5; whnf)
          (conv => lhs; arg 7; ui_whnf_blk))))
        let tgt2 := (← getMainTarget).consumeMData
        let some (_, lhs2, _) := tgt2.eq? | break
        Jvm.Tactics.rwEvalBranchByInstrWith Jvm.Tactics.defaultEvalBranchThm true (lhs2.consumeMData.getArg! 6)
        if !(← getUnsolvedGoals).isEmpty then
          evalTactic (← `(tactic| (conv => lhs; tactic => ui_norm_locals; ui_norm_run_args)))
    else
      break

elab "ui_branch" : tactic => do
  let tgt := (← getMainTarget).consumeMData
  let some (_, lhs, _) := tgt.eq? | throwError "ui_branch: goal is not an equation"
  let lhs := lhs.consumeMData
  if !lhs.isAppOfArity ``Jvm.runJvmResFast 8 then throwError "ui_branch: not a fast JVM run"
  evalTactic (← `(tactic| (conv => lhs; tactic => ui_norm_run_args)))
  evalTactic (← `(tactic| rw [Jvm.runJvmResFast_at_branch_cons _ (hbr := rfl)]))
  if !(← getUnsolvedGoals).isEmpty then
    evalTactic (← `(tactic| (
      (conv => lhs; arg 2; whnf)
      (conv => lhs; arg 4; whnf)
      (conv => lhs; arg 5; whnf)
      (conv => lhs; arg 7; ui_whnf_blk))))
    let tgt2 := (← getMainTarget).consumeMData
    let some (_, lhs2, _) := tgt2.eq? | return ()
    Jvm.Tactics.rwEvalBranchByInstrWith Jvm.Tactics.defaultEvalBranchThm true (lhs2.consumeMData.getArg! 6)
    if !(← getUnsolvedGoals).isEmpty then
      evalTactic (← `(tactic| try (first
        | rw [ite_eq_left (by decide)]
        | rw [ite_eq_right (by decide)])))
      if !(← getUnsolvedGoals).isEmpty then
        evalTactic (← `(tactic| (conv => lhs; tactic => ui_norm_locals; ui_norm_run_args)))

/-- Steps one stop instruction whose hook result is computed by `rfl`, then continues with `ui_step_blk`. -/
macro "ui_rfl_step" : tactic => `(tactic| (
  first
    | rw [Jvm.runJvmResFast_invokestatic_step _ (by rfl)]
    | rw [Jvm.runJvmResFast_invokeinterface_step _ (by rfl)]
    | rw [Jvm.runJvmResFast_invokevirtual_step _ (by rfl)]
    | rw [Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) (by rfl) rfl]
  ui_step_blk))

end StepTactics

/-! ### Arithmetic and step lemmas -/

theorem u32_slt_ofNat (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    (UInt32.ofNat a).toBitVec.slt (UInt32.ofNat b).toBitVec = decide (a < b) := by
  rw [BitVec.slt, Jvm.u32_toInt_eq_toNat (by rw [Jvm.ui32_ofNat_toNat_of_lt a ha]; exact ha),
    Jvm.u32_toInt_eq_toNat (by rw [Jvm.ui32_ofNat_toNat_of_lt b hb]; exact hb),
    Jvm.ui32_ofNat_toNat_of_lt a ha, Jvm.ui32_ofNat_toNat_of_lt b hb]
  simp

theorem u32_idiv2_ofNat (s : Nat) (hs : s < 2 ^ 31) :
    Jvm.jvmI32Div (UInt32.ofNat s) 2 = some (UInt32.ofNat (s / 2)) := by
  unfold Jvm.jvmI32Div
  have hmsb : (UInt32.ofNat s).toBitVec.msb = false := by
    rw [BitVec.msb_eq_decide]; simp [Jvm.ui32_ofNat_toNat_of_lt s hs]; omega
  simp only [show ((2 : UInt32) == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  congr 1
  apply UInt32.toBitVec_inj.mp
  show (UInt32.ofNat s).toBitVec.sdiv (2#32) = (UInt32.ofNat (s / 2)).toBitVec
  rw [BitVec.sdiv_eq, hmsb, show (2#32).msb = false from rfl]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_udiv, Jvm.ui32_ofNat_toNat_of_lt s hs]
  omega

theorem u32_sle_ofNat (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    (UInt32.ofNat a).toBitVec.sle (UInt32.ofNat b).toBitVec = decide (a ≤ b) := by
  rw [BitVec.sle, Jvm.u32_toInt_eq_toNat (by rw [Jvm.ui32_ofNat_toNat_of_lt a ha]; exact ha),
    Jvm.u32_toInt_eq_toNat (by rw [Jvm.ui32_ofNat_toNat_of_lt b hb]; exact hb),
    Jvm.ui32_ofNat_toNat_of_lt a ha, Jvm.ui32_ofNat_toNat_of_lt b hb]
  simp

theorem i32_sle_zero (x : Int32) : x.toUInt32.toBitVec.sle 0#32 = decide (x ≤ 0) := by
  have h := Int32.le_iff_toBitVec_sle (a := x) (b := 0)
  cases hb : x.toUInt32.toBitVec.sle 0#32 <;> simp_all [Int32.toBitVec_toUInt32]

theorem i32_zero_slt (x : Int32) : (0#32).slt x.toUInt32.toBitVec = decide (0 < x) := by
  have h := Int32.lt_iff_toBitVec_slt (a := 0) (b := x)
  cases hb : (0#32).slt x.toUInt32.toBitVec <;> simp_all [Int32.toBitVec_toUInt32]

theorem i32_ofInt_nat (n : Nat) : (Int32.ofInt (n : Int)).toUInt32 = UInt32.ofNat n := by
  apply UInt32.toBitVec_inj.mp
  simp [Int32.ofInt]
  rfl

theorem runFast_floatList_get {resolveProg : String → Option (List JvmInstr)}
    {d sf f pc pc0 : Nat} {prog rest : List JvmInstr} {xs : List Float32} {i : Nat}
    (hi : i < xs.length) (hi31 : i < 2 ^ 31)
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap UiExt} {hp : UiHeap} :
    Jvm.runJvmResFast (mkUiCommonHooks resolveProg d sf) (f + 1) prog pc
        (.invokeinterface "java/util/List" "get" "(I)Ljava/lang/Object;" :: rest)
        ⟨pc0, .i32 (UInt32.ofNat i) :: .ext (.floatList xs) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkUiCommonHooks resolveProg d sf) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.boxedFloat xs[i]) :: stk, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_invokeinterface_step _ ?_
  have hs := Jvm.ui32_slt_zero_of_lt i hi31
  have ht := Jvm.ui32_ofNat_toNat_of_lt i hi31
  have key : Jvm.stepInvokeInterfaceGeneric (mkUiCommonHooks resolveProg d sf)
      ⟨pc, .i32 (UInt32.ofNat i) :: .ext (.floatList xs) :: stk, locs, jh, hp⟩
      "java/util/List" "get" "(I)Ljava/lang/Object;" =
      if (UInt32.ofNat i).toBitVec.slt 0#32 then .inr none
      else if h : (UInt32.ofNat i).toNat < xs.length then
        .inl (some ⟨pc + 1, .ext (.boxedFloat xs[(UInt32.ofNat i).toNat]) :: stk, locs, jh, hp⟩)
      else .inr none := by
    cases d <;> rfl
  rw [key]
  simp only [hs, Bool.false_eq_true, ↓reduceIte, ht, hi, ↓reduceDIte]

theorem runFast_checkcast_comparable {resolveProg : String → Option (List JvmInstr)}
    {d sf f pc pc0 : Nat} {prog rest : List JvmInstr} {v : Float32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap UiExt} {hp : UiHeap} :
    Jvm.runJvmResFast (mkUiCommonHooks resolveProg d sf) (f + 1) prog pc
        (.checkcast "java/lang/Comparable" :: rest) ⟨pc0, .ext (.boxedFloat v) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkUiCommonHooks resolveProg d sf) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.boxedFloat v) :: stk, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  cases d <;> rfl

theorem runFast_compareTo {resolveProg : String → Option (List JvmInstr)}
    {d sf f pc pc0 : Nat} {prog rest : List JvmInstr} {a b : Float32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap UiExt} {hp : UiHeap} :
    Jvm.runJvmResFast (mkUiCommonHooks resolveProg d sf) (f + 1) prog pc
        (.invokeinterface "java/lang/Comparable" "compareTo" "(Ljava/lang/Object;)I" :: rest)
        ⟨pc0, .ext (.boxedFloat b) :: .ext (.boxedFloat a) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkUiCommonHooks resolveProg d sf) f prog (pc + 1) rest
        ⟨pc + 1, .i32 (floatCompare a b).toUInt32 :: stk, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_invokeinterface_step _ ?_
  cases d <;> rfl

theorem runFast_list_size_float {resolveProg : String → Option (List JvmInstr)}
    {d sf f pc pc0 : Nat} {prog rest : List JvmInstr} {xs : List Float32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap UiExt} {hp : UiHeap} :
    Jvm.runJvmResFast (mkUiCommonHooks resolveProg d sf) (f + 1) prog pc
        (.invokeinterface "java/util/List" "size" "()I" :: rest)
        ⟨pc0, .ext (.floatList xs) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkUiCommonHooks resolveProg d sf) f prog (pc + 1) rest
        ⟨pc + 1, .i32 (UInt32.ofNat xs.length) :: stk, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_invokeinterface_step _ ?_
  cases d <;> rfl

section GenericBranches
variable {hooks : Jvm.JvmHooks UiExt UiHeap}

theorem runFast_ifgt_branch {f1 pc target : Nat} {prog rest : List JvmInstr}
    {x : UInt32} {srest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap UiExt} {hp : UiHeap}
    (h : (0#32).slt x.toBitVec = true) :
    Jvm.runJvmResFast hooks (f1 + 1) prog pc (.ifgt target :: rest) ⟨pc, .i32 x :: srest, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f1 prog target (prog.drop target) ⟨target, srest, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch, h]

theorem runFast_ifgt_fallthrough {f1 pc target : Nat} {prog rest : List JvmInstr}
    {x : UInt32} {srest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap UiExt} {hp : UiHeap}
    (h : (0#32).slt x.toBitVec = false) :
    Jvm.runJvmResFast hooks (f1 + 1) prog pc (.ifgt target :: rest) ⟨pc, .i32 x :: srest, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f1 prog (pc + 1) rest ⟨pc + 1, srest, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch, h]

theorem runFast_if_icmpge_branch {f1 pc target : Nat} {prog rest : List JvmInstr}
    {a b : UInt32} {srest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap UiExt} {hp : UiHeap}
    (h : b.toBitVec.sle a.toBitVec = true) :
    Jvm.runJvmResFast hooks (f1 + 1) prog pc (.if_icmpge target :: rest)
        ⟨pc, .i32 b :: .i32 a :: srest, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f1 prog target (prog.drop target) ⟨target, srest, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch, h]

theorem runFast_if_icmpge_fallthrough {f1 pc target : Nat} {prog rest : List JvmInstr}
    {a b : UInt32} {srest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap UiExt} {hp : UiHeap}
    (h : b.toBitVec.sle a.toBitVec = false) :
    Jvm.runJvmResFast hooks (f1 + 1) prog pc (.if_icmpge target :: rest)
        ⟨pc, .i32 b :: .i32 a :: srest, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f1 prog (pc + 1) rest ⟨pc + 1, srest, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch, h]

theorem runFast_idiv2 {f pc pc0 : Nat} {prog rest : List JvmInstr} {s : Nat} (hs : s < 2 ^ 31)
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap UiExt} {hp : UiHeap} :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.idiv :: rest)
        ⟨pc0, .i32 2 :: .i32 (UInt32.ofNat s) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest
        ⟨pc + 1, .i32 (UInt32.ofNat (s / 2)) :: stk, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  have h := u32_idiv2_ofNat s hs
  dsimp only [Jvm.stepInstr, Jvm.JvmVal.asI32?]
  rw [h]

end GenericBranches

theorem runFast_ireturn {resolveProg : String → Option (List JvmInstr)}
    {d sf f pc pc0 : Nat} {prog rest : List JvmInstr} {x : UInt32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap UiExt} {hp : UiHeap} :
    Jvm.runJvmResFast (mkUiCommonHooks resolveProg d sf) (f + 1) prog pc (.ireturn :: rest)
        ⟨pc0, .i32 x :: stk, locs, jh, hp⟩ =
      some (.i32 x, ⟨pc, .i32 x :: stk, locs, jh, hp⟩) := by
  rw [Jvm.runJvmResFast_step_nonbranch _ f prog pc .ireturn rest _ rfl (by simp)]
  cases d <;> rfl

/-! ### `floorBinarySearch` -/

/-- Locals at the loop head of `floorBinarySearch`: the list, the boxed value, `low`, and `high`. -/
def floorLocs (keys : List Float32) (value : Float32) (low high : Nat) (rest : Nat → JvmVal) :
    Nat → JvmVal :=
  setLocal (setLocal (setLocal (setLocal rest 0 (.ext (.floatList keys))) 1 (.ext (.boxedFloat value)))
    2 (.i32 (UInt32.ofNat low))) 3 (.i32 (UInt32.ofNat high))

theorem floorLocs_setLow (keys : List Float32) (value : Float32) (low high mid : Nat) (rest : Nat → JvmVal) :
    setLocal (setLocal (floorLocs keys value low high rest) 4 (.i32 (UInt32.ofNat mid))) 2
        (.i32 (UInt32.ofNat mid)) =
      floorLocs keys value mid high (setLocal rest 4 (.i32 (UInt32.ofNat mid))) := by
  funext i
  simp only [floorLocs, setLocal]
  by_cases h2 : i = 2 <;> by_cases h3 : i = 3 <;> by_cases h4 : i = 4 <;> by_cases h1 : i = 1 <;>
    by_cases h0 : i = 0 <;> simp_all

theorem floorLocs_setHigh (keys : List Float32) (value : Float32) (low high mid : Nat) (rest : Nat → JvmVal) :
    setLocal (setLocal (floorLocs keys value low high rest) 4 (.i32 (UInt32.ofNat mid))) 3
        (.i32 (UInt32.ofNat mid)) =
      floorLocs keys value low mid (setLocal rest 4 (.i32 (UInt32.ofNat mid))) := by
  funext i
  simp only [floorLocs, setLocal]
  by_cases h2 : i = 2 <;> by_cases h3 : i = 3 <;> by_cases h4 : i = 4 <;> by_cases h1 : i = 1 <;>
    by_cases h0 : i = 0 <;> simp_all

theorem floorBinarySearch_loop_equiv (resolveProg : String → Option (List JvmInstr)) (d sf : Nat)
    (keys : List Float32) (value : Float32) (hlen : keys.length < 2 ^ 30) (hp : UiHeap)
    (jh : Jvm.JvmHeap UiExt) :
    ∀ n low high (rest : Nat → JvmVal) (k : Nat),
      high - low ≤ n → low < high → high ≤ keys.length →
      ∃ L', Jvm.runJvmResFast (mkUiCommonHooks resolveProg d sf) (k + 7 + 21 * n) EasingPiecewiseKt_floorBinarySearch_prog 14
          (EasingPiecewiseKt_floorBinarySearch_prog.drop 14) ⟨14, [], floorLocs keys value low high rest, jh, hp⟩ =
        some (.i32 (UInt32.ofNat (floorBinarySearchLoop keys value low high n)),
          ⟨39, [.i32 (UInt32.ofNat (floorBinarySearchLoop keys value low high n))], L', jh, hp⟩) := by
  intro n
  induction n with
  | zero => intro low high rest k hn hlh hhi; omega
  | succ n ih =>
    intro low high rest k hn hlh hhi
    have hlow31 : low + 1 < 2 ^ 31 := by omega
    have hhigh31 : high < 2 ^ 31 := by omega
    by_cases hstop : high ≤ low + 1
    · apply Exists.intro
      conv => lhs; arg 5; dsimp only [EasingPiecewiseKt_floorBinarySearch_prog, List.drop]
      rw [show k + 7 + 21 * (n + 1) = (k + 7 + 21 * n + 16) + 1 + 1 + 1 + 1 + 1 by omega]
      ui_step_blk
      rw [show UInt32.ofNat low + 1 = UInt32.ofNat (low + 1) from (UInt32.ofNat_add low 1).symm]
      have hle : (UInt32.ofNat high).toBitVec.sle (UInt32.ofNat (low + 1)).toBitVec = true := by
        rw [u32_sle_ofNat high (low + 1) hhigh31 hlow31]; simp [hstop]
      rw [runFast_if_icmpge_branch hle]
      have hmodel : floorBinarySearchLoop keys value low high (n + 1) = low := by
        simp [floorBinarySearchLoop, show ¬ (low + 1 < high) by omega]
      rw [hmodel]
      conv => lhs; arg 5; dsimp only [EasingPiecewiseKt_floorBinarySearch_prog, List.drop]
      ui_step_blk
      rw [runFast_ireturn]
    · have hlt : (UInt32.ofNat high).toBitVec.sle (UInt32.ofNat (low + 1)).toBitVec = false := by
        rw [u32_sle_ofNat high (low + 1) hhigh31 hlow31]; simp; omega
      have hmid : (low + high) / 2 < keys.length := by omega
      have hget : keys[(low + high) / 2]! = keys[(low + high) / 2] := getElem!_pos keys _ hmid
      by_cases hle : floatCompare keys[(low + high) / 2] value ≤ 0
      · have hmodel : floorBinarySearchLoop keys value low high (n + 1) =
            floorBinarySearchLoop keys value ((low + high) / 2) high n := by
          simp [floorBinarySearchLoop, show low + 1 < high by omega, hget, hle]
        rw [hmodel]
        obtain ⟨L', hL'⟩ := ih ((low + high) / 2) high (setLocal rest 4 (.i32 (UInt32.ofNat ((low + high) / 2)))) k
          (by omega) (by omega) hhi
        apply Exists.intro
        conv => lhs; arg 5; dsimp only [EasingPiecewiseKt_floorBinarySearch_prog, List.drop]
        rw [show k + 7 + 21 * (n + 1) = (k + 7 + 21 * n + 16) + 1 + 1 + 1 + 1 + 1 by omega]
        ui_step_blk
        rw [show UInt32.ofNat low + 1 = UInt32.ofNat (low + 1) from (UInt32.ofNat_add low 1).symm]
        rw [runFast_if_icmpge_fallthrough hlt]
        ui_step_blk
        rw [show UInt32.ofNat low + UInt32.ofNat high = UInt32.ofNat (low + high) from
          (UInt32.ofNat_add low high).symm]
        rw [runFast_idiv2 (by omega)]
        ui_step_blk
        rw [runFast_floatList_get hmid (by omega)]
        rw [runFast_checkcast_comparable]
        ui_step_blk
        rw [runFast_compareTo]
        have hgt : (0#32).slt (floatCompare keys[(low + high) / 2] value).toUInt32.toBitVec = false := by
          rw [i32_zero_slt]; simp [Int32.not_lt.mpr hle]
        rw [runFast_ifgt_fallthrough hgt]
        ui_step_blk
        rw [Jvm.runJvmResFast_goto, floorLocs_setLow]
        exact hL'
      · have hmodel : floorBinarySearchLoop keys value low high (n + 1) =
            floorBinarySearchLoop keys value low ((low + high) / 2) n := by
          simp [floorBinarySearchLoop, show low + 1 < high by omega, hget, hle]
        rw [hmodel]
        obtain ⟨L', hL'⟩ := ih low ((low + high) / 2) (setLocal rest 4 (.i32 (UInt32.ofNat ((low + high) / 2)))) k
          (by omega) (by omega) (by omega)
        apply Exists.intro
        conv => lhs; arg 5; dsimp only [EasingPiecewiseKt_floorBinarySearch_prog, List.drop]
        rw [show k + 7 + 21 * (n + 1) = (k + 7 + 21 * n + 16) + 1 + 1 + 1 + 1 + 1 by omega]
        ui_step_blk
        rw [show UInt32.ofNat low + 1 = UInt32.ofNat (low + 1) from (UInt32.ofNat_add low 1).symm]
        rw [runFast_if_icmpge_fallthrough hlt]
        ui_step_blk
        rw [show UInt32.ofNat low + UInt32.ofNat high = UInt32.ofNat (low + high) from
          (UInt32.ofNat_add low high).symm]
        rw [runFast_idiv2 (by omega)]
        ui_step_blk
        rw [runFast_floatList_get hmid (by omega)]
        rw [runFast_checkcast_comparable]
        ui_step_blk
        rw [runFast_compareTo]
        have hgt : (0#32).slt (floatCompare keys[(low + high) / 2] value).toUInt32.toBitVec = true := by
          rw [i32_zero_slt]; simp [Int32.not_le.mp hle]
        rw [runFast_ifgt_branch hgt]
        conv => lhs; arg 5; dsimp only [EasingPiecewiseKt_floorBinarySearch_prog, List.drop]
        ui_step_blk
        rw [Jvm.runJvmResFast_goto, floorLocs_setHigh]
        exact hL'

theorem log2_lt_self (n : Nat) (hn : 0 < n) : Nat.log2 n < n := by
  rw [Nat.log2_lt (by omega)]
  exact Nat.lt_two_pow_self

/-- `floorBinarySearch` on a nonempty list of fewer than `2^30` keys (so `low + high` cannot overflow) returns the
model's floor index, or `-1` when `value` precedes the first key. -/
theorem floorBinarySearch_equiv (resolveProg : String → Option (List JvmInstr)) (d sf fuel : Nat)
    (keys : List Float32) (value : Float32) (hne : keys ≠ []) (hlen : keys.length < 2 ^ 30)
    (hf : 21 * keys.length + 20 ≤ fuel) (hp : UiHeap) (jh : Jvm.JvmHeap UiExt) :
    ∃ endSt, Jvm.runJvmRes (mkUiCommonHooks resolveProg d sf) fuel EasingPiecewiseKt_floorBinarySearch_prog
        (initUiJvmState [(0, .ext (.floatList keys)), (1, .ext (.boxedFloat value))] hp jh) =
      some (.i32 (Int32.ofInt (floorBinarySearch keys value)).toUInt32, endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  have hpos : 0 < keys.length := by
    cases keys with
    | nil => exact absurd rfl hne
    | cons _ _ => simp
  have hlen0 : keys.length ≠ 0 := by omega
  suffices h : ∃ L, Jvm.runJvmResFast (mkUiCommonHooks resolveProg d sf) (k + (21 * keys.length + 20))
      EasingPiecewiseKt_floorBinarySearch_prog 0 EasingPiecewiseKt_floorBinarySearch_prog
      (initUiJvmState [(0, .ext (.floatList keys)), (1, .ext (.boxedFloat value))] hp jh) =
      some (.i32 (Int32.ofInt (floorBinarySearch keys value)).toUInt32,
        ⟨if floatCompare keys[0] value ≤ 0 then 39 else 13,
          [.i32 (Int32.ofInt (floorBinarySearch keys value)).toUInt32], L, jh, hp⟩) by
    obtain ⟨L, hL⟩ := h
    exact ⟨_, Jvm.runJvmRes_of_runJvmResFast0 _ _ _ _ _ rfl hL, rfl, rfl⟩
  simp only [initUiJvmState, Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
  by_cases h0 : floatCompare keys[0] value ≤ 0
  · have hfuel_log : floorBinarySearchFuel keys.length ≤ keys.length := by
      have := log2_lt_self keys.length hpos
      simp only [floorBinarySearchFuel]; omega
    have hloopEq : floorBinarySearchLoop keys value 0 keys.length keys.length =
        floorBinarySearchLoop keys value 0 keys.length (floorBinarySearchFuel keys.length) :=
      floorBinarySearchLoop_terminates_in_log keys value 0 keys.length keys.length hpos (Nat.le_refl _) hfuel_log
    have hmodel : floorBinarySearch keys value =
        (floorBinarySearchLoop keys value 0 keys.length keys.length : Int) := by
      rw [hloopEq]
      simp [floorBinarySearch, hlen0, show ¬ (floatCompare keys[0] value > 0) from Int32.not_lt.mpr h0]
    rw [hmodel, i32_ofInt_nat]
    simp only [h0, ↓reduceIte]
    obtain ⟨L', hL'⟩ := floorBinarySearch_loop_equiv resolveProg d sf keys value hlen hp jh keys.length 0
      keys.length (fun _ => .i32 0) (k + 1) (by omega) hpos (Nat.le_refl _)
    refine ⟨L', ?_⟩
    conv => lhs; arg 5; dsimp only [EasingPiecewiseKt_floorBinarySearch_prog]
    rw [show k + (21 * keys.length + 20) = (k + 1 + 7 + 21 * keys.length) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
      1 + 1 + 1 + 1 by omega]
    ui_step_blk
    rw [runFast_list_size_float]
    ui_step_blk
    rw [show (0 : UInt32) = UInt32.ofNat 0 from rfl]
    rw [runFast_floatList_get hpos (by omega)]
    rw [runFast_checkcast_comparable]
    ui_step_blk
    rw [runFast_compareTo]
    rw [Jvm.runJvmResFast_ifle_branch _ (by rw [i32_sle_zero]; simp [h0])]
    exact hL'
  · have hmodel : floorBinarySearch keys value = -1 := by
      simp [floorBinarySearch, hlen0, show floatCompare keys[0] value > 0 from Int32.not_le.mp h0]
    rw [hmodel]
    simp only [h0, ↓reduceIte]
    apply Exists.intro
    conv => lhs; arg 5; dsimp only [EasingPiecewiseKt_floorBinarySearch_prog]
    rw [show k + (21 * keys.length + 20) = (k + 21 * keys.length + 6) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
      1 + 1 + 1 + 1 + 1 + 1 by omega]
    ui_step_blk
    rw [runFast_list_size_float]
    ui_step_blk
    rw [show (0 : UInt32) = UInt32.ofNat 0 from rfl]
    rw [runFast_floatList_get hpos (by omega)]
    rw [runFast_checkcast_comparable]
    ui_step_blk
    rw [runFast_compareTo]
    rw [Jvm.runJvmResFast_ifle_fallthrough _ (by rw [i32_sle_zero]; simp [h0])]
    ui_step_blk
    rw [runFast_ireturn]
    rfl

end UiCommon.KotlinJvmVerification
