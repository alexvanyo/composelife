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
import JvmSemantics
import KotlinJvmBytecode

namespace ResourceState.KotlinJvmVerification

open ResourceState.JvmVerification
open ResourceState.KotlinJvmBytecode
open ResourceState.Model

/-! ### Program Lookup, Heap Invariants, and Fuel Monotonicity -/

def rsProgLookup (fnTag : String) : Option (List JvmInstr) :=
  match fnTag with
  | "ResourceStateKt.isLoading" => some ResourceStateKt_isLoading_prog
  | "ResourceStateKt.isSuccess" => some ResourceStateKt_isSuccess_prog
  | "ResourceStateKt.isFailure" => some ResourceStateKt_isFailure_prog
  | "ResourceStateKt.successes" => some ResourceStateKt_successes_prog
  | "ResourceStateKt.firstSuccess" => some ResourceStateKt_firstSuccess_prog
  | "ResourceStateKt.map" => some ResourceStateKt_map_prog
  | "ResourceStateKt.flatMap" => some ResourceStateKt_flatMap_prog
  | "ResourceStateKt.combine" => some ResourceStateKt_combine_prog
  | "ResourceStateKt.combine_1" => some ResourceStateKt_combine_1_prog
  | "ResourceStateKt.combine_2" => some ResourceStateKt_combine_2_prog
  | "ResourceStateKt.asResourceState" => some ResourceStateKt_asResourceState_prog
  | "ResourceStateKt.collectAsState" => some ResourceStateKt_collectAsState_prog
  | _ => none

def ExtendsRsProgs (resolveProg : String → Option (List JvmInstr)) : Prop :=
  ∀ fnTag prog, rsProgLookup fnTag = some prog → resolveProg fnTag = some prog

theorem rsProgLookup_extends : ExtendsRsProgs rsProgLookup :=
  fun _ _ h => h

def HasRsStaticsClean (jh : Jvm.JvmHeap RsExt) : Prop :=
  jh.getStatic? "com/alexvanyo/composelife/resourcestate/ResourceState$Loading" "INSTANCE" = none

theorem emptyJvmHeap_staticsClean : HasRsStaticsClean ({} : Jvm.JvmHeap RsExt) := rfl

instance (resolveProg : String → Option (List JvmInstr)) (d fuel : Nat) :
    Jvm.HasDefaultIsZero (mkRsHooks resolveProg d fuel) where
  isZero?_eq := by cases d <;> rfl

theorem runJvmResFast_mono {Ext Heap : Type} (hooks : Jvm.JvmHooks Ext Heap) :
    ∀ {f1 f2 : Nat} {prog : List JvmInstr} {pc : Nat} {instrs : List JvmInstr}
      {st : Jvm.JvmState Ext Heap} {ra : Jvm.JvmVal Ext} {rb : Jvm.JvmState Ext Heap},
      f1 ≤ f2 →
      Jvm.runJvmResFast hooks f1 prog pc instrs st = some (ra, rb) →
      Jvm.runJvmResFast hooks f2 prog pc instrs st = some (ra, rb) := by
  intro f1
  induction f1 using Nat.strongRecOn with
  | ind f1Orig ih =>
    intro f2 prog pc instrs st ra rb hle hfast
    cases f1Orig with
    | zero => simp [Jvm.runJvmResFast] at hfast
    | succ f1 =>
      cases f2 with
      | zero => omega
      | succ f2 =>
        have hle' : f1 ≤ f2 := Nat.le_of_succ_le_succ hle
        cases instrs with
        | nil => simp [Jvm.runJvmResFast] at hfast
        | cons instr rest =>
          by_cases hbr : Jvm.isBranchInstr instr = true
          · rw [Jvm.runJvmResFast_at_branch_cons hooks f1 prog pc instr rest st hbr] at hfast
            rw [Jvm.runJvmResFast_at_branch_cons hooks f2 prog pc instr rest st hbr]
            dsimp only [Jvm.evalResBranchInstrCons] at hfast ⊢
            rw [ite_eq_left hbr] at hfast ⊢
            cases instr <;> simp [Jvm.isBranchInstr] at hbr
            · dsimp only [Jvm.dispatchBranch] at hfast ⊢
              rcases hstk : st.stack with _ | ⟨v, s⟩ <;> simp [hstk] at hfast ⊢
              rcases hz : hooks.isZero? v with _ | c <;> simp [hz] at hfast ⊢
              split at hfast <;> simp_all <;> exact ih f1 (Nat.lt_succ_self f1) hle' hfast
            · dsimp only [Jvm.dispatchBranch] at hfast ⊢
              rcases hstk : st.stack with _ | ⟨v, s⟩ <;> simp [hstk] at hfast ⊢
              rcases hz : hooks.isZero? v with _ | c <;> simp [hz] at hfast ⊢
              split at hfast <;> simp_all <;> exact ih f1 (Nat.lt_succ_self f1) hle' hfast
            · dsimp only [Jvm.dispatchBranch] at hfast ⊢
              rcases hstk : st.stack with _ | ⟨v, s⟩ <;> simp [hstk] at hfast ⊢
              rcases ha : v.asI32? with _ | iv <;> simp [ha] at hfast ⊢
              split at hfast <;> simp_all <;> exact ih f1 (Nat.lt_succ_self f1) hle' hfast
            · dsimp only [Jvm.dispatchBranch] at hfast ⊢
              rcases hstk : st.stack with _ | ⟨v, s⟩ <;> simp [hstk] at hfast ⊢
              rcases ha : v.asI32? with _ | iv <;> simp [ha] at hfast ⊢
              split at hfast <;> simp_all <;> exact ih f1 (Nat.lt_succ_self f1) hle' hfast
            · dsimp only [Jvm.dispatchBranch] at hfast ⊢
              rcases hstk : st.stack with _ | ⟨v, s⟩ <;> simp [hstk] at hfast ⊢
              rcases ha : v.asI32? with _ | iv <;> simp [ha] at hfast ⊢
              split at hfast <;> simp_all <;> exact ih f1 (Nat.lt_succ_self f1) hle' hfast
            · dsimp only [Jvm.dispatchBranch] at hfast ⊢
              rcases hstk : st.stack with _ | ⟨v, s⟩ <;> simp [hstk] at hfast ⊢
              rcases ha : v.asI32? with _ | iv <;> simp [ha] at hfast ⊢
              split at hfast <;> simp_all <;> exact ih f1 (Nat.lt_succ_self f1) hle' hfast
            · dsimp only [Jvm.dispatchBranch] at hfast ⊢
              rcases hstk : st.stack with _ | ⟨v, s⟩ <;> simp [hstk] at hfast ⊢
              split at hfast <;> simp_all <;> exact ih f1 (Nat.lt_succ_self f1) hle' hfast
            · dsimp only [Jvm.dispatchBranch] at hfast ⊢
              rcases hstk : st.stack with _ | ⟨v, s⟩ <;> simp [hstk] at hfast ⊢
              split at hfast <;> simp_all <;> exact ih f1 (Nat.lt_succ_self f1) hle' hfast
            · dsimp only [Jvm.dispatchBranch] at hfast ⊢
              rcases hstk : st.stack with _ | ⟨b, _ | ⟨a, s⟩⟩ <;> simp [hstk] at hfast ⊢
              rcases ha : a.asI32? with _ | av <;> rcases hb : b.asI32? with _ | bv <;> simp [ha, hb] at hfast ⊢
              split at hfast <;> simp_all <;> exact ih f1 (Nat.lt_succ_self f1) hle' hfast
            · dsimp only [Jvm.dispatchBranch] at hfast ⊢
              rcases hstk : st.stack with _ | ⟨b, _ | ⟨a, s⟩⟩ <;> simp [hstk] at hfast ⊢
              rcases ha : a.asI32? with _ | av <;> rcases hb : b.asI32? with _ | bv <;> simp [ha, hb] at hfast ⊢
              split at hfast <;> simp_all <;> exact ih f1 (Nat.lt_succ_self f1) hle' hfast
            · dsimp only [Jvm.dispatchBranch] at hfast ⊢
              rcases hstk : st.stack with _ | ⟨b, _ | ⟨a, s⟩⟩ <;> simp [hstk] at hfast ⊢
              rcases ha : a.asI32? with _ | av <;> rcases hb : b.asI32? with _ | bv <;> simp [ha, hb] at hfast ⊢
              split at hfast <;> simp_all <;> exact ih f1 (Nat.lt_succ_self f1) hle' hfast
            · dsimp only [Jvm.dispatchBranch] at hfast ⊢
              rcases hstk : st.stack with _ | ⟨b, _ | ⟨a, s⟩⟩ <;> simp [hstk] at hfast ⊢
              rcases ha : a.asI32? with _ | av <;> rcases hb : b.asI32? with _ | bv <;> simp [ha, hb] at hfast ⊢
              split at hfast <;> simp_all <;> exact ih f1 (Nat.lt_succ_self f1) hle' hfast
            · dsimp only [Jvm.dispatchBranch] at hfast ⊢
              rcases hstk : st.stack with _ | ⟨b, _ | ⟨a, s⟩⟩ <;> simp [hstk] at hfast ⊢
              rcases ha : a.asI32? with _ | av <;> rcases hb : b.asI32? with _ | bv <;> simp [ha, hb] at hfast ⊢
              split at hfast <;> simp_all <;> exact ih f1 (Nat.lt_succ_self f1) hle' hfast
            · dsimp only [Jvm.dispatchBranch] at hfast ⊢
              rcases hstk : st.stack with _ | ⟨b, _ | ⟨a, s⟩⟩ <;> simp [hstk] at hfast ⊢
              rcases ha : a.asI32? with _ | av <;> rcases hb : b.asI32? with _ | bv <;> simp [ha, hb] at hfast ⊢
              split at hfast <;> simp_all <;> exact ih f1 (Nat.lt_succ_self f1) hle' hfast
            · dsimp only [Jvm.dispatchBranch] at hfast ⊢
              rcases hstk : st.stack with _ | ⟨b, _ | ⟨a, s⟩⟩ <;> simp [hstk] at hfast ⊢
              rcases hr : Jvm.JvmVal.refEq? hooks.beqRefExt a b with _ | r <;> simp [hr] at hfast ⊢
              split at hfast <;> simp_all <;> exact ih f1 (Nat.lt_succ_self f1) hle' hfast
            · dsimp only [Jvm.dispatchBranch] at hfast ⊢
              rcases hstk : st.stack with _ | ⟨b, _ | ⟨a, s⟩⟩ <;> simp [hstk] at hfast ⊢
              rcases hr : Jvm.JvmVal.refEq? hooks.beqRefExt a b with _ | r <;> simp [hr] at hfast ⊢
              split at hfast <;> simp_all <;> exact ih f1 (Nat.lt_succ_self f1) hle' hfast
            · exact ih f1 (Nat.lt_succ_self f1) hle' hfast
            · dsimp only [Jvm.dispatchBranch] at hfast ⊢
              rcases hstk : st.stack with _ | ⟨k, s⟩ <;> simp [hstk] at hfast ⊢
              rcases ha : k.asI32? with _ | kv <;> simp [ha] at hfast ⊢
              exact ih f1 (Nat.lt_succ_self f1) hle' hfast
            · dsimp only [Jvm.dispatchBranch] at hfast ⊢
              rcases hstk : st.stack with _ | ⟨k, s⟩ <;> simp [hstk] at hfast ⊢
              rcases ha : k.asI32? with _ | kv <;> simp [ha] at hfast ⊢
              exact ih f1 (Nat.lt_succ_self f1) hle' hfast
          · have hbrf : Jvm.isBranchInstr instr = false := by
              cases hb : Jvm.isBranchInstr instr <;> simp_all
            by_cases hi2l : instr = .i2l ∧ ∃ r', rest = .lconst 4294967295 :: .land :: r'
            · rcases hi2l with ⟨rfl, r', rfl⟩
              cases f1 with
              | zero => simp [Jvm.runJvmResFast] at hfast
              | succ f1b =>
                cases f2 with
                | zero => omega
                | succ f2b =>
                  cases f1b with
                  | zero => simp [Jvm.runJvmResFast] at hfast
                  | succ f1c =>
                    cases f2b with
                    | zero => omega
                    | succ f2c =>
                      cases hstk : st.stack with
                      | nil => simp [Jvm.runJvmResFast, hstk] at hfast
                      | cons hd tl =>
                        cases hd with
                        | i32 x =>
                          simp only [Jvm.runJvmResFast, hstk] at hfast ⊢
                          exact ih f1c (by omega) (by omega) hfast
                        | _ => simp [Jvm.runJvmResFast, hstk] at hfast
            · rw [Jvm.runJvmResFast_step_nonbranch hooks f1 prog pc instr rest st hbrf hi2l] at hfast
              rw [Jvm.runJvmResFast_step_nonbranch hooks f2 prog pc instr rest st hbrf hi2l]
              cases hstep : Jvm.stepInstr hooks instr { st with pc := pc } with
              | inl o =>
                cases o with
                | none => simp [hstep] at hfast
                | some st' =>
                  simp only [hstep] at hfast ⊢
                  split at hfast
                  · next hpc =>
                    rw [ite_eq_left hpc]
                    exact ih f1 (Nat.lt_succ_self f1) hle' hfast
                  · next hpc =>
                    rw [ite_eq_right hpc]
                    exact ih f1 (Nat.lt_succ_self f1) hle' hfast
              | inr r =>
                cases r with
                | none => simp [hstep] at hfast
                | some v =>
                  simp only [hstep] at hfast ⊢
                  exact hfast

theorem exists_run_done {Ext Heap : Type} (hooks : Jvm.JvmHooks Ext Heap)
    {fuel : Nat} {prog : List JvmInstr} {st : Jvm.JvmState Ext Heap}
    {v : Jvm.JvmVal Ext} {endPc : Nat} {endStk : List (Jvm.JvmVal Ext)}
    {endLocs : Nat → Jvm.JvmVal Ext} {jh : Jvm.JvmHeap Ext} {hp : Heap}
    (hpc : st.pc = 0)
    (h : Jvm.runJvmResFast hooks fuel prog 0 prog st =
      some (v, ⟨endPc, endStk, endLocs, jh, hp⟩)) :
    ∃ endSt,
      Jvm.runJvmRes hooks fuel prog st = some (v, endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp :=
  ⟨⟨endPc, endStk, endLocs, jh, hp⟩,
    Jvm.runJvmRes_of_runJvmResFast0 hooks fuel prog st _ hpc h, rfl, rfl⟩

theorem exists_run_done_mono {Ext Heap : Type} (hooks : Jvm.JvmHooks Ext Heap)
    {f1 f2 : Nat} (hle : f1 ≤ f2) {prog : List JvmInstr} {st : Jvm.JvmState Ext Heap}
    {v : Jvm.JvmVal Ext} {jh : Jvm.JvmHeap Ext} {hp : Heap}
    (hpc : st.pc = 0)
    (h : ∃ endPc endStk endLocs,
      Jvm.runJvmResFast hooks f1 prog 0 prog st =
        some (v, ⟨endPc, endStk, endLocs, jh, hp⟩)) :
    ∃ endSt,
      Jvm.runJvmRes hooks f2 prog st = some (v, endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  rcases h with ⟨endPc, endStk, endLocs, hfast⟩
  exact exists_run_done hooks hpc (runJvmResFast_mono hooks hle hfast)

/-! ### Fast Symbolic Block Stepper & Domain Step Lemmas -/

def isRsStop : JvmInstr → Bool
  | .invokestatic _ _ _ | .invokevirtual _ _ _ | .invokespecial _ _ _ | .invokeinterface _ _ _
  | .getstatic _ _ _ | .putstatic _ _ _ | .getfield _ _ _ | .putfield _ _ _
  | .newClass _ | .anewarray _ | .aaload | .aastore | .arraylength
  | .checkcast _ | .instanceof _ | .athrow
  | .areturn | .ireturn | .lreturn | .freturn | .dreturn | .vreturn
  | .ifeq _ | .ifne _ | .iflt _ | .ifle _ | .ifgt _ | .ifge _
  | .ifnull _ | .ifnonnull _ | .if_icmpeq _ | .if_icmpne _ | .if_icmplt _
  | .if_icmpge _ | .if_icmpgt _ | .if_icmple _ | .if_acmpeq _ | .if_acmpne _
  | .goto _ | .tableswitch _ _ _ | .lookupswitch _ _ => true
  | _ => false

section StepTactics

open Lean Elab Tactic Meta

def rsOpaqueConsts : NameSet :=
  NameSet.empty
    |>.insert ``mkRsHooks
    |>.insert ``rsProgLookup
    |>.insert ``ResourceStateKt_isLoading_prog
    |>.insert ``ResourceStateKt_isSuccess_prog
    |>.insert ``ResourceStateKt_isFailure_prog
    |>.insert ``ResourceStateKt_successes_prog
    |>.insert ``ResourceStateKt_firstSuccess_prog
    |>.insert ``ResourceStateKt_map_prog
    |>.insert ``ResourceStateKt_flatMap_prog
    |>.insert ``ResourceStateKt_combine_prog
    |>.insert ``ResourceStateKt_combine_1_prog
    |>.insert ``ResourceStateKt_combine_2_prog
    |>.insert ``ResourceStateKt_asResourceState_prog
    |>.insert ``ResourceStateKt_collectAsState_prog
    |>.insert ``RsVal.toJvmVal
    |>.insert ``RsVal.ofJvmVal?
    |>.insert ``Model.ResourceState.isLoading
    |>.insert ``Model.ResourceState.isSuccess
    |>.insert ``Model.ResourceState.isFailure
    |>.insert ``Model.ResourceState.map
    |>.insert ``Model.ResourceState.flatMap
    |>.insert ``Model.combine2
    |>.insert ``Model.combine3
    |>.insert ``Model.combineMany
    |>.insert ``Model.successesFlow
    |>.insert ``Model.firstSuccessModel
    |>.insert ``Model.asResourceStateFlow
    |>.insert ``Model.collectAsStateModel

def rsInitConsts : List Name :=
  [``initRsJvmState, ``Jvm.initJvmState]

elab "rs_whnf_blk" : conv => withMainContext do
  let lhs ← Lean.Elab.Tactic.Conv.getLhs
  let res ← Jvm.Tactics.withOpaque rsOpaqueConsts
    (Jvm.Tactics.normJvmBlkExpr rsInitConsts (fun _ => pure none) lhs)
  Lean.Elab.Tactic.Conv.changeLhs res

elab "rs_norm_locals" : tactic =>
  Lean.Elab.Tactic.liftMetaTactic fun g => do
    let tgt ← instantiateMVars (← g.getType)
    let res ← Jvm.Tactics.normJvmLocalsExpr rsInitConsts (fun _ => pure none) [] tgt
    return [← g.replaceTargetDefEq res]

elab "rs_norm_run_args" : tactic =>
  Lean.Elab.Tactic.liftMetaTactic fun g => do
    let tgt ← instantiateMVars (← g.getType)
    let normSt := fun s : Expr => do
      let s1 ← Jvm.Tactics.withOpaque rsOpaqueConsts
        (Jvm.Tactics.normJvmBlkExpr rsInitConsts (fun _ => pure none) s)
      if s1.isAppOfArity ``Jvm.JvmState.mk 7 then
        let sa := s1.getAppArgs
        let pcField ← Jvm.Tactics.normJvmNatWith rsOpaqueConsts sa[2]!
        return mkAppN s1.getAppFn #[sa[0]!, sa[1]!, pcField, sa[3]!, sa[4]!, sa[5]!, sa[6]!]
      else
        return s1
    let normRun := fun b : Expr => do
      if b.isAppOfArity ``Jvm.runJvmResFast 8 then
        let ba := b.getAppArgs
        let fuel' ← Jvm.Tactics.withOpaque rsOpaqueConsts (whnf ba[3]!)
        let pc' ← Jvm.Tactics.withOpaque rsOpaqueConsts (whnf ba[5]!)
        let st' ← normSt ba[7]!
        let mut instrs' := ba[6]!
        let mut instrsEq : Option Expr := none
        if instrs'.isAppOfArity ``List.drop 3 then
          let da := instrs'.getAppArgs
          if let some n ← Jvm.Tactics.evalNatLit? da[1]! then
            let (rhs, eqP) ← Jvm.Tactics.fastDropListEq da[2]! n
            instrs' := rhs
            instrsEq := some eqP
        else if instrs'.isConst then
          if let some u ← unfoldDefinition? instrs' then
            instrs' := u
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

def isRsNonStop : TacticM Bool := do
  let tgt := (← getMainTarget).consumeMData
  let some (_, lhs, _) := tgt.eq? | return false
  let lhs := lhs.consumeMData
  if lhs.isAppOfArity ``Jvm.runJvmResFast 8 then
    let instrs ← whnf (lhs.getArg! 6)
    if instrs.isAppOfArity ``List.cons 3 then
      let instr := instrs.getArg! 1
      let br ← whnf (mkApp (mkConst ``isRsStop) instr)
      return br.isConstOf ``Bool.false
  return false

def isRsForwardGoto : TacticM Bool := do
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

elab "rs_step_one_chunk" : tactic => do
  let tgt := (← getMainTarget).consumeMData
  let some (_, lhs, _) := tgt.eq? | return ()
  let lhs := lhs.consumeMData
  if !lhs.isAppOfArity ``Jvm.runJvmResFast 8 then return ()
  evalTactic (← `(tactic| (conv => lhs; tactic => rs_norm_run_args)))
  evalTactic (← `(tactic| rw [Jvm.runJvmResFast_stepBlockChunkWith _ isRsStop 64]))
  if !(← getUnsolvedGoals).isEmpty then
    evalTactic (← `(tactic| (conv => lhs; arg 2; rs_whnf_blk)))
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
      evalTactic (← `(tactic| (conv => lhs; tactic => rs_norm_locals)))
      evalTactic (← `(tactic| (conv => lhs; tactic => rs_norm_run_args)))

elab "rs_step_blk" : tactic => do
  for _ in [:40] do
    if (← getUnsolvedGoals).isEmpty then break
    if ← isRsNonStop then
      evalTactic (← `(tactic| rs_step_one_chunk))
    else if ← isRsForwardGoto then
      evalTactic (← `(tactic| (conv => lhs; tactic => rs_norm_run_args)))
      evalTactic (← `(tactic| rw [Jvm.runJvmResFast_at_branch_cons _ (hbr := rfl)]))
      if !(← getUnsolvedGoals).isEmpty then
        evalTactic (← `(tactic| (
          (conv => lhs; arg 2; whnf)
          (conv => lhs; arg 4; whnf)
          (conv => lhs; arg 5; whnf)
          (conv => lhs; arg 7; rs_whnf_blk))))
        let tgt2 := (← getMainTarget).consumeMData
        let some (_, lhs2, _) := tgt2.eq? | break
        Jvm.Tactics.rwEvalBranchByInstrWith Jvm.Tactics.defaultEvalBranchThm true (lhs2.consumeMData.getArg! 6)
        if !(← getUnsolvedGoals).isEmpty then
          evalTactic (← `(tactic| (conv => lhs; tactic => rs_norm_locals; rs_norm_run_args)))
    else
      break

elab "rs_branch" : tactic => do
  let tgt := (← getMainTarget).consumeMData
  let some (_, lhs, _) := tgt.eq? | return ()
  let lhs := lhs.consumeMData
  if !lhs.isAppOfArity ``Jvm.runJvmResFast 8 then return ()
  evalTactic (← `(tactic| (conv => lhs; tactic => rs_norm_run_args)))
  evalTactic (← `(tactic| rw [Jvm.runJvmResFast_at_branch_cons _ (hbr := rfl)]))
  if !(← getUnsolvedGoals).isEmpty then
    evalTactic (← `(tactic| (
      (conv => lhs; arg 2; whnf)
      (conv => lhs; arg 4; whnf)
      (conv => lhs; arg 5; whnf)
      (conv => lhs; arg 7; rs_whnf_blk))))
    let tgt2 := (← getMainTarget).consumeMData
    let some (_, lhs2, _) := tgt2.eq? | return ()
    Jvm.Tactics.rwEvalBranchByInstrWith Jvm.Tactics.defaultEvalBranchThm true (lhs2.consumeMData.getArg! 6)
    if !(← getUnsolvedGoals).isEmpty then
      evalTactic (← `(tactic| try (first
        | rw [ite_eq_left (by decide)]
        | rw [ite_eq_right (by decide)])))
      if !(← getUnsolvedGoals).isEmpty then
        evalTactic (← `(tactic| (conv => lhs; tactic => rs_norm_locals; rs_norm_run_args)))

end StepTactics

/-! ### Domain Hook & Instruction Step Lemmas -/

theorem runJvmResFast_of_step {Ext Heap : Type} (hooks : Jvm.JvmHooks Ext Heap)
    {f pc pc0 : Nat} {prog rest : List JvmInstr} {instr : JvmInstr}
    {stk : List (Jvm.JvmVal Ext)} {locs : Nat → Jvm.JvmVal Ext} {jh : Jvm.JvmHeap Ext} {hp : Heap}
    (hbrf : Jvm.isBranchInstr instr = false)
    (hi2l : ¬(instr = .i2l ∧ ∃ r', rest = .lconst 4294967295 :: .land :: r'))
    {st' : Jvm.JvmState Ext Heap}
    (hstep : Jvm.stepInstr hooks instr ⟨pc, stk, locs, jh, hp⟩ = .inl (some st'))
    (hpc' : st'.pc = pc + 1) :
    Jvm.runJvmResFast hooks (f + 1) prog pc (instr :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest st' := by
  rw [Jvm.runJvmResFast_step_nonbranch hooks f prog pc instr rest _ hbrf hi2l]
  have hst : { (⟨pc0, stk, locs, jh, hp⟩ : Jvm.JvmState Ext Heap) with pc := pc } = ⟨pc, stk, locs, jh, hp⟩ := rfl
  rw [hst, hstep]
  simp [hpc']

theorem runJvmResFast_checkNotNullParam {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    {v : JvmVal} (hnn : v.isNull = false) {msg : String} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap RsExt} {hp : RsHeap} :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter"
          "(Ljava/lang/Object;Ljava/lang/String;)V" :: rest)
        ⟨pc0, .str msg :: v :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, stk, locs, jh, hp⟩ := by
  apply runJvmResFast_of_step _ rfl (by simp) _ rfl
  have h1 :
      Jvm.stepInstr (mkRsHooks resolveProg (d + 1) subFuel)
        (.invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter"
          "(Ljava/lang/Object;Ljava/lang/String;)V")
        ⟨pc, .str msg :: v :: stk, locs, jh, hp⟩ =
      (if v.isNull then .inr none else .inl (some ⟨pc + 1, stk, locs, jh, hp⟩)) := rfl
  rw [h1, hnn]
  rfl

theorem runJvmResFast_checkNotNull {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    {v : JvmVal} (hnn : v.isNull = false) {msg : String} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap RsExt} {hp : RsHeap} :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
          "(Ljava/lang/Object;Ljava/lang/String;)V" :: rest)
        ⟨pc0, .str msg :: v :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, stk, locs, jh, hp⟩ := by
  apply runJvmResFast_of_step _ rfl (by simp) _ rfl
  have h1 :
      Jvm.stepInstr (mkRsHooks resolveProg (d + 1) subFuel)
        (.invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
          "(Ljava/lang/Object;Ljava/lang/String;)V")
        ⟨pc, .str msg :: v :: stk, locs, jh, hp⟩ =
      (if v.isNull then .inr none else .inl (some ⟨pc + 1, stk, locs, jh, hp⟩)) := rfl
  rw [h1, hnn]
  rfl

theorem runJvmResFast_areEqual {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    {a b : JvmVal} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap RsExt} {hp : RsHeap}
    (ha : a.equalsModeled jh = true := by rfl) (hb : b.equalsModeled jh = true := by rfl) :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokestatic "kotlin/jvm/internal/Intrinsics" "areEqual"
          "(Ljava/lang/Object;Ljava/lang/Object;)Z" :: rest)
        ⟨pc0, b :: a :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .bool (Jvm.JvmVal.beqVal beqRsExt a b) :: stk, locs, jh, hp⟩ :=
  runJvmResFast_of_step _ rfl (by simp) (Jvm.stepInstr_areEqual _ ha hb) rfl

theorem runJvmResFast_getstatic_loading {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap RsExt} {hp : RsHeap}
    (hclean : HasRsStaticsClean jh) :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.getstatic "com/alexvanyo/composelife/resourcestate/ResourceState$Loading" "INSTANCE"
          "Lcom/alexvanyo/composelife/resourcestate/ResourceState$Loading;" :: rest)
        ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.res .loading) :: stk, locs, jh, hp⟩ := by
  apply runJvmResFast_of_step _ rfl (by simp) _ rfl
  dsimp only [Jvm.stepInstr]
  rw [hclean]
  rfl

theorem runJvmResFast_instanceof_res {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    {cls : String} {v : JvmVal} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap RsExt} {hp : RsHeap}
    (res : Bool)
    (heval : Jvm.evalInstanceOf (mkRsHooks resolveProg (d + 1) subFuel) jh cls v = res) :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.instanceof cls :: rest) ⟨pc0, v :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .i32 (if res then 1 else 0) :: stk, locs, jh, hp⟩ := by
  apply runJvmResFast_of_step _ rfl (by simp) _ rfl
  dsimp only [Jvm.stepInstr]
  rw [heval]

theorem runJvmResFast_checkcast_res {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    {cls : String} {v v' : JvmVal} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap RsExt} {hp : RsHeap}
    (heval : Jvm.evalCheckCast (mkRsHooks resolveProg (d + 1) subFuel) jh cls v = some v') :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.checkcast cls :: rest) ⟨pc0, v :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, v' :: stk, locs, jh, hp⟩ := by
  apply runJvmResFast_of_step _ rfl (by simp) _ rfl
  dsimp only [Jvm.stepInstr]
  rw [heval]

theorem runJvmResFast_newClass_rs {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    {cls : String} (hnsb : (cls == "java/lang/StringBuilder") = false)
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap RsExt} {hp : RsHeap} :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.newClass cls :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .allocRef cls :: stk, locs, jh, hp⟩ := by
  apply runJvmResFast_of_step _ rfl (by simp) _ rfl
  dsimp only [Jvm.stepInstr]
  rw [ite_eq_right (by rw [hnsb]; decide)]
  rfl

theorem runJvmResFast_ireturn_rs {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    {v : JvmVal} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap RsExt} {hp : RsHeap} :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.ireturn :: rest) ⟨pc0, v :: stk, locs, jh, hp⟩ =
      some (v, ⟨pc, v :: stk, locs, jh, hp⟩) := by
  rw [Jvm.runJvmResFast_step_nonbranch (hbr := rfl) (hno := by simp)]
  rfl

theorem runJvmResFast_areturn_rs {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    {v : JvmVal} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap RsExt} {hp : RsHeap} :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.areturn :: rest) ⟨pc0, v :: stk, locs, jh, hp⟩ =
      some (v, ⟨pc, v :: stk, locs, jh, hp⟩) := by
  rw [Jvm.runJvmResFast_step_nonbranch (hbr := rfl) (hno := by simp)]
  rfl

theorem runJvmResFast_success_getValue {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    {v : RsVal} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap RsExt} {hp : RsHeap} :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokevirtual "com/alexvanyo/composelife/resourcestate/ResourceState$Success"
          "getValue" "()Ljava/lang/Object;" :: rest)
        ⟨pc0, .ext (.res (.success v)) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, v.toJvmVal :: stk, locs, jh, hp⟩ :=
  runJvmResFast_of_step _ rfl (by simp) rfl rfl

theorem runJvmResFast_failure_getThrowable {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    {t : ThrowableModel} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap RsExt} {hp : RsHeap} :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokevirtual "com/alexvanyo/composelife/resourcestate/ResourceState$Failure"
          "getThrowable" "()Ljava/lang/Throwable;" :: rest)
        ⟨pc0, .ext (.res (.failure t)) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.throwable t) :: stk, locs, jh, hp⟩ :=
  runJvmResFast_of_step _ rfl (by simp) rfl rfl

theorem runJvmResFast_success_init {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    {v : RsVal} {cls1 cls2 : String} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap RsExt} {hp : RsHeap} :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokespecial "com/alexvanyo/composelife/resourcestate/ResourceState$Success"
          "<init>" "(Ljava/lang/Object;)V" :: rest)
        ⟨pc0, v.toJvmVal :: .allocRef cls1 :: .allocRef cls2 :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.res (.success v)) :: stk, locs, jh, hp⟩ := by
  apply runJvmResFast_of_step _ rfl (by simp) _ rfl
  have h1 :
      Jvm.stepInstr (mkRsHooks resolveProg (d + 1) subFuel)
        (.invokespecial "com/alexvanyo/composelife/resourcestate/ResourceState$Success"
          "<init>" "(Ljava/lang/Object;)V")
        ⟨pc, v.toJvmVal :: .allocRef cls1 :: .allocRef cls2 :: stk, locs, jh, hp⟩ =
      (match RsVal.ofJvmVal? v.toJvmVal with
       | some pv => .inl (some ⟨pc + 1, .ext (.res (.success pv)) :: stk, locs, jh, hp⟩)
       | none => .inr none) := rfl
  rw [h1, RsVal.ofJvmVal?_toJvmVal]

theorem runJvmResFast_failure_init {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    {t : ThrowableModel} {cls1 cls2 : String} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap RsExt} {hp : RsHeap} :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokespecial "com/alexvanyo/composelife/resourcestate/ResourceState$Failure"
          "<init>" "(Ljava/lang/Throwable;)V" :: rest)
        ⟨pc0, .ext (.throwable t) :: .allocRef cls1 :: .allocRef cls2 :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.res (.failure t)) :: stk, locs, jh, hp⟩ :=
  runJvmResFast_of_step _ rfl (by simp) rfl rfl

theorem runJvmResFast_fn1_invoke {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 cid : Nat} {prog rest : List JvmInstr}
    {arg out : JvmVal} {fn : JvmVal → Option JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap RsExt} {hp : RsHeap}
    (hcl : hp.closures[cid]? = some (.fn1 fn))
    (hout : fn arg = some out) :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokeinterface "kotlin/jvm/functions/Function1" "invoke"
          "(Ljava/lang/Object;)Ljava/lang/Object;" :: rest)
        ⟨pc0, arg :: .ext (.closureRef cid) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, out :: stk, locs, jh, hp⟩ := by
  apply runJvmResFast_of_step _ rfl (by simp) _ rfl
  have h1 :
      Jvm.stepInstr (mkRsHooks resolveProg (d + 1) subFuel)
        (.invokeinterface "kotlin/jvm/functions/Function1" "invoke"
          "(Ljava/lang/Object;)Ljava/lang/Object;")
        ⟨pc, arg :: .ext (.closureRef cid) :: stk, locs, jh, hp⟩ =
      (match invokeRsClosure ⟨pc, arg :: .ext (.closureRef cid) :: stk, locs, jh, hp⟩ cid [arg] with
       | some res => .inl (some ⟨pc + 1, res :: stk, locs, jh, hp⟩)
       | none => .inr none) := rfl
  rw [h1]
  simp [invokeRsClosure, hcl, hout]

theorem runJvmResFast_fn2_invoke {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 cid : Nat} {prog rest : List JvmInstr}
    {a0 a1 out : JvmVal} {fn : JvmVal → JvmVal → Option JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap RsExt} {hp : RsHeap}
    (hcl : hp.closures[cid]? = some (.fn2 fn))
    (hout : fn a0 a1 = some out) :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokeinterface "kotlin/jvm/functions/Function2" "invoke"
          "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" :: rest)
        ⟨pc0, a1 :: a0 :: .ext (.closureRef cid) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, out :: stk, locs, jh, hp⟩ := by
  apply runJvmResFast_of_step _ rfl (by simp) _ rfl
  have h1 :
      Jvm.stepInstr (mkRsHooks resolveProg (d + 1) subFuel)
        (.invokeinterface "kotlin/jvm/functions/Function2" "invoke"
          "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;")
        ⟨pc, a1 :: a0 :: .ext (.closureRef cid) :: stk, locs, jh, hp⟩ =
      (match invokeRsClosure ⟨pc, a1 :: a0 :: .ext (.closureRef cid) :: stk, locs, jh, hp⟩ cid [a0, a1] with
       | some res => .inl (some ⟨pc + 1, res :: stk, locs, jh, hp⟩)
       | none => .inr none) := rfl
  rw [h1]
  simp [invokeRsClosure, hcl, hout]

theorem runJvmResFast_fn3_invoke {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 cid : Nat} {prog rest : List JvmInstr}
    {a0 a1 a2 out : JvmVal} {fn : JvmVal → JvmVal → JvmVal → Option JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap RsExt} {hp : RsHeap}
    (hcl : hp.closures[cid]? = some (.fn3 fn))
    (hout : fn a0 a1 a2 = some out) :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokeinterface "kotlin/jvm/functions/Function3" "invoke"
          "(Ljava/lang/Object;Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" :: rest)
        ⟨pc0, a2 :: a1 :: a0 :: .ext (.closureRef cid) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, out :: stk, locs, jh, hp⟩ := by
  apply runJvmResFast_of_step _ rfl (by simp) _ rfl
  have h1 :
      Jvm.stepInstr (mkRsHooks resolveProg (d + 1) subFuel)
        (.invokeinterface "kotlin/jvm/functions/Function3" "invoke"
          "(Ljava/lang/Object;Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;")
        ⟨pc, a2 :: a1 :: a0 :: .ext (.closureRef cid) :: stk, locs, jh, hp⟩ =
      (match invokeRsClosure ⟨pc, a2 :: a1 :: a0 :: .ext (.closureRef cid) :: stk, locs, jh, hp⟩ cid
          [a0, a1, a2] with
       | some res => .inl (some ⟨pc + 1, res :: stk, locs, jh, hp⟩)
       | none => .inr none) := rfl
  rw [h1]
  simp [invokeRsClosure, hcl, hout]

/-! ### 1-3: `isLoading`, `isSuccess`, `isFailure` Equivalence Theorems -/

theorem isLoading_equiv (resolveProg : String → Option (List JvmInstr))
    (d subFuel fuel : Nat) (hd : 1 ≤ d) (hf : 30 ≤ fuel)
    (r : Model.ResourceState RsVal) (hp : RsHeap) (jh : Jvm.JvmHeap RsExt)
    (hclean : HasRsStaticsClean jh) :
    ∃ endSt,
      Jvm.runJvmRes (mkRsHooks resolveProg d subFuel) fuel ResourceStateKt_isLoading_prog
          (initRsJvmState [(0, .ext (.res r))] hp jh) =
        some (.i32 (if r.isLoading then 1 else 0), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  cases r with
  | loading =>
    apply exists_run_done _ rfl
    apply runJvmResFast_mono _ hf
    rs_step_blk
    rw [runJvmResFast_checkNotNullParam (by rfl)]
    rs_step_blk
    rw [runJvmResFast_getstatic_loading hclean]
    rw [runJvmResFast_areEqual]
    rs_branch
    rs_step_blk
    rw [runJvmResFast_ireturn_rs]
    all_goals try rfl
  | success v =>
    apply exists_run_done _ rfl
    apply runJvmResFast_mono _ hf
    rs_step_blk
    rw [runJvmResFast_checkNotNullParam (by rfl)]
    rs_step_blk
    rw [runJvmResFast_getstatic_loading hclean]
    rw [runJvmResFast_areEqual]
    rw [show Jvm.JvmVal.beqVal beqRsExt (.ext (.res (.success v))) (.ext (.res .loading)) = false by rfl]
    rs_branch
    rs_step_blk
    rw [runJvmResFast_instanceof_res true rfl]
    rs_branch
    rs_step_blk
    rw [runJvmResFast_ireturn_rs]
    all_goals try rfl
  | failure t =>
    apply exists_run_done _ rfl
    apply runJvmResFast_mono _ hf
    rs_step_blk
    rw [runJvmResFast_checkNotNullParam (by rfl)]
    rs_step_blk
    rw [runJvmResFast_getstatic_loading hclean]
    rw [runJvmResFast_areEqual]
    rw [show Jvm.JvmVal.beqVal beqRsExt (.ext (.res (.failure t))) (.ext (.res .loading)) = false by rfl]
    rs_branch
    rs_step_blk
    rw [runJvmResFast_instanceof_res false rfl]
    rs_branch
    rs_step_blk
    rw [runJvmResFast_instanceof_res true rfl]
    rs_branch
    rs_step_blk
    rw [runJvmResFast_ireturn_rs]
    all_goals try rfl

theorem isSuccess_equiv (resolveProg : String → Option (List JvmInstr))
    (d subFuel fuel : Nat) (hd : 1 ≤ d) (hf : 30 ≤ fuel)
    (r : Model.ResourceState RsVal) (hp : RsHeap) (jh : Jvm.JvmHeap RsExt)
    (hclean : HasRsStaticsClean jh) :
    ∃ endSt,
      Jvm.runJvmRes (mkRsHooks resolveProg d subFuel) fuel ResourceStateKt_isSuccess_prog
          (initRsJvmState [(0, .ext (.res r))] hp jh) =
        some (.i32 (if r.isSuccess then 1 else 0), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  cases r with
  | loading =>
    apply exists_run_done _ rfl
    apply runJvmResFast_mono _ hf
    rs_step_blk
    rw [runJvmResFast_checkNotNullParam (by rfl)]
    rs_step_blk
    rw [runJvmResFast_getstatic_loading hclean]
    rw [runJvmResFast_areEqual]
    rs_branch
    rs_step_blk
    rw [runJvmResFast_ireturn_rs]
    all_goals try rfl
  | success v =>
    apply exists_run_done _ rfl
    apply runJvmResFast_mono _ hf
    rs_step_blk
    rw [runJvmResFast_checkNotNullParam (by rfl)]
    rs_step_blk
    rw [runJvmResFast_getstatic_loading hclean]
    rw [runJvmResFast_areEqual]
    rw [show Jvm.JvmVal.beqVal beqRsExt (.ext (.res (.success v))) (.ext (.res .loading)) = false by rfl]
    rs_branch
    rs_step_blk
    rw [runJvmResFast_instanceof_res true rfl]
    rs_branch
    rs_step_blk
    rw [runJvmResFast_ireturn_rs]
    all_goals try rfl
  | failure t =>
    apply exists_run_done _ rfl
    apply runJvmResFast_mono _ hf
    rs_step_blk
    rw [runJvmResFast_checkNotNullParam (by rfl)]
    rs_step_blk
    rw [runJvmResFast_getstatic_loading hclean]
    rw [runJvmResFast_areEqual]
    rw [show Jvm.JvmVal.beqVal beqRsExt (.ext (.res (.failure t))) (.ext (.res .loading)) = false by rfl]
    rs_branch
    rs_step_blk
    rw [runJvmResFast_instanceof_res false rfl]
    rs_branch
    rs_step_blk
    rw [runJvmResFast_instanceof_res true rfl]
    rs_branch
    rs_step_blk
    rw [runJvmResFast_ireturn_rs]
    all_goals try rfl

theorem isFailure_equiv (resolveProg : String → Option (List JvmInstr))
    (d subFuel fuel : Nat) (hd : 1 ≤ d) (hf : 30 ≤ fuel)
    (r : Model.ResourceState RsVal) (hp : RsHeap) (jh : Jvm.JvmHeap RsExt)
    (hclean : HasRsStaticsClean jh) :
    ∃ endSt,
      Jvm.runJvmRes (mkRsHooks resolveProg d subFuel) fuel ResourceStateKt_isFailure_prog
          (initRsJvmState [(0, .ext (.res r))] hp jh) =
        some (.i32 (if r.isFailure then 1 else 0), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  cases r with
  | loading =>
    apply exists_run_done _ rfl
    apply runJvmResFast_mono _ hf
    rs_step_blk
    rw [runJvmResFast_checkNotNullParam (by rfl)]
    rs_step_blk
    rw [runJvmResFast_getstatic_loading hclean]
    rw [runJvmResFast_areEqual]
    rs_branch
    rs_step_blk
    rw [runJvmResFast_ireturn_rs]
    all_goals try rfl
  | success v =>
    apply exists_run_done _ rfl
    apply runJvmResFast_mono _ hf
    rs_step_blk
    rw [runJvmResFast_checkNotNullParam (by rfl)]
    rs_step_blk
    rw [runJvmResFast_getstatic_loading hclean]
    rw [runJvmResFast_areEqual]
    rw [show Jvm.JvmVal.beqVal beqRsExt (.ext (.res (.success v))) (.ext (.res .loading)) = false by rfl]
    rs_branch
    rs_step_blk
    rw [runJvmResFast_instanceof_res true rfl]
    rs_branch
    rs_step_blk
    rw [runJvmResFast_ireturn_rs]
    all_goals try rfl
  | failure t =>
    apply exists_run_done _ rfl
    apply runJvmResFast_mono _ hf
    rs_step_blk
    rw [runJvmResFast_checkNotNullParam (by rfl)]
    rs_step_blk
    rw [runJvmResFast_getstatic_loading hclean]
    rw [runJvmResFast_areEqual]
    rw [show Jvm.JvmVal.beqVal beqRsExt (.ext (.res (.failure t))) (.ext (.res .loading)) = false by rfl]
    rs_branch
    rs_step_blk
    rw [runJvmResFast_instanceof_res false rfl]
    rs_branch
    rs_step_blk
    rw [runJvmResFast_instanceof_res true rfl]
    rs_branch
    rs_step_blk
    rw [runJvmResFast_ireturn_rs]
    all_goals try rfl

/-! ### 4-5: `map` and `flatMap` Equivalence Theorems -/

theorem map_equiv (resolveProg : String → Option (List JvmInstr))
    (d subFuel fuel : Nat) (hd : 1 ≤ d) (hf : 45 ≤ fuel)
    (r : Model.ResourceState RsVal) (f : RsVal → RsVal) (cid : Nat)
    (hp : RsHeap) (jh : Jvm.JvmHeap RsExt)
    (hclean : HasRsStaticsClean jh)
    (hcl : hp.closures[cid]? = some (.fn1 (fun v => (RsVal.ofJvmVal? v).map (fun x => (f x).toJvmVal)))) :
    ∃ endSt,
      Jvm.runJvmRes (mkRsHooks resolveProg d subFuel) fuel ResourceStateKt_map_prog
          (initRsJvmState [(0, .ext (.res r)), (1, .ext (.closureRef cid))] hp jh) =
        some (.ext (.res (r.map f)), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  cases r with
  | loading =>
    apply exists_run_done _ rfl
    apply runJvmResFast_mono _ hf
    rs_step_blk
    rw [runJvmResFast_checkNotNullParam (by rfl)]
    rs_step_blk
    rw [runJvmResFast_checkNotNullParam (by rfl)]
    rs_step_blk
    rw [runJvmResFast_getstatic_loading hclean]
    rw [runJvmResFast_areEqual]
    rs_branch
    rs_step_blk
    rw [runJvmResFast_getstatic_loading hclean]
    rw [runJvmResFast_checkcast_res rfl]
    rs_step_blk
    rw [runJvmResFast_areturn_rs]
    all_goals try rfl
  | success v =>
    apply exists_run_done _ rfl
    apply runJvmResFast_mono _ hf
    rs_step_blk
    rw [runJvmResFast_checkNotNullParam (by rfl)]
    rs_step_blk
    rw [runJvmResFast_checkNotNullParam (by rfl)]
    rs_step_blk
    rw [runJvmResFast_getstatic_loading hclean]
    rw [runJvmResFast_areEqual]
    rw [show Jvm.JvmVal.beqVal beqRsExt (.ext (.res (.success v))) (.ext (.res .loading)) = false by rfl]
    rs_branch
    rs_step_blk
    rw [runJvmResFast_instanceof_res true rfl]
    rs_branch
    rs_step_blk
    rw [runJvmResFast_newClass_rs (by decide)]
    rs_step_blk
    rw [runJvmResFast_checkcast_res rfl]
    rw [runJvmResFast_success_getValue]
    rw [runJvmResFast_fn1_invoke hcl (out := (f v).toJvmVal) (by simp [RsVal.ofJvmVal?_toJvmVal])]
    rw [runJvmResFast_success_init]
    rw [runJvmResFast_checkcast_res rfl]
    rs_step_blk
    rw [runJvmResFast_areturn_rs]
    all_goals try rfl
  | failure t =>
    apply exists_run_done _ rfl
    apply runJvmResFast_mono _ hf
    rs_step_blk
    rw [runJvmResFast_checkNotNullParam (by rfl)]
    rs_step_blk
    rw [runJvmResFast_checkNotNullParam (by rfl)]
    rs_step_blk
    rw [runJvmResFast_getstatic_loading hclean]
    rw [runJvmResFast_areEqual]
    rw [show Jvm.JvmVal.beqVal beqRsExt (.ext (.res (.failure t))) (.ext (.res .loading)) = false by rfl]
    rs_branch
    rs_step_blk
    rw [runJvmResFast_instanceof_res false rfl]
    rs_branch
    rs_step_blk
    rw [runJvmResFast_instanceof_res true rfl]
    rs_branch
    rs_step_blk
    rw [runJvmResFast_newClass_rs (by decide)]
    rs_step_blk
    rw [runJvmResFast_checkcast_res rfl]
    rw [runJvmResFast_failure_getThrowable]
    rw [runJvmResFast_failure_init]
    rw [runJvmResFast_checkcast_res rfl]
    rs_step_blk
    rw [runJvmResFast_areturn_rs]
    all_goals try rfl

theorem flatMap_equiv (resolveProg : String → Option (List JvmInstr))
    (d subFuel fuel : Nat) (hd : 1 ≤ d) (hf : 45 ≤ fuel)
    (r : Model.ResourceState RsVal) (f : RsVal → Model.ResourceState RsVal) (cid : Nat)
    (hp : RsHeap) (jh : Jvm.JvmHeap RsExt)
    (hclean : HasRsStaticsClean jh)
    (hcl : hp.closures[cid]? = some (.fn1 (fun v => (RsVal.ofJvmVal? v).map (fun x => .ext (.res (f x)))))) :
    ∃ endSt,
      Jvm.runJvmRes (mkRsHooks resolveProg d subFuel) fuel ResourceStateKt_flatMap_prog
          (initRsJvmState [(0, .ext (.res r)), (1, .ext (.closureRef cid))] hp jh) =
        some (.ext (.res (r.flatMap f)), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  cases r with
  | loading =>
    apply exists_run_done _ rfl
    apply runJvmResFast_mono _ hf
    rs_step_blk
    rw [runJvmResFast_checkNotNullParam (by rfl)]
    rs_step_blk
    rw [runJvmResFast_checkNotNullParam (by rfl)]
    rs_step_blk
    rw [runJvmResFast_getstatic_loading hclean]
    rw [runJvmResFast_areEqual]
    rs_branch
    rs_step_blk
    rw [runJvmResFast_getstatic_loading hclean]
    rw [runJvmResFast_checkcast_res rfl]
    rs_step_blk
    rw [runJvmResFast_areturn_rs]
    all_goals try rfl
  | success v =>
    apply exists_run_done _ rfl
    apply runJvmResFast_mono _ hf
    rs_step_blk
    rw [runJvmResFast_checkNotNullParam (by rfl)]
    rs_step_blk
    rw [runJvmResFast_checkNotNullParam (by rfl)]
    rs_step_blk
    rw [runJvmResFast_getstatic_loading hclean]
    rw [runJvmResFast_areEqual]
    rw [show Jvm.JvmVal.beqVal beqRsExt (.ext (.res (.success v))) (.ext (.res .loading)) = false by rfl]
    rs_branch
    rs_step_blk
    rw [runJvmResFast_instanceof_res true rfl]
    rs_branch
    rs_step_blk
    rw [runJvmResFast_checkcast_res rfl]
    rw [runJvmResFast_success_getValue]
    rw [runJvmResFast_fn1_invoke hcl (out := .ext (.res (f v))) (by simp [RsVal.ofJvmVal?_toJvmVal])]
    rw [runJvmResFast_checkcast_res rfl]
    rs_step_blk
    rw [runJvmResFast_areturn_rs]
    all_goals try rfl
  | failure t =>
    apply exists_run_done _ rfl
    apply runJvmResFast_mono _ hf
    rs_step_blk
    rw [runJvmResFast_checkNotNullParam (by rfl)]
    rs_step_blk
    rw [runJvmResFast_checkNotNullParam (by rfl)]
    rs_step_blk
    rw [runJvmResFast_getstatic_loading hclean]
    rw [runJvmResFast_areEqual]
    rw [show Jvm.JvmVal.beqVal beqRsExt (.ext (.res (.failure t))) (.ext (.res .loading)) = false by rfl]
    rs_branch
    rs_step_blk
    rw [runJvmResFast_instanceof_res false rfl]
    rs_branch
    rs_step_blk
    rw [runJvmResFast_instanceof_res true rfl]
    rs_branch
    rs_step_blk
    rw [runJvmResFast_newClass_rs (by decide)]
    rs_step_blk
    rw [runJvmResFast_checkcast_res rfl]
    rw [runJvmResFast_failure_getThrowable]
    rw [runJvmResFast_failure_init]
    rw [runJvmResFast_checkcast_res rfl]
    rs_step_blk
    rw [runJvmResFast_areturn_rs]
    all_goals try rfl

/-! ### 6-9: Flow & Compose Helper Equivalence Theorems (`successes`, `firstSuccess`, `asResourceState`, `collectAsState`) -/

theorem runJvmResFast_successes_init {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    {tr : Model.FlowTrace (Model.ResourceState RsVal)} {cls1 cls2 : String}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap RsExt} {hp : RsHeap} :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokespecial "com/alexvanyo/composelife/resourcestate/ResourceStateKt$successes$$inlined$transform$1"
          "<init>" "(Lkotlinx/coroutines/flow/Flow;Lkotlin/coroutines/Continuation;)V" :: rest)
        ⟨pc0, .null :: .ext (.resFlow tr) :: .allocRef cls1 :: .allocRef cls2 :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.transformStub "successes" (some tr)) :: stk, locs, jh, hp⟩ :=
  runJvmResFast_of_step _ rfl (by simp) rfl rfl

theorem runJvmResFast_flowkt_flow {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    {tr : Model.FlowTrace (Model.ResourceState RsVal)}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap RsExt} {hp : RsHeap} :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokestatic "kotlinx/coroutines/flow/FlowKt" "flow"
          "(Lkotlin/jvm/functions/Function2;)Lkotlinx/coroutines/flow/Flow;" :: rest)
        ⟨pc0, .ext (.transformStub "successes" (some tr)) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.resFlow (Model.successesFlow tr)) :: stk, locs, jh, hp⟩ :=
  runJvmResFast_of_step _ rfl (by simp) rfl rfl

theorem runJvmResFast_flowkt_first {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    {tr : Model.FlowTrace (Model.ResourceState RsVal)} {headRes : Model.ResourceState RsVal}
    (hhead : tr.emissions.head? = some headRes)
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap RsExt} {hp : RsHeap} :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokestatic "kotlinx/coroutines/flow/FlowKt" "first"
          "(Lkotlinx/coroutines/flow/Flow;Lkotlin/coroutines/Continuation;)Ljava/lang/Object;" :: rest)
        ⟨pc0, .ext .continuation :: .ext (.resFlow tr) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.res headRes) :: stk, locs, jh, hp⟩ := by
  apply runJvmResFast_of_step _ rfl (by simp) _ rfl
  have h1 :
      Jvm.stepInstr (mkRsHooks resolveProg (d + 1) subFuel)
        (.invokestatic "kotlinx/coroutines/flow/FlowKt" "first"
          "(Lkotlinx/coroutines/flow/Flow;Lkotlin/coroutines/Continuation;)Ljava/lang/Object;")
        ⟨pc, .ext .continuation :: .ext (.resFlow tr) :: stk, locs, jh, hp⟩ =
      (match tr.emissions.head? with
       | some headRes => .inl (some ⟨pc + 1, .ext (.res headRes) :: stk, locs, jh, hp⟩)
       | none => .inr none) := rfl
  rw [h1, hhead]

theorem runJvmResFast_asResourceState_map_init {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    {tr : Model.FlowTrace RsVal} {cls1 cls2 : String}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap RsExt} {hp : RsHeap} :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokespecial "com/alexvanyo/composelife/resourcestate/ResourceStateKt$asResourceState$$inlined$map$1"
          "<init>" "(Lkotlinx/coroutines/flow/Flow;)V" :: rest)
        ⟨pc0, .ext (.flow tr) :: .allocRef cls1 :: .allocRef cls2 :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.resFlow { emissions := tr.emissions.map Model.ResourceState.success,
                                   terminalFailure? := tr.terminalFailure? }) :: stk,
         locs, jh, hp⟩ :=
  runJvmResFast_of_step _ rfl (by simp) rfl rfl

theorem runJvmResFast_asResourceState_catch_init {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {cls1 cls2 : String}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap RsExt} {hp : RsHeap} :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokespecial "com/alexvanyo/composelife/resourcestate/ResourceStateKt$asResourceState$2"
          "<init>" "(Lkotlin/coroutines/Continuation;)V" :: rest)
        ⟨pc0, .null :: .allocRef cls1 :: .allocRef cls2 :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.transformStub "asResourceState$catch" none) :: stk, locs, jh, hp⟩ :=
  runJvmResFast_of_step _ rfl (by simp) rfl rfl

theorem runJvmResFast_flowkt_catch {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    {tr : Model.FlowTrace RsVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap RsExt} {hp : RsHeap} :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokestatic "kotlinx/coroutines/flow/FlowKt" "catch"
          "(Lkotlinx/coroutines/flow/Flow;Lkotlin/jvm/functions/Function3;)Lkotlinx/coroutines/flow/Flow;" :: rest)
        ⟨pc0, .ext (.transformStub "asResourceState$catch" none) ::
          .ext (.resFlow { emissions := tr.emissions.map Model.ResourceState.success,
                           terminalFailure? := tr.terminalFailure? }) :: stk,
         locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.resFlow (Model.asResourceStateFlow tr)) :: stk, locs, jh, hp⟩ := by
  apply runJvmResFast_of_step _ rfl (by simp) _ rfl
  have h1 :
      Jvm.stepInstr (mkRsHooks resolveProg (d + 1) subFuel)
        (.invokestatic "kotlinx/coroutines/flow/FlowKt" "catch"
          "(Lkotlinx/coroutines/flow/Flow;Lkotlin/jvm/functions/Function3;)Lkotlinx/coroutines/flow/Flow;")
        ⟨pc, .ext (.transformStub "asResourceState$catch" none) ::
          .ext (.resFlow { emissions := tr.emissions.map Model.ResourceState.success,
                           terminalFailure? := tr.terminalFailure? }) :: stk,
         locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .ext (.resFlow (Model.asResourceStateFlow tr)) :: stk, locs, jh, hp⟩) := by
    cases htf : tr.terminalFailure? <;> simp [Model.asResourceStateFlow, htf] <;> rfl
  exact h1

theorem runJvmResFast_composer_markerStart {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    {key info : JvmVal} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap RsExt} {hp : RsHeap} :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokestatic "androidx/compose/runtime/ComposerKt" "sourceInformationMarkerStart"
          "(Landroidx/compose/runtime/Composer;ILjava/lang/String;)V" :: rest)
        ⟨pc0, info :: key :: .ext .composer :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, stk, locs, jh, hp⟩ :=
  runJvmResFast_of_step _ rfl (by simp) rfl rfl

theorem runJvmResFast_composer_markerEnd {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap RsExt} {hp : RsHeap} :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokestatic "androidx/compose/runtime/ComposerKt" "sourceInformationMarkerEnd"
          "(Landroidx/compose/runtime/Composer;)V" :: rest)
        ⟨pc0, .ext .composer :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, stk, locs, jh, hp⟩ :=
  runJvmResFast_of_step _ rfl (by simp) rfl rfl

theorem runJvmResFast_composer_isTrace {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap RsExt} {hp : RsHeap} :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokestatic "androidx/compose/runtime/ComposerKt" "isTraceInProgress" "()Z" :: rest)
        ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .i32 (if hp.traceEnabled then 1 else 0) :: stk, locs, jh, hp⟩ :=
  runJvmResFast_of_step _ rfl (by simp) rfl rfl

theorem runJvmResFast_composer_traceStart {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    {a0 a1 a2 a3 : JvmVal} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap RsExt} {hp : RsHeap} :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokestatic "androidx/compose/runtime/ComposerKt" "traceEventStart"
          "(IIILjava/lang/String;)V" :: rest)
        ⟨pc0, a3 :: a2 :: a1 :: a0 :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, stk, locs, jh, hp⟩ :=
  runJvmResFast_of_step _ rfl (by simp) rfl rfl

theorem runJvmResFast_composer_traceEnd {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap RsExt} {hp : RsHeap} :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokestatic "androidx/compose/runtime/ComposerKt" "traceEventEnd" "()V" :: rest)
        ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, stk, locs, jh, hp⟩ :=
  runJvmResFast_of_step _ rfl (by simp) rfl rfl

theorem runJvmResFast_collectAsState_call {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    {tr : Model.FlowTrace (Model.ResourceState RsVal)} {initVal : Model.ResourceState RsVal}
    {a0 a1 a2 a3 : JvmVal} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap RsExt} {hp : RsHeap} :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokestatic "androidx/compose/runtime/SnapshotStateKt" "collectAsState"
          "(Lkotlinx/coroutines/flow/Flow;Ljava/lang/Object;Lkotlin/coroutines/CoroutineContext;Landroidx/compose/runtime/SnapshotMutationPolicy;Landroidx/compose/runtime/Composer;II)Landroidx/compose/runtime/State;" ::
          rest)
        ⟨pc0, a3 :: a2 :: .ext .composer :: a1 :: a0 :: .ext (.res initVal) :: .ext (.resFlow tr) :: stk,
         locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.composeState (tr.emissions.getLast?.getD initVal)) :: stk, locs, jh, hp⟩ :=
  runJvmResFast_of_step _ rfl (by simp) rfl rfl

theorem successes_equiv (resolveProg : String → Option (List JvmInstr))
    (d subFuel fuel : Nat) (hd : 1 ≤ d) (hf : 20 ≤ fuel)
    (tr : Model.FlowTrace (Model.ResourceState RsVal))
    (hp : RsHeap) (jh : Jvm.JvmHeap RsExt) :
    ∃ endSt,
      Jvm.runJvmRes (mkRsHooks resolveProg d subFuel) fuel ResourceStateKt_successes_prog
          (initRsJvmState [(0, .ext (.resFlow tr))] hp jh) =
        some (.ext (.resFlow (Model.successesFlow tr)), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  apply exists_run_done _ rfl
  apply runJvmResFast_mono _ hf
  rs_step_blk
  rw [runJvmResFast_checkNotNullParam (by rfl)]
  rs_step_blk
  rw [runJvmResFast_newClass_rs (by decide)]
  rs_step_blk
  rw [runJvmResFast_successes_init]
  rs_step_blk
  rw [runJvmResFast_checkcast_res rfl]
  rw [runJvmResFast_flowkt_flow]
  rs_step_blk
  rw [runJvmResFast_areturn_rs]

theorem firstSuccess_equiv (resolveProg : String → Option (List JvmInstr))
    (hext : ExtendsRsProgs resolveProg)
    (d subFuel fuel : Nat) (hd : 2 ≤ d) (hsub : 20 ≤ subFuel) (hf : 10 ≤ fuel)
    (tr : Model.FlowTrace (Model.ResourceState RsVal))
    (headRes : Model.ResourceState RsVal)
    (hhead : Model.firstSuccessModel tr = some headRes)
    (hp : RsHeap) (jh : Jvm.JvmHeap RsExt) :
    ∃ endSt,
      Jvm.runJvmRes (mkRsHooks resolveProg d subFuel) fuel ResourceStateKt_firstSuccess_prog
          (initRsJvmState [(0, .ext (.resFlow tr)), (1, .ext .continuation)] hp jh) =
        some (.ext (.res headRes), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 2 := ⟨d - 2, by omega⟩
  obtain ⟨subSt, hSucc, hjhSub, hhpSub⟩ :=
    successes_equiv resolveProg (d' + 1) subFuel subFuel (by omega) hsub tr hp jh
  have hLookup : resolveProg "ResourceStateKt.successes" = some ResourceStateKt_successes_prog :=
    hext "ResourceStateKt.successes" ResourceStateKt_successes_prog rfl
  have hFirst : (Model.successesFlow tr).emissions.head? = some headRes := hhead
  apply exists_run_done _ rfl
  apply runJvmResFast_mono _ hf
  rs_step_blk
  have hSubStep (locs : Nat → JvmVal) :
      Jvm.stepInstr (mkRsHooks resolveProg (d' + 2) subFuel)
        (.invokestatic "com/alexvanyo/composelife/resourcestate/ResourceStateKt" "successes" "(Lkotlinx/coroutines/flow/Flow;)Lkotlinx/coroutines/flow/Flow;")
        ⟨1, [.ext (.resFlow tr)], locs, jh, hp⟩ =
      .inl (some ⟨2, [.ext (.resFlow (Model.successesFlow tr))], locs, jh, hp⟩) := by
    have hTags : Jvm.parseMethodParamTags "(Lkotlinx/coroutines/flow/Flow;)Lkotlinx/coroutines/flow/Flow;" = ['L'] := rfl
    have hBase :
        Jvm.stepInstr (mkRsHooks resolveProg (d' + 2) subFuel)
          (.invokestatic "com/alexvanyo/composelife/resourcestate/ResourceStateKt" "successes" "(Lkotlinx/coroutines/flow/Flow;)Lkotlinx/coroutines/flow/Flow;")
          ⟨1, [.ext (.resFlow tr)], locs, jh, hp⟩ =
        (match
          (match resolveProg "ResourceStateKt.successes" with
          | some prog =>
            match Jvm.runJvmRes (mkRsHooks resolveProg (d' + 1) subFuel) subFuel prog
                (initRsJvmState [(0, .ext (.resFlow tr))] hp jh) with
            | some (res, endSt) =>
              some (res, (⟨1, [.ext (.resFlow tr)], locs, endSt.jvmHeap, endSt.heap⟩ : JvmState))
            | none => none
          | none => none) with
        | some (res, st') => .inl (some ⟨2, [res], st'.locals, st'.jvmHeap, st'.heap⟩)
        | none => .inr none) := by
      dsimp only [Jvm.stepInstr, Jvm.stepInvokeStaticGeneric, mkRsHooks, normalizeRsClass]
      rw [hTags]
      rfl
    rw [hBase, hLookup]
    dsimp only
    rw [hSucc]
    dsimp only
    rw [hjhSub, hhpSub]
  rw [runJvmResFast_of_step _ rfl (by simp) (hSubStep _) rfl]
  rs_step_blk
  rw [runJvmResFast_flowkt_first hFirst]
  rs_step_blk
  rw [runJvmResFast_areturn_rs]
  all_goals try rfl

theorem asResourceState_equiv (resolveProg : String → Option (List JvmInstr))
    (d subFuel fuel : Nat) (hd : 1 ≤ d) (hf : 30 ≤ fuel)
    (tr : Model.FlowTrace RsVal) (hp : RsHeap) (jh : Jvm.JvmHeap RsExt) :
    ∃ endSt,
      Jvm.runJvmRes (mkRsHooks resolveProg d subFuel) fuel ResourceStateKt_asResourceState_prog
          (initRsJvmState [(0, .ext (.flow tr))] hp jh) =
        some (.ext (.resFlow (Model.asResourceStateFlow tr)), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  apply exists_run_done _ rfl
  apply runJvmResFast_mono _ hf
  rs_step_blk
  rw [runJvmResFast_checkNotNullParam (by rfl)]
  rs_step_blk
  rw [runJvmResFast_newClass_rs (by decide)]
  rs_step_blk
  rw [runJvmResFast_asResourceState_map_init]
  rs_step_blk
  rw [runJvmResFast_checkcast_res rfl]
  rs_step_blk
  rw [runJvmResFast_newClass_rs (by decide)]
  rs_step_blk
  rw [runJvmResFast_asResourceState_catch_init]
  rs_step_blk
  rw [runJvmResFast_checkcast_res rfl]
  rw [runJvmResFast_flowkt_catch]
  rs_step_blk
  rw [runJvmResFast_areturn_rs]

theorem collectAsState_equiv (resolveProg : String → Option (List JvmInstr))
    (d subFuel fuel : Nat) (hd : 1 ≤ d) (hf : 40 ≤ fuel)
    (tr : Model.FlowTrace (Model.ResourceState RsVal))
    (changed : UInt32) (hp : RsHeap) (jh : Jvm.JvmHeap RsExt)
    (hclean : HasRsStaticsClean jh) :
    ∃ endSt,
      Jvm.runJvmRes (mkRsHooks resolveProg d subFuel) fuel ResourceStateKt_collectAsState_prog
          (initRsJvmState [(0, .ext (.resFlow tr)), (1, .ext .composer), (2, .i32 changed)] hp jh) =
        some (.ext (.composeState (Model.collectAsStateModel tr)), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  cases htr : hp.traceEnabled with
  | false =>
    apply exists_run_done _ rfl
    apply runJvmResFast_mono _ hf
    rs_step_blk
    rw [runJvmResFast_checkNotNullParam (by rfl)]
    rs_step_blk
    rw [runJvmResFast_composer_markerStart]
    rs_step_blk
    rw [runJvmResFast_composer_isTrace, htr]
    rs_branch
    rs_step_blk
    rw [runJvmResFast_getstatic_loading hclean]
    rs_step_blk
    rw [runJvmResFast_collectAsState_call]
    rs_step_blk
    rw [runJvmResFast_composer_isTrace, htr]
    rs_branch
    rs_step_blk
    rw [runJvmResFast_composer_markerEnd]
    rs_step_blk
    rw [runJvmResFast_areturn_rs]
    all_goals try rfl
  | true =>
    apply exists_run_done _ rfl
    apply runJvmResFast_mono _ hf
    rs_step_blk
    rw [runJvmResFast_checkNotNullParam (by rfl)]
    rs_step_blk
    rw [runJvmResFast_composer_markerStart]
    rs_step_blk
    rw [runJvmResFast_composer_isTrace, htr]
    rs_branch
    rs_step_blk
    rw [runJvmResFast_composer_traceStart]
    rs_step_blk
    rw [runJvmResFast_getstatic_loading hclean]
    rs_step_blk
    rw [runJvmResFast_collectAsState_call]
    rs_step_blk
    rw [runJvmResFast_composer_isTrace, htr]
    rs_branch
    rs_step_blk
    rw [runJvmResFast_composer_traceEnd]
    rs_step_blk
    rw [runJvmResFast_composer_markerEnd]
    rs_step_blk
    rw [runJvmResFast_areturn_rs]
    all_goals try rfl

/-! ### 10-12: `combine` (2-arg, 3-arg, vararg) Equivalence Theorems -/

@[simp] theorem RsVal.toJvmVal_isRef (v : RsVal) : v.toJvmVal.isRef = true := by
  cases v <;> rfl

@[simp] theorem RsVal.toJvmVal_isNull (v : RsVal) : v.toJvmVal.isNull = false := by
  cases v <;> rfl

@[simp] theorem RsVal.toJvmVal_isCat2 (v : RsVal) : v.toJvmVal.isCat2 = false := by
  cases v <;> rfl

theorem list_take_succ {α : Type} (xs : List α) (i : Nat) (h : i < xs.length) :
    xs.take (i + 1) = xs.take i ++ [xs[i]] := by
  induction xs generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    cases i with
    | zero => simp
    | succ i =>
      simp only [List.take_succ_cons, List.cons_append, List.getElem_cons_succ]
      congr 1
      exact ih i (by simpa using h)

theorem list_take_all {α : Type} (xs : List α) : xs.take xs.length = xs :=
  List.take_length

def resFailureThrowable : Model.ResourceState RsVal → Model.ThrowableModel
  | .failure t => t
  | _ => .named ""

def resSuccessVal : Model.ResourceState RsVal → RsVal
  | .success v => v
  | _ => .unit

theorem filter_isFailure_map (states : List (Model.ResourceState RsVal)) :
    (states.filter Model.ResourceState.isFailure).map resFailureThrowable = Model.extractFailures states := by
  induction states with
  | nil => rfl
  | cons r rs ih =>
    cases r with
    | loading => simp [Model.ResourceState.isFailure, Model.extractFailures, ih]
    | success _ => simp [Model.ResourceState.isFailure, Model.extractFailures, ih]
    | failure t => simp [Model.ResourceState.isFailure, Model.extractFailures, List.filter_cons, resFailureThrowable, ih]

theorem filter_isLoading_isEmpty (states : List (Model.ResourceState RsVal)) :
    (states.filter Model.ResourceState.isLoading).isEmpty = !Model.hasLoading states := by
  induction states with
  | nil => rfl
  | cons r rs ih =>
    cases r <;> simp [Model.ResourceState.isLoading, Model.hasLoading, List.filter_cons, ih]

theorem filter_isSuccess_map (states : List (Model.ResourceState RsVal)) :
    (states.filter Model.ResourceState.isSuccess).map resSuccessVal = Model.extractSuccesses states := by
  induction states with
  | nil => rfl
  | cons r rs ih =>
    cases r with
    | loading => simp [Model.ResourceState.isSuccess, Model.extractSuccesses, ih]
    | failure _ => simp [Model.ResourceState.isSuccess, Model.extractSuccesses, ih]
    | success v => simp [Model.ResourceState.isSuccess, Model.extractSuccesses, List.filter_cons, resSuccessVal, ih]

theorem filter_isSuccess_length_eq (states : List (Model.ResourceState RsVal))
    (hfail : Model.extractFailures states = []) (hload : Model.hasLoading states = false) :
    (states.filter Model.ResourceState.isSuccess).length = states.length := by
  induction states with
  | nil => rfl
  | cons r rs ih =>
    cases r with
    | loading => simp [Model.hasLoading] at hload
    | failure _ => simp [Model.extractFailures] at hfail
    | success _ =>
      simp only [Model.extractFailures] at hfail
      simp only [Model.hasLoading] at hload
      simp [Model.ResourceState.isSuccess, List.filter_cons, ih hfail hload]

theorem combine2_all_success (r1 r2 : Model.ResourceState RsVal)
    (hfail : Model.extractFailures [r1, r2] = []) (hload : Model.hasLoading [r1, r2] = false) :
    ∃ a b, r1 = .success a ∧ r2 = .success b := by
  cases r1 <;> cases r2 <;>
    simp [Model.extractFailures, Model.hasLoading] at hfail hload ⊢

theorem combine3_all_success (r1 r2 r3 : Model.ResourceState RsVal)
    (hfail : Model.extractFailures [r1, r2, r3] = []) (hload : Model.hasLoading [r1, r2, r3] = false) :
    ∃ a b c, r1 = .success a ∧ r2 = .success b ∧ r3 = .success c := by
  cases r1 <;> cases r2 <;> cases r3 <;>
    simp [Model.extractFailures, Model.hasLoading] at hfail hload ⊢

def ListBackedBy (jh : Jvm.JvmHeap RsExt) (listAddr arrAddr : Nat)
    (elems : Array JvmVal) : Prop :=
  arrAddr ≠ listAddr ∧
  arrAddr < jh.objects.size ∧
  listAddr < jh.objects.size ∧
  jh.get? listAddr = some (.instance "java/util/ArrayList" [("arr", .heapRef arrAddr)]) ∧
  jh.get? arrAddr = some (.objArray "java/lang/Object" elems)

theorem ListBackedBy.extract {jh : Jvm.JvmHeap RsExt} {listAddr arrAddr : Nat}
    {elems : Array JvmVal} (h : ListBackedBy jh listAddr arrAddr elems) :
    Jvm.extractListArray? jh listAddr = some elems := by
  rcases h with ⟨_, _, _, hl, ha⟩
  simp [Jvm.extractListArray?, hl, ha]

theorem ListBackedBy.preserve {jh1 jh2 : Jvm.JvmHeap RsExt} {listAddr arrAddr : Nat}
    {elems : Array JvmVal} (h : ListBackedBy jh1 listAddr arrAddr elems)
    (hl : jh2.get? listAddr = jh1.get? listAddr)
    (ha : jh2.get? arrAddr = jh1.get? arrAddr)
    (hsz : jh1.objects.size ≤ jh2.objects.size) :
    ListBackedBy jh2 listAddr arrAddr elems := by
  rcases h with ⟨hne, haLt, hlLt, hgl, hga⟩
  exact ⟨hne, by omega, by omega, hl.trans hgl, ha.trans hga⟩

def IterBackedBy (jh : Jvm.JvmHeap RsExt) (itAddr arrAddr : Nat)
    (idx : UInt32) (elems : Array JvmVal) : Prop :=
  itAddr ≠ arrAddr ∧
  itAddr < jh.objects.size ∧
  arrAddr < jh.objects.size ∧
  jh.get? itAddr = some (.instance "java/util/Iterator" [("arr", .heapRef arrAddr), ("idx", .i32 idx)]) ∧
  jh.get? arrAddr = some (.objArray "java/lang/Object" elems)

theorem IterBackedBy.preserve {jh1 jh2 : Jvm.JvmHeap RsExt} {itAddr arrAddr : Nat}
    {idx : UInt32} {elems : Array JvmVal} (h : IterBackedBy jh1 itAddr arrAddr idx elems)
    (hi : jh2.get? itAddr = jh1.get? itAddr)
    (ha : jh2.get? arrAddr = jh1.get? arrAddr)
    (hsz : jh1.objects.size ≤ jh2.objects.size) :
    IterBackedBy jh2 itAddr arrAddr idx elems := by
  rcases h with ⟨hne, hiLt, haLt, hgi, hga⟩
  exact ⟨hne, by omega, by omega, hi.trans hgi, ha.trans hga⟩

theorem runJvmResFast_anewarray {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {cls : String}
    {n : UInt32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap RsExt} {hp : RsHeap}
    (hn : n.toBitVec.slt 0#32 = false) :
    let allocRes := jh.alloc (.objArray cls (Array.replicate n.toNat .null))
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.anewarray cls :: rest)
        ⟨pc0, .i32 n :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .heapRef allocRes.1 :: stk, locs, allocRes.2, hp⟩ := by
  apply runJvmResFast_of_step _ rfl (by simp) _ rfl
  have hBase :
      Jvm.stepInstr (mkRsHooks resolveProg (d + 1) subFuel) (.anewarray cls)
        ⟨pc, .i32 n :: stk, locs, jh, hp⟩ =
      (if n.toBitVec.slt 0#32 then .inr none
       else
         let allocRes := jh.alloc (.objArray cls (Array.replicate n.toNat .null))
         .inl (some ⟨pc + 1, .heapRef allocRes.1 :: stk, locs, allocRes.2, hp⟩)) := rfl
  rw [hBase]
  simp [hn]

theorem runJvmResFast_aastore_res {hooks : Jvm.JvmHooks RsExt RsHeap}
    {f pc pc0 addr : Nat} {prog rest : List JvmInstr}
    {idx : UInt32} {r : Model.ResourceState RsVal} {elems : Array JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap RsExt} {hp : RsHeap}
    (hs : idx.toBitVec.slt 0#32 = false)
    (hget : jh.get? addr = some (.objArray "com/alexvanyo/composelife/resourcestate/ResourceState" elems))
    (hcompat : Jvm.isArrayElemCompat hooks jh
      "com/alexvanyo/composelife/resourcestate/ResourceState" (.ext (.res r)) = true)
    (hlt : idx.toNat < elems.size) :
    let jh' := jh.set addr (.objArray "com/alexvanyo/composelife/resourcestate/ResourceState"
      (elems.set idx.toNat (.ext (.res r)) hlt))
    Jvm.runJvmResFast hooks (f + 1) prog pc
        (.aastore :: rest)
        ⟨pc0, .ext (.res r) :: .i32 idx :: .heapRef addr :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest
        ⟨pc + 1, stk, locs, jh', hp⟩ :=
  runJvmResFast_of_step _ rfl (by simp) (Jvm.stepInstr_aastore hooks hcompat hget hs hlt) rfl

theorem runJvmResFast_aaload {hooks : Jvm.JvmHooks RsExt RsHeap}
    {f pc pc0 addr : Nat} {prog rest : List JvmInstr} {cls : String}
    {idx : UInt32} {elems : Array JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap RsExt} {hp : RsHeap}
    (hs : idx.toBitVec.slt 0#32 = false)
    (hget : jh.get? addr = some (.objArray cls elems))
    (hlt : idx.toNat < elems.size) :
    Jvm.runJvmResFast hooks (f + 1) prog pc
        (.aaload :: rest)
        ⟨pc0, .i32 idx :: .heapRef addr :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest
        ⟨pc + 1, elems[idx.toNat] :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_aaload (hooks := hooks) hget hs hlt

theorem runJvmResFast_arraylength {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 addr : Nat} {prog rest : List JvmInstr} {cls : String}
    {elems : Array JvmVal} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap RsExt} {hp : RsHeap}
    (hget : jh.get? addr = some (.objArray cls elems)) :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.arraylength :: rest)
        ⟨pc0, .heapRef addr :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .i32 (UInt32.ofNat elems.size) :: stk, locs, jh, hp⟩ := by
  apply runJvmResFast_of_step _ rfl (by simp) _ rfl
  dsimp only [Jvm.stepInstr]
  rw [hget]
  rfl

theorem runJvmResFast_arraylist_init_void {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap RsExt} {hp : RsHeap} :
    let arrAlloc := jh.alloc (.objArray "java/lang/Object" #[])
    let listAlloc := arrAlloc.2.alloc (.instance "java/util/ArrayList" [("arr", .heapRef arrAlloc.1)])
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokespecial "java/util/ArrayList" "<init>" "()V" :: rest)
        ⟨pc0, .allocRef "java/util/ArrayList" :: .allocRef "java/util/ArrayList" :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .heapRef listAlloc.1 :: stk, locs, listAlloc.2, hp⟩ :=
  runJvmResFast_of_step _ rfl (by simp) rfl rfl

theorem runJvmResFast_arraylist_init_cap {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {cap : UInt32}
    {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap RsExt} {hp : RsHeap}
    (hcap : cap.toBitVec.slt 0#32 = false) :
    let arrAlloc := jh.alloc (.objArray "java/lang/Object" #[])
    let listAlloc := arrAlloc.2.alloc (.instance "java/util/ArrayList" [("arr", .heapRef arrAlloc.1)])
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokespecial "java/util/ArrayList" "<init>" "(I)V" :: rest)
        ⟨pc0, .i32 cap :: .allocRef "java/util/ArrayList" :: .allocRef "java/util/ArrayList" :: stk,
          locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .heapRef listAlloc.1 :: stk, locs, listAlloc.2, hp⟩ := by
  apply runJvmResFast_of_step _ rfl (by simp) _ rfl
  have hBase :
      Jvm.stepInstr (mkRsHooks resolveProg (d + 1) subFuel)
        (.invokespecial "java/util/ArrayList" "<init>" "(I)V")
        ⟨pc, .i32 cap :: .allocRef "java/util/ArrayList" :: .allocRef "java/util/ArrayList" :: stk,
          locs, jh, hp⟩ =
      (if cap.toBitVec.slt 0#32 then .inr none
       else
         let arrAlloc := jh.alloc (.objArray "java/lang/Object" #[])
         let listAlloc := arrAlloc.2.alloc (.instance "java/util/ArrayList" [("arr", .heapRef arrAlloc.1)])
         .inl (some ⟨pc + 1, .heapRef listAlloc.1 :: stk, locs, listAlloc.2, hp⟩)) := rfl
  rw [hBase]
  simp [hcap]

theorem arraylist_init_backed {jh : Jvm.JvmHeap RsExt} :
    let arrAlloc := jh.alloc (.objArray "java/lang/Object" #[])
    let listAlloc := arrAlloc.2.alloc (.instance "java/util/ArrayList" [("arr", .heapRef arrAlloc.1)])
    ListBackedBy listAlloc.2 listAlloc.1 arrAlloc.1 #[] ∧
    arrAlloc.1 = jh.objects.size ∧
    listAlloc.1 = jh.objects.size + 1 ∧
    listAlloc.2.objects.size = jh.objects.size + 2 ∧
    listAlloc.2.statics = jh.statics ∧
    (∀ a, a < jh.objects.size → listAlloc.2.get? a = jh.get? a) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, rfl, ?_, ?_, rfl, ?_⟩
  · simp [Jvm.JvmHeap.alloc]
  · simp [Jvm.JvmHeap.alloc]; omega
  · simp [Jvm.JvmHeap.alloc]
  · exact Jvm.jvmHeap_get?_alloc_self _ _
  · rw [Jvm.jvmHeap_get?_alloc_old _ _ (by simp [Jvm.JvmHeap.alloc])]
    exact Jvm.jvmHeap_get?_alloc_self _ _
  · simp [Jvm.JvmHeap.alloc]
  · simp [Jvm.JvmHeap.alloc]
  · intro a ha
    have h1 : a < (jh.alloc (.objArray "java/lang/Object" #[])).2.objects.size := by
      simp [Jvm.JvmHeap.alloc]; omega
    rw [Jvm.jvmHeap_get?_alloc_old _ _ h1]
    exact Jvm.jvmHeap_get?_alloc_old _ _ ha

theorem runJvmResFast_checkcast_arrayList {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 listAddr arrAddr : Nat} {prog rest : List JvmInstr}
    {tgtCls : String} {elems : Array JvmVal} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap RsExt} {hp : RsHeap}
    (hb : ListBackedBy jh listAddr arrAddr elems)
    (hsub : tgtCls = "java/util/Collection" ∨ tgtCls = "java/util/List" ∨ tgtCls = "java/lang/Iterable") :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.checkcast tgtCls :: rest)
        ⟨pc0, .heapRef listAddr :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .heapRef listAddr :: stk, locs, jh, hp⟩ := by
  apply runJvmResFast_of_step _ rfl (by simp) _ rfl
  have hgl := hb.2.2.2.1
  have hci : jh.checkInstanceOf tgtCls listAddr (mkRsHooks resolveProg (d + 1) subFuel).isSubtypeOf = true := by
    rcases hsub with rfl | rfl | rfl <;>
      simp [Jvm.JvmHeap.checkInstanceOf, hgl, Jvm.HeapObj.matchesType, mkRsHooks, Jvm.defaultIsSubtypeOf]
  dsimp only [Jvm.stepInstr, Jvm.evalCheckCast, Jvm.JvmHeap.checkCast]
  rw [hci]
  rfl

theorem stepInstr_invokeinterface {Ext Heap : Type} (hooks : Jvm.JvmHooks Ext Heap)
    (st : Jvm.JvmState Ext Heap) (cls m desc : String) :
    Jvm.stepInstr hooks (.invokeinterface cls m desc) st =
      Jvm.stepInvokeInterfaceGeneric hooks st cls m desc := rfl

theorem runJvmResFast_collection_add {hooks : Jvm.JvmHooks RsExt RsHeap}
    {f pc pc0 listAddr arrAddr : Nat} {prog rest : List JvmInstr}
    {elem : JvmVal} {elems : Array JvmVal} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap RsExt} {hp : RsHeap}
    (hb : ListBackedBy jh listAddr arrAddr elems)
    (href : elem.isRef = true) :
    let jh' := jh.set arrAddr (.objArray "java/lang/Object" (elems.push elem))
    Jvm.runJvmResFast hooks (f + 1) prog pc
        (.invokeinterface "java/util/Collection" "add" "(Ljava/lang/Object;)Z" :: rest)
        ⟨pc0, elem :: .heapRef listAddr :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest
        ⟨pc + 1, .i32 1 :: stk, locs, jh', hp⟩ := by
  refine runJvmResFast_of_step _ rfl (by simp) ?_ rfl
  rcases hb with ⟨_, _, _, hgl, hga⟩
  have hcompat : Jvm.isArrayElemCompat hooks jh "java/lang/Object" elem = true := by
    cases elem <;> simp_all [Jvm.isArrayElemCompat, Jvm.JvmVal.isRef]
  have hf1 : List.find? (fun x : String × JvmVal => x.fst == "arr") [("arr", .heapRef arrAddr)] =
      some ("arr", .heapRef arrAddr) := rfl
  rw [stepInstr_invokeinterface]
  simp only [Jvm.stepInvokeInterfaceGeneric, hgl, hf1, Option.map, hga, hcompat, ↓reduceIte]

theorem listBackedBy_set_arr {jh : Jvm.JvmHeap RsExt} {listAddr arrAddr : Nat}
    {elems : Array JvmVal} {elem : JvmVal} (hb : ListBackedBy jh listAddr arrAddr elems) :
    let jh' := jh.set arrAddr (.objArray "java/lang/Object" (elems.push elem))
    ListBackedBy jh' listAddr arrAddr (elems.push elem) ∧
    jh'.objects.size = jh.objects.size ∧
    jh'.statics = jh.statics ∧
    (∀ a, a ≠ arrAddr → jh'.get? a = jh.get? a) := by
  rcases hb with ⟨hne, haLt, hlLt, hgl, hga⟩
  refine ⟨⟨hne, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp [Jvm.JvmHeap.set, haLt]
  · simp [Jvm.JvmHeap.set, haLt, hlLt]
  · rw [Jvm.jvmHeap_get?_set_ne _ _ hne.symm]
    exact hgl
  · exact Jvm.jvmHeap_get?_set_self hga
  · simp [Jvm.JvmHeap.set, haLt]
  · simp [Jvm.JvmHeap.set, haLt]
  · intro a hne'
    exact Jvm.jvmHeap_get?_set_ne _ _ hne'

theorem runJvmResFast_collection_isEmpty {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 listAddr arrAddr : Nat} {prog rest : List JvmInstr}
    {elems : Array JvmVal} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap RsExt} {hp : RsHeap}
    (hb : ListBackedBy jh listAddr arrAddr elems) :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokeinterface "java/util/Collection" "isEmpty" "()Z" :: rest)
        ⟨pc0, .heapRef listAddr :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .i32 (if elems.isEmpty then 1 else 0) :: stk, locs, jh, hp⟩ := by
  apply runJvmResFast_of_step _ rfl (by simp) _ rfl
  have hex := hb.extract
  have hBase :
      Jvm.stepInstr (mkRsHooks resolveProg (d + 1) subFuel)
        (.invokeinterface "java/util/Collection" "isEmpty" "()Z")
        ⟨pc, .heapRef listAddr :: stk, locs, jh, hp⟩ =
      (match Jvm.extractListArray? jh listAddr with
       | some elems => .inl (some ⟨pc + 1, .i32 (if elems.isEmpty then 1 else 0) :: stk, locs, jh, hp⟩)
       | none => .inr none) := rfl
  rw [hBase, hex]

theorem runJvmResFast_list_size {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 listAddr arrAddr : Nat} {prog rest : List JvmInstr}
    {elems : Array JvmVal} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap RsExt} {hp : RsHeap}
    (hb : ListBackedBy jh listAddr arrAddr elems) :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokeinterface "java/util/List" "size" "()I" :: rest)
        ⟨pc0, .heapRef listAddr :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .i32 (UInt32.ofNat elems.size) :: stk, locs, jh, hp⟩ := by
  apply runJvmResFast_of_step _ rfl (by simp) _ rfl
  have hex := hb.extract
  have hBase :
      Jvm.stepInstr (mkRsHooks resolveProg (d + 1) subFuel)
        (.invokeinterface "java/util/List" "size" "()I")
        ⟨pc, .heapRef listAddr :: stk, locs, jh, hp⟩ =
      (match Jvm.extractListArray? jh listAddr with
       | some elems => .inl (some ⟨pc + 1, .i32 (UInt32.ofNat elems.size) :: stk, locs, jh, hp⟩)
       | none => .inr none) := rfl
  rw [hBase, hex]

theorem runJvmResFast_list_get {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 listAddr arrAddr : Nat} {prog rest : List JvmInstr}
    {idx : UInt32} {elems : Array JvmVal} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap RsExt} {hp : RsHeap}
    (hb : ListBackedBy jh listAddr arrAddr elems)
    (hs : idx.toBitVec.slt 0#32 = false)
    (hlt : idx.toNat < elems.size) :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokeinterface "java/util/List" "get" "(I)Ljava/lang/Object;" :: rest)
        ⟨pc0, .i32 idx :: .heapRef listAddr :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, elems[idx.toNat] :: stk, locs, jh, hp⟩ := by
  apply runJvmResFast_of_step _ rfl (by simp) _ rfl
  have hex := hb.extract
  dsimp only [Jvm.stepInstr, Jvm.stepInvokeInterfaceGeneric, mkRsHooks]
  simp only [Jvm.JvmVal.asI32?_i32, hex, hs, hlt]
  rfl

theorem runJvmResFast_collections_first {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 listAddr arrAddr : Nat} {prog rest : List JvmInstr}
    {elems : Array JvmVal} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap RsExt} {hp : RsHeap}
    (hb : ListBackedBy jh listAddr arrAddr elems)
    (hlt : 0 < elems.size) :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokestatic "kotlin/collections/CollectionsKt" "first" "(Ljava/util/List;)Ljava/lang/Object;" :: rest)
        ⟨pc0, .heapRef listAddr :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, elems[0] :: stk, locs, jh, hp⟩ := by
  apply runJvmResFast_of_step _ rfl (by simp) _ rfl
  have hex := hb.extract
  have hBase :
      Jvm.stepInstr (mkRsHooks resolveProg (d + 1) subFuel)
        (.invokestatic "kotlin/collections/CollectionsKt" "first" "(Ljava/util/List;)Ljava/lang/Object;")
        ⟨pc, .heapRef listAddr :: stk, locs, jh, hp⟩ =
      (match Jvm.extractListArray? jh listAddr with
       | some elems =>
         if h : 0 < elems.size then .inl (some ⟨pc + 1, elems[0] :: stk, locs, jh, hp⟩)
         else .inr none
       | none => .inr none) := rfl
  rw [hBase, hex]
  simp [hlt]

theorem runJvmResFast_collections_sizeOrDefault {hooks : Jvm.JvmHooks RsExt RsHeap}
    {f pc pc0 listAddr arrAddr : Nat} {prog rest : List JvmInstr}
    {dflt : JvmVal} {elems : Array JvmVal} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap RsExt} {hp : RsHeap}
    (hb : ListBackedBy jh listAddr arrAddr elems) :
    Jvm.runJvmResFast hooks (f + 1) prog pc
        (.invokestatic "kotlin/collections/CollectionsKt" "collectionSizeOrDefault"
          "(Ljava/lang/Iterable;I)I" :: rest)
        ⟨pc0, dflt :: .heapRef listAddr :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest
        ⟨pc + 1, .i32 (UInt32.ofNat elems.size) :: stk, locs, jh, hp⟩ := by
  refine runJvmResFast_of_step _ rfl (by simp) ?_ rfl
  have hex := hb.extract
  unfold Jvm.stepInstr Jvm.stepInvokeStaticGeneric
  simp only [hex]

theorem runJvmResFast_iterable_iterator {hooks : Jvm.JvmHooks RsExt RsHeap}
    {f pc pc0 listAddr arrAddr : Nat} {prog rest : List JvmInstr}
    {elems : Array JvmVal} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap RsExt} {hp : RsHeap}
    (hb : ListBackedBy jh listAddr arrAddr elems) :
    let itAlloc := jh.alloc (.instance "java/util/Iterator" [("arr", .heapRef arrAddr), ("idx", .i32 0)])
    Jvm.runJvmResFast hooks (f + 1) prog pc
        (.invokeinterface "java/lang/Iterable" "iterator" "()Ljava/util/Iterator;" :: rest)
        ⟨pc0, .heapRef listAddr :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest
        ⟨pc + 1, .heapRef itAlloc.1 :: stk, locs, itAlloc.2, hp⟩ := by
  refine runJvmResFast_of_step _ rfl (by simp) ?_ rfl
  have hex := hb.extract
  have hgl := hb.2.2.2.1
  unfold Jvm.stepInstr Jvm.stepInvokeInterfaceGeneric
  simp only [hex, hgl]
  rfl

theorem iterable_iterator_backed {jh : Jvm.JvmHeap RsExt} {listAddr arrAddr : Nat}
    {elems : Array JvmVal} (hb : ListBackedBy jh listAddr arrAddr elems) :
    let itAlloc := jh.alloc (.instance "java/util/Iterator" [("arr", .heapRef arrAddr), ("idx", .i32 0)])
    IterBackedBy itAlloc.2 itAlloc.1 arrAddr 0 elems ∧
    itAlloc.1 = jh.objects.size ∧
    itAlloc.2.objects.size = jh.objects.size + 1 ∧
    itAlloc.2.statics = jh.statics ∧
    (∀ a, a < jh.objects.size → itAlloc.2.get? a = jh.get? a) := by
  rcases hb with ⟨_, haLt, _, _, hga⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, rfl, ?_, rfl, ?_⟩
  · simp [Jvm.JvmHeap.alloc]; omega
  · simp [Jvm.JvmHeap.alloc]
  · simp [Jvm.JvmHeap.alloc]; omega
  · exact Jvm.jvmHeap_get?_alloc_self _ _
  · rw [Jvm.jvmHeap_get?_alloc_old _ _ haLt]
    exact hga
  · simp [Jvm.JvmHeap.alloc]
  · intro a ha
    exact Jvm.jvmHeap_get?_alloc_old _ _ ha

theorem runJvmResFast_iterator_hasNext {hooks : Jvm.JvmHooks RsExt RsHeap}
    {f pc pc0 itAddr arrAddr : Nat} {prog rest : List JvmInstr}
    {idx : UInt32} {elems : Array JvmVal} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap RsExt} {hp : RsHeap}
    (hb : IterBackedBy jh itAddr arrAddr idx elems) :
    Jvm.runJvmResFast hooks (f + 1) prog pc
        (.invokeinterface "java/util/Iterator" "hasNext" "()Z" :: rest)
        ⟨pc0, .heapRef itAddr :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest
        ⟨pc + 1, .i32 (if idx.toNat < elems.size then 1 else 0) :: stk, locs, jh, hp⟩ := by
  refine runJvmResFast_of_step _ rfl (by simp) ?_ rfl
  rcases hb with ⟨_, _, _, hgi, hga⟩
  have hf1 : List.find? (fun x : String × JvmVal => x.fst == "arr")
      [("arr", .heapRef arrAddr), ("idx", .i32 idx)] = some ("arr", .heapRef arrAddr) := rfl
  have hf2 : List.find? (fun x : String × JvmVal => x.fst == "idx")
      [("arr", .heapRef arrAddr), ("idx", .i32 idx)] = some ("idx", .i32 idx) := rfl
  rw [stepInstr_invokeinterface]
  simp only [Jvm.stepInvokeInterfaceGeneric, hgi, hf1, hf2, Option.map, hga]

theorem runJvmResFast_iterator_next {hooks : Jvm.JvmHooks RsExt RsHeap}
    {f pc pc0 itAddr arrAddr : Nat} {prog rest : List JvmInstr}
    {idx : UInt32} {elems : Array JvmVal} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap RsExt} {hp : RsHeap}
    (hb : IterBackedBy jh itAddr arrAddr idx elems)
    (hlt : idx.toNat < elems.size) :
    let jh' := jh.set itAddr (.instance "java/util/Iterator" [("arr", .heapRef arrAddr), ("idx", .i32 (idx + 1))])
    Jvm.runJvmResFast hooks (f + 1) prog pc
        (.invokeinterface "java/util/Iterator" "next" "()Ljava/lang/Object;" :: rest)
        ⟨pc0, .heapRef itAddr :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest
        ⟨pc + 1, elems[idx.toNat] :: stk, locs, jh', hp⟩ := by
  refine runJvmResFast_of_step _ rfl (by simp) ?_ rfl
  rcases hb with ⟨_, _, _, hgi, hga⟩
  have hf1 : List.find? (fun x : String × JvmVal => x.fst == "arr")
      [("arr", .heapRef arrAddr), ("idx", .i32 idx)] = some ("arr", .heapRef arrAddr) := rfl
  have hf2 : List.find? (fun x : String × JvmVal => x.fst == "idx")
      [("arr", .heapRef arrAddr), ("idx", .i32 idx)] = some ("idx", .i32 idx) := rfl
  rw [stepInstr_invokeinterface]
  simp only [Jvm.stepInvokeInterfaceGeneric, hgi, hf1, hf2, Option.map, hga, hlt, dite_true]

theorem iterBackedBy_next {jh : Jvm.JvmHeap RsExt} {itAddr arrAddr : Nat}
    {idx : UInt32} {elems : Array JvmVal} (hb : IterBackedBy jh itAddr arrAddr idx elems) :
    let jh' := jh.set itAddr (.instance "java/util/Iterator" [("arr", .heapRef arrAddr), ("idx", .i32 (idx + 1))])
    IterBackedBy jh' itAddr arrAddr (idx + 1) elems ∧
    jh'.objects.size = jh.objects.size ∧
    jh'.statics = jh.statics ∧
    (∀ a, a ≠ itAddr → jh'.get? a = jh.get? a) := by
  rcases hb with ⟨hne, hiLt, haLt, hgi, hga⟩
  refine ⟨⟨hne, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp [Jvm.JvmHeap.set, hiLt]
  · simp [Jvm.JvmHeap.set, hiLt, haLt]
  · exact Jvm.jvmHeap_get?_set_self hgi
  · rw [Jvm.jvmHeap_get?_set_ne _ _ hne.symm]
    exact hga
  · simp [Jvm.JvmHeap.set, hiLt]
  · simp [Jvm.JvmHeap.set, hiLt]
  · intro a hne'
    exact Jvm.jvmHeap_get?_set_ne _ _ hne'

theorem mapM_throwables (ts : List ThrowableModel) :
    (ts.map fun t => (.ext (.throwable t) : JvmVal)).mapM (fun
      | .ext (.throwable t) => some t
      | _ => none) = some ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.map_cons, List.mapM_cons]
    rw [ih]
    rfl

theorem runJvmResFast_compositeException_init {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 listAddr arrAddr : Nat} {prog rest : List JvmInstr}
    {ts : List ThrowableModel} {elems : Array JvmVal}
    {cls1 cls2 : String} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap RsExt} {hp : RsHeap}
    (hb : ListBackedBy jh listAddr arrAddr elems)
    (heq : elems.toList = ts.map fun t => .ext (.throwable t))
    (hlen : 2 ≤ ts.length) :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokespecial "com/alexvanyo/composelife/resourcestate/CompositeException"
          "<init>" "(Ljava/util/List;)V" :: rest)
        ⟨pc0, .heapRef listAddr :: .allocRef cls1 :: .allocRef cls2 :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.throwable (.composite ts)) :: stk, locs, jh, hp⟩ := by
  apply runJvmResFast_of_step _ rfl (by simp) _ rfl
  have hex : extractThrowableList? jh listAddr = some ts := by
    have hla := hb.extract
    simp only [extractThrowableList?, hla, heq]
    exact mapM_throwables ts
  have hBase :
      Jvm.stepInstr (mkRsHooks resolveProg (d + 1) subFuel)
        (.invokespecial "com/alexvanyo/composelife/resourcestate/CompositeException"
          "<init>" "(Ljava/util/List;)V")
        ⟨pc, .heapRef listAddr :: .allocRef cls1 :: .allocRef cls2 :: stk, locs, jh, hp⟩ =
      (match extractThrowableList? jh listAddr with
       | some ts =>
         if 2 ≤ ts.length then .inl (some ⟨pc + 1, .ext (.throwable (.composite ts)) :: stk, locs, jh, hp⟩)
         else .inr none
       | none => .inr none) := rfl
  rw [hBase, hex]
  simp [hlen]

theorem mapM_rsVals (xs : List RsVal) :
    (xs.map RsVal.toJvmVal).mapM RsVal.ofJvmVal? = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.mapM_cons, RsVal.ofJvmVal?_toJvmVal]
    rw [ih]
    rfl

theorem runJvmResFast_listFn1_invoke {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 cid listAddr arrAddr : Nat} {prog rest : List JvmInstr}
    {fn : List RsVal → RsVal} {xs : List RsVal} {elems : Array JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap RsExt} {hp : RsHeap}
    (hcl : hp.closures[cid]? = some (.listFn1 fn))
    (hb : ListBackedBy jh listAddr arrAddr elems)
    (heq : elems.toList = xs.map RsVal.toJvmVal) :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokeinterface "kotlin/jvm/functions/Function1" "invoke"
          "(Ljava/lang/Object;)Ljava/lang/Object;" :: rest)
        ⟨pc0, .heapRef listAddr :: .ext (.closureRef cid) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, (fn xs).toJvmVal :: stk, locs, jh, hp⟩ := by
  apply runJvmResFast_of_step _ rfl (by simp) _ rfl
  have hex : extractRsValList? jh listAddr = some xs := by
    have hla := hb.extract
    simp only [extractRsValList?, hla, heq]
    exact mapM_rsVals xs
  have h1 :
      Jvm.stepInstr (mkRsHooks resolveProg (d + 1) subFuel)
        (.invokeinterface "kotlin/jvm/functions/Function1" "invoke"
          "(Ljava/lang/Object;)Ljava/lang/Object;")
        ⟨pc, .heapRef listAddr :: .ext (.closureRef cid) :: stk, locs, jh, hp⟩ =
      (match invokeRsClosure ⟨pc, .heapRef listAddr :: .ext (.closureRef cid) :: stk, locs, jh, hp⟩
          cid [.heapRef listAddr] with
       | some res => .inl (some ⟨pc + 1, res :: stk, locs, jh, hp⟩)
       | none => .inr none) := rfl
  rw [h1]
  simp [invokeRsClosure, hcl, hex]

theorem runJvmResFast_iload {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 idx : Nat} {prog rest : List JvmInstr}
    {v : JvmVal} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap RsExt} {hp : RsHeap} (hl : locs idx = v) :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.iload idx :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, v :: stk, locs, jh, hp⟩ := by
  apply runJvmResFast_of_step _ rfl (by simp) _ rfl
  dsimp only [Jvm.stepInstr]
  rw [hl]

theorem runJvmResFast_aload {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 idx : Nat} {prog rest : List JvmInstr}
    {v : JvmVal} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap RsExt} {hp : RsHeap} (hl : locs idx = v) :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.aload idx :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, v :: stk, locs, jh, hp⟩ := by
  apply runJvmResFast_of_step _ rfl (by simp) _ rfl
  dsimp only [Jvm.stepInstr]
  rw [hl]

theorem runJvmResFast_astore {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 idx : Nat} {prog rest : List JvmInstr}
    {v : JvmVal} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap RsExt} {hp : RsHeap} :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.astore idx :: rest) ⟨pc0, v :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, stk, Jvm.setLocal locs idx v, jh, hp⟩ :=
  runJvmResFast_of_step _ rfl (by simp) rfl rfl

theorem runJvmResFast_istore {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 idx : Nat} {prog rest : List JvmInstr}
    {v : UInt32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap RsExt} {hp : RsHeap} :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.istore idx :: rest) ⟨pc0, .i32 v :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, stk, Jvm.setLocal locs idx (.i32 v), jh, hp⟩ :=
  runJvmResFast_of_step _ rfl (by simp) rfl rfl

theorem runJvmResFast_iconst {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    {v : UInt32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap RsExt} {hp : RsHeap} :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.iconst v :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .i32 v :: stk, locs, jh, hp⟩ :=
  runJvmResFast_of_step _ rfl (by simp) rfl rfl

theorem runJvmResFast_pop {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    {v : JvmVal} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap RsExt} {hp : RsHeap} :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.pop :: rest) ⟨pc0, v :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, stk, locs, jh, hp⟩ :=
  runJvmResFast_of_step _ rfl (by simp) rfl rfl

theorem runJvmResFast_swap {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    {a b : JvmVal} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap RsExt} {hp : RsHeap} (hca : a.isCat2 = false) (hcb : b.isCat2 = false) :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.swap :: rest) ⟨pc0, b :: a :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, a :: b :: stk, locs, jh, hp⟩ := by
  apply runJvmResFast_of_step _ rfl (by simp) _ rfl
  dsimp only [Jvm.stepInstr]
  simp [hca, hcb]

theorem runJvmResFast_iinc_add1 {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 idx : Nat} {prog rest : List JvmInstr}
    {cur : UInt32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap RsExt} {hp : RsHeap} (hl : locs idx = .i32 cur) :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.iinc idx 1 :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, stk, Jvm.setLocal locs idx (.i32 (cur + 1)), jh, hp⟩ := by
  apply runJvmResFast_of_step _ rfl (by simp) _ rfl
  dsimp only [Jvm.stepInstr]
  rw [hl]
  rfl

theorem runJvmResFast_if_icmpge_branch {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc target : Nat} {prog rest : List JvmInstr}
    {a b : UInt32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap RsExt} {hp : RsHeap}
    (h : b.toBitVec.sle a.toBitVec = true) :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.if_icmpge target :: rest) ⟨pc, .i32 b :: .i32 a :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog target (prog.drop target)
        ⟨target, stk, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons (mkRsHooks resolveProg (d + 1) subFuel) (hbr := rfl)]
  dsimp only [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch]
  simp only [Jvm.JvmVal.asI32?_i32, h]
  rfl

theorem runJvmResFast_if_icmpge_fallthrough {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc target : Nat} {prog rest : List JvmInstr}
    {a b : UInt32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap RsExt} {hp : RsHeap}
    (h : b.toBitVec.sle a.toBitVec = false) :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.if_icmpge target :: rest) ⟨pc, .i32 b :: .i32 a :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, stk, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons (mkRsHooks resolveProg (d + 1) subFuel) (hbr := rfl)]
  dsimp only [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch]
  simp only [Jvm.JvmVal.asI32?_i32, h]
  rfl

def filterLoopInstrs (pcLoop pcDone arrSlot listSlot idxSlot lenSlot tmpSlot : Nat)
    (cls : String) (tail : List JvmInstr) : List JvmInstr :=
  [.iload idxSlot, .iload lenSlot, .if_icmpge pcDone,
   .aload arrSlot, .iload idxSlot, .aaload, .astore tmpSlot,
   .aload tmpSlot, .instanceof cls, .ifeq (pcLoop + 14),
   .aload listSlot, .aload tmpSlot,
   .invokeinterface "java/util/Collection" "add" "(Ljava/lang/Object;)Z",
   .pop, .iinc idxSlot 1, .goto pcLoop] ++ tail

theorem runJvmResFast_filter_loop {resolveProg : String → Option (List JvmInstr)}
    {d subFuel fRest pcLoop pcDone arrSlot listSlot idxSlot lenSlot tmpSlot srcArrAddr listAddr listArrAddr : Nat}
    {prog : List JvmInstr} {cls : String} {pred : Model.ResourceState RsVal → Bool}
    {states : List (Model.ResourceState RsVal)} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap RsExt} {hp : RsHeap}
    {P : JvmVal × JvmState → Prop}
    (hLoop : prog.drop pcLoop =
      filterLoopInstrs pcLoop pcDone arrSlot listSlot idxSlot lenSlot tmpSlot cls (prog.drop pcDone))
    (hInst : ∀ r : Model.ResourceState RsVal,
      (mkRsHooks resolveProg (d + 1) subFuel).checkInstanceOf cls (.ext (.res r)) = pred r)
    (hlenLt : states.length < 2 ^ 31)
    (hSrcArr : jh.get? srcArrAddr = some (.objArray "com/alexvanyo/composelife/resourcestate/ResourceState"
      (states.map fun r => (.ext (.res r) : JvmVal)).toArray))
    (hSrcNe : srcArrAddr ≠ listArrAddr)
    (hSlots :
      arrSlot ≠ idxSlot ∧ arrSlot ≠ tmpSlot ∧
      listSlot ≠ idxSlot ∧ listSlot ≠ tmpSlot ∧
      lenSlot ≠ idxSlot ∧ lenSlot ≠ tmpSlot ∧
      idxSlot ≠ tmpSlot)
    (hLocArr : locs arrSlot = .heapRef srcArrAddr)
    (hLocList : locs listSlot = .heapRef listAddr)
    (hLocLen : locs lenSlot = .i32 (UInt32.ofNat states.length)) :
    ∀ (i : Nat), i ≤ states.length → ∀ (curJh : Jvm.JvmHeap RsExt) (curLocs : Nat → JvmVal),
      (∀ s, s ≠ idxSlot → s ≠ tmpSlot → curLocs s = locs s) →
      curLocs idxSlot = .i32 (UInt32.ofNat i) →
      ListBackedBy curJh listAddr listArrAddr
        (((states.take i).filter pred).map (fun r => (.ext (.res r) : JvmVal))).toArray →
      (∀ a, a ≠ listArrAddr → curJh.get? a = jh.get? a) →
      curJh.objects.size = jh.objects.size →
      curJh.statics = jh.statics →
      (∀ endLocs endJh,
        (∀ s, s ≠ idxSlot → s ≠ tmpSlot → endLocs s = locs s) →
        ListBackedBy endJh listAddr listArrAddr
          ((states.filter pred).map (fun r => (.ext (.res r) : JvmVal))).toArray →
        (∀ a, a ≠ listArrAddr → endJh.get? a = jh.get? a) →
        endJh.objects.size = jh.objects.size →
        endJh.statics = jh.statics →
        (∃ p, Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) fRest prog pcDone (prog.drop pcDone)
          ⟨pcDone, stk, endLocs, endJh, hp⟩ = some p ∧ P p)) →
      ∃ p, Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel)
        (16 * (states.length - i) + 3 + fRest) prog pcLoop (prog.drop pcLoop)
        ⟨pcLoop, stk, curLocs, curJh, hp⟩ = some p ∧ P p := by
  intro i
  obtain ⟨k, hk⟩ : ∃ k, k = states.length - i := ⟨states.length - i, rfl⟩
  induction k generalizing i with
  | zero =>
    intro hi curJh curLocs hOtherLoc hIdx hb hOtherJh hSize hStat hcont
    have hiEq : i = states.length := by omega
    subst hiEq
    simp only [Nat.sub_self, Nat.mul_zero, Nat.zero_add]
    rw [show 3 + fRest = fRest + 1 + 1 + 1 by omega, hLoop]
    dsimp only [filterLoopInstrs, List.cons_append, List.nil_append]
    rw [runJvmResFast_iload hIdx]
    have hCurLen : curLocs lenSlot = .i32 (UInt32.ofNat states.length) := by
      rw [hOtherLoc lenSlot hSlots.2.2.2.2.1 hSlots.2.2.2.2.2.1, hLocLen]
    rw [runJvmResFast_iload hCurLen]
    rw [runJvmResFast_if_icmpge_branch (by simp [BitVec.sle])]
    rw [list_take_all] at hb
    exact hcont curLocs curJh hOtherLoc hb hOtherJh hSize hStat
  | succ k ih =>
    intro hi curJh curLocs hOtherLoc hIdx hb hOtherJh hSize hStat hcont
    have hiLt : i < states.length := by omega
    have hiLt2 : i < 2 ^ 31 := by omega
    have hkEq : 16 * (states.length - i) + 3 + fRest =
        (16 * k + 3 + fRest) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
          1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 := by omega
    rw [hkEq, hLoop]
    dsimp only [filterLoopInstrs, List.cons_append, List.nil_append]
    rw [runJvmResFast_iload hIdx]
    have hCurLen : curLocs lenSlot = .i32 (UInt32.ofNat states.length) := by
      rw [hOtherLoc lenSlot hSlots.2.2.2.2.1 hSlots.2.2.2.2.2.1, hLocLen]
    rw [runJvmResFast_iload hCurLen]
    have hSle : (UInt32.ofNat states.length).toBitVec.sle (UInt32.ofNat i).toBitVec = false := by
      rw [BitVec.sle,
        Jvm.u32_toInt_eq_toNat (by rw [Jvm.ui32_ofNat_toNat_of_lt states.length hlenLt]; exact hlenLt),
        Jvm.u32_toInt_eq_toNat (by rw [Jvm.ui32_ofNat_toNat_of_lt i hiLt2]; exact hiLt2),
        Jvm.ui32_ofNat_toNat_of_lt states.length hlenLt,
        Jvm.ui32_ofNat_toNat_of_lt i hiLt2]
      exact decide_eq_false (by omega)
    rw [runJvmResFast_if_icmpge_fallthrough hSle]
    have hCurArr : curLocs arrSlot = .heapRef srcArrAddr := by
      rw [hOtherLoc arrSlot hSlots.1 hSlots.2.1, hLocArr]
    rw [runJvmResFast_aload hCurArr]
    rw [runJvmResFast_iload hIdx]
    have hSlt0 : (UInt32.ofNat i).toBitVec.slt 0#32 = false := Jvm.ui32_slt_zero_of_lt i hiLt2
    have hSrcCur : curJh.get? srcArrAddr = some (.objArray "com/alexvanyo/composelife/resourcestate/ResourceState"
        (states.map fun r => (.ext (.res r) : JvmVal)).toArray) := by
      rw [hOtherJh srcArrAddr hSrcNe, hSrcArr]
    have hElemLt : (UInt32.ofNat i).toNat < (states.map fun r => (.ext (.res r) : JvmVal)).toArray.size := by
      simp [Jvm.ui32_ofNat_toNat_of_lt i hiLt2, hiLt]
    rw [runJvmResFast_aaload hSlt0 hSrcCur hElemLt]
    have hElemEq : (states.map fun r => (.ext (.res r) : JvmVal)).toArray[(UInt32.ofNat i).toNat] =
        .ext (.res states[i]) := by
      simp [Jvm.ui32_ofNat_toNat_of_lt i hiLt2]
    rw [hElemEq]
    rw [runJvmResFast_astore]
    rw [runJvmResFast_aload (v := .ext (.res states[i])) (by simp [Jvm.setLocal])]
    rw [runJvmResFast_instanceof_res (pred states[i])
      (show Jvm.evalInstanceOf (mkRsHooks resolveProg (d + 1) subFuel) curJh cls (.ext (.res states[i])) =
        pred states[i] from hInst states[i])]
    have hTakeSucc :
        (((states.take (i + 1)).filter pred).map (fun r => (.ext (.res r) : JvmVal))).toArray =
          if pred states[i] then
            (((states.take i).filter pred).map (fun r => (.ext (.res r) : JvmVal))).toArray.push
              (.ext (.res states[i]))
          else
            (((states.take i).filter pred).map (fun r => (.ext (.res r) : JvmVal))).toArray := by
      rw [list_take_succ states i hiLt, List.filter_append]
      cases hpr : pred states[i] <;> simp [hpr, List.map_append]
    have hLoc1Idx : (Jvm.setLocal curLocs tmpSlot (.ext (.res states[i]))) idxSlot =
        .i32 (UInt32.ofNat i) := by
      simp [Jvm.setLocal, hSlots.2.2.2.2.2.2, hIdx]
    have hAdd1 : UInt32.ofNat i + 1 = UInt32.ofNat (i + 1) := by
      simp [UInt32.ofNat_add]
    have hLocNextOther : ∀ s, s ≠ idxSlot → s ≠ tmpSlot →
        Jvm.setLocal (Jvm.setLocal curLocs tmpSlot (.ext (.res states[i]))) idxSlot
          (.i32 (UInt32.ofNat i + 1)) s = locs s := by
      intro s hs1 hs2
      simp [Jvm.setLocal, hs1, hs2, hOtherLoc s hs1 hs2]
    have hLocNextIdx :
        Jvm.setLocal (Jvm.setLocal curLocs tmpSlot (.ext (.res states[i]))) idxSlot
          (.i32 (UInt32.ofNat i + 1)) idxSlot = .i32 (UInt32.ofNat (i + 1)) := by
      simp only [Jvm.setLocal, ↓reduceIte, hAdd1]
    cases hpr : pred states[i] with
    | true =>
      simp only [hpr, ↓reduceIte] at hTakeSucc
      rw [Jvm.runJvmResFast_ifeq_fallthrough (hooks := mkRsHooks resolveProg (d + 1) subFuel) (by decide)]
      have hLoc1List : (Jvm.setLocal curLocs tmpSlot (.ext (.res states[i]))) listSlot = .heapRef listAddr := by
        have : (Jvm.setLocal curLocs tmpSlot (.ext (.res states[i]))) listSlot = curLocs listSlot := by
          simp [Jvm.setLocal, hSlots.2.2.2.1]
        rw [this, hOtherLoc listSlot hSlots.2.2.1 hSlots.2.2.2.1, hLocList]
      rw [runJvmResFast_aload hLoc1List]
      rw [runJvmResFast_aload (v := .ext (.res states[i])) (by simp [Jvm.setLocal])]
      rw [runJvmResFast_collection_add hb (href := rfl)]
      rw [runJvmResFast_pop]
      rw [runJvmResFast_iinc_add1 hLoc1Idx]
      rw [Jvm.runJvmResFast_goto]
      have hPack := listBackedBy_set_arr hb (elem := .ext (.res states[i]))
      rw [← hTakeSucc] at hPack ⊢
      rw [show 16 * k + 3 + fRest = 16 * (states.length - (i + 1)) + 3 + fRest by omega]
      exact ih (i + 1) (by omega) (by omega) _ _
        hLocNextOther hLocNextIdx hPack.1
        (fun a ha => by rw [hPack.2.2.2 a ha, hOtherJh a ha])
        (by rw [hPack.2.1, hSize]) (by rw [hPack.2.2.1, hStat]) hcont
    | false =>
      simp only [hpr, Bool.false_eq_true, ↓reduceIte] at hTakeSucc
      rw [Jvm.runJvmResFast_ifeq_branch (hooks := mkRsHooks resolveProg (d + 1) subFuel) (by rfl)]
      have hIncDrop : prog.drop (pcLoop + 14) = [.iinc idxSlot 1, .goto pcLoop] ++ prog.drop pcDone := by
        rw [show prog.drop (pcLoop + 14) = (prog.drop pcLoop).drop 14 by simp [List.drop_drop], hLoop]
        rfl
      rw [hIncDrop]
      dsimp only [List.cons_append, List.nil_append]
      rw [runJvmResFast_iinc_add1 hLoc1Idx]
      rw [Jvm.runJvmResFast_goto]
      have hRemEq : 16 * (states.length - (i + 1)) + 3 + fRest ≤ 16 * k + 3 + fRest + 4 := by omega
      rw [← hTakeSucc] at hb
      obtain ⟨p, hpRun, hP⟩ := ih (i + 1) (by omega) (by omega) _ _
        hLocNextOther hLocNextIdx hb hOtherJh hSize hStat hcont
      exact ⟨p, runJvmResFast_mono _ hRemEq hpRun, hP⟩

def mapFailureLoopInstrs
    (pcLoop pcDone iterSlot outListSlot tmp1 failSlot tmpOutSlot dummySlot : Nat)
    (tail : List JvmInstr) : List JvmInstr :=
  [.aload iterSlot,
   .invokeinterface "java/util/Iterator" "hasNext" "()Z",
   .ifeq pcDone,
   .aload iterSlot,
   .invokeinterface "java/util/Iterator" "next" "()Ljava/lang/Object;",
   .astore tmp1,
   .aload outListSlot,
   .aload tmp1,
   .checkcast "com/alexvanyo/composelife/resourcestate/ResourceState$Failure",
   .astore failSlot,
   .astore tmpOutSlot,
   .iconst 0,
   .istore dummySlot,
   .aload failSlot,
   .invokevirtual "com/alexvanyo/composelife/resourcestate/ResourceState$Failure" "getThrowable"
     "()Ljava/lang/Throwable;",
   .aload tmpOutSlot,
   .swap,
   .invokeinterface "java/util/Collection" "add" "(Ljava/lang/Object;)Z",
   .pop,
   .goto pcLoop] ++ tail

theorem runJvmResFast_mapFailure_loop {resolveProg : String → Option (List JvmInstr)}
    {d subFuel fRest pcLoop pcDone iterSlot outListSlot tmp1 failSlot tmpOutSlot dummySlot
      itAddr srcArrAddr outListAddr outArrAddr : Nat}
    {prog : List JvmInstr} {ts : List ThrowableModel} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap RsExt} {hp : RsHeap}
    {P : JvmVal × JvmState → Prop}
    (hLoop : prog.drop pcLoop =
      mapFailureLoopInstrs pcLoop pcDone iterSlot outListSlot tmp1 failSlot tmpOutSlot dummySlot (prog.drop pcDone))
    (hlenLt : ts.length < 2 ^ 31)
    (hNeSrcOut : srcArrAddr ≠ outArrAddr)
    (hNeItOut : itAddr ≠ outArrAddr)
    (hNeOutListIt : outListAddr ≠ itAddr)
    (hSlots :
      iterSlot ∉ [tmp1, failSlot, tmpOutSlot, dummySlot] ∧
      outListSlot ∉ [tmp1, failSlot, tmpOutSlot, dummySlot] ∧
      failSlot ≠ tmpOutSlot ∧ failSlot ≠ dummySlot ∧ tmpOutSlot ≠ dummySlot)
    (hLocIter : locs iterSlot = .heapRef itAddr)
    (hLocOut : locs outListSlot = .heapRef outListAddr) :
    ∀ (i : Nat), i ≤ ts.length → ∀ (curJh : Jvm.JvmHeap RsExt) (curLocs : Nat → JvmVal),
      (∀ s, s ∉ [tmp1, failSlot, tmpOutSlot, dummySlot] → curLocs s = locs s) →
      IterBackedBy curJh itAddr srcArrAddr (UInt32.ofNat i)
        (ts.map fun t => (.ext (.res (.failure t)) : JvmVal)).toArray →
      ListBackedBy curJh outListAddr outArrAddr
        (((ts.take i).map fun t => (.ext (.throwable t) : JvmVal))).toArray →
      (∀ a, a ≠ itAddr → a ≠ outArrAddr → curJh.get? a = jh.get? a) →
      curJh.objects.size = jh.objects.size →
      curJh.statics = jh.statics →
      (∀ endLocs endJh,
        (∀ s, s ∉ [tmp1, failSlot, tmpOutSlot, dummySlot] → endLocs s = locs s) →
        ListBackedBy endJh outListAddr outArrAddr
          (ts.map fun t => (.ext (.throwable t) : JvmVal)).toArray →
        (∀ a, a ≠ itAddr → a ≠ outArrAddr → endJh.get? a = jh.get? a) →
        endJh.objects.size = jh.objects.size →
        endJh.statics = jh.statics →
        (∃ p, Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) fRest prog pcDone (prog.drop pcDone)
          ⟨pcDone, stk, endLocs, endJh, hp⟩ = some p ∧ P p)) →
      ∃ p, Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel)
        (20 * (ts.length - i) + 3 + fRest) prog pcLoop (prog.drop pcLoop)
        ⟨pcLoop, stk, curLocs, curJh, hp⟩ = some p ∧ P p := by
  intro i
  obtain ⟨k, hk⟩ : ∃ k, k = ts.length - i := ⟨ts.length - i, rfl⟩
  induction k generalizing i with
  | zero =>
    intro hi curJh curLocs hOtherLoc hIter hOut hOtherJh hSize hStat hcont
    have hiEq : i = ts.length := by omega
    subst hiEq
    simp only [Nat.sub_self, Nat.mul_zero, Nat.zero_add]
    rw [show 3 + fRest = fRest + 1 + 1 + 1 by omega, hLoop]
    dsimp only [mapFailureLoopInstrs, List.cons_append, List.nil_append]
    have hCurIt : curLocs iterSlot = .heapRef itAddr := by
      rw [hOtherLoc iterSlot hSlots.1, hLocIter]
    rw [runJvmResFast_aload hCurIt]
    rw [runJvmResFast_iterator_hasNext hIter]
    have hNotLt : ¬ (UInt32.ofNat ts.length).toNat < (ts.map fun t => (.ext (.res (.failure t)) : JvmVal)).toArray.size := by
      simp [Jvm.ui32_ofNat_toNat_of_lt ts.length hlenLt]
    simp only [hNotLt, ↓reduceIte]
    rw [Jvm.runJvmResFast_ifeq_branch (hooks := mkRsHooks resolveProg (d + 1) subFuel) (by rfl)]
    rw [list_take_all] at hOut
    exact hcont curLocs curJh hOtherLoc hOut hOtherJh hSize hStat
  | succ k ih =>
    intro hi curJh curLocs hOtherLoc hIter hOut hOtherJh hSize hStat hcont
    have hiLt : i < ts.length := by omega
    have hiLt2 : i < 2 ^ 31 := by omega
    have hkEq : 20 * (ts.length - i) + 3 + fRest =
        (20 * k + 3 + fRest) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
          1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 := by omega
    rw [hkEq, hLoop]
    dsimp only [mapFailureLoopInstrs, List.cons_append, List.nil_append]
    have hCurIt : curLocs iterSlot = .heapRef itAddr := by
      rw [hOtherLoc iterSlot hSlots.1, hLocIter]
    rw [runJvmResFast_aload hCurIt]
    rw [runJvmResFast_iterator_hasNext hIter]
    have hLt : (UInt32.ofNat i).toNat < (ts.map fun t => (.ext (.res (.failure t)) : JvmVal)).toArray.size := by
      simp [Jvm.ui32_ofNat_toNat_of_lt i hiLt2, hiLt]
    simp only [hLt, ↓reduceIte]
    rw [Jvm.runJvmResFast_ifeq_fallthrough (hooks := mkRsHooks resolveProg (d + 1) subFuel) (by decide)]
    rw [runJvmResFast_aload hCurIt]
    rw [runJvmResFast_iterator_next hIter hLt]
    have hElemEq : (ts.map fun t => (.ext (.res (.failure t)) : JvmVal)).toArray[(UInt32.ofNat i).toNat] =
        .ext (.res (.failure ts[i])) := by
      simp [Jvm.ui32_ofNat_toNat_of_lt i hiLt2]
    rw [hElemEq]
    have hIterNext := iterBackedBy_next hIter
    have hOutAfterNext :
        ListBackedBy (curJh.set itAddr (.instance "java/util/Iterator"
          [("arr", .heapRef srcArrAddr), ("idx", .i32 (UInt32.ofNat i + 1))])) outListAddr outArrAddr
          (((ts.take i).map fun t => (.ext (.throwable t) : JvmVal))).toArray := by
      refine hOut.preserve ?_ ?_ (by omega)
      · exact hIterNext.2.2.2 outListAddr hNeOutListIt
      · exact hIterNext.2.2.2 outArrAddr hNeItOut.symm
    rw [runJvmResFast_astore]
    have hLoc1Out : (Jvm.setLocal curLocs tmp1 (.ext (.res (.failure ts[i])))) outListSlot = .heapRef outListAddr := by
      have hne : outListSlot ≠ tmp1 := by simp_all [List.mem_cons]
      simp only [Jvm.setLocal, hne, ↓reduceIte]
      rw [hOtherLoc outListSlot hSlots.2.1, hLocOut]
    rw [runJvmResFast_aload hLoc1Out]
    rw [runJvmResFast_aload (v := .ext (.res (.failure ts[i]))) (by simp [Jvm.setLocal])]
    rw [runJvmResFast_checkcast_res rfl]
    rw [runJvmResFast_astore]
    rw [runJvmResFast_astore]
    rw [runJvmResFast_iconst]
    rw [runJvmResFast_istore]
    rw [runJvmResFast_aload (v := .ext (.res (.failure ts[i])))
      (by simp [Jvm.setLocal, hSlots.2.2.2.1, hSlots.2.2.1])]
    rw [runJvmResFast_failure_getThrowable]
    rw [runJvmResFast_aload (v := .heapRef outListAddr) (by simp [Jvm.setLocal, hSlots.2.2.2.2])]
    rw [runJvmResFast_swap (hca := rfl) (hcb := rfl)]
    rw [runJvmResFast_collection_add hOutAfterNext (href := rfl)]
    rw [runJvmResFast_pop]
    rw [Jvm.runJvmResFast_goto]
    have hAdd1 : UInt32.ofNat i + 1 = UInt32.ofNat (i + 1) := by simp [UInt32.ofNat_add]
    have hPackIter :
        IterBackedBy ((curJh.set itAddr (.instance "java/util/Iterator"
          [("arr", .heapRef srcArrAddr), ("idx", .i32 (UInt32.ofNat i + 1))])).set outArrAddr
          (.objArray "java/lang/Object"
            ((((ts.take i).map fun t => (.ext (.throwable t) : JvmVal))).toArray.push
              (.ext (.throwable ts[i])))))
          itAddr srcArrAddr (UInt32.ofNat (i + 1))
          (ts.map fun t => (.ext (.res (.failure t)) : JvmVal)).toArray := by
      have hAdd := listBackedBy_set_arr hOutAfterNext (elem := .ext (.throwable ts[i]))
      rw [← hAdd1]
      refine hIterNext.1.preserve ?_ ?_ (by omega)
      · exact hAdd.2.2.2 itAddr hNeItOut
      · exact hAdd.2.2.2 srcArrAddr hNeSrcOut
    have hTakeSucc :
        (((ts.take (i + 1)).map fun t => (.ext (.throwable t) : JvmVal))).toArray =
          (((ts.take i).map fun t => (.ext (.throwable t) : JvmVal))).toArray.push
            (.ext (.throwable ts[i])) := by
      rw [list_take_succ ts i hiLt, List.map_append]
      simp
    have hPackOut := listBackedBy_set_arr hOutAfterNext (elem := .ext (.throwable ts[i]))
    rw [← hTakeSucc] at hPackIter hPackOut ⊢
    rw [show 20 * k + 3 + fRest = 20 * (ts.length - (i + 1)) + 3 + fRest by omega]
    have hNextLocOther : ∀ s, s ∉ [tmp1, failSlot, tmpOutSlot, dummySlot] →
        Jvm.setLocal (Jvm.setLocal (Jvm.setLocal (Jvm.setLocal curLocs tmp1 (.ext (.res (.failure ts[i]))))
          failSlot (.ext (.res (.failure ts[i]))))
          tmpOutSlot (.heapRef outListAddr)) dummySlot (.i32 0) s = locs s := by
      intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hs
      rcases hs with ⟨hs1, hs2, hs3, hs4⟩
      simp [Jvm.setLocal, hs1, hs2, hs3, hs4, hOtherLoc s (by simp [hs1, hs2, hs3, hs4])]
    exact ih (i + 1) (by omega) (by omega) _ _
      hNextLocOther hPackIter hPackOut.1
      (fun a ha1 ha2 => by
        rw [hPackOut.2.2.2 a ha2, hIterNext.2.2.2 a ha1, hOtherJh a ha1 ha2])
      (by rw [hPackOut.2.1, hIterNext.2.1, hSize])
      (by rw [hPackOut.2.2.1, hIterNext.2.2.1, hStat])
      hcont

def mapSuccessLoopInstrs
    (pcLoop pcDone iterSlot outListSlot tmp1 succSlot tmpOutSlot dummySlot : Nat)
    (tail : List JvmInstr) : List JvmInstr :=
  [.aload iterSlot,
   .invokeinterface "java/util/Iterator" "hasNext" "()Z",
   .ifeq pcDone,
   .aload iterSlot,
   .invokeinterface "java/util/Iterator" "next" "()Ljava/lang/Object;",
   .astore tmp1,
   .aload outListSlot,
   .aload tmp1,
   .checkcast "com/alexvanyo/composelife/resourcestate/ResourceState$Success",
   .astore succSlot,
   .astore tmpOutSlot,
   .iconst 0,
   .istore dummySlot,
   .aload succSlot,
   .invokevirtual "com/alexvanyo/composelife/resourcestate/ResourceState$Success" "getValue"
     "()Ljava/lang/Object;",
   .aload tmpOutSlot,
   .swap,
   .invokeinterface "java/util/Collection" "add" "(Ljava/lang/Object;)Z",
   .pop,
   .goto pcLoop] ++ tail

theorem runJvmResFast_mapSuccess_loop {resolveProg : String → Option (List JvmInstr)}
    {d subFuel fRest pcLoop pcDone iterSlot outListSlot tmp1 succSlot tmpOutSlot dummySlot
      itAddr srcArrAddr outListAddr outArrAddr : Nat}
    {prog : List JvmInstr} {vs : List RsVal} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap RsExt} {hp : RsHeap}
    {P : JvmVal × JvmState → Prop}
    (hLoop : prog.drop pcLoop =
      mapSuccessLoopInstrs pcLoop pcDone iterSlot outListSlot tmp1 succSlot tmpOutSlot dummySlot (prog.drop pcDone))
    (hlenLt : vs.length < 2 ^ 31)
    (hNeSrcOut : srcArrAddr ≠ outArrAddr)
    (hNeItOut : itAddr ≠ outArrAddr)
    (hNeOutListIt : outListAddr ≠ itAddr)
    (hSlots :
      iterSlot ∉ [tmp1, succSlot, tmpOutSlot, dummySlot] ∧
      outListSlot ∉ [tmp1, succSlot, tmpOutSlot, dummySlot] ∧
      succSlot ≠ tmpOutSlot ∧ succSlot ≠ dummySlot ∧ tmpOutSlot ≠ dummySlot)
    (hLocIter : locs iterSlot = .heapRef itAddr)
    (hLocOut : locs outListSlot = .heapRef outListAddr) :
    ∀ (i : Nat), i ≤ vs.length → ∀ (curJh : Jvm.JvmHeap RsExt) (curLocs : Nat → JvmVal),
      (∀ s, s ∉ [tmp1, succSlot, tmpOutSlot, dummySlot] → curLocs s = locs s) →
      IterBackedBy curJh itAddr srcArrAddr (UInt32.ofNat i)
        (vs.map fun v => (.ext (.res (.success v)) : JvmVal)).toArray →
      ListBackedBy curJh outListAddr outArrAddr
        (((vs.take i).map RsVal.toJvmVal)).toArray →
      (∀ a, a ≠ itAddr → a ≠ outArrAddr → curJh.get? a = jh.get? a) →
      curJh.objects.size = jh.objects.size →
      curJh.statics = jh.statics →
      (∀ endLocs endJh,
        (∀ s, s ∉ [tmp1, succSlot, tmpOutSlot, dummySlot] → endLocs s = locs s) →
        ListBackedBy endJh outListAddr outArrAddr
          (vs.map RsVal.toJvmVal).toArray →
        (∀ a, a ≠ itAddr → a ≠ outArrAddr → endJh.get? a = jh.get? a) →
        endJh.objects.size = jh.objects.size →
        endJh.statics = jh.statics →
        (∃ p, Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) fRest prog pcDone (prog.drop pcDone)
          ⟨pcDone, stk, endLocs, endJh, hp⟩ = some p ∧ P p)) →
      ∃ p, Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel)
        (20 * (vs.length - i) + 3 + fRest) prog pcLoop (prog.drop pcLoop)
        ⟨pcLoop, stk, curLocs, curJh, hp⟩ = some p ∧ P p := by
  intro i
  obtain ⟨k, hk⟩ : ∃ k, k = vs.length - i := ⟨vs.length - i, rfl⟩
  induction k generalizing i with
  | zero =>
    intro hi curJh curLocs hOtherLoc hIter hOut hOtherJh hSize hStat hcont
    have hiEq : i = vs.length := by omega
    subst hiEq
    simp only [Nat.sub_self, Nat.mul_zero, Nat.zero_add]
    rw [show 3 + fRest = fRest + 1 + 1 + 1 by omega, hLoop]
    dsimp only [mapSuccessLoopInstrs, List.cons_append, List.nil_append]
    have hCurIt : curLocs iterSlot = .heapRef itAddr := by
      rw [hOtherLoc iterSlot hSlots.1, hLocIter]
    rw [runJvmResFast_aload hCurIt]
    rw [runJvmResFast_iterator_hasNext hIter]
    have hNotLt : ¬ (UInt32.ofNat vs.length).toNat < (vs.map fun v => (.ext (.res (.success v)) : JvmVal)).toArray.size := by
      simp [Jvm.ui32_ofNat_toNat_of_lt vs.length hlenLt]
    simp only [hNotLt, ↓reduceIte]
    rw [Jvm.runJvmResFast_ifeq_branch (hooks := mkRsHooks resolveProg (d + 1) subFuel) (by rfl)]
    rw [list_take_all] at hOut
    exact hcont curLocs curJh hOtherLoc hOut hOtherJh hSize hStat
  | succ k ih =>
    intro hi curJh curLocs hOtherLoc hIter hOut hOtherJh hSize hStat hcont
    have hiLt : i < vs.length := by omega
    have hiLt2 : i < 2 ^ 31 := by omega
    have hkEq : 20 * (vs.length - i) + 3 + fRest =
        (20 * k + 3 + fRest) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
          1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 := by omega
    rw [hkEq, hLoop]
    dsimp only [mapSuccessLoopInstrs, List.cons_append, List.nil_append]
    have hCurIt : curLocs iterSlot = .heapRef itAddr := by
      rw [hOtherLoc iterSlot hSlots.1, hLocIter]
    rw [runJvmResFast_aload hCurIt]
    rw [runJvmResFast_iterator_hasNext hIter]
    have hLt : (UInt32.ofNat i).toNat < (vs.map fun v => (.ext (.res (.success v)) : JvmVal)).toArray.size := by
      simp [Jvm.ui32_ofNat_toNat_of_lt i hiLt2, hiLt]
    simp only [hLt, ↓reduceIte]
    rw [Jvm.runJvmResFast_ifeq_fallthrough (hooks := mkRsHooks resolveProg (d + 1) subFuel) (by decide)]
    rw [runJvmResFast_aload hCurIt]
    rw [runJvmResFast_iterator_next hIter hLt]
    have hElemEq : (vs.map fun v => (.ext (.res (.success v)) : JvmVal)).toArray[(UInt32.ofNat i).toNat] =
        .ext (.res (.success vs[i])) := by
      simp [Jvm.ui32_ofNat_toNat_of_lt i hiLt2]
    rw [hElemEq]
    have hIterNext := iterBackedBy_next hIter
    have hOutAfterNext :
        ListBackedBy (curJh.set itAddr (.instance "java/util/Iterator"
          [("arr", .heapRef srcArrAddr), ("idx", .i32 (UInt32.ofNat i + 1))])) outListAddr outArrAddr
          (((vs.take i).map RsVal.toJvmVal)).toArray := by
      refine hOut.preserve ?_ ?_ (by omega)
      · exact hIterNext.2.2.2 outListAddr hNeOutListIt
      · exact hIterNext.2.2.2 outArrAddr hNeItOut.symm
    rw [runJvmResFast_astore]
    have hLoc1Out : (Jvm.setLocal curLocs tmp1 (.ext (.res (.success vs[i])))) outListSlot = .heapRef outListAddr := by
      have hne : outListSlot ≠ tmp1 := by simp_all [List.mem_cons]
      simp only [Jvm.setLocal, hne, ↓reduceIte]
      rw [hOtherLoc outListSlot hSlots.2.1, hLocOut]
    rw [runJvmResFast_aload hLoc1Out]
    rw [runJvmResFast_aload (v := .ext (.res (.success vs[i]))) (by simp [Jvm.setLocal])]
    rw [runJvmResFast_checkcast_res rfl]
    rw [runJvmResFast_astore]
    rw [runJvmResFast_astore]
    rw [runJvmResFast_iconst]
    rw [runJvmResFast_istore]
    rw [runJvmResFast_aload (v := .ext (.res (.success vs[i])))
      (by simp [Jvm.setLocal, hSlots.2.2.2.1, hSlots.2.2.1])]
    rw [runJvmResFast_success_getValue]
    rw [runJvmResFast_aload (v := .heapRef outListAddr) (by simp [Jvm.setLocal, hSlots.2.2.2.2])]
    rw [runJvmResFast_swap (hca := RsVal.toJvmVal_isCat2 vs[i]) (hcb := rfl)]
    rw [runJvmResFast_collection_add hOutAfterNext (href := RsVal.toJvmVal_isRef vs[i])]
    rw [runJvmResFast_pop]
    rw [Jvm.runJvmResFast_goto]
    have hAdd1 : UInt32.ofNat i + 1 = UInt32.ofNat (i + 1) := by simp [UInt32.ofNat_add]
    have hPackIter :
        IterBackedBy ((curJh.set itAddr (.instance "java/util/Iterator"
          [("arr", .heapRef srcArrAddr), ("idx", .i32 (UInt32.ofNat i + 1))])).set outArrAddr
          (.objArray "java/lang/Object"
            ((((vs.take i).map RsVal.toJvmVal)).toArray.push vs[i].toJvmVal)))
          itAddr srcArrAddr (UInt32.ofNat (i + 1))
          (vs.map fun v => (.ext (.res (.success v)) : JvmVal)).toArray := by
      have hAdd := listBackedBy_set_arr hOutAfterNext (elem := vs[i].toJvmVal)
      rw [← hAdd1]
      refine hIterNext.1.preserve ?_ ?_ (by omega)
      · exact hAdd.2.2.2 itAddr hNeItOut
      · exact hAdd.2.2.2 srcArrAddr hNeSrcOut
    have hTakeSucc :
        (((vs.take (i + 1)).map RsVal.toJvmVal)).toArray =
          (((vs.take i).map RsVal.toJvmVal)).toArray.push vs[i].toJvmVal := by
      rw [list_take_succ vs i hiLt, List.map_append]
      simp
    have hPackOut := listBackedBy_set_arr hOutAfterNext (elem := vs[i].toJvmVal)
    rw [← hTakeSucc] at hPackIter hPackOut ⊢
    rw [show 20 * k + 3 + fRest = 20 * (vs.length - (i + 1)) + 3 + fRest by omega]
    have hNextLocOther : ∀ s, s ∉ [tmp1, succSlot, tmpOutSlot, dummySlot] →
        Jvm.setLocal (Jvm.setLocal (Jvm.setLocal (Jvm.setLocal curLocs tmp1 (.ext (.res (.success vs[i]))))
          succSlot (.ext (.res (.success vs[i]))))
          tmpOutSlot (.heapRef outListAddr)) dummySlot (.i32 0) s = locs s := by
      intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hs
      rcases hs with ⟨hs1, hs2, hs3, hs4⟩
      simp [Jvm.setLocal, hs1, hs2, hs3, hs4, hOtherLoc s (by simp [hs1, hs2, hs3, hs4])]
    exact ih (i + 1) (by omega) (by omega) _ _
      hNextLocOther hPackIter hPackOut.1
      (fun a ha1 ha2 => by
        rw [hPackOut.2.2.2 a ha2, hIterNext.2.2.2 a ha1, hOtherJh a ha1 ha2])
      (by rw [hPackOut.2.1, hIterNext.2.1, hSize])
      (by rw [hPackOut.2.2.1, hIterNext.2.2.1, hStat])
      hcont

theorem runJvmResFast_dup {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    {v : JvmVal} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap RsExt} {hp : RsHeap} :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.dup :: rest) ⟨pc0, v :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, v :: v :: stk, locs, jh, hp⟩ :=
  runJvmResFast_of_step _ rfl (by simp) rfl rfl

theorem runJvmResFast_nop {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap RsExt} {hp : RsHeap} :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.nop :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, stk, locs, jh, hp⟩ :=
  runJvmResFast_of_step _ rfl (by simp) rfl rfl

theorem get?_some_lt {Ext : Type} {jh : Jvm.JvmHeap Ext} {a : Nat} {o : Jvm.HeapObj Ext}
    (h : jh.get? a = some o) : a < jh.objects.size := by
  simp only [Jvm.JvmHeap.get?] at h
  exact Nat.lt_of_not_le fun hge => by simp [Array.getElem?_eq_none hge] at h

theorem runJvmResFast_ldcStr {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    {s : String} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap RsExt} {hp : RsHeap} :
    Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.ldcStr s :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .str s :: stk, locs, jh, hp⟩ :=
  runJvmResFast_of_step _ rfl (by simp) rfl rfl

end ResourceState.KotlinJvmVerification
