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

import Lean
import JvmSemantics
import proofs.MacroCellEngineProofs
import proofs.HashLifeKernelProofs
import proofs.SemanticModelProofs

namespace Algorithm.JvmVerification

/-! ### Execution helpers -/

export Jvm (
  isBranchInstr BlockChunkRes BlockResChunkRes
  signExtend_and_mask coerceInI32_of_le compareUnsigned_slt' compareUnsigned_sle'
)

@[inline] def stepListAt (pc : Nat) (instrs : List JvmInstr) (st : JvmState) : Option JvmVal :=
  Jvm.stepListAt algHooks pc instrs st

@[inline] def stepListAtClean (pc : Nat) (instrs : List JvmInstr) (st : JvmState) : Option JvmVal :=
  Jvm.stepListAtClean algHooks pc instrs st

def runJvmResFast (fuel : Nat) (prog : List JvmInstr) (pc : Nat) (instrs : List JvmInstr) (st : JvmState) :
    Option (JvmVal × JvmState) :=
  Jvm.runJvmResFast algHooks fuel prog pc instrs st

def runJvmValFast (fuel : Nat) (prog : List JvmInstr) (pc : Nat) (instrs : List JvmInstr) (st : JvmState) :
    Option JvmVal :=
  Jvm.runJvmValFast algHooks fuel prog pc instrs st

def stepBlockChunk (n : Nat) (fuel : Nat) (pc : Nat) (instrs : List JvmInstr) (st : JvmState) :
    BlockChunkRes AlgExt AlgHeap :=
  Jvm.stepBlockChunk algHooks n fuel pc instrs st

def afterBlockChunk (r : BlockChunkRes AlgExt AlgHeap) (prog : List JvmInstr) : Option JvmVal :=
  Jvm.afterBlockChunk algHooks r prog

def evalBranchInstrCons (fuel1 : Nat) (prog : List JvmInstr) (pc : Nat) (instr : JvmInstr)
    (rest : List JvmInstr) (st : JvmState) : Option JvmVal :=
  Jvm.evalBranchInstrCons algHooks fuel1 prog pc instr rest st

def stepResBlockChunk (n : Nat) (fuel : Nat) (pc : Nat) (instrs : List JvmInstr) (st : JvmState) :
    BlockResChunkRes AlgExt AlgHeap :=
  Jvm.stepResBlockChunk algHooks n fuel pc instrs st

def afterResBlockChunk (r : BlockResChunkRes AlgExt AlgHeap) (prog : List JvmInstr) :
    Option (JvmVal × JvmState) :=
  Jvm.afterResBlockChunk algHooks r prog

def evalResBranchInstrCons (fuel1 : Nat) (prog : List JvmInstr) (pc : Nat) (instr : JvmInstr)
    (rest : List JvmInstr) (st : JvmState) : Option (JvmVal × JvmState) :=
  Jvm.evalResBranchInstrCons algHooks fuel1 prog pc instr rest st

theorem runJvm_nonbranch (fuel : Nat) (prog : List JvmInstr) (st : JvmState) (instr : JvmInstr)
    (hget : prog[st.pc]? = some instr) (hnbr : isBranchInstr instr = false) :
    runJvm (fuel + 1) prog st =
      match stepInstr instr st with
      | .inl (some st') => runJvm fuel prog st'
      | .inl none => none
      | .inr res => res := by
  dsimp only [runJvm, stepInstr]
  rw [Jvm.runJvm_nonbranch algHooks fuel prog st instr hget hnbr]
  cases Jvm.stepInstr algHooks instr st with
  | inl o => cases o <;> rfl
  | inr res => rfl

theorem runJvm_of_stepListAt (prog instrs : List JvmInstr)
    (fuel : Nat) (st : JvmState) (v : JvmVal)
    (hdrop : prog.drop st.pc = instrs) (hfuel : instrs.length ≤ fuel)
    (hstep : stepListAt st.pc instrs st = some v) :
    runJvm fuel prog st = some v :=
  Jvm.runJvm_of_stepListAt algHooks prog instrs fuel st v hdrop hfuel hstep

theorem stepListAt_of_clean (pc : Nat) (instrs : List JvmInstr) (st : JvmState) (v : JvmVal)
    (h : stepListAtClean pc instrs st = some v) :
    stepListAt pc instrs st = some v :=
  Jvm.stepListAt_of_clean algHooks pc instrs st v h

theorem runJvm_of_stepListAtClean (prog instrs : List JvmInstr)
    (fuel : Nat) (st : JvmState) (v : JvmVal)
    (hdrop : prog.drop st.pc = instrs) (hfuel : instrs.length ≤ fuel)
    (hstep : stepListAtClean st.pc instrs st = some v) :
    runJvm fuel prog st = some v :=
  Jvm.runJvm_of_stepListAtClean algHooks prog instrs fuel st v hdrop hfuel hstep

theorem runJvmRes_nonbranch (fuel : Nat) (prog : List JvmInstr) (st : JvmState) (instr : JvmInstr)
    (hget : prog[st.pc]? = some instr) (hnbr : isBranchInstr instr = false) :
    runJvmRes (fuel + 1) prog st =
      match stepInstr instr st with
      | .inl (some st') => runJvmRes fuel prog st'
      | .inl none => none
      | .inr (some res) => some (res, st)
      | .inr none => none := by
  dsimp only [runJvmRes, stepInstr]
  rw [Jvm.runJvmRes_nonbranch algHooks fuel prog st instr hget hnbr]
  cases Jvm.stepInstr algHooks instr st with
  | inl o => cases o <;> rfl
  | inr o => cases o <;> rfl

theorem runJvm_eq_runJvmRes (fuel : Nat) (prog : List JvmInstr) (st : JvmState) :
    runJvm fuel prog st = (runJvmRes fuel prog st).map Prod.fst :=
  Jvm.runJvm_eq_runJvmRes algHooks
    Jvm.defaultIteVal_eq_if (fun _ _ _ => Jvm.defaultIteVal_eq_if _ _ _)
    (fun _ _ _ => Jvm.defaultIteVal_eq_if _ _ _) fuel prog st

theorem runJvmRes_of_runJvmResFast (fuel : Nat) (prog : List JvmInstr) (pc : Nat) (instrs : List JvmInstr)
    (st : JvmState) (res : JvmVal × JvmState)
    (hpc : st.pc = pc) (hdrop : prog.drop pc = instrs)
    (hfast : runJvmResFast fuel prog pc instrs st = some res) :
    runJvmRes fuel prog st = some res :=
  Jvm.runJvmRes_of_runJvmResFast algHooks fuel prog pc instrs st res hpc hdrop hfast

theorem runJvm_of_runJvmValFast (fuel : Nat) (prog : List JvmInstr) (st : JvmState) (v : JvmVal)
    (hfast : runJvmValFast fuel prog st.pc (prog.drop st.pc) st = some v) :
    runJvm fuel prog st = some v :=
  Jvm.runJvm_of_runJvmValFast algHooks
    Jvm.defaultIteVal_eq_if (fun _ _ _ => Jvm.defaultIteVal_eq_if _ _ _)
    (fun _ _ _ => Jvm.defaultIteVal_eq_if _ _ _) fuel prog st v hfast

theorem runJvm_of_runJvmValFast0 (fuel : Nat) (prog : List JvmInstr) (st : JvmState) (v : JvmVal)
    (hpc : st.pc = 0)
    (hfast : runJvmValFast fuel prog 0 prog st = some v) :
    runJvm fuel prog st = some v :=
  Jvm.runJvm_of_runJvmValFast0 algHooks
    Jvm.defaultIteVal_eq_if (fun _ _ _ => Jvm.defaultIteVal_eq_if _ _ _)
    (fun _ _ _ => Jvm.defaultIteVal_eq_if _ _ _) fuel prog st v hpc hfast

theorem runJvmRes_of_runJvmResFast0 (fuel : Nat) (prog : List JvmInstr) (st : JvmState)
    (res : JvmVal × JvmState) (hpc : st.pc = 0)
    (hfast : runJvmResFast fuel prog 0 prog st = some res) :
    runJvmRes fuel prog st = some res :=
  Jvm.runJvmRes_of_runJvmResFast0 algHooks fuel prog st res hpc hfast

theorem runJvmRes_map_of_runJvmResFast0 {α : Type} (f : JvmVal × JvmState → α)
    (fuel : Nat) (prog : List JvmInstr) (st : JvmState) (y : α)
    (hpc : st.pc = 0)
    (hfast : (runJvmResFast fuel prog 0 prog st).map f = some y) :
    (runJvmRes fuel prog st).map f = some y :=
  Jvm.runJvmRes_map_of_runJvmResFast0 algHooks f fuel prog st y hpc hfast

theorem runJvmValFast_stepBlockChunk (maxSteps fuel : Nat) (prog : List JvmInstr) (pc : Nat)
    (instrs : List JvmInstr) (st : JvmState) :
    runJvmValFast fuel prog pc instrs st = afterBlockChunk (stepBlockChunk maxSteps fuel pc instrs st) prog :=
  Jvm.runJvmValFast_stepBlockChunk algHooks maxSteps fuel prog pc instrs st

theorem runJvmValFast_at_branch_cons (f1 : Nat) (prog : List JvmInstr) (pc : Nat)
    (instr : JvmInstr) (rest : List JvmInstr) (st : JvmState) (hbr : isBranchInstr instr = true) :
    runJvmValFast (f1 + 1) prog pc (instr :: rest) st = evalBranchInstrCons f1 prog pc instr rest st :=
  Jvm.runJvmValFast_at_branch_cons algHooks f1 prog pc instr rest st hbr

theorem runJvmResFast_stepBlockChunk (maxSteps fuel : Nat) (prog : List JvmInstr) (pc : Nat)
    (instrs : List JvmInstr) (st : JvmState) :
    runJvmResFast fuel prog pc instrs st = afterResBlockChunk (stepResBlockChunk maxSteps fuel pc instrs st) prog :=
  Jvm.runJvmResFast_stepBlockChunk algHooks maxSteps fuel prog pc instrs st

theorem runJvmResFast_at_branch_cons (f1 : Nat) (prog : List JvmInstr) (pc : Nat)
    (instr : JvmInstr) (rest : List JvmInstr) (st : JvmState) (hbr : isBranchInstr instr = true) :
    runJvmResFast (f1 + 1) prog pc (instr :: rest) st = evalResBranchInstrCons f1 prog pc instr rest st :=
  Jvm.runJvmResFast_at_branch_cons algHooks f1 prog pc instr rest st hbr

theorem runJvmValFast_step_nonbranch (f1 : Nat) (prog : List JvmInstr) (pc : Nat) (instr : JvmInstr)
    (rest : List JvmInstr) (st : JvmState) (hbr : isBranchInstr instr = false)
    (hno : ¬(instr = .i2l ∧ ∃ rest', rest = .lconst 4294967295 :: .land :: rest')) :
    runJvmValFast (f1 + 1) prog pc (instr :: rest) st =
      match stepInstr instr { st with pc := pc } with
      | .inl (some st') =>
        if st'.pc = pc + 1 then runJvmValFast f1 prog (pc + 1) rest st'
        else runJvmValFast f1 prog st'.pc (prog.drop st'.pc) st'
      | .inl none => none
      | .inr (some v) => some v
      | .inr none => none := by
  dsimp only [runJvmValFast, stepInstr]
  rw [Jvm.runJvmValFast_step_nonbranch algHooks f1 prog pc instr rest st hbr hno]
  cases Jvm.stepInstr algHooks instr { st with pc := pc } with
  | inl o => cases o <;> rfl
  | inr o => cases o <;> rfl

theorem runJvmResFast_step_nonbranch (f1 : Nat) (prog : List JvmInstr) (pc : Nat)
    (instr : JvmInstr) (rest : List JvmInstr) (st : JvmState) (hbr : isBranchInstr instr = false)
    (hno : ¬(instr = .i2l ∧ ∃ r', rest = .lconst 4294967295 :: .land :: r')) :
    runJvmResFast (f1 + 1) prog pc (instr :: rest) st =
      match stepInstr instr { st with pc := pc } with
      | .inl (some st') =>
        if st'.pc = pc + 1 then runJvmResFast f1 prog (pc + 1) rest st'
        else runJvmResFast f1 prog st'.pc (prog.drop st'.pc) st'
      | .inl none => none
      | .inr (some v) => some (v, { st with pc := pc })
      | .inr none => none := by
  dsimp only [runJvmResFast, stepInstr]
  rw [Jvm.runJvmResFast_step_nonbranch algHooks f1 prog pc instr rest st hbr hno]
  cases Jvm.stepInstr algHooks instr { st with pc := pc } with
  | inl o => cases o <;> rfl
  | inr o => cases o <;> rfl

def whnfUnfoldInitJvmState (s' : Lean.Expr) : Lean.MetaM Lean.Expr := do
  if s'.isAppOf ``initJvmState || s'.isAppOf ``Jvm.initJvmState then
    let u1 ← match ← Lean.Meta.unfoldDefinition? s' with | some u => pure u | none => pure s'
    let u2 ← if u1.isAppOf ``Jvm.initJvmState then
        match ← Lean.Meta.unfoldDefinition? u1 with | some u => pure u | none => pure u1
      else pure u1
    Lean.Meta.whnfCore u2
  else
    Lean.Meta.whnfCore s'

partial def reduceStateProj (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let e := e.consumeMData
  if let .proj ``Jvm.JvmState i s := e then
    let s' ← reduceStateProj s
    if s'.isAppOfArity ``Jvm.JvmState.mk 7 then
      return ← reduceStateProj (s'.getArg! (2 + i))
    let sw ← whnfUnfoldInitJvmState s'
    if sw.isAppOfArity ``Jvm.JvmState.mk 7 then
      return ← reduceStateProj (sw.getArg! (2 + i))
    return .proj ``Jvm.JvmState i s'
  if let .proj ``AlgHeap i h := e then
    let h' ← reduceStateProj h
    if h'.isAppOfArity ``AlgHeap.mk 3 then
      return ← reduceStateProj (h'.getArg! i)
    return .proj ``AlgHeap i h'
  if let some n := e.getAppFn.constName? then
    if e.getAppNumArgs == 3 &&
       (n == ``Jvm.JvmState.pc || n == ``Jvm.JvmState.stack ||
        n == ``Jvm.JvmState.locals || n == ``Jvm.JvmState.jvmHeap || n == ``Jvm.JvmState.heap) then
      let args := e.getAppArgs
      let i := if n == ``Jvm.JvmState.pc then 0
        else if n == ``Jvm.JvmState.stack then 1
        else if n == ``Jvm.JvmState.locals then 2
        else if n == ``Jvm.JvmState.jvmHeap then 3
        else 4
      let s' ← reduceStateProj args[2]!
      if s'.isAppOfArity ``Jvm.JvmState.mk 7 then
        return ← reduceStateProj (s'.getArg! (2 + i))
      let sw ← whnfUnfoldInitJvmState s'
      if sw.isAppOfArity ``Jvm.JvmState.mk 7 then
        return ← reduceStateProj (sw.getArg! (2 + i))
      return Lean.mkAppN e.getAppFn #[args[0]!, args[1]!, s']
    if e.getAppNumArgs == 1 &&
       (n == ``AlgHeap.arenas || n == ``AlgHeap.u64Arrays || n == ``AlgHeap.asciiArrays) then
      let i := if n == ``AlgHeap.arenas then 0
        else if n == ``AlgHeap.u64Arrays then 1
        else 2
      let h' ← reduceStateProj e.appArg!
      if h'.isAppOfArity ``AlgHeap.mk 3 then
        return ← reduceStateProj (h'.getArg! i)
      return Lean.mkApp e.getAppFn h'
    if n == ``AlgHeap.mk && e.getAppNumArgs == 3 then
      let args := e.getAppArgs
      return Lean.mkApp3 e.getAppFn
        (← reduceStateProj args[0]!) (← reduceStateProj args[1]!) (← reduceStateProj args[2]!)
    if n == ``Jvm.setLocal && e.getAppNumArgs == 4 then
      let args := e.getAppArgs
      return Lean.mkApp4 e.getAppFn args[0]! (← reduceStateProj args[1]!) args[2]! args[3]!
  return e

partial def normJvmExpr (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let e ← Lean.Meta.whnf e
  let fn := e.getAppFn
  let args := e.getAppArgs
  match fn.constName? with
  | some n =>
    if n == ``Sum.inl || n == ``Sum.inr || n == ``Prod.mk ||
       n == ``Option.some || n == ``List.cons then
      let args' ← args.mapM normJvmExpr
      return Lean.mkAppN fn args'
    else if n == ``Jvm.BlockChunkRes.done || n == ``Jvm.BlockResChunkRes.done then
      let res' ← normJvmExpr args[2]!
      return Lean.mkAppN fn #[args[0]!, args[1]!, res']
    else if n == ``Jvm.BlockChunkRes.cont || n == ``Jvm.BlockResChunkRes.cont then
      let f' ← normJvmExpr args[2]!
      let pc' ← normJvmExpr args[3]!
      let st' ← normJvmExpr args[5]!
      return Lean.mkAppN fn #[args[0]!, args[1]!, f', pc', args[4]!, st']
    else if n == ``Jvm.BlockChunkRes.jump || n == ``Jvm.BlockResChunkRes.jump then
      let f' ← normJvmExpr args[2]!
      let st' ← normJvmExpr args[3]!
      return Lean.mkAppN fn #[args[0]!, args[1]!, f', st']
    else if n == ``Jvm.JvmState.mk then
      let pc' ← normJvmExpr args[2]!
      let stk' ← normJvmExpr args[3]!
      let locs' ← reduceStateProj args[4]!
      let jh' ← reduceStateProj args[5]!
      let heap' ← reduceStateProj args[6]!
      return Lean.mkAppN fn #[args[0]!, args[1]!, pc', stk', locs', jh', heap']
    else if n == ``Bool.rec then
      let args' ← args.mapM fun a => do
        let aw ← Lean.Meta.whnf a
        if aw.isLambda then
          Lean.Meta.lambdaTelescope aw fun xs body => do
            let body' ← normJvmExpr body
            Lean.Meta.mkLambdaFVars xs body'
        else return a
      return Lean.mkAppN fn args'
    else
      return e
  | none => return e

elab "jvm_whnf_blk" : conv => do
  let lhs ← Lean.Elab.Tactic.Conv.getLhs
  let lhs' ← normJvmExpr lhs
  Lean.Elab.Tactic.Conv.changeLhs lhs'

partial def evalNatLit? (e : Lean.Expr) : Lean.MetaM (Option Nat) := do
  if e.hasFVar || e.hasLooseBVars then return none
  let e ← Lean.Meta.whnf e
  if let some n := e.rawNatLit? then return some n
  if e.isConstOf ``Nat.zero then return some 0
  if e.isAppOfArity ``Nat.succ 1 then
    return (← evalNatLit? e.appArg!).map (· + 1)
  return none

def foldInitLocals (init slots : Lean.Expr) : Lean.Expr := Id.run do
  let mut acc := init
  let mut cur := slots
  let extTy := Lean.mkConst ``AlgExt
  while cur.isAppOfArity ``List.cons 3 do
    let hd := cur.getArg! 1
    let tl := cur.getArg! 2
    if hd.isAppOfArity ``Prod.mk 4 then
      acc := Lean.mkApp4 (Lean.mkConst ``Jvm.setLocal) extTy acc (hd.getArg! 2) (hd.getArg! 3)
      cur := tl
    else
      break
  return acc

partial def normJvmLocalsExpr (e : Lean.Expr) : Lean.MetaM Lean.Expr :=
  Lean.Meta.transform e
    (pre := fun sub => do
      if sub.isAppOfArity ``List.cons 3 && (sub.getArg! 0).isConstOf ``Jvm.JvmInstr then
        return .done sub
      else if sub.isAppOfArity ``List.nil 1 && (sub.getArg! 0).isConstOf ``Jvm.JvmInstr then
        return .done sub
      else if sub.isAppOfArity ``Jvm.setLocal 5 then
        let args := sub.getAppArgs
        if let (some nk, some nidx) := (← evalNatLit? args[2]!, ← evalNatLit? args[4]!) then
          if nidx == nk then
            return .visit args[3]!
          else
            return .visit (Lean.mkApp args[1]! args[4]!)
        return .continue
      else if sub.isAppOfArity ``List.foldl 6 then
        let args := sub.getAppArgs
        if Option.isSome (args[2]!.find? (·.isConstOf ``Jvm.setLocal)) then
          if let some _ ← evalNatLit? args[5]! then
            if args[4]!.isAppOfArity ``List.cons 3 || args[4]!.isAppOfArity ``List.nil 1 then
              return .visit (Lean.mkApp (foldInitLocals args[3]! args[4]!) args[5]!)
        return .continue
      else if sub.isProj then
        let sub' ← reduceStateProj sub
        if sub' != sub then return .visit sub'
        return .continue
      else if sub.isAppOfArity ``Jvm.JvmState.locals 3 || sub.isAppOfArity ``Jvm.JvmState.heap 3 ||
              sub.isAppOfArity ``AlgHeap.arenas 1 || sub.isAppOfArity ``AlgHeap.u64Arrays 1 ||
              sub.isAppOfArity ``AlgHeap.asciiArrays 1 then
        let sub' ← reduceStateProj sub
        if sub' != sub then return .visit sub'
        return .continue
      else if sub.isApp && (sub.appFn!.isProj || sub.appFn!.isAppOfArity ``Jvm.JvmState.locals 3) then
        let locs' ← reduceStateProj sub.appFn!
        if locs' != sub.appFn! then
          return .visit (Lean.mkApp locs' sub.appArg!)
        return .continue
      else if sub.isAppOfArity ``Jvm.JvmState.locals 4 then
        let s := sub.appFn!.getArg! 2
        let idx := sub.appArg!
        if let some _ ← evalNatLit? idx then
          let sw ← Lean.Meta.whnf s
          if sw.isAppOfArity ``Jvm.JvmState.mk 7 then
            let locs := sw.getArg! 4
            if locs.isAppOfArity ``List.foldl 5 then
              let folded := foldInitLocals (locs.getArg! 3) (locs.getArg! 4)
              return .visit (Lean.mkApp folded idx)
            else
              let next := Lean.mkApp locs idx
              if next != sub then return .visit next else return .continue
          else return .continue
        else return .continue
      else if sub.isApp && sub.appFn!.isLambda then
        let body := sub.appFn!.bindingBody!
        if !body.hasLooseBVars && !sub.appArg!.hasFVar && !sub.appArg!.hasLooseBVars then
          if let some _ ← evalNatLit? sub.appArg! then
            return .visit body
        return .continue
      else
        return .continue)
    (post := fun sub => do
      if sub.isAppOfArity ``Jvm.JvmVal.asI32 2 then
        let a := sub.appArg!
        if a.isAppOfArity ``Jvm.JvmVal.i32 2 then
          return .done (a.getArg! 1)
        else if a.isAppOfArity ``Jvm.JvmVal.i64 2 then
          return .done (Lean.mkApp (Lean.mkConst ``UInt64.toUInt32) (a.getArg! 1))
        return .done sub
      else if sub.isAppOfArity ``Jvm.JvmVal.asI64 2 then
        let a := sub.appArg!
        if a.isAppOfArity ``Jvm.JvmVal.i64 2 then
          return .done (a.getArg! 1)
        else if a.isAppOfArity ``Jvm.JvmVal.i32 2 then
          return .done (Lean.mkApp (Lean.mkConst ``UInt32.toUInt64) (a.getArg! 1))
        return .done sub
      else if sub.isAppOfArity ``Jvm.JvmVal.isNull 2 then
        let a := sub.appArg!
        if a.isAppOfArity ``Jvm.JvmVal.null 1 then
          return .done (Lean.mkConst ``Bool.true)
        return .done sub
      else
        return .done sub)

elab "norm_jvm_locals" : conv => do
  let lhs ← Lean.Elab.Tactic.Conv.getLhs
  let lhs' ← normJvmLocalsExpr lhs
  Lean.Elab.Tactic.Conv.changeLhs lhs'

@[simp] theorem algHooks_checkInstanceOf : algHooks.checkInstanceOf = checkInstanceOf := rfl

@[simp] theorem checkInstanceOf_level4_level4 (h : UInt32) (nw ne sw se : UInt64) :
    checkInstanceOf "com/alexvanyo/composelife/model/MacroCell$Level4Node"
      (.ext (.mc (.level4Node h nw ne sw se))) = true := rfl

@[simp] theorem checkInstanceOf_level4_cell (h : UInt32) (nw ne sw se : MacroCell) :
    checkInstanceOf "com/alexvanyo/composelife/model/MacroCell$Level4Node"
      (.ext (.mc (.cellNode h nw ne sw se))) = false := rfl

@[simp] theorem checkInstanceOf_cell_level4 (h : UInt32) (nw ne sw se : UInt64) :
    checkInstanceOf "com/alexvanyo/composelife/model/MacroCell$CellNode"
      (.ext (.mc (.level4Node h nw ne sw se))) = false := rfl

@[simp] theorem checkInstanceOf_cell_cell (h : UInt32) (nw ne sw se : MacroCell) :
    checkInstanceOf "com/alexvanyo/composelife/model/MacroCell$CellNode"
      (.ext (.mc (.cellNode h nw ne sw se))) = true := rfl

theorem ui32_beq_0_0 : ((0 : UInt32) == 0) = true := rfl
theorem ui32_beq_1_0 : ((1 : UInt32) == 0) = false := rfl

partial def fastDropListEq (e : Lean.Expr) (n : Nat) : Lean.MetaM (Lean.Expr × Lean.Expr) := do
  let ty := Lean.mkConst ``Jvm.JvmInstr
  if n == 0 then
    let lhs := Lean.mkAppN (Lean.mkConst ``List.drop [Lean.Level.zero]) #[ty, Lean.toExpr 0, e]
    return (e, ← Lean.Meta.mkExpectedTypeHint (← Lean.Meta.mkEqRefl e) (← Lean.Meta.mkEq lhs e))
  let mut cur := e
  let mut remaining := n
  let step := 40
  let mut accEq : Option Lean.Expr := none
  let mut dropped : Nat := 0
  while remaining > 0 do
    let k := min remaining step
    let curWhnf ← Lean.Meta.whnf cur
    let mut tail := curWhnf
    for _ in [:k] do
      let t ← Lean.Meta.whnf tail
      if t.isAppOfArity ``List.cons 3 then
        tail := t.getArg! 2
      else
        tail := t
        break
    let lhsStep := Lean.mkAppN (Lean.mkConst ``List.drop [Lean.Level.zero]) #[ty, Lean.toExpr k, curWhnf]
    let stepEq ← Lean.Meta.mkExpectedTypeHint (← Lean.Meta.mkEqRefl tail) (← Lean.Meta.mkEq lhsStep tail)
    match accEq with
    | none =>
      let origLhs := Lean.mkAppN (Lean.mkConst ``List.drop [Lean.Level.zero]) #[ty, Lean.toExpr k, e]
      let eq0 ← Lean.Meta.mkExpectedTypeHint stepEq (← Lean.Meta.mkEq origLhs tail)
      accEq := some eq0
      cur := tail
      dropped := k
    | some prevEq =>
      let fnDropK := Lean.mkApp2 (Lean.mkConst ``List.drop [Lean.Level.zero]) ty (Lean.toExpr k)
      let ap ← Lean.Meta.mkCongrArg fnDropK prevEq
      let eqCurWhnf ← Lean.Meta.mkEqTrans ap stepEq
      let ddrop := Lean.mkAppN (Lean.mkConst ``List.drop_drop [Lean.Level.zero])
        #[ty, Lean.toExpr k, Lean.toExpr dropped, e]
      let symD ← Lean.Meta.mkEqSymm ddrop
      let ap1 ← Lean.Meta.mkEqTrans symD eqCurWhnf
      let newDropped := dropped + k
      let sumEq := Lean.mkAppN (Lean.mkConst ``List.drop [Lean.Level.zero]) #[ty, Lean.toExpr newDropped, e]
      let ap2 ← Lean.Meta.mkExpectedTypeHint ap1 (← Lean.Meta.mkEq sumEq tail)
      accEq := some ap2
      cur := tail
      dropped := newDropped
    remaining := remaining - k
  return (cur, accEq.get!)

theorem option_map_ite {α β : Type} (f : α → β) (c : Prop) [Decidable c] (t e : Option α) :
    (if c then t else e).map f = if c then t.map f else e.map f := by
  split <;> rfl

partial def normRunTail (b : Lean.Expr) : Lean.MetaM (Lean.Expr × Option Lean.Expr) := do
  if b.isAppOfArity ``Option.map 4 then
    let ma := b.getAppArgs
    let (inner', eqOpt) ← normRunTail ma[3]!
    let newB := Lean.mkAppN b.getAppFn #[ma[0]!, ma[1]!, ma[2]!, inner']
    match eqOpt with
    | none => return (newB, none)
    | some eqP =>
      let pf3 := Lean.mkAppN b.getAppFn #[ma[0]!, ma[1]!, ma[2]!]
      return (newB, some (← Lean.Meta.mkCongrArg pf3 eqP))
  else if b.isAppOfArity ``runJvmValFast 5 || b.isAppOfArity ``runJvmResFast 5 then
    let ba := b.getAppArgs
    let fuel' ← Lean.Meta.whnf ba[0]!
    let pc' ← Lean.Meta.whnf ba[2]!
    let st' ← normJvmExpr ba[4]!
    let mut instrs' := ba[3]!
    let mut instrsEq : Option Lean.Expr := none
    if instrs'.isAppOfArity ``List.drop 3 then
      let da := instrs'.getAppArgs
      if let some n ← evalNatLit? da[1]! then
        let (rhs, eqP) ← fastDropListEq da[2]! n
        instrs' := rhs
        instrsEq := some eqP
    let newB := Lean.mkAppN b.getAppFn #[fuel', ba[1]!, pc', instrs', st']
    match instrsEq with
    | none => return (newB, none)
    | some eqP =>
      let lam := Lean.mkLambda `x .default (← Lean.Meta.inferType ba[3]!)
        (Lean.mkAppN b.getAppFn #[fuel', ba[1]!, pc', Lean.Expr.bvar 0, st'])
      let fullEq ← Lean.Meta.mkCongrArg lam eqP
      let prefixB := Lean.mkAppN b.getAppFn #[fuel', ba[1]!, pc', ba[3]!, st']
      let defEq ← Lean.Meta.mkExpectedTypeHint (← Lean.Meta.mkEqRefl b) (← Lean.Meta.mkEq b prefixB)
      return (newB, some (← Lean.Meta.mkEqTrans defEq fullEq))
  else return (b, none)

elab "jvm_whnf_run_args" : conv => do
  let e ← Lean.Elab.Tactic.Conv.getLhs
  let eTop := if e.isAppOfArity ``Option.map 4 then e else e
  if eTop.isAppOfArity ``Option.map 4 ||
     eTop.isAppOfArity ``runJvmValFast 5 || eTop.isAppOfArity ``runJvmResFast 5 then
    let (e', eqOpt) ← normRunTail eTop
    match eqOpt with
    | some eqP => Lean.Elab.Tactic.Conv.updateLhs e' eqP
    | none => Lean.Elab.Tactic.Conv.changeLhs e'
  else if e.isAppOfArity ``ite 5 then
    let args := e.getAppArgs
    let (t', teqOpt) ← normRunTail args[3]!
    let (f', feqOpt) ← normRunTail args[4]!
    let newE := Lean.mkAppN e.getAppFn #[args[0]!, args[1]!, args[2]!, t', f']
    if teqOpt.isNone && feqOpt.isNone then
      Lean.Elab.Tactic.Conv.changeLhs newE
    else
      let teq ← match teqOpt with
        | some p => pure p
        | none => Lean.Meta.mkExpectedTypeHint (← Lean.Meta.mkEqRefl t') (← Lean.Meta.mkEq args[3]! t')
      let feq ← match feqOpt with
        | some p => pure p
        | none => Lean.Meta.mkExpectedTypeHint (← Lean.Meta.mkEqRefl f') (← Lean.Meta.mkEq args[4]! f')
      let pf3 := Lean.mkAppN e.getAppFn #[args[0]!, args[1]!, args[2]!]
      let c1 ← Lean.Meta.mkCongrArg pf3 teq
      let c2 ← Lean.Meta.mkCongr c1 feq
      Lean.Elab.Tactic.Conv.updateLhs newE c2

def unwrapRunLhs (e : Lean.Expr) : Lean.Expr × Bool :=
  let e := e.consumeMData
  if e.isAppOfArity ``Option.map 4 then
    ((e.getArg! 3).consumeMData, true)
  else
    (e, false)

def isRunJvmAtNonBranch : Lean.Elab.Tactic.TacticM Bool := do
  let tgt := (← Lean.Elab.Tactic.getMainTarget).consumeMData
  let some (_, lhs, _) := tgt.eq? | return false
  let (inner, _) := unwrapRunLhs lhs
  if inner.isAppOfArity ``runJvmValFast 5 || inner.isAppOfArity ``runJvmResFast 5 then
    let instrs ← Lean.Meta.whnf (inner.getArg! 3)
    if instrs.isAppOfArity ``List.cons 3 then
      let instr := instrs.getArg! 1
      let br ← Lean.Meta.whnf (Lean.mkApp (Lean.mkConst ``isBranchInstr) instr)
      return br.isConstOf ``Bool.false
  return false

def isRunJvmAtForwardGoto : Lean.Elab.Tactic.TacticM Bool := do
  let tgt := (← Lean.Elab.Tactic.getMainTarget).consumeMData
  let some (_, lhs, _) := tgt.eq? | return false
  let (inner, _) := unwrapRunLhs lhs
  if inner.isAppOfArity ``runJvmValFast 5 || inner.isAppOfArity ``runJvmResFast 5 then
    let instrs ← Lean.Meta.whnf (inner.getArg! 3)
    if instrs.isAppOfArity ``List.cons 3 then
      let instr ← Lean.Meta.whnf (instrs.getArg! 1)
      if instr.isAppOfArity ``Jvm.JvmInstr.goto 1 then
        if let (some pcVal, some tgtVal) := (← evalNatLit? (inner.getArg! 2), ← evalNatLit? (instr.getArg! 0)) then
          return pcVal < tgtVal
  return false

theorem afterBlockChunk_cont (f pc : Nat) (is : List JvmInstr) (st : JvmState) (prog : List JvmInstr) :
    afterBlockChunk (.cont f pc is st) prog = runJvmValFast f prog pc is st := rfl

theorem afterBlockChunk_jump (f pc : Nat) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes)
    (prog : List JvmInstr) :
    afterBlockChunk (.jump f ⟨pc, stk, locs, jh, ⟨ar, u64, asc⟩⟩) prog =
      runJvmValFast f prog pc (prog.drop pc) ⟨pc, stk, locs, jh, ⟨ar, u64, asc⟩⟩ := rfl

theorem afterBlockChunk_done (res : Option JvmVal) (prog : List JvmInstr) :
    afterBlockChunk (.done res) prog = res := rfl

theorem afterResBlockChunk_cont (f pc : Nat) (is : List JvmInstr) (st : JvmState) (prog : List JvmInstr) :
    afterResBlockChunk (.cont f pc is st) prog = runJvmResFast f prog pc is st := rfl

theorem afterResBlockChunk_jump (f pc : Nat) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes)
    (prog : List JvmInstr) :
    afterResBlockChunk (.jump f ⟨pc, stk, locs, jh, ⟨ar, u64, asc⟩⟩) prog =
      runJvmResFast f prog pc (prog.drop pc) ⟨pc, stk, locs, jh, ⟨ar, u64, asc⟩⟩ := rfl

theorem afterResBlockChunk_done (res : Option (JvmVal × JvmState)) (prog : List JvmInstr) :
    afterResBlockChunk (.done res) prog = res := rfl

private theorem option_map_some' {α β : Type} (f : α → β) (x : α) :
    Option.map f (some x) = some (f x) := rfl

private theorem option_map_none' {α β : Type} (f : α → β) :
    Option.map f none = none := rfl

private theorem evalBranchInstrCons_ifeq (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalBranchInstrCons f1 prog pc (.ifeq target) rest ⟨pc0, v :: s, locs, jh, ⟨ar, u64, asc⟩⟩ =
      if v.asI32 == 0 then runJvmValFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, ⟨ar, u64, asc⟩⟩
      else runJvmValFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, ⟨ar, u64, asc⟩⟩ := rfl

private theorem evalBranchInstrCons_ifne (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalBranchInstrCons f1 prog pc (.ifne target) rest ⟨pc0, v :: s, locs, jh, ⟨ar, u64, asc⟩⟩ =
      if !(v.asI32 == 0) then runJvmValFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, ⟨ar, u64, asc⟩⟩
      else runJvmValFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, ⟨ar, u64, asc⟩⟩ := rfl

private theorem evalBranchInstrCons_iflt (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalBranchInstrCons f1 prog pc (.iflt target) rest ⟨pc0, v :: s, locs, jh, ⟨ar, u64, asc⟩⟩ =
      if v.asI32.toBitVec.slt 0#32 then
        runJvmValFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, ⟨ar, u64, asc⟩⟩
      else runJvmValFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, ⟨ar, u64, asc⟩⟩ := rfl

private theorem evalBranchInstrCons_ifle (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalBranchInstrCons f1 prog pc (.ifle target) rest ⟨pc0, v :: s, locs, jh, ⟨ar, u64, asc⟩⟩ =
      if v.asI32.toBitVec.sle 0#32 then
        runJvmValFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, ⟨ar, u64, asc⟩⟩
      else runJvmValFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, ⟨ar, u64, asc⟩⟩ := rfl

private theorem evalBranchInstrCons_ifgt (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalBranchInstrCons f1 prog pc (.ifgt target) rest ⟨pc0, v :: s, locs, jh, ⟨ar, u64, asc⟩⟩ =
      if (0#32).slt v.asI32.toBitVec then
        runJvmValFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, ⟨ar, u64, asc⟩⟩
      else runJvmValFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, ⟨ar, u64, asc⟩⟩ := rfl

private theorem evalBranchInstrCons_ifge (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalBranchInstrCons f1 prog pc (.ifge target) rest ⟨pc0, v :: s, locs, jh, ⟨ar, u64, asc⟩⟩ =
      if (0#32).sle v.asI32.toBitVec then
        runJvmValFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, ⟨ar, u64, asc⟩⟩
      else runJvmValFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, ⟨ar, u64, asc⟩⟩ := rfl

private theorem evalBranchInstrCons_ifnull (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalBranchInstrCons f1 prog pc (.ifnull target) rest ⟨pc0, v :: s, locs, jh, ⟨ar, u64, asc⟩⟩ =
      if v.isNull then runJvmValFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, ⟨ar, u64, asc⟩⟩
      else runJvmValFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, ⟨ar, u64, asc⟩⟩ := rfl

private theorem evalBranchInstrCons_ifnonnull (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalBranchInstrCons f1 prog pc (.ifnonnull target) rest ⟨pc0, v :: s, locs, jh, ⟨ar, u64, asc⟩⟩ =
      if !v.isNull then runJvmValFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, ⟨ar, u64, asc⟩⟩
      else runJvmValFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, ⟨ar, u64, asc⟩⟩ := rfl

private theorem evalBranchInstrCons_if_icmpeq (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (b a : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalBranchInstrCons f1 prog pc (.if_icmpeq target) rest ⟨pc0, b :: a :: s, locs, jh, ⟨ar, u64, asc⟩⟩ =
      if a.asI32 == b.asI32 then runJvmValFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, ⟨ar, u64, asc⟩⟩
      else runJvmValFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, ⟨ar, u64, asc⟩⟩ := rfl

private theorem evalBranchInstrCons_if_icmpne (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (b a : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalBranchInstrCons f1 prog pc (.if_icmpne target) rest ⟨pc0, b :: a :: s, locs, jh, ⟨ar, u64, asc⟩⟩ =
      if !(a.asI32 == b.asI32) then runJvmValFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, ⟨ar, u64, asc⟩⟩
      else runJvmValFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, ⟨ar, u64, asc⟩⟩ := rfl

private theorem evalBranchInstrCons_if_icmplt (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (b a : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalBranchInstrCons f1 prog pc (.if_icmplt target) rest ⟨pc0, b :: a :: s, locs, jh, ⟨ar, u64, asc⟩⟩ =
      if a.asI32.toBitVec.slt b.asI32.toBitVec then
        runJvmValFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, ⟨ar, u64, asc⟩⟩
      else runJvmValFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, ⟨ar, u64, asc⟩⟩ := rfl

private theorem evalBranchInstrCons_goto (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalBranchInstrCons f1 prog pc (.goto target) rest ⟨pc0, stk, locs, jh, ⟨ar, u64, asc⟩⟩ =
      runJvmValFast f1 prog target (prog.drop target) ⟨target, stk, locs, jh, ⟨ar, u64, asc⟩⟩ := rfl

private theorem evalResBranchInstrCons_ifeq (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalResBranchInstrCons f1 prog pc (.ifeq target) rest ⟨pc0, v :: s, locs, jh, ⟨ar, u64, asc⟩⟩ =
      if v.asI32 == 0 then runJvmResFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, ⟨ar, u64, asc⟩⟩
      else runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, ⟨ar, u64, asc⟩⟩ := rfl

private theorem evalResBranchInstrCons_ifne (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalResBranchInstrCons f1 prog pc (.ifne target) rest ⟨pc0, v :: s, locs, jh, ⟨ar, u64, asc⟩⟩ =
      if !(v.asI32 == 0) then runJvmResFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, ⟨ar, u64, asc⟩⟩
      else runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, ⟨ar, u64, asc⟩⟩ := rfl

private theorem evalResBranchInstrCons_iflt (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalResBranchInstrCons f1 prog pc (.iflt target) rest ⟨pc0, v :: s, locs, jh, ⟨ar, u64, asc⟩⟩ =
      if v.asI32.toBitVec.slt 0#32 then
        runJvmResFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, ⟨ar, u64, asc⟩⟩
      else runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, ⟨ar, u64, asc⟩⟩ := rfl

private theorem evalResBranchInstrCons_ifle (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalResBranchInstrCons f1 prog pc (.ifle target) rest ⟨pc0, v :: s, locs, jh, ⟨ar, u64, asc⟩⟩ =
      if v.asI32.toBitVec.sle 0#32 then
        runJvmResFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, ⟨ar, u64, asc⟩⟩
      else runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, ⟨ar, u64, asc⟩⟩ := rfl

private theorem evalResBranchInstrCons_ifgt (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalResBranchInstrCons f1 prog pc (.ifgt target) rest ⟨pc0, v :: s, locs, jh, ⟨ar, u64, asc⟩⟩ =
      if (0#32).slt v.asI32.toBitVec then
        runJvmResFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, ⟨ar, u64, asc⟩⟩
      else runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, ⟨ar, u64, asc⟩⟩ := rfl

private theorem evalResBranchInstrCons_ifge (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalResBranchInstrCons f1 prog pc (.ifge target) rest ⟨pc0, v :: s, locs, jh, ⟨ar, u64, asc⟩⟩ =
      if (0#32).sle v.asI32.toBitVec then
        runJvmResFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, ⟨ar, u64, asc⟩⟩
      else runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, ⟨ar, u64, asc⟩⟩ := rfl

private theorem evalResBranchInstrCons_ifnull (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalResBranchInstrCons f1 prog pc (.ifnull target) rest ⟨pc0, v :: s, locs, jh, ⟨ar, u64, asc⟩⟩ =
      if v.isNull then runJvmResFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, ⟨ar, u64, asc⟩⟩
      else runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, ⟨ar, u64, asc⟩⟩ := rfl

private theorem evalResBranchInstrCons_ifnonnull (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalResBranchInstrCons f1 prog pc (.ifnonnull target) rest ⟨pc0, v :: s, locs, jh, ⟨ar, u64, asc⟩⟩ =
      if !v.isNull then runJvmResFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, ⟨ar, u64, asc⟩⟩
      else runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, ⟨ar, u64, asc⟩⟩ := rfl

private theorem evalResBranchInstrCons_if_icmpeq (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (b a : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalResBranchInstrCons f1 prog pc (.if_icmpeq target) rest ⟨pc0, b :: a :: s, locs, jh, ⟨ar, u64, asc⟩⟩ =
      if a.asI32 == b.asI32 then runJvmResFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, ⟨ar, u64, asc⟩⟩
      else runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, ⟨ar, u64, asc⟩⟩ := rfl

private theorem evalResBranchInstrCons_if_icmpne (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (b a : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalResBranchInstrCons f1 prog pc (.if_icmpne target) rest ⟨pc0, b :: a :: s, locs, jh, ⟨ar, u64, asc⟩⟩ =
      if !(a.asI32 == b.asI32) then runJvmResFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, ⟨ar, u64, asc⟩⟩
      else runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, ⟨ar, u64, asc⟩⟩ := rfl

private theorem evalResBranchInstrCons_if_icmplt (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (b a : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalResBranchInstrCons f1 prog pc (.if_icmplt target) rest ⟨pc0, b :: a :: s, locs, jh, ⟨ar, u64, asc⟩⟩ =
      if a.asI32.toBitVec.slt b.asI32.toBitVec then
        runJvmResFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, ⟨ar, u64, asc⟩⟩
      else runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, ⟨ar, u64, asc⟩⟩ := rfl

private theorem evalResBranchInstrCons_goto (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalResBranchInstrCons f1 prog pc (.goto target) rest ⟨pc0, stk, locs, jh, ⟨ar, u64, asc⟩⟩ =
      runJvmResFast f1 prog target (prog.drop target) ⟨target, stk, locs, jh, ⟨ar, u64, asc⟩⟩ := rfl

def rwEvalBranchByInstr (isRes : Bool) (instr : Lean.Expr) : Lean.Elab.Tactic.TacticM Unit := do
  let some n := instr.consumeMData.getAppFn.constName? | return ()
  let thm : Option Lean.Name :=
    if !isRes then
      if n == ``Jvm.JvmInstr.ifeq then some ``evalBranchInstrCons_ifeq
      else if n == ``Jvm.JvmInstr.ifne then some ``evalBranchInstrCons_ifne
      else if n == ``Jvm.JvmInstr.iflt then some ``evalBranchInstrCons_iflt
      else if n == ``Jvm.JvmInstr.ifle then some ``evalBranchInstrCons_ifle
      else if n == ``Jvm.JvmInstr.ifgt then some ``evalBranchInstrCons_ifgt
      else if n == ``Jvm.JvmInstr.ifge then some ``evalBranchInstrCons_ifge
      else if n == ``Jvm.JvmInstr.ifnull then some ``evalBranchInstrCons_ifnull
      else if n == ``Jvm.JvmInstr.ifnonnull then some ``evalBranchInstrCons_ifnonnull
      else if n == ``Jvm.JvmInstr.if_icmpeq then some ``evalBranchInstrCons_if_icmpeq
      else if n == ``Jvm.JvmInstr.if_icmpne then some ``evalBranchInstrCons_if_icmpne
      else if n == ``Jvm.JvmInstr.if_icmplt then some ``evalBranchInstrCons_if_icmplt
      else if n == ``Jvm.JvmInstr.goto then some ``evalBranchInstrCons_goto
      else none
    else
      if n == ``Jvm.JvmInstr.ifeq then some ``evalResBranchInstrCons_ifeq
      else if n == ``Jvm.JvmInstr.ifne then some ``evalResBranchInstrCons_ifne
      else if n == ``Jvm.JvmInstr.iflt then some ``evalResBranchInstrCons_iflt
      else if n == ``Jvm.JvmInstr.ifle then some ``evalResBranchInstrCons_ifle
      else if n == ``Jvm.JvmInstr.ifgt then some ``evalResBranchInstrCons_ifgt
      else if n == ``Jvm.JvmInstr.ifge then some ``evalResBranchInstrCons_ifge
      else if n == ``Jvm.JvmInstr.ifnull then some ``evalResBranchInstrCons_ifnull
      else if n == ``Jvm.JvmInstr.ifnonnull then some ``evalResBranchInstrCons_ifnonnull
      else if n == ``Jvm.JvmInstr.if_icmpeq then some ``evalResBranchInstrCons_if_icmpeq
      else if n == ``Jvm.JvmInstr.if_icmpne then some ``evalResBranchInstrCons_if_icmpne
      else if n == ``Jvm.JvmInstr.if_icmplt then some ``evalResBranchInstrCons_if_icmplt
      else if n == ``Jvm.JvmInstr.goto then some ``evalResBranchInstrCons_goto
      else none
  if let some tn := thm then
    let id := Lean.mkIdent tn
    Lean.Elab.Tactic.evalTactic (← `(tactic| try rw [$id:ident]))

def rwOptionMapResult : Lean.Elab.Tactic.TacticM Unit := do
  let tgt ← Lean.Elab.Tactic.getMainTarget
  let some (_, lhs, _) := tgt.consumeMData.eq? | return ()
  let lhs := lhs.consumeMData
  if lhs.isAppOfArity ``Option.map 4 then
    let arg := lhs.appArg!.consumeMData
    if arg.isAppOfArity ``Option.some 2 then
      Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; rw [option_map_some'])))
    else if arg.isAppOfArity ``Option.none 1 then
      Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; rw [option_map_none'])))

elab "jvm_step_one_chunk" : tactic => do
  let tgt := (← Lean.Elab.Tactic.getMainTarget).consumeMData
  let some (_, lhs, _) := tgt.eq? | return ()
  let (inner, isMap) := unwrapRunLhs lhs
  let isRes := inner.isAppOfArity ``runJvmResFast 5
  if isRes then
    Lean.Elab.Tactic.evalTactic (← `(tactic| rw [runJvmResFast_stepBlockChunk 40]))
  else
    Lean.Elab.Tactic.evalTactic (← `(tactic| rw [runJvmValFast_stepBlockChunk 40]))
  if !(← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then
    if isMap then
      Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; arg 2; arg 1; jvm_whnf_blk)))
    else
      Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; arg 1; jvm_whnf_blk)))
    let tgt2 := (← Lean.Elab.Tactic.getMainTarget).consumeMData
    let some (_, lhs2, _) := tgt2.eq? | return ()
    let (afterApp, _) := unwrapRunLhs lhs2
    let chunkRes := (afterApp.getArg! 0).consumeMData
    if let some cn := chunkRes.getAppFn.constName? then
      if !isRes then
        if cn == ``Jvm.BlockChunkRes.cont then
          Lean.Elab.Tactic.evalTactic (← `(tactic| rw [afterBlockChunk_cont]))
        else if cn == ``Jvm.BlockChunkRes.jump then
          Lean.Elab.Tactic.evalTactic (← `(tactic| rw [afterBlockChunk_jump]))
        else if cn == ``Jvm.BlockChunkRes.done then
          Lean.Elab.Tactic.evalTactic (← `(tactic| rw [afterBlockChunk_done]))
      else
        if cn == ``Jvm.BlockResChunkRes.cont then
          Lean.Elab.Tactic.evalTactic (← `(tactic| rw [afterResBlockChunk_cont]))
        else if cn == ``Jvm.BlockResChunkRes.jump then
          Lean.Elab.Tactic.evalTactic (← `(tactic| rw [afterResBlockChunk_jump]))
        else if cn == ``Jvm.BlockResChunkRes.done then
          Lean.Elab.Tactic.evalTactic (← `(tactic| rw [afterResBlockChunk_done]))
          rwOptionMapResult
    if !(← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then
      Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; norm_jvm_locals)))
      Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; jvm_whnf_run_args)))

private theorem ite_bool_eq_true_left {α : Type} {b : Bool} (h : b = true) (t e : α) :
    (if b = true then t else e) = t := by subst h; rfl

private theorem ite_bool_eq_true_right {α : Type} {b : Bool} (h : b = false) (t e : α) :
    (if b = true then t else e) = e := by subst h; rfl

elab "reduce_top_mc_ite" : tactic => Lean.Elab.Tactic.withMainContext do
  let tgt ← Lean.Elab.Tactic.getMainTarget
  let some (_, lhs, rhs) := tgt.eq? | return ()
  let lhs := lhs.consumeMData
  let (hasMap, mapFn, mapArgs, iteExpr) :=
    if lhs.isAppOfArity ``Option.map 4 then
      (true, lhs.getAppFn, lhs.getAppArgs, lhs.appArg!.consumeMData)
    else
      (false, lhs, #[], lhs)
  if !iteExpr.isAppOfArity ``ite 5 then return ()
  let args := iteExpr.getAppArgs
  let cond := args[1]!.consumeMData
  if !cond.isAppOfArity ``Eq 3 then return ()
  let b := cond.getArg! 1
  let eqTrue ← Lean.Meta.mkEq b (Lean.mkConst ``Bool.true)
  let eqFalse ← Lean.Meta.mkEq b (Lean.mkConst ``Bool.false)
  let saved ← Lean.Elab.Tactic.getGoals
  let g ← Lean.Elab.Tactic.getMainGoal
  let tryClose (goalTy : Lean.Expr) (thmName : Lean.Name) (branchExpr : Lean.Expr) :
      Lean.Elab.Tactic.TacticM Bool := do
    let mvar ← Lean.Meta.mkFreshExprMVar goalTy
    Lean.Elab.Tactic.setGoals [mvar.mvarId!]
    try
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        simp only [algHooks_checkInstanceOf, checkInstanceOf_level4_level4, checkInstanceOf_level4_cell,
          checkInstanceOf_cell_level4, checkInstanceOf_cell_cell,
          ui32_beq_0_0, ui32_beq_1_0, eq_self_iff_true,
          Bool.not_true, Bool.not_false, Bool.false_eq_true, beq_self_eq_true, ite_true, ite_false]))
    catch _ =>
      Lean.Elab.Tactic.setGoals saved
      return false
    let rem ← Lean.Elab.Tactic.getUnsolvedGoals
    if rem.isEmpty then
      let pf ← Lean.instantiateMVars mvar
      let stepEq := Lean.mkAppN (Lean.mkConst thmName) #[args[0]!, b, pf, args[3]!, args[4]!]
      let fullEq ←
        if hasMap then
          let fn := Lean.mkApp3 mapFn mapArgs[0]! mapArgs[1]! mapArgs[2]!
          Lean.Meta.mkCongrArg fn stepEq
        else
          pure stepEq
      let newLhs :=
        if hasMap then
          Lean.mkAppN mapFn #[mapArgs[0]!, mapArgs[1]!, mapArgs[2]!, branchExpr]
        else branchExpr
      let newTgt ← Lean.Meta.mkEq newLhs rhs
      let newMvar ← Lean.Meta.mkFreshExprMVar newTgt
      g.assign (← Lean.Meta.mkEqTrans fullEq newMvar)
      Lean.Elab.Tactic.setGoals (newMvar.mvarId! :: saved.tail!)
      return true
    Lean.Elab.Tactic.setGoals saved
    return false
  if ← tryClose eqTrue ``ite_bool_eq_true_left args[3]! then return ()
  let _ ← tryClose eqFalse ``ite_bool_eq_true_right args[4]!

elab "jvm_step_nonbranch_chunks" : tactic => do
  for _ in [:40] do
    if (← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then break
    if ← isRunJvmAtNonBranch then
      Lean.Elab.Tactic.evalTactic (← `(tactic| jvm_step_one_chunk))
    else if ← isRunJvmAtForwardGoto then
      let tgt := (← Lean.Elab.Tactic.getMainTarget).consumeMData
      let some (_, lhs, _) := tgt.eq? | break
      let (inner, isMap) := unwrapRunLhs lhs
      let isRes := inner.isAppOfArity ``runJvmResFast 5
      if isRes then
        Lean.Elab.Tactic.evalTactic (← `(tactic| rw [runJvmResFast_at_branch_cons (hbr := rfl)]))
      else
        Lean.Elab.Tactic.evalTactic (← `(tactic| rw [runJvmValFast_at_branch_cons (hbr := rfl)]))
      if !(← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then
        if isMap then
          Lean.Elab.Tactic.evalTactic (← `(tactic| (
            (conv => lhs; arg 2; arg 1; whnf)
            (conv => lhs; arg 2; arg 3; whnf)
            (conv => lhs; arg 2; arg 4; whnf)
            (conv => lhs; arg 2; arg 6; jvm_whnf_blk))))
          let tgt2 := (← Lean.Elab.Tactic.getMainTarget).consumeMData
          let some (_, lhs2, _) := tgt2.eq? | break
          let (evalApp, _) := unwrapRunLhs lhs2
          rwEvalBranchByInstr isRes (evalApp.getArg! 3)
          if !(← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then
            Lean.Elab.Tactic.evalTactic (← `(tactic| (
              (conv => lhs; try rw [option_map_ite])
              (conv => lhs; norm_jvm_locals; jvm_whnf_run_args))))
        else
          Lean.Elab.Tactic.evalTactic (← `(tactic| (
            (conv => lhs; arg 1; whnf)
            (conv => lhs; arg 3; whnf)
            (conv => lhs; arg 4; whnf)
            (conv => lhs; arg 6; jvm_whnf_blk))))
          let tgt2 := (← Lean.Elab.Tactic.getMainTarget).consumeMData
          let some (_, lhs2, _) := tgt2.eq? | break
          rwEvalBranchByInstr isRes (lhs2.getArg! 3)
          if !(← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then
            Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; norm_jvm_locals; jvm_whnf_run_args)))
    else
      break

elab "jvm_step_branch_tail" : tactic => do
  if (← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then return ()
  let tgt := (← Lean.Elab.Tactic.getMainTarget).consumeMData
  let some (_, lhs, _) := tgt.eq? | return ()
  let (inner, isMap) := unwrapRunLhs lhs
  let isRes := inner.isAppOfArity ``runJvmResFast 5
  let isVal := inner.isAppOfArity ``runJvmValFast 5
  if !isRes && !isVal then return ()
  try
    if isRes then
      Lean.Elab.Tactic.evalTactic (← `(tactic| rw [runJvmResFast_at_branch_cons (hbr := rfl)]))
    else
      Lean.Elab.Tactic.evalTactic (← `(tactic| rw [runJvmValFast_at_branch_cons (hbr := rfl)]))
  catch _ =>
    return ()
  if !(← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then
    if isMap then
      Lean.Elab.Tactic.evalTactic (← `(tactic| (
        (conv => lhs; arg 2; arg 1; whnf)
        (conv => lhs; arg 2; arg 3; whnf)
        (conv => lhs; arg 2; arg 4; whnf)
        (conv => lhs; arg 2; arg 6; jvm_whnf_blk))))
      let tgt2 := (← Lean.Elab.Tactic.getMainTarget).consumeMData
      let some (_, lhs2, _) := tgt2.eq? | return ()
      let (evalApp, _) := unwrapRunLhs lhs2
      rwEvalBranchByInstr isRes (evalApp.getArg! 3)
      Lean.Elab.Tactic.evalTactic (← `(tactic| (
        (conv => lhs; arg 2; norm_jvm_locals)
        (conv => lhs; try rw [option_map_ite])
        reduce_top_mc_ite)))
      rwOptionMapResult
      Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; jvm_whnf_run_args)))
    else
      Lean.Elab.Tactic.evalTactic (← `(tactic| (
        (conv => lhs; arg 1; whnf)
        (conv => lhs; arg 3; whnf)
        (conv => lhs; arg 4; whnf)
        (conv => lhs; arg 6; jvm_whnf_blk))))
      let tgt2 := (← Lean.Elab.Tactic.getMainTarget).consumeMData
      let some (_, lhs2, _) := tgt2.eq? | return ()
      rwEvalBranchByInstr isRes (lhs2.getArg! 3)
      Lean.Elab.Tactic.evalTactic (← `(tactic| (
        (conv => lhs; norm_jvm_locals)
        reduce_top_mc_ite
        (conv => lhs; jvm_whnf_run_args))))

elab "jvm_step_blk0" _prog:ident : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| jvm_step_nonbranch_chunks))
  if !(← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then
    Lean.Elab.Tactic.evalTactic (← `(tactic| jvm_step_branch_tail))

elab "jvm_step_blk" _prog:ident : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| jvm_step_nonbranch_chunks))
  if !(← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then
    Lean.Elab.Tactic.evalTactic (← `(tactic| jvm_step_branch_tail))


end Algorithm.JvmVerification
