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
import Jvm.Proofs

namespace Jvm.Tactics

open Lean Elab Tactic Meta

def withOpaque {α : Type} (opaques : NameSet) (k : MetaM α) : MetaM α := do
  let orig ← getTransparency
  withConfig (fun cfg => { cfg with transparency := orig }) do
    Lean.Meta.withCanUnfoldPred (fun cfg c => do
      if opaques.contains c.name then return false
      else Lean.Meta.canUnfoldDefault cfg c) k

def natLit? (e : Expr) : Option Nat :=
  e.rawNatLit? <|> e.nat?

partial def evalNatLit? (e : Expr) : MetaM (Option Nat) := do
  if e.hasFVar || e.hasLooseBVars then return none
  let e ← whnf e
  if let some n := natLit? e then return some n
  if e.isConstOf ``Nat.zero then return some 0
  if e.isAppOfArity ``Nat.succ 1 then
    return (← evalNatLit? e.appArg!).map (· + 1)
  return none

partial def normJvmNatWith (opaques : NameSet) (e : Expr) : MetaM Expr := do
  if let some n := natLit? e then
    return Lean.mkNatLit n
  let e ← withOpaque opaques (whnf e)
  if let some n := natLit? e then
    return Lean.mkNatLit n
  if e.isAppOfArity ``Nat.succ 1 then
    let a ← normJvmNatWith opaques (e.getArg! 0)
    if let some n := natLit? a then
      return Lean.mkNatLit (n + 1)
    return mkApp (mkConst ``Nat.succ) a
  else if e.isAppOfArity ``Nat.add 2 then
    let a ← normJvmNatWith opaques (e.getArg! 0)
    let b ← normJvmNatWith opaques (e.getArg! 1)
    if let (some na, some nb) := (natLit? a, natLit? b) then
      return Lean.mkNatLit (na + nb)
    return mkApp2 (mkConst ``Nat.add) a b
  else return e

def whnfUnfoldInitJvmState (initConsts : List Name := [``Jvm.initJvmState]) (s' : Expr) : MetaM Expr := do
  if initConsts.any s'.isAppOf || s'.isAppOf ``Jvm.initJvmState then
    let u1 ← match ← unfoldDefinition? s' with | some u => pure u | none => pure s'
    let u2 ← if u1.isAppOf ``Jvm.initJvmState then
        match ← unfoldDefinition? u1 with | some u => pure u | none => pure u1
      else pure u1
    whnfCore u2
  else
    whnfCore s'

def foldInitLocals (init slots : Expr) : Expr := Id.run do
  let mut acc := init
  let mut cur := slots
  while cur.isAppOfArity ``List.cons 3 do
    let hd := cur.getArg! 1
    let tl := cur.getArg! 2
    if hd.isAppOfArity ``Prod.mk 4 then
      let valTy := hd.getArg! 1
      let extTy := if valTy.isAppOf ``Jvm.JvmVal then valTy.appArg! else valTy
      acc := mkApp4 (mkConst ``Jvm.setLocal) extTy acc (hd.getArg! 2) (hd.getArg! 3)
      cur := tl
    else
      break
  return acc

partial def reduceJvmStateProj (initConsts : List Name := [``Jvm.initJvmState])
    (extraProj : Expr → MetaM (Option Expr) := fun _ => pure none) (e : Expr) : MetaM Expr := do
  let e := e.consumeMData
  if let .proj ``Jvm.JvmState i s := e then
    let s' ← reduceJvmStateProj initConsts extraProj s
    if s'.isAppOfArity ``Jvm.JvmState.mk 7 then
      return ← reduceJvmStateProj initConsts extraProj (s'.getArg! (2 + i))
    let sw ← whnfUnfoldInitJvmState initConsts s'
    if sw.isAppOfArity ``Jvm.JvmState.mk 7 then
      return ← reduceJvmStateProj initConsts extraProj (sw.getArg! (2 + i))
    return .proj ``Jvm.JvmState i s'
  if let some r ← extraProj e then
    return r
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
      let s' ← reduceJvmStateProj initConsts extraProj args[2]!
      if s'.isAppOfArity ``Jvm.JvmState.mk 7 then
        return ← reduceJvmStateProj initConsts extraProj (s'.getArg! (2 + i))
      let sw ← whnfUnfoldInitJvmState initConsts s'
      if sw.isAppOfArity ``Jvm.JvmState.mk 7 then
        return ← reduceJvmStateProj initConsts extraProj (sw.getArg! (2 + i))
      return mkAppN e.getAppFn #[args[0]!, args[1]!, s']
    if n == ``Jvm.setLocal && e.getAppNumArgs == 4 then
      let args := e.getAppArgs
      return mkApp4 e.getAppFn args[0]! (← reduceJvmStateProj initConsts extraProj args[1]!) args[2]! args[3]!
  return e

partial def normJvmBlkExpr (initConsts : List Name := [``Jvm.initJvmState])
    (extraProj : Expr → MetaM (Option Expr) := fun _ => pure none) (e : Expr) : MetaM Expr := do
  let e ← whnf e
  let fn := e.getAppFn
  let args := e.getAppArgs
  match fn.constName? with
  | some n =>
    if n == ``Sum.inl || n == ``Sum.inr || n == ``Prod.mk ||
       n == ``Option.some || n == ``List.cons then
      let args' ← args.mapM (normJvmBlkExpr initConsts extraProj)
      return mkAppN fn args'
    else if n == ``Jvm.BlockChunkRes.done || n == ``Jvm.BlockResChunkRes.done then
      let res' ← normJvmBlkExpr initConsts extraProj args[2]!
      return mkAppN fn #[args[0]!, args[1]!, res']
    else if n == ``Jvm.BlockChunkRes.cont || n == ``Jvm.BlockResChunkRes.cont then
      let f' ← normJvmBlkExpr initConsts extraProj args[2]!
      let pc' ← normJvmBlkExpr initConsts extraProj args[3]!
      let st' ← normJvmBlkExpr initConsts extraProj args[5]!
      return mkAppN fn #[args[0]!, args[1]!, f', pc', args[4]!, st']
    else if n == ``Jvm.BlockChunkRes.jump || n == ``Jvm.BlockResChunkRes.jump then
      let f' ← normJvmBlkExpr initConsts extraProj args[2]!
      let st' ← normJvmBlkExpr initConsts extraProj args[3]!
      return mkAppN fn #[args[0]!, args[1]!, f', st']
    else if n == ``Jvm.JvmState.mk then
      let pc' ← normJvmBlkExpr initConsts extraProj args[2]!
      let stk' ← normJvmBlkExpr initConsts extraProj args[3]!
      let locs' ← reduceJvmStateProj initConsts extraProj args[4]!
      let jh' ← reduceJvmStateProj initConsts extraProj args[5]!
      let heap' ← reduceJvmStateProj initConsts extraProj args[6]!
      return mkAppN fn #[args[0]!, args[1]!, pc', stk', locs', jh', heap']
    else if n == ``Bool.rec then
      let args' ← args.mapM fun a => do
        let aw ← whnf a
        if aw.isLambda then
          lambdaTelescope aw fun xs body => do
            let body' ← normJvmBlkExpr initConsts extraProj body
            mkLambdaFVars xs body'
        else return a
      return mkAppN fn args'
    else
      return e
  | none => return e

partial def normJvmLocalsExpr (initConsts : List Name := [``Jvm.initJvmState])
    (extraProj : Expr → MetaM (Option Expr) := fun _ => pure none)
    (extraAppNames : List Name := []) (e : Expr) : MetaM Expr :=
  Meta.transform e
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
            return .visit (mkApp args[1]! args[4]!)
        return .continue
      else if sub.isAppOfArity ``List.foldl 6 then
        let args := sub.getAppArgs
        if Option.isSome (args[2]!.find? (·.isConstOf ``Jvm.setLocal)) then
          if let some _ ← evalNatLit? args[5]! then
            if args[4]!.isAppOfArity ``List.cons 3 || args[4]!.isAppOfArity ``List.nil 1 then
              return .visit (mkApp (foldInitLocals args[3]! args[4]!) args[5]!)
        return .continue
      else if sub.isProj then
        let sub' ← reduceJvmStateProj initConsts extraProj sub
        if sub' != sub then return .visit sub'
        return .continue
      else if sub.isAppOfArity ``Jvm.JvmState.locals 3 || sub.isAppOfArity ``Jvm.JvmState.heap 3 ||
              extraAppNames.any (fun nm => sub.isAppOfArity nm 1) then
        let sub' ← reduceJvmStateProj initConsts extraProj sub
        if sub' != sub then return .visit sub'
        return .continue
      else if sub.isApp && (sub.appFn!.isProj || sub.appFn!.isAppOfArity ``Jvm.JvmState.locals 3) then
        let locs' ← reduceJvmStateProj initConsts extraProj sub.appFn!
        if locs' != sub.appFn! then
          return .visit (mkApp locs' sub.appArg!)
        return .continue
      else if sub.isAppOfArity ``Jvm.JvmState.locals 4 then
        let s := sub.appFn!.getArg! 2
        let idx := sub.appArg!
        if let some _ ← evalNatLit? idx then
          let sw ← whnf s
          if sw.isAppOfArity ``Jvm.JvmState.mk 7 then
            let locs := sw.getArg! 4
            if locs.isAppOfArity ``List.foldl 5 then
              let folded := foldInitLocals (locs.getArg! 3) (locs.getArg! 4)
              return .visit (mkApp folded idx)
            else
              let next := mkApp locs idx
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
      if sub.isAppOfArity ``Jvm.JvmVal.asI32? 2 then
        let a := sub.appArg!
        if a.isAppOfArity ``Jvm.JvmVal.i32 2 then
          return .done (mkAppN (mkConst ``Option.some [Level.zero]) #[mkConst ``UInt32, a.getArg! 1])
        return .done sub
      else if sub.isAppOfArity ``Jvm.JvmVal.asI64? 2 then
        let a := sub.appArg!
        if a.isAppOfArity ``Jvm.JvmVal.i64 2 then
          return .done (mkAppN (mkConst ``Option.some [Level.zero]) #[mkConst ``UInt64, a.getArg! 1])
        return .done sub
      else if sub.isAppOfArity ``Jvm.JvmVal.asF32? 2 then
        let a := sub.appArg!
        if a.isAppOfArity ``Jvm.JvmVal.f32 2 then
          return .done (mkAppN (mkConst ``Option.some [Level.zero]) #[mkConst ``Float32, a.getArg! 1])
        return .done sub
      else if sub.isAppOfArity ``Jvm.JvmVal.asF64? 2 then
        let a := sub.appArg!
        if a.isAppOfArity ``Jvm.JvmVal.f64 2 then
          return .done (mkAppN (mkConst ``Option.some [Level.zero]) #[mkConst ``Float, a.getArg! 1])
        return .done sub
      else if sub.isAppOfArity ``Jvm.JvmVal.isNull 2 then
        let a := sub.appArg!
        if a.isAppOfArity ``Jvm.JvmVal.null 1 then
          return .done (mkConst ``Bool.true)
        return .done sub
      else
        return .done sub)

partial def fastDropListEq (e : Expr) (n : Nat) : MetaM (Expr × Expr) := do
  let ty := mkConst ``Jvm.JvmInstr
  if n == 0 then
    let lhs := mkAppN (mkConst ``List.drop [Level.zero]) #[ty, toExpr 0, e]
    return (e, ← mkExpectedTypeHint (← mkEqRefl e) (← mkEq lhs e))
  let mut cur := e
  let mut remaining := n
  let step := 40
  let mut accEq : Option Expr := none
  let mut dropped : Nat := 0
  while remaining > 0 do
    let k := min remaining step
    let curWhnf ← whnf cur
    let mut tail := curWhnf
    for _ in [:k] do
      let t ← whnf tail
      if t.isAppOfArity ``List.cons 3 then
        tail := t.getArg! 2
      else
        tail := t
        break
    let lhsStep := mkAppN (mkConst ``List.drop [Level.zero]) #[ty, toExpr k, curWhnf]
    let stepEq ← mkExpectedTypeHint (← mkEqRefl tail) (← mkEq lhsStep tail)
    match accEq with
    | none =>
      let origLhs := mkAppN (mkConst ``List.drop [Level.zero]) #[ty, toExpr k, e]
      let eq0 ← mkExpectedTypeHint stepEq (← mkEq origLhs tail)
      accEq := some eq0
      cur := tail
      dropped := k
    | some prevEq =>
      let fnDropK := mkApp2 (mkConst ``List.drop [Level.zero]) ty (toExpr k)
      let ap ← mkCongrArg fnDropK prevEq
      let eqCurWhnf ← mkEqTrans ap stepEq
      let ddrop := mkAppN (mkConst ``List.drop_drop [Level.zero]) #[ty, toExpr k, toExpr dropped, e]
      let symD ← mkEqSymm ddrop
      let ap1 ← mkEqTrans symD eqCurWhnf
      let newDropped := dropped + k
      let sumEq := mkAppN (mkConst ``List.drop [Level.zero]) #[ty, toExpr newDropped, e]
      let ap2 ← mkExpectedTypeHint ap1 (← mkEq sumEq tail)
      accEq := some ap2
      cur := tail
      dropped := newDropped
    remaining := remaining - k
  return (cur, accEq.get!)

def unwrapRunLhs (e : Expr) : Expr × Bool :=
  let e := e.consumeMData
  if e.isAppOfArity ``Option.map 4 then
    ((e.getArg! 3).consumeMData, true)
  else
    (e, false)

def rwOptionMapResult : TacticM Unit := do
  let tgt ← getMainTarget
  let some (_, lhs, _) := tgt.consumeMData.eq? | return ()
  let lhs := lhs.consumeMData
  if lhs.isAppOfArity ``Option.map 4 then
    let arg := lhs.appArg!.consumeMData
    if arg.isAppOfArity ``Option.some 2 then
      evalTactic (← `(tactic| (conv => lhs; rw [Jvm.option_map_some'])))
    else if arg.isAppOfArity ``Option.none 1 then
      evalTactic (← `(tactic| (conv => lhs; rw [Jvm.option_map_none'])))

def defaultEvalBranchThm (isRes : Bool) (instrName : Name) : Option Name :=
  if !isRes then
    if instrName == ``Jvm.JvmInstr.ifeq then some ``Jvm.evalBranchInstrCons_ifeq
    else if instrName == ``Jvm.JvmInstr.ifne then some ``Jvm.evalBranchInstrCons_ifne
    else if instrName == ``Jvm.JvmInstr.iflt then some ``Jvm.evalBranchInstrCons_iflt
    else if instrName == ``Jvm.JvmInstr.ifle then some ``Jvm.evalBranchInstrCons_ifle
    else if instrName == ``Jvm.JvmInstr.ifgt then some ``Jvm.evalBranchInstrCons_ifgt
    else if instrName == ``Jvm.JvmInstr.ifge then some ``Jvm.evalBranchInstrCons_ifge
    else if instrName == ``Jvm.JvmInstr.ifnull then some ``Jvm.evalBranchInstrCons_ifnull
    else if instrName == ``Jvm.JvmInstr.ifnonnull then some ``Jvm.evalBranchInstrCons_ifnonnull
    else if instrName == ``Jvm.JvmInstr.if_icmpeq then some ``Jvm.evalBranchInstrCons_if_icmpeq
    else if instrName == ``Jvm.JvmInstr.if_icmpne then some ``Jvm.evalBranchInstrCons_if_icmpne
    else if instrName == ``Jvm.JvmInstr.if_icmplt then some ``Jvm.evalBranchInstrCons_if_icmplt
    else if instrName == ``Jvm.JvmInstr.if_icmpge then some ``Jvm.evalBranchInstrCons_if_icmpge
    else if instrName == ``Jvm.JvmInstr.if_icmpgt then some ``Jvm.evalBranchInstrCons_if_icmpgt
    else if instrName == ``Jvm.JvmInstr.if_icmple then some ``Jvm.evalBranchInstrCons_if_icmple
    else if instrName == ``Jvm.JvmInstr.tableswitch then some ``Jvm.evalBranchInstrCons_tableswitch
    else if instrName == ``Jvm.JvmInstr.lookupswitch then some ``Jvm.evalBranchInstrCons_lookupswitch
    else if instrName == ``Jvm.JvmInstr.goto then some ``Jvm.evalBranchInstrCons_goto
    else none
  else
    if instrName == ``Jvm.JvmInstr.ifeq then some ``Jvm.evalResBranchInstrCons_ifeq
    else if instrName == ``Jvm.JvmInstr.ifne then some ``Jvm.evalResBranchInstrCons_ifne
    else if instrName == ``Jvm.JvmInstr.iflt then some ``Jvm.evalResBranchInstrCons_iflt
    else if instrName == ``Jvm.JvmInstr.ifle then some ``Jvm.evalResBranchInstrCons_ifle
    else if instrName == ``Jvm.JvmInstr.ifgt then some ``Jvm.evalResBranchInstrCons_ifgt
    else if instrName == ``Jvm.JvmInstr.ifge then some ``Jvm.evalResBranchInstrCons_ifge
    else if instrName == ``Jvm.JvmInstr.ifnull then some ``Jvm.evalResBranchInstrCons_ifnull
    else if instrName == ``Jvm.JvmInstr.ifnonnull then some ``Jvm.evalResBranchInstrCons_ifnonnull
    else if instrName == ``Jvm.JvmInstr.if_icmpeq then some ``Jvm.evalResBranchInstrCons_if_icmpeq
    else if instrName == ``Jvm.JvmInstr.if_icmpne then some ``Jvm.evalResBranchInstrCons_if_icmpne
    else if instrName == ``Jvm.JvmInstr.if_icmplt then some ``Jvm.evalResBranchInstrCons_if_icmplt
    else if instrName == ``Jvm.JvmInstr.if_icmpge then some ``Jvm.evalResBranchInstrCons_if_icmpge
    else if instrName == ``Jvm.JvmInstr.if_icmpgt then some ``Jvm.evalResBranchInstrCons_if_icmpgt
    else if instrName == ``Jvm.JvmInstr.if_icmple then some ``Jvm.evalResBranchInstrCons_if_icmple
    else if instrName == ``Jvm.JvmInstr.tableswitch then some ``Jvm.evalResBranchInstrCons_tableswitch
    else if instrName == ``Jvm.JvmInstr.lookupswitch then some ``Jvm.evalResBranchInstrCons_lookupswitch
    else if instrName == ``Jvm.JvmInstr.goto then some ``Jvm.evalResBranchInstrCons_goto
    else none

def rwEvalBranchByInstrWith (lookup : Bool → Name → Option Name := defaultEvalBranchThm)
    (isRes : Bool) (instr : Expr) : TacticM Unit := do
  let some n := instr.consumeMData.getAppFn.constName? | return ()
  if let some tn := lookup isRes n then
    let id := mkIdent tn
    evalTactic (← `(tactic| try rw [$id:ident]))
    if n == ``Jvm.JvmInstr.ifeq || n == ``Jvm.JvmInstr.ifne then
      let boolId := mkIdent (tn.appendAfter "_bool")
      evalTactic (← `(tactic| try rw [$boolId:ident]))

partial def normRunTailWith (runValName runResName : Name)
    (normSt : Expr → MetaM Expr) (b : Expr) : MetaM (Expr × Option Expr) := do
  if b.isAppOfArity ``Option.map 4 then
    let ma := b.getAppArgs
    let (inner', eqOpt) ← normRunTailWith runValName runResName normSt ma[3]!
    let newB := mkAppN b.getAppFn #[ma[0]!, ma[1]!, ma[2]!, inner']
    match eqOpt with
    | none => return (newB, none)
    | some eqP =>
      let pf3 := mkAppN b.getAppFn #[ma[0]!, ma[1]!, ma[2]!]
      return (newB, some (← mkCongrArg pf3 eqP))
  else if b.isAppOfArity runValName 5 || b.isAppOfArity runResName 5 then
    let ba := b.getAppArgs
    let fuel' ← whnf ba[0]!
    let pc' ← whnf ba[2]!
    let st' ← normSt ba[4]!
    let mut instrs' := ba[3]!
    let mut instrsEq : Option Expr := none
    if instrs'.isAppOfArity ``List.drop 3 then
      let da := instrs'.getAppArgs
      if let some n ← evalNatLit? da[1]! then
        let (rhs, eqP) ← fastDropListEq da[2]! n
        instrs' := rhs
        instrsEq := some eqP
    let newB := mkAppN b.getAppFn #[fuel', ba[1]!, pc', instrs', st']
    match instrsEq with
    | none => return (newB, none)
    | some eqP =>
      let lam := mkLambda `x .default (← inferType ba[3]!)
        (mkAppN b.getAppFn #[fuel', ba[1]!, pc', Expr.bvar 0, st'])
      let fullEq ← mkCongrArg lam eqP
      let prefixB := mkAppN b.getAppFn #[fuel', ba[1]!, pc', ba[3]!, st']
      let defEq ← mkExpectedTypeHint (← mkEqRefl b) (← mkEq b prefixB)
      return (newB, some (← mkEqTrans defEq fullEq))
  else return (b, none)

def isRunJvmAtPred (runValName runResName : Name) (pred : Name) : TacticM Bool := do
  let tgt := (← getMainTarget).consumeMData
  let some (_, lhs, _) := tgt.eq? | return false
  let (inner, _) := unwrapRunLhs lhs
  if inner.isAppOfArity runValName 5 || inner.isAppOfArity runResName 5 then
    let instrs ← whnf (inner.getArg! 3)
    if instrs.isAppOfArity ``List.cons 3 then
      let instr := instrs.getArg! 1
      let br ← whnf (mkApp (mkConst pred) instr)
      return br.isConstOf ``Bool.false
  return false

def isRunJvmAtForwardGoto (runValName runResName : Name) : TacticM Bool := do
  let tgt := (← getMainTarget).consumeMData
  let some (_, lhs, _) := tgt.eq? | return false
  let (inner, _) := unwrapRunLhs lhs
  if inner.isAppOfArity runValName 5 || inner.isAppOfArity runResName 5 then
    let instrs ← whnf (inner.getArg! 3)
    if instrs.isAppOfArity ``List.cons 3 then
      let instr ← whnf (instrs.getArg! 1)
      if instr.isAppOfArity ``Jvm.JvmInstr.goto 1 then
        if let (some pcVal, some tgtVal) := (← evalNatLit? (inner.getArg! 2), ← evalNatLit? (instr.getArg! 0)) then
          return pcVal < tgtVal
  return false

end Jvm.Tactics
