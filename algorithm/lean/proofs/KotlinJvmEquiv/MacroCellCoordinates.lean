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
import models.MacroCellCoordinatesModel
import proofs.KotlinJvmEquiv.AlgKotlinProgs

/-!
# JVM bytecode equivalence for `MacroCellCoordinates.kt`

Every lifted method of `MacroCellCoordinatesKt` (`cellToLeafBit`, `coordinatesToLeaf`, `leafToCoordinates`,
`coordinatesToLevel4` and the three `$default` bridges) is proven to compute the standalone model of
`models/MacroCellCoordinatesModel.lean` under `mkAlgKotlinHooks resolveProg depth subFuel`, for every lookup
`resolveProg` that maps the four `MacroCellCoordinatesKt` tags to their lifted programs (`ResolvesMccProgs`, which
`algKotlinProgLookup` satisfies). Calls between lifted methods are not modeled: they run the callee's lifted
program, so the theorems ask for enough call depth and callee fuel. Each `*_equiv` theorem states the returned value
and the exact final JVM heap and `AlgHeap`.

A `Set<IntOffset>` argument is any collection that the hooks model (`algKotlinColl?`) whose elements, in iteration
order, are the boxed `IntOffset`s of the coordinate list (`encodeCoords`). A `$default` bridge replaces an offset by
`0` when its default-argument bit (`2` for `offsetX`, `4` for `offsetY`) is set in the mask; its last argument
(the marker) is arbitrary. `coordinatesToLevel4` reads `MacroCell.Level4Node.Companion`, so its theorems take a heap
whose `Companion` static is unset (the hooks resolve it) or holds the companion singleton.
-/

namespace Algorithm.KotlinJvmVerification.MacroCellCoordinates

open Algorithm.JvmVerification
open Algorithm.KotlinJvmBytecode
open Algorithm.KotlinModel

/-! ### Encodings, lookup and hooks -/

/-- `IntOffset(x, y)` of a model coordinate. -/
def packCoord (p : Int32 × Int32) : UInt64 :=
  packIntOffset p.1.toUInt32 p.2.toUInt32

/-- The elements of a `Set<IntOffset>` holding `coords` in iteration order. -/
def encodeCoords (coords : List (Int32 × Int32)) : Array JvmVal :=
  encodeIntOffsets (coords.map packCoord)

/-- `resolveProg` maps the tags of the four `MacroCellCoordinatesKt` methods that are called to their programs. -/
def ResolvesMccProgs (rp : String → Option (List JvmInstr)) : Prop :=
  rp "MacroCellCoordinatesKt.cellToLeafBit:(II)I" = some MacroCellCoordinatesKt_cellToLeafBit_prog ∧
  rp "MacroCellCoordinatesKt.coordinatesToLeaf:(Ljava/util/Set;II)J" = some MacroCellCoordinatesKt_coordinatesToLeaf_prog ∧
  rp "MacroCellCoordinatesKt.leafToCoordinates:(JII)Ljava/util/Set;" = some MacroCellCoordinatesKt_leafToCoordinates_prog ∧
  rp ("MacroCellCoordinatesKt.coordinatesToLevel4:(Ljava/util/Set;II)" ++
    "Lcom/alexvanyo/composelife/model/MacroCell$Level4Node;") = some MacroCellCoordinatesKt_coordinatesToLevel4_prog

theorem algKotlinProgLookup_resolvesMccProgs : ResolvesMccProgs algKotlinProgLookup := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [algKotlinProgLookup, ↓reduceIte] <;> rfl

/-- The invocation callback type of `algKotlinHooksWith`. -/
abbrev InvokeProg := String → JvmState → List (Nat × JvmVal) → Option (Option (JvmVal × JvmState))

instance mccHasDefaultIsZeroWith (ip : InvokeProg) : Jvm.HasDefaultIsZero (algKotlinHooksWith ip) where
  isZero?_eq := rfl

instance mccHasDefaultIsZero (rp : String → Option (List JvmInstr)) (d sf : Nat) :
    Jvm.HasDefaultIsZero (mkAlgKotlinHooks rp d sf) where
  isZero?_eq := by cases d <;> rfl

/-- Stop predicate for the block stepper: calls, statics, casts, returns and branches. -/
def isMccStop : JvmInstr → Bool
  | .invokestatic _ _ _ | .invokevirtual _ _ _ | .invokespecial _ _ _ | .invokeinterface _ _ _
  | .invokedynamic _ _ _ | .getstatic _ _ _ | .putstatic _ _ _ | .getfield _ _ _ | .putfield _ _ _
  | .newClass _ | .checkcast _ | .instanceof _ | .idiv | .ldiv | .athrow
  | .areturn | .ireturn | .lreturn | .freturn | .dreturn | .vreturn
  | .ifeq _ | .ifne _ | .iflt _ | .ifle _ | .ifgt _ | .ifge _
  | .ifnull _ | .ifnonnull _ | .if_icmpeq _ | .if_icmpne _ | .if_icmplt _
  | .if_icmpge _ | .if_icmpgt _ | .if_icmple _ | .if_acmpeq _ | .if_acmpne _
  | .goto _ | .tableswitch _ _ _ | .lookupswitch _ _ => true
  | _ => false

section StepTactics

open Lean Elab Tactic Meta

def mccOpaqueConsts : NameSet :=
  NameSet.empty
    |>.insert ``mkAlgKotlinHooks
    |>.insert ``algKotlinHooksWith
    |>.insert ``algKotlinProgLookup
    |>.insert ``MacroCellCoordinatesKt_cellToLeafBit_prog
    |>.insert ``MacroCellCoordinatesKt_coordinatesToLeaf_prog
    |>.insert ``MacroCellCoordinatesKt_coordinatesToLeaf_default_prog
    |>.insert ``MacroCellCoordinatesKt_leafToCoordinates_prog
    |>.insert ``MacroCellCoordinatesKt_leafToCoordinates_default_prog
    |>.insert ``MacroCellCoordinatesKt_coordinatesToLevel4_prog
    |>.insert ``MacroCellCoordinatesKt_coordinatesToLevel4_default_prog
    |>.insert ``cellToLeafBitModel
    |>.insert ``coordinatesToLeafModel
    |>.insert ``leafToCoordinatesModel
    |>.insert ``coordinatesToLevel4Model
    |>.insert ``Algorithm.cellToLeafBitUInt
    |>.insert ``Algorithm.makeLevel4Node
    |>.insert ``packIntOffset
    |>.insert ``intOffsetX
    |>.insert ``intOffsetY
    |>.insert ``packCoord

def mccInitConsts : List Name :=
  [``initKotlinJvmState, ``Jvm.initJvmState]

elab "mcc_whnf_blk" : conv => withMainContext do
  let lhs ← Lean.Elab.Tactic.Conv.getLhs
  let res ← Jvm.Tactics.withOpaque mccOpaqueConsts
    (Jvm.Tactics.normJvmBlkExpr mccInitConsts (fun _ => pure none) lhs)
  Lean.Elab.Tactic.Conv.changeLhs res

elab "mcc_norm_locals" : tactic =>
  Lean.Elab.Tactic.liftMetaTactic fun g => do
    let tgt ← instantiateMVars (← g.getType)
    let res ← Jvm.Tactics.normJvmLocalsExpr mccInitConsts (fun _ => pure none) [] tgt
    return [← g.replaceTargetDefEq res]

elab "mcc_norm_run_args" : tactic =>
  Lean.Elab.Tactic.liftMetaTactic fun g => do
    let tgt ← instantiateMVars (← g.getType)
    let normSt := fun s : Expr => do
      let s1 ← Jvm.Tactics.withOpaque mccOpaqueConsts
        (Jvm.Tactics.normJvmBlkExpr mccInitConsts (fun _ => pure none) s)
      if s1.isAppOfArity ``Jvm.JvmState.mk 7 then
        let sa := s1.getAppArgs
        let pcField ← Jvm.Tactics.normJvmNatWith mccOpaqueConsts sa[2]!
        return mkAppN s1.getAppFn #[sa[0]!, sa[1]!, pcField, sa[3]!, sa[4]!, sa[5]!, sa[6]!]
      else
        return s1
    let normRun := fun b : Expr => do
      if b.isAppOfArity ``Jvm.runJvmResFast 8 then
        let ba := b.getAppArgs
        let fuel' ← Jvm.Tactics.withOpaque mccOpaqueConsts (whnf ba[3]!)
        let pc' ← Jvm.Tactics.withOpaque mccOpaqueConsts (whnf ba[5]!)
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

def isMccNonStop : TacticM Bool := do
  let tgt := (← getMainTarget).consumeMData
  let some (_, lhs, _) := tgt.eq? | return false
  let lhs := lhs.consumeMData
  if lhs.isAppOfArity ``Jvm.runJvmResFast 8 then
    let instrs ← whnf (lhs.getArg! 6)
    if instrs.isAppOfArity ``List.cons 3 then
      let instr := instrs.getArg! 1
      let br ← whnf (mkApp (mkConst ``isMccStop) instr)
      return br.isConstOf ``Bool.false
  return false

def isMccForwardGoto : TacticM Bool := do
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

elab "mcc_step_one_chunk" : tactic => do
  let tgt := (← getMainTarget).consumeMData
  let some (_, lhs, _) := tgt.eq? | return ()
  let lhs := lhs.consumeMData
  if !lhs.isAppOfArity ``Jvm.runJvmResFast 8 then return ()
  evalTactic (← `(tactic| (conv => lhs; tactic => mcc_norm_run_args)))
  evalTactic (← `(tactic| rw [Jvm.runJvmResFast_stepBlockChunkWith _ isMccStop 64]))
  if !(← getUnsolvedGoals).isEmpty then
    evalTactic (← `(tactic| (conv => lhs; arg 2; mcc_whnf_blk)))
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
      evalTactic (← `(tactic| (conv => lhs; tactic => mcc_norm_locals)))
      evalTactic (← `(tactic| (conv => lhs; tactic => mcc_norm_run_args)))

elab "mcc_step_blk" : tactic => do
  for _ in [:40] do
    if (← getUnsolvedGoals).isEmpty then break
    if ← isMccNonStop then
      evalTactic (← `(tactic| mcc_step_one_chunk))
    else if ← isMccForwardGoto then
      evalTactic (← `(tactic| (conv => lhs; tactic => mcc_norm_run_args)))
      evalTactic (← `(tactic| rw [Jvm.runJvmResFast_at_branch_cons _ (hbr := rfl)]))
      if !(← getUnsolvedGoals).isEmpty then
        evalTactic (← `(tactic| (
          (conv => lhs; arg 2; whnf)
          (conv => lhs; arg 4; whnf)
          (conv => lhs; arg 5; whnf)
          (conv => lhs; arg 7; mcc_whnf_blk))))
        let tgt2 := (← getMainTarget).consumeMData
        let some (_, lhs2, _) := tgt2.eq? | break
        Jvm.Tactics.rwEvalBranchByInstrWith Jvm.Tactics.defaultEvalBranchThm true (lhs2.consumeMData.getArg! 6)
        if !(← getUnsolvedGoals).isEmpty then
          evalTactic (← `(tactic| (conv => lhs; tactic => mcc_norm_locals; mcc_norm_run_args)))
    else
      break

elab "mcc_branch" : tactic => do
  let tgt := (← getMainTarget).consumeMData
  let some (_, lhs, _) := tgt.eq? | throwError "mcc_branch: goal is not an equation"
  let lhs := lhs.consumeMData
  if !lhs.isAppOfArity ``Jvm.runJvmResFast 8 then throwError "mcc_branch: not a fast JVM run"
  evalTactic (← `(tactic| (conv => lhs; tactic => mcc_norm_run_args)))
  evalTactic (← `(tactic| rw [Jvm.runJvmResFast_at_branch_cons _ (hbr := rfl)]))
  if !(← getUnsolvedGoals).isEmpty then
    evalTactic (← `(tactic| (
      (conv => lhs; arg 2; whnf)
      (conv => lhs; arg 4; whnf)
      (conv => lhs; arg 5; whnf)
      (conv => lhs; arg 7; mcc_whnf_blk))))
    let tgt2 := (← getMainTarget).consumeMData
    let some (_, lhs2, _) := tgt2.eq? | return ()
    Jvm.Tactics.rwEvalBranchByInstrWith Jvm.Tactics.defaultEvalBranchThm true (lhs2.consumeMData.getArg! 6)
    if !(← getUnsolvedGoals).isEmpty then
      evalTactic (← `(tactic| try (first
        | rw [ite_eq_left (by decide)]
        | rw [ite_eq_right (by decide)])))
      if !(← getUnsolvedGoals).isEmpty then
        evalTactic (← `(tactic| (conv => lhs; tactic => mcc_norm_locals; mcc_norm_run_args)))

/-- Steps exactly one non-branch instruction whose effect is computed by `rfl`. -/
macro "mcc_step1" : tactic => `(tactic| rw [Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) (by rfl) rfl])

/-- Steps one stop instruction whose hook result is computed by `rfl`, then continues with `mcc_step_blk`. -/
macro "mcc_rfl_step" : tactic => `(tactic| (
  first
    | rw [Jvm.runJvmResFast_invokestatic_step _ (by rfl)]
    | rw [Jvm.runJvmResFast_invokeinterface_step _ (by rfl)]
    | rw [Jvm.runJvmResFast_invokevirtual_step _ (by rfl)]
    | rw [Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) (by rfl) rfl]
  mcc_step_blk))

end StepTactics

/-! ### Generic run lemmas -/

/-- A fast run from pc 0 that returns `v` in a state with heaps `jh`/`hp` gives the same `runJvmRes` result. -/
theorem exists_of_fast {H : Jvm.JvmHooks AlgExt AlgHeap} {fuel : Nat} {prog : List JvmInstr}
    {st0 : JvmState} {v : JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} (hpc : st0.pc = 0)
    (h : ∃ pc stk locs, Jvm.runJvmResFast H fuel prog 0 prog st0 = some (v, ⟨pc, stk, locs, jh, hp⟩)) :
    ∃ endSt, Jvm.runJvmRes H fuel prog st0 = some (v, endSt) ∧ endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨pc, stk, locs, h⟩ := h
  exact ⟨_, Jvm.runJvmRes_of_runJvmResFast0 H fuel prog st0 _ hpc h, rfl, rfl⟩

/-! ### Generic single-instruction steps -/

section Generic

variable {H : Jvm.JvmHooks AlgExt AlgHeap}

theorem fast_if_icmpgt_jump {f pc pc0 target : Nat} {prog rest : List JvmInstr} {a b : UInt32}
    {s : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (h : b.toBitVec.slt a.toBitVec = true) :
    Jvm.runJvmResFast H (f + 1) prog pc (.if_icmpgt target :: rest) ⟨pc0, .i32 b :: .i32 a :: s, locs, jh, hp⟩ =
      Jvm.runJvmResFast H f prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons H (hbr := rfl), Jvm.evalResBranchInstrCons_if_icmpgt, h]
  rfl

theorem fast_if_icmpgt_fall {f pc pc0 target : Nat} {prog rest : List JvmInstr} {a b : UInt32}
    {s : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (h : b.toBitVec.slt a.toBitVec = false) :
    Jvm.runJvmResFast H (f + 1) prog pc (.if_icmpgt target :: rest) ⟨pc0, .i32 b :: .i32 a :: s, locs, jh, hp⟩ =
      Jvm.runJvmResFast H f prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons H (hbr := rfl), Jvm.evalResBranchInstrCons_if_icmpgt, h]
  rfl

theorem fast_if_icmpge_jump {f pc pc0 target : Nat} {prog rest : List JvmInstr} {a b : UInt32}
    {s : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (h : b.toBitVec.sle a.toBitVec = true) :
    Jvm.runJvmResFast H (f + 1) prog pc (.if_icmpge target :: rest) ⟨pc0, .i32 b :: .i32 a :: s, locs, jh, hp⟩ =
      Jvm.runJvmResFast H f prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons H (hbr := rfl), Jvm.evalResBranchInstrCons_if_icmpge, h]
  rfl

theorem fast_if_icmpge_fall {f pc pc0 target : Nat} {prog rest : List JvmInstr} {a b : UInt32}
    {s : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (h : b.toBitVec.sle a.toBitVec = false) :
    Jvm.runJvmResFast H (f + 1) prog pc (.if_icmpge target :: rest) ⟨pc0, .i32 b :: .i32 a :: s, locs, jh, hp⟩ =
      Jvm.runJvmResFast H f prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons H (hbr := rfl), Jvm.evalResBranchInstrCons_if_icmpge, h]
  rfl

theorem fast_ireturn {ip : InvokeProg} {f pc pc0 : Nat} {prog rest : List JvmInstr} {v : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    Jvm.runJvmResFast (algKotlinHooksWith ip) (f + 1) prog pc (.ireturn :: rest) ⟨pc0, v :: stk, locs, jh, hp⟩ =
      some (v, ⟨pc, v :: stk, locs, jh, hp⟩) := by
  rw [Jvm.runJvmResFast_step_nonbranch _ f prog pc .ireturn rest _ rfl (by simp)]
  rfl

theorem fast_lreturn {f pc pc0 : Nat} {prog rest : List JvmInstr} {v : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    Jvm.runJvmResFast H (f + 1) prog pc (.lreturn :: rest) ⟨pc0, v :: stk, locs, jh, hp⟩ =
      some (v, ⟨pc, v :: stk, locs, jh, hp⟩) := by
  rw [Jvm.runJvmResFast_step_nonbranch H f prog pc .lreturn rest _ rfl (by simp)]
  rfl

theorem fast_areturn {f pc pc0 : Nat} {prog rest : List JvmInstr} {v : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    Jvm.runJvmResFast H (f + 1) prog pc (.areturn :: rest) ⟨pc0, v :: stk, locs, jh, hp⟩ =
      some (v, ⟨pc, v :: stk, locs, jh, hp⟩) := by
  rw [Jvm.runJvmResFast_step_nonbranch H f prog pc .areturn rest _ rfl (by simp)]
  rfl

end Generic

/-! ### Reference-interpreter steps (for runs that throw) -/

theorem setLocal_apply_self (l : Nat → JvmVal) (i : Nat) (v : JvmVal) : setLocal l i v i = v := by
  simp [setLocal]

theorem setLocal_apply_ne (l : Nat → JvmVal) {i j : Nat} (v : JvmVal) (h : j ≠ i) : setLocal l i v j = l j := by
  simp [setLocal, h]

section Res

variable {ip : InvokeProg}

theorem res_if_icmpgt {f pc t : Nat} {prog : List JvmInstr} {a b : UInt32}
    {s : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hget : prog[pc]? = some (.if_icmpgt t)) :
    Jvm.runJvmRes (algKotlinHooksWith ip) (f + 1) prog ⟨pc, .i32 b :: .i32 a :: s, locs, jh, hp⟩ =
      if b.toBitVec.slt a.toBitVec then Jvm.runJvmRes (algKotlinHooksWith ip) f prog ⟨t, s, locs, jh, hp⟩
      else Jvm.runJvmRes (algKotlinHooksWith ip) f prog ⟨pc + 1, s, locs, jh, hp⟩ := by
  simp only [Jvm.runJvmRes, hget]
  rfl

theorem res_if_icmpge {f pc t : Nat} {prog : List JvmInstr} {a b : UInt32}
    {s : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hget : prog[pc]? = some (.if_icmpge t)) :
    Jvm.runJvmRes (algKotlinHooksWith ip) (f + 1) prog ⟨pc, .i32 b :: .i32 a :: s, locs, jh, hp⟩ =
      if b.toBitVec.sle a.toBitVec then Jvm.runJvmRes (algKotlinHooksWith ip) f prog ⟨t, s, locs, jh, hp⟩
      else Jvm.runJvmRes (algKotlinHooksWith ip) f prog ⟨pc + 1, s, locs, jh, hp⟩ := by
  simp only [Jvm.runJvmRes, hget]
  rfl

theorem res_ifeq {f pc t : Nat} {prog : List JvmInstr} {v : UInt32}
    {s : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hget : prog[pc]? = some (.ifeq t)) :
    Jvm.runJvmRes (algKotlinHooksWith ip) (f + 1) prog ⟨pc, .i32 v :: s, locs, jh, hp⟩ =
      if v = 0 then Jvm.runJvmRes (algKotlinHooksWith ip) f prog ⟨t, s, locs, jh, hp⟩
      else Jvm.runJvmRes (algKotlinHooksWith ip) f prog ⟨pc + 1, s, locs, jh, hp⟩ := by
  simp only [Jvm.runJvmRes, hget]
  have hz : (algKotlinHooksWith ip).isZero? (.i32 v) = some (v == 0) := rfl
  rw [hz]
  by_cases h : v = 0
  · subst h; rfl
  · rw [beq_false_of_ne h]; simp only [h, ↓reduceIte]

theorem res_ifne {f pc t : Nat} {prog : List JvmInstr} {v : UInt32}
    {s : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hget : prog[pc]? = some (.ifne t)) :
    Jvm.runJvmRes (algKotlinHooksWith ip) (f + 1) prog ⟨pc, .i32 v :: s, locs, jh, hp⟩ =
      if v = 0 then Jvm.runJvmRes (algKotlinHooksWith ip) f prog ⟨pc + 1, s, locs, jh, hp⟩
      else Jvm.runJvmRes (algKotlinHooksWith ip) f prog ⟨t, s, locs, jh, hp⟩ := by
  simp only [Jvm.runJvmRes, hget]
  have hz : (algKotlinHooksWith ip).isZero? (.i32 v) = some (v == 0) := rfl
  rw [hz]
  by_cases h : v = 0
  · subst h; rfl
  · rw [beq_false_of_ne h]; simp only [h, ↓reduceIte]

theorem res_ifeq_z {f pc t : Nat} {prog : List JvmInstr}
    {s : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hget : prog[pc]? = some (.ifeq t)) :
    Jvm.runJvmRes (algKotlinHooksWith ip) (f + 1) prog ⟨pc, .i32 0 :: s, locs, jh, hp⟩ =
      Jvm.runJvmRes (algKotlinHooksWith ip) f prog ⟨t, s, locs, jh, hp⟩ := by
  rw [res_ifeq hget]; rfl

theorem res_ifeq_nz {f pc t : Nat} {prog : List JvmInstr} {v : UInt32}
    {s : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hget : prog[pc]? = some (.ifeq t)) (h : v ≠ 0) :
    Jvm.runJvmRes (algKotlinHooksWith ip) (f + 1) prog ⟨pc, .i32 v :: s, locs, jh, hp⟩ =
      Jvm.runJvmRes (algKotlinHooksWith ip) f prog ⟨pc + 1, s, locs, jh, hp⟩ := by
  rw [res_ifeq hget]; simp only [h, ↓reduceIte]

theorem res_ifne_z {f pc t : Nat} {prog : List JvmInstr}
    {s : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hget : prog[pc]? = some (.ifne t)) :
    Jvm.runJvmRes (algKotlinHooksWith ip) (f + 1) prog ⟨pc, .i32 0 :: s, locs, jh, hp⟩ =
      Jvm.runJvmRes (algKotlinHooksWith ip) f prog ⟨pc + 1, s, locs, jh, hp⟩ := by
  rw [res_ifne hget]; rfl

theorem res_ifne_nz {f pc t : Nat} {prog : List JvmInstr} {v : UInt32}
    {s : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hget : prog[pc]? = some (.ifne t)) (h : v ≠ 0) :
    Jvm.runJvmRes (algKotlinHooksWith ip) (f + 1) prog ⟨pc, .i32 v :: s, locs, jh, hp⟩ =
      Jvm.runJvmRes (algKotlinHooksWith ip) f prog ⟨t, s, locs, jh, hp⟩ := by
  rw [res_ifne hget]; simp only [h, ↓reduceIte]

theorem res_step {H : Jvm.JvmHooks AlgExt AlgHeap} {f : Nat} {prog : List JvmInstr} {st st' : JvmState}
    {instr : JvmInstr} (hget : prog[st.pc]? = some instr) (hnbr : Jvm.isBranchInstr instr = false)
    (hs : Jvm.stepInstr H instr st = .inl (some st')) :
    Jvm.runJvmRes H (f + 1) prog st = Jvm.runJvmRes H f prog st' := by
  rw [Jvm.runJvmRes_nonbranch H f prog st instr hget hnbr, hs]

theorem res_stop {H : Jvm.JvmHooks AlgExt AlgHeap} {f : Nat} {prog : List JvmInstr} {st : JvmState}
    {instr : JvmInstr} (hget : prog[st.pc]? = some instr) (hnbr : Jvm.isBranchInstr instr = false)
    (hs : Jvm.stepInstr H instr st = .inr none) :
    Jvm.runJvmRes H (f + 1) prog st = none := by
  rw [Jvm.runJvmRes_nonbranch H f prog st instr hget hnbr, hs]

theorem res_goto {f pc t : Nat} {prog : List JvmInstr}
    {s : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hget : prog[pc]? = some (.goto t)) :
    Jvm.runJvmRes (algKotlinHooksWith ip) (f + 1) prog ⟨pc, s, locs, jh, hp⟩ =
      Jvm.runJvmRes (algKotlinHooksWith ip) f prog ⟨t, s, locs, jh, hp⟩ := by
  simp only [Jvm.runJvmRes, hget]
  rfl

end Res

/-- One non-branch step of the reference interpreter whose effect is computed by `dsimp`. -/
macro "mcc_res_nb" : tactic => `(tactic| (
  first
    | rw [res_stop (by rfl) (by rfl) (by rfl)]
    | (rw [res_step (by rfl) (by rfl) (by rfl)]
       try simp (disch := decide) only [setLocal_apply_self, setLocal_apply_ne])))

/-- Steps the reference interpreter through non-branch instructions and branches on constants. -/
macro "mcc_res_auto" : tactic => `(tactic| repeat (first
  | (rw [res_ifeq_z (by rfl)])
  | (rw [res_ifeq_nz (by rfl) (by decide)])
  | (rw [res_ifne_z (by rfl)])
  | (rw [res_ifne_nz (by rfl) (by decide)])
  | (rw [res_goto (by rfl)])
  | mcc_res_nb))

theorem mcc_ite_pos {α : Type} {c : Prop} [Decidable c] (h : c) (a b : α) : (if c then a else b) = a := by
  simp [h]

theorem mcc_ite_neg {α : Type} {c : Prop} [Decidable c] (h : ¬c) (a b : α) : (if c then a else b) = b := by
  simp [h]

/-! ### Signed range checks -/

theorem u32_slt0 (u : UInt32) : u.toBitVec.slt (UInt32.toBitVec 0) = decide (2 ^ 31 ≤ u.toNat) := by
  have := u.toNat_lt_size
  simp only [BitVec.slt, BitVec.toInt_eq_toNat_cond, UInt32.toNat_toBitVec]
  simp only [UInt32.size] at this
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, show (0 : UInt32).toNat = 0 from rfl]
  by_cases h : 2 * u.toNat < 2 ^ 32 <;> simp only [h, ite_true, ite_false] <;> omega

theorem u32_sle8 (u : UInt32) :
    (UInt32.toBitVec 8).sle u.toBitVec = decide (8 ≤ u.toNat ∧ u.toNat < 2 ^ 31) := by
  have := u.toNat_lt_size
  simp only [BitVec.sle, BitVec.toInt_eq_toNat_cond, UInt32.toNat_toBitVec]
  simp only [UInt32.size] at this
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, show (8 : UInt32).toNat = 8 from rfl]
  by_cases h : 2 * u.toNat < 2 ^ 32 <;> simp only [h, ite_true, ite_false] <;> omega

theorem i32_inRange_iff (x : Int32) : (0 ≤ x.toInt ∧ x.toInt < 8) ↔ x.toUInt32.toNat < 8 := by
  have h1 : x.toInt = x.toBitVec.toInt := rfl
  have h2 : x.toUInt32.toNat = x.toBitVec.toNat := rfl
  have := x.toBitVec.isLt
  rw [h1, h2, BitVec.toInt_eq_toNat_cond]
  split <;> omega

theorem u32_inRange_branches (u : UInt32) (h : u.toNat < 8) :
    u.toBitVec.slt (0 : UInt32).toBitVec = false ∧ (8 : UInt32).toBitVec.sle u.toBitVec = false := by
  have := u.toNat_lt_size
  simp only [BitVec.slt, BitVec.sle, BitVec.toInt_eq_toNat_cond, UInt32.toNat_toBitVec, decide_eq_false_iff_not]
  simp
  omega

/-! ### `cellToLeafBit` -/

/-- In range, `cellToLeafBit(u, v)` returns `cellToLeafBitUInt u v` and leaves both heaps unchanged. -/
theorem cellToLeafBit_fast_ok (ip : InvokeProg) (k : Nat) (u v : UInt32) (hu : u.toNat < 8) (hv : v.toNat < 8)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    ∃ pc stk locs,
      Jvm.runJvmResFast (algKotlinHooksWith ip) (k + 45) MacroCellCoordinatesKt_cellToLeafBit_prog 0 MacroCellCoordinatesKt_cellToLeafBit_prog
          (Jvm.initJvmState [(0, .i32 u), (1, .i32 v)] (.i32 0) hp jh) =
        some (.i32 (Algorithm.cellToLeafBitUInt u v), ⟨pc, stk, locs, jh, hp⟩) := by
  have hx := u32_inRange_branches _ hu
  have hy := u32_inRange_branches _ hv
  refine ⟨?pc, ?stk, ?locs, ?main⟩
  case main =>
  conv => lhs; arg 5; dsimp only [MacroCellCoordinatesKt_cellToLeafBit_prog]
  mcc_step_blk
  refine (fast_if_icmpgt_fall hx.1).trans ?_
  mcc_step_blk
  refine (fast_if_icmpge_fall hx.2).trans ?_
  mcc_step_blk
  mcc_branch
  mcc_step_blk
  refine (fast_if_icmpgt_fall hy.1).trans ?_
  mcc_step_blk
  refine (fast_if_icmpge_fall hy.2).trans ?_
  mcc_step_blk
  mcc_branch
  mcc_step_blk
  mcc_branch
  mcc_step_blk
  mcc_rfl_step
  mcc_rfl_step
  mcc_rfl_step
  exact fast_ireturn

theorem cellToLeafBitModel_some_of (x y : Int32) (b : UInt32) (hb : cellToLeafBitModel x y = some b) :
    x.toUInt32.toNat < 8 ∧ y.toUInt32.toNat < 8 ∧ Algorithm.cellToLeafBitUInt x.toUInt32 y.toUInt32 = b := by
  have hrange : 0 ≤ x.toInt ∧ x.toInt < 8 ∧ 0 ≤ y.toInt ∧ y.toInt < 8 := by
    by_cases hc : 0 ≤ x.toInt ∧ x.toInt < 8 ∧ 0 ≤ y.toInt ∧ y.toInt < 8
    · exact hc
    · simp [cellToLeafBitModel, hc] at hb
  refine ⟨(i32_inRange_iff x).1 ⟨hrange.1, hrange.2.1⟩, (i32_inRange_iff y).1 ⟨hrange.2.2.1, hrange.2.2.2⟩, ?_⟩
  simpa [cellToLeafBitModel, hrange] using hb

theorem cellToLeafBit_res_none (ip : InvokeProg) (k : Nat)
    (x y : Int32) (hb : cellToLeafBitModel x y = none)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
      Jvm.runJvmRes (algKotlinHooksWith ip) (k + 45) MacroCellCoordinatesKt_cellToLeafBit_prog
          (Jvm.initJvmState [(0, .i32 x.toUInt32), (1, .i32 y.toUInt32)] (.i32 0) hp jh) = none := by
  have hn : ¬ (x.toUInt32.toNat < 8 ∧ y.toUInt32.toNat < 8) := by
    intro h
    have hx := (i32_inRange_iff x).2 h.1
    have hy := (i32_inRange_iff y).2 h.2
    simp [cellToLeafBitModel, hx, hy] at hb
  dsimp only [Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
  mcc_res_auto
  rw [res_if_icmpgt (by rfl), u32_slt0]
  by_cases hx0 : 2 ^ 31 ≤ x.toUInt32.toNat
  · simp only [hx0, decide_true, ite_true]
    mcc_res_auto
  simp only [hx0, decide_false, Bool.false_eq_true, ite_false]
  mcc_res_auto
  rw [res_if_icmpge (by rfl), u32_sle8]
  by_cases hx8 : 8 ≤ x.toUInt32.toNat
  · rw [mcc_ite_pos (by simp only [decide_eq_true_eq]; omega)]
    mcc_res_auto
  rw [mcc_ite_neg (by simp only [decide_eq_true_eq]; omega)]
  mcc_res_auto
  rw [res_if_icmpgt (by rfl), u32_slt0]
  by_cases hy0 : 2 ^ 31 ≤ y.toUInt32.toNat
  · simp only [hy0, decide_true, ite_true]
    mcc_res_auto
  simp only [hy0, decide_false, Bool.false_eq_true, ite_false]
  mcc_res_auto
  rw [res_if_icmpge (by rfl), u32_sle8]
  by_cases hy8 : 8 ≤ y.toUInt32.toNat
  · rw [mcc_ite_pos (by simp only [decide_eq_true_eq]; omega)]
    mcc_res_auto
  exact absurd ⟨by omega, by omega⟩ hn

/-- Every `mkAlgKotlinHooks` is an `algKotlinHooksWith`. -/
theorem mkAlgKotlinHooks_eq_with (rp : String → Option (List JvmInstr)) (d sf : Nat) :
    ∃ ip, mkAlgKotlinHooks rp d sf = algKotlinHooksWith ip := by
  cases d <;> exact ⟨_, rfl⟩

/--
`cellToLeafBit(x, y)` on the JVM computes `cellToLeafBitModel x y`: in range it returns the Morton bit index and
leaves both heaps unchanged; out of range the `require` throws (`none`).
-/
theorem cellToLeafBit_equiv (rp : String → Option (List JvmInstr)) (d sf fuel : Nat) (hf : 45 ≤ fuel)
    (x y : Int32) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    (Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) fuel MacroCellCoordinatesKt_cellToLeafBit_prog
        (Jvm.initJvmState [(0, .i32 x.toUInt32), (1, .i32 y.toUInt32)] (.i32 0) hp jh)).map
        (fun r => (r.1, r.2.jvmHeap, r.2.heap)) =
      (cellToLeafBitModel x y).map (fun b => (.i32 b, jh, hp)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  obtain ⟨ip, hip⟩ := mkAlgKotlinHooks_eq_with rp d sf
  rw [hip]
  cases hb : cellToLeafBitModel x y with
  | none => rw [cellToLeafBit_res_none ip k x y hb jh hp]; rfl
  | some b =>
    obtain ⟨hu, hv, hbv⟩ := cellToLeafBitModel_some_of x y b hb
    obtain ⟨pc, stk, locs, h⟩ := cellToLeafBit_fast_ok ip k _ _ hu hv jh hp
    rw [Jvm.runJvmRes_of_runJvmResFast0 _ _ _ _ _ rfl h, hbv]
    rfl

/-! ### Calls into lifted `MacroCellCoordinatesKt` methods -/

/-- `invokestatic MacroCellCoordinatesKt.<method>` under `mkAlgKotlinHooks rp (d1 + 1) sf` runs the lifted callee. -/
theorem stepMccStatic {rp : String → Option (List JvmInstr)} {d1 sf : Nat} {st : JvmState}
    {method desc : String} (tags : List Char) {args stkRest : List JvmVal} {res : JvmVal} {endSt : JvmState}
    {prog : List JvmInstr}
    (htags : Jvm.parseMethodParamTags desc = tags)
    (hlen : args.length = tags.length)
    (hstk : st.stack = args.reverse ++ stkRest)
    (hprog : rp ("MacroCellCoordinatesKt." ++ method ++ ":" ++ desc) = some prog)
    (hrun : Jvm.runJvmRes (mkAlgKotlinHooks rp d1 sf) sf prog
        { pc := 0, stack := [],
          locals := (algKotlinParamSlots 0 tags args).foldl (fun loc (i, v) => setLocal loc i v) (fun _ => .i32 0),
          jvmHeap := st.jvmHeap, heap := st.heap } = some (res, endSt))
    (hv : desc.endsWith ")V" = false) :
    Jvm.stepInvokeStaticGeneric (mkAlgKotlinHooks rp (d1 + 1) sf) st "MacroCellCoordinatesKt" method desc =
      .inl (some { st with
        pc := st.pc + 1, stack := res :: stkRest, jvmHeap := endSt.jvmHeap, heap := endSt.heap }) := by
  have hE : Jvm.stepInvokeStaticGeneric (mkAlgKotlinHooks rp (d1 + 1) sf) st "MacroCellCoordinatesKt" method desc =
      (mkAlgKotlinHooks rp (d1 + 1) sf).stepInvokeStatic st "MacroCellCoordinatesKt" method desc := rfl
  rw [hE]
  have hl : isAlgKotlinLiftedClass "MacroCellCoordinatesKt" = true := rfl
  have htag : algKotlinTag "MacroCellCoordinatesKt" method desc =
      "MacroCellCoordinatesKt." ++ method ++ ":" ++ desc := by
    simp only [algKotlinTag, String.append_assoc]; rfl
  have hlt : ¬ (args.reverse ++ stkRest).length < tags.length := by simp [hlen]
  have htake : ((args.reverse ++ stkRest).take tags.length).reverse = args := by
    rw [← hlen, List.take_left' (by simp), List.reverse_reverse]
  have hdrop : (args.reverse ++ stkRest).drop tags.length = stkRest := by
    rw [← hlen, List.drop_left' (by simp)]
  dsimp only [mkAlgKotlinHooks, algKotlinHooksWith]
  simp only [hl, ↓reduceIte, hstk, htags, hlt, htake, hdrop, htag, hprog, Option.map_some]
  rw [hrun]
  simp only [algKotlinAfterCall, hv, Bool.false_eq_true, ↓reduceIte]

set_option maxRecDepth 4096 in
theorem tags_II : Jvm.parseMethodParamTags "(II)I" = ['I', 'I'] := by decide

/-- A call of the lifted `cellToLeafBit` with in-range arguments pushes `cellToLeafBitUInt u v`. -/
theorem fast_call_cellToLeafBit {rp : String → Option (List JvmInstr)} {d1 sf : Nat}
    (hres : ResolvesMccProgs rp) (hsf : 45 ≤ sf)
    {f pc pc0 : Nat} {prog rest : List JvmInstr} {u v : UInt32} (hu : u.toNat < 8) (hv : v.toNat < 8)
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    Jvm.runJvmResFast (mkAlgKotlinHooks rp (d1 + 1) sf) (f + 1) prog pc
        (.invokestatic "com/alexvanyo/composelife/algorithm/MacroCellCoordinatesKt" "cellToLeafBit" "(II)I" :: rest)
        ⟨pc0, .i32 v :: .i32 u :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkAlgKotlinHooks rp (d1 + 1) sf) f prog (pc + 1) rest
        ⟨pc + 1, .i32 (Algorithm.cellToLeafBitUInt u v) :: stk, locs, jh, hp⟩ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hsf
  obtain ⟨ip, hip⟩ := mkAlgKotlinHooks_eq_with rp d1 (k + 45)
  obtain ⟨epc, estk, elocs, h⟩ := cellToLeafBit_fast_ok ip k u v hu hv jh hp
  have hrun := Jvm.runJvmRes_of_runJvmResFast0 _ _ _ _ _ rfl h
  rw [← hip] at hrun
  exact Jvm.runJvmResFast_invokestatic_step _
    (stepMccStatic (st := ⟨pc, .i32 v :: .i32 u :: stk, locs, jh, hp⟩) (method := "cellToLeafBit")
      (stkRest := stk) (endSt := ⟨epc, estk, elocs, jh, hp⟩)
      ['I', 'I'] (args := [.i32 u, .i32 v]) tags_II rfl rfl hres.1 hrun (by decide +kernel))

/-! ### Value and heap helpers -/

theorem intOffsetX_pack (x y : UInt32) : intOffsetX (packIntOffset x y) = x := by
  unfold intOffsetX packIntOffset
  apply UInt32.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi, show 32 + i < 64 by omega, show i < 64 by omega]

theorem intOffsetY_pack (x y : UInt32) : intOffsetY (packIntOffset x y) = y := by
  unfold intOffsetY packIntOffset
  apply UInt32.toBitVec_inj.mp
  simp

theorem nat_and63_mod (n : Nat) : (n &&& 63) % 64 = n % 64 := by
  rw [show (63 : Nat) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem shl_and63 (a : UInt64) (b : UInt32) : a <<< (b &&& 63).toUInt64 = a <<< b.toUInt64 := by
  apply UInt64.toBitVec_inj.mp
  simp [nat_and63_mod]

theorem ushr_and63 (a : UInt64) (b : UInt32) : a >>> (b &&& 63).toUInt64 = a >>> b.toUInt64 := by
  apply UInt64.toBitVec_inj.mp
  simp [nat_and63_mod]

theorem int32_sub_toUInt32 (a b : Int32) : (a - b).toUInt32 = a.toUInt32 - b.toUInt32 := by simp

theorem heap_get_alloc_lt {jh : Jvm.JvmHeap AlgExt} (obj : Jvm.HeapObj AlgExt) {addr : Nat}
    (hlt : addr < jh.objects.size) : (jh.alloc obj).2.get? addr = jh.get? addr := by
  dsimp only [Jvm.JvmHeap.alloc, Jvm.JvmHeap.get?]
  rw [Array.getElem?_push_lt hlt, Array.getElem?_eq_getElem hlt]

theorem heap_get_alloc_self (jh : Jvm.JvmHeap AlgExt) (obj : Jvm.HeapObj AlgExt) :
    (jh.alloc obj).2.get? jh.objects.size = some obj := by
  dsimp only [Jvm.JvmHeap.alloc, Jvm.JvmHeap.get?]
  simp

theorem heap_alloc_set_self (jh : Jvm.JvmHeap AlgExt) (o1 o2 : Jvm.HeapObj AlgExt) :
    (jh.alloc o1).2.set jh.objects.size o2 = (jh.alloc o2).2 := by
  simp [Jvm.JvmHeap.alloc, Jvm.JvmHeap.set, Array.set_push]

theorem algKotlinColl_arr {jh : Jvm.JvmHeap AlgExt} {addr arrAddr : Nat} {cls ec : String} {es : Array JvmVal}
    (h : algKotlinColl? jh addr = some (cls, arrAddr, ec, es)) : jh.get? arrAddr = some (.objArray ec es) := by
  unfold algKotlinColl? at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  · rename_i heq
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact heq

/-- The iterator that `Set.iterator()` allocates over the backing array `arrAddr`, at position `idx`. -/
def iterObj (arrAddr idx : Nat) : Jvm.HeapObj AlgExt :=
  .instance "java/util/Iterator" [("arr", .heapRef arrAddr), ("idx", .i32 (UInt32.ofNat idx))]

theorem fast_set_iterator {ip : InvokeProg} {f pc pc0 addr arrAddr : Nat} {cls ec : String} {es : Array JvmVal}
    {prog rest : List JvmInstr} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hcoll : algKotlinColl? jh addr = some (cls, arrAddr, ec, es)) :
    Jvm.runJvmResFast (algKotlinHooksWith ip) (f + 1) prog pc
        (.invokeinterface "java/util/Set" "iterator" "()Ljava/util/Iterator;" :: rest)
        ⟨pc0, .heapRef addr :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (algKotlinHooksWith ip) f prog (pc + 1) rest
        ⟨pc + 1, .heapRef jh.objects.size :: stk, locs, (jh.alloc (iterObj arrAddr 0)).2, hp⟩ := by
  refine Jvm.runJvmResFast_invokeinterface_step _ ?_
  have hE : Jvm.stepInvokeInterfaceGeneric (algKotlinHooksWith ip) ⟨pc, .heapRef addr :: stk, locs, jh, hp⟩
      "java/util/Set" "iterator" "()Ljava/util/Iterator;" =
      algKotlinStepInterfaceLeaf ⟨pc, .heapRef addr :: stk, locs, jh, hp⟩
        "java/util/Set" "iterator" "()Ljava/util/Iterator;" := rfl
  rw [hE]
  unfold algKotlinStepInterfaceLeaf
  simp only [hcoll]
  rfl

theorem fast_iter_hasNext {H : Jvm.JvmHooks AlgExt AlgHeap} {f pc pc0 itAddr arrAddr idx : Nat} {ec : String}
    {es : Array JvmVal} {prog rest : List JvmInstr} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hit : jh.get? itAddr = some (iterObj arrAddr idx)) (harr : jh.get? arrAddr = some (.objArray ec es))
    (h32 : idx < 2 ^ 32) :
    Jvm.runJvmResFast H (f + 1) prog pc (.invokeinterface "java/util/Iterator" "hasNext" "()Z" :: rest)
        ⟨pc0, .heapRef itAddr :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast H f prog (pc + 1) rest
        ⟨pc + 1, .i32 (if idx < es.size then 1 else 0) :: stk, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_invokeinterface_step _ ?_
  simp [Jvm.stepInvokeInterfaceGeneric, hit, harr, iterObj, Nat.mod_eq_of_lt h32]

theorem fast_iter_next {H : Jvm.JvmHooks AlgExt AlgHeap} {f pc pc0 itAddr arrAddr idx : Nat} {ec : String}
    {es : Array JvmVal} {prog rest : List JvmInstr} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hit : jh.get? itAddr = some (iterObj arrAddr idx)) (harr : jh.get? arrAddr = some (.objArray ec es))
    (hlt : idx < es.size) (h32 : idx < 2 ^ 32) :
    Jvm.runJvmResFast H (f + 1) prog pc (.invokeinterface "java/util/Iterator" "next" "()Ljava/lang/Object;" :: rest)
        ⟨pc0, .heapRef itAddr :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast H f prog (pc + 1) rest
        ⟨pc + 1, es[idx] :: stk, locs, jh.set itAddr (iterObj arrAddr (idx + 1)), hp⟩ := by
  refine Jvm.runJvmResFast_invokeinterface_step _ ?_
  have hadd : UInt32.ofNat idx + 1 = UInt32.ofNat (idx + 1) := by rw [UInt32.ofNat_add]; rfl
  have hn : (UInt32.ofNat idx).toNat = idx := by simp [Nat.mod_eq_of_lt h32]
  have hlt' : (UInt32.ofNat idx).toNat < es.size := by rw [hn]; exact hlt
  have hs : ("arr" == "idx") = false := by decide +kernel
  unfold iterObj at hit
  dsimp only [Jvm.stepInvokeInterfaceGeneric]
  simp only [hit, List.find?, beq_self_eq_true, Option.map_some, hs]
  rw [harr]
  simp only [hn, hadd, iterObj, hlt, dite_true]

/-! ### `coordinatesToLeaf` -/

/-- One step of `coordinatesToLeafModel`'s fold. -/
def leafStep (ox oy : Int32) (acc : UInt64) (p : Int32 × Int32) : UInt64 :=
  match cellToLeafBitModel (p.1 - ox) (p.2 - oy) with
  | some bit => acc ||| ((1 : UInt64) <<< bit.toUInt64)
  | none => acc

theorem coordinatesToLeafModel_eq_foldl (coords : List (Int32 × Int32)) (ox oy : Int32) :
    coordinatesToLeafModel coords ox oy = coords.foldl (leafStep ox oy) 0 := rfl

/-- The loop locals of `coordinatesToLeaf` over arbitrary other slots `L`. -/
abbrev lpLocs (L : Nat → JvmVal) (ox oy : UInt32) (acc : UInt64) (it : Nat) : Nat → JvmVal :=
  setLocal (setLocal (setLocal (setLocal L 1 (.i32 ox)) 2 (.i32 oy)) 3 (.i64 acc)) 5 (.heapRef it)

theorem lpLocs_absorb {L : Nat → JvmVal} {ox oy : UInt32} {acc : UInt64} {it : Nat}
    (h1 : L 1 = .i32 ox) (h2 : L 2 = .i32 oy) (h3 : L 3 = .i64 acc) (h5 : L 5 = .heapRef it) :
    lpLocs L ox oy acc it = L := by
  funext i
  simp only [lpLocs, setLocal]
  split
  · subst_vars; exact h5.symm
  split
  · subst_vars; exact h3.symm
  split
  · subst_vars; exact h2.symm
  split
  · subst_vars; exact h1.symm
  rfl

/-- The locals of `coordinatesToLeaf` at pc 40, after unpacking the element `pk` into `localX`/`localY`. -/
abbrev headLocs (L : Nat → JvmVal) (pk : UInt64) (dx dy : UInt32) : Nat → JvmVal :=
  setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal L
    6 (.i64 pk)) 9 (.i64 pk)) 11 (.i32 0)) 8 (.i32 (intOffsetX pk))) 10 (.i64 pk)) 12 (.i32 0))
    9 (.i32 (intOffsetY pk))) 10 (.i32 dx)) 11 (.i32 dy)

theorem coordsLeaf_head {rp : String → Option (List JvmInstr)} {d1 sf : Nat}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {arrAddr : Nat} {ec : String} {es : Array JvmVal}
    (harr : jh.get? arrAddr = some (.objArray ec es)) (harrLt : arrAddr < jh.objects.size)
    (k : Nat) (hk : k < es.size) (hk32 : k + 1 < 2 ^ 32) (p : Int32 × Int32)
    (hel : es[k] = .ext (.intOffset (packCoord p))) (L : Nat → JvmVal) (ox oy : UInt32) (acc : UInt64)
    (f : Nat) :
    Jvm.runJvmResFast (mkAlgKotlinHooks rp (d1 + 1) sf) (f + 33) MacroCellCoordinatesKt_coordinatesToLeaf_prog 8
        (MacroCellCoordinatesKt_coordinatesToLeaf_prog.drop 8)
        ⟨8, [], lpLocs L ox oy acc jh.objects.size, (jh.alloc (iterObj arrAddr k)).2, hp⟩ =
      Jvm.runJvmResFast (mkAlgKotlinHooks rp (d1 + 1) sf) (f + 1) MacroCellCoordinatesKt_coordinatesToLeaf_prog 40
        (MacroCellCoordinatesKt_coordinatesToLeaf_prog.drop 40)
        ⟨40, [.i32 (intOffsetX (packCoord p) - ox), .i32 0],
          headLocs (lpLocs L ox oy acc jh.objects.size) (packCoord p) (intOffsetX (packCoord p) - ox)
            (intOffsetY (packCoord p) - oy),
          (jh.alloc (iterObj arrAddr (k + 1))).2, hp⟩ := by
  have hit : (jh.alloc (iterObj arrAddr k)).2.get? jh.objects.size = some (iterObj arrAddr k) :=
    heap_get_alloc_self _ _
  have harr' : (jh.alloc (iterObj arrAddr k)).2.get? arrAddr = some (.objArray ec es) := by
    rw [heap_get_alloc_lt _ harrLt, harr]
  mcc_step_blk
  refine (fast_iter_hasNext hit harr' (by omega)).trans ?_
  simp only [hk, ↓reduceIte]
  mcc_branch
  mcc_step_blk
  refine (fast_iter_next hit harr' hk (by omega)).trans ?_
  rw [hel, heap_alloc_set_self]
  mcc_rfl_step
  mcc_rfl_step
  mcc_rfl_step
  mcc_rfl_step
  rfl

section Tails

variable {rp : String → Option (List JvmInstr)} {d1 sf : Nat} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
  (L : Nat → JvmVal) (pk : UInt64) (dx dy : UInt32) (f : Nat)

theorem coordsLeaf_tail_x0 (hx : 2 ^ 31 ≤ dx.toNat) :
    Jvm.runJvmResFast (mkAlgKotlinHooks rp (d1 + 1) sf) (f + 3) MacroCellCoordinatesKt_coordinatesToLeaf_prog 40
        (MacroCellCoordinatesKt_coordinatesToLeaf_prog.drop 40) ⟨40, [.i32 dx, .i32 0], headLocs L pk dx dy, jh, hp⟩ =
      Jvm.runJvmResFast (mkAlgKotlinHooks rp (d1 + 1) sf) f MacroCellCoordinatesKt_coordinatesToLeaf_prog 8
        (MacroCellCoordinatesKt_coordinatesToLeaf_prog.drop 8) ⟨8, [], headLocs L pk dx dy, jh, hp⟩ := by
  mcc_step_blk
  refine (fast_if_icmpgt_jump (by rw [u32_slt0]; simpa using hx)).trans ?_
  mcc_step_blk
  mcc_branch

theorem coordsLeaf_tail_x8 (hx0 : ¬ 2 ^ 31 ≤ dx.toNat) (hx : 8 ≤ dx.toNat) :
    Jvm.runJvmResFast (mkAlgKotlinHooks rp (d1 + 1) sf) (f + 7) MacroCellCoordinatesKt_coordinatesToLeaf_prog 40
        (MacroCellCoordinatesKt_coordinatesToLeaf_prog.drop 40) ⟨40, [.i32 dx, .i32 0], headLocs L pk dx dy, jh, hp⟩ =
      Jvm.runJvmResFast (mkAlgKotlinHooks rp (d1 + 1) sf) f MacroCellCoordinatesKt_coordinatesToLeaf_prog 8
        (MacroCellCoordinatesKt_coordinatesToLeaf_prog.drop 8) ⟨8, [], headLocs L pk dx dy, jh, hp⟩ := by
  mcc_step_blk
  refine (fast_if_icmpgt_fall (by rw [u32_slt0]; simpa using hx0)).trans ?_
  mcc_step_blk
  refine (fast_if_icmpge_jump (by rw [u32_sle8]; simp only [decide_eq_true_eq]; omega)).trans ?_
  mcc_step_blk
  mcc_branch

theorem coordsLeaf_tail_y0 (hx : dx.toNat < 8) (hy : 2 ^ 31 ≤ dy.toNat) :
    Jvm.runJvmResFast (mkAlgKotlinHooks rp (d1 + 1) sf) (f + 12) MacroCellCoordinatesKt_coordinatesToLeaf_prog 40
        (MacroCellCoordinatesKt_coordinatesToLeaf_prog.drop 40) ⟨40, [.i32 dx, .i32 0], headLocs L pk dx dy, jh, hp⟩ =
      Jvm.runJvmResFast (mkAlgKotlinHooks rp (d1 + 1) sf) f MacroCellCoordinatesKt_coordinatesToLeaf_prog 8
        (MacroCellCoordinatesKt_coordinatesToLeaf_prog.drop 8) ⟨8, [], headLocs L pk dx dy, jh, hp⟩ := by
  have hb := u32_inRange_branches _ hx
  mcc_step_blk
  refine (fast_if_icmpgt_fall hb.1).trans ?_
  mcc_step_blk
  refine (fast_if_icmpge_fall hb.2).trans ?_
  mcc_step_blk
  mcc_branch
  mcc_step_blk
  refine (fast_if_icmpgt_jump (by rw [u32_slt0]; simpa using hy)).trans ?_
  mcc_step_blk
  mcc_branch

theorem coordsLeaf_tail_y8 (hx : dx.toNat < 8) (hy0 : ¬ 2 ^ 31 ≤ dy.toNat) (hy : 8 ≤ dy.toNat) :
    Jvm.runJvmResFast (mkAlgKotlinHooks rp (d1 + 1) sf) (f + 16) MacroCellCoordinatesKt_coordinatesToLeaf_prog 40
        (MacroCellCoordinatesKt_coordinatesToLeaf_prog.drop 40) ⟨40, [.i32 dx, .i32 0], headLocs L pk dx dy, jh, hp⟩ =
      Jvm.runJvmResFast (mkAlgKotlinHooks rp (d1 + 1) sf) f MacroCellCoordinatesKt_coordinatesToLeaf_prog 8
        (MacroCellCoordinatesKt_coordinatesToLeaf_prog.drop 8) ⟨8, [], headLocs L pk dx dy, jh, hp⟩ := by
  have hb := u32_inRange_branches _ hx
  mcc_step_blk
  refine (fast_if_icmpgt_fall hb.1).trans ?_
  mcc_step_blk
  refine (fast_if_icmpge_fall hb.2).trans ?_
  mcc_step_blk
  mcc_branch
  mcc_step_blk
  refine (fast_if_icmpgt_fall (by rw [u32_slt0]; simpa using hy0)).trans ?_
  mcc_step_blk
  refine (fast_if_icmpge_jump (by rw [u32_sle8]; simp only [decide_eq_true_eq]; omega)).trans ?_
  mcc_step_blk
  mcc_branch

theorem coordsLeaf_tail_in (hres : ResolvesMccProgs rp) (hsf : 45 ≤ sf) (ox oy : UInt32) (acc : UInt64)
    (it : Nat) (hx : dx.toNat < 8) (hy : dy.toNat < 8) :
    Jvm.runJvmResFast (mkAlgKotlinHooks rp (d1 + 1) sf) (f + 27) MacroCellCoordinatesKt_coordinatesToLeaf_prog 40
        (MacroCellCoordinatesKt_coordinatesToLeaf_prog.drop 40)
        ⟨40, [.i32 dx, .i32 0], headLocs (lpLocs L ox oy acc it) pk dx dy, jh, hp⟩ =
      Jvm.runJvmResFast (mkAlgKotlinHooks rp (d1 + 1) sf) f MacroCellCoordinatesKt_coordinatesToLeaf_prog 8
        (MacroCellCoordinatesKt_coordinatesToLeaf_prog.drop 8)
        ⟨8, [], setLocal (setLocal (headLocs (lpLocs L ox oy acc it) pk dx dy)
          12 (.i32 (Algorithm.cellToLeafBitUInt dx dy)))
          3 (.i64 (acc ||| (1 : UInt64) <<< (Algorithm.cellToLeafBitUInt dx dy).toUInt64)), jh, hp⟩ := by
  have hbx := u32_inRange_branches _ hx
  have hby := u32_inRange_branches _ hy
  mcc_step_blk
  refine (fast_if_icmpgt_fall hbx.1).trans ?_
  mcc_step_blk
  refine (fast_if_icmpge_fall hbx.2).trans ?_
  mcc_step_blk
  mcc_branch
  mcc_step_blk
  refine (fast_if_icmpgt_fall hby.1).trans ?_
  mcc_step_blk
  refine (fast_if_icmpge_fall hby.2).trans ?_
  mcc_step_blk
  mcc_branch
  mcc_step_blk
  refine (fast_call_cellToLeafBit hres hsf hx hy).trans ?_
  mcc_step_blk
  mcc_branch
  rw [shl_and63]
  rfl

end Tails

theorem cellToLeafBitModel_of_lt (x y : Int32) (hx : x.toUInt32.toNat < 8) (hy : y.toUInt32.toNat < 8) :
    cellToLeafBitModel x y = some (Algorithm.cellToLeafBitUInt x.toUInt32 y.toUInt32) := by
  have h1 := (i32_inRange_iff x).2 hx
  have h2 := (i32_inRange_iff y).2 hy
  simp [cellToLeafBitModel, h1, h2]

theorem cellToLeafBitModel_of_not (x y : Int32) (h : ¬ (x.toUInt32.toNat < 8 ∧ y.toUInt32.toNat < 8)) :
    cellToLeafBitModel x y = none := by
  have : ¬ (0 ≤ x.toInt ∧ x.toInt < 8 ∧ 0 ≤ y.toInt ∧ y.toInt < 8) := by
    intro hc
    exact h ⟨(i32_inRange_iff x).1 ⟨hc.1, hc.2.1⟩, (i32_inRange_iff y).1 ⟨hc.2.2.1, hc.2.2.2⟩⟩
  simp [cellToLeafBitModel, this]

theorem coordsLeaf_iter {rp : String → Option (List JvmInstr)} {d1 sf : Nat} (hres : ResolvesMccProgs rp)
    (hsf : 45 ≤ sf) {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {arrAddr : Nat} {ec : String} {es : Array JvmVal}
    (harr : jh.get? arrAddr = some (.objArray ec es)) (harrLt : arrAddr < jh.objects.size)
    (k : Nat) (hk : k < es.size) (hk32 : k + 1 < 2 ^ 32) (p : Int32 × Int32)
    (hel : es[k] = .ext (.intOffset (packCoord p))) (ox oy : Int32) (acc : UInt64) (locs : Nat → JvmVal)
    (hl1 : locs 1 = .i32 ox.toUInt32) (hl2 : locs 2 = .i32 oy.toUInt32) (hl3 : locs 3 = .i64 acc)
    (hl5 : locs 5 = .heapRef jh.objects.size) :
    ∃ locs' m, locs' 1 = .i32 ox.toUInt32 ∧ locs' 2 = .i32 oy.toUInt32 ∧
      locs' 3 = .i64 (leafStep ox oy acc p) ∧ locs' 5 = .heapRef jh.objects.size ∧
      ∀ f, Jvm.runJvmResFast (mkAlgKotlinHooks rp (d1 + 1) sf) (f + 60) MacroCellCoordinatesKt_coordinatesToLeaf_prog 8
          (MacroCellCoordinatesKt_coordinatesToLeaf_prog.drop 8) ⟨8, [], locs, (jh.alloc (iterObj arrAddr k)).2, hp⟩ =
        Jvm.runJvmResFast (mkAlgKotlinHooks rp (d1 + 1) sf) (f + m) MacroCellCoordinatesKt_coordinatesToLeaf_prog 8
          (MacroCellCoordinatesKt_coordinatesToLeaf_prog.drop 8) ⟨8, [], locs', (jh.alloc (iterObj arrAddr (k + 1))).2, hp⟩ := by
  have hx : intOffsetX (packCoord p) - ox.toUInt32 = (p.1 - ox).toUInt32 := by
    simp only [packCoord, intOffsetX_pack, int32_sub_toUInt32]
  have hy : intOffsetY (packCoord p) - oy.toUInt32 = (p.2 - oy).toUInt32 := by
    simp only [packCoord, intOffsetY_pack, int32_sub_toUInt32]
  have e : ∀ H : Jvm.JvmHeap AlgExt, (⟨8, [], locs, H, hp⟩ : JvmState) =
      ⟨8, [], lpLocs locs ox.toUInt32 oy.toUInt32 acc jh.objects.size, H, hp⟩ := by
    intro H; rw [lpLocs_absorb hl1 hl2 hl3 hl5]
  have hhead := coordsLeaf_head (rp := rp) (d1 := d1) (sf := sf) (hp := hp) harr harrLt k hk hk32 p hel locs
    ox.toUInt32 oy.toUInt32 acc
  simp only [hx, hy] at hhead
  generalize hdx : (p.1 - ox).toUInt32 = dx at hhead
  generalize hdy : (p.2 - oy).toUInt32 = dy at hhead
  by_cases hin : dx.toNat < 8 ∧ dy.toNat < 8
  · have hstep : leafStep ox oy acc p =
        acc ||| (1 : UInt64) <<< (Algorithm.cellToLeafBitUInt dx dy).toUInt64 := by
      rw [← hdx, ← hdy] at hin ⊢
      simp only [leafStep, cellToLeafBitModel_of_lt _ _ hin.1 hin.2]
    refine ⟨setLocal (setLocal (headLocs (lpLocs locs ox.toUInt32 oy.toUInt32 acc jh.objects.size)
      (packCoord p) dx dy) 12 (.i32 (Algorithm.cellToLeafBitUInt dx dy)))
      3 (.i64 (acc ||| (1 : UInt64) <<< (Algorithm.cellToLeafBitUInt dx dy).toUInt64)),
      1, ?_, ?_, ?_, ?_, fun f => ?_⟩
    rotate_left 4
    · rw [e, show f + 60 = (f + 27) + 33 by omega, hhead, show f + 27 + 1 = (f + 1) + 27 by omega,
        coordsLeaf_tail_in _ _ _ _ _ hres hsf _ _ _ _ hin.1 hin.2]
    all_goals simp [setLocal, hstep]
  · have hstep : leafStep ox oy acc p = acc := by
      rw [← hdx, ← hdy] at hin
      simp only [leafStep, cellToLeafBitModel_of_not _ _ hin]
    by_cases hx0 : 2 ^ 31 ≤ dx.toNat
    · refine ⟨headLocs (lpLocs locs ox.toUInt32 oy.toUInt32 acc jh.objects.size) (packCoord p) dx dy,
        25, ?_, ?_, ?_, ?_, fun f => ?_⟩
      rotate_left 4
      · rw [e, show f + 60 = (f + 27) + 33 by omega, hhead, show f + 27 + 1 = (f + 25) + 3 by omega,
          coordsLeaf_tail_x0 _ _ _ _ _ hx0]
      all_goals simp [setLocal, hstep]
    by_cases hx8 : 8 ≤ dx.toNat
    · refine ⟨headLocs (lpLocs locs ox.toUInt32 oy.toUInt32 acc jh.objects.size) (packCoord p) dx dy,
        21, ?_, ?_, ?_, ?_, fun f => ?_⟩
      rotate_left 4
      · rw [e, show f + 60 = (f + 27) + 33 by omega, hhead, show f + 27 + 1 = (f + 21) + 7 by omega,
          coordsLeaf_tail_x8 _ _ _ _ _ hx0 hx8]
      all_goals simp [setLocal, hstep]
    have hxl : dx.toNat < 8 := by omega
    by_cases hy0 : 2 ^ 31 ≤ dy.toNat
    · refine ⟨headLocs (lpLocs locs ox.toUInt32 oy.toUInt32 acc jh.objects.size) (packCoord p) dx dy,
        16, ?_, ?_, ?_, ?_, fun f => ?_⟩
      rotate_left 4
      · rw [e, show f + 60 = (f + 27) + 33 by omega, hhead, show f + 27 + 1 = (f + 16) + 12 by omega,
          coordsLeaf_tail_y0 _ _ _ _ _ hxl hy0]
      all_goals simp [setLocal, hstep]
    have hy8 : 8 ≤ dy.toNat := by omega
    refine ⟨headLocs (lpLocs locs ox.toUInt32 oy.toUInt32 acc jh.objects.size) (packCoord p) dx dy,
        12, ?_, ?_, ?_, ?_, fun f => ?_⟩
    rotate_left 4
    · rw [e, show f + 60 = (f + 27) + 33 by omega, hhead, show f + 27 + 1 = (f + 12) + 16 by omega,
        coordsLeaf_tail_y8 _ _ _ _ _ hxl hy0 hy8]
    all_goals simp [setLocal, hstep]

theorem coordsLeaf_exit {rp : String → Option (List JvmInstr)} {d1 sf : Nat}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {arrAddr : Nat} {ec : String} {es : Array JvmVal}
    (harr : jh.get? arrAddr = some (.objArray ec es)) (harrLt : arrAddr < jh.objects.size)
    (h32 : es.size < 2 ^ 32) (L : Nat → JvmVal) (ox oy : UInt32) (acc : UInt64) (f : Nat) :
    ∃ pc stk locs',
      Jvm.runJvmResFast (mkAlgKotlinHooks rp (d1 + 1) sf) (f + 6) MacroCellCoordinatesKt_coordinatesToLeaf_prog 8
          (MacroCellCoordinatesKt_coordinatesToLeaf_prog.drop 8)
          ⟨8, [], lpLocs L ox oy acc jh.objects.size, (jh.alloc (iterObj arrAddr es.size)).2, hp⟩ =
        some (.i64 acc, ⟨pc, stk, locs', (jh.alloc (iterObj arrAddr es.size)).2, hp⟩) := by
  have hit : (jh.alloc (iterObj arrAddr es.size)).2.get? jh.objects.size = some (iterObj arrAddr es.size) :=
    heap_get_alloc_self _ _
  have harr' : (jh.alloc (iterObj arrAddr es.size)).2.get? arrAddr = some (.objArray ec es) := by
    rw [heap_get_alloc_lt _ harrLt, harr]
  refine ⟨?pc, ?stk, ?locs, ?main⟩
  case main =>
  mcc_step_blk
  refine (fast_iter_hasNext hit harr' h32).trans ?_
  simp only [Nat.lt_irrefl, ↓reduceIte]
  mcc_branch
  mcc_step_blk
  exact fast_lreturn

theorem encodeCoords_getElem (coords : List (Int32 × Int32)) (k : Nat) (hk : k < (encodeCoords coords).size) :
    (encodeCoords coords)[k] = .ext (.intOffset (packCoord (coords[k]'(by simpa [encodeCoords, encodeIntOffsets]
      using hk)))) := by
  simp [encodeCoords, encodeIntOffsets]

theorem encodeCoords_size (coords : List (Int32 × Int32)) : (encodeCoords coords).size = coords.length := by
  simp [encodeCoords, encodeIntOffsets]

theorem coordsLeaf_loop {rp : String → Option (List JvmInstr)} {d1 sf : Nat} (hres : ResolvesMccProgs rp)
    (hsf : 45 ≤ sf) {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {arrAddr : Nat} {ec : String}
    (coords : List (Int32 × Int32)) (harr : jh.get? arrAddr = some (.objArray ec (encodeCoords coords)))
    (h32 : coords.length < 2 ^ 32) (ox oy : Int32) :
    ∀ rem k acc locs fuel, k + rem = coords.length → 60 * rem + 6 ≤ fuel →
      locs 1 = .i32 ox.toUInt32 → locs 2 = .i32 oy.toUInt32 → locs 3 = .i64 acc →
      locs 5 = .heapRef jh.objects.size →
      ∃ pc stk locs',
        Jvm.runJvmResFast (mkAlgKotlinHooks rp (d1 + 1) sf) fuel MacroCellCoordinatesKt_coordinatesToLeaf_prog 8
            (MacroCellCoordinatesKt_coordinatesToLeaf_prog.drop 8) ⟨8, [], locs, (jh.alloc (iterObj arrAddr k)).2, hp⟩ =
          some (.i64 ((coords.drop k).foldl (leafStep ox oy) acc),
            ⟨pc, stk, locs', (jh.alloc (iterObj arrAddr coords.length)).2, hp⟩) := by
  have harrLt := Jvm.jvmHeap_get?_some_lt harr
  have hsize := encodeCoords_size coords
  intro rem
  induction rem with
  | zero =>
    intro k acc locs fuel hk hf hl1 hl2 hl3 hl5
    obtain ⟨f, rfl⟩ := Nat.exists_eq_add_of_le' (show 6 ≤ fuel by omega)
    have hkn : k = coords.length := by omega
    subst hkn
    have e : (⟨8, [], locs, (jh.alloc (iterObj arrAddr coords.length)).2, hp⟩ : JvmState) =
        ⟨8, [], lpLocs locs ox.toUInt32 oy.toUInt32 acc jh.objects.size,
          (jh.alloc (iterObj arrAddr coords.length)).2, hp⟩ := by
      rw [lpLocs_absorb hl1 hl2 hl3 hl5]
    rw [e, List.drop_length, List.foldl_nil]
    have hx := coordsLeaf_exit (rp := rp) (d1 := d1) (sf := sf) (hp := hp) harr harrLt (by omega) locs
      ox.toUInt32 oy.toUInt32 acc f
    rw [hsize] at hx
    exact hx
  | succ r ih =>
    intro k acc locs fuel hk hf hl1 hl2 hl3 hl5
    have hkl : k < coords.length := by omega
    have hkes : k < (encodeCoords coords).size := by omega
    obtain ⟨locs', m, h1, h2, h3, h5, hrun⟩ := coordsLeaf_iter (d1 := d1) (hp := hp) hres hsf harr harrLt k hkes
      (by omega) (coords[k]'hkl) (encodeCoords_getElem coords k hkes) ox oy acc locs hl1 hl2 hl3 hl5
    obtain ⟨f, rfl⟩ := Nat.exists_eq_add_of_le' (show 60 ≤ fuel by omega)
    rw [hrun f, List.drop_eq_getElem_cons hkl, List.foldl_cons]
    exact ih (k + 1) _ locs' (f + m) (by omega) (by omega) h1 h2 h3 h5

theorem coordsLeaf_prefix {rp : String → Option (List JvmInstr)} {d1 sf : Nat} (ox oy : Int32)
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {setAddr arrAddr : Nat} {cls ec : String} {es : Array JvmVal}
    (hcoll : algKotlinColl? jh setAddr = some (cls, arrAddr, ec, es)) (f : Nat) :
    ∃ L : Nat → JvmVal, L 1 = .i32 ox.toUInt32 ∧ L 2 = .i32 oy.toUInt32 ∧ L 3 = .i64 0 ∧
      L 5 = .heapRef jh.objects.size ∧
      Jvm.runJvmResFast (mkAlgKotlinHooks rp (d1 + 1) sf) (f + 8) MacroCellCoordinatesKt_coordinatesToLeaf_prog 0
          MacroCellCoordinatesKt_coordinatesToLeaf_prog
          (Jvm.initJvmState [(0, .heapRef setAddr), (1, .i32 ox.toUInt32), (2, .i32 oy.toUInt32)] (.i32 0) hp jh) =
        Jvm.runJvmResFast (mkAlgKotlinHooks rp (d1 + 1) sf) f MacroCellCoordinatesKt_coordinatesToLeaf_prog 8
          (MacroCellCoordinatesKt_coordinatesToLeaf_prog.drop 8) ⟨8, [], L, (jh.alloc (iterObj arrAddr 0)).2, hp⟩ := by
  refine ⟨?L, ?h1, ?h2, ?h3, ?h5, ?main⟩
  case main =>
    conv => lhs; arg 5; dsimp only [MacroCellCoordinatesKt_coordinatesToLeaf_prog]
    mcc_step_blk
    mcc_rfl_step
    refine (fast_set_iterator hcoll).trans ?_
    mcc_step1
    conv => lhs; tactic => mcc_norm_run_args
    rfl
  all_goals rfl

theorem coordinatesToLeaf_fast {rp : String → Option (List JvmInstr)} {d1 sf : Nat} (hres : ResolvesMccProgs rp)
    (hsf : 45 ≤ sf) (coords : List (Int32 × Int32)) (h32 : coords.length < 2 ^ 32) (ox oy : Int32)
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {setAddr arrAddr : Nat} {cls ec : String}
    (hcoll : algKotlinColl? jh setAddr = some (cls, arrAddr, ec, encodeCoords coords)) (f : Nat) :
    ∃ pc stk locs',
      Jvm.runJvmResFast (mkAlgKotlinHooks rp (d1 + 1) sf) (f + 60 * coords.length + 14) MacroCellCoordinatesKt_coordinatesToLeaf_prog 0
          MacroCellCoordinatesKt_coordinatesToLeaf_prog
          (Jvm.initJvmState [(0, .heapRef setAddr), (1, .i32 ox.toUInt32), (2, .i32 oy.toUInt32)] (.i32 0) hp jh) =
        some (.i64 (coordinatesToLeafModel coords ox oy),
          ⟨pc, stk, locs', (jh.alloc (iterObj arrAddr coords.length)).2, hp⟩) := by
  have harr := algKotlinColl_arr hcoll
  obtain ⟨L, h1, h2, h3, h5, hpre⟩ := coordsLeaf_prefix (rp := rp) (d1 := d1) (sf := sf) ox oy hcoll
    (f + 60 * coords.length + 6)
  obtain ⟨pc, stk, locs', hl⟩ := coordsLeaf_loop (d1 := d1) (hp := hp) hres hsf coords harr h32 ox oy
    coords.length 0 0 L (f + 60 * coords.length + 6) (by omega) (by omega) h1 h2 h3 h5
  refine ⟨pc, stk, locs', ?_⟩
  rw [show f + 60 * coords.length + 14 = (f + 60 * coords.length + 6) + 8 by omega, hpre,
    coordinatesToLeafModel_eq_foldl]
  rw [List.drop_zero] at hl
  exact hl

/-! ### `coordinatesToLeaf` calls and `$default` -/

set_option maxRecDepth 4096 in
theorem tags_LII : Jvm.parseMethodParamTags "(Ljava/util/Set;II)J" = ['L', 'I', 'I'] := by decide

/-- A call of the lifted `coordinatesToLeaf` pushes `coordinatesToLeafModel coords ox oy` and allocates one
iterator. -/
theorem fast_call_coordinatesToLeaf {rp : String → Option (List JvmInstr)} {d1 sf : Nat}
    (hres : ResolvesMccProgs rp) (hsf : 45 ≤ sf) {coords : List (Int32 × Int32)} (h32 : coords.length < 2 ^ 32)
    (hsf2 : 60 * coords.length + 14 ≤ sf) {ox oy : Int32} {u v : UInt32} (hu : u = ox.toUInt32)
    (hv : v = oy.toUInt32)
    {f pc pc0 : Nat} {prog rest : List JvmInstr} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {setAddr arrAddr : Nat} {cls ec : String}
    (hcoll : algKotlinColl? jh setAddr = some (cls, arrAddr, ec, encodeCoords coords)) :
    Jvm.runJvmResFast (mkAlgKotlinHooks rp (d1 + 2) sf) (f + 1) prog pc
        (.invokestatic "com/alexvanyo/composelife/algorithm/MacroCellCoordinatesKt" "coordinatesToLeaf" "(Ljava/util/Set;II)J" :: rest)
        ⟨pc0, .i32 v :: .i32 u :: .heapRef setAddr :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkAlgKotlinHooks rp (d1 + 2) sf) f prog (pc + 1) rest
        ⟨pc + 1, .i64 (coordinatesToLeafModel coords ox oy) :: stk, locs,
          (jh.alloc (iterObj arrAddr coords.length)).2, hp⟩ := by
  subst hu hv
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' hsf2
  obtain ⟨epc, estk, elocs, h⟩ := coordinatesToLeaf_fast (d1 := d1) (hp := hp) hres hsf coords h32 ox oy hcoll k
  have hrun := Jvm.runJvmRes_of_runJvmResFast0 _ _ _ _ _ rfl h
  rw [show k + 60 * coords.length + 14 = sf by omega] at hrun
  exact Jvm.runJvmResFast_invokestatic_step _
    (stepMccStatic (d1 := d1 + 1) (st := ⟨pc, .i32 oy.toUInt32 :: .i32 ox.toUInt32 :: .heapRef setAddr :: stk,
        locs, jh, hp⟩) (method := "coordinatesToLeaf")
      (stkRest := stk) (endSt := ⟨epc, estk, elocs, (jh.alloc (iterObj arrAddr coords.length)).2, hp⟩)
      ['L', 'I', 'I'] (args := [.heapRef setAddr, .i32 ox.toUInt32, .i32 oy.toUInt32]) tags_LII rfl rfl
      hres.2.1 hrun (by decide +kernel))

/-- The offset that a `$default` wrapper passes on: `0` when the mask bit is set, the argument otherwise. -/
def dflt (mask bit : UInt32) (o : Int32) : Int32 := if mask &&& bit = 0 then o else 0

theorem coordinatesToLeaf_default_fast {rp : String → Option (List JvmInstr)} {d1 sf : Nat}
    (hres : ResolvesMccProgs rp) (hsf : 45 ≤ sf) (coords : List (Int32 × Int32)) (h32 : coords.length < 2 ^ 32)
    (hsf2 : 60 * coords.length + 14 ≤ sf) (ox oy : Int32) (mask : UInt32) (marker : JvmVal)
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {setAddr arrAddr : Nat} {cls ec : String}
    (hcoll : algKotlinColl? jh setAddr = some (cls, arrAddr, ec, encodeCoords coords)) (f : Nat) :
    ∃ pc stk locs',
      Jvm.runJvmResFast (mkAlgKotlinHooks rp (d1 + 2) sf) (f + 17) MacroCellCoordinatesKt_coordinatesToLeaf_default_prog 0
          MacroCellCoordinatesKt_coordinatesToLeaf_default_prog
          (Jvm.initJvmState [(0, .heapRef setAddr), (1, .i32 ox.toUInt32), (2, .i32 oy.toUInt32), (3, .i32 mask),
            (4, marker)] (.i32 0) hp jh) =
        some (.i64 (coordinatesToLeafModel coords (dflt mask 2 ox) (dflt mask 4 oy)),
          ⟨pc, stk, locs', (jh.alloc (iterObj arrAddr coords.length)).2, hp⟩) := by
  by_cases h2 : mask &&& 2 = 0 <;> by_cases h4 : mask &&& 4 = 0
  all_goals
    refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left 3
    conv => lhs; arg 5; dsimp only [MacroCellCoordinatesKt_coordinatesToLeaf_default_prog]
    mcc_step_blk
    first
      | refine (Jvm.runJvmResFast_ifeq_branch _ h2).trans ?_
      | refine (Jvm.runJvmResFast_ifeq_fallthrough _ (by simpa using h2)).trans ?_
    mcc_step_blk
    first
      | refine (Jvm.runJvmResFast_ifeq_branch _ h4).trans ?_
      | refine (Jvm.runJvmResFast_ifeq_fallthrough _ (by simpa using h4)).trans ?_
    mcc_step_blk
    refine (fast_call_coordinatesToLeaf hres hsf h32 hsf2 (ox := dflt mask 2 ox) (oy := dflt mask 4 oy)
      (by simp only [dflt, h2, ↓reduceIte] <;> rfl) (by simp only [dflt, h4, ↓reduceIte] <;> rfl) hcoll).trans ?_
    exact fast_lreturn

/--
`coordinatesToLeaf(coordinates, offsetX, offsetY)` on the JVM computes `coordinatesToLeafModel`: for a `Set<IntOffset>`
holding `coords` (in iteration order), it returns the leaf bits and its only heap effect is the one iterator it
allocates over the set's backing array.
-/
theorem coordinatesToLeaf_equiv (rp : String → Option (List JvmInstr)) (hres : ResolvesMccProgs rp)
    (d sf fuel : Nat) (hd : 1 ≤ d) (hsf : 45 ≤ sf) (coords : List (Int32 × Int32)) (h32 : coords.length < 2 ^ 32)
    (hf : 60 * coords.length + 14 ≤ fuel) (ox oy : Int32) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (setAddr arrAddr : Nat) (cls ec : String)
    (hcoll : algKotlinColl? jh setAddr = some (cls, arrAddr, ec, encodeCoords coords)) :
    (Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) fuel MacroCellCoordinatesKt_coordinatesToLeaf_prog
        (Jvm.initJvmState [(0, .heapRef setAddr), (1, .i32 ox.toUInt32), (2, .i32 oy.toUInt32)] (.i32 0) hp jh)).map
        (fun r => (r.1, r.2.jvmHeap, r.2.heap)) =
      some (.i64 (coordinatesToLeafModel coords ox oy), (jh.alloc (iterObj arrAddr coords.length)).2, hp) := by
  obtain ⟨d1, rfl⟩ := Nat.exists_eq_add_of_le' hd
  obtain ⟨f, rfl⟩ := Nat.exists_eq_add_of_le' hf
  obtain ⟨pc, stk, locs, h⟩ := coordinatesToLeaf_fast (d1 := d1) (hp := hp) hres hsf coords h32 ox oy hcoll f
  rw [show f + (60 * coords.length + 14) = f + 60 * coords.length + 14 by omega,
    Jvm.runJvmRes_of_runJvmResFast0 _ _ _ _ _ rfl h]
  rfl

/--
`coordinatesToLeaf$default(coordinates, offsetX, offsetY, mask, marker)` computes `coordinatesToLeafModel` with each
offset replaced by `0` when its default-argument bit (`2` for `offsetX`, `4` for `offsetY`) is set in `mask`.
-/
theorem coordinatesToLeaf_default_equiv (rp : String → Option (List JvmInstr)) (hres : ResolvesMccProgs rp)
    (d sf fuel : Nat) (hd : 2 ≤ d) (hsf : 45 ≤ sf) (coords : List (Int32 × Int32)) (h32 : coords.length < 2 ^ 32)
    (hsf2 : 60 * coords.length + 14 ≤ sf) (hf : 17 ≤ fuel) (ox oy : Int32) (mask : UInt32) (marker : JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (setAddr arrAddr : Nat) (cls ec : String)
    (hcoll : algKotlinColl? jh setAddr = some (cls, arrAddr, ec, encodeCoords coords)) :
    (Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) fuel MacroCellCoordinatesKt_coordinatesToLeaf_default_prog
        (Jvm.initJvmState [(0, .heapRef setAddr), (1, .i32 ox.toUInt32), (2, .i32 oy.toUInt32), (3, .i32 mask),
          (4, marker)] (.i32 0) hp jh)).map
        (fun r => (r.1, r.2.jvmHeap, r.2.heap)) =
      some (.i64 (coordinatesToLeafModel coords (if mask &&& 2 = 0 then ox else 0)
          (if mask &&& 4 = 0 then oy else 0)),
        (jh.alloc (iterObj arrAddr coords.length)).2, hp) := by
  obtain ⟨d1, rfl⟩ := Nat.exists_eq_add_of_le' hd
  obtain ⟨f, rfl⟩ := Nat.exists_eq_add_of_le' hf
  obtain ⟨pc, stk, locs, h⟩ := coordinatesToLeaf_default_fast (d1 := d1) (hp := hp) hres hsf coords h32 hsf2
    ox oy mask marker hcoll f
  rw [Jvm.runJvmRes_of_runJvmResFast0 _ _ _ _ _ rfl h]
  rfl

/-! ### `leafToCoordinates` -/

/-- The `LinkedHashSet` that `leafToCoordinates` builds, holding `es`, allocated on top of `jh`. -/
def lhsHeap (jh : Jvm.JvmHeap AlgExt) (es : Array JvmVal) : Jvm.JvmHeap AlgExt :=
  (allocAlgKotlinColl jh "java/util/LinkedHashSet" es).2

theorem lhsHeap_size (jh : Jvm.JvmHeap AlgExt) (es : Array JvmVal) :
    (allocAlgKotlinColl jh "java/util/LinkedHashSet" es).1 = jh.objects.size + 1 := by
  simp [allocAlgKotlinColl, Jvm.JvmHeap.alloc]

theorem lhsHeap_get_inst (jh : Jvm.JvmHeap AlgExt) (es : Array JvmVal) :
    (lhsHeap jh es).get? (jh.objects.size + 1) =
      some (.instance "java/util/LinkedHashSet" [("arr", .heapRef jh.objects.size)]) := by
  simp [lhsHeap, allocAlgKotlinColl, Jvm.JvmHeap.alloc, Jvm.JvmHeap.get?, Array.getElem_push]

theorem lhsHeap_get_arr (jh : Jvm.JvmHeap AlgExt) (es : Array JvmVal) :
    (lhsHeap jh es).get? jh.objects.size = some (.objArray "java/lang/Object" es) := by
  simp [lhsHeap, allocAlgKotlinColl, Jvm.JvmHeap.alloc, Jvm.JvmHeap.get?, Array.getElem?_push]

theorem lhsHeap_coll (jh : Jvm.JvmHeap AlgExt) (es : Array JvmVal) :
    algKotlinColl? (lhsHeap jh es) (jh.objects.size + 1) =
      some ("java/util/LinkedHashSet", jh.objects.size, "java/lang/Object", es) := by
  unfold algKotlinColl?
  rw [lhsHeap_get_inst]
  simp only [isAlgKotlinCollClass]
  simp [lhsHeap_get_arr]

theorem lhsHeap_set (jh : Jvm.JvmHeap AlgExt) (es es' : Array JvmVal) :
    (lhsHeap jh es).set jh.objects.size (.objArray "java/lang/Object" es') = lhsHeap jh es' := by
  simp [lhsHeap, allocAlgKotlinColl, Jvm.JvmHeap.alloc, Jvm.JvmHeap.set, Array.set_push]
  omega

theorem fast_lhs_init {ip : InvokeProg} {f pc pc0 : Nat} {prog rest : List JvmInstr} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    Jvm.runJvmResFast (algKotlinHooksWith ip) (f + 1) prog pc
        (.invokespecial "java/util/LinkedHashSet" "<init>" "()V" :: rest)
        ⟨pc0, .allocRef "java/util/LinkedHashSet" :: .allocRef "java/util/LinkedHashSet" :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (algKotlinHooksWith ip) f prog (pc + 1) rest
        ⟨pc + 1, .heapRef (jh.objects.size + 1) :: stk, locs, lhsHeap jh #[], hp⟩ := by
  have h : Jvm.stepInvokeSpecialGeneric (algKotlinHooksWith ip)
      ⟨pc, .allocRef "java/util/LinkedHashSet" :: .allocRef "java/util/LinkedHashSet" :: stk, locs, jh, hp⟩
      "java/util/LinkedHashSet" "<init>" "()V" =
      .inl (some ⟨pc + 1, .heapRef (allocAlgKotlinColl jh "java/util/LinkedHashSet" #[]).1 :: stk, locs,
        lhsHeap jh #[], hp⟩) := by
    have hE : Jvm.stepInvokeSpecialGeneric (algKotlinHooksWith ip)
        ⟨pc, .allocRef "java/util/LinkedHashSet" :: .allocRef "java/util/LinkedHashSet" :: stk, locs, jh, hp⟩
        "java/util/LinkedHashSet" "<init>" "()V" =
        algKotlinStepSpecialLeaf
          ⟨pc, .allocRef "java/util/LinkedHashSet" :: .allocRef "java/util/LinkedHashSet" :: stk, locs, jh, hp⟩
          "java/util/LinkedHashSet" "<init>" "()V" := rfl
    rw [hE]
    rfl
  rw [lhsHeap_size] at h
  exact Jvm.runJvmResFast_invokespecial_step _ h

theorem fast_checkcast_lhs {ip : InvokeProg} {f pc pc0 : Nat} {prog rest : List JvmInstr} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {es : Array JvmVal} :
    Jvm.runJvmResFast (algKotlinHooksWith ip) (f + 1) prog pc (.checkcast "java/util/Set" :: rest)
        ⟨pc0, .heapRef (jh.objects.size + 1) :: stk, locs, lhsHeap jh es, hp⟩ =
      Jvm.runJvmResFast (algKotlinHooksWith ip) f prog (pc + 1) rest
        ⟨pc + 1, .heapRef (jh.objects.size + 1) :: stk, locs, lhsHeap jh es, hp⟩ := by
  have hm : Jvm.HeapObj.matchesType (algKotlinHooksWith ip).isSubtypeOf "java/util/Set"
      (.instance "java/util/LinkedHashSet" [("arr", .heapRef jh.objects.size)] : Jvm.HeapObj AlgExt) = true := by
    rfl
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  unfold Jvm.stepInstr
  simp [Jvm.evalCheckCast, Jvm.JvmHeap.checkCast, Jvm.JvmHeap.checkInstanceOf, lhsHeap_get_inst, hm]

/-- The loop locals of `leafToCoordinates` (outer loop, `y = j`) over arbitrary other slots `L`. -/
abbrev outerLocs (L : Nat → JvmVal) (leaf : UInt64) (ox oy : UInt32) (setAddr : Nat) (j : UInt32) :
    Nat → JvmVal :=
  setLocal (setLocal (setLocal (setLocal (setLocal L 0 (.i64 leaf)) 2 (.i32 ox)) 3 (.i32 oy)) 4 (.heapRef setAddr))
    5 (.i32 j)

theorem l2c_prefix {rp : String → Option (List JvmInstr)} {d1 sf : Nat} (leaf : UInt64) (hl : leaf ≠ 0)
    (ox oy : Int32) {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} (f : Nat) :
    ∃ L : Nat → JvmVal, L 0 = .i64 leaf ∧ L 2 = .i32 ox.toUInt32 ∧ L 3 = .i32 oy.toUInt32 ∧
      L 4 = .heapRef (jh.objects.size + 1) ∧ L 5 = .i32 0 ∧
      Jvm.runJvmResFast (mkAlgKotlinHooks rp (d1 + 1) sf) (f + 11) MacroCellCoordinatesKt_leafToCoordinates_prog 0
          MacroCellCoordinatesKt_leafToCoordinates_prog
          (Jvm.initJvmState [(0, .i64 leaf), (2, .i32 ox.toUInt32), (3, .i32 oy.toUInt32)] (.i32 0) hp jh) =
        Jvm.runJvmResFast (mkAlgKotlinHooks rp (d1 + 1) sf) f MacroCellCoordinatesKt_leafToCoordinates_prog 13
          (MacroCellCoordinatesKt_leafToCoordinates_prog.drop 13) ⟨13, [], L, lhsHeap jh #[], hp⟩ := by
  refine ⟨?L, ?h0, ?h2, ?h3, ?h4, ?h5, ?main⟩
  case main =>
    conv => lhs; arg 5; dsimp only [MacroCellCoordinatesKt_leafToCoordinates_prog]
    mcc_step_blk
    refine (Jvm.runJvmResFast_ifne_branch _ (beq_false_of_ne fun h => hl ((Jvm.lcmp_eq_zero _ _ _).1 h))).trans ?_
    conv => lhs; tactic => mcc_norm_run_args
    mcc_rfl_step
    refine fast_lhs_init.trans ?_
    refine fast_checkcast_lhs.trans ?_
    mcc_step1
    mcc_step1
    mcc_step1
    conv => lhs; tactic => mcc_norm_run_args
    rfl
  all_goals rfl

/-! #### Model pieces -/

/-- The cell at column `x`, row `y` of `leafToCoordinatesModel`'s `filterMap`. -/
def cellAt (leaf : UInt64) (ox oy : Int32) (y x : Nat) : Option (Int32 × Int32) :=
  let bit := Algorithm.cellToLeafBitUInt (UInt32.ofNat x) (UInt32.ofNat y)
  if ((leaf >>> bit.toUInt64) &&& 1) != 0 then
    some (Int32.ofInt (x : Int) + ox, Int32.ofInt (y : Int) + oy)
  else
    none

/-- The first `n` columns of row `y`. -/
def rowPart (leaf : UInt64) (ox oy : Int32) (y n : Nat) : List (Int32 × Int32) :=
  (List.range n).filterMap (cellAt leaf ox oy y)

/-- The first `m` rows. -/
def allPart (leaf : UInt64) (ox oy : Int32) (m : Nat) : List (Int32 × Int32) :=
  (List.range m).flatMap fun y => rowPart leaf ox oy y 8

theorem leafToCoordinatesModel_eq (leaf : UInt64) (ox oy : Int32) (hl : leaf ≠ 0) :
    leafToCoordinatesModel leaf ox oy = allPart leaf ox oy 8 := by
  have : (leaf == 0) = false := beq_false_of_ne hl
  simp only [leafToCoordinatesModel, this, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem rowPart_succ (leaf : UInt64) (ox oy : Int32) (y n : Nat) :
    rowPart leaf ox oy y (n + 1) = rowPart leaf ox oy y n ++ (cellAt leaf ox oy y n).toList := by
  simp only [rowPart, List.range_succ, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
  cases cellAt leaf ox oy y n <;> rfl

theorem allPart_succ (leaf : UInt64) (ox oy : Int32) (m : Nat) :
    allPart leaf ox oy (m + 1) = allPart leaf ox oy m ++ rowPart leaf ox oy m 8 := by
  simp [allPart, List.range_succ, List.flatMap_append]

theorem int32_ofInt_toUInt32 (k : Nat) (hk : k < 8) : (Int32.ofInt (k : Int)).toUInt32 = UInt32.ofNat k := by
  revert k; decide

theorem cell_toUInt32 (k : Nat) (hk : k < 8) (o : Int32) :
    (Int32.ofInt (k : Int) + o).toUInt32 = UInt32.ofNat k + o.toUInt32 := by
  rw [Int32.toUInt32_add, int32_ofInt_toUInt32 k hk]

theorem mem_parts {leaf : UInt64} {ox oy : Int32} {j k : Nat} {q : Int32 × Int32} (hk : k ≤ 8)
    (h : q ∈ allPart leaf ox oy j ++ rowPart leaf ox oy j k) :
    ∃ x y, x < 8 ∧ (y < j ∨ y = j ∧ x < k) ∧ q = (Int32.ofInt (x : Int) + ox, Int32.ofInt (y : Int) + oy) := by
  have hc : ∀ y x, cellAt leaf ox oy y x = some q →
      q = (Int32.ofInt (x : Int) + ox, Int32.ofInt (y : Int) + oy) := by
    intro y x hq
    dsimp only [cellAt] at hq
    split at hq
    · exact (Option.some.inj hq).symm
    · contradiction
  simp only [List.mem_append, allPart, rowPart, List.mem_flatMap, List.mem_filterMap, List.mem_range] at h
  rcases h with ⟨y, hy, x, hx, hq⟩ | ⟨x, hx, hq⟩
  · exact ⟨x, y, hx, Or.inl hy, hc y x hq⟩
  · exact ⟨x, j, by omega, Or.inr ⟨rfl, hx⟩, hc j x hq⟩

theorem uint32_ofNat_inj {x k : Nat} (hx : x < 8) (hk : k < 8) (h : UInt32.ofNat x = UInt32.ofNat k) : x = k := by
  have := congrArg UInt32.toNat h
  rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat'] at this
  omega

theorem packCoord_cell_inj {ox oy : Int32} {x y k j : Nat} (hx : x < 8) (hy : y < 8) (hk : k < 8) (hj : j < 8)
    (h : packCoord (Int32.ofInt (x : Int) + ox, Int32.ofInt (y : Int) + oy) =
      packCoord (Int32.ofInt (k : Int) + ox, Int32.ofInt (j : Int) + oy)) : x = k ∧ y = j := by
  have h1 := congrArg intOffsetX h
  have h2 := congrArg intOffsetY h
  simp only [packCoord, intOffsetX_pack, intOffsetY_pack, cell_toUInt32 _ hx, cell_toUInt32 _ hy,
    cell_toUInt32 _ hk, cell_toUInt32 _ hj] at h1 h2
  exact ⟨uint32_ofNat_inj hx hk ((UInt32.add_left_inj _).mp h1),
    uint32_ofNat_inj hy hj ((UInt32.add_left_inj _).mp h2)⟩

theorem parts_not_mem (leaf : UInt64) (ox oy : Int32) {j k : Nat} (hj : j < 8) (hk : k < 8) :
    (encodeCoords (allPart leaf ox oy j ++ rowPart leaf ox oy j k)).any
      (fun y => algKotlinEquals (.ext (.intOffset (packCoord (Int32.ofInt (k : Int) + ox,
        Int32.ofInt (j : Int) + oy)))) y) = false := by
  rw [Array.any_eq_false]
  intro i hi
  simp only [encodeCoords_size] at hi
  rw [encodeCoords_getElem _ _ (by simpa [encodeCoords_size] using hi)]
  have hm := List.getElem_mem hi
  obtain ⟨x, y, hx, hxy, hq⟩ := mem_parts (by omega) hm
  rw [hq]
  show ¬ ((_ == _) = true)
  rw [beq_iff_eq]
  intro he
  have hy : y < 8 := by omega
  obtain ⟨rfl, rfl⟩ := packCoord_cell_inj hk hj hx hy he
  omega

theorem fast_set_add_lhs {ip : InvokeProg} {f pc pc0 : Nat} {prog rest : List JvmInstr} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {es : Array JvmVal} {x : JvmVal}
    (hnot : es.any (fun y => algKotlinEquals x y) = false) :
    Jvm.runJvmResFast (algKotlinHooksWith ip) (f + 1) prog pc
        (.invokeinterface "java/util/Set" "add" "(Ljava/lang/Object;)Z" :: rest)
        ⟨pc0, x :: .heapRef (jh.objects.size + 1) :: stk, locs, lhsHeap jh es, hp⟩ =
      Jvm.runJvmResFast (algKotlinHooksWith ip) f prog (pc + 1) rest
        ⟨pc + 1, .i32 1 :: stk, locs, lhsHeap jh (es.push x), hp⟩ := by
  refine Jvm.runJvmResFast_invokeinterface_step _ ?_
  have hE : Jvm.stepInvokeInterfaceGeneric (algKotlinHooksWith ip)
      ⟨pc, x :: .heapRef (jh.objects.size + 1) :: stk, locs, lhsHeap jh es, hp⟩
      "java/util/Set" "add" "(Ljava/lang/Object;)Z" =
      algKotlinStepInterfaceLeaf ⟨pc, x :: .heapRef (jh.objects.size + 1) :: stk, locs, lhsHeap jh es, hp⟩
        "java/util/Set" "add" "(Ljava/lang/Object;)Z" := rfl
  rw [hE]
  unfold algKotlinStepInterfaceLeaf
  simp only [algKotlinCollAdd, lhsHeap_coll, hnot]
  simp [lhsHeap_set]

/-- The inner-loop locals of `leafToCoordinates` (`y = j`, `x = k`). -/
abbrev innerLocs (L : Nat → JvmVal) (leaf : UInt64) (ox oy : UInt32) (setAddr : Nat) (j k : UInt32) :
    Nat → JvmVal :=
  setLocal (outerLocs L leaf ox oy setAddr j) 6 (.i32 k)

theorem cellAt_none {leaf : UInt64} {ox oy : Int32} {j k : Nat}
    (hb : (leaf >>> (Algorithm.cellToLeafBitUInt (UInt32.ofNat k) (UInt32.ofNat j)).toUInt64 &&& 1) = 0) :
    cellAt leaf ox oy j k = none := by
  simp [cellAt, hb]

theorem cellAt_some {leaf : UInt64} {ox oy : Int32} {j k : Nat}
    (hb : ¬ (leaf >>> (Algorithm.cellToLeafBitUInt (UInt32.ofNat k) (UInt32.ofNat j)).toUInt64 &&& 1) = 0) :
    cellAt leaf ox oy j k = some (Int32.ofInt (k : Int) + ox, Int32.ofInt (j : Int) + oy) := by
  simp [cellAt, hb]

theorem encodeCoords_append_single (l : List (Int32 × Int32)) (p : Int32 × Int32) :
    encodeCoords (l ++ [p]) = (encodeCoords l).push (.ext (.intOffset (packCoord p))) := by
  simp [encodeCoords, encodeIntOffsets]

theorem l2c_iter {rp : String → Option (List JvmInstr)} {d1 sf : Nat} (hres : ResolvesMccProgs rp)
    (hsf : 45 ≤ sf) {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} (leaf : UInt64) (ox oy : Int32) (j k : Nat)
    (hj : j < 8) (hk : k < 8) (L : Nat → JvmVal) :
    ∃ L' m, L' 0 = .i64 leaf ∧ L' 2 = .i32 ox.toUInt32 ∧ L' 3 = .i32 oy.toUInt32 ∧
      L' 4 = .heapRef (jh.objects.size + 1) ∧ L' 5 = .i32 (UInt32.ofNat j) ∧ L' 6 = .i32 (UInt32.ofNat (k + 1)) ∧
      ∀ f, Jvm.runJvmResFast (mkAlgKotlinHooks rp (d1 + 1) sf) (f + 28) MacroCellCoordinatesKt_leafToCoordinates_prog 18
          (MacroCellCoordinatesKt_leafToCoordinates_prog.drop 18)
          ⟨18, [], innerLocs L leaf ox.toUInt32 oy.toUInt32 (jh.objects.size + 1) (UInt32.ofNat j) (UInt32.ofNat k),
            lhsHeap jh (encodeCoords (allPart leaf ox oy j ++ rowPart leaf ox oy j k)), hp⟩ =
        Jvm.runJvmResFast (mkAlgKotlinHooks rp (d1 + 1) sf) (f + m) MacroCellCoordinatesKt_leafToCoordinates_prog 18
          (MacroCellCoordinatesKt_leafToCoordinates_prog.drop 18)
          ⟨18, [], L', lhsHeap jh (encodeCoords (allPart leaf ox oy j ++ rowPart leaf ox oy j (k + 1))), hp⟩ := by
  have hk' : (UInt32.ofNat k).toNat < 8 := by rw [UInt32.toNat_ofNat']; omega
  have hj' : (UInt32.ofNat j).toNat < 8 := by rw [UInt32.toNat_ofNat']; omega
  generalize hbit : Algorithm.cellToLeafBitUInt (UInt32.ofNat k) (UInt32.ofNat j) = bit
  by_cases hb : (leaf >>> bit.toUInt64 &&& 1) = 0
  · refine ⟨setLocal (setLocal (innerLocs L leaf ox.toUInt32 oy.toUInt32 (jh.objects.size + 1) (UInt32.ofNat j)
      (UInt32.ofNat k)) 7 (.i32 bit)) 6 (.i32 (UInt32.ofNat k + 1)), 11, ?_, ?_, ?_, ?_, ?_, ?_, fun f => ?_⟩
    rotate_left 6
    · rw [rowPart_succ, cellAt_none (hbit ▸ hb), Option.toList_none, List.append_nil]
      mcc_step_blk
      refine (fast_if_icmpge_fall (u32_inRange_branches _ hk').2).trans ?_
      mcc_step_blk
      refine (fast_call_cellToLeafBit hres hsf hk' hj').trans ?_
      mcc_step_blk
      rw [ushr_and63, hbit]
      refine (Jvm.runJvmResFast_ifeq_branch _ ((Jvm.lcmp_eq_zero _ _ _).2 hb)).trans ?_
      conv => lhs; tactic => mcc_norm_run_args
      mcc_step_blk
      mcc_branch
      rfl
    all_goals simp [setLocal]
  · refine ⟨setLocal (setLocal (innerLocs L leaf ox.toUInt32 oy.toUInt32 (jh.objects.size + 1) (UInt32.ofNat j)
      (UInt32.ofNat k)) 7 (.i32 bit)) 6 (.i32 (UInt32.ofNat k + 1)), 0, ?_, ?_, ?_, ?_, ?_, ?_, fun f => ?_⟩
    rotate_left 6
    · have hpk : packIntOffset (UInt32.ofNat k + ox.toUInt32) (UInt32.ofNat j + oy.toUInt32) =
          packCoord (Int32.ofInt (k : Int) + ox, Int32.ofInt (j : Int) + oy) := by
        simp only [packCoord, cell_toUInt32 _ hk, cell_toUInt32 _ hj]
      rw [rowPart_succ, cellAt_some (hbit ▸ hb), Option.toList_some, ← List.append_assoc,
        encodeCoords_append_single]
      mcc_step_blk
      refine (fast_if_icmpge_fall (u32_inRange_branches _ hk').2).trans ?_
      mcc_step_blk
      refine (fast_call_cellToLeafBit hres hsf hk' hj').trans ?_
      mcc_step_blk
      rw [ushr_and63, hbit]
      refine (Jvm.runJvmResFast_ifeq_fallthrough _
        (beq_false_of_ne fun h => hb ((Jvm.lcmp_eq_zero _ _ _).1 h))).trans ?_
      mcc_step_blk
      mcc_rfl_step
      mcc_rfl_step
      rw [hpk]
      refine (fast_set_add_lhs (parts_not_mem leaf ox oy hj hk)).trans ?_
      mcc_step_blk
      mcc_branch
      rfl
    all_goals simp [setLocal]

theorem outerLocs_absorb {L : Nat → JvmVal} {leaf : UInt64} {ox oy : UInt32} {setAddr : Nat} {j : UInt32}
    (h0 : L 0 = .i64 leaf) (h2 : L 2 = .i32 ox) (h3 : L 3 = .i32 oy) (h4 : L 4 = .heapRef setAddr)
    (h5 : L 5 = .i32 j) : outerLocs L leaf ox oy setAddr j = L := by
  funext i
  simp only [outerLocs, setLocal]
  split
  · subst_vars; exact h5.symm
  split
  · subst_vars; exact h4.symm
  split
  · subst_vars; exact h3.symm
  split
  · subst_vars; exact h2.symm
  split
  · subst_vars; exact h0.symm
  rfl

theorem innerLocs_absorb {L : Nat → JvmVal} {leaf : UInt64} {ox oy : UInt32} {setAddr : Nat} {j k : UInt32}
    (h0 : L 0 = .i64 leaf) (h2 : L 2 = .i32 ox) (h3 : L 3 = .i32 oy) (h4 : L 4 = .heapRef setAddr)
    (h5 : L 5 = .i32 j) (h6 : L 6 = .i32 k) : innerLocs L leaf ox oy setAddr j k = L := by
  unfold innerLocs
  rw [outerLocs_absorb h0 h2 h3 h4 h5]
  funext i
  simp only [setLocal]
  split
  · subst_vars; exact h6.symm
  rfl

theorem l2c_inner_exit {rp : String → Option (List JvmInstr)} {d1 sf : Nat} {H : Jvm.JvmHeap AlgExt}
    {hp : AlgHeap} (L : Nat → JvmVal) (leaf : UInt64) (ox oy : UInt32) (setAddr : Nat) (j : UInt32) (f : Nat) :
    Jvm.runJvmResFast (mkAlgKotlinHooks rp (d1 + 1) sf) (f + 5) MacroCellCoordinatesKt_leafToCoordinates_prog 18
        (MacroCellCoordinatesKt_leafToCoordinates_prog.drop 18) ⟨18, [], innerLocs L leaf ox oy setAddr j (UInt32.ofNat 8), H, hp⟩ =
      Jvm.runJvmResFast (mkAlgKotlinHooks rp (d1 + 1) sf) f MacroCellCoordinatesKt_leafToCoordinates_prog 13
        (MacroCellCoordinatesKt_leafToCoordinates_prog.drop 13)
        ⟨13, [], setLocal (innerLocs L leaf ox oy setAddr j (UInt32.ofNat 8)) 5 (.i32 (j + 1)), H, hp⟩ := by
  mcc_step_blk
  refine (fast_if_icmpge_jump (by rw [u32_sle8]; decide)).trans ?_
  conv => lhs; tactic => mcc_norm_run_args
  mcc_step_blk
  mcc_branch
  rfl

theorem l2c_outer_head {rp : String → Option (List JvmInstr)} {d1 sf : Nat} {H : Jvm.JvmHeap AlgExt}
    {hp : AlgHeap} (L : Nat → JvmVal) (leaf : UInt64) (ox oy : UInt32) (setAddr : Nat) (j : Nat) (hj : j < 8)
    (f : Nat) :
    Jvm.runJvmResFast (mkAlgKotlinHooks rp (d1 + 1) sf) (f + 5) MacroCellCoordinatesKt_leafToCoordinates_prog 13
        (MacroCellCoordinatesKt_leafToCoordinates_prog.drop 13) ⟨13, [], outerLocs L leaf ox oy setAddr (UInt32.ofNat j), H, hp⟩ =
      Jvm.runJvmResFast (mkAlgKotlinHooks rp (d1 + 1) sf) f MacroCellCoordinatesKt_leafToCoordinates_prog 18
        (MacroCellCoordinatesKt_leafToCoordinates_prog.drop 18)
        ⟨18, [], innerLocs L leaf ox oy setAddr (UInt32.ofNat j) (UInt32.ofNat 0), H, hp⟩ := by
  have hj' : (UInt32.ofNat j).toNat < 8 := by rw [UInt32.toNat_ofNat']; omega
  mcc_step_blk
  refine (fast_if_icmpge_fall (u32_inRange_branches _ hj').2).trans ?_
  mcc_step1
  mcc_step1
  rfl

theorem l2c_outer_exit {rp : String → Option (List JvmInstr)} {d1 sf : Nat} {H : Jvm.JvmHeap AlgExt}
    {hp : AlgHeap} (L : Nat → JvmVal) (leaf : UInt64) (ox oy : UInt32) (setAddr : Nat) (f : Nat) :
    ∃ pc stk locs,
      Jvm.runJvmResFast (mkAlgKotlinHooks rp (d1 + 1) sf) (f + 5) MacroCellCoordinatesKt_leafToCoordinates_prog 13
          (MacroCellCoordinatesKt_leafToCoordinates_prog.drop 13) ⟨13, [], outerLocs L leaf ox oy setAddr (UInt32.ofNat 8), H, hp⟩ =
        some (.heapRef setAddr, ⟨pc, stk, locs, H, hp⟩) := by
  refine ⟨?pc, ?stk, ?locs, ?main⟩
  case main =>
    mcc_step_blk
    refine (fast_if_icmpge_jump (by rw [u32_sle8]; decide)).trans ?_
    conv => lhs; tactic => mcc_norm_run_args
    mcc_step_blk
    exact fast_areturn

theorem l2c_inner_loop {rp : String → Option (List JvmInstr)} {d1 sf : Nat} (hres : ResolvesMccProgs rp)
    (hsf : 45 ≤ sf) {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} (leaf : UInt64) (ox oy : Int32) (j : Nat)
    (hj : j < 8) :
    ∀ rem k (L : Nat → JvmVal), k + rem = 8 → L 0 = .i64 leaf → L 2 = .i32 ox.toUInt32 →
      L 3 = .i32 oy.toUInt32 → L 4 = .heapRef (jh.objects.size + 1) → L 5 = .i32 (UInt32.ofNat j) →
      L 6 = .i32 (UInt32.ofNat k) →
      ∃ L' m, L' 0 = .i64 leaf ∧ L' 2 = .i32 ox.toUInt32 ∧ L' 3 = .i32 oy.toUInt32 ∧
        L' 4 = .heapRef (jh.objects.size + 1) ∧ L' 5 = .i32 (UInt32.ofNat (j + 1)) ∧
        ∀ f, Jvm.runJvmResFast (mkAlgKotlinHooks rp (d1 + 1) sf) (f + 28 * rem + 5) MacroCellCoordinatesKt_leafToCoordinates_prog 18
            (MacroCellCoordinatesKt_leafToCoordinates_prog.drop 18)
            ⟨18, [], L, lhsHeap jh (encodeCoords (allPart leaf ox oy j ++ rowPart leaf ox oy j k)), hp⟩ =
          Jvm.runJvmResFast (mkAlgKotlinHooks rp (d1 + 1) sf) (f + m) MacroCellCoordinatesKt_leafToCoordinates_prog 13
            (MacroCellCoordinatesKt_leafToCoordinates_prog.drop 13)
            ⟨13, [], L', lhsHeap jh (encodeCoords (allPart leaf ox oy (j + 1))), hp⟩ := by
  intro rem
  induction rem with
  | zero =>
    intro k L hk h0 h2 h3 h4 h5 h6
    have hk8 : k = 8 := by omega
    subst hk8
    have e := innerLocs_absorb h0 h2 h3 h4 h5 h6
    refine ⟨setLocal L 5 (.i32 (UInt32.ofNat j + 1)), 0, ?_, ?_, ?_, ?_, ?_, fun f => ?_⟩
    rotate_left 5
    · rw [← e, Nat.mul_zero, Nat.add_zero, l2c_inner_exit, allPart_succ]
      rfl
    all_goals simp [setLocal, h0, h2, h3, h4]
  | succ r ih =>
    intro k L hk h0 h2 h3 h4 h5 h6
    have hk8 : k < 8 := by omega
    obtain ⟨L1, m1, g0, g2, g3, g4, g5, g6, hrun⟩ := l2c_iter (d1 := d1) (jh := jh) (hp := hp) hres hsf leaf ox oy j k
      hj hk8 L
    obtain ⟨L', m', k0, k2, k3, k4, k5, hrun'⟩ := ih (k + 1) L1 (by omega) g0 g2 g3 g4 g5 g6
    refine ⟨L', m1 + m', k0, k2, k3, k4, k5, fun f => ?_⟩
    rw [← innerLocs_absorb h0 h2 h3 h4 h5 h6, show f + 28 * (r + 1) + 5 = (f + 28 * r + 5) + 28 by omega, hrun,
      show f + 28 * r + 5 + m1 = (f + m1) + 28 * r + 5 by omega, hrun', Nat.add_assoc]

theorem l2c_outer_loop {rp : String → Option (List JvmInstr)} {d1 sf : Nat} (hres : ResolvesMccProgs rp)
    (hsf : 45 ≤ sf) {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} (leaf : UInt64) (ox oy : Int32) :
    ∀ rem j (L : Nat → JvmVal) fuel, j + rem = 8 → 234 * rem + 5 ≤ fuel → L 0 = .i64 leaf →
      L 2 = .i32 ox.toUInt32 → L 3 = .i32 oy.toUInt32 → L 4 = .heapRef (jh.objects.size + 1) →
      L 5 = .i32 (UInt32.ofNat j) →
      ∃ pc stk locs,
        Jvm.runJvmResFast (mkAlgKotlinHooks rp (d1 + 1) sf) fuel MacroCellCoordinatesKt_leafToCoordinates_prog 13
            (MacroCellCoordinatesKt_leafToCoordinates_prog.drop 13) ⟨13, [], L, lhsHeap jh (encodeCoords (allPart leaf ox oy j)), hp⟩ =
          some (.heapRef (jh.objects.size + 1),
            ⟨pc, stk, locs, lhsHeap jh (encodeCoords (allPart leaf ox oy 8)), hp⟩) := by
  intro rem
  induction rem with
  | zero =>
    intro j L fuel hj hf h0 h2 h3 h4 h5
    have hj8 : j = 8 := by omega
    subst hj8
    obtain ⟨f, rfl⟩ := Nat.exists_eq_add_of_le' hf
    rw [← outerLocs_absorb h0 h2 h3 h4 h5]
    exact l2c_outer_exit _ _ _ _ _ _
  | succ r ih =>
    intro j L fuel hj hf h0 h2 h3 h4 h5
    have hj8 : j < 8 := by omega
    obtain ⟨f, rfl⟩ := Nat.exists_eq_add_of_le' hf
    obtain ⟨L', m, k0, k2, k3, k4, k5, hrun⟩ := l2c_inner_loop (d1 := d1) (jh := jh) (hp := hp) hres hsf leaf ox oy
      j hj8 8 0 (innerLocs L leaf ox.toUInt32 oy.toUInt32 (jh.objects.size + 1) (UInt32.ofNat j) (UInt32.ofNat 0))
      rfl (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal])
      (by simp [setLocal])
    rw [← outerLocs_absorb h0 h2 h3 h4 h5, show f + (234 * (r + 1) + 5) = (f + 234 * r + 5 + 229) + 5 by omega,
      l2c_outer_head _ _ _ _ _ _ hj8, show f + 234 * r + 5 + 229 = (f + 234 * r + 5) + 28 * 8 + 5 by omega]
    have e : allPart leaf ox oy j = allPart leaf ox oy j ++ rowPart leaf ox oy j 0 := by
      simp [rowPart]
    rw [e, hrun]
    exact ih (j + 1) L' _ (by omega) (by omega) k0 k2 k3 k4 k5

theorem leafToCoordinates_fast_nz {rp : String → Option (List JvmInstr)} {d1 sf : Nat} (hres : ResolvesMccProgs rp)
    (hsf : 45 ≤ sf) (leaf : UInt64) (hl : leaf ≠ 0) (ox oy : Int32) {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (f : Nat) :
    ∃ pc stk locs,
      Jvm.runJvmResFast (mkAlgKotlinHooks rp (d1 + 1) sf) (f + 1888) MacroCellCoordinatesKt_leafToCoordinates_prog 0 MacroCellCoordinatesKt_leafToCoordinates_prog
          (Jvm.initJvmState [(0, .i64 leaf), (2, .i32 ox.toUInt32), (3, .i32 oy.toUInt32)] (.i32 0) hp jh) =
        some (.heapRef (jh.objects.size + 1),
          ⟨pc, stk, locs, lhsHeap jh (encodeCoords (allPart leaf ox oy 8)), hp⟩) := by
  obtain ⟨L, h0, h2, h3, h4, h5, hpre⟩ := l2c_prefix (rp := rp) (d1 := d1) (sf := sf) (jh := jh) (hp := hp) leaf hl
    ox oy (f + 1877)
  rw [show f + 1888 = (f + 1877) + 11 by omega, hpre]
  exact l2c_outer_loop (d1 := d1) (jh := jh) (hp := hp) hres hsf leaf ox oy 8 0 L (f + 1877) rfl (by omega)
    h0 h2 h3 h4 h5

theorem leafToCoordinates_fast_zero {rp : String → Option (List JvmInstr)} {d1 sf : Nat} (ox oy : Int32)
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} (f : Nat) :
    ∃ pc stk locs,
      Jvm.runJvmResFast (mkAlgKotlinHooks rp (d1 + 1) sf) (f + 6) MacroCellCoordinatesKt_leafToCoordinates_prog 0 MacroCellCoordinatesKt_leafToCoordinates_prog
          (Jvm.initJvmState [(0, .i64 0), (2, .i32 ox.toUInt32), (3, .i32 oy.toUInt32)] (.i32 0) hp jh) =
        some (.heapRef (allocAlgKotlinColl jh "kotlin/collections/EmptySet" #[]).1,
          ⟨pc, stk, locs, (allocAlgKotlinColl jh "kotlin/collections/EmptySet" #[]).2, hp⟩) := by
  refine ⟨?pc, ?stk, ?locs, ?main⟩
  case main =>
    conv => lhs; arg 5; dsimp only [MacroCellCoordinatesKt_leafToCoordinates_prog]
    mcc_step_blk
    refine (Jvm.runJvmResFast_ifne_fallthrough _ ((Jvm.lcmp_eq_zero _ _ _).2 rfl)).trans ?_
    mcc_rfl_step
    exact fast_areturn

/--
`leafToCoordinates(leaf, offsetX, offsetY)` on the JVM computes `leafToCoordinatesModel`: it returns a fresh set
holding the model's coordinates in its iteration order (row-major), which is the only heap effect. For `leaf == 0`
the set is `emptySet()`; otherwise it is the `LinkedHashSet` that `mutableSetOf()` creates.
-/
theorem leafToCoordinates_equiv (rp : String → Option (List JvmInstr)) (hres : ResolvesMccProgs rp)
    (d sf fuel : Nat) (hd : 1 ≤ d) (hsf : 45 ≤ sf) (hf : 1888 ≤ fuel) (leaf : UInt64) (ox oy : Int32)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    (Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) fuel MacroCellCoordinatesKt_leafToCoordinates_prog
        (Jvm.initJvmState [(0, .i64 leaf), (2, .i32 ox.toUInt32), (3, .i32 oy.toUInt32)] (.i32 0) hp jh)).map
        (fun r => (r.1, r.2.jvmHeap, r.2.heap)) =
      some (.heapRef (allocAlgKotlinColl jh
          (if leaf = 0 then "kotlin/collections/EmptySet" else "java/util/LinkedHashSet")
          (encodeCoords (leafToCoordinatesModel leaf ox oy))).1,
        (allocAlgKotlinColl jh (if leaf = 0 then "kotlin/collections/EmptySet" else "java/util/LinkedHashSet")
          (encodeCoords (leafToCoordinatesModel leaf ox oy))).2, hp) := by
  obtain ⟨d1, rfl⟩ := Nat.exists_eq_add_of_le' hd
  by_cases hl : leaf = 0
  · subst hl
    obtain ⟨f, rfl⟩ := Nat.exists_eq_add_of_le' (show 6 ≤ fuel by omega)
    obtain ⟨pc, stk, locs, h⟩ := leafToCoordinates_fast_zero (rp := rp) (d1 := d1) (sf := sf) (hp := hp) ox oy
      (jh := jh) f
    rw [Jvm.runJvmRes_of_runJvmResFast0 _ _ _ _ _ rfl h]
    rfl
  · obtain ⟨f, rfl⟩ := Nat.exists_eq_add_of_le' hf
    obtain ⟨pc, stk, locs, h⟩ := leafToCoordinates_fast_nz (d1 := d1) (hp := hp) (jh := jh) hres hsf leaf hl ox oy f
    rw [Jvm.runJvmRes_of_runJvmResFast0 _ _ _ _ _ rfl h, leafToCoordinatesModel_eq leaf ox oy hl]
    simp only [hl, ↓reduceIte, lhsHeap_size]
    rfl

/-! ### `leafToCoordinates` calls and `$default` -/

theorem exists_of_map {r : Option (JvmVal × JvmState)} {v : JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (h : r.map (fun r => (r.1, r.2.jvmHeap, r.2.heap)) = some (v, jh, hp)) :
    ∃ endSt : JvmState, r = some (v, endSt) ∧ endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  cases r with
  | none => simp at h
  | some p =>
    obtain ⟨v', endSt⟩ := p
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨endSt, rfl, rfl, rfl⟩

/-- The set that `leafToCoordinates(leaf, ox, oy)` allocates on `jh`, and the heap after it. -/
def l2cAlloc (jh : Jvm.JvmHeap AlgExt) (leaf : UInt64) (ox oy : Int32) : Nat × Jvm.JvmHeap AlgExt :=
  allocAlgKotlinColl jh (if leaf = 0 then "kotlin/collections/EmptySet" else "java/util/LinkedHashSet")
    (encodeCoords (leafToCoordinatesModel leaf ox oy))

set_option maxRecDepth 4096 in
theorem tags_JII : Jvm.parseMethodParamTags "(JII)Ljava/util/Set;" = ['J', 'I', 'I'] := by decide

/-- A call of the lifted `leafToCoordinates` pushes the set it allocates. -/
theorem fast_call_leafToCoordinates {rp : String → Option (List JvmInstr)} {d1 sf : Nat}
    (hres : ResolvesMccProgs rp) (hsf : 45 ≤ sf) (hsf2 : 1888 ≤ sf) {leaf : UInt64} {ox oy : Int32}
    {u v : UInt32} (hu : u = ox.toUInt32) (hv : v = oy.toUInt32)
    {f pc pc0 : Nat} {prog rest : List JvmInstr} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    Jvm.runJvmResFast (mkAlgKotlinHooks rp (d1 + 2) sf) (f + 1) prog pc
        (.invokestatic "com/alexvanyo/composelife/algorithm/MacroCellCoordinatesKt" "leafToCoordinates" "(JII)Ljava/util/Set;" :: rest)
        ⟨pc0, .i32 v :: .i32 u :: .i64 leaf :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkAlgKotlinHooks rp (d1 + 2) sf) f prog (pc + 1) rest
        ⟨pc + 1, .heapRef (l2cAlloc jh leaf ox oy).1 :: stk, locs, (l2cAlloc jh leaf ox oy).2, hp⟩ := by
  subst hu hv
  obtain ⟨endSt, hrun, hj, hh⟩ :=
    exists_of_map (leafToCoordinates_equiv rp hres (d1 + 1) sf sf (by omega) hsf hsf2 leaf ox oy jh hp)
  have hs := stepMccStatic (d1 := d1 + 1) (st := ⟨pc, .i32 oy.toUInt32 :: .i32 ox.toUInt32 :: .i64 leaf :: stk,
      locs, jh, hp⟩) (method := "leafToCoordinates") (stkRest := stk) (endSt := endSt)
    ['J', 'I', 'I'] (args := [.i64 leaf, .i32 ox.toUInt32, .i32 oy.toUInt32]) tags_JII rfl rfl
    hres.2.2.1 hrun (by decide +kernel)
  rw [hj, hh] at hs
  exact Jvm.runJvmResFast_invokestatic_step _ hs

theorem leafToCoordinates_default_fast {rp : String → Option (List JvmInstr)} {d1 sf : Nat}
    (hres : ResolvesMccProgs rp) (hsf : 45 ≤ sf) (hsf2 : 1888 ≤ sf) (leaf : UInt64) (ox oy : Int32)
    (mask : UInt32) (marker : JvmVal) {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} (f : Nat) :
    ∃ pc stk locs',
      Jvm.runJvmResFast (mkAlgKotlinHooks rp (d1 + 2) sf) (f + 17) MacroCellCoordinatesKt_leafToCoordinates_default_prog 0
          MacroCellCoordinatesKt_leafToCoordinates_default_prog
          (Jvm.initJvmState [(0, .i64 leaf), (2, .i32 ox.toUInt32), (3, .i32 oy.toUInt32), (4, .i32 mask),
            (5, marker)] (.i32 0) hp jh) =
        some (.heapRef (l2cAlloc jh leaf (dflt mask 2 ox) (dflt mask 4 oy)).1,
          ⟨pc, stk, locs', (l2cAlloc jh leaf (dflt mask 2 ox) (dflt mask 4 oy)).2, hp⟩) := by
  by_cases h2 : mask &&& 2 = 0 <;> by_cases h4 : mask &&& 4 = 0
  all_goals
    refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left 3
    conv => lhs; arg 5; dsimp only [MacroCellCoordinatesKt_leafToCoordinates_default_prog]
    mcc_step_blk
    first
      | refine (Jvm.runJvmResFast_ifeq_branch _ h2).trans ?_
      | refine (Jvm.runJvmResFast_ifeq_fallthrough _ (by simpa using h2)).trans ?_
    mcc_step_blk
    first
      | refine (Jvm.runJvmResFast_ifeq_branch _ h4).trans ?_
      | refine (Jvm.runJvmResFast_ifeq_fallthrough _ (by simpa using h4)).trans ?_
    mcc_step_blk
    refine (fast_call_leafToCoordinates hres hsf hsf2 (ox := dflt mask 2 ox) (oy := dflt mask 4 oy)
      (by simp only [dflt, h2, ↓reduceIte] <;> rfl) (by simp only [dflt, h4, ↓reduceIte] <;> rfl)).trans ?_
    exact fast_areturn

/--
`leafToCoordinates$default(leaf, offsetX, offsetY, mask, marker)` computes `leafToCoordinatesModel` with each offset
replaced by `0` when its default-argument bit (`2` for `offsetX`, `4` for `offsetY`) is set in `mask`; the result
and heap effect are those of `leafToCoordinates_equiv`.
-/
theorem leafToCoordinates_default_equiv (rp : String → Option (List JvmInstr)) (hres : ResolvesMccProgs rp)
    (d sf fuel : Nat) (hd : 2 ≤ d) (hsf : 45 ≤ sf) (hsf2 : 1888 ≤ sf) (hf : 17 ≤ fuel) (leaf : UInt64)
    (ox oy : Int32) (mask : UInt32) (marker : JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    (Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) fuel MacroCellCoordinatesKt_leafToCoordinates_default_prog
        (Jvm.initJvmState [(0, .i64 leaf), (2, .i32 ox.toUInt32), (3, .i32 oy.toUInt32), (4, .i32 mask),
          (5, marker)] (.i32 0) hp jh)).map
        (fun r => (r.1, r.2.jvmHeap, r.2.heap)) =
      let ox' := if mask &&& 2 = 0 then ox else 0
      let oy' := if mask &&& 4 = 0 then oy else 0
      some (.heapRef (allocAlgKotlinColl jh
          (if leaf = 0 then "kotlin/collections/EmptySet" else "java/util/LinkedHashSet")
          (encodeCoords (leafToCoordinatesModel leaf ox' oy'))).1,
        (allocAlgKotlinColl jh (if leaf = 0 then "kotlin/collections/EmptySet" else "java/util/LinkedHashSet")
          (encodeCoords (leafToCoordinatesModel leaf ox' oy'))).2, hp) := by
  obtain ⟨d1, rfl⟩ := Nat.exists_eq_add_of_le' hd
  obtain ⟨f, rfl⟩ := Nat.exists_eq_add_of_le' hf
  obtain ⟨pc, stk, locs, h⟩ := leafToCoordinates_default_fast (d1 := d1) (jh := jh) (hp := hp) hres hsf hsf2 leaf
    ox oy mask marker f
  rw [Jvm.runJvmRes_of_runJvmResFast0 _ _ _ _ _ rfl h]
  rfl

/-! ### `coordinatesToLevel4` -/

theorem algKotlinColl_alloc {jh : Jvm.JvmHeap AlgExt} {a : Nat} {x : String × Nat × String × Array JvmVal}
    (o : Jvm.HeapObj AlgExt) (h : algKotlinColl? jh a = some x) : algKotlinColl? (jh.alloc o).2 a = some x := by
  unfold algKotlinColl? at h ⊢
  split at h <;> try contradiction
  rename_i cls fields hobj
  rw [heap_get_alloc_lt _ (Jvm.jvmHeap_get?_some_lt hobj), hobj]
  simp only
  split at h <;> try contradiction
  rename_i hcls
  simp only [hcls, ↓reduceIte]
  split at h <;> try contradiction
  rename_i arrAddr hfind
  simp only [hfind]
  split at h <;> try contradiction
  rename_i ec es harr
  rw [heap_get_alloc_lt _ (Jvm.jvmHeap_get?_some_lt harr), harr]
  exact h

/-- The heap after `coordinatesToLevel4`: its four `coordinatesToLeaf` calls each allocate one iterator. -/
def iter4 (jh : Jvm.JvmHeap AlgExt) (arrAddr n : Nat) : Jvm.JvmHeap AlgExt :=
  ((((jh.alloc (iterObj arrAddr n)).2.alloc (iterObj arrAddr n)).2.alloc (iterObj arrAddr n)).2.alloc
    (iterObj arrAddr n)).2

/-- `MacroCell.Level4Node`'s companion class and the static field that holds it. -/
abbrev level4Node : String := "com/alexvanyo/composelife/model/MacroCell$Level4Node"
abbrev level4Companion : String := "com/alexvanyo/composelife/model/MacroCell$Level4Node$Companion"

/-- `Level4Node.Companion` reads as the companion singleton when the static is unset (the hooks resolve it) or holds
that singleton. -/
theorem fast_getCompanion {rp : String → Option (List JvmInstr)} {d sf f pc pc0 : Nat}
    {prog rest : List JvmInstr} {desc : String}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hcomp : jh.getStatic? level4Node "Companion" = none ∨
      jh.getStatic? level4Node "Companion" = some (.allocRef level4Companion)) :
    Jvm.runJvmResFast (mkAlgKotlinHooks rp d sf) (f + 1) prog pc (.getstatic level4Node "Companion" desc :: rest)
        ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkAlgKotlinHooks rp d sf) f prog (pc + 1) rest
        ⟨pc + 1, .allocRef level4Companion :: stk, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  dsimp only [Jvm.stepInstr]
  rcases hcomp with h | h <;> rw [h]
  cases d <;> rfl

theorem int32_add8_toUInt32 (o : Int32) : o.toUInt32 + 8 = (o + 8).toUInt32 := by
  rw [Int32.toUInt32_add]; rfl

theorem coordinatesToLevel4_fast {rp : String → Option (List JvmInstr)} {d1 sf : Nat}
    (hres : ResolvesMccProgs rp) (hsf : 45 ≤ sf) (coords : List (Int32 × Int32)) (h32 : coords.length < 2 ^ 32)
    (hsf2 : 60 * coords.length + 14 ≤ sf) (ox oy : Int32)
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {setAddr arrAddr : Nat} {cls ec : String}
    (hcoll : algKotlinColl? jh setAddr = some (cls, arrAddr, ec, encodeCoords coords))
    (hcomp : jh.getStatic? level4Node "Companion" = none ∨
      jh.getStatic? level4Node "Companion" = some (.allocRef level4Companion)) (f : Nat) :
    ∃ pc stk locs',
      Jvm.runJvmResFast (mkAlgKotlinHooks rp (d1 + 2) sf) (f + 34) MacroCellCoordinatesKt_coordinatesToLevel4_prog 0
          MacroCellCoordinatesKt_coordinatesToLevel4_prog
          (Jvm.initJvmState [(0, .heapRef setAddr), (1, .i32 ox.toUInt32), (2, .i32 oy.toUInt32)] (.i32 0) hp jh) =
        some (.ext (.mc (Algorithm.makeLevel4Node (coordinatesToLevel4Model coords ox oy).nw
            (coordinatesToLevel4Model coords ox oy).ne (coordinatesToLevel4Model coords ox oy).sw
            (coordinatesToLevel4Model coords ox oy).se)),
          ⟨pc, stk, locs', iter4 jh arrAddr coords.length, hp⟩) := by
  have hc1 := algKotlinColl_alloc (iterObj arrAddr coords.length) hcoll
  have hc2 := algKotlinColl_alloc (iterObj arrAddr coords.length) hc1
  have hc3 := algKotlinColl_alloc (iterObj arrAddr coords.length) hc2
  refine ⟨?pc, ?stk, ?locs, ?main⟩
  case main =>
    conv => lhs; arg 5; dsimp only [MacroCellCoordinatesKt_coordinatesToLevel4_prog]
    mcc_step_blk
    mcc_rfl_step
    refine (fast_getCompanion hcomp).trans ?_
    mcc_step_blk
    refine (fast_call_coordinatesToLeaf hres hsf h32 hsf2 rfl rfl hcoll).trans ?_
    mcc_rfl_step
    rw [int32_add8_toUInt32]
    refine (fast_call_coordinatesToLeaf hres hsf h32 hsf2 rfl rfl hc1).trans ?_
    mcc_rfl_step
    rw [int32_add8_toUInt32]
    refine (fast_call_coordinatesToLeaf hres hsf h32 hsf2 rfl rfl hc2).trans ?_
    mcc_rfl_step
    rw [int32_add8_toUInt32, int32_add8_toUInt32]
    refine (fast_call_coordinatesToLeaf hres hsf h32 hsf2 rfl rfl hc3).trans ?_
    mcc_rfl_step
    mcc_rfl_step
    exact fast_areturn

/--
`coordinatesToLevel4(coordinates, offsetX, offsetY)` on the JVM computes `coordinatesToLevel4Model`: it returns the
`Level4Node` of the model's four quadrant leaves, and its only heap effect is the four iterators that its
`coordinatesToLeaf` calls allocate. `Level4Node.Companion` is the companion singleton (or not yet stored).
-/
theorem coordinatesToLevel4_equiv (rp : String → Option (List JvmInstr)) (hres : ResolvesMccProgs rp)
    (d sf fuel : Nat) (hd : 2 ≤ d) (hsf : 45 ≤ sf) (coords : List (Int32 × Int32)) (h32 : coords.length < 2 ^ 32)
    (hsf2 : 60 * coords.length + 14 ≤ sf) (hf : 34 ≤ fuel) (ox oy : Int32) (jh : Jvm.JvmHeap AlgExt)
    (hp : AlgHeap) (setAddr arrAddr : Nat) (cls ec : String)
    (hcoll : algKotlinColl? jh setAddr = some (cls, arrAddr, ec, encodeCoords coords))
    (hcomp : jh.getStatic? level4Node "Companion" = none ∨
      jh.getStatic? level4Node "Companion" = some (.allocRef level4Companion)) :
    (Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) fuel MacroCellCoordinatesKt_coordinatesToLevel4_prog
        (Jvm.initJvmState [(0, .heapRef setAddr), (1, .i32 ox.toUInt32), (2, .i32 oy.toUInt32)] (.i32 0) hp jh)).map
        (fun r => (r.1, r.2.jvmHeap, r.2.heap)) =
      let q := coordinatesToLevel4Model coords ox oy
      some (.ext (.mc (Algorithm.makeLevel4Node q.nw q.ne q.sw q.se)), iter4 jh arrAddr coords.length, hp) := by
  obtain ⟨d1, rfl⟩ := Nat.exists_eq_add_of_le' hd
  obtain ⟨f, rfl⟩ := Nat.exists_eq_add_of_le' hf
  obtain ⟨pc, stk, locs, h⟩ := coordinatesToLevel4_fast (d1 := d1) (hp := hp) hres hsf coords h32 hsf2 ox oy
    hcoll hcomp f
  rw [Jvm.runJvmRes_of_runJvmResFast0 _ _ _ _ _ rfl h]
  rfl

set_option maxRecDepth 4096 in
theorem tags_LII_l4 :
    Jvm.parseMethodParamTags "(Ljava/util/Set;II)Lcom/alexvanyo/composelife/model/MacroCell$Level4Node;" =
      ['L', 'I', 'I'] := by decide

/-- A call of the lifted `coordinatesToLevel4` pushes the model's `Level4Node`. -/
theorem fast_call_coordinatesToLevel4 {rp : String → Option (List JvmInstr)} {d1 sf : Nat}
    (hres : ResolvesMccProgs rp) (hsf : 45 ≤ sf) {coords : List (Int32 × Int32)} (h32 : coords.length < 2 ^ 32)
    (hsf2 : 60 * coords.length + 14 ≤ sf) (hsf3 : 34 ≤ sf) {ox oy : Int32} {u v : UInt32} (hu : u = ox.toUInt32)
    (hv : v = oy.toUInt32)
    {f pc pc0 : Nat} {prog rest : List JvmInstr} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {setAddr arrAddr : Nat} {cls ec : String}
    (hcoll : algKotlinColl? jh setAddr = some (cls, arrAddr, ec, encodeCoords coords))
    (hcomp : jh.getStatic? level4Node "Companion" = none ∨
      jh.getStatic? level4Node "Companion" = some (.allocRef level4Companion)) :
    Jvm.runJvmResFast (mkAlgKotlinHooks rp (d1 + 3) sf) (f + 1) prog pc
        (.invokestatic "com/alexvanyo/composelife/algorithm/MacroCellCoordinatesKt" "coordinatesToLevel4"
          "(Ljava/util/Set;II)Lcom/alexvanyo/composelife/model/MacroCell$Level4Node;" :: rest)
        ⟨pc0, .i32 v :: .i32 u :: .heapRef setAddr :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkAlgKotlinHooks rp (d1 + 3) sf) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.mc (Algorithm.makeLevel4Node (coordinatesToLevel4Model coords ox oy).nw
            (coordinatesToLevel4Model coords ox oy).ne (coordinatesToLevel4Model coords ox oy).sw
            (coordinatesToLevel4Model coords ox oy).se)) :: stk, locs,
          iter4 jh arrAddr coords.length, hp⟩ := by
  subst hu hv
  obtain ⟨endSt, hrun, hj, hh⟩ := exists_of_map (coordinatesToLevel4_equiv rp hres (d1 + 2) sf sf (by omega) hsf
    coords h32 hsf2 hsf3 ox oy jh hp setAddr arrAddr cls ec hcoll hcomp)
  have hs := stepMccStatic (d1 := d1 + 2) (st := ⟨pc, .i32 oy.toUInt32 :: .i32 ox.toUInt32 :: .heapRef setAddr :: stk,
      locs, jh, hp⟩) (method := "coordinatesToLevel4") (stkRest := stk) (endSt := endSt)
    ['L', 'I', 'I'] (args := [.heapRef setAddr, .i32 ox.toUInt32, .i32 oy.toUInt32]) tags_LII_l4 rfl rfl
    hres.2.2.2 hrun (by decide +kernel)
  rw [hj, hh] at hs
  exact Jvm.runJvmResFast_invokestatic_step _ hs

theorem coordinatesToLevel4_default_fast {rp : String → Option (List JvmInstr)} {d1 sf : Nat}
    (hres : ResolvesMccProgs rp) (hsf : 45 ≤ sf) (coords : List (Int32 × Int32)) (h32 : coords.length < 2 ^ 32)
    (hsf2 : 60 * coords.length + 14 ≤ sf) (hsf3 : 34 ≤ sf) (ox oy : Int32) (mask : UInt32) (marker : JvmVal)
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {setAddr arrAddr : Nat} {cls ec : String}
    (hcoll : algKotlinColl? jh setAddr = some (cls, arrAddr, ec, encodeCoords coords))
    (hcomp : jh.getStatic? level4Node "Companion" = none ∨
      jh.getStatic? level4Node "Companion" = some (.allocRef level4Companion)) (f : Nat) :
    ∃ pc stk locs',
      Jvm.runJvmResFast (mkAlgKotlinHooks rp (d1 + 3) sf) (f + 17) MacroCellCoordinatesKt_coordinatesToLevel4_default_prog 0
          MacroCellCoordinatesKt_coordinatesToLevel4_default_prog
          (Jvm.initJvmState [(0, .heapRef setAddr), (1, .i32 ox.toUInt32), (2, .i32 oy.toUInt32), (3, .i32 mask),
            (4, marker)] (.i32 0) hp jh) =
        some (.ext (.mc (Algorithm.makeLevel4Node
            (coordinatesToLevel4Model coords (dflt mask 2 ox) (dflt mask 4 oy)).nw
            (coordinatesToLevel4Model coords (dflt mask 2 ox) (dflt mask 4 oy)).ne
            (coordinatesToLevel4Model coords (dflt mask 2 ox) (dflt mask 4 oy)).sw
            (coordinatesToLevel4Model coords (dflt mask 2 ox) (dflt mask 4 oy)).se)),
          ⟨pc, stk, locs', iter4 jh arrAddr coords.length, hp⟩) := by
  by_cases h2 : mask &&& 2 = 0 <;> by_cases h4 : mask &&& 4 = 0
  all_goals
    refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left 3
    conv => lhs; arg 5; dsimp only [MacroCellCoordinatesKt_coordinatesToLevel4_default_prog]
    mcc_step_blk
    first
      | refine (Jvm.runJvmResFast_ifeq_branch _ h2).trans ?_
      | refine (Jvm.runJvmResFast_ifeq_fallthrough _ (by simpa using h2)).trans ?_
    mcc_step_blk
    first
      | refine (Jvm.runJvmResFast_ifeq_branch _ h4).trans ?_
      | refine (Jvm.runJvmResFast_ifeq_fallthrough _ (by simpa using h4)).trans ?_
    mcc_step_blk
    refine (fast_call_coordinatesToLevel4 hres hsf h32 hsf2 hsf3 (ox := dflt mask 2 ox) (oy := dflt mask 4 oy)
      (by simp only [dflt, h2, ↓reduceIte] <;> rfl) (by simp only [dflt, h4, ↓reduceIte] <;> rfl) hcoll
      hcomp).trans ?_
    exact fast_areturn

/--
`coordinatesToLevel4$default(coordinates, offsetX, offsetY, mask, marker)` computes `coordinatesToLevel4Model` with
each offset replaced by `0` when its default-argument bit (`2` for `offsetX`, `4` for `offsetY`) is set in `mask`;
the heap effect is that of `coordinatesToLevel4_equiv`.
-/
theorem coordinatesToLevel4_default_equiv (rp : String → Option (List JvmInstr)) (hres : ResolvesMccProgs rp)
    (d sf fuel : Nat) (hd : 3 ≤ d) (hsf : 45 ≤ sf) (coords : List (Int32 × Int32)) (h32 : coords.length < 2 ^ 32)
    (hsf2 : 60 * coords.length + 14 ≤ sf) (hsf3 : 34 ≤ sf) (hf : 17 ≤ fuel) (ox oy : Int32) (mask : UInt32)
    (marker : JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (setAddr arrAddr : Nat) (cls ec : String)
    (hcoll : algKotlinColl? jh setAddr = some (cls, arrAddr, ec, encodeCoords coords))
    (hcomp : jh.getStatic? level4Node "Companion" = none ∨
      jh.getStatic? level4Node "Companion" = some (.allocRef level4Companion)) :
    (Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) fuel MacroCellCoordinatesKt_coordinatesToLevel4_default_prog
        (Jvm.initJvmState [(0, .heapRef setAddr), (1, .i32 ox.toUInt32), (2, .i32 oy.toUInt32), (3, .i32 mask),
          (4, marker)] (.i32 0) hp jh)).map
        (fun r => (r.1, r.2.jvmHeap, r.2.heap)) =
      let q := coordinatesToLevel4Model coords (if mask &&& 2 = 0 then ox else 0) (if mask &&& 4 = 0 then oy else 0)
      some (.ext (.mc (Algorithm.makeLevel4Node q.nw q.ne q.sw q.se)), iter4 jh arrAddr coords.length, hp) := by
  obtain ⟨d1, rfl⟩ := Nat.exists_eq_add_of_le' hd
  obtain ⟨f, rfl⟩ := Nat.exists_eq_add_of_le' hf
  obtain ⟨pc, stk, locs, h⟩ := coordinatesToLevel4_default_fast (d1 := d1) (hp := hp) hres hsf coords h32 hsf2
    hsf3 ox oy mask marker hcoll hcomp f
  rw [Jvm.runJvmRes_of_runJvmResFast0 _ _ _ _ _ rfl h]
  rfl

end Algorithm.KotlinJvmVerification.MacroCellCoordinates