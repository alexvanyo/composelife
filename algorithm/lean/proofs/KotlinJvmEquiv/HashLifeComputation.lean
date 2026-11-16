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
import models.HashLifeComputationModel
import theorems.HashLifeComputationModelTheorems
import theorems.BitComputationTheorems
import proofs.KotlinJvmEquiv.AlgKotlinProgs
import proofs.KotlinJvmEquiv.BitComputation

/-!
# JVM bytecode equivalence for `HashLifeComputation.kt`

Every lifted method of `HashLifeComputationKt` and of its two function-reference classes
(`HashLifeComputationKt$computeLevel4NextGeneration$1`/`$2`) is proven to compute the standalone model of
`models/HashLifeComputationModel.lean`, under `mkAlgKotlinHooks resolveProg depth subFuel` for every lookup
`resolveProg` that extends `algKotlinProgLookup` (`ExtendsAlgKotlinProgs`). Calls between lifted methods are not
modeled: they run the callee's lifted program, so each theorem asks for enough call depth and callee fuel.

The default leaf kernel of `computeLevel4NextGeneration` (`ULong::computeNextGenerationPureKotlin`) runs the lifted
`BitComputationKt` programs; their results under `mkAlgKotlinHooks` are transferred from the `algHooks` proofs of
`BitComputation.lean` (`runJvmRes_transfer`: both hooks step every instruction of those programs identically).
-/

namespace Algorithm.KotlinJvmVerification

open Algorithm.JvmVerification
open Algorithm.KotlinJvmBytecode
open Algorithm.KotlinModel

namespace HashLifeComputation

/-! ### Lookup, hooks and generic run lemmas -/

/-- `resolveProg` maps every tag of `algKotlinProgLookup` to the same lifted program. -/
def ExtendsAlgKotlinProgs (resolveProg : String → Option (List JvmInstr)) : Prop :=
  ∀ tag prog, algKotlinProgLookup tag = some prog → resolveProg tag = some prog

theorem algKotlinProgLookup_extends : ExtendsAlgKotlinProgs algKotlinProgLookup :=
  fun _ _ h => h

instance hlcHasDefaultIsZero (resolveProg : String → Option (List JvmInstr)) (d subFuel : Nat) :
    Jvm.HasDefaultIsZero (mkAlgKotlinHooks resolveProg d subFuel) where
  isZero?_eq := by cases d <;> rfl

/--
A run under `H2` with more fuel gives the result of a run under `H1`, when both hooks step every instruction of
`prog` identically and agree on the two hook fields that branches read.
-/
theorem runJvmRes_transfer {Ext Heap : Type} (H1 H2 : Jvm.JvmHooks Ext Heap) (prog : List JvmInstr)
    (hz : H1.isZero? = H2.isZero?) (hr : H1.beqRefExt = H2.beqRefExt)
    (hs : ∀ i ∈ prog, ∀ st, Jvm.stepInstr H1 i st = Jvm.stepInstr H2 i st) :
    ∀ (n m : Nat) (st : Jvm.JvmState Ext Heap) (r : Jvm.JvmVal Ext × Jvm.JvmState Ext Heap),
      Jvm.runJvmRes H1 n prog st = some r → Jvm.runJvmRes H2 (n + m) prog st = some r := by
  intro n
  induction n with
  | zero => intro m st r h; simp [Jvm.runJvmRes] at h
  | succ n ih =>
    intro m st r h
    rw [show n + 1 + m = (n + m) + 1 by omega]
    rw [Jvm.runJvmRes.eq_2] at h ⊢
    rw [hz, hr] at h
    cases hpc : prog[st.pc]? with
    | none => simp [hpc] at h
    | some i =>
      have hmem : i ∈ prog := List.mem_of_getElem? hpc
      simp only [hpc] at h ⊢
      cases i <;> simp only [] at h ⊢
      all_goals first
        | (rw [hs _ hmem] at h
           rcases hstep : Jvm.stepInstr H2 _ st with (_ | st') | (_ | res) <;> simp only [hstep] at h ⊢
           all_goals first | exact ih m _ r h | exact h | cases h)
        | (revert h
           repeat' split
           all_goals (intro h; first | exact ih m _ r h | cases h))

/-- Instructions that `algHooks` and `mkAlgKotlinHooks` step identically (checked in `stepInstr_alg_eq_kotlin`). -/
def algKotlinAgreeInstr : JvmInstr → Bool
  | .ior | .iand | .ishl | .iushr | .iconst _ | .lload _ | .l2i | .iload _ | .iaload | .baload | .aload _
  | .lushr | .lconst _ | .land | .ireturn | .lcmp | .istore _ | .astore _ | .ifne _ => true
  | .getstatic c f _ => c == "com/alexvanyo/composelife/algorithm/BitComputationKt" && f == "QUAD_INFO_LUT"
  | .invokestatic c m d =>
    c == "com/alexvanyo/composelife/algorithm/AlgorithmLeanKt" && m == "getNEXT_GEN_4X4_LUT" && d == "()[B"
  | _ => false

theorem stepInstr_alg_eq_kotlin (r : String → Option (List JvmInstr)) (d sf : Nat) (i : JvmInstr)
    (h : algKotlinAgreeInstr i = true) (st : JvmState) :
    Jvm.stepInstr algHooks i st = Jvm.stepInstr (mkAlgKotlinHooks r d sf) i st := by
  cases i <;> simp only [algKotlinAgreeInstr, Bool.false_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  case getstatic c f desc =>
    obtain ⟨rfl, rfl⟩ := h
    cases d <;> rfl
  case invokestatic c m desc =>
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    cases d <;> rfl
  all_goals (cases d <;> rfl)

theorem pureKotlin_prog_agree :
    BitComputationKt_computeNextGenerationPureKotlin_prog.all algKotlinAgreeInstr = true := by decide

/-- Stop predicate for the block stepper: calls, statics, casts, returns and branches. -/
def isHlcStop : JvmInstr → Bool
  | .invokestatic _ _ _ | .invokevirtual _ _ _ | .invokespecial _ _ _ | .invokeinterface _ _ _
  | .invokedynamic _ _ _ | .getstatic _ _ _ | .putstatic _ _ _ | .getfield _ _ _ | .putfield _ _ _
  | .newClass _ | .checkcast _ | .instanceof _ | .idiv | .ldiv | .athrow
  | .areturn | .ireturn | .lreturn | .freturn | .dreturn | .vreturn
  | .ifeq _ | .ifne _ | .iflt _ | .ifle _ | .ifgt _ | .ifge _
  | .ifnull _ | .ifnonnull _ | .if_icmpeq _ | .if_icmpne _ | .if_icmplt _
  | .if_icmpge _ | .if_icmpgt _ | .if_icmple _ | .if_acmpeq _ | .if_acmpne _
  | .goto _ | .tableswitch _ _ _ | .lookupswitch _ _ => true
  | _ => false

/-! ### Single-instruction steps -/

section Steps

variable {r : String → Option (List JvmInstr)} {d sf : Nat}

theorem runFast_ulongCtor {f pc pc0 : Nat} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    Jvm.runJvmResFast (mkAlgKotlinHooks r d sf) (f + 1) prog pc
        (.invokestatic "kotlin/ULong" "constructor-impl" "(J)J" :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkAlgKotlinHooks r d sf) f prog (pc + 1) rest ⟨pc + 1, stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_invokestatic_step _ rfl

theorem runFast_ireturn {f pc pc0 : Nat} {prog rest : List JvmInstr} {v : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    Jvm.runJvmResFast (mkAlgKotlinHooks r d sf) (f + 1) prog pc (.ireturn :: rest)
        ⟨pc0, v :: stk, locs, jh, hp⟩ =
      some (v, ⟨pc, v :: stk, locs, jh, hp⟩) := by
  rw [Jvm.runJvmResFast_step_nonbranch _ f prog pc .ireturn rest _ rfl (by simp)]
  cases d <;> rfl

theorem runFast_lreturn {f pc pc0 : Nat} {prog rest : List JvmInstr} {v : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    Jvm.runJvmResFast (mkAlgKotlinHooks r d sf) (f + 1) prog pc (.lreturn :: rest)
        ⟨pc0, v :: stk, locs, jh, hp⟩ =
      some (v, ⟨pc, v :: stk, locs, jh, hp⟩) := by
  rw [Jvm.runJvmResFast_step_nonbranch _ f prog pc .lreturn rest _ rfl (by simp)]
  rfl

theorem runFast_areturn {f pc pc0 : Nat} {prog rest : List JvmInstr} {v : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    Jvm.runJvmResFast (mkAlgKotlinHooks r d sf) (f + 1) prog pc (.areturn :: rest)
        ⟨pc0, v :: stk, locs, jh, hp⟩ =
      some (v, ⟨pc, v :: stk, locs, jh, hp⟩) := by
  rw [Jvm.runJvmResFast_step_nonbranch _ f prog pc .areturn rest _ rfl (by simp)]
  rfl

end Steps

section StepTactics

open Lean Elab Tactic Meta

def hlcOpaqueConsts : NameSet :=
  NameSet.empty
    |>.insert ``mkAlgKotlinHooks
    |>.insert ``algKotlinProgLookup
    |>.insert ``HashLifeComputationKt_computeNextGeneration_prog
    |>.insert ``HashLifeComputationKt_computeNextGeneration_1_prog
    |>.insert ``HashLifeComputationKt_packLeafNode_prog
    |>.insert ``HashLifeComputationKt_LeafNode_prog
    |>.insert ``HashLifeComputationKt_getNw_prog
    |>.insert ``HashLifeComputationKt_getNe_prog
    |>.insert ``HashLifeComputationKt_getSw_prog
    |>.insert ``HashLifeComputationKt_getSe_prog
    |>.insert ``HashLifeComputationKt_centeredSubnodeLevel3_prog
    |>.insert ``HashLifeComputationKt_centeredHorizontalSubnodeLevel3_prog
    |>.insert ``HashLifeComputationKt_centeredVerticalSubnodeLevel3_prog
    |>.insert ``HashLifeComputationKt_centeredSubSubnodeLevel4_prog
    |>.insert ``HashLifeComputationKt_centeredSubSubnodeLevel4_1_prog
    |>.insert ``HashLifeComputationKt_computeLevel4NextGeneration_prog
    |>.insert ``HashLifeComputationKt_computeLevel4NextGeneration_qFGr5tM_default_prog
    |>.insert ``HashLifeComputationKt_computeLevel4NextGeneration_1_prog
    |>.insert ``HashLifeComputationKt_computeLevel4NextGeneration_default_prog
    |>.insert ``HashLifeComputationKt_computeLevel4NextGeneration_1_invoke_prog
    |>.insert ``HashLifeComputationKt_computeLevel4NextGeneration_1_invoke_1_prog
    |>.insert ``HashLifeComputationKt_computeLevel4NextGeneration_2_invoke_prog
    |>.insert ``HashLifeComputationKt_computeLevel4NextGeneration_2_invoke_1_prog
    |>.insert ``BitComputationKt_computeNextGenerationPureKotlin_prog
    |>.insert ``BitComputationKt_computeNextGenerationPureKotlin_1_prog
    |>.insert ``packLeafNodeModel
    |>.insert ``leafNwModel
    |>.insert ``leafNeModel
    |>.insert ``leafSwModel
    |>.insert ``leafSeModel
    |>.insert ``centeredSubnodeLevel3Model
    |>.insert ``centeredHorizontalSubnodeLevel3Model
    |>.insert ``centeredVerticalSubnodeLevel3Model
    |>.insert ``centeredSubSubnodeLevel4Model
    |>.insert ``computeLevel4NextGenerationModel
    |>.insert ``computeNextGenerationPureKotlinModel
    |>.insert ``Algorithm.exportComputeLeafNextGen8x8BranchUInt
    |>.insert ``evalPureKotlinFromHeap

def hlcInitConsts : List Name :=
  [``Jvm.initJvmState]

elab "hlc_whnf_blk" : conv => withMainContext do
  let lhs ← Lean.Elab.Tactic.Conv.getLhs
  let res ← Jvm.Tactics.withOpaque hlcOpaqueConsts
    (Jvm.Tactics.normJvmBlkExpr hlcInitConsts (fun _ => pure none) lhs)
  Lean.Elab.Tactic.Conv.changeLhs res

elab "hlc_norm_locals" : tactic =>
  Lean.Elab.Tactic.liftMetaTactic fun g => do
    let tgt ← instantiateMVars (← g.getType)
    let res ← Jvm.Tactics.normJvmLocalsExpr hlcInitConsts (fun _ => pure none) [] tgt
    return [← g.replaceTargetDefEq res]

elab "hlc_norm_run_args" : tactic =>
  Lean.Elab.Tactic.liftMetaTactic fun g => do
    let tgt ← instantiateMVars (← g.getType)
    let normSt := fun s : Expr => do
      let s1 ← Jvm.Tactics.withOpaque hlcOpaqueConsts
        (Jvm.Tactics.normJvmBlkExpr hlcInitConsts (fun _ => pure none) s)
      if s1.isAppOfArity ``Jvm.JvmState.mk 7 then
        let sa := s1.getAppArgs
        let pcField ← Jvm.Tactics.normJvmNatWith hlcOpaqueConsts sa[2]!
        return mkAppN s1.getAppFn #[sa[0]!, sa[1]!, pcField, sa[3]!, sa[4]!, sa[5]!, sa[6]!]
      else
        return s1
    let normRun := fun b : Expr => do
      if b.isAppOfArity ``Jvm.runJvmResFast 8 then
        let ba := b.getAppArgs
        let fuel' ← Jvm.Tactics.withOpaque hlcOpaqueConsts (whnf ba[3]!)
        let pc' ← Jvm.Tactics.withOpaque hlcOpaqueConsts (whnf ba[5]!)
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

def isHlcNonStop : TacticM Bool := do
  let tgt := (← getMainTarget).consumeMData
  let some (_, lhs, _) := tgt.eq? | return false
  let lhs := lhs.consumeMData
  if lhs.isAppOfArity ``Jvm.runJvmResFast 8 then
    let instrs ← whnf (lhs.getArg! 6)
    if instrs.isAppOfArity ``List.cons 3 then
      let instr := instrs.getArg! 1
      let br ← whnf (mkApp (mkConst ``isHlcStop) instr)
      return br.isConstOf ``Bool.false
  return false

elab "hlc_step_one_chunk" : tactic => do
  let tgt := (← getMainTarget).consumeMData
  let some (_, lhs, _) := tgt.eq? | return ()
  let lhs := lhs.consumeMData
  if !lhs.isAppOfArity ``Jvm.runJvmResFast 8 then return ()
  evalTactic (← `(tactic| (conv => lhs; tactic => hlc_norm_run_args)))
  evalTactic (← `(tactic| rw [Jvm.runJvmResFast_stepBlockChunkWith _ isHlcStop 64]))
  if !(← getUnsolvedGoals).isEmpty then
    evalTactic (← `(tactic| (conv => lhs; arg 2; hlc_whnf_blk)))
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
      evalTactic (← `(tactic| (conv => lhs; tactic => hlc_norm_locals)))
      evalTactic (← `(tactic| (conv => lhs; tactic => hlc_norm_run_args)))

/-- Steps non-stop chunks and `ULong.constructor-impl` calls (the identity) until another stop instruction. -/
elab "hlc_step_blk" : tactic => do
  for _ in [:60] do
    if (← getUnsolvedGoals).isEmpty then break
    if ← isHlcNonStop then
      evalTactic (← `(tactic| hlc_step_one_chunk))
    else
      let ok ← (do
        evalTactic (← `(tactic| rw [runFast_ulongCtor]))
        pure true) <|> pure false
      if ok then
        evalTactic (← `(tactic| (conv => lhs; tactic => hlc_norm_run_args)))
      else
        break

end StepTactics


/-- A fast run from pc 0 that returns `v` in a state with heaps `jh`/`hp` gives the same `runJvmRes` result. -/
theorem exists_of_fast {H : Jvm.JvmHooks AlgExt AlgHeap} {fuel : Nat} {prog : List JvmInstr}
    {st0 : JvmState} {v : JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} (hpc : st0.pc = 0)
    (h : ∃ pc stk locs, Jvm.runJvmResFast H fuel prog 0 prog st0 = some (v, ⟨pc, stk, locs, jh, hp⟩)) :
    ∃ endSt, Jvm.runJvmRes H fuel prog st0 = some (v, endSt) ∧ endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨pc, stk, locs, h⟩ := h
  exact ⟨_, Jvm.runJvmRes_of_runJvmResFast0 H fuel prog st0 _ hpc h, rfl, rfl⟩

/-- Closes `some (v, st) = some (w, ?st)` from `v = w`. -/
theorem some_pair_eq {v w : JvmVal} {st : JvmState} (h : v = w) :
    (some (v, st) : Option (JvmVal × JvmState)) = some (w, st) := by rw [h]

/-- A static call into a lifted method runs the callee's program; a callee that keeps the heaps continues the caller
with its result. -/
theorem runFast_call_static {r : String → Option (List JvmInstr)} {d sf f pc pc0 n : Nat}
    {prog rest callee : List JvmInstr} {C M D : String}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {res : JvmVal}
    (hgen : ∀ st, Jvm.stepInvokeStaticGeneric (mkAlgKotlinHooks r (d + 1) sf) st C M D =
      (mkAlgKotlinHooks r (d + 1) sf).stepInvokeStatic st C M D)
    (hcls : isAlgKotlinLiftedClass C = true)
    (hprog : r (algKotlinTag C M D) = some callee)
    (hn : (Jvm.parseMethodParamTags D).length = n) (hlen : n ≤ stk.length)
    (hv : D.endsWith ")V" = false)
    (hcall : ∃ endSt, Jvm.runJvmRes (mkAlgKotlinHooks r d sf) sf callee
      (Jvm.initJvmState (algKotlinParamSlots 0 (Jvm.parseMethodParamTags D) (stk.take n).reverse) (.i32 0) hp jh) =
        some (res, endSt) ∧ endSt.jvmHeap = jh ∧ endSt.heap = hp) :
    Jvm.runJvmResFast (mkAlgKotlinHooks r (d + 1) sf) (f + 1) prog pc (.invokestatic C M D :: rest)
        ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkAlgKotlinHooks r (d + 1) sf) f prog (pc + 1) rest
        ⟨pc + 1, res :: stk.drop n, locs, jh, hp⟩ := by
  obtain ⟨endSt, hrun, hj, hh⟩ := hcall
  refine Jvm.runJvmResFast_invokestatic_step _ ?_
  rw [hgen]
  have hlt : ¬ stk.length < n := by omega
  subst hn
  have hrun' : Jvm.runJvmRes (mkAlgKotlinHooks r d sf) sf callee
      { pc := 0, stack := [],
        locals := (algKotlinParamSlots 0 (Jvm.parseMethodParamTags D)
          (stk.take (Jvm.parseMethodParamTags D).length).reverse).foldl
            (fun loc (i, v) => Jvm.setLocal loc i v) (fun _ => .i32 0),
        jvmHeap := jh, heap := hp } = some (res, endSt) := hrun
  simp only [mkAlgKotlinHooks, algKotlinHooksWith, hcls, ite_true, hlt, ite_false, hprog, Option.map_some, hrun',
    algKotlinAfterCall, hv, Bool.false_eq_true, hj, hh]

/-- The Lean-compiled leaf kernel `f_Algorithm_exportComputeLeafNextGen8x8BranchUInt` (a leaf hook). -/
theorem runFast_exportLeafKernel {r : String → Option (List JvmInstr)} {d sf f pc pc0 : Nat}
    {prog rest : List JvmInstr} {w : UInt64}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    Jvm.runJvmResFast (mkAlgKotlinHooks r d sf) (f + 1) prog pc
        (.invokestatic "com/alexvanyo/composelife/algorithm/AlgorithmLeanKt"
          "f_Algorithm_exportComputeLeafNextGen8x8BranchUInt-VKZWuLQ" "(J)I" :: rest)
        ⟨pc0, .i64 w :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkAlgKotlinHooks r d sf) f prog (pc + 1) rest
        ⟨pc + 1, .i32 (Algorithm.computeLeafNextGen8x8BranchUInt w) :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_invokestatic_step _ (by cases d <;> rfl)

/-- `MacroCell.Level4Node.getNw` (an `algHooks` leaf hook). -/
theorem runFast_l4GetNw {r : String → Option (List JvmInstr)} {d sf f pc pc0 : Nat}
    {prog rest : List JvmInstr} {h : UInt32} {nw ne sw se : UInt64}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    Jvm.runJvmResFast (mkAlgKotlinHooks r d sf) (f + 1) prog pc
        (.invokevirtual "com/alexvanyo/composelife/model/MacroCell$Level4Node" "getNw-s-VKNKU" "()J" :: rest)
        ⟨pc0, .ext (.mc (.level4Node h nw ne sw se)) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkAlgKotlinHooks r d sf) f prog (pc + 1) rest
        ⟨pc + 1, .i64 nw :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_invokevirtual_step _ (by cases d <;> rfl)

/-- `MacroCell.Level4Node.getNe` (an `algHooks` leaf hook). -/
theorem runFast_l4GetNe {r : String → Option (List JvmInstr)} {d sf f pc pc0 : Nat}
    {prog rest : List JvmInstr} {h : UInt32} {nw ne sw se : UInt64}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    Jvm.runJvmResFast (mkAlgKotlinHooks r d sf) (f + 1) prog pc
        (.invokevirtual "com/alexvanyo/composelife/model/MacroCell$Level4Node" "getNe-s-VKNKU" "()J" :: rest)
        ⟨pc0, .ext (.mc (.level4Node h nw ne sw se)) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkAlgKotlinHooks r d sf) f prog (pc + 1) rest
        ⟨pc + 1, .i64 ne :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_invokevirtual_step _ (by cases d <;> rfl)

/-- `MacroCell.Level4Node.getSw` (an `algHooks` leaf hook). -/
theorem runFast_l4GetSw {r : String → Option (List JvmInstr)} {d sf f pc pc0 : Nat}
    {prog rest : List JvmInstr} {h : UInt32} {nw ne sw se : UInt64}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    Jvm.runJvmResFast (mkAlgKotlinHooks r d sf) (f + 1) prog pc
        (.invokevirtual "com/alexvanyo/composelife/model/MacroCell$Level4Node" "getSw-s-VKNKU" "()J" :: rest)
        ⟨pc0, .ext (.mc (.level4Node h nw ne sw se)) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkAlgKotlinHooks r d sf) f prog (pc + 1) rest
        ⟨pc + 1, .i64 sw :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_invokevirtual_step _ (by cases d <;> rfl)

/-- `MacroCell.Level4Node.getSe` (an `algHooks` leaf hook). -/
theorem runFast_l4GetSe {r : String → Option (List JvmInstr)} {d sf f pc pc0 : Nat}
    {prog rest : List JvmInstr} {h : UInt32} {nw ne sw se : UInt64}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    Jvm.runJvmResFast (mkAlgKotlinHooks r d sf) (f + 1) prog pc
        (.invokevirtual "com/alexvanyo/composelife/model/MacroCell$Level4Node" "getSe-s-VKNKU" "()J" :: rest)
        ⟨pc0, .ext (.mc (.level4Node h nw ne sw se)) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkAlgKotlinHooks r d sf) f prog (pc + 1) rest
        ⟨pc + 1, .i64 se :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_invokevirtual_step _ (by cases d <;> rfl)

/-- Runtime class of the function-reference singleton `HashLifeComputationKt$computeLevel4NextGeneration$1`. -/
abbrev lambdaClass1 : String :=
  "com/alexvanyo/composelife/algorithm/HashLifeComputationKt$computeLevel4NextGeneration$1"

/-- Runtime class of the function-reference singleton `HashLifeComputationKt$computeLevel4NextGeneration$2`. -/
abbrev lambdaClass2 : String :=
  "com/alexvanyo/composelife/algorithm/HashLifeComputationKt$computeLevel4NextGeneration$2"

/-- A virtual call of a function reference's `invoke-VKZWuLQ` runs the callee's program on the receiver and argument. -/
theorem runFast_call_invokeU {r : String → Option (List JvmInstr)} {d sf f pc pc0 : Nat}
    {prog rest callee : List JvmInstr} {cls c : String} {w : UInt64}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {res : JvmVal}
    (hgen : ∀ st, Jvm.stepInvokeVirtualGeneric (mkAlgKotlinHooks r (d + 1) sf) st cls "invoke-VKZWuLQ"
      "(J)Ljava/lang/Integer;" =
      (mkAlgKotlinHooks r (d + 1) sf).stepInvokeVirtual st cls "invoke-VKZWuLQ" "(J)Ljava/lang/Integer;")
    (hcls : isAlgKotlinLiftedClass cls = true)
    (hprog : r (algKotlinTag cls "invoke-VKZWuLQ" "(J)Ljava/lang/Integer;") = some callee)
    (hcall : ∃ endSt, Jvm.runJvmRes (mkAlgKotlinHooks r d sf) sf callee
      (Jvm.initJvmState [(0, .allocRef c), (1, .i64 w)] (.i32 0) hp jh) =
        some (res, endSt) ∧ endSt.jvmHeap = jh ∧ endSt.heap = hp) :
    Jvm.runJvmResFast (mkAlgKotlinHooks r (d + 1) sf) (f + 1) prog pc
        (.invokevirtual cls "invoke-VKZWuLQ" "(J)Ljava/lang/Integer;" :: rest)
        ⟨pc0, .i64 w :: .allocRef c :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkAlgKotlinHooks r (d + 1) sf) f prog (pc + 1) rest
        ⟨pc + 1, res :: stk, locs, jh, hp⟩ := by
  obtain ⟨endSt, hrun, hj, hh⟩ := hcall
  refine Jvm.runJvmResFast_invokevirtual_step _ ?_
  rw [hgen]
  have ht : Jvm.parseMethodParamTags "(J)Ljava/lang/Integer;" = ['J'] := rfl
  have hrun' : Jvm.runJvmRes (mkAlgKotlinHooks r d sf) sf callee
      { pc := 0, stack := [],
        locals := ((0, Jvm.JvmVal.allocRef c) :: algKotlinParamSlots 1 ['J'] [.i64 w]).foldl
            (fun loc (i, v) => Jvm.setLocal loc i v) (fun _ => .i32 0),
        jvmHeap := jh, heap := hp } = some (res, endSt) := hrun
  have hlt : (stk.length + 1 + 1 < 1 + 1 || Jvm.JvmVal.isNull (.allocRef c : JvmVal)) = false := by
    simp [Jvm.JvmVal.isNull]
  have hv : "(J)Ljava/lang/Integer;".endsWith ")V" = false := by decide +kernel
  simp only [mkAlgKotlinHooks, algKotlinHooksWith, hcls, ite_true, ht, List.length_cons, List.length_nil,
    List.take_succ_cons, List.take_zero, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    hlt, Bool.false_eq_true, ite_false, List.drop_succ_cons, List.drop_zero, hprog, Option.map_some, hrun',
    algKotlinAfterCall, hj, hh, hv, Bool.false_eq_true, ite_false]

/-- An interface call `Function1.invoke` on a function-reference singleton runs its lifted bridge `invoke`. -/
theorem runFast_call_fnInvokeRef {r : String → Option (List JvmInstr)} {d sf f pc pc0 : Nat}
    {prog rest callee : List JvmInstr} {c : String} {x : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {res : JvmVal}
    (hcls : isAlgKotlinLiftedClass c = true)
    (hprog : r (algKotlinTag c "invoke" "(Ljava/lang/Object;)Ljava/lang/Object;") = some callee)
    (hcall : ∃ endSt, Jvm.runJvmRes (mkAlgKotlinHooks r d sf) sf callee
      (Jvm.initJvmState [(0, .allocRef c), (1, x)] (.i32 0) hp jh) =
        some (res, endSt) ∧ endSt.jvmHeap = jh ∧ endSt.heap = hp) :
    Jvm.runJvmResFast (mkAlgKotlinHooks r (d + 1) sf) (f + 1) prog pc
        (.invokeinterface "kotlin/jvm/functions/Function1" "invoke" "(Ljava/lang/Object;)Ljava/lang/Object;" :: rest)
        ⟨pc0, x :: .allocRef c :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkAlgKotlinHooks r (d + 1) sf) f prog (pc + 1) rest
        ⟨pc + 1, res :: stk, locs, jh, hp⟩ := by
  obtain ⟨endSt, hrun, hj, hh⟩ := hcall
  refine Jvm.runJvmResFast_invokeinterface_step _ ?_
  rw [show ∀ st, Jvm.stepInvokeInterfaceGeneric (mkAlgKotlinHooks r (d + 1) sf) st "kotlin/jvm/functions/Function1"
      "invoke" "(Ljava/lang/Object;)Ljava/lang/Object;" = (mkAlgKotlinHooks r (d + 1) sf).stepInvokeInterface st
      "kotlin/jvm/functions/Function1" "invoke" "(Ljava/lang/Object;)Ljava/lang/Object;" from fun _ => rfl]
  have ht : Jvm.parseMethodParamTags "(Ljava/lang/Object;)Ljava/lang/Object;" = ['L'] := rfl
  have hrun' : Jvm.runJvmRes (mkAlgKotlinHooks r d sf) sf callee
      { pc := 0, stack := [],
        locals := ((0, Jvm.JvmVal.allocRef c) :: algKotlinParamSlots 1 ['L'] [x]).foldl
            (fun loc (i, v) => Jvm.setLocal loc i v) (fun _ => .i32 0),
        jvmHeap := jh, heap := hp } = some (res, endSt) := hrun
  have hle : (1 + 1 ≤ stk.length + 1 + 1) = True := by simp
  have hv : "(Ljava/lang/Object;)Ljava/lang/Object;".endsWith ")V" = false := by decide +kernel
  simp only [mkAlgKotlinHooks, algKotlinHooksWith, ht, List.length_cons, List.length_nil,
    List.getElem?_cons_succ, List.getElem?_cons_zero, hcls, Bool.true_and, decide_eq_true_eq, hle, ite_true,
    List.take_succ_cons, List.take_zero, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.drop_succ_cons, List.drop_zero, hprog, Option.map_some, hrun', algKotlinAfterCall, hj, hh, hv,
    Bool.false_eq_true, ite_false]

/-- An interface call `Function1.invoke` on a caller-supplied `(ULong) -> Int` callback (a leaf hook). -/
theorem runFast_fnInvokeCallback {r : String → Option (List JvmInstr)} {d sf f pc pc0 : Nat}
    {prog rest : List JvmInstr} {g : UInt64 → UInt32} {w : UInt64}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    Jvm.runJvmResFast (mkAlgKotlinHooks r d sf) (f + 1) prog pc
        (.invokeinterface "kotlin/jvm/functions/Function1" "invoke" "(Ljava/lang/Object;)Ljava/lang/Object;" :: rest)
        ⟨pc0, .boxedULong w :: .ext (.fnU64ToI32 g) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkAlgKotlinHooks r d sf) f prog (pc + 1) rest
        ⟨pc + 1, .boxedInt (g w) :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_invokeinterface_step _ (by cases d <;> rfl)

/-- `Intrinsics.checkNotNullParameter` on a non-null value. -/
theorem runFast_checkNotNullParameter {H : Jvm.JvmHooks AlgExt AlgHeap} {f pc pc0 : Nat}
    {prog rest : List JvmInstr} {v msg : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hv : v.isNull = false) :
    Jvm.runJvmResFast H (f + 1) prog pc
        (.invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter"
          "(Ljava/lang/Object;Ljava/lang/String;)V" :: rest) ⟨pc0, msg :: v :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast H f prog (pc + 1) rest ⟨pc + 1, stk, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_invokestatic_step _ ?_
  show (if v.isNull then (.inr none : Option JvmState ⊕ Option JvmVal)
    else .inl (some ⟨pc + 1, stk, locs, jh, hp⟩)) = _
  rw [hv]
  rfl

/-! ### Bit identities -/

theorem sext_and_ffff (x : UInt32) :
    ({ toBitVec := x.toBitVec.signExtend 64 } : UInt64) &&& 65535 = x.toUInt64 &&& 65535 := by
  apply UInt64.toBitVec_inj.mp
  ext i hi
  simp only [UInt64.toBitVec_and, UInt32.toBitVec_toUInt64, BitVec.getElem_and]
  by_cases h16 : i < 16
  · simp [BitVec.getElem_signExtend, BitVec.getElem_setWidth, show i < 32 by omega]
  · have : (65535 : UInt64).toBitVec[i] = false := by
      rw [BitVec.getElem_eq_testBit_toNat]
      show Nat.testBit (2 ^ 16 - 1) i = false
      rw [Nat.testBit_two_pow_sub_one]
      simp only [decide_eq_false_iff_not]
      omega
    rw [this, Bool.and_false, Bool.and_false]

end HashLifeComputation

open HashLifeComputation

/-! ### Straight-line leaf methods -/

/-- Equivalence theorem for `packLeafNode`. -/
theorem packLeafNode_equiv (resolveProg : String → Option (List JvmInstr)) (d subFuel fuel : Nat)
    (hf : 28 ≤ fuel) (nw ne sw se : UInt32) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    ∃ endSt,
      Jvm.runJvmRes (mkAlgKotlinHooks resolveProg d subFuel) fuel HashLifeComputationKt_packLeafNode_prog
          (Jvm.initJvmState [(0, .i32 nw), (1, .i32 ne), (2, .i32 sw), (3, .i32 se)] (.i32 0) hp jh) =
        some (.i64 (packLeafNodeModel nw ne sw se), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  refine exists_of_fast rfl ⟨?pc, ?stk, ?locs, ?main⟩
  case main =>
  simp only [Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
  conv => lhs; arg 5; dsimp only [HashLifeComputationKt_packLeafNode_prog]
  hlc_step_blk
  rw [runFast_lreturn]
  refine some_pair_eq ?_
  simp only [sext_and_ffff]
  rfl

/-- Equivalence theorem for `LeafNode` (a call to `packLeafNode`). -/
theorem LeafNode_equiv (resolveProg : String → Option (List JvmInstr)) (hr : ExtendsAlgKotlinProgs resolveProg)
    (d subFuel fuel : Nat) (hd : 1 ≤ d) (hsf : 28 ≤ subFuel) (hf : 6 ≤ fuel)
    (nw ne sw se : UInt32) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    ∃ endSt,
      Jvm.runJvmRes (mkAlgKotlinHooks resolveProg d subFuel) fuel HashLifeComputationKt_LeafNode_prog
          (Jvm.initJvmState [(0, .i32 nw), (1, .i32 ne), (2, .i32 sw), (3, .i32 se)] (.i32 0) hp jh) =
        some (.i64 (packLeafNodeModel nw ne sw se), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨d1, rfl⟩ := Nat.exists_eq_add_of_le' hd
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  refine exists_of_fast rfl ⟨?pc, ?stk, ?locs, ?main⟩
  case main =>
  simp only [Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
  conv => lhs; arg 5; dsimp only [HashLifeComputationKt_LeafNode_prog]
  hlc_step_blk
  rw [runFast_call_static (n := 4) (fun _ => rfl) rfl (hr _ _ rfl) rfl (by simp) (by decide +kernel)
    (packLeafNode_equiv resolveProg d1 subFuel subFuel hsf nw ne sw se jh hp)]
  rw [runFast_lreturn]

/-- Equivalence theorem for `LeafNode.nw`. -/
theorem getNw_equiv (resolveProg : String → Option (List JvmInstr)) (d subFuel fuel : Nat)
    (hf : 8 ≤ fuel) (w : UInt64) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    ∃ endSt,
      Jvm.runJvmRes (mkAlgKotlinHooks resolveProg d subFuel) fuel HashLifeComputationKt_getNw_prog
          (Jvm.initJvmState [(0, .i64 w)] (.i32 0) hp jh) =
        some (.i32 (leafNwModel w), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  refine exists_of_fast rfl ⟨?pc, ?stk, ?locs, ?main⟩
  case main =>
  simp only [Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
  conv => lhs; arg 5; dsimp only [HashLifeComputationKt_getNw_prog]
  hlc_step_blk
  rw [runFast_ireturn]
  rfl

/-- Equivalence theorem for `LeafNode.ne`. -/
theorem getNe_equiv (resolveProg : String → Option (List JvmInstr)) (d subFuel fuel : Nat)
    (hf : 11 ≤ fuel) (w : UInt64) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    ∃ endSt,
      Jvm.runJvmRes (mkAlgKotlinHooks resolveProg d subFuel) fuel HashLifeComputationKt_getNe_prog
          (Jvm.initJvmState [(0, .i64 w)] (.i32 0) hp jh) =
        some (.i32 (leafNeModel w), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  refine exists_of_fast rfl ⟨?pc, ?stk, ?locs, ?main⟩
  case main =>
  simp only [Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
  conv => lhs; arg 5; dsimp only [HashLifeComputationKt_getNe_prog]
  hlc_step_blk
  rw [runFast_ireturn]
  rfl

/-- Equivalence theorem for `LeafNode.sw`. -/
theorem getSw_equiv (resolveProg : String → Option (List JvmInstr)) (d subFuel fuel : Nat)
    (hf : 11 ≤ fuel) (w : UInt64) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    ∃ endSt,
      Jvm.runJvmRes (mkAlgKotlinHooks resolveProg d subFuel) fuel HashLifeComputationKt_getSw_prog
          (Jvm.initJvmState [(0, .i64 w)] (.i32 0) hp jh) =
        some (.i32 (leafSwModel w), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  refine exists_of_fast rfl ⟨?pc, ?stk, ?locs, ?main⟩
  case main =>
  simp only [Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
  conv => lhs; arg 5; dsimp only [HashLifeComputationKt_getSw_prog]
  hlc_step_blk
  rw [runFast_ireturn]
  rfl

/-- Equivalence theorem for `LeafNode.se`. -/
theorem getSe_equiv (resolveProg : String → Option (List JvmInstr)) (d subFuel fuel : Nat)
    (hf : 8 ≤ fuel) (w : UInt64) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    ∃ endSt,
      Jvm.runJvmRes (mkAlgKotlinHooks resolveProg d subFuel) fuel HashLifeComputationKt_getSe_prog
          (Jvm.initJvmState [(0, .i64 w)] (.i32 0) hp jh) =
        some (.i32 (leafSeModel w), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  refine exists_of_fast rfl ⟨?pc, ?stk, ?locs, ?main⟩
  case main =>
  simp only [Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
  conv => lhs; arg 5; dsimp only [HashLifeComputationKt_getSe_prog]
  hlc_step_blk
  rw [runFast_ireturn]
  rfl

/-- Equivalence theorem for `centeredSubnodeLevel3`. -/
theorem centeredSubnodeLevel3_equiv (resolveProg : String → Option (List JvmInstr)) (d subFuel fuel : Nat)
    (hf : 68 ≤ fuel) (w : UInt64) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    ∃ endSt,
      Jvm.runJvmRes (mkAlgKotlinHooks resolveProg d subFuel) fuel HashLifeComputationKt_centeredSubnodeLevel3_prog
          (Jvm.initJvmState [(0, .i64 w)] (.i32 0) hp jh) =
        some (.i32 (centeredSubnodeLevel3Model w), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  refine exists_of_fast rfl ⟨?pc, ?stk, ?locs, ?main⟩
  case main =>
  simp only [Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
  conv => lhs; arg 5; dsimp only [HashLifeComputationKt_centeredSubnodeLevel3_prog]
  hlc_step_blk
  rw [runFast_ireturn]
  rfl

/-- Equivalence theorem for `centeredHorizontalSubnodeLevel3`. -/
theorem centeredHorizontalSubnodeLevel3_equiv (resolveProg : String → Option (List JvmInstr)) (d subFuel fuel : Nat)
    (hf : 68 ≤ fuel) (w e : UInt64) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    ∃ endSt,
      Jvm.runJvmRes (mkAlgKotlinHooks resolveProg d subFuel) fuel HashLifeComputationKt_centeredHorizontalSubnodeLevel3_prog
          (Jvm.initJvmState [(0, .i64 w), (2, .i64 e)] (.i32 0) hp jh) =
        some (.i32 (centeredHorizontalSubnodeLevel3Model w e), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  refine exists_of_fast rfl ⟨?pc, ?stk, ?locs, ?main⟩
  case main =>
  simp only [Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
  conv => lhs; arg 5; dsimp only [HashLifeComputationKt_centeredHorizontalSubnodeLevel3_prog]
  hlc_step_blk
  rw [runFast_ireturn]
  rfl

/-- Equivalence theorem for `centeredVerticalSubnodeLevel3`. -/
theorem centeredVerticalSubnodeLevel3_equiv (resolveProg : String → Option (List JvmInstr)) (d subFuel fuel : Nat)
    (hf : 68 ≤ fuel) (n s : UInt64) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    ∃ endSt,
      Jvm.runJvmRes (mkAlgKotlinHooks resolveProg d subFuel) fuel HashLifeComputationKt_centeredVerticalSubnodeLevel3_prog
          (Jvm.initJvmState [(0, .i64 n), (2, .i64 s)] (.i32 0) hp jh) =
        some (.i32 (centeredVerticalSubnodeLevel3Model n s), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  refine exists_of_fast rfl ⟨?pc, ?stk, ?locs, ?main⟩
  case main =>
  simp only [Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
  conv => lhs; arg 5; dsimp only [HashLifeComputationKt_centeredVerticalSubnodeLevel3_prog]
  hlc_step_blk
  rw [runFast_ireturn]
  rfl

/-- Equivalence theorem for `centeredSubSubnodeLevel4(nw, ne, sw, se)`. -/
theorem centeredSubSubnodeLevel4_equiv (resolveProg : String → Option (List JvmInstr)) (d subFuel fuel : Nat)
    (hf : 68 ≤ fuel) (nw ne sw se : UInt64) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    ∃ endSt,
      Jvm.runJvmRes (mkAlgKotlinHooks resolveProg d subFuel) fuel HashLifeComputationKt_centeredSubSubnodeLevel4_prog
          (Jvm.initJvmState [(0, .i64 nw), (2, .i64 ne), (4, .i64 sw), (6, .i64 se)] (.i32 0) hp jh) =
        some (.i32 (centeredSubSubnodeLevel4Model nw ne sw se), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  refine exists_of_fast rfl ⟨?pc, ?stk, ?locs, ?main⟩
  case main =>
  simp only [Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
  conv => lhs; arg 5; dsimp only [HashLifeComputationKt_centeredSubSubnodeLevel4_prog]
  hlc_step_blk
  rw [runFast_ireturn]
  rfl

/-- Equivalence theorem for `ULong.computeNextGeneration` (the Lean-compiled leaf kernel). -/
theorem computeNextGeneration_equiv (resolveProg : String → Option (List JvmInstr)) (d subFuel fuel : Nat)
    (hf : 3 ≤ fuel) (w : UInt64) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    ∃ endSt,
      Jvm.runJvmRes (mkAlgKotlinHooks resolveProg d subFuel) fuel HashLifeComputationKt_computeNextGeneration_prog
          (Jvm.initJvmState [(0, .i64 w)] (.i32 0) hp jh) =
        some (.i32 (Algorithm.computeLeafNextGen8x8BranchUInt w), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  refine exists_of_fast rfl ⟨?pc, ?stk, ?locs, ?main⟩
  case main =>
  simp only [Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
  conv => lhs; arg 5; dsimp only [HashLifeComputationKt_computeNextGeneration_prog]
  hlc_step_blk
  rw [runFast_exportLeafKernel, runFast_ireturn]

/-- Equivalence theorem for `Long.computeNextGeneration` (forwards to `ULong.computeNextGeneration`). -/
theorem computeNextGeneration_1_equiv (resolveProg : String → Option (List JvmInstr))
    (hr : ExtendsAlgKotlinProgs resolveProg) (d subFuel fuel : Nat) (hd : 1 ≤ d) (hsf : 3 ≤ subFuel)
    (hf : 4 ≤ fuel) (w : UInt64) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    ∃ endSt,
      Jvm.runJvmRes (mkAlgKotlinHooks resolveProg d subFuel) fuel HashLifeComputationKt_computeNextGeneration_1_prog
          (Jvm.initJvmState [(0, .i64 w)] (.i32 0) hp jh) =
        some (.i32 (Algorithm.computeLeafNextGen8x8BranchUInt w), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨d1, rfl⟩ := Nat.exists_eq_add_of_le' hd
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  refine exists_of_fast rfl ⟨?pc, ?stk, ?locs, ?main⟩
  case main =>
  simp only [Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
  conv => lhs; arg 5; dsimp only [HashLifeComputationKt_computeNextGeneration_1_prog]
  hlc_step_blk
  rw [runFast_call_static (n := 1) (fun _ => rfl) rfl (hr _ _ rfl) rfl (by simp) (by decide +kernel)
    (computeNextGeneration_equiv resolveProg d1 subFuel subFuel hsf w jh hp)]
  rw [runFast_ireturn]

/-- Equivalence theorem for `centeredSubSubnodeLevel4(node: MacroCell.Level4Node)`. -/
theorem centeredSubSubnodeLevel4_1_equiv (resolveProg : String → Option (List JvmInstr))
    (hr : ExtendsAlgKotlinProgs resolveProg) (d subFuel fuel : Nat) (hd : 1 ≤ d) (hsf : 68 ≤ subFuel)
    (hf : 13 ≤ fuel) (h : UInt32) (nw ne sw se : UInt64) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    ∃ endSt,
      Jvm.runJvmRes (mkAlgKotlinHooks resolveProg d subFuel) fuel HashLifeComputationKt_centeredSubSubnodeLevel4_1_prog
          (Jvm.initJvmState [(0, .ext (.mc (.level4Node h nw ne sw se)))] (.i32 0) hp jh) =
        some (.i32 (centeredSubSubnodeLevel4Model nw ne sw se), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨d1, rfl⟩ := Nat.exists_eq_add_of_le' hd
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  refine exists_of_fast rfl ⟨?pc, ?stk, ?locs, ?main⟩
  case main =>
  simp only [Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
  conv => lhs; arg 5; dsimp only [HashLifeComputationKt_centeredSubSubnodeLevel4_1_prog]
  hlc_step_blk
  rw [Jvm.runJvmResFast_invokestatic_step _ (by rfl)]
  hlc_step_blk
  rw [runFast_l4GetNw]
  hlc_step_blk
  rw [runFast_l4GetNe]
  hlc_step_blk
  rw [runFast_l4GetSw]
  hlc_step_blk
  rw [runFast_l4GetSe]
  rw [runFast_call_static (n := 4) (fun _ => rfl) rfl (hr _ _ rfl) rfl (by simp) (by decide +kernel)
    (centeredSubSubnodeLevel4_equiv resolveProg d1 subFuel subFuel hsf nw ne sw se jh hp)]
  rw [runFast_ireturn]

/-! ### The default leaf kernel `ULong::computeNextGenerationPureKotlin` and its function references -/

namespace HashLifeComputation

/-- `Long.computeNextGenerationPureKotlin` under `mkAlgKotlinHooks`, transferred from its `algHooks` proof
(`computeNextGenerationPureKotlin_res_equiv`): both hooks step each of its instructions identically. -/
theorem pureKotlin_run_kotlin (r : String → Option (List JvmInstr)) (d sf : Nat) (hsf : 250 ≤ sf) (w : UInt64)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (hqi : HasQuadInfoLut jh) (hng : HasNextGen4x4Lut jh) :
    ∃ endSt, Jvm.runJvmRes (mkAlgKotlinHooks r d sf) sf BitComputationKt_computeNextGenerationPureKotlin_prog
        (Jvm.initJvmState [(0, .i64 w)] (.i32 0) hp jh) =
      some (.i32 (computeNextGenerationPureKotlinModel w), endSt) ∧ endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨st', hrun, hj, hh⟩ := computeNextGenerationPureKotlin_res_equiv w jh hp hqi hng
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hsf
  refine ⟨st', runJvmRes_transfer algHooks _ _ (by cases d <;> rfl) (by cases d <;> rfl) ?_ 250 m _ _ hrun, hj, hh⟩
  intro i hi st
  exact stepInstr_alg_eq_kotlin r d _ i (List.all_eq_true.mp pureKotlin_prog_agree i hi) st

/-- `ULong.computeNextGenerationPureKotlin` (`-VKZWuLQ`) under `mkAlgKotlinHooks`: it calls the lifted
`computeNextGenerationPureKotlin(J)I`. -/
theorem pureKotlin_1_run_kotlin (r : String → Option (List JvmInstr)) (hr : ExtendsAlgKotlinProgs r)
    (d sf fuel : Nat) (hd : 1 ≤ d) (hsf : 250 ≤ sf) (hf : 3 ≤ fuel) (w : UInt64)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (hqi : HasQuadInfoLut jh) (hng : HasNextGen4x4Lut jh) :
    ∃ endSt, Jvm.runJvmRes (mkAlgKotlinHooks r d sf) fuel BitComputationKt_computeNextGenerationPureKotlin_1_prog
        (Jvm.initJvmState [(0, .i64 w)] (.i32 0) hp jh) =
      some (.i32 (computeNextGenerationPureKotlinModel w), endSt) ∧ endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨d1, rfl⟩ := Nat.exists_eq_add_of_le' hd
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  refine exists_of_fast rfl ⟨?pc, ?stk, ?locs, ?main⟩
  case main =>
  simp only [Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
  conv => lhs; arg 5; dsimp only [BitComputationKt_computeNextGenerationPureKotlin_1_prog]
  hlc_step_blk
  rw [runFast_call_static (n := 1) (fun _ => rfl) rfl (hr _ _ rfl) rfl (by simp) (by decide +kernel)
    (pureKotlin_run_kotlin r d1 sf hsf w jh hp hqi hng)]
  rw [runFast_ireturn]

end HashLifeComputation

open HashLifeComputation

/-- Equivalence theorem for `HashLifeComputationKt$computeLevel4NextGeneration$1.invoke-VKZWuLQ` (the function
reference `ULong::computeNextGenerationPureKotlin`, boxing its result). -/
theorem invoke_equiv (resolveProg : String → Option (List JvmInstr)) (hr : ExtendsAlgKotlinProgs resolveProg)
    (d subFuel fuel : Nat) (hd : 2 ≤ d) (hsf : 250 ≤ subFuel) (hf : 4 ≤ fuel) (recv : JvmVal) (w : UInt64)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (hqi : HasQuadInfoLut jh) (hng : HasNextGen4x4Lut jh) :
    ∃ endSt,
      Jvm.runJvmRes (mkAlgKotlinHooks resolveProg d subFuel) fuel HashLifeComputationKt_computeLevel4NextGeneration_1_invoke_prog
          (Jvm.initJvmState [(0, recv), (1, .i64 w)] (.i32 0) hp jh) =
        some (.boxedInt (computeNextGenerationPureKotlinModel w), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨d1, rfl⟩ := Nat.exists_eq_add_of_le' (show 1 ≤ d by omega)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  refine exists_of_fast rfl ⟨?pc, ?stk, ?locs, ?main⟩
  case main =>
  simp only [Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
  conv => lhs; arg 5; dsimp only [HashLifeComputationKt_computeLevel4NextGeneration_1_invoke_prog]
  hlc_step_blk
  rw [runFast_call_static (n := 1) (fun _ => rfl) rfl (hr _ _ rfl) rfl (by simp) (by decide +kernel)
    (pureKotlin_1_run_kotlin resolveProg hr d1 subFuel subFuel (by omega) hsf (by omega) w jh hp hqi hng)]
  rw [Jvm.runJvmResFast_invokestatic_step _ (by rfl)]
  rw [runFast_areturn]

/-- Equivalence theorem for `HashLifeComputationKt$computeLevel4NextGeneration$2.invoke-VKZWuLQ` (the function
reference `ULong::computeNextGenerationPureKotlin`, boxing its result). -/
theorem invoke_2_equiv (resolveProg : String → Option (List JvmInstr)) (hr : ExtendsAlgKotlinProgs resolveProg)
    (d subFuel fuel : Nat) (hd : 2 ≤ d) (hsf : 250 ≤ subFuel) (hf : 4 ≤ fuel) (recv : JvmVal) (w : UInt64)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (hqi : HasQuadInfoLut jh) (hng : HasNextGen4x4Lut jh) :
    ∃ endSt,
      Jvm.runJvmRes (mkAlgKotlinHooks resolveProg d subFuel) fuel HashLifeComputationKt_computeLevel4NextGeneration_2_invoke_prog
          (Jvm.initJvmState [(0, recv), (1, .i64 w)] (.i32 0) hp jh) =
        some (.boxedInt (computeNextGenerationPureKotlinModel w), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨d1, rfl⟩ := Nat.exists_eq_add_of_le' (show 1 ≤ d by omega)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  refine exists_of_fast rfl ⟨?pc, ?stk, ?locs, ?main⟩
  case main =>
  simp only [Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
  conv => lhs; arg 5; dsimp only [HashLifeComputationKt_computeLevel4NextGeneration_2_invoke_prog]
  hlc_step_blk
  rw [runFast_call_static (n := 1) (fun _ => rfl) rfl (hr _ _ rfl) rfl (by simp) (by decide +kernel)
    (pureKotlin_1_run_kotlin resolveProg hr d1 subFuel subFuel (by omega) hsf (by omega) w jh hp hqi hng)]
  rw [Jvm.runJvmResFast_invokestatic_step _ (by rfl)]
  rw [runFast_areturn]

/-- Equivalence theorem for the bridge `HashLifeComputationKt$computeLevel4NextGeneration$1.invoke(Object)`: unboxes
the `ULong` and calls `invoke-VKZWuLQ` on the singleton. -/
theorem invoke_1_equiv (resolveProg : String → Option (List JvmInstr)) (hr : ExtendsAlgKotlinProgs resolveProg)
    (d subFuel fuel : Nat) (hd : 3 ≤ d) (hsf : 250 ≤ subFuel) (hf : 6 ≤ fuel) (w : UInt64)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (hqi : HasQuadInfoLut jh) (hng : HasNextGen4x4Lut jh) :
    ∃ endSt,
      Jvm.runJvmRes (mkAlgKotlinHooks resolveProg d subFuel) fuel HashLifeComputationKt_computeLevel4NextGeneration_1_invoke_1_prog
          (Jvm.initJvmState [(0, .allocRef lambdaClass1), (1, .boxedULong w)] (.i32 0) hp jh) =
        some (.boxedInt (computeNextGenerationPureKotlinModel w), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨d1, rfl⟩ := Nat.exists_eq_add_of_le' (show 1 ≤ d by omega)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  refine exists_of_fast rfl ⟨?pc, ?stk, ?locs, ?main⟩
  case main =>
  simp only [Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
  conv => lhs; arg 5; dsimp only [HashLifeComputationKt_computeLevel4NextGeneration_1_invoke_1_prog]
  hlc_step_blk
  rw [Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) (by rfl) rfl]
  rw [Jvm.runJvmResFast_invokevirtual_step _ (by rfl)]
  rw [runFast_call_invokeU (fun _ => rfl) rfl (hr _ _ rfl)
    (invoke_equiv resolveProg hr d1 subFuel subFuel (by omega) hsf (by omega) _ w jh hp hqi hng)]
  rw [runFast_areturn]

/-- Equivalence theorem for the bridge `HashLifeComputationKt$computeLevel4NextGeneration$2.invoke(Object)`: unboxes
the `ULong` and calls `invoke-VKZWuLQ` on the singleton. -/
theorem invoke_3_equiv (resolveProg : String → Option (List JvmInstr)) (hr : ExtendsAlgKotlinProgs resolveProg)
    (d subFuel fuel : Nat) (hd : 3 ≤ d) (hsf : 250 ≤ subFuel) (hf : 6 ≤ fuel) (w : UInt64)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (hqi : HasQuadInfoLut jh) (hng : HasNextGen4x4Lut jh) :
    ∃ endSt,
      Jvm.runJvmRes (mkAlgKotlinHooks resolveProg d subFuel) fuel HashLifeComputationKt_computeLevel4NextGeneration_2_invoke_1_prog
          (Jvm.initJvmState [(0, .allocRef lambdaClass2), (1, .boxedULong w)] (.i32 0) hp jh) =
        some (.boxedInt (computeNextGenerationPureKotlinModel w), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨d1, rfl⟩ := Nat.exists_eq_add_of_le' (show 1 ≤ d by omega)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  refine exists_of_fast rfl ⟨?pc, ?stk, ?locs, ?main⟩
  case main =>
  simp only [Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
  conv => lhs; arg 5; dsimp only [HashLifeComputationKt_computeLevel4NextGeneration_2_invoke_1_prog]
  hlc_step_blk
  rw [Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) (by rfl) rfl]
  rw [Jvm.runJvmResFast_invokevirtual_step _ (by rfl)]
  rw [runFast_call_invokeU (fun _ => rfl) rfl (hr _ _ rfl)
    (invoke_2_equiv resolveProg hr d1 subFuel subFuel (by omega) hsf (by omega) _ w jh hp hqi hng)]
  rw [runFast_areturn]

namespace HashLifeComputation

/--
`computeLevel4NextGeneration-qFGr5tM` for a leaf-kernel argument `fn` on which `Function1.invoke` computes `g`
(`hfn`, discharged below for a caller-supplied callback and for the two function-reference singletons).
-/
theorem computeLevel4_run_of (r : String → Option (List JvmInstr)) (hr : ExtendsAlgKotlinProgs r)
    (d1 sf k : Nat) (hsf : 68 ≤ sf) (nw ne sw se : UInt64) (fn : JvmVal) (g : UInt64 → UInt32)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (hnn : fn.isNull = false)
    (hfn : ∀ (f pc pc0 : Nat) (prog rest : List JvmInstr) (w : UInt64) (stk : List JvmVal) (locs : Nat → JvmVal),
      Jvm.runJvmResFast (mkAlgKotlinHooks r (d1 + 1) sf) (f + 1) prog pc
          (.invokeinterface "kotlin/jvm/functions/Function1" "invoke" "(Ljava/lang/Object;)Ljava/lang/Object;" ::
            rest) ⟨pc0, .boxedULong w :: fn :: stk, locs, jh, hp⟩ =
        Jvm.runJvmResFast (mkAlgKotlinHooks r (d1 + 1) sf) f prog (pc + 1) rest
          ⟨pc + 1, .boxedInt (g w) :: stk, locs, jh, hp⟩) :
    ∃ endSt, Jvm.runJvmRes (mkAlgKotlinHooks r (d1 + 1) sf) (k + 95) HashLifeComputationKt_computeLevel4NextGeneration_prog
        (Jvm.initJvmState [(0, .i64 nw), (2, .i64 ne), (4, .i64 sw), (6, .i64 se), (8, fn)] (.i32 0) hp jh) =
      some (.i64 (computeLevel4NextGenerationModel nw ne sw se g), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  refine exists_of_fast rfl ⟨?pc, ?stk, ?locs, ?main⟩
  case main =>
  simp only [Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
  conv => lhs; arg 5; dsimp only [HashLifeComputationKt_computeLevel4NextGeneration_prog]
  hlc_step_blk
  rw [runFast_checkNotNullParameter hnn]
  hlc_step_blk
  rw [runFast_call_static (n := 1) (fun _ => rfl) rfl (hr _ _ rfl) rfl (by simp) (by decide +kernel)
    (centeredSubnodeLevel3_equiv r d1 sf sf hsf nw jh hp)]
  hlc_step_blk
  rw [runFast_call_static (n := 2) (fun _ => rfl) rfl (hr _ _ rfl) rfl (by simp) (by decide +kernel)
    (centeredHorizontalSubnodeLevel3_equiv r d1 sf sf hsf nw ne jh hp)]
  hlc_step_blk
  rw [runFast_call_static (n := 1) (fun _ => rfl) rfl (hr _ _ rfl) rfl (by simp) (by decide +kernel)
    (centeredSubnodeLevel3_equiv r d1 sf sf hsf ne jh hp)]
  hlc_step_blk
  rw [runFast_call_static (n := 2) (fun _ => rfl) rfl (hr _ _ rfl) rfl (by simp) (by decide +kernel)
    (centeredVerticalSubnodeLevel3_equiv r d1 sf sf hsf nw sw jh hp)]
  hlc_step_blk
  rw [runFast_call_static (n := 4) (fun _ => rfl) rfl (hr _ _ rfl) rfl (by simp) (by decide +kernel)
    (centeredSubSubnodeLevel4_equiv r d1 sf sf hsf nw ne sw se jh hp)]
  hlc_step_blk
  rw [runFast_call_static (n := 2) (fun _ => rfl) rfl (hr _ _ rfl) rfl (by simp) (by decide +kernel)
    (centeredVerticalSubnodeLevel3_equiv r d1 sf sf hsf ne se jh hp)]
  hlc_step_blk
  rw [runFast_call_static (n := 1) (fun _ => rfl) rfl (hr _ _ rfl) rfl (by simp) (by decide +kernel)
    (centeredSubnodeLevel3_equiv r d1 sf sf hsf sw jh hp)]
  hlc_step_blk
  rw [runFast_call_static (n := 2) (fun _ => rfl) rfl (hr _ _ rfl) rfl (by simp) (by decide +kernel)
    (centeredHorizontalSubnodeLevel3_equiv r d1 sf sf hsf sw se jh hp)]
  hlc_step_blk
  rw [runFast_call_static (n := 1) (fun _ => rfl) rfl (hr _ _ rfl) rfl (by simp) (by decide +kernel)
    (centeredSubnodeLevel3_equiv r d1 sf sf hsf se jh hp)]
  hlc_step_blk
  rw [runFast_call_static (n := 4) (fun _ => rfl) rfl (hr _ _ rfl) rfl (by simp) (by decide +kernel)
    (packLeafNode_equiv r d1 sf sf (by omega)
      (centeredSubnodeLevel3Model nw)
      (centeredHorizontalSubnodeLevel3Model nw ne)
      (centeredVerticalSubnodeLevel3Model nw sw)
      (centeredSubSubnodeLevel4Model nw ne sw se) jh hp)]
  hlc_step_blk
  rw [runFast_call_static (n := 4) (fun _ => rfl) rfl (hr _ _ rfl) rfl (by simp) (by decide +kernel)
    (packLeafNode_equiv r d1 sf sf (by omega)
      (centeredHorizontalSubnodeLevel3Model nw ne)
      (centeredSubnodeLevel3Model ne)
      (centeredSubSubnodeLevel4Model nw ne sw se)
      (centeredVerticalSubnodeLevel3Model ne se) jh hp)]
  hlc_step_blk
  rw [runFast_call_static (n := 4) (fun _ => rfl) rfl (hr _ _ rfl) rfl (by simp) (by decide +kernel)
    (packLeafNode_equiv r d1 sf sf (by omega)
      (centeredVerticalSubnodeLevel3Model nw sw)
      (centeredSubSubnodeLevel4Model nw ne sw se)
      (centeredSubnodeLevel3Model sw)
      (centeredHorizontalSubnodeLevel3Model sw se) jh hp)]
  hlc_step_blk
  rw [runFast_call_static (n := 4) (fun _ => rfl) rfl (hr _ _ rfl) rfl (by simp) (by decide +kernel)
    (packLeafNode_equiv r d1 sf sf (by omega)
      (centeredSubSubnodeLevel4Model nw ne sw se)
      (centeredVerticalSubnodeLevel3Model ne se)
      (centeredHorizontalSubnodeLevel3Model sw se)
      (centeredSubnodeLevel3Model se) jh hp)]
  hlc_step_blk
  rw [Jvm.runJvmResFast_invokestatic_step _ (by rfl), hfn]
  rw [Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) (by rfl) rfl]
  rw [Jvm.runJvmResFast_invokevirtual_step _ (by rfl)]
  hlc_step_blk
  rw [Jvm.runJvmResFast_invokestatic_step _ (by rfl), hfn]
  rw [Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) (by rfl) rfl]
  rw [Jvm.runJvmResFast_invokevirtual_step _ (by rfl)]
  hlc_step_blk
  rw [Jvm.runJvmResFast_invokestatic_step _ (by rfl), hfn]
  rw [Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) (by rfl) rfl]
  rw [Jvm.runJvmResFast_invokevirtual_step _ (by rfl)]
  hlc_step_blk
  rw [Jvm.runJvmResFast_invokestatic_step _ (by rfl), hfn]
  rw [Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) (by rfl) rfl]
  rw [Jvm.runJvmResFast_invokevirtual_step _ (by rfl)]
  hlc_step_blk
  rw [runFast_call_static (n := 4) (fun _ => rfl) rfl (hr _ _ rfl) rfl (by simp) (by decide +kernel)
    (packLeafNode_equiv r d1 sf sf (by omega)
      (g (packLeafNodeModel
        (centeredSubnodeLevel3Model nw)
        (centeredHorizontalSubnodeLevel3Model nw ne)
        (centeredVerticalSubnodeLevel3Model nw sw)
        (centeredSubSubnodeLevel4Model nw ne sw se)))
      (g (packLeafNodeModel
        (centeredHorizontalSubnodeLevel3Model nw ne)
        (centeredSubnodeLevel3Model ne)
        (centeredSubSubnodeLevel4Model nw ne sw se)
        (centeredVerticalSubnodeLevel3Model ne se)))
      (g (packLeafNodeModel
        (centeredVerticalSubnodeLevel3Model nw sw)
        (centeredSubSubnodeLevel4Model nw ne sw se)
        (centeredSubnodeLevel3Model sw)
        (centeredHorizontalSubnodeLevel3Model sw se)))
      (g (packLeafNodeModel
        (centeredSubSubnodeLevel4Model nw ne sw se)
        (centeredVerticalSubnodeLevel3Model ne se)
        (centeredHorizontalSubnodeLevel3Model sw se)
        (centeredSubnodeLevel3Model se))) jh hp)]
  rw [runFast_lreturn]
  rfl

end HashLifeComputation

namespace HashLifeComputation

/-- `Function1.invoke` on one of the two function-reference singletons runs its lifted bridge and returns the boxed
`computeNextGenerationPureKotlinModel` result. -/
theorem runFast_fnInvokeLambda (r : String → Option (List JvmInstr)) (hr : ExtendsAlgKotlinProgs r)
    (d1 sf : Nat) (hd : 3 ≤ d1) (hsf : 250 ≤ sf) (c : String) (hc : c = lambdaClass1 ∨ c = lambdaClass2)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (hqi : HasQuadInfoLut jh) (hng : HasNextGen4x4Lut jh)
    (f pc pc0 : Nat) (prog rest : List JvmInstr) (w : UInt64) (stk : List JvmVal) (locs : Nat → JvmVal) :
    Jvm.runJvmResFast (mkAlgKotlinHooks r (d1 + 1) sf) (f + 1) prog pc
        (.invokeinterface "kotlin/jvm/functions/Function1" "invoke" "(Ljava/lang/Object;)Ljava/lang/Object;" :: rest)
        ⟨pc0, .boxedULong w :: .allocRef c :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkAlgKotlinHooks r (d1 + 1) sf) f prog (pc + 1) rest
        ⟨pc + 1, .boxedInt (computeNextGenerationPureKotlinModel w) :: stk, locs, jh, hp⟩ := by
  rcases hc with rfl | rfl
  · exact runFast_call_fnInvokeRef rfl (hr _ _ rfl)
      (invoke_1_equiv r hr d1 sf sf hd hsf (by omega) w jh hp hqi hng)
  · exact runFast_call_fnInvokeRef rfl (hr _ _ rfl)
      (invoke_3_equiv r hr d1 sf sf hd hsf (by omega) w jh hp hqi hng)

/-- A function-reference class's `INSTANCE` reads as its stateless singleton when the static is unset (the hooks
resolve it) or holds that singleton. -/
theorem runFast_getInstance {r : String → Option (List JvmInstr)} {d sf f pc pc0 : Nat}
    {prog rest : List JvmInstr} {c desc : String}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hc : c = lambdaClass1 ∨ c = lambdaClass2)
    (hinst : jh.getStatic? c "INSTANCE" = none ∨ jh.getStatic? c "INSTANCE" = some (.allocRef c)) :
    Jvm.runJvmResFast (mkAlgKotlinHooks r d sf) (f + 1) prog pc (.getstatic c "INSTANCE" desc :: rest)
        ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkAlgKotlinHooks r d sf) f prog (pc + 1) rest ⟨pc + 1, .allocRef c :: stk, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  dsimp only [Jvm.stepInstr]
  rcases hinst with h | h <;> rw [h]
  rcases hc with rfl | rfl <;> (cases d <;> rfl)

theorem runFast_vreturn {H : Jvm.JvmHooks AlgExt AlgHeap} {f pc pc0 : Nat} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    Jvm.runJvmResFast H (f + 1) prog pc (.vreturn :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      some (.unit, ⟨pc, stk, locs, jh, hp⟩) := by
  rw [Jvm.runJvmResFast_step_nonbranch _ f prog pc .vreturn rest _ rfl (by simp)]
  rfl

end HashLifeComputation

/-! ### `computeLevel4NextGeneration` and its overloads and `$default` bridges -/

/-- Equivalence theorem for `computeLevel4NextGeneration(nw, ne, sw, se, computeLeafNextGen)` with a caller-supplied
leaf kernel `g`. -/
theorem computeLevel4NextGeneration_equiv (resolveProg : String → Option (List JvmInstr))
    (hr : ExtendsAlgKotlinProgs resolveProg) (d subFuel fuel : Nat) (hd : 1 ≤ d) (hsf : 68 ≤ subFuel)
    (hf : 95 ≤ fuel) (nw ne sw se : UInt64) (g : UInt64 → UInt32) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    ∃ endSt,
      Jvm.runJvmRes (mkAlgKotlinHooks resolveProg d subFuel) fuel HashLifeComputationKt_computeLevel4NextGeneration_prog
          (Jvm.initJvmState [(0, .i64 nw), (2, .i64 ne), (4, .i64 sw), (6, .i64 se), (8, .ext (.fnU64ToI32 g))]
            (.i32 0) hp jh) =
        some (.i64 (computeLevel4NextGenerationModel nw ne sw se g), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨d1, rfl⟩ := Nat.exists_eq_add_of_le' hd
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  exact computeLevel4_run_of resolveProg hr d1 subFuel k hsf nw ne sw se _ g jh hp rfl
    (fun _ _ _ _ _ _ _ _ => runFast_fnInvokeCallback)

/-- Equivalence theorem for `computeLevel4NextGeneration(nw, ne, sw, se, computeLeafNextGen)` with the default leaf
kernel `ULong::computeNextGenerationPureKotlin` (either function-reference singleton). -/
theorem computeLevel4NextGeneration_lambda_equiv (resolveProg : String → Option (List JvmInstr))
    (hr : ExtendsAlgKotlinProgs resolveProg) (d subFuel fuel : Nat) (hd : 4 ≤ d) (hsf : 250 ≤ subFuel)
    (hf : 95 ≤ fuel) (c : String) (hc : c = lambdaClass1 ∨ c = lambdaClass2) (nw ne sw se : UInt64)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (hqi : HasQuadInfoLut jh) (hng : HasNextGen4x4Lut jh) :
    ∃ endSt,
      Jvm.runJvmRes (mkAlgKotlinHooks resolveProg d subFuel) fuel HashLifeComputationKt_computeLevel4NextGeneration_prog
          (Jvm.initJvmState [(0, .i64 nw), (2, .i64 ne), (4, .i64 sw), (6, .i64 se), (8, .allocRef c)]
            (.i32 0) hp jh) =
        some (.i64 (computeLevel4NextGenerationModel nw ne sw se computeNextGenerationPureKotlinModel), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨d1, rfl⟩ := Nat.exists_eq_add_of_le' (show 1 ≤ d by omega)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  exact computeLevel4_run_of resolveProg hr d1 subFuel k (by omega) nw ne sw se _ _ jh hp rfl
    (runFast_fnInvokeLambda resolveProg hr d1 subFuel (by omega) hsf c hc jh hp hqi hng)

/-- Equivalence theorem for `computeLevel4NextGeneration-qFGr5tM$default` when the caller passes its own leaf kernel
`g` (default-mask bit 16 clear). -/
theorem computeLevel4NextGeneration_qFGr5tM_default_equiv (resolveProg : String → Option (List JvmInstr))
    (hr : ExtendsAlgKotlinProgs resolveProg) (d subFuel fuel : Nat) (hd : 2 ≤ d) (hsf : 95 ≤ subFuel)
    (hf : 11 ≤ fuel) (nw ne sw se : UInt64) (g : UInt64 → UInt32) (mask : UInt32) (hmask : mask &&& 16 = 0)
    (marker : JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    ∃ endSt,
      Jvm.runJvmRes (mkAlgKotlinHooks resolveProg d subFuel) fuel HashLifeComputationKt_computeLevel4NextGeneration_qFGr5tM_default_prog
          (Jvm.initJvmState [(0, .i64 nw), (2, .i64 ne), (4, .i64 sw), (6, .i64 se), (8, .ext (.fnU64ToI32 g)),
            (9, .i32 mask), (10, marker)] (.i32 0) hp jh) =
        some (.i64 (computeLevel4NextGenerationModel nw ne sw se g), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨d1, rfl⟩ := Nat.exists_eq_add_of_le' (show 1 ≤ d by omega)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  refine exists_of_fast rfl ⟨?pc, ?stk, ?locs, ?main⟩
  case main =>
  simp only [Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
  conv => lhs; arg 5; dsimp only [HashLifeComputationKt_computeLevel4NextGeneration_qFGr5tM_default_prog]
  hlc_step_blk
  rw [Jvm.runJvmResFast_at_branch_cons _ (hbr := rfl), Jvm.evalResBranchInstrCons_ifeq, hmask]
  simp only [beq_self_eq_true, ite_true]
  conv => lhs; tactic => hlc_norm_run_args
  hlc_step_blk
  rw [runFast_call_static (n := 5) (fun _ => rfl) rfl (hr _ _ rfl) rfl (by simp) (by decide +kernel)
    (computeLevel4NextGeneration_equiv resolveProg hr d1 subFuel subFuel (by omega) (by omega) hsf nw ne sw se g
      jh hp)]
  rw [runFast_lreturn]

/-- Equivalence theorem for `computeLevel4NextGeneration-qFGr5tM$default` when the default leaf kernel is used
(default-mask bit 16 set): it loads the singleton `ULong::computeNextGenerationPureKotlin` reference. -/
theorem computeLevel4NextGeneration_qFGr5tM_default_lambda_equiv (resolveProg : String → Option (List JvmInstr))
    (hr : ExtendsAlgKotlinProgs resolveProg) (d subFuel fuel : Nat) (hd : 5 ≤ d) (hsf : 250 ≤ subFuel)
    (hf : 14 ≤ fuel) (nw ne sw se : UInt64) (fn : JvmVal) (mask : UInt32) (hmask : mask &&& 16 ≠ 0)
    (marker : JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (hqi : HasQuadInfoLut jh)
    (hng : HasNextGen4x4Lut jh)
    (hinst : jh.getStatic? lambdaClass1 "INSTANCE" = none ∨
      jh.getStatic? lambdaClass1 "INSTANCE" = some (.allocRef lambdaClass1)) :
    ∃ endSt,
      Jvm.runJvmRes (mkAlgKotlinHooks resolveProg d subFuel) fuel HashLifeComputationKt_computeLevel4NextGeneration_qFGr5tM_default_prog
          (Jvm.initJvmState [(0, .i64 nw), (2, .i64 ne), (4, .i64 sw), (6, .i64 se), (8, fn),
            (9, .i32 mask), (10, marker)] (.i32 0) hp jh) =
        some (.i64 (computeLevel4NextGenerationModel nw ne sw se computeNextGenerationPureKotlinModel), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨d1, rfl⟩ := Nat.exists_eq_add_of_le' (show 1 ≤ d by omega)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  refine exists_of_fast rfl ⟨?pc, ?stk, ?locs, ?main⟩
  case main =>
  simp only [Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
  conv => lhs; arg 5; dsimp only [HashLifeComputationKt_computeLevel4NextGeneration_qFGr5tM_default_prog]
  hlc_step_blk
  have hb : (mask &&& 16 == 0) = false := by simpa using hmask
  rw [Jvm.runJvmResFast_at_branch_cons _ (hbr := rfl), Jvm.evalResBranchInstrCons_ifeq]
  simp only [hb, Bool.false_eq_true, ite_false]
  rw [runFast_getInstance (Or.inl rfl) hinst]
  rw [Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) (by rfl) rfl]
  hlc_step_blk
  rw [runFast_call_static (n := 5) (fun _ => rfl) rfl (hr _ _ rfl) rfl (by simp) (by decide +kernel)
    (computeLevel4NextGeneration_lambda_equiv resolveProg hr d1 subFuel subFuel (by omega) hsf (by omega)
      lambdaClass1 (Or.inl rfl) nw ne sw se jh hp hqi hng)]
  rw [runFast_lreturn]

/-- Equivalence theorem for `computeLevel4NextGeneration(node: MacroCell.Level4Node, computeLeafNextGen)` with a
caller-supplied leaf kernel `g`. -/
theorem computeLevel4NextGeneration_1_equiv (resolveProg : String → Option (List JvmInstr))
    (hr : ExtendsAlgKotlinProgs resolveProg) (d subFuel fuel : Nat) (hd : 2 ≤ d) (hsf : 95 ≤ subFuel)
    (hf : 17 ≤ fuel) (h : UInt32) (nw ne sw se : UInt64) (g : UInt64 → UInt32)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    ∃ endSt,
      Jvm.runJvmRes (mkAlgKotlinHooks resolveProg d subFuel) fuel HashLifeComputationKt_computeLevel4NextGeneration_1_prog
          (Jvm.initJvmState [(0, .ext (.mc (.level4Node h nw ne sw se))), (1, .ext (.fnU64ToI32 g))] (.i32 0) hp jh) =
        some (.i64 (computeLevel4NextGenerationModel nw ne sw se g), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨d1, rfl⟩ := Nat.exists_eq_add_of_le' (show 1 ≤ d by omega)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  refine exists_of_fast rfl ⟨?pc, ?stk, ?locs, ?main⟩
  case main =>
  simp only [Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
  conv => lhs; arg 5; dsimp only [HashLifeComputationKt_computeLevel4NextGeneration_1_prog]
  hlc_step_blk
  rw [runFast_checkNotNullParameter rfl]
  hlc_step_blk
  rw [runFast_checkNotNullParameter rfl]
  hlc_step_blk
  rw [runFast_l4GetNw]
  hlc_step_blk
  rw [runFast_l4GetNe]
  hlc_step_blk
  rw [runFast_l4GetSw]
  hlc_step_blk
  rw [runFast_l4GetSe]
  hlc_step_blk
  rw [runFast_call_static (n := 5) (fun _ => rfl) rfl (hr _ _ rfl) rfl (by simp) (by decide +kernel)
    (computeLevel4NextGeneration_equiv resolveProg hr d1 subFuel subFuel (by omega) (by omega) hsf nw ne sw se g
      jh hp)]
  rw [runFast_lreturn]

/-- Equivalence theorem for `computeLevel4NextGeneration(node: MacroCell.Level4Node, computeLeafNextGen)` with the
default leaf kernel `ULong::computeNextGenerationPureKotlin` (either function-reference singleton). -/
theorem computeLevel4NextGeneration_1_lambda_equiv (resolveProg : String → Option (List JvmInstr))
    (hr : ExtendsAlgKotlinProgs resolveProg) (d subFuel fuel : Nat) (hd : 5 ≤ d) (hsf : 250 ≤ subFuel)
    (hf : 17 ≤ fuel) (c : String) (hc : c = lambdaClass1 ∨ c = lambdaClass2) (h : UInt32) (nw ne sw se : UInt64)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (hqi : HasQuadInfoLut jh) (hng : HasNextGen4x4Lut jh) :
    ∃ endSt,
      Jvm.runJvmRes (mkAlgKotlinHooks resolveProg d subFuel) fuel HashLifeComputationKt_computeLevel4NextGeneration_1_prog
          (Jvm.initJvmState [(0, .ext (.mc (.level4Node h nw ne sw se))), (1, .allocRef c)] (.i32 0) hp jh) =
        some (.i64 (computeLevel4NextGenerationModel nw ne sw se computeNextGenerationPureKotlinModel), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨d1, rfl⟩ := Nat.exists_eq_add_of_le' (show 1 ≤ d by omega)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  refine exists_of_fast rfl ⟨?pc, ?stk, ?locs, ?main⟩
  case main =>
  simp only [Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
  conv => lhs; arg 5; dsimp only [HashLifeComputationKt_computeLevel4NextGeneration_1_prog]
  hlc_step_blk
  rw [runFast_checkNotNullParameter rfl]
  hlc_step_blk
  rw [runFast_checkNotNullParameter rfl]
  hlc_step_blk
  rw [runFast_l4GetNw]
  hlc_step_blk
  rw [runFast_l4GetNe]
  hlc_step_blk
  rw [runFast_l4GetSw]
  hlc_step_blk
  rw [runFast_l4GetSe]
  hlc_step_blk
  rw [runFast_call_static (n := 5) (fun _ => rfl) rfl (hr _ _ rfl) rfl (by simp) (by decide +kernel)
    (computeLevel4NextGeneration_lambda_equiv resolveProg hr d1 subFuel subFuel (by omega) hsf (by omega)
      c hc nw ne sw se jh hp hqi hng)]
  rw [runFast_lreturn]

/-- Equivalence theorem for `computeLevel4NextGeneration$default(node, computeLeafNextGen)` when the caller passes
its own leaf kernel `g` (default-mask bit 2 clear). -/
theorem computeLevel4NextGeneration_default_equiv (resolveProg : String → Option (List JvmInstr))
    (hr : ExtendsAlgKotlinProgs resolveProg) (d subFuel fuel : Nat) (hd : 3 ≤ d) (hsf : 95 ≤ subFuel)
    (hf : 8 ≤ fuel) (h : UInt32) (nw ne sw se : UInt64) (g : UInt64 → UInt32) (mask : UInt32)
    (hmask : mask &&& 2 = 0) (marker : JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    ∃ endSt,
      Jvm.runJvmRes (mkAlgKotlinHooks resolveProg d subFuel) fuel HashLifeComputationKt_computeLevel4NextGeneration_default_prog
          (Jvm.initJvmState [(0, .ext (.mc (.level4Node h nw ne sw se))), (1, .ext (.fnU64ToI32 g)),
            (2, .i32 mask), (3, marker)] (.i32 0) hp jh) =
        some (.i64 (computeLevel4NextGenerationModel nw ne sw se g), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨d1, rfl⟩ := Nat.exists_eq_add_of_le' (show 1 ≤ d by omega)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  refine exists_of_fast rfl ⟨?pc, ?stk, ?locs, ?main⟩
  case main =>
  simp only [Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
  conv => lhs; arg 5; dsimp only [HashLifeComputationKt_computeLevel4NextGeneration_default_prog]
  hlc_step_blk
  rw [Jvm.runJvmResFast_at_branch_cons _ (hbr := rfl), Jvm.evalResBranchInstrCons_ifeq, hmask]
  simp only [beq_self_eq_true, ite_true]
  conv => lhs; tactic => hlc_norm_run_args
  hlc_step_blk
  rw [runFast_call_static (n := 2) (fun _ => rfl) rfl (hr _ _ rfl) rfl (by simp) (by decide +kernel)
    (computeLevel4NextGeneration_1_equiv resolveProg hr d1 subFuel subFuel (by omega) hsf (by omega) h nw ne sw se g
      jh hp)]
  rw [runFast_lreturn]

/-- Equivalence theorem for `computeLevel4NextGeneration$default(node, computeLeafNextGen)` when the default leaf
kernel is used (default-mask bit 2 set): it loads the singleton `ULong::computeNextGenerationPureKotlin` reference. -/
theorem computeLevel4NextGeneration_default_lambda_equiv (resolveProg : String → Option (List JvmInstr))
    (hr : ExtendsAlgKotlinProgs resolveProg) (d subFuel fuel : Nat) (hd : 6 ≤ d) (hsf : 250 ≤ subFuel)
    (hf : 11 ≤ fuel) (h : UInt32) (nw ne sw se : UInt64) (fn : JvmVal) (mask : UInt32) (hmask : mask &&& 2 ≠ 0)
    (marker : JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (hqi : HasQuadInfoLut jh)
    (hng : HasNextGen4x4Lut jh)
    (hinst : jh.getStatic? lambdaClass2 "INSTANCE" = none ∨
      jh.getStatic? lambdaClass2 "INSTANCE" = some (.allocRef lambdaClass2)) :
    ∃ endSt,
      Jvm.runJvmRes (mkAlgKotlinHooks resolveProg d subFuel) fuel HashLifeComputationKt_computeLevel4NextGeneration_default_prog
          (Jvm.initJvmState [(0, .ext (.mc (.level4Node h nw ne sw se))), (1, fn), (2, .i32 mask), (3, marker)]
            (.i32 0) hp jh) =
        some (.i64 (computeLevel4NextGenerationModel nw ne sw se computeNextGenerationPureKotlinModel), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨d1, rfl⟩ := Nat.exists_eq_add_of_le' (show 1 ≤ d by omega)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  refine exists_of_fast rfl ⟨?pc, ?stk, ?locs, ?main⟩
  case main =>
  simp only [Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
  conv => lhs; arg 5; dsimp only [HashLifeComputationKt_computeLevel4NextGeneration_default_prog]
  hlc_step_blk
  have hb : (mask &&& 2 == 0) = false := by simpa using hmask
  rw [Jvm.runJvmResFast_at_branch_cons _ (hbr := rfl), Jvm.evalResBranchInstrCons_ifeq]
  simp only [hb, Bool.false_eq_true, ite_false]
  rw [runFast_getInstance (Or.inr rfl) hinst]
  rw [Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) (by rfl) rfl]
  hlc_step_blk
  rw [runFast_call_static (n := 2) (fun _ => rfl) rfl (hr _ _ rfl) rfl (by simp) (by decide +kernel)
    (computeLevel4NextGeneration_1_lambda_equiv resolveProg hr d1 subFuel subFuel (by omega) hsf (by omega)
      lambdaClass2 (Or.inr rfl) h nw ne sw se jh hp hqi hng)]
  rw [runFast_lreturn]

namespace HashLifeComputation

/-- The function-reference constructor `HashLifeComputationKt$computeLevel4NextGeneration$1.<init>` is not lifted (it
loads a class literal); when `r` does not map it, the hooks model it as producing the stateless singleton. -/
theorem runFast_lambdaInit1 {r : String → Option (List JvmInstr)} {d sf f pc pc0 : Nat}
    {prog rest : List JvmInstr} {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hinit : r "HashLifeComputationKt$computeLevel4NextGeneration$1.<init>:()V" = none) :
    Jvm.runJvmResFast (mkAlgKotlinHooks r d sf) (f + 1) prog pc
        (.invokespecial "com/alexvanyo/composelife/algorithm/HashLifeComputationKt$computeLevel4NextGeneration$1" "<init>" "()V" :: rest)
        ⟨pc0, .allocRef lambdaClass1 :: .allocRef lambdaClass1 :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkAlgKotlinHooks r d sf) f prog (pc + 1) rest
        ⟨pc + 1, .allocRef lambdaClass1 :: stk, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_invokespecial_step _ ?_
  have htag : algKotlinTag "com/alexvanyo/composelife/algorithm/HashLifeComputationKt$computeLevel4NextGeneration$1" "<init>" "()V" =
      "HashLifeComputationKt$computeLevel4NextGeneration$1.<init>:()V" := rfl
  show (mkAlgKotlinHooks r d sf).stepInvokeSpecial _ "com/alexvanyo/composelife/algorithm/HashLifeComputationKt$computeLevel4NextGeneration$1" "<init>"
    "()V" = _
  cases d <;> dsimp only [mkAlgKotlinHooks, algKotlinHooksWith] <;> rw [htag, hinit] <;> rfl

end HashLifeComputation

/-- Equivalence theorem for the static initializer of `HashLifeComputationKt$computeLevel4NextGeneration$1`: it stores
the stateless function-reference singleton in `INSTANCE`. -/
theorem clinit_HashLifeComputationKt_computeLevel4NextGeneration_1_equiv
    (resolveProg : String → Option (List JvmInstr))
    (hinit : resolveProg "HashLifeComputationKt$computeLevel4NextGeneration$1.<init>:()V" = none) (d subFuel fuel : Nat)
    (hf : 5 ≤ fuel)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    ∃ endSt,
      Jvm.runJvmRes (mkAlgKotlinHooks resolveProg d subFuel) fuel
          HashLifeComputationKt_computeLevel4NextGeneration_1_clinit_prog (Jvm.initJvmState [] (.i32 0) hp jh) =
        some (.unit, endSt) ∧
      endSt.jvmHeap = jh.setStatic "com/alexvanyo/composelife/algorithm/HashLifeComputationKt$computeLevel4NextGeneration$1" "INSTANCE"
        (.allocRef lambdaClass1) ∧
      endSt.heap = hp := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  refine exists_of_fast rfl ⟨4, [], fun _ => .i32 0, ?_⟩
  simp only [Jvm.initJvmState, List.foldl_nil]
  conv => lhs; arg 5; dsimp only [HashLifeComputationKt_computeLevel4NextGeneration_1_clinit_prog]
  cases d <;>
  · rw [Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) (by rfl) rfl]
    hlc_step_blk
    rw [runFast_lambdaInit1 hinit]
    rw [Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) (by rfl) rfl]
    rw [runFast_vreturn]

namespace HashLifeComputation

/-- The function-reference constructor `HashLifeComputationKt$computeLevel4NextGeneration$2.<init>` is not lifted (it
loads a class literal); when `r` does not map it, the hooks model it as producing the stateless singleton. -/
theorem runFast_lambdaInit2 {r : String → Option (List JvmInstr)} {d sf f pc pc0 : Nat}
    {prog rest : List JvmInstr} {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hinit : r "HashLifeComputationKt$computeLevel4NextGeneration$2.<init>:()V" = none) :
    Jvm.runJvmResFast (mkAlgKotlinHooks r d sf) (f + 1) prog pc
        (.invokespecial "com/alexvanyo/composelife/algorithm/HashLifeComputationKt$computeLevel4NextGeneration$2" "<init>" "()V" :: rest)
        ⟨pc0, .allocRef lambdaClass2 :: .allocRef lambdaClass2 :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkAlgKotlinHooks r d sf) f prog (pc + 1) rest
        ⟨pc + 1, .allocRef lambdaClass2 :: stk, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_invokespecial_step _ ?_
  have htag : algKotlinTag "com/alexvanyo/composelife/algorithm/HashLifeComputationKt$computeLevel4NextGeneration$2" "<init>" "()V" =
      "HashLifeComputationKt$computeLevel4NextGeneration$2.<init>:()V" := rfl
  show (mkAlgKotlinHooks r d sf).stepInvokeSpecial _ "com/alexvanyo/composelife/algorithm/HashLifeComputationKt$computeLevel4NextGeneration$2" "<init>"
    "()V" = _
  cases d <;> dsimp only [mkAlgKotlinHooks, algKotlinHooksWith] <;> rw [htag, hinit] <;> rfl

end HashLifeComputation

/-- Equivalence theorem for the static initializer of `HashLifeComputationKt$computeLevel4NextGeneration$2`: it stores
the stateless function-reference singleton in `INSTANCE`. -/
theorem clinit_HashLifeComputationKt_computeLevel4NextGeneration_2_equiv
    (resolveProg : String → Option (List JvmInstr))
    (hinit : resolveProg "HashLifeComputationKt$computeLevel4NextGeneration$2.<init>:()V" = none) (d subFuel fuel : Nat)
    (hf : 5 ≤ fuel)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    ∃ endSt,
      Jvm.runJvmRes (mkAlgKotlinHooks resolveProg d subFuel) fuel
          HashLifeComputationKt_computeLevel4NextGeneration_2_clinit_prog (Jvm.initJvmState [] (.i32 0) hp jh) =
        some (.unit, endSt) ∧
      endSt.jvmHeap = jh.setStatic "com/alexvanyo/composelife/algorithm/HashLifeComputationKt$computeLevel4NextGeneration$2" "INSTANCE"
        (.allocRef lambdaClass2) ∧
      endSt.heap = hp := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  refine exists_of_fast rfl ⟨4, [], fun _ => .i32 0, ?_⟩
  simp only [Jvm.initJvmState, List.foldl_nil]
  conv => lhs; arg 5; dsimp only [HashLifeComputationKt_computeLevel4NextGeneration_2_clinit_prog]
  cases d <;>
  · rw [Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) (by rfl) rfl]
    hlc_step_blk
    rw [runFast_lambdaInit2 hinit]
    rw [Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) (by rfl) rfl]
    rw [runFast_vreturn]

end Algorithm.KotlinJvmVerification
