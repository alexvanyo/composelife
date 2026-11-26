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

import Jvm.FastExec
import Jvm.Proofs
import Jvm.Tactics
import JvmSemantics
import KotlinJvmBytecode
import models.GeometryExtensionsModel
import models.SpiralRingModel
import theorems.GeometryExtensionsModelTheorems
import theorems.SpiralRingModelTheorems

namespace Geometry.KotlinJvmVerification
open Geometry.JvmVerification
open Geometry.KotlinJvmBytecode
open Geometry.KotlinModel

local instance (c : UInt64 → Float32) (d : Float32 → Float32) :
    Jvm.HasDefaultIsZero (mkGeomHooks c d) := ⟨rfl⟩

private theorem mkGeomHooks_iteZero? (c : UInt64 → Float32) (d : Float32 → Float32)
    (v : JvmVal) (t e : Option JvmVal) :
    (mkGeomHooks c d).iteZero? v t e =
      match (mkGeomHooks c d).isZero? v with | some true => t | some false => e | none => none := by
  dsimp [mkGeomHooks, Jvm.JvmHooks.iteZero?, Jvm.JvmHooks.isZero?]
  cases hv : Jvm.JvmVal.asI32? v with
  | none => rfl
  | some x => by_cases hx : (x == 0) = true <;> simp [Jvm.defaultIteVal, hx] <;> split <;> rfl

private theorem mkGeomHooks_iteNonZero? (c : UInt64 → Float32) (d : Float32 → Float32)
    (v : JvmVal) (t e : Option JvmVal) :
    (mkGeomHooks c d).iteNonZero? v t e =
      match (mkGeomHooks c d).isZero? v with | some true => e | some false => t | none => none := by
  dsimp [mkGeomHooks, Jvm.JvmHooks.iteNonZero?, Jvm.JvmHooks.isZero?]
  cases hv : Jvm.JvmVal.asI32? v with
  | none => rfl
  | some x => by_cases hx : (x == 0) = true <;> simp [Jvm.defaultIteVal, hx] <;> split <;> rfl

private theorem geomHooks_iteZero? (v : JvmVal) (t e : Option JvmVal) :
    geomHooks.iteZero? v t e =
      match geomHooks.isZero? v with | some true => t | some false => e | none => none :=
  mkGeomHooks_iteZero? _ _ v t e

private theorem geomHooks_iteNonZero? (v : JvmVal) (t e : Option JvmVal) :
    geomHooks.iteNonZero? v t e =
      match geomHooks.isZero? v with | some true => e | some false => t | none => none :=
  mkGeomHooks_iteNonZero? _ _ v t e

private def ringStop : JvmInstr → Bool
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

private def geomOpaqueConsts : NameSet :=
  NameSet.empty
    |>.insert ``Int32.toUInt32
    |>.insert ``UInt32.toInt32
    |>.insert ``Geometry.JvmVerification.geomHooks
    |>.insert ``Geometry.JvmVerification.mkGeomHooks
    |>.insert ``Geometry.JvmVerification.stepIntOffsetStatic
    |>.insert ``Geometry.JvmVerification.packIntOffset
    |>.insert ``Geometry.JvmVerification.unpackIntOffsetX
    |>.insert ``Geometry.JvmVerification.unpackIntOffsetY
    |>.insert ``Geometry.KotlinModel.packOffset
    |>.insert ``Geometry.KotlinModel.offsetX
    |>.insert ``Geometry.KotlinModel.offsetY
    |>.insert ``Geometry.KotlinModel.absI32UInt
    |>.insert ``Geometry.KotlinModel.maxI32UInt
    |>.insert ``Geometry.KotlinModel.toRingIndexModel
    |>.insert ``Geometry.KotlinModel.toRingOffsetModel
    |>.insert ``Jvm.i32ToFloat32
    |>.insert ``Jvm.i32ToFloat
    |>.insert ``Jvm.floatToI32
    |>.insert ``Float32.ofBits
    |>.insert ``Float32.toBits
    |>.insert ``Float.sqrt
    |>.insert ``Float.floor

private def geomInitConsts : List Name :=
  [``initJvmState, ``Jvm.initJvmState]

elab "geom_whnf_blk" : conv => withMainContext do
  let lhs ← Lean.Elab.Tactic.Conv.getLhs
  let res ← Jvm.Tactics.withOpaque geomOpaqueConsts
    (Jvm.Tactics.normJvmBlkExpr geomInitConsts (fun _ => pure none) lhs)
  Lean.Elab.Tactic.Conv.changeLhs res

elab "geom_norm_locals" : tactic =>
  Lean.Elab.Tactic.liftMetaTactic fun g => do
    let tgt ← instantiateMVars (← g.getType)
    let res ← Jvm.Tactics.normJvmLocalsExpr geomInitConsts (fun _ => pure none) [] tgt
    return [← g.replaceTargetDefEq res]

elab "geom_norm_run_args" : tactic =>
  Lean.Elab.Tactic.liftMetaTactic fun g => do
    let tgt ← instantiateMVars (← g.getType)
    let normSt := fun s : Expr => do
      let s1 ← Jvm.Tactics.withOpaque geomOpaqueConsts
        (Jvm.Tactics.normJvmBlkExpr geomInitConsts (fun _ => pure none) s)
      if s1.isAppOfArity ``Jvm.JvmState.mk 7 then
        let sa := s1.getAppArgs
        let pcField ← Jvm.Tactics.normJvmNatWith geomOpaqueConsts sa[2]!
        return mkAppN s1.getAppFn #[sa[0]!, sa[1]!, pcField, sa[3]!, sa[4]!, sa[5]!, sa[6]!]
      else
        return s1
    let normRun := fun b : Expr => do
      if b.isAppOfArity ``Jvm.runJvmResFast 8 then
        let ba := b.getAppArgs
        let fuel' ← Jvm.Tactics.withOpaque geomOpaqueConsts (whnf ba[3]!)
        let pc' ← Jvm.Tactics.withOpaque geomOpaqueConsts (whnf ba[5]!)
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

elab "geom_step_chunk" : tactic => do
  let tgt := (← getMainTarget).consumeMData
  let some (_, lhs, _) := tgt.eq? | return ()
  let lhs := lhs.consumeMData
  if !lhs.isAppOfArity ``Jvm.runJvmResFast 8 then return ()
  evalTactic (← `(tactic| (conv => lhs; tactic => geom_norm_run_args)))
  evalTactic (← `(tactic| rw [Jvm.runJvmResFast_stepBlockChunkWith _ ringStop 64]))
  if !(← getUnsolvedGoals).isEmpty then
    evalTactic (← `(tactic| (conv => lhs; arg 2; geom_whnf_blk)))
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
      evalTactic (← `(tactic| (conv => lhs; tactic => geom_norm_locals; geom_norm_run_args)))

end StepTactics

private theorem step_checkNotNullParameter
    (hooks : Jvm.JvmHooks Empty Unit)
    {f pc pc0 : Nat} {prog rest : List JvmInstr} {tag : String} {v : JvmVal} (hn : Jvm.JvmVal.isNull v = false)
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} :
    Jvm.runJvmResFast hooks (f + 1) prog pc
        (.invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter"
          "(Ljava/lang/Object;Ljava/lang/String;)V" :: rest)
        ⟨pc0, .str tag :: v :: stk, locs, jh, ()⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest ⟨pc + 1, stk, locs, jh, ()⟩ := by
  refine Jvm.runJvmResFast_invokestatic_step hooks ?_
  simp [Jvm.stepInvokeStaticGeneric, hn]

private theorem step_intOffsetCtor
    (c : UInt64 → Float32) (d : Float32 → Float32)
    {f pc pc0 : Nat} {prog rest : List JvmInstr} {p : UInt64}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} :
    Jvm.runJvmResFast (mkGeomHooks c d) (f + 1) prog pc
        (.invokestatic "androidx/compose/ui/unit/IntOffset" "constructor-impl" "(J)J" :: rest)
        ⟨pc0, .i64 p :: stk, locs, jh, ()⟩ =
      Jvm.runJvmResFast (mkGeomHooks c d) f prog (pc + 1) rest ⟨pc + 1, .i64 p :: stk, locs, jh, ()⟩ := by
  refine Jvm.runJvmResFast_invokestatic_step (mkGeomHooks c d) ?_
  dsimp only [Jvm.JvmHooks.stepInvokeStatic, mkGeomHooks, stepIntOffsetStatic]
  rfl

private theorem step_intOffsetGetX
    (c : UInt64 → Float32) (d : Float32 → Float32)
    {f pc pc0 : Nat} {prog rest : List JvmInstr} {p : UInt64}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} :
    Jvm.runJvmResFast (mkGeomHooks c d) (f + 1) prog pc
        (.invokestatic "androidx/compose/ui/unit/IntOffset" "getX-impl" "(J)I" :: rest)
        ⟨pc0, .i64 p :: stk, locs, jh, ()⟩ =
      Jvm.runJvmResFast (mkGeomHooks c d) f prog (pc + 1) rest
        ⟨pc + 1, .i32 (unpackIntOffsetX p).toUInt32 :: stk, locs, jh, ()⟩ := by
  refine Jvm.runJvmResFast_invokestatic_step (mkGeomHooks c d) ?_
  dsimp only [Jvm.JvmHooks.stepInvokeStatic, mkGeomHooks, stepIntOffsetStatic, JvmVal.asI64?]
  rfl

private theorem step_intOffsetGetY
    (c : UInt64 → Float32) (d : Float32 → Float32)
    {f pc pc0 : Nat} {prog rest : List JvmInstr} {p : UInt64}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} :
    Jvm.runJvmResFast (mkGeomHooks c d) (f + 1) prog pc
        (.invokestatic "androidx/compose/ui/unit/IntOffset" "getY-impl" "(J)I" :: rest)
        ⟨pc0, .i64 p :: stk, locs, jh, ()⟩ =
      Jvm.runJvmResFast (mkGeomHooks c d) f prog (pc + 1) rest
        ⟨pc + 1, .i32 (unpackIntOffsetY p).toUInt32 :: stk, locs, jh, ()⟩ := by
  refine Jvm.runJvmResFast_invokestatic_step (mkGeomHooks c d) ?_
  dsimp only [Jvm.JvmHooks.stepInvokeStatic, mkGeomHooks, stepIntOffsetStatic, JvmVal.asI64?]
  rfl

private theorem step_pairGetFirst
    (hooks : Jvm.JvmHooks Empty Unit)
    {f pc pc0 : Nat} {prog rest : List JvmInstr} {a b : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} :
    Jvm.runJvmResFast hooks (f + 1) prog pc
        (.invokevirtual "kotlin/Pair" "getFirst" "()Ljava/lang/Object;" :: rest)
        ⟨pc0, .pair a b :: stk, locs, jh, ()⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest ⟨pc + 1, a :: stk, locs, jh, ()⟩ := by
  refine Jvm.runJvmResFast_invokevirtual_step hooks ?_
  simp [Jvm.stepInvokeVirtualGeneric]

private theorem step_pairGetSecond
    (hooks : Jvm.JvmHooks Empty Unit)
    {f pc pc0 : Nat} {prog rest : List JvmInstr} {a b : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} :
    Jvm.runJvmResFast hooks (f + 1) prog pc
        (.invokevirtual "kotlin/Pair" "getSecond" "()Ljava/lang/Object;" :: rest)
        ⟨pc0, .pair a b :: stk, locs, jh, ()⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest ⟨pc + 1, b :: stk, locs, jh, ()⟩ := by
  refine Jvm.runJvmResFast_invokevirtual_step hooks ?_
  simp [Jvm.stepInvokeVirtualGeneric]

private theorem step_checkcastNumberBoxedInt
    (c : UInt64 → Float32) (d : Float32 → Float32)
    {f pc pc0 : Nat} {prog rest : List JvmInstr} {x : UInt32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} :
    Jvm.runJvmResFast (mkGeomHooks c d) (f + 1) prog pc
        (.checkcast "java/lang/Number" :: rest)
        ⟨pc0, .boxedInt x :: stk, locs, jh, ()⟩ =
      Jvm.runJvmResFast (mkGeomHooks c d) f prog (pc + 1) rest ⟨pc + 1, .boxedInt x :: stk, locs, jh, ()⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr (mkGeomHooks c d) rfl (by simp) rfl rfl

private theorem step_numberIntValueBoxedInt
    (hooks : Jvm.JvmHooks Empty Unit)
    {f pc pc0 : Nat} {prog rest : List JvmInstr} {x : UInt32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} :
    Jvm.runJvmResFast hooks (f + 1) prog pc
        (.invokevirtual "java/lang/Number" "intValue" "()I" :: rest)
        ⟨pc0, .boxedInt x :: stk, locs, jh, ()⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest ⟨pc + 1, .i32 x :: stk, locs, jh, ()⟩ := by
  refine Jvm.runJvmResFast_invokevirtual_step hooks ?_
  simp [Jvm.stepInvokeVirtualGeneric]

private theorem step_integerValueOf
    (c : UInt64 → Float32) (d : Float32 → Float32)
    {f pc pc0 : Nat} {prog rest : List JvmInstr} {x : UInt32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} :
    Jvm.runJvmResFast (mkGeomHooks c d) (f + 1) prog pc
        (.invokestatic "java/lang/Integer" "valueOf" "(I)Ljava/lang/Integer;" :: rest)
        ⟨pc0, .i32 x :: stk, locs, jh, ()⟩ =
      Jvm.runJvmResFast (mkGeomHooks c d) f prog (pc + 1) rest ⟨pc + 1, .boxedInt x :: stk, locs, jh, ()⟩ := by
  refine Jvm.runJvmResFast_invokestatic_step (mkGeomHooks c d) ?_
  simp [Jvm.stepInvokeStaticGeneric, JvmVal.asI32?]

private theorem step_tuplesTo
    (c : UInt64 → Float32) (d : Float32 → Float32)
    {f pc pc0 : Nat} {prog rest : List JvmInstr} {a b : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} :
    Jvm.runJvmResFast (mkGeomHooks c d) (f + 1) prog pc
        (.invokestatic "kotlin/TuplesKt" "to" "(Ljava/lang/Object;Ljava/lang/Object;)Lkotlin/Pair;" :: rest)
        ⟨pc0, b :: a :: stk, locs, jh, ()⟩ =
      Jvm.runJvmResFast (mkGeomHooks c d) f prog (pc + 1) rest ⟨pc + 1, .pair a b :: stk, locs, jh, ()⟩ := by
  refine Jvm.runJvmResFast_invokestatic_step (mkGeomHooks c d) ?_
  simp [Jvm.stepInvokeStaticGeneric, stepIntOffsetStatic]

private theorem u64_eq_of_toBitVec {a b : UInt64} (h : a.toBitVec = b.toBitVec) : a = b := by
  cases a; cases b; cases h; rfl

private theorem u64_signExtend_shl32 (x : UInt32) :
    ({ toBitVec := BitVec.signExtend 64 x.toBitVec } : UInt64) <<<
        (((32 : UInt32) &&& (63 : UInt32)).toUInt64) =
      x.toUInt64 <<< 32 := by
  apply u64_eq_of_toBitVec
  apply BitVec.eq_of_getLsbD_eq
  intro i
  have hL :
      (({ toBitVec := BitVec.signExtend 64 x.toBitVec } : UInt64) <<<
          (((32 : UInt32) &&& (63 : UInt32)).toUInt64)).toBitVec.getLsbD i =
        (BitVec.signExtend 64 x.toBitVec <<< 32#64).getLsbD i := rfl
  have hR : (x.toUInt64 <<< 32).toBitVec.getLsbD i =
      (BitVec.zeroExtend 64 x.toBitVec <<< 32#64).getLsbD i := rfl
  rw [hL, hR]
  by_cases hi64 : i < 64
  · by_cases hi : i < 32
    · simp [BitVec.getLsbD_shiftLeft, hi]
    · have hlt32 : i - 32 < 32 := by omega
      simp [BitVec.getElem_signExtend, BitVec.getElem_setWidth, hi, hi64, hlt32]
  · simp [BitVec.getLsbD_shiftLeft, hi64]

private theorem u64_signExtend_andMask (y : UInt32) :
    ({ toBitVec := BitVec.signExtend 64 y.toBitVec } : UInt64) &&& (4294967295 : UInt64) =
      y.toUInt64 := by
  apply u64_eq_of_toBitVec
  apply BitVec.eq_of_getLsbD_eq
  intro i
  have hL :
      (({ toBitVec := BitVec.signExtend 64 y.toBitVec } : UInt64) &&&
          (4294967295 : UInt64)).toBitVec.getLsbD i =
        ((BitVec.signExtend 64 y.toBitVec) &&& 4294967295#64).getLsbD i := rfl
  have hR : y.toUInt64.toBitVec.getLsbD i = (BitVec.zeroExtend 64 y.toBitVec).getLsbD i := rfl
  rw [hL, hR]
  by_cases hi64 : i < 64
  · have hm : (4294967295#64).getLsbD i = decide (i < 32) := by
      rw [BitVec.getLsbD_ofNat, show (4294967295 : Nat) = 2 ^ 32 - 1 by rfl,
        Nat.testBit_two_pow_sub_one]
      simp [hi64]
    by_cases hi : i < 32
    · have hm' : (4294967295#64).getLsbD i = true := by rw [hm]; exact decide_eq_true hi
      rw [BitVec.getLsbD_and, hm', Bool.and_true]
      simp [hi, hi64, BitVec.getElem_signExtend, BitVec.getElem_setWidth]
    · have hm' : (4294967295#64).getLsbD i = false := by rw [hm]; simp [hi]
      rw [BitVec.getLsbD_and, hm', Bool.and_false]
      have hlt : y.toNat < 2 ^ i := by
        have hy : y.toNat < 2 ^ 32 := y.toBitVec.isLt
        have hp : 2 ^ 32 ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      simp [BitVec.getLsbD, hi64, Nat.testBit_lt_two_pow hlt]
  · simp [hi64]

private theorem packOffset_signExt (x y : Int32) :
    ({ toBitVec := BitVec.signExtend 64 x.toUInt32.toBitVec } : UInt64) <<<
        (((32 : UInt32) &&& (63 : UInt32)).toUInt64) |||
      y.toUInt32.toUInt64 = packOffset x y := by
  rw [u64_signExtend_shl32]
  rfl

private theorem step_getCompanionZero
    (hooks : Jvm.JvmHooks Empty Unit)
    {f pc pc0 : Nat} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty}
    (hc : hooks = geomHooks)
    (hs : jh.getStatic? "androidx/compose/ui/unit/IntOffset" "Companion" = none) :
    Jvm.runJvmResFast hooks (f + 1) prog pc
        (.getstatic "androidx/compose/ui/unit/IntOffset" "Companion"
          "Landroidx/compose/ui/unit/IntOffset$Companion;" :: rest)
        ⟨pc0, stk, locs, jh, ()⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest
        ⟨pc + 1, .allocRef "androidx/compose/ui/unit/IntOffset$Companion" :: stk, locs, jh, ()⟩ := by
  subst hc
  exact Jvm.runJvmResFast_step_of_stepInstr geomHooks rfl (by simp)
    (by
      dsimp only [Jvm.stepInstr, mkGeomHooks]
      rw [hs]
      rfl)
    rfl

private theorem step_getZeroVal
    {f pc pc0 : Nat} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} :
    Jvm.runJvmResFast geomHooks (f + 1) prog pc
        (.invokevirtual "androidx/compose/ui/unit/IntOffset$Companion" "getZero-nOcc-ac" "()J" :: rest)
        ⟨pc0, .allocRef "androidx/compose/ui/unit/IntOffset$Companion" :: stk, locs, jh, ()⟩ =
      Jvm.runJvmResFast geomHooks f prog (pc + 1) rest
        ⟨pc + 1, .i64 0 :: stk, locs, jh, ()⟩ := by
  refine Jvm.runJvmResFast_invokevirtual_step geomHooks ?_
  dsimp only [Jvm.stepInvokeVirtualGeneric, Jvm.JvmHooks.stepInvokeVirtual, mkGeomHooks]
  rfl

private theorem step_intOffsetEq0
    {f pc pc0 : Nat} {prog rest : List JvmInstr} {a b : UInt64}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} :
    Jvm.runJvmResFast geomHooks (f + 1) prog pc
        (.invokestatic "androidx/compose/ui/unit/IntOffset" "equals-impl0" "(JJ)Z" :: rest)
        ⟨pc0, .i64 b :: .i64 a :: stk, locs, jh, ()⟩ =
      Jvm.runJvmResFast geomHooks f prog (pc + 1) rest
        ⟨pc + 1, .i32 (if a == b then 1 else 0) :: stk, locs, jh, ()⟩ := by
  refine Jvm.runJvmResFast_invokestatic_step geomHooks ?_
  dsimp only [Jvm.stepInvokeStaticGeneric, Jvm.JvmHooks.stepInvokeStatic, mkGeomHooks,
    stepIntOffsetStatic, JvmVal.asI64?]
  rfl

private theorem step_mathAbs
    {f pc pc0 : Nat} {prog rest : List JvmInstr} {x : UInt32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} :
    Jvm.runJvmResFast geomHooks (f + 1) prog pc
        (.invokestatic "java/lang/Math" "abs" "(I)I" :: rest)
        ⟨pc0, .i32 x :: stk, locs, jh, ()⟩ =
      Jvm.runJvmResFast geomHooks f prog (pc + 1) rest
        ⟨pc + 1, .i32 (if x.toBitVec.slt 0#32 then -x else x) :: stk, locs, jh, ()⟩ := by
  refine Jvm.runJvmResFast_invokestatic_step geomHooks ?_
  simp [Jvm.stepInvokeStaticGeneric, JvmVal.asI32?]

private theorem step_mathMax
    {f pc pc0 : Nat} {prog rest : List JvmInstr} {a b : UInt32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} :
    Jvm.runJvmResFast geomHooks (f + 1) prog pc
        (.invokestatic "java/lang/Math" "max" "(II)I" :: rest)
        ⟨pc0, .i32 b :: .i32 a :: stk, locs, jh, ()⟩ =
      Jvm.runJvmResFast geomHooks f prog (pc + 1) rest
        ⟨pc + 1, .i32 (if a.toBitVec.slt b.toBitVec then b else a) :: stk, locs, jh, ()⟩ := by
  refine Jvm.runJvmResFast_invokestatic_step geomHooks ?_
  simp [Jvm.stepInvokeStaticGeneric, JvmVal.asI32?]

private theorem step_idiv4
    {f pc pc0 : Nat} {prog rest : List JvmInstr} {a : UInt32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} :
    Jvm.runJvmResFast geomHooks (f + 1) prog pc (.idiv :: rest)
        ⟨pc0, .i32 4 :: .i32 a :: stk, locs, jh, ()⟩ =
      Jvm.runJvmResFast geomHooks f prog (pc + 1) rest
        ⟨pc + 1, .i32 (UInt32.ofBitVec (a.toBitVec.sdiv 4#32)) :: stk, locs, jh, ()⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr geomHooks rfl (by simp)
    (by
      dsimp only [Jvm.stepInstr, JvmVal.asI32?, Jvm.jvmI32Div]
      rfl)
    rfl

private theorem step_floatToRawIntBits
    (c : UInt64 → Float32) (d : Float32 → Float32)
    {f pc pc0 : Nat} {prog rest : List JvmInstr} {x : Float32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} :
    Jvm.runJvmResFast (mkGeomHooks c d) (f + 1) prog pc
        (.invokestatic "java/lang/Float" "floatToRawIntBits" "(F)I" :: rest)
        ⟨pc0, .f32 x :: stk, locs, jh, ()⟩ =
      Jvm.runJvmResFast (mkGeomHooks c d) f prog (pc + 1) rest
        ⟨pc + 1, .i32 x.toBits :: stk, locs, jh, ()⟩ := by
  refine Jvm.runJvmResFast_invokestatic_step (mkGeomHooks c d) ?_
  dsimp only [Jvm.stepInvokeStaticGeneric, Jvm.JvmHooks.stepInvokeStatic, mkGeomHooks,
    stepIntOffsetStatic, JvmVal.asF32?]
  rfl

private theorem step_offsetCtor
    (c : UInt64 → Float32) (d : Float32 → Float32)
    {f pc pc0 : Nat} {prog rest : List JvmInstr} {p : UInt64}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} :
    Jvm.runJvmResFast (mkGeomHooks c d) (f + 1) prog pc
        (.invokestatic "androidx/compose/ui/geometry/Offset" "constructor-impl" "(J)J" :: rest)
        ⟨pc0, .i64 p :: stk, locs, jh, ()⟩ =
      Jvm.runJvmResFast (mkGeomHooks c d) f prog (pc + 1) rest ⟨pc + 1, .i64 p :: stk, locs, jh, ()⟩ := by
  refine Jvm.runJvmResFast_invokestatic_step (mkGeomHooks c d) ?_
  dsimp only [Jvm.stepInvokeStaticGeneric, Jvm.JvmHooks.stepInvokeStatic, mkGeomHooks, stepIntOffsetStatic]
  rfl

private theorem step_offsetGetDistance
    (c : UInt64 → Float32) (d : Float32 → Float32)
    {f pc pc0 : Nat} {prog rest : List JvmInstr} {p : UInt64}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} :
    Jvm.runJvmResFast (mkGeomHooks c d) (f + 1) prog pc
        (.invokestatic "androidx/compose/ui/geometry/Offset" "getDistance-impl" "(J)F" :: rest)
        ⟨pc0, .i64 p :: stk, locs, jh, ()⟩ =
      Jvm.runJvmResFast (mkGeomHooks c d) f prog (pc + 1) rest
        ⟨pc + 1, .f32 (c p) :: stk, locs, jh, ()⟩ := by
  refine Jvm.runJvmResFast_invokestatic_step (mkGeomHooks c d) ?_
  dsimp only [Jvm.stepInvokeStaticGeneric, Jvm.JvmHooks.stepInvokeStatic, mkGeomHooks,
    stepIntOffsetStatic, JvmVal.asI64?]
  rfl

private theorem step_dpOffsetGetX
    (c : UInt64 → Float32) (d : Float32 → Float32)
    {f pc pc0 : Nat} {prog rest : List JvmInstr} {p : UInt64}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} :
    Jvm.runJvmResFast (mkGeomHooks c d) (f + 1) prog pc
        (.invokestatic "androidx/compose/ui/unit/DpOffset" "getX-D9Ej5fM" "(J)F" :: rest)
        ⟨pc0, .i64 p :: stk, locs, jh, ()⟩ =
      Jvm.runJvmResFast (mkGeomHooks c d) f prog (pc + 1) rest
        ⟨pc + 1, .f32 (Float32.ofBits (p >>> 32).toUInt32) :: stk, locs, jh, ()⟩ := by
  refine Jvm.runJvmResFast_invokestatic_step (mkGeomHooks c d) ?_
  dsimp only [Jvm.stepInvokeStaticGeneric, Jvm.JvmHooks.stepInvokeStatic, mkGeomHooks,
    stepIntOffsetStatic, JvmVal.asI64?]
  rfl

private theorem step_dpOffsetGetY
    (c : UInt64 → Float32) (d : Float32 → Float32)
    {f pc pc0 : Nat} {prog rest : List JvmInstr} {p : UInt64}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} :
    Jvm.runJvmResFast (mkGeomHooks c d) (f + 1) prog pc
        (.invokestatic "androidx/compose/ui/unit/DpOffset" "getY-D9Ej5fM" "(J)F" :: rest)
        ⟨pc0, .i64 p :: stk, locs, jh, ()⟩ =
      Jvm.runJvmResFast (mkGeomHooks c d) f prog (pc + 1) rest
        ⟨pc + 1, .f32 (Float32.ofBits p.toUInt32) :: stk, locs, jh, ()⟩ := by
  refine Jvm.runJvmResFast_invokestatic_step (mkGeomHooks c d) ?_
  dsimp only [Jvm.stepInvokeStaticGeneric, Jvm.JvmHooks.stepInvokeStatic, mkGeomHooks,
    stepIntOffsetStatic, JvmVal.asI64?]
  rfl

private theorem step_densityToPx
    (c : UInt64 → Float32) (d : Float32 → Float32)
    {f pc pc0 : Nat} {prog rest : List JvmInstr} {x : Float32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} :
    Jvm.runJvmResFast (mkGeomHooks c d) (f + 1) prog pc
        (.invokeinterface "androidx/compose/ui/unit/Density" "toPx-0680j_4" "(F)F" :: rest)
        ⟨pc0, .f32 x :: .allocRef "androidx/compose/ui/unit/Density" :: stk, locs, jh, ()⟩ =
      Jvm.runJvmResFast (mkGeomHooks c d) f prog (pc + 1) rest
        ⟨pc + 1, .f32 (d x) :: stk, locs, jh, ()⟩ := by
  refine Jvm.runJvmResFast_invokeinterface_step (mkGeomHooks c d) ?_
  dsimp only [Jvm.stepInvokeInterfaceGeneric, Jvm.JvmHooks.stepInvokeInterface, mkGeomHooks, JvmVal.asF32?]
  rfl

/-- Bridge theorem: `OffsetExtensionsKt.toIntOffset(Pair<Int, Int>)` packs `(first, second)` via `packOffset`. -/
theorem toIntOffset_equiv (x y : Int32) (jh : Jvm.JvmHeap Empty := {}) :
    runJvm 35 OffsetExtensionsKt_toIntOffset_prog
      (initJvmState [(0, .pair (.boxedInt x.toUInt32) (.boxedInt y.toUInt32))] jh) =
      some (.i64 (packOffset x y)) := by
  have hfast :
      ∃ st', Jvm.runJvmResFast geomHooks 35 OffsetExtensionsKt_toIntOffset_prog 0 OffsetExtensionsKt_toIntOffset_prog
        (initJvmState [(0, .pair (.boxedInt x.toUInt32) (.boxedInt y.toUInt32))] jh) =
        some (.i64 (packOffset x y), st') := by
    refine ⟨?_, ?_⟩; swap
    geom_step_chunk
    rw [step_checkNotNullParameter geomHooks rfl]
    geom_step_chunk
    rw [step_pairGetFirst geomHooks, step_checkcastNumberBoxedInt, step_numberIntValueBoxedInt geomHooks]
    geom_step_chunk
    rw [step_pairGetSecond geomHooks, step_checkcastNumberBoxedInt, step_numberIntValueBoxedInt geomHooks]
    geom_step_chunk
    rw [step_intOffsetCtor, packOffset_signExt]
    rw [Jvm.runJvmResFast.eq_def]
    rfl
  rcases hfast with ⟨st', hfast⟩
  dsimp only [runJvm]
  rw [Jvm.runJvm_eq_runJvmRes geomHooks geomHooks_iteZero? geomHooks_iteNonZero?,
    Jvm.runJvmRes_of_runJvmResFast0 geomHooks 35 OffsetExtensionsKt_toIntOffset_prog _ _ rfl hfast]
  rfl

/-- Bridge theorem: `OffsetExtensionsKt.toPair(IntOffset)` unpacks into `Pair(x, y)`. -/
theorem toPair_equiv (o : UInt64) (jh : Jvm.JvmHeap Empty := {}) :
    runJvm 20 OffsetExtensionsKt_toPair_prog (initJvmState [(0, .i64 o)] jh) =
      some (.pair (.boxedInt (offsetX o).toUInt32) (.boxedInt (offsetY o).toUInt32)) := by
  have hfast :
      ∃ st', Jvm.runJvmResFast geomHooks 20 OffsetExtensionsKt_toPair_prog 0 OffsetExtensionsKt_toPair_prog
        (initJvmState [(0, .i64 o)] jh) =
        some (.pair (.boxedInt (offsetX o).toUInt32) (.boxedInt (offsetY o).toUInt32), st') := by
    refine ⟨?_, ?_⟩; swap
    geom_step_chunk
    rw [step_intOffsetGetX, step_integerValueOf]
    geom_step_chunk
    rw [step_intOffsetGetY, step_integerValueOf, step_tuplesTo]
    rw [Jvm.runJvmResFast.eq_def]
    rfl
  rcases hfast with ⟨st', hfast⟩
  dsimp only [runJvm]
  rw [Jvm.runJvm_eq_runJvmRes geomHooks geomHooks_iteZero? geomHooks_iteNonZero?,
    Jvm.runJvmRes_of_runJvmResFast0 geomHooks 20 OffsetExtensionsKt_toPair_prog _ _ rfl hfast]
  rfl

/-- Bridge theorem: `OffsetExtensionsKt.euclideanDistance(IntOffset)` invokes `Offset.getDistance-impl`. -/
theorem euclideanDistance_equiv
    (calcDistance : UInt64 → Float32) (densityToPx : Float32 → Float32)
    (o : UInt64) (jh : Jvm.JvmHeap Empty := {}) :
    Jvm.runJvm (mkGeomHooks calcDistance densityToPx) 45 OffsetExtensionsKt_euclideanDistance_prog
      (initJvmState [(0, .i64 o)] jh) =
      some (.f32 (calcDistance (
        ((Jvm.i32ToFloat32 (offsetX o).toUInt32).toBits.toUInt64 <<< 32) |||
        (Jvm.i32ToFloat32 (offsetY o).toUInt32).toBits.toUInt64))) := by
  have hfast :
      ∃ st', Jvm.runJvmResFast (mkGeomHooks calcDistance densityToPx) 45 OffsetExtensionsKt_euclideanDistance_prog 0
        OffsetExtensionsKt_euclideanDistance_prog (initJvmState [(0, .i64 o)] jh) =
        some (.f32 (calcDistance (
          ((Jvm.i32ToFloat32 (offsetX o).toUInt32).toBits.toUInt64 <<< 32) |||
          (Jvm.i32ToFloat32 (offsetY o).toUInt32).toBits.toUInt64)), st') := by
    refine ⟨?_, ?_⟩; swap
    geom_step_chunk
    rw [step_intOffsetGetX]
    geom_step_chunk
    rw [step_intOffsetGetY]
    geom_step_chunk
    rw [step_floatToRawIntBits]
    geom_step_chunk
    rw [step_floatToRawIntBits]
    geom_step_chunk
    rw [u64_signExtend_shl32, u64_signExtend_andMask, step_offsetCtor]
    geom_step_chunk
    rw [step_offsetGetDistance]
    rw [Jvm.runJvmResFast.eq_def]
    rfl
  rcases hfast with ⟨st', hfast⟩
  rw [Jvm.runJvm_eq_runJvmRes (mkGeomHooks calcDistance densityToPx)
      (mkGeomHooks_iteZero? calcDistance densityToPx) (mkGeomHooks_iteNonZero? calcDistance densityToPx),
    Jvm.runJvmRes_of_runJvmResFast0 (mkGeomHooks calcDistance densityToPx) 45 OffsetExtensionsKt_euclideanDistance_prog _ _ rfl hfast]
  rfl

/-- Bridge theorem: `OffsetExtensionsKt.toPx(DpOffset)` converts `x` and `y` via `Density.toPx`. -/
theorem toPx_equiv
    (calcDistance : UInt64 → Float32) (densityToPx : Float32 → Float32)
    (dp : UInt64) (jh : Jvm.JvmHeap Empty := {}) :
    Jvm.runJvm (mkGeomHooks calcDistance densityToPx) 45 OffsetExtensionsKt_toPx_prog
      (initJvmState [(0, .allocRef "androidx/compose/ui/unit/Density"), (1, .i64 dp)] jh) =
      some (.i64 (
        ((densityToPx (Float32.ofBits (dp >>> 32).toUInt32)).toBits.toUInt64 <<< 32) |||
        (densityToPx (Float32.ofBits dp.toUInt32)).toBits.toUInt64)) := by
  have hfast :
      ∃ st', Jvm.runJvmResFast (mkGeomHooks calcDistance densityToPx) 45 OffsetExtensionsKt_toPx_prog 0 OffsetExtensionsKt_toPx_prog
        (initJvmState [(0, .allocRef "androidx/compose/ui/unit/Density"), (1, .i64 dp)] jh) =
        some (.i64 (
          ((densityToPx (Float32.ofBits (dp >>> 32).toUInt32)).toBits.toUInt64 <<< 32) |||
          (densityToPx (Float32.ofBits dp.toUInt32)).toBits.toUInt64), st') := by
    refine ⟨?_, ?_⟩; swap
    geom_step_chunk
    rw [step_checkNotNullParameter (mkGeomHooks calcDistance densityToPx) rfl]
    geom_step_chunk
    rw [step_dpOffsetGetX, step_densityToPx]
    geom_step_chunk
    rw [step_dpOffsetGetY, step_densityToPx]
    geom_step_chunk
    rw [step_floatToRawIntBits]
    geom_step_chunk
    rw [step_floatToRawIntBits]
    geom_step_chunk
    rw [u64_signExtend_shl32, u64_signExtend_andMask, step_offsetCtor]
    rw [Jvm.runJvmResFast.eq_def]
    rfl
  rcases hfast with ⟨st', hfast⟩
  rw [Jvm.runJvm_eq_runJvmRes (mkGeomHooks calcDistance densityToPx)
      (mkGeomHooks_iteZero? calcDistance densityToPx) (mkGeomHooks_iteNonZero? calcDistance densityToPx),
    Jvm.runJvmRes_of_runJvmResFast0 (mkGeomHooks calcDistance densityToPx) 45 OffsetExtensionsKt_toPx_prog _ _ rfl hfast]
  rfl

private theorem toRingIndex_zero_equiv_of_fuel (k : Nat) (jh : Jvm.JvmHeap Empty := {})
    (hs : jh.getStatic? "androidx/compose/ui/unit/IntOffset" "Companion" = none := by rfl) :
    runJvm (k + 7) OffsetExtensionsKt_toRingIndex_prog (initJvmState [(0, .i64 0)] jh) = some (.i32 0) := by
  have hfast :
      ∃ st', Jvm.runJvmResFast geomHooks (k + 7) OffsetExtensionsKt_toRingIndex_prog 0 OffsetExtensionsKt_toRingIndex_prog
        (initJvmState [(0, .i64 0)] jh) = some (.i32 0, st') := by
    refine ⟨?_, ?_⟩; swap
    geom_step_chunk
    rw [step_getCompanionZero geomHooks rfl hs, step_getZeroVal, step_intOffsetEq0]
    rw [Jvm.runJvmResFast_at_branch_cons _ (hbr := rfl), Jvm.evalResBranchInstrCons_ifeq]
    simp only [beq_self_eq_true, ↓reduceIte, show ((1 : UInt32) == 0) = false from rfl,
      Bool.false_eq_true]
    geom_step_chunk
    rw [Jvm.runJvmResFast.eq_def]
    rfl
  rcases hfast with ⟨st', hfast⟩
  dsimp only [runJvm]
  rw [Jvm.runJvm_eq_runJvmRes geomHooks geomHooks_iteZero? geomHooks_iteNonZero?,
    Jvm.runJvmRes_of_runJvmResFast0 geomHooks (k + 7) OffsetExtensionsKt_toRingIndex_prog _ _ rfl hfast]
  rfl

/-- Zero origin short-circuit of `OffsetExtensionsKt.toRingIndex`. -/
theorem toRingIndex_zero_equiv (jh : Jvm.JvmHeap Empty := {})
    (hs : jh.getStatic? "androidx/compose/ui/unit/IntOffset" "Companion" = none := by rfl) :
    runJvm 15 OffsetExtensionsKt_toRingIndex_prog (initJvmState [(0, .i64 0)] jh) = some (.i32 0) :=
  toRingIndex_zero_equiv_of_fuel 8 jh hs

private theorem unpackIntOffsetX_eq (p : UInt64) : unpackIntOffsetX p = offsetX p := rfl
private theorem unpackIntOffsetY_eq (p : UInt64) : unpackIntOffsetY p = offsetY p := rfl
private theorem u32_add (a b : Int32) : (a + b).toUInt32 = a.toUInt32 + b.toUInt32 := rfl
private theorem u32_sub (a b : Int32) : (a - b).toUInt32 = a.toUInt32 - b.toUInt32 := rfl
private theorem u32_neg (a : Int32) : (-a).toUInt32 = -a.toUInt32 := rfl
private theorem beq_int32_toUInt32 (a b : Int32) : (a.toUInt32 == b.toUInt32) = (a == b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  constructor
  · intro h
    cases a; cases b
    exact congrArg Int32.ofUInt32 h
  · intro h
    subst h
    rfl

private theorem step_ireturn
    {f pc pc0 : Nat} {prog rest : List JvmInstr}
    {v : UInt32} {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} :
    Jvm.runJvmResFast geomHooks (f + 1) prog pc (.ireturn :: rest) ⟨pc0, .i32 v :: stk, locs, jh, ()⟩ =
      some (.i32 v, ⟨pc, .i32 v :: stk, locs, jh, ()⟩) := by
  have hstep : Jvm.stepInstr geomHooks Jvm.JvmInstr.ireturn ⟨pc, .i32 v :: stk, locs, jh, ()⟩ =
      .inr (some (.i32 v)) := by
    dsimp only [Jvm.stepInstr, mkGeomHooks]
    rfl
  rw [Jvm.runJvmResFast.eq_def]
  dsimp only
  rw [Jvm.ite_bool_eq_true_right (rfl : Jvm.isBranchInstr Jvm.JvmInstr.ireturn = false), hstep]

@[irreducible] private def hold {α : Type _} (x : α) : α := x

private theorem hold_subst {α : Type _} {x y : α} {P : α → Prop}
    (heq : x = hold y) (hy : P y) : P x := by
  unfold hold at heq
  exact heq ▸ hy

/--
Symbolic equivalence for bounded coordinates `|x|, |y| ≤ 23169`: real compiled `OffsetExtensionsKt_toRingIndex_prog`
never fails `check(...)` assertions and returns the exact `toRingIndexMath x.toInt y.toInt` result
with proved Chebyshev shell bounds.
-/
theorem toRingIndex_equiv_of_bounded (x y : Int32)
    (hx : x.toInt.natAbs ≤ 23169) (hy : y.toInt.natAbs ≤ 23169)
    (jh : Jvm.JvmHeap Empty := {})
    (hs : jh.getStatic? "androidx/compose/ui/unit/IntOffset" "Companion" = none := by rfl) :
    ∃ idx : Int32,
      runJvm 120 OffsetExtensionsKt_toRingIndex_prog (initJvmState [(0, .i64 (packOffset x y))] jh) =
        some (.i32 idx.toUInt32) ∧
      toRingIndexModel x y = some idx ∧
      idx.toInt = toRingIndexMath x.toInt y.toInt ∧
      (x = 0 ∧ y = 0 → idx = 0) ∧
      (let r : Int := max x.toInt.natAbs y.toInt.natAbs
       1 ≤ r →
       (2 * (r - 1) + 1) * (2 * (r - 1) + 1) ≤ idx.toInt ∧
       idx.toInt < (2 * r + 1) * (2 * r + 1)) := by
  rcases toRingIndex_noCheckFail_and_shellBounds x y hx hy with ⟨idx, hmod, him, hz, hsh⟩
  refine ⟨idx, ?_, hmod, him, hz, hsh⟩
  by_cases h0 : x = 0 ∧ y = 0
  · rcases h0 with ⟨rfl, rfl⟩
    have hidx0 : idx = 0 := hz ⟨rfl, rfl⟩
    subst hidx0
    have hpz : packOffset (0 : Int32) (0 : Int32) = 0 := rfl
    have hzero : (0 : Int32).toUInt32 = 0 := rfl
    rw [hpz, hzero]
    exact toRingIndex_zero_equiv_of_fuel 113 jh hs
  · have hp0 : packOffset x y ≠ 0 := by
      intro hpk
      apply h0
      have hox : offsetX (packOffset x y) = x := offsetX_pack x y
      have hoy : offsetY (packOffset x y) = y := offsetY_pack x y
      rw [hpk] at hox hoy
      exact ⟨hox.symm, hoy.symm⟩
    have hpB : (packOffset x y == 0) = false := beq_false_of_ne hp0
    have hxy0 : (x == 0 && y == 0) = false := by
      cases hx0 : x == 0 <;> cases hy0 : y == 0 <;> simp_all [beq_iff_eq]
    have hxPack : offsetX (packOffset x y) = x := offsetX_pack x y
    have hyPack : offsetY (packOffset x y) = y := offsetY_pack x y
    suffices hfast : ∃ st',
        Jvm.runJvmResFast geomHooks 120 OffsetExtensionsKt_toRingIndex_prog 0 OffsetExtensionsKt_toRingIndex_prog
          (initJvmState [(0, .i64 (packOffset x y))] jh) =
          some (.i32 idx.toUInt32, st') by
      rcases hfast with ⟨st', hfast⟩
      dsimp only [runJvm]
      rw [Jvm.runJvm_eq_runJvmRes geomHooks geomHooks_iteZero? geomHooks_iteNonZero?,
        Jvm.runJvmRes_of_runJvmResFast0 geomHooks 120 OffsetExtensionsKt_toRingIndex_prog _ _ rfl hfast]
      rfl
    set ring32 : UInt32 :=
      if (if x.toUInt32.toBitVec.slt 0#32 then -x.toUInt32 else x.toUInt32).toBitVec.slt
          (if y.toUInt32.toBitVec.slt 0#32 then -y.toUInt32 else y.toUInt32).toBitVec then
        if y.toUInt32.toBitVec.slt 0#32 then -y.toUInt32 else y.toUInt32
      else if x.toUInt32.toBitVec.slt 0#32 then -x.toUInt32 else x.toUInt32
    set ring : Int32 := ring32.toInt32
    have hringEq :
        ring = (maxI32UInt (absI32UInt x.toUInt32) (absI32UInt y.toUInt32)).toInt32 := rfl
    dsimp only [toRingIndexModel] at hmod
    rw [ite_eq_right (fun h => by simp [hxy0] at h), ← hringEq] at hmod
    set ringMin : Int32 := (2 * (ring - 1) + 1) * (2 * (ring - 1) + 1)
    set ringMax : Int32 := (2 * ring + 1) * (2 * ring + 1)
    set ringQ : Int32 := Int32.ofBitVec ((ringMax - ringMin).toBitVec.sdiv 4#32)
    set ringQ1 : Int32 := ringMin + ringQ
    set ringQ2 : Int32 := ringQ1 + ringQ
    set ringQ3 : Int32 := ringQ2 + ringQ
    have hchk : ringMax = ringQ3 + ringQ := by
      by_contra hnc
      have hb := beq_false_of_ne hnc
      simp only [hb, Bool.false_eq_true, ↓reduceIte] at hmod
      cases hmod
    have hchkB : (ringMax == ringQ3 + ringQ) = true := beq_iff_eq.mpr hchk
    simp only [hchkB, ↓reduceIte] at hmod
    have hringU : ring.toUInt32 = ring32 := rfl
    have hMinU : ringMin.toUInt32 = (2 * (ring32 - 1) + 1) * (2 * (ring32 - 1) + 1) := by
      dsimp only [ringMin]; rw [← hringU]; rfl
    have hMaxU : ringMax.toUInt32 = (2 * ring32 + 1) * (2 * ring32 + 1) := by
      dsimp only [ringMax]; rw [← hringU]; rfl
    have hQU : ringQ.toUInt32 =
        { toBitVec := (ringMax.toUInt32 - ringMin.toUInt32).toBitVec.sdiv 4#32 } := by
      dsimp only [ringQ]; rw [← u32_sub]; rfl
    have hQ1U : ringQ1.toUInt32 = ringMin.toUInt32 + ringQ.toUInt32 := rfl
    have hQ2U : ringQ2.toUInt32 = ringQ1.toUInt32 + ringQ.toUInt32 := rfl
    have hQ3U : ringQ3.toUInt32 = ringQ2.toUInt32 + ringQ.toUInt32 := rfl
    have hChkU : ringMax.toUInt32 = ringQ3.toUInt32 + ringQ.toUInt32 := by
      rw [← u32_add, ← hchk]
    have hringDef :
        (if (if x.toUInt32.toBitVec.slt 0#32 then -x.toUInt32 else x.toUInt32).toBitVec.slt
            (if y.toUInt32.toBitVec.slt 0#32 then -y.toUInt32 else y.toUInt32).toBitVec then
          if y.toUInt32.toBitVec.slt 0#32 then -y.toUInt32 else y.toUInt32
        else if x.toUInt32.toBitVec.slt 0#32 then -x.toUInt32 else x.toUInt32) = ring32 := rfl
    have h1nz : ((1 : UInt32) == 0) = false := rfl
    apply hold_subst (P := fun z => ∃ st', z = some (JvmVal.i32 idx.toUInt32, st'))
    · geom_step_chunk
      rw [step_getCompanionZero geomHooks rfl hs, step_getZeroVal, step_intOffsetEq0]
      simp only [hpB, Bool.false_eq_true, ↓reduceIte]
      rw [Jvm.runJvmResFast_at_branch_cons _ (hbr := rfl), Jvm.evalResBranchInstrCons_ifeq]
      simp only [show ((0 : UInt32) == 0) = true from rfl, ↓reduceIte]
      geom_step_chunk
      rw [step_intOffsetGetX, step_mathAbs]
      geom_step_chunk
      rw [step_intOffsetGetY, step_mathAbs, step_mathMax]
      geom_step_chunk
      rw [step_idiv4]
      geom_step_chunk
      simp only [unpackIntOffsetX_eq, unpackIntOffsetY_eq, hxPack, hyPack]
      rw [hringDef]
      rw [Jvm.runJvmResFast_at_branch_cons _ (hbr := rfl), Jvm.evalResBranchInstrCons_if_icmpne]
      rw [← hMaxU, ← hMinU, ← hQU, ← hQ1U, ← hQ2U, ← hQ3U, ← hChkU]
      simp only [beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      geom_step_chunk
      rw [Jvm.runJvmResFast_at_branch_cons _ (hbr := rfl), Jvm.evalResBranchInstrCons_goto]
      geom_norm_run_args
      rw [Jvm.runJvmResFast_at_branch_cons _ (hbr := rfl), Jvm.evalResBranchInstrCons_ifne]
      simp only [h1nz, Bool.not_false, ↓reduceIte]
      geom_step_chunk
      rw [step_intOffsetGetY]
      simp only [unpackIntOffsetY_eq, hyPack]
      geom_step_chunk
      rw [Jvm.runJvmResFast_at_branch_cons _ (hbr := rfl), Jvm.evalResBranchInstrCons_if_icmpne]
      rw [← hringU, ← u32_neg, beq_int32_toUInt32]
      unfold hold
      rfl
    by_cases hyNeg : y = -ring
    · have hb : (y == -ring) = true := beq_iff_eq.mpr hyNeg
      simp only [hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hmod ⊢
      injection hmod with hidx
      rw [← hidx]
      refine ⟨?_, ?_⟩; swap
      geom_step_chunk
      rw [step_intOffsetGetX]
      simp only [unpackIntOffsetX_eq, hxPack]
      geom_step_chunk
      rw [Jvm.runJvmResFast_at_branch_cons _ (hbr := rfl), Jvm.evalResBranchInstrCons_goto]
      geom_norm_run_args
      rw [step_ireturn]; simp only [u32_add]; rfl
    · have hb : (y == -ring) = false := beq_false_of_ne hyNeg
      simp only [hb, Bool.not_false, Bool.false_eq_true, ↓reduceIte] at hmod ⊢
      apply hold_subst (P := fun z => ∃ st', z = some (JvmVal.i32 idx.toUInt32, st'))
      · geom_step_chunk
        rw [step_intOffsetGetX]
        simp only [unpackIntOffsetX_eq, hxPack]
        geom_step_chunk
        rw [Jvm.runJvmResFast_at_branch_cons _ (hbr := rfl), Jvm.evalResBranchInstrCons_if_icmpne]
        rw [beq_int32_toUInt32]
        unfold hold
        rfl
      by_cases hxPos : x = ring
      · have hb2 : (x == ring) = true := beq_iff_eq.mpr hxPos
        simp only [hb2, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hmod ⊢
        injection hmod with hidx
        rw [← hidx]
        refine ⟨?_, ?_⟩; swap
        geom_step_chunk
        rw [step_intOffsetGetY]
        simp only [unpackIntOffsetY_eq, hyPack]
        geom_step_chunk
        rw [Jvm.runJvmResFast_at_branch_cons _ (hbr := rfl), Jvm.evalResBranchInstrCons_goto]
        geom_norm_run_args
        rw [step_ireturn]; simp only [u32_add]; rfl
      · have hb2 : (x == ring) = false := beq_false_of_ne hxPos
        simp only [hb2, Bool.not_false, Bool.false_eq_true, ↓reduceIte] at hmod ⊢
        apply hold_subst (P := fun z => ∃ st', z = some (JvmVal.i32 idx.toUInt32, st'))
        · geom_step_chunk
          rw [step_intOffsetGetY]
          simp only [unpackIntOffsetY_eq, hyPack]
          geom_step_chunk
          rw [Jvm.runJvmResFast_at_branch_cons _ (hbr := rfl), Jvm.evalResBranchInstrCons_if_icmpne]
          rw [beq_int32_toUInt32]
          unfold hold
          rfl
        by_cases hyPos : y = ring
        · have hb3 : (y == ring) = true := beq_iff_eq.mpr hyPos
          simp only [hb3, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hmod ⊢
          injection hmod with hidx
          rw [← hidx]
          refine ⟨?_, ?_⟩; swap
          geom_step_chunk
          rw [step_intOffsetGetX]
          simp only [unpackIntOffsetX_eq, hxPack]
          geom_step_chunk
          rw [Jvm.runJvmResFast_at_branch_cons _ (hbr := rfl), Jvm.evalResBranchInstrCons_goto]
          geom_norm_run_args
          rw [step_ireturn]; simp only [u32_add, u32_sub]; rfl
        · have hb3 : (y == ring) = false := beq_false_of_ne hyPos
          simp only [hb3, Bool.not_false, Bool.false_eq_true, ↓reduceIte] at hmod ⊢
          have hxNeg : x = -ring := by
            by_contra hnx
            have hbx := beq_false_of_ne hnx
            simp only [hbx, Bool.false_eq_true, ↓reduceIte] at hmod
            cases hmod
          have hb4 : (x == -ring) = true := beq_iff_eq.mpr hxNeg
          simp only [hb4, ↓reduceIte] at hmod
          injection hmod with hidx
          rw [← hidx]
          refine ⟨?_, ?_⟩; swap
          geom_step_chunk
          rw [step_intOffsetGetX]
          simp only [unpackIntOffsetX_eq, hxPack]
          geom_step_chunk
          rw [Jvm.runJvmResFast_at_branch_cons _ (hbr := rfl), Jvm.evalResBranchInstrCons_if_icmpne]
          rw [← u32_neg, beq_int32_toUInt32, hb4]
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          geom_step_chunk
          rw [Jvm.runJvmResFast_at_branch_cons _ (hbr := rfl), Jvm.evalResBranchInstrCons_goto]
          geom_norm_run_args
          rw [Jvm.runJvmResFast_at_branch_cons _ (hbr := rfl), Jvm.evalResBranchInstrCons_ifne]
          simp only [h1nz, Bool.not_false, ↓reduceIte]
          geom_step_chunk
          rw [step_intOffsetGetY]
          simp only [unpackIntOffsetY_eq, hyPack]
          geom_step_chunk
          rw [step_ireturn]; simp only [u32_add, u32_sub]; rfl

/-- Zero origin short-circuit of `OffsetExtensionsKt.toRingOffset`. -/
theorem toRingOffset_zero_equiv (jh : Jvm.JvmHeap Empty := {})
    (hs : jh.getStatic? "androidx/compose/ui/unit/IntOffset" "Companion" = none := by rfl) :
    runJvm 15 OffsetExtensionsKt_toRingOffset_prog (initJvmState [(0, .i32 0)] jh) = some (.i64 0) := by
  have hfast :
      ∃ st', Jvm.runJvmResFast geomHooks 15 OffsetExtensionsKt_toRingOffset_prog 0 OffsetExtensionsKt_toRingOffset_prog
        (initJvmState [(0, .i32 0)] jh) = some (.i64 0, st') := by
    refine ⟨?_, ?_⟩; swap
    geom_step_chunk
    rw [Jvm.runJvmResFast_at_branch_cons _ (hbr := rfl), Jvm.evalResBranchInstrCons_ifne]
    simp only [beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [step_getCompanionZero geomHooks rfl hs, step_getZeroVal]
    rw [Jvm.runJvmResFast.eq_def]
    rfl
  rcases hfast with ⟨st', hfast⟩
  dsimp only [runJvm]
  rw [Jvm.runJvm_eq_runJvmRes geomHooks geomHooks_iteZero? geomHooks_iteNonZero?,
    Jvm.runJvmRes_of_runJvmResFast0 geomHooks 15 OffsetExtensionsKt_toRingOffset_prog _ _ rfl hfast]
  rfl

end Geometry.KotlinJvmVerification
