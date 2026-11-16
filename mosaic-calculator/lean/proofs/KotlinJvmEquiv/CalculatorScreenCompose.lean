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

import proofs.KotlinJvmEquiv.CalculatorEngineScreenHelpers

namespace MosaicCalculator.KotlinJvmVerification

open MosaicCalculator.JvmVerification
open MosaicCalculator.KotlinJvmBytecode
open MosaicCalculator.Model

private instance instHasDefaultIsZeroScreen (r : String → Option (List JvmInstr)) (d f : Nat) :
    Jvm.HasDefaultIsZero (mkCalcHooks r d f) where
  isZero?_eq := by cases d <;> rfl

local elab "unfold_screen_priv" : tactic =>
  Lean.Elab.Tactic.liftMetaTactic fun g => do
    let tgt ← g.getType
    let tgt' ← Lean.Meta.transform tgt fun e => do
      if let .const n _ := e.getAppFn then
        let s := n.toString
        if s.endsWith "isVoidStaticTarget" || s.endsWith "normalizeCalcClass" ||
           s.endsWith "singletonLambdaFnTag?" then
          if let some e' ← Lean.Meta.unfoldDefinition? e then
            return .done (← Lean.Meta.whnf e')
      return .continue
    return [← g.replaceTargetDefEq tgt']

local elab "unfold_locals_priv" : tactic =>
  Lean.Elab.Tactic.liftMetaTactic fun g => do
    let tgt ← g.getType
    let tgt' ← Lean.Meta.transform tgt fun e => do
      if let .const n _ := e.getAppFn then
        let s := n.toString
        if s.contains "assignParamLocalsAux" || s.contains "assignLinearLocals" then
          let args := e.getAppArgs
          if let some lastArg := args.back? then
            let lastWhnf ← Lean.Meta.whnf lastArg
            if lastWhnf.isAppOf ``List.nil || lastWhnf.isAppOf ``List.cons then
              if let some e' ← Lean.Meta.unfoldDefinition? e then
                return .visit (← Lean.Meta.whnf e')
        else if s.contains "upsertGroup" || s.contains "findGroup?" ||
                s.contains "updateGroup" || s.contains "listSetAt" then
          if s.endsWith ".match_1" then
            if let some e' ← Lean.Meta.unfoldDefinition? e then
              return .visit e'
          else
            let args := e.getAppArgs
            if args.any (fun a => a.isAppOf ``List.nil || a.isAppOf ``List.cons) then
              if let some e' ← Lean.Meta.unfoldDefinition? e then
                return .visit e'
      return .continue
    return [← g.replaceTargetDefEq tgt']

/-! ### Screen-Local Fast Execution Lemmas -/

private theorem runFast_ireturn (r : String → Option (List JvmInstr)) (d subFuel f pc pc0 : Nat)
    {prog rest : List JvmInstr} {v : JvmVal} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks r d subFuel) (f + 1) prog pc (.ireturn :: rest)
        ⟨pc0, v :: stk, locs, jh, hp⟩ =
      some (v, ⟨pc, v :: stk, locs, jh, hp⟩) := by
  rw [Jvm.runJvmResFast_step_nonbranch (mkCalcHooks r d subFuel) f prog pc .ireturn rest
    ⟨pc0, v :: stk, locs, jh, hp⟩ rfl (by simp)]
  cases d <;> rfl

private theorem runFast_areturn' {hooks : Jvm.JvmHooks CalcExt CalcHeap} {f pc pc0 : Nat}
    {prog rest : List JvmInstr} {v : JvmVal} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.areturn :: rest) ⟨pc0, v :: stk, locs, jh, hp⟩ =
      some (v, ⟨pc, v :: stk, locs, jh, hp⟩) := by
  rw [Jvm.runJvmResFast_step_nonbranch hooks f prog pc .areturn rest
    ⟨pc0, v :: stk, locs, jh, hp⟩ rfl (by simp)]
  rfl

private theorem runFast_goto' {hooks : Jvm.JvmHooks CalcExt CalcHeap} {f pc pc0 target : Nat}
    {prog rest : List JvmInstr} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.goto target :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog target (prog.drop target) ⟨target, stk, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  rfl

private theorem runFast_ifnull_branch' {hooks : Jvm.JvmHooks CalcExt CalcHeap}
    {f pc pc0 target : Nat} {prog rest : List JvmInstr} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.ifnull target :: rest) ⟨pc0, .null :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog target (prog.drop target) ⟨target, stk, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch, Jvm.JvmVal.isNull]

private theorem runFast_ifnull_fallthrough' {hooks : Jvm.JvmHooks CalcExt CalcHeap}
    {f pc pc0 target : Nat} {prog rest : List JvmInstr} {v : JvmVal} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} (hnn : v.isNull = false) :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.ifnull target :: rest) ⟨pc0, v :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest ⟨pc + 1, stk, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch, hnn]

private theorem runFast_ifeq_zero [Jvm.HasDefaultIsZero hooks]
    {f pc pc0 target : Nat} {prog rest : List JvmInstr} {v : UInt32} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap}
    (hz : v = 0 := by decide) :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.ifeq target :: rest) ⟨pc0, .i32 v :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog target (prog.drop target) ⟨target, stk, locs, jh, hp⟩ := by
  subst hz
  rw [Jvm.runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch,
    Jvm.HasDefaultIsZero.isZero?_eq (hooks := hooks)]

private theorem runFast_ifeq_nonzero [Jvm.HasDefaultIsZero hooks]
    {f pc pc0 target : Nat} {prog rest : List JvmInstr} {v : UInt32} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} (hnz : v ≠ 0) :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.ifeq target :: rest) ⟨pc0, .i32 v :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest ⟨pc + 1, stk, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch,
    Jvm.HasDefaultIsZero.isZero?_eq (hooks := hooks), hnz]

private theorem runFast_if_icmpeq_ne {hooks : Jvm.JvmHooks CalcExt CalcHeap}
    {f pc pc0 target : Nat} {prog rest : List JvmInstr} {a b : UInt32} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} (hne : a ≠ b) :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.if_icmpeq target :: rest)
        ⟨pc0, .i32 b :: .i32 a :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest ⟨pc + 1, stk, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch, hne]

private theorem runFast_checkNotNull' (d subFuel f pc pc0 : Nat)
    {prog rest : List JvmInstr} {param : String} {v : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap}
    (hnn : v.isNull = false) :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) (f + 1) prog pc
        (.invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter"
          "(Ljava/lang/Object;Ljava/lang/String;)V" :: rest)
        ⟨pc0, .str param :: v :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, stk, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkCalcHooks calcProgLookup (d + 1) subFuel)
      (.invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter"
        "(Ljava/lang/Object;Ljava/lang/String;)V")
      ⟨pc, .str param :: v :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, stk, locs, jh, hp⟩) := by
    dsimp only [Jvm.stepInstr, Jvm.stepInvokeStaticGeneric]
    simp [hnn]
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks calcProgLookup (d + 1) subFuel) rfl (by simp) hs rfl

private theorem runFast_getKey (d subFuel f pc pc0 : Nat)
    {prog rest : List JvmInstr} {k : String}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) (f + 1) prog pc
        (.invokevirtual "com/jakewharton/mosaic/layout/KeyEvent" "getKey" "()Ljava/lang/String;" :: rest)
        ⟨pc0, .ext (.keyEvent k) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .str k :: stk, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkCalcHooks calcProgLookup (d + 1) subFuel)
      (.invokevirtual "com/jakewharton/mosaic/layout/KeyEvent" "getKey" "()Ljava/lang/String;")
      ⟨pc, .ext (.keyEvent k) :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .str k :: stk, locs, jh, hp⟩) := rfl
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks calcProgLookup (d + 1) subFuel) rfl (by simp) hs rfl

private theorem runFast_sourceInfo' (d subFuel f pc pc0 : Nat)
    {prog rest : List JvmInstr} {info : String}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) (f + 1) prog pc
        (.invokestatic "androidx/compose/runtime/ComposerKt" "sourceInformation"
          "(Landroidx/compose/runtime/Composer;Ljava/lang/String;)V" :: rest)
        ⟨pc0, .str info :: .ext .composer :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, stk, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkCalcHooks calcProgLookup (d + 1) subFuel)
      (.invokestatic "androidx/compose/runtime/ComposerKt" "sourceInformation"
        "(Landroidx/compose/runtime/Composer;Ljava/lang/String;)V")
      ⟨pc, .str info :: .ext .composer :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, stk, locs, jh, hp⟩) := rfl
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks calcProgLookup (d + 1) subFuel) rfl (by simp) hs rfl

private theorem runFast_shouldExecute' (d subFuel f pc pc0 : Nat)
    {prog rest : List JvmInstr} {p flags : UInt32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    let res := Compose.shouldExecute hp.composer (p != 0) flags.toInt32
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) (f + 1) prog pc
        (.invokeinterface "androidx/compose/runtime/Composer" "shouldExecute" "(ZI)Z" :: rest)
        ⟨pc0, .i32 flags :: .i32 p :: .ext .composer :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .i32 (if res then 1 else 0) :: stk, locs, jh, hp⟩ := by
  intro res
  have hs : Jvm.stepInstr (mkCalcHooks calcProgLookup (d + 1) subFuel)
      (.invokeinterface "androidx/compose/runtime/Composer" "shouldExecute" "(ZI)Z")
      ⟨pc, .i32 flags :: .i32 p :: .ext .composer :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 (if res then 1 else 0) :: stk, locs, jh, hp⟩) := rfl
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks calcProgLookup (d + 1) subFuel) rfl (by simp) hs rfl

private theorem runFast_isTraceInProgress' (d subFuel f pc pc0 : Nat)
    {prog rest : List JvmInstr} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} (ht : hp.composer.traceEnabled = false) :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) (f + 1) prog pc
        (.invokestatic "androidx/compose/runtime/ComposerKt" "isTraceInProgress" "()Z" :: rest)
        ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .i32 0 :: stk, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkCalcHooks calcProgLookup (d + 1) subFuel)
      (.invokestatic "androidx/compose/runtime/ComposerKt" "isTraceInProgress" "()Z")
      ⟨pc, stk, locs, jh, hp⟩ = .inl (some ⟨pc + 1, .i32 0 :: stk, locs, jh, hp⟩) := by
    dsimp only [Jvm.stepInstr, Jvm.stepInvokeStaticGeneric, mkCalcHooks]
    rw [ht]
    rfl
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks calcProgLookup (d + 1) subFuel) rfl (by simp) hs rfl

private theorem runFast_text' (d subFuel f pc pc0 : Nat)
    {prog rest : List JvmInstr} {txt : String}
    {modV a2 a3 a4 a5 a6 chV dfltV : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) (f + 1) prog pc
        (.invokestatic "com/jakewharton/mosaic/ui/Text" "Text-cbmis8g"
          "(Ljava/lang/String;Lcom/jakewharton/mosaic/modifier/Modifier;IIIIILandroidx/compose/runtime/Composer;II)V" :: rest)
        ⟨pc0, dfltV :: chV :: .ext .composer :: a6 :: a5 :: a4 :: a3 :: a2 :: modV :: .str txt :: stk,
          locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, stk, locs, jh, emitMosaicNode hp (.text txt)⟩ := by
  have hs : Jvm.stepInstr (mkCalcHooks calcProgLookup (d + 1) subFuel)
      (.invokestatic "com/jakewharton/mosaic/ui/Text" "Text-cbmis8g"
        "(Ljava/lang/String;Lcom/jakewharton/mosaic/modifier/Modifier;IIIIILandroidx/compose/runtime/Composer;II)V")
      ⟨pc, dfltV :: chV :: .ext .composer :: a6 :: a5 :: a4 :: a3 :: a2 :: modV :: .str txt :: stk,
        locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, stk, locs, jh, emitMosaicNode hp (.text txt)⟩) := rfl
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks calcProgLookup (d + 1) subFuel) rfl (by simp) hs rfl

private theorem runFast_makeConcat_gt' (d subFuel f pc pc0 : Nat)
    {prog rest : List JvmInstr} {line : String}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) (f + 1) prog pc
        (.invokedynamic "makeConcatWithConstants" "> \x01" "(Ljava/lang/String;)Ljava/lang/String;" :: rest)
        ⟨pc0, .str line :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .str ("> " ++ line) :: stk, locs, jh, hp⟩ := by
  have hcat : Jvm.evalMakeConcatWithConstants "> \x01" "(Ljava/lang/String;)Ljava/lang/String;"
      (.str line :: stk) = some (">" ++ (" " ++ (line ++ "")), stk) := by
    dsimp only [Jvm.evalMakeConcatWithConstants]
    have hm1 : Jvm.parseMethodParamTags "(Ljava/lang/String;)Ljava/lang/String;" = ['L'] := by decide
    have hm2 : String.toList "> \x01" = ['>', ' ', '\x01'] := by decide
    rw [hm1, hm2]
    dsimp only [List.length]
    split
    · omega
    · rfl
  have hcat' : Jvm.evalMakeConcatWithConstants "> \x01" "(Ljava/lang/String;)Ljava/lang/String;"
      (.str line :: stk) = some ("> " ++ line, stk) := by
    rw [hcat]
    simp only [String.append_empty, ← String.append_assoc]
    rfl
  have hs : Jvm.stepInstr (mkCalcHooks calcProgLookup (d + 1) subFuel)
      (.invokedynamic "makeConcatWithConstants" "> \x01" "(Ljava/lang/String;)Ljava/lang/String;")
      ⟨pc, .str line :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .str ("> " ++ line) :: stk, locs, jh, hp⟩) := by
    dsimp only [Jvm.stepInstr]
    have hm : ("makeConcatWithConstants" == "makeConcatWithConstants") = true := rfl
    change (if ("makeConcatWithConstants" == "makeConcatWithConstants") = true then
      match Jvm.evalMakeConcatWithConstants "> \x01" "(Ljava/lang/String;)Ljava/lang/String;"
          (.str line :: stk) with
      | some (s, rest) =>
        Sum.inl (some (Jvm.JvmState.mk (pc + 1) (.str s :: rest) locs jh hp : JvmState))
      | none => Sum.inr none
      else _) = _
    rw [hm, hcat']
    simp only [↓reduceIte]
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks calcProgLookup (d + 1) subFuel) rfl (by simp) hs rfl

private theorem runFast_getStatic_unit' (d subFuel f pc pc0 : Nat)
    {prog rest : List JvmInstr} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap}
    (hclean : jh.getStatic? "kotlin/Unit" "INSTANCE" = none) :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) (f + 1) prog pc
        (.getstatic "kotlin/Unit" "INSTANCE" "Lkotlin/Unit;" :: rest)
        ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext .unit :: stk, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkCalcHooks calcProgLookup (d + 1) subFuel)
      (.getstatic "kotlin/Unit" "INSTANCE" "Lkotlin/Unit;") ⟨pc, stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .ext .unit :: stk, locs, jh, hp⟩) := by
    dsimp only [Jvm.stepInstr]
    rw [hclean]
    rfl
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks calcProgLookup (d + 1) subFuel) rfl (by simp) hs rfl

private theorem runFast_getStatic_singletonInst (d subFuel f pc pc0 : Nat)
    {prog rest : List JvmInstr} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap}
    (hclean : jh.getStatic?
        "com/alexvanyo/composelife/mosaiccalculator/ComposableSingletons$CalculatorScreenKt"
        "INSTANCE" = none) :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) (f + 1) prog pc
        (.getstatic
          "com/alexvanyo/composelife/mosaiccalculator/ComposableSingletons$CalculatorScreenKt"
          "INSTANCE"
          "Lcom/alexvanyo/composelife/mosaiccalculator/ComposableSingletons$CalculatorScreenKt;" :: rest)
        ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.companion "ComposableSingletons$CalculatorScreenKt") :: stk, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkCalcHooks calcProgLookup (d + 1) subFuel)
      (.getstatic
        "com/alexvanyo/composelife/mosaiccalculator/ComposableSingletons$CalculatorScreenKt"
        "INSTANCE"
        "Lcom/alexvanyo/composelife/mosaiccalculator/ComposableSingletons$CalculatorScreenKt;")
      ⟨pc, stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .ext (.companion "ComposableSingletons$CalculatorScreenKt") :: stk, locs, jh, hp⟩) := by
    dsimp only [Jvm.stepInstr]
    rw [hclean]
    rfl
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks calcProgLookup (d + 1) subFuel) rfl (by simp) hs rfl

private theorem runFast_getLambda_step (d subFuel f pc : Nat)
    {prog rest : List JvmInstr} {method fld : String} {cid : Nat}
    {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap}
    (hsuf : 2 ≤ subFuel)
    (hStat : jh.getStatic? "ComposableSingletons$CalculatorScreenKt" fld = some (.ext (.closureRef cid)))
    (hTag : calcProgLookup ("ComposableSingletons$CalculatorScreenKt." ++ method) = some [
      .getstatic "ComposableSingletons$CalculatorScreenKt" fld "Lkotlin/jvm/functions/Function3;",
      .areturn]) :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) (f + 1) prog pc
        (.invokevirtual
          "com/alexvanyo/composelife/mosaiccalculator/ComposableSingletons$CalculatorScreenKt"
          method "()Lkotlin/jvm/functions/Function3;" :: rest)
        ⟨pc, .ext (.companion "ComposableSingletons$CalculatorScreenKt") :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.closureRef cid) :: stk, locs, jh, hp⟩ := by
  obtain ⟨sf, rfl⟩ := Nat.exists_eq_add_of_le' hsuf
  have hsub : Jvm.runJvmRes (mkCalcHooks calcProgLookup d (sf + 2)) (sf + 2)
      [.getstatic "ComposableSingletons$CalculatorScreenKt" fld "Lkotlin/jvm/functions/Function3;",
       .areturn]
      ⟨0, [], fun _ => .i32 0, jh, hp⟩ =
        some (.ext (.closureRef cid), ⟨1, [.ext (.closureRef cid)], fun _ => .i32 0, jh, hp⟩) := by
    apply Jvm.runJvmRes_of_runJvmResFast0 _ _ _ _ _ rfl
    rw [Jvm.runJvmResFast_step_nonbranch (mkCalcHooks calcProgLookup d (sf + 2)) (sf + 1) _ 0
      (.getstatic _ _ _) [.areturn] ⟨0, [], fun _ => .i32 0, jh, hp⟩ rfl (by simp)]
    have hs0 : Jvm.stepInstr (mkCalcHooks calcProgLookup d (sf + 2))
        (.getstatic "ComposableSingletons$CalculatorScreenKt" fld "Lkotlin/jvm/functions/Function3;")
        ⟨0, [], fun _ => .i32 0, jh, hp⟩ =
        .inl (some ⟨1, [.ext (.closureRef cid)], fun _ => .i32 0, jh, hp⟩) := by
      dsimp only [Jvm.stepInstr]
      rw [hStat]
    rw [hs0]
    dsimp only
    rw [ite_eq_left rfl]
    rw [runFast_areturn']
  have hs : Jvm.stepInstr (mkCalcHooks calcProgLookup (d + 1) (sf + 2))
      (.invokevirtual
        "com/alexvanyo/composelife/mosaiccalculator/ComposableSingletons$CalculatorScreenKt"
        method "()Lkotlin/jvm/functions/Function3;")
      ⟨pc, .ext (.companion "ComposableSingletons$CalculatorScreenKt") :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .ext (.closureRef cid) :: stk, locs, jh, hp⟩) := by
    change (mkCalcHooks calcProgLookup (d + 1) (sf + 2)).stepInvokeVirtual _ _ _ _ = _
    dsimp only [mkCalcHooks]
    unfold_screen_priv
    conv => lhs; whnf
    rw [hTag]
    dsimp only
    rw [show Jvm.parseMethodParamTags "()Lkotlin/jvm/functions/Function3;" = [] from by decide]
    unfold_locals_priv
    dsimp only [List.foldl]
    rw [hsub]
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks calcProgLookup (d + 1) (sf + 2))
    rfl (by simp) hs rfl

private theorem runFast_row_text (d subFuel f pc cid : Nat)
    {prog rest : List JvmInstr} {fnTag rowText : String}
    {arrV alignV chV dfltV : JvmVal} {prevChildren : List Mosaic.MosaicNode} {prevH? : Option Nat}
    {parents : List (List Mosaic.MosaicNode × Option Nat)}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap}
    (hnode : hp.nodeStack = (prevChildren, prevH?) :: parents)
    (hclos : hp.closures[cid]? = some (fnTag, []))
    (hbody : ∃ bodyProg endSt,
      calcProgLookup fnTag = some bodyProg ∧
      Jvm.runJvmRes (mkCalcHooks calcProgLookup d subFuel) subFuel bodyProg
          (initCalcJvmState [(0, .ext .unit), (1, .ext .composer), (2, .i32 6)]
            { hp with nodeStack := ([], none) :: hp.nodeStack } jh) =
        some (.ext .unit, endSt) ∧
      endSt.jvmHeap = jh ∧
      endSt.heap = emitMosaicNode { hp with nodeStack := ([], none) :: hp.nodeStack } (.text rowText)) :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) (f + 1) prog pc
        (.invokestatic "com/jakewharton/mosaic/ui/Row" "Row"
          "(Lcom/jakewharton/mosaic/modifier/Modifier;Lcom/jakewharton/mosaic/ui/Arrangement$Horizontal;Lcom/jakewharton/mosaic/ui/Alignment$Vertical;Lkotlin/jvm/functions/Function3;Landroidx/compose/runtime/Composer;II)V" :: rest)
        ⟨pc, dfltV :: chV :: .ext .composer :: .ext (.closureRef cid) :: alignV :: arrV :: .null :: stk,
          locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, stk, locs, jh,
          { hp with nodeStack := (prevChildren ++ [.row [.text rowText] none], prevH?) :: parents }⟩ := by
  obtain ⟨bodyProg, endSt, hprog, hrun, hjh', hhp'⟩ := hbody
  have hstep : (mkCalcHooks calcProgLookup (d + 1) subFuel).stepInvokeStatic
      ⟨pc, dfltV :: chV :: .ext .composer :: .ext (.closureRef cid) :: alignV :: arrV :: .null :: stk,
        locs, jh, hp⟩
      "com/jakewharton/mosaic/ui/Row" "Row"
      "(Lcom/jakewharton/mosaic/modifier/Modifier;Lcom/jakewharton/mosaic/ui/Arrangement$Horizontal;Lcom/jakewharton/mosaic/ui/Alignment$Vertical;Lkotlin/jvm/functions/Function3;Landroidx/compose/runtime/Composer;II)V" =
      .inl (some ⟨pc + 1, stk, locs, jh,
        { hp with nodeStack := (prevChildren ++ [.row [.text rowText] none], prevH?) :: parents }⟩) := by
    conv => lhs; whnf
    dsimp only
    rw [hclos]
    dsimp only
    rw [hprog]
    dsimp only [List.append_nil]
    unfold_locals_priv
    dsimp only [initCalcJvmState, Jvm.initJvmState, List.foldl] at hrun ⊢
    rw [hrun]
    dsimp only
    rw [hhp', hjh']
    dsimp only [emitMosaicNode]
    rw [hnode]
    rfl
  have hs : Jvm.stepInstr (mkCalcHooks calcProgLookup (d + 1) subFuel)
      (.invokestatic "com/jakewharton/mosaic/ui/Row" "Row"
        "(Lcom/jakewharton/mosaic/modifier/Modifier;Lcom/jakewharton/mosaic/ui/Arrangement$Horizontal;Lcom/jakewharton/mosaic/ui/Alignment$Vertical;Lkotlin/jvm/functions/Function3;Landroidx/compose/runtime/Composer;II)V")
      ⟨pc, dfltV :: chV :: .ext .composer :: .ext (.closureRef cid) :: alignV :: arrV :: .null :: stk,
        locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, stk, locs, jh,
        { hp with nodeStack := (prevChildren ++ [.row [.text rowText] none], prevH?) :: parents }⟩) := by
    dsimp only [Jvm.stepInstr, Jvm.stepInvokeStaticGeneric]
    exact hstep
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks calcProgLookup (d + 1) subFuel)
    rfl (by simp) hs rfl

private theorem runFast_formatDisplayLine (d subFuel f pc : Nat)
    {prog rest : List JvmInstr} {cSt : CalculatorState}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap}
    (hsuf : 35 ≤ subFuel)
    (herrSwitch : ∃ errAddr,
      jh.getStatic? "com/alexvanyo/composelife/mosaiccalculator/CalculatorEngineKt$WhenMappings"
        "$EnumSwitchMapping$1" = some (.heapRef errAddr) ∧
      jh.get? errAddr = some (.intArray #[1, 2])) :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 2) subFuel) (f + 1) prog pc
        (.invokestatic "com/alexvanyo/composelife/mosaiccalculator/CalculatorEngineKt"
          "formatDisplayLine"
          "(Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorState;)Ljava/lang/String;" :: rest)
        ⟨pc, .ext (.calcState cSt) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 2) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .str (formatDisplayLineModel cSt) :: stk, locs, jh, hp⟩ := by
  have heq := formatDisplayLine_equiv calcProgLookup (d + 1) subFuel subFuel (by omega) hsuf
    cSt hp jh herrSwitch
  obtain ⟨endSt, hrun, hjh', hhp'⟩ := heq
  have hstep : (mkCalcHooks calcProgLookup (d + 2) subFuel).stepInvokeStatic
      ⟨pc, .ext (.calcState cSt) :: stk, locs, jh, hp⟩
      "com/alexvanyo/composelife/mosaiccalculator/CalculatorEngineKt"
      "formatDisplayLine"
      "(Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorState;)Ljava/lang/String;" =
      .inl (some ⟨pc + 1, .str (formatDisplayLineModel cSt) :: stk, locs, jh, hp⟩) := by
    conv => lhs; whnf
    unfold_screen_priv
    dsimp only
    rw [show "CalculatorEngineKt" ++ "." ++ "formatDisplayLine" = "CalculatorEngineKt.formatDisplayLine"
      from by apply String.ext; simp]
    rw [show Jvm.parseMethodParamTags
        "(Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorState;)Ljava/lang/String;" =
        ['L'] from by decide]
    dsimp only [List.length]
    cases (stk.length + 1).decLt 1 with
    | isTrue h => omega
    | isFalse _ =>
      dsimp only [List.take, List.drop, List.reverse, List.reverseAux]
      unfold_locals_priv
      rw [show calcProgLookup "CalculatorEngineKt.formatDisplayLine" = some formatDisplayLine_prog from rfl]
      dsimp only [initCalcJvmState, Jvm.initJvmState, List.foldl] at hrun ⊢
      rw [hrun]
      dsimp only
      rw [hjh', hhp']
      rfl
  have hs : Jvm.stepInstr (mkCalcHooks calcProgLookup (d + 2) subFuel)
      (.invokestatic "com/alexvanyo/composelife/mosaiccalculator/CalculatorEngineKt"
        "formatDisplayLine"
        "(Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorState;)Ljava/lang/String;")
      ⟨pc, .ext (.calcState cSt) :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .str (formatDisplayLineModel cSt) :: stk, locs, jh, hp⟩) := by
    dsimp only [Jvm.stepInstr, Jvm.stepInvokeStaticGeneric]
    exact hstep
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks calcProgLookup (d + 2) subFuel)
    rfl (by simp) hs rfl

private theorem runFast_function1Invoke (d subFuel f pc : Nat)
    {prog rest : List JvmInstr} {cid : Nat} {arg res : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh jh' : Jvm.JvmHeap CalcExt} {hp hp' : CalcHeap}
    (fnTag : String) (caps? : Option JvmVal) (bodyProg : List JvmInstr)
    (hclos : hp.closures[cid]? = some (fnTag, caps?.toList))
    (hlookup : calcProgLookup fnTag = some bodyProg)
    (hrun : ∃ endSt,
      Jvm.runJvmRes (mkCalcHooks calcProgLookup d subFuel) subFuel bodyProg
          (initCalcJvmState
            (match caps? with | none => [(0, arg)] | some c => [(0, c), (1, arg)])
            hp jh) =
        some (res, endSt) ∧
      endSt.jvmHeap = jh' ∧ endSt.heap = hp') :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) (f + 1) prog pc
        (.invokeinterface "kotlin/jvm/functions/Function1" "invoke"
          "(Ljava/lang/Object;)Ljava/lang/Object;" :: rest)
        ⟨pc, arg :: .ext (.closureRef cid) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, res :: stk, locs, jh', hp'⟩ := by
  obtain ⟨endSt, hexec, hjh', hhp'⟩ := hrun
  have hs : Jvm.stepInstr (mkCalcHooks calcProgLookup (d + 1) subFuel)
      (.invokeinterface "kotlin/jvm/functions/Function1" "invoke"
        "(Ljava/lang/Object;)Ljava/lang/Object;")
      ⟨pc, arg :: .ext (.closureRef cid) :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, res :: stk, locs, jh', hp'⟩) := by
    change (mkCalcHooks calcProgLookup (d + 1) subFuel).stepInvokeInterface _ _ _ _ = _
    conv => lhs; whnf
    dsimp only
    rw [hclos]
    cases caps? with
    | none =>
      dsimp only [Option.toList]
      rw [hlookup]
      dsimp only [List.nil_append]
      unfold_locals_priv
      dsimp only [initCalcJvmState, Jvm.initJvmState, List.foldl] at hexec ⊢
      rw [hexec]
      dsimp only
      rw [hjh', hhp']
    | some c =>
      dsimp only [Option.toList]
      rw [hlookup]
      dsimp only [List.cons_append, List.nil_append]
      unfold_locals_priv
      dsimp only [initCalcJvmState, Jvm.initJvmState, List.foldl] at hexec ⊢
      rw [hexec]
      dsimp only
      rw [hjh', hhp']
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks calcProgLookup (d + 1) subFuel)
    rfl (by simp) hs rfl

/-- Bytecode equivalence theorem for `CalculatorScreenKt.CalculatorScreen$lambda$0$0`. -/
theorem CalculatorScreen_lambda_0_0_equiv (d subFuel fuel : Nat)
    (hd : 2 ≤ d) (hsub : 30 ≤ subFuel) (hf : 20 ≤ fuel)
    (cid : Nat) (keyStr : String) (hp : CalcHeap) (jh : Jvm.JvmHeap CalcExt)
    (hstat : ∀ cls fld,
      cls ≠ "com/alexvanyo/composelife/mosaiccalculator/CalculatorEngineKt$WhenMappings" →
      cls ≠ "ComposableSingletons$CalculatorScreenKt" →
      jh.getStatic? cls fld = none)
    (fnTag : String) (caps? : Option JvmVal) (bodyProg : List JvmInstr)
    (hInvoke : ∀ k : CalculatorKey,
      ∃ hp' jh' res subEnd,
        hp.closures[cid]? = some (fnTag, caps?.toList) ∧
        calcProgLookup fnTag = some bodyProg ∧
        Jvm.runJvmRes (mkCalcHooks calcProgLookup (d - 1) subFuel) subFuel bodyProg
            (initCalcJvmState
              (match caps? with
              | none => [(0, .ext (.calcKey k))]
              | some c => [(0, c), (1, .ext (.calcKey k))])
              hp jh) =
          some (res, subEnd) ∧
        subEnd.jvmHeap = jh' ∧ subEnd.heap = hp') :
    ∃ endSt handled,
      Jvm.runJvmRes (mkCalcHooks calcProgLookup d subFuel) fuel CalculatorScreen_lambda_0_0_prog
          (initCalcJvmState [(0, .ext (.closureRef cid)), (1, .ext (.keyEvent keyStr))] hp jh) =
        some (.i32 (if handled then 1 else 0), endSt) ∧
      match mapTerminalKeyModel keyStr with
      | none => handled = false ∧ endSt.jvmHeap = jh ∧ endSt.heap = hp
      | some k =>
        handled = true ∧
        ∃ res subEnd,
          hp.closures[cid]? = some (fnTag, caps?.toList) ∧
          calcProgLookup fnTag = some bodyProg ∧
          Jvm.runJvmRes (mkCalcHooks calcProgLookup (d - 1) subFuel) subFuel bodyProg
              (initCalcJvmState
                (match caps? with
                | none => [(0, .ext (.calcKey k))]
                | some c => [(0, c), (1, .ext (.calcKey k))])
                hp jh) =
            some (res, subEnd) ∧
          subEnd.jvmHeap = endSt.jvmHeap ∧ subEnd.heap = endSt.heap := by
  obtain ⟨d', rfl⟩ := Nat.exists_eq_add_of_le' hd
  obtain ⟨kF, rfl⟩ := Nat.exists_eq_add_of_le' hf
  have hm := mapTerminalKey_equiv calcProgLookup (d' + 1) subFuel subFuel (by omega)
    (by omega) keyStr hp jh hstat
  dsimp only at hm
  obtain ⟨mSt, hmRun, hmJh, hmHp⟩ := hm
  have hMapStep : ∀ {f0 pc0 : Nat} {prog0 rest0 : List JvmInstr} {stk0 : List JvmVal}
      {locs0 : Nat → JvmVal},
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d' + 2) subFuel) (f0 + 1) prog0 pc0
          (.invokestatic "com/alexvanyo/composelife/mosaiccalculator/CalculatorEngineKt"
            "mapTerminalKey"
            "(Ljava/lang/String;)Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorKey;" ::
            rest0)
          ⟨pc0, .str keyStr :: stk0, locs0, jh, hp⟩ =
        Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d' + 2) subFuel) f0 prog0 (pc0 + 1) rest0
          ⟨pc0 + 1,
            (match mapTerminalKeyModel keyStr with | some ck => .ext (.calcKey ck) | none => .null) ::
              stk0,
            locs0, jh, hp⟩ := by
    intro f0 pc0 prog0 rest0 stk0 locs0
    have hstep : (mkCalcHooks calcProgLookup (d' + 2) subFuel).stepInvokeStatic
        ⟨pc0, .str keyStr :: stk0, locs0, jh, hp⟩
        "com/alexvanyo/composelife/mosaiccalculator/CalculatorEngineKt"
        "mapTerminalKey"
        "(Ljava/lang/String;)Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorKey;" =
        .inl (some ⟨pc0 + 1,
          (match mapTerminalKeyModel keyStr with | some ck => .ext (.calcKey ck) | none => .null) ::
            stk0,
          locs0, jh, hp⟩) := by
      conv => lhs; whnf
      unfold_screen_priv
      dsimp only
      rw [show "CalculatorEngineKt" ++ "." ++ "mapTerminalKey" = "CalculatorEngineKt.mapTerminalKey"
        from by apply String.ext; simp]
      rw [show Jvm.parseMethodParamTags
          "(Ljava/lang/String;)Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorKey;" =
          ['L'] from by decide]
      dsimp only [List.length]
      cases (stk0.length + 1).decLt 1 with
      | isTrue h => omega
      | isFalse _ =>
        dsimp only [List.take, List.drop, List.reverse, List.reverseAux]
        unfold_locals_priv
        rw [show calcProgLookup "CalculatorEngineKt.mapTerminalKey" = some mapTerminalKey_prog from rfl]
        dsimp only [initCalcJvmState, Jvm.initJvmState, List.foldl] at hmRun ⊢
        rw [hmRun]
        dsimp only
        rw [hmJh, hmHp]
        rfl
    have hs : Jvm.stepInstr (mkCalcHooks calcProgLookup (d' + 2) subFuel)
        (.invokestatic "com/alexvanyo/composelife/mosaiccalculator/CalculatorEngineKt"
          "mapTerminalKey"
          "(Ljava/lang/String;)Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorKey;")
        ⟨pc0, .str keyStr :: stk0, locs0, jh, hp⟩ =
        .inl (some ⟨pc0 + 1,
          (match mapTerminalKeyModel keyStr with | some ck => .ext (.calcKey ck) | none => .null) ::
            stk0,
          locs0, jh, hp⟩) := by
      dsimp only [Jvm.stepInstr, Jvm.stepInvokeStaticGeneric]
      exact hstep
    exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks calcProgLookup (d' + 2) subFuel)
      rfl (by simp) hs rfl
  let locs0 : Nat → JvmVal := @setLocal CalcExt
    (@setLocal CalcExt (fun _ => .i32 0) 0 (.ext (.closureRef cid))) 1 (.ext (.keyEvent keyStr))
  have hl0 : locs0 0 = .ext (.closureRef cid) := rfl
  have hl1 : locs0 1 = .ext (.keyEvent keyStr) := rfl
  cases hmk : mapTerminalKeyModel keyStr with
  | none =>
    refine ⟨⟨16, [.i32 0], @setLocal CalcExt locs0 2 .null, jh, hp⟩, false,
      Jvm.runJvmRes_of_runJvmResFast0 _ _ _ _ _ rfl ?_, rfl, rfl, rfl⟩
    dsimp only [initCalcJvmState, Jvm.initJvmState, List.foldl]
    change Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d' + 2) subFuel) (kF + 20)
        CalculatorScreen_lambda_0_0_prog 0 CalculatorScreen_lambda_0_0_prog
        ⟨0, [], locs0, jh, hp⟩ = _
    dsimp only [CalculatorScreen_lambda_0_0_prog]
    rw [runFast_aload, hl1, runFast_ldcStr, runFast_checkNotNull' (d' + 1) subFuel _ _ _ rfl]
    rw [runFast_aload, hl1, runFast_getKey, hMapStep, hmk, runFast_astore]
    have hl2 : (@setLocal CalcExt locs0 2 .null) 2 = .null := rfl
    rw [runFast_aload, hl2, runFast_ifnull_branch']
    dsimp only [CalculatorScreen_lambda_0_0_prog, List.drop]
    rw [runFast_iconst, runFast_ireturn calcProgLookup (d' + 2) subFuel]
    rfl
  | some ck =>
    obtain ⟨hp', jh', res, subEnd, hclos, hlook, hsubRun, hsubJh, hsubHp⟩ := hInvoke ck
    refine ⟨⟨16, [.i32 1], @setLocal CalcExt locs0 2 (.ext (.calcKey ck)), jh', hp'⟩, true,
      Jvm.runJvmRes_of_runJvmResFast0 _ _ _ _ _ rfl ?_,
      ⟨rfl, res, subEnd, hclos, hlook, hsubRun, hsubJh, hsubHp⟩⟩
    dsimp only [initCalcJvmState, Jvm.initJvmState, List.foldl]
    change Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d' + 2) subFuel) (kF + 20)
        CalculatorScreen_lambda_0_0_prog 0 CalculatorScreen_lambda_0_0_prog
        ⟨0, [], locs0, jh, hp⟩ = _
    dsimp only [CalculatorScreen_lambda_0_0_prog]
    rw [runFast_aload, hl1, runFast_ldcStr, runFast_checkNotNull' (d' + 1) subFuel _ _ _ rfl]
    rw [runFast_aload, hl1, runFast_getKey, hMapStep, hmk, runFast_astore]
    have hl0' : (@setLocal CalcExt locs0 2 (.ext (.calcKey ck))) 0 = .ext (.closureRef cid) := rfl
    have hl2' : (@setLocal CalcExt locs0 2 (.ext (.calcKey ck))) 2 = .ext (.calcKey ck) := rfl
    rw [runFast_aload, hl2', runFast_ifnull_fallthrough' rfl]
    rw [runFast_aload, hl0', runFast_aload, hl2']
    rw [runFast_function1Invoke (d' + 1) subFuel _ _ fnTag caps? bodyProg hclos hlook
      ⟨subEnd, hsubRun, hsubJh, hsubHp⟩]
    rw [runFast_pop, runFast_iconst, runFast_goto']
    dsimp only [CalculatorScreen_lambda_0_0_prog, List.drop]
    rw [runFast_ireturn calcProgLookup (d' + 2) subFuel]
    rfl

private def mkRowLambdaProg' (info : String) (traceKey : UInt32) (traceInfo rowText : String) :
    List JvmInstr :=
  [ .aload 0, .ldcStr "$this$Row"
  , .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter" "(Ljava/lang/Object;Ljava/lang/String;)V"
  , .aload 1, .ldcStr info
  , .invokestatic "androidx/compose/runtime/ComposerKt" "sourceInformation"
      "(Landroidx/compose/runtime/Composer;Ljava/lang/String;)V"
  , .aload 1, .iload 2, .iconst 17, .iand, .iconst 16, .if_icmpeq 14, .iconst 1, .goto 15, .iconst 0
  , .iload 2, .iconst 1, .iand
  , .invokeinterface "androidx/compose/runtime/Composer" "shouldExecute" "(ZI)Z"
  , .ifeq 42
  , .invokestatic "androidx/compose/runtime/ComposerKt" "isTraceInProgress" "()Z"
  , .ifeq 27
  , .iconst traceKey, .iload 2, .iconst 4294967295, .ldcStr traceInfo
  , .invokestatic "androidx/compose/runtime/ComposerKt" "traceEventStart" "(IIILjava/lang/String;)V"
  , .ldcStr rowText, .aconstNull, .iconst 0, .iconst 0, .iconst 0, .iconst 0, .iconst 0
  , .aload 1, .iconst 6, .iconst 126
  , .invokestatic "com/jakewharton/mosaic/ui/Text" "Text-cbmis8g"
      "(Ljava/lang/String;Lcom/jakewharton/mosaic/modifier/Modifier;IIIIILandroidx/compose/runtime/Composer;II)V"
  , .invokestatic "androidx/compose/runtime/ComposerKt" "isTraceInProgress" "()Z"
  , .ifeq 44
  , .invokestatic "androidx/compose/runtime/ComposerKt" "traceEventEnd" "()V"
  , .goto 44
  , .aload 1, .invokeinterface "androidx/compose/runtime/Composer" "skipToGroupEnd" "()V"
  , .getstatic "kotlin/Unit" "INSTANCE" "Lkotlin/Unit;"
  , .areturn ]

private theorem rowLambda_exec_any (d fuel : Nat) (hf : 40 ≤ fuel)
    (info : String) (traceKey : UInt32) (traceInfo rowText : String)
    (hp : CalcHeap) (jh : Jvm.JvmHeap CalcExt)
    (htrace : hp.composer.traceEnabled = false)
    (hunit : jh.getStatic? "kotlin/Unit" "INSTANCE" = none) :
    ∃ st',
      Jvm.runJvmRes (mkCalcHooks calcProgLookup (d + 1) fuel) fuel
          (mkRowLambdaProg' info traceKey traceInfo rowText)
          (initCalcJvmState [(0, .ext .unit), (1, .ext .composer), (2, .i32 6)] hp jh) =
        some (.ext .unit, st') ∧
      st'.jvmHeap = jh ∧
      st'.heap = emitMosaicNode hp (.text rowText) := by
  obtain ⟨kF, rfl⟩ := Nat.exists_eq_add_of_le' hf
  suffices h : ∃ st',
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) (kF + 40)) (kF + 40)
          (mkRowLambdaProg' info traceKey traceInfo rowText) 0
          (mkRowLambdaProg' info traceKey traceInfo rowText)
          (initCalcJvmState [(0, .ext .unit), (1, .ext .composer), (2, .i32 6)] hp jh) =
        some (.ext .unit, st') ∧
      st'.jvmHeap = jh ∧
      st'.heap = emitMosaicNode hp (.text rowText) by
    obtain ⟨st', h1, h2, h3⟩ := h
    exact ⟨st', Jvm.runJvmRes_of_runJvmResFast0 _ _ _ _ _ rfl h1, h2, h3⟩
  dsimp only [initCalcJvmState, Jvm.initJvmState, List.foldl]
  let locs0 : Nat → JvmVal :=
    @setLocal CalcExt
      (@setLocal CalcExt
        (@setLocal CalcExt (fun _ => .i32 0) 0 (.ext .unit))
        1 (.ext .composer))
      2 (.i32 6)
  have hl0 : locs0 0 = .ext .unit := rfl
  have hl1 : locs0 1 = .ext .composer := rfl
  have hl2 : locs0 2 = .i32 6 := rfl
  change ∃ st',
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) (kF + 40)) (kF + 40)
          (mkRowLambdaProg' info traceKey traceInfo rowText) 0
          (mkRowLambdaProg' info traceKey traceInfo rowText) ⟨0, [], locs0, jh, hp⟩ =
        some (.ext .unit, st') ∧
      st'.jvmHeap = jh ∧
      st'.heap = emitMosaicNode hp (.text rowText)
  dsimp only [mkRowLambdaProg']
  rw [runFast_aload, hl0, runFast_ldcStr, runFast_checkNotNullParam]
  rw [runFast_aload, hl1, runFast_ldcStr, runFast_sourceInfo]
  rw [runFast_aload, hl1, runFast_iload, hl2, runFast_iconst, runFast_iand, runFast_iconst]
  rw [runFast_if_icmpeq_ne (by decide)]
  rw [runFast_iconst, runFast_goto']
  dsimp only [mkRowLambdaProg', List.drop]
  rw [runFast_iload, hl2, runFast_iconst, runFast_iand, runFast_shouldExecute]
  have hse : Compose.shouldExecute hp.composer (((1 : UInt32) != 0)) ((6 &&& 1 : UInt32).toInt32) = true := by
    simp [Compose.shouldExecute]
  rw [hse]
  simp only [↓reduceIte]
  rw [runFast_ifeq_nonzero (by decide)]
  rw [runFast_isTraceInProgress, htrace]
  rw [ite_eq_right (by decide)]
  rw [runFast_ifeq_zero]
  dsimp only [mkRowLambdaProg', List.drop]
  rw [runFast_ldcStr, runFast_aconstNull, runFast_iconst, runFast_iconst, runFast_iconst,
    runFast_iconst, runFast_iconst, runFast_aload, hl1, runFast_iconst, runFast_iconst, runFast_text]
  rw [runFast_isTraceInProgress]
  have htrace' : (emitMosaicNode hp (.text rowText)).composer.traceEnabled = false := by
    dsimp [emitMosaicNode]
    cases hp.nodeStack with
    | nil => exact htrace
    | cons _ _ => exact htrace
  rw [htrace']
  rw [ite_eq_right (by decide)]
  rw [runFast_ifeq_zero]
  dsimp only [mkRowLambdaProg', List.drop]
  rw [runFast_getStatic_unit hunit, runFast_areturn']
  exact ⟨_, rfl, rfl, rfl⟩

/-- Bytecode equivalence theorem for `CalculatorScreenKt.CalculatorScreen$lambda$1`. -/
theorem CalculatorScreen_lambda_1_equiv (d subFuel fuel : Nat)
    (hd : 2 ≤ d) (hsub : 40 ≤ subFuel) (hf : 110 ≤ fuel)
    (cSt : CalculatorState) (jh : Jvm.JvmHeap CalcExt) (hp : CalcHeap)
    (htrace : hp.composer.traceEnabled = false)
    (prevChildren : List Mosaic.MosaicNode) (prevH? : Option Nat)
    (parents : List (List Mosaic.MosaicNode × Option Nat))
    (hnode : hp.nodeStack = (prevChildren, prevH?) :: parents)
    (herrSwitch : ∃ errAddr,
      jh.getStatic? "com/alexvanyo/composelife/mosaiccalculator/CalculatorEngineKt$WhenMappings"
        "$EnumSwitchMapping$1" = some (.heapRef errAddr) ∧
      jh.get? errAddr = some (.intArray #[1, 2]))
    (hstat : ∀ cls fld,
      cls ≠ "com/alexvanyo/composelife/mosaiccalculator/CalculatorEngineKt$WhenMappings" →
      cls ≠ "ComposableSingletons$CalculatorScreenKt" →
      jh.getStatic? cls fld = none)
    (hsing : HasSingletonRowLambdas jh hp.closures) :
    ∃ endSt,
      Jvm.runJvmRes (mkCalcHooks calcProgLookup d subFuel) fuel CalculatorScreen_lambda_1_prog
          (initCalcJvmState
            [(0, .ext (.calcState cSt)), (1, .ext .unit), (2, .ext .composer), (3, .i32 6)]
            hp jh) =
        some (.ext .unit, endSt) ∧
      endSt.jvmHeap = jh ∧
      endSt.heap = { hp with
        nodeStack := (prevChildren ++
          [ .text "=== Calculator ==="
          , .text s!"> {formatDisplayLineModel cSt}"
          , .row [.text "[7] [8] [9] [/]"] none
          , .row [.text "[4] [5] [6] [*]"] none
          , .row [.text "[1] [2] [3] [-]"] none
          , .row [.text "[0] [C] [=] [+]"] none
          ], prevH?) :: parents } := by
  obtain ⟨d', rfl⟩ := Nat.exists_eq_add_of_le' hd
  obtain ⟨kF, rfl⟩ := Nat.exists_eq_add_of_le' hf
  obtain ⟨id0, id1, id2, id3, hs0, hs1, hs2, hs3, hc0, hc1, hc2, hc3⟩ := hsing
  have hunit : jh.getStatic? "kotlin/Unit" "INSTANCE" = none :=
    hstat _ _ (by decide) (by decide)
  have hsingInst : jh.getStatic?
      "com/alexvanyo/composelife/mosaiccalculator/ComposableSingletons$CalculatorScreenKt"
      "INSTANCE" = none :=
    hstat _ _ (by decide) (by decide)
  let hp1 : CalcHeap := { hp with
    nodeStack := (prevChildren ++ [.text "=== Calculator ==="], prevH?) :: parents }
  let hp2 : CalcHeap := { hp with
    nodeStack := (prevChildren ++ [.text "=== Calculator ===",
      .text ("> " ++ formatDisplayLineModel cSt)], prevH?) :: parents }
  let hp3 : CalcHeap := { hp2 with
    nodeStack := ((prevChildren ++ [.text "=== Calculator ===",
      .text ("> " ++ formatDisplayLineModel cSt)]) ++
      [.row [.text "[7] [8] [9] [/]"] none], prevH?) :: parents }
  let hp4 : CalcHeap := { hp3 with
    nodeStack := (((prevChildren ++ [.text "=== Calculator ===",
      .text ("> " ++ formatDisplayLineModel cSt)]) ++
      [.row [.text "[7] [8] [9] [/]"] none]) ++
      [.row [.text "[4] [5] [6] [*]"] none], prevH?) :: parents }
  let hp5 : CalcHeap := { hp4 with
    nodeStack := ((((prevChildren ++ [.text "=== Calculator ===",
      .text ("> " ++ formatDisplayLineModel cSt)]) ++
      [.row [.text "[7] [8] [9] [/]"] none]) ++
      [.row [.text "[4] [5] [6] [*]"] none]) ++
      [.row [.text "[1] [2] [3] [-]"] none], prevH?) :: parents }
  have hemit1 : emitMosaicNode hp (.text "=== Calculator ===") = hp1 := by
    dsimp only [emitMosaicNode, hp1]; rw [hnode]
  have hemit2 : emitMosaicNode hp1 (.text ("> " ++ formatDisplayLineModel cSt)) = hp2 := by
    dsimp only [emitMosaicNode, hp1, hp2]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  suffices h : ∃ endSt,
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d' + 2) subFuel) (kF + 110)
          CalculatorScreen_lambda_1_prog 0 CalculatorScreen_lambda_1_prog
          (initCalcJvmState
            [(0, .ext (.calcState cSt)), (1, .ext .unit), (2, .ext .composer), (3, .i32 6)]
            hp jh) =
        some (.ext .unit, endSt) ∧
      endSt.jvmHeap = jh ∧
      endSt.heap = { hp with
        nodeStack := (prevChildren ++
          [ .text "=== Calculator ==="
          , .text s!"> {formatDisplayLineModel cSt}"
          , .row [.text "[7] [8] [9] [/]"] none
          , .row [.text "[4] [5] [6] [*]"] none
          , .row [.text "[1] [2] [3] [-]"] none
          , .row [.text "[0] [C] [=] [+]"] none
          ], prevH?) :: parents } by
    obtain ⟨endSt, h1, h2, h3⟩ := h
    exact ⟨endSt, Jvm.runJvmRes_of_runJvmResFast0 _ _ _ _ _ rfl h1, h2, h3⟩
  dsimp only [initCalcJvmState, Jvm.initJvmState, List.foldl]
  let locs0 : Nat → JvmVal :=
    @setLocal CalcExt
      (@setLocal CalcExt
        (@setLocal CalcExt
          (@setLocal CalcExt (fun _ => .i32 0) 0 (.ext (.calcState cSt)))
          1 (.ext .unit))
        2 (.ext .composer))
      3 (.i32 6)
  have hl0 : locs0 0 = .ext (.calcState cSt) := rfl
  have hl1 : locs0 1 = .ext .unit := rfl
  have hl2 : locs0 2 = .ext .composer := rfl
  have hl3 : locs0 3 = .i32 6 := rfl
  change ∃ endSt,
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d' + 2) subFuel) (kF + 110)
          CalculatorScreen_lambda_1_prog 0 CalculatorScreen_lambda_1_prog ⟨0, [], locs0, jh, hp⟩ =
        some (.ext .unit, endSt) ∧
      endSt.jvmHeap = jh ∧
      endSt.heap = { hp with
        nodeStack := (prevChildren ++
          [ .text "=== Calculator ==="
          , .text s!"> {formatDisplayLineModel cSt}"
          , .row [.text "[7] [8] [9] [/]"] none
          , .row [.text "[4] [5] [6] [*]"] none
          , .row [.text "[1] [2] [3] [-]"] none
          , .row [.text "[0] [C] [=] [+]"] none
          ], prevH?) :: parents }
  dsimp only [CalculatorScreen_lambda_1_prog]
  rw [runFast_aload, hl1, runFast_ldcStr, runFast_checkNotNull' (d' + 1) subFuel _ _ _ rfl]
  rw [runFast_aload, hl2, runFast_ldcStr, runFast_sourceInfo' (d' + 1) subFuel]
  rw [runFast_aload, hl2, runFast_iload, hl3, runFast_iconst, runFast_iand, runFast_iconst]
  rw [runFast_if_icmpeq_ne (by decide)]
  rw [runFast_iconst, runFast_goto']
  dsimp only [CalculatorScreen_lambda_1_prog, List.drop]
  rw [runFast_iload, hl3, runFast_iconst, runFast_iand]
  have hsh0 : Compose.shouldExecute hp.composer ((1 : UInt32) != 0) ((6 : UInt32) &&& (1 : UInt32)).toInt32 = true := by
    dsimp only [Compose.shouldExecute]
    simp
  rw [runFast_shouldExecute' (d' + 1) subFuel]
  rw [hsh0]
  simp only [↓reduceIte]
  rw [runFast_ifeq_nonzero (by decide)]
  rw [runFast_isTraceInProgress' (d' + 1) subFuel _ _ _ htrace]
  rw [runFast_ifeq_zero]
  dsimp only [CalculatorScreen_lambda_1_prog, List.drop]
  rw [runFast_ldcStr, runFast_aconstNull, runFast_iconst, runFast_iconst, runFast_iconst,
    runFast_iconst, runFast_iconst, runFast_aload, hl2, runFast_iconst, runFast_iconst]
  rw [runFast_text' (d' + 1) subFuel, hemit1]
  rw [runFast_aload, hl0, runFast_formatDisplayLine d' subFuel _ _ (by omega) herrSwitch]
  rw [runFast_makeConcat_gt' (d' + 1) subFuel]
  rw [runFast_aconstNull, runFast_iconst, runFast_iconst, runFast_iconst,
    runFast_iconst, runFast_iconst, runFast_aload, hl2, runFast_iconst, runFast_iconst]
  rw [runFast_text' (d' + 1) subFuel, hemit2]
  rw [runFast_aconstNull, runFast_aconstNull, runFast_aconstNull,
    runFast_getStatic_singletonInst (d' + 1) subFuel _ _ _ hsingInst]
  rw [runFast_getLambda_step (d' + 1) subFuel _ _ (by omega) hs0 rfl]
  rw [runFast_aload, hl2, runFast_iconst, runFast_iconst]
  rw [runFast_row_text (d' + 1) subFuel _ _ id0 (hp := hp2) rfl hc0
    (by
      obtain ⟨st', h1, h2, h3⟩ := rowLambda_exec_any d' subFuel (by omega)
        "C63@2157L23:CalculatorScreen.kt#b0tpbg" 125313259
        "com.alexvanyo.composelife.mosaiccalculator.ComposableSingletons$CalculatorScreenKt.lambda$125313259.<anonymous> (CalculatorScreen.kt:63)"
        "[7] [8] [9] [/]" { hp2 with nodeStack := ([], none) :: hp2.nodeStack } jh htrace hunit
      exact ⟨lambda_125313259_lambda_0_prog, st', rfl, h1, h2, h3⟩)]
  rw [runFast_aconstNull, runFast_aconstNull, runFast_aconstNull,
    runFast_getStatic_singletonInst (d' + 1) subFuel _ _ _ hsingInst]
  rw [runFast_getLambda_step (d' + 1) subFuel _ _ (by omega) hs1 rfl]
  rw [runFast_aload, hl2, runFast_iconst, runFast_iconst]
  rw [runFast_row_text (d' + 1) subFuel _ _ id1 (hp := hp3) rfl hc1
    (by
      obtain ⟨st', h1, h2, h3⟩ := rowLambda_exec_any d' subFuel (by omega)
        "C66@2217L23:CalculatorScreen.kt#b0tpbg" 9509460
        "com.alexvanyo.composelife.mosaiccalculator.ComposableSingletons$CalculatorScreenKt.lambda$9509460.<anonymous> (CalculatorScreen.kt:66)"
        "[4] [5] [6] [*]" { hp3 with nodeStack := ([], none) :: hp3.nodeStack } jh htrace hunit
      exact ⟨lambda_9509460_lambda_0_prog, st', rfl, h1, h2, h3⟩)]
  rw [runFast_aconstNull, runFast_aconstNull, runFast_aconstNull,
    runFast_getStatic_singletonInst (d' + 1) subFuel _ _ _ hsingInst]
  rw [runFast_getLambda_step (d' + 1) subFuel _ _ (by omega) hs2 rfl]
  rw [runFast_aload, hl2, runFast_iconst, runFast_iconst]
  rw [runFast_row_text (d' + 1) subFuel _ _ id2 (hp := hp4) rfl hc2
    (by
      obtain ⟨st', h1, h2, h3⟩ := rowLambda_exec_any d' subFuel (by omega)
        "C69@2277L23:CalculatorScreen.kt#b0tpbg" 2033009011
        "com.alexvanyo.composelife.mosaiccalculator.ComposableSingletons$CalculatorScreenKt.lambda$2033009011.<anonymous> (CalculatorScreen.kt:69)"
        "[1] [2] [3] [-]" { hp4 with nodeStack := ([], none) :: hp4.nodeStack } jh htrace hunit
      exact ⟨lambda_2033009011_lambda_0_prog, st', rfl, h1, h2, h3⟩)]
  rw [runFast_aconstNull, runFast_aconstNull, runFast_aconstNull,
    runFast_getStatic_singletonInst (d' + 1) subFuel _ _ _ hsingInst]
  rw [runFast_getLambda_step (d' + 1) subFuel _ _ (by omega) hs3 rfl]
  rw [runFast_aload, hl2, runFast_iconst, runFast_iconst]
  rw [runFast_row_text (d' + 1) subFuel _ _ id3 (hp := hp5) rfl hc3
    (by
      obtain ⟨st', h1, h2, h3⟩ := rowLambda_exec_any d' subFuel (by omega)
        "C72@2337L23:CalculatorScreen.kt#b0tpbg" 4056508562
        "com.alexvanyo.composelife.mosaiccalculator.ComposableSingletons$CalculatorScreenKt.lambda$-238458734.<anonymous> (CalculatorScreen.kt:72)"
        "[0] [C] [=] [+]" { hp5 with nodeStack := ([], none) :: hp5.nodeStack } jh htrace hunit
      exact ⟨lambda__238458734_lambda_0_prog, st', rfl, h1, h2, h3⟩)]
  have htr5 : hp.composer.traceEnabled = false := htrace
  rw [runFast_isTraceInProgress' (d' + 1) subFuel _ _ _ (by exact htr5)]
  rw [runFast_ifeq_zero]
  dsimp only [CalculatorScreen_lambda_1_prog, List.drop]
  rw [runFast_getStatic_unit' (d' + 1) subFuel _ _ _ hunit, runFast_areturn']
  refine ⟨_, rfl, rfl, ?_⟩
  simp only [hp5, hp4, hp3, hp2, List.append_assoc, List.cons_append, List.nil_append]
  rfl

set_option maxRecDepth 2048 in
/-- Bytecode equivalence theorem for `CalculatorScreenKt.CalculatorScreen$lambda$2`. -/
theorem CalculatorScreen_lambda_2_equiv (d subFuel fuel : Nat)
    (hd : 1 ≤ d) (hf : 15 ≤ fuel)
    (cSt : CalculatorState) (onKey : JvmVal) (modV : JvmVal)
    (ch defF recompCh : UInt32) (hp hp' : CalcHeap) (jh jh' : Jvm.JvmHeap CalcExt)
    (hunit : jh'.getStatic? "kotlin/Unit" "INSTANCE" = none)
    (hScreen : ∃ subEnd,
      Jvm.runJvmRes (mkCalcHooks calcProgLookup (d - 1) subFuel) subFuel CalculatorScreen_prog
          (initCalcJvmState
            [(0, .ext (.calcState cSt)), (1, onKey), (2, modV), (3, .ext .composer),
             (4, .i32 (Compose.updateChangedFlags (ch ||| 1))), (5, .i32 defF)]
            hp jh) =
        some (.ext .unit, subEnd) ∧
      subEnd.jvmHeap = jh' ∧ subEnd.heap = hp') :
    ∃ endSt,
      Jvm.runJvmRes (mkCalcHooks calcProgLookup d subFuel) fuel CalculatorScreen_lambda_2_prog
          (initCalcJvmState
            [(0, .ext (.calcState cSt)), (1, onKey), (2, modV), (3, .i32 ch), (4, .i32 defF),
             (5, .ext .composer), (6, .i32 recompCh)]
            hp jh) =
        some (.ext .unit, endSt) ∧
      endSt.jvmHeap = jh' ∧ endSt.heap = hp' := by
  obtain ⟨d', rfl⟩ := Nat.exists_eq_add_of_le' hd
  obtain ⟨kF, rfl⟩ := Nat.exists_eq_add_of_le' hf
  obtain ⟨subEnd, hrun, hjh', hhp'⟩ := hScreen
  suffices h : ∃ endSt,
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d' + 1) subFuel) (kF + 15)
          CalculatorScreen_lambda_2_prog 0 CalculatorScreen_lambda_2_prog
          (initCalcJvmState
            [(0, .ext (.calcState cSt)), (1, onKey), (2, modV), (3, .i32 ch), (4, .i32 defF),
             (5, .ext .composer), (6, .i32 recompCh)]
            hp jh) =
        some (.ext .unit, endSt) ∧
      endSt.jvmHeap = jh' ∧ endSt.heap = hp' by
    obtain ⟨endSt, h1, h2, h3⟩ := h
    exact ⟨endSt, Jvm.runJvmRes_of_runJvmResFast0 _ _ _ _ _ rfl h1, h2, h3⟩
  dsimp only [initCalcJvmState, Jvm.initJvmState, List.foldl]
  let locs0 : Nat → JvmVal :=
    @setLocal CalcExt
      (@setLocal CalcExt
        (@setLocal CalcExt
          (@setLocal CalcExt
            (@setLocal CalcExt
              (@setLocal CalcExt
                (@setLocal CalcExt (fun _ => .i32 0) 0 (.ext (.calcState cSt)))
                1 onKey)
              2 modV)
            3 (.i32 ch))
          4 (.i32 defF))
        5 (.ext .composer))
      6 (.i32 recompCh)
  have hl0 : locs0 0 = .ext (.calcState cSt) := rfl
  have hl1 : locs0 1 = onKey := rfl
  have hl2 : locs0 2 = modV := rfl
  have hl3 : locs0 3 = .i32 ch := rfl
  have hl4 : locs0 4 = .i32 defF := rfl
  have hl5 : locs0 5 = .ext .composer := rfl
  change ∃ endSt,
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d' + 1) subFuel) (kF + 15)
          CalculatorScreen_lambda_2_prog 0 CalculatorScreen_lambda_2_prog ⟨0, [], locs0, jh, hp⟩ =
        some (.ext .unit, endSt) ∧
      endSt.jvmHeap = jh' ∧ endSt.heap = hp'
  dsimp only [CalculatorScreen_lambda_2_prog]
  rw [runFast_aload, hl0, runFast_aload, hl1, runFast_aload, hl2, runFast_aload, hl5]
  rw [runFast_iload, hl3, runFast_iconst, runFast_ior]
  have huc : Jvm.stepInstr (mkCalcHooks calcProgLookup (d' + 1) subFuel)
      (.invokestatic "androidx/compose/runtime/RecomposeScopeImplKt" "updateChangedFlags" "(I)I")
      ⟨7, [.i32 (ch ||| 1), .ext .composer, modV, onKey, .ext (.calcState cSt)], locs0, jh, hp⟩ =
      .inl (some ⟨8, [.i32 (Compose.updateChangedFlags (ch ||| 1)),
        .ext .composer, modV, onKey, .ext (.calcState cSt)], locs0, jh, hp⟩) := rfl
  rw [Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks calcProgLookup (d' + 1) subFuel) rfl (by simp) huc rfl]
  rw [runFast_iload, hl4]
  have hsScr : Jvm.stepInstr (mkCalcHooks calcProgLookup (d' + 1) subFuel)
      (.invokestatic "CalculatorScreenKt" "CalculatorScreen"
        "(Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorState;Lkotlin/jvm/functions/Function1;Lcom/jakewharton/mosaic/modifier/Modifier;Landroidx/compose/runtime/Composer;II)V")
      ⟨9, [.i32 defF, .i32 (Compose.updateChangedFlags (ch ||| 1)),
        .ext .composer, modV, onKey, .ext (.calcState cSt)], locs0, jh, hp⟩ =
      .inl (some ⟨10, [], locs0, jh', hp'⟩) := by
    have hstep : (mkCalcHooks calcProgLookup (d' + 1) subFuel).stepInvokeStatic
        ⟨9, [.i32 defF, .i32 (Compose.updateChangedFlags (ch ||| 1)),
          .ext .composer, modV, onKey, .ext (.calcState cSt)], locs0, jh, hp⟩
        "CalculatorScreenKt" "CalculatorScreen"
        "(Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorState;Lkotlin/jvm/functions/Function1;Lcom/jakewharton/mosaic/modifier/Modifier;Landroidx/compose/runtime/Composer;II)V" =
        .inl (some ⟨10, [], locs0, jh', hp'⟩) := by
      conv => lhs; whnf
      unfold_screen_priv
      dsimp only
      rw [show "CalculatorScreenKt" ++ "." ++ "CalculatorScreen" = "CalculatorScreenKt.CalculatorScreen"
        from by apply String.ext; simp]
      rw [show Jvm.parseMethodParamTags
          "(Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorState;Lkotlin/jvm/functions/Function1;Lcom/jakewharton/mosaic/modifier/Modifier;Landroidx/compose/runtime/Composer;II)V" =
          ['L', 'L', 'L', 'L', 'I', 'I'] from by decide]
      dsimp only [List.length, List.take, List.drop, List.reverse, List.reverseAux]
      unfold_locals_priv
      rw [show d' + 1 - 1 = d' from rfl] at hrun
      simp only [Nat.reduceAdd, calcProgLookup, initCalcJvmState, Jvm.initJvmState, List.foldl] at hrun ⊢
      rw [hrun]
      dsimp only
      rw [hjh', hhp']
      rfl
    dsimp only [Jvm.stepInstr, Jvm.stepInvokeStaticGeneric]
    exact hstep
  rw [Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks calcProgLookup (d' + 1) subFuel) rfl (by simp) hsScr rfl]
  rw [runFast_getStatic_unit' d' subFuel _ _ _ hunit, runFast_areturn']
  exact ⟨_, rfl, rfl, rfl⟩

/-! ### `CalculatorScreen` Composable Bytecode Proofs -/

private theorem runFast_vreturn' {hooks : Jvm.JvmHooks CalcExt CalcHeap} {f pc : Nat}
    {prog rest : List JvmInstr} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.vreturn :: rest) ⟨pc, stk, locs, jh, hp⟩ =
      some (.unit, ⟨pc, stk, locs, jh, hp⟩) := by
  rw [Jvm.runJvmResFast_step_nonbranch hooks f prog pc .vreturn rest ⟨pc, stk, locs, jh, hp⟩ rfl (by simp)]
  rfl

private theorem runFast_ifne_zero' [Jvm.HasDefaultIsZero hooks]
    {f pc target : Nat} {prog rest : List JvmInstr} {v : UInt32} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap}
    (hz : v = 0 := by decide) :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.ifne target :: rest) ⟨pc, .i32 v :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest ⟨pc + 1, stk, locs, jh, hp⟩ := by
  subst hz
  rw [Jvm.runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch,
    Jvm.HasDefaultIsZero.isZero?_eq (hooks := hooks)]

private theorem runFast_ifne_nonzero' [Jvm.HasDefaultIsZero hooks]
    {f pc target : Nat} {prog rest : List JvmInstr} {v : UInt32} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} (hnz : v ≠ 0) :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.ifne target :: rest) ⟨pc, .i32 v :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog target (prog.drop target) ⟨target, stk, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch,
    Jvm.HasDefaultIsZero.isZero?_eq (hooks := hooks), hnz]

private theorem runFast_if_icmpeq_eq' {hooks : Jvm.JvmHooks CalcExt CalcHeap}
    {f pc target : Nat} {prog rest : List JvmInstr} {a b : UInt32} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} (heq : a = b) :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.if_icmpeq target :: rest)
        ⟨pc, .i32 b :: .i32 a :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog target (prog.drop target) ⟨target, stk, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch, heq]

private theorem runFast_if_icmpne_ne' {hooks : Jvm.JvmHooks CalcExt CalcHeap}
    {f pc target : Nat} {prog rest : List JvmInstr} {a b : UInt32} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} (hne : a ≠ b) :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.if_icmpne target :: rest)
        ⟨pc, .i32 b :: .i32 a :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog target (prog.drop target) ⟨target, stk, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch, hne]

private theorem runFast_getComposerCompanion {d subFuel f pc : Nat}
    {prog rest : List JvmInstr} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap}
    (hnone : jh.getStatic? "androidx/compose/runtime/Composer" "Companion" = none) :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) (f + 1) prog pc
        (.getstatic "androidx/compose/runtime/Composer" "Companion"
          "Landroidx/compose/runtime/Composer$Companion;" :: rest)
        ⟨pc, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.companion "Composer$Companion") :: stk, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  dsimp only [Jvm.stepInstr, mkCalcHooks]
  rw [hnone]
  rfl

private theorem runFast_getEmpty' {d subFuel f pc : Nat}
    {prog rest : List JvmInstr} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) (f + 1) prog pc
        (.invokevirtual "androidx/compose/runtime/Composer$Companion" "getEmpty"
          "()Ljava/lang/Object;" :: rest)
        ⟨pc, .ext (.companion "Composer$Companion") :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext .composerEmpty :: stk, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  change (mkCalcHooks calcProgLookup (d + 1) subFuel).stepInvokeVirtual _ _ _ _ = _
  conv => lhs; whnf

private theorem runFast_invokedynamic_bsm1 {d subFuel f pc : Nat}
    {prog rest : List JvmInstr} {bsmArg desc fnTag : String} {c0 : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap}
    (htags : Jvm.parseMethodParamTags desc = ['L'])
    (hbsm : extractBsmTarget bsmArg = some fnTag) :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) (f + 1) prog pc
        (.invokedynamic "LambdaMetafactory" bsmArg desc :: rest)
        ⟨pc, c0 :: stk, locs, jh, hp⟩ =
      let r := allocClosure hp fnTag [c0]
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.closureRef r.1) :: stk, locs, jh, r.2⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  change (mkCalcHooks calcProgLookup (d + 1) subFuel).stepInvokeDynamic _ _ _ _ = _
  dsimp only [mkCalcHooks]
  rw [show ("LambdaMetafactory" == "LambdaMetafactory") = true from rfl]
  simp only [↓reduceIte, htags, List.length_cons, List.length_nil]
  cases (stk.length + 1).decLt 1 with
  | isTrue h => omega
  | isFalse _ =>
    dsimp only [List.take, List.drop, List.reverse, List.reverseAux]
    rw [hbsm]
    rfl

private theorem runFast_invokedynamic_bsm5 {d subFuel f pc : Nat}
    {prog rest : List JvmInstr} {bsmArg desc fnTag : String} {c0 c1 c2 c3 c4 : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap}
    (htags : Jvm.parseMethodParamTags desc = ['L', 'L', 'L', 'I', 'I'])
    (hbsm : extractBsmTarget bsmArg = some fnTag) :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) (f + 1) prog pc
        (.invokedynamic "LambdaMetafactory" bsmArg desc :: rest)
        ⟨pc, c4 :: c3 :: c2 :: c1 :: c0 :: stk, locs, jh, hp⟩ =
      let r := allocClosure hp fnTag [c0, c1, c2, c3, c4]
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.closureRef r.1) :: stk, locs, jh, r.2⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  change (mkCalcHooks calcProgLookup (d + 1) subFuel).stepInvokeDynamic _ _ _ _ = _
  dsimp only [mkCalcHooks]
  rw [show ("LambdaMetafactory" == "LambdaMetafactory") = true from rfl]
  simp only [↓reduceIte, htags, List.length_cons, List.length_nil]
  cases (stk.length + 5).decLt 5 with
  | isTrue h => omega
  | isFalse _ =>
    dsimp only [List.take, List.drop, List.reverse, List.reverseAux]
    rw [hbsm]
    rfl

set_option maxRecDepth 2048 in
private theorem runFast_column_lambda1 (d subFuel f pc cid : Nat)
    {prog rest : List JvmInstr} {cSt : CalculatorState} {handler? : Option Nat}
    {arrV alignV chV dfltV : JvmVal} {children : List Mosaic.MosaicNode}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp hpAfter : CalcHeap}
    (hclos : hp.closures[cid]? = some ("CalculatorScreenKt.CalculatorScreen$lambda$1", [.ext (.calcState cSt)]))
    (hbody : ∃ endSt,
      Jvm.runJvmRes (mkCalcHooks calcProgLookup d subFuel) subFuel CalculatorScreen_lambda_1_prog
          (initCalcJvmState
            [(0, .ext (.calcState cSt)), (1, .ext .unit), (2, .ext .composer), (3, .i32 6)]
            { hp with nodeStack := ([], handler?) :: hp.nodeStack } jh) =
        some (.ext .unit, endSt) ∧
      endSt.jvmHeap = jh ∧
      endSt.heap = { hp with nodeStack := (children, handler?) :: hp.nodeStack })
    (hemit : hpAfter = emitMosaicNode hp (.column children handler?)) :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) (f + 1) prog pc
        (.invokestatic "com/jakewharton/mosaic/ui/Column" "Column"
          "(Lcom/jakewharton/mosaic/modifier/Modifier;Lcom/jakewharton/mosaic/ui/Arrangement$Vertical;Lcom/jakewharton/mosaic/ui/Alignment$Horizontal;Lkotlin/jvm/functions/Function3;Landroidx/compose/runtime/Composer;II)V" :: rest)
        ⟨pc, dfltV :: chV :: .ext .composer :: .ext (.closureRef cid) :: alignV :: arrV :: .ext (.modifier handler?) :: stk,
          locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, stk, locs, jh, hpAfter⟩ := by
  obtain ⟨endSt, hrun, hjh', hhp'⟩ := hbody
  subst hemit
  have hstep : (mkCalcHooks calcProgLookup (d + 1) subFuel).stepInvokeStatic
      ⟨pc, dfltV :: chV :: .ext .composer :: .ext (.closureRef cid) :: alignV :: arrV :: .ext (.modifier handler?) :: stk,
        locs, jh, hp⟩
      "com/jakewharton/mosaic/ui/Column" "Column"
      "(Lcom/jakewharton/mosaic/modifier/Modifier;Lcom/jakewharton/mosaic/ui/Arrangement$Vertical;Lcom/jakewharton/mosaic/ui/Alignment$Horizontal;Lkotlin/jvm/functions/Function3;Landroidx/compose/runtime/Composer;II)V" =
      .inl (some ⟨pc + 1, stk, locs, jh, emitMosaicNode hp (.column children handler?)⟩) := by
    conv => lhs; whnf
    dsimp only
    rw [hclos]
    dsimp only [List.cons_append]
    rw [show calcProgLookup "CalculatorScreenKt.CalculatorScreen$lambda$1" =
        some CalculatorScreen_lambda_1_prog from rfl]
    dsimp only
    unfold_locals_priv
    dsimp only [initCalcJvmState, Jvm.initJvmState, List.foldl] at hrun ⊢
    rw [hrun]
    dsimp only
    rw [hhp', hjh']
  have hs : Jvm.stepInstr (mkCalcHooks calcProgLookup (d + 1) subFuel)
      (.invokestatic "com/jakewharton/mosaic/ui/Column" "Column"
        "(Lcom/jakewharton/mosaic/modifier/Modifier;Lcom/jakewharton/mosaic/ui/Arrangement$Vertical;Lcom/jakewharton/mosaic/ui/Alignment$Horizontal;Lkotlin/jvm/functions/Function3;Landroidx/compose/runtime/Composer;II)V")
      ⟨pc, dfltV :: chV :: .ext .composer :: .ext (.closureRef cid) :: alignV :: arrV :: .ext (.modifier handler?) :: stk,
        locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, stk, locs, jh, emitMosaicNode hp (.column children handler?)⟩) := by
    dsimp only [Jvm.stepInstr, Jvm.stepInvokeStaticGeneric]
    exact hstep
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks calcProgLookup (d + 1) subFuel)
    rfl (by simp) hs rfl

/-- Expected emitted Mosaic nodes for `CalculatorScreen(state, ...)` given key handler closure id. -/
def calculatorScreenMosaicNode (cSt : CalculatorState) (keyHandlerCid : Nat) : Mosaic.MosaicNode :=
  .column
    [ .text "=== Calculator ==="
    , .text s!"> {formatDisplayLineModel cSt}"
    , .row [.text "[7] [8] [9] [/]"] none
    , .row [.text "[4] [5] [6] [*]"] none
    , .row [.text "[1] [2] [3] [-]"] none
    , .row [.text "[0] [C] [=] [+]"] none
    ]
    (some keyHandlerCid)

private theorem parseTags_bsm00 :
    Jvm.parseMethodParamTags "(Lkotlin/jvm/functions/Function1;)Lkotlin/jvm/functions/Function1;" = ['L'] := by
  decide

private theorem parseTags_bsm1 :
    Jvm.parseMethodParamTags
      "(Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorState;)Lkotlin/jvm/functions/Function3;" = ['L'] := by
  decide

set_option maxRecDepth 2048 in
private theorem parseTags_bsm2 :
    Jvm.parseMethodParamTags
      "(Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorState;Lkotlin/jvm/functions/Function1;Lcom/jakewharton/mosaic/modifier/Modifier;II)Lkotlin/jvm/functions/Function2;" =
      ['L', 'L', 'L', 'I', 'I'] := by
  decide

private theorem lookup_screen_keyHandler (closures : Array (String × List JvmVal))
    (onKey : JvmVal) (cSt : CalculatorState) :
    let closures1 := closures.push ("CalculatorScreenKt.CalculatorScreen$lambda$0$0", [onKey])
    let closures2 := closures1.push ("CalculatorScreenKt.CalculatorScreen$lambda$1", [.ext (.calcState cSt)])
    closures2[closures.size]? = some ("CalculatorScreenKt.CalculatorScreen$lambda$0$0", [onKey]) := by
  intro closures1 closures2
  have hlt1 : closures.size < closures1.size := by simp [closures1]
  have hlt2 : closures.size < closures2.size := by simp [closures2]; omega
  rw [Array.getElem?_eq_getElem hlt2]
  simp only [closures2, closures1, Array.getElem_push_lt hlt1]
  rw [Array.getElem_push_eq]

private theorem lookup_screen_colBody (closures : Array (String × List JvmVal))
    (onKey : JvmVal) (cSt : CalculatorState) :
    let closures1 := closures.push ("CalculatorScreenKt.CalculatorScreen$lambda$0$0", [onKey])
    let closures2 := closures1.push ("CalculatorScreenKt.CalculatorScreen$lambda$1", [.ext (.calcState cSt)])
    closures2[closures1.size]? = some ("CalculatorScreenKt.CalculatorScreen$lambda$1", [.ext (.calcState cSt)]) := by
  intro closures1 closures2
  rw [Array.getElem?_eq_getElem (by simp [closures2])]
  rw [Array.getElem_push_eq]

private theorem setLocal_same (locs : Nat → JvmVal) (idx : Nat) (v : JvmVal) :
    setLocal locs idx v idx = v := by
  dsimp only [setLocal]
  split
  · rfl
  · next h => exact False.elim (h rfl)

private theorem setLocal_diff (locs : Nat → JvmVal) {idx k : Nat} (v : JvmVal)
    (h : (k == idx) = false) : setLocal locs idx v k = locs k := by
  have hne : k ≠ idx := fun hc => by subst hc; simp at h
  dsimp only [setLocal]
  split
  · next hc => exact False.elim (hne hc)
  · rfl

local macro "peel_loc" : tactic =>
  `(tactic| repeat (first | rw [setLocal_same] | rw [setLocal_diff _ _ rfl]))

private theorem traceEnabled_readRemember (m : Compose.ComposerModel JvmVal) :
    (Compose.readRememberSlot m).2.traceEnabled = m.traceEnabled := by
  dsimp only [Compose.readRememberSlot]
  cases m.groupStack with
  | nil => rfl
  | cons _ _ => dsimp only; split <;> rfl

private theorem traceEnabled_writeRemember (m : Compose.ComposerModel JvmVal) (v : JvmVal) :
    (Compose.writeRememberSlot m v).traceEnabled = m.traceEnabled := by
  dsimp only [Compose.writeRememberSlot]
  cases m.groupStack with
  | nil => rfl
  | cons _ _ => dsimp only; split <;> rfl

private theorem groupStack_head_checkChanged (m : Compose.ComposerModel JvmVal) (v : JvmVal)
    (k : Int32) (h : ∃ f rest, m.groupStack = f :: rest ∧ f.key = k) :
    ∃ f rest, (Compose.checkChangedSlot (Jvm.JvmVal.beqVal beqCalcExt) m v).2.groupStack = f :: rest ∧
      f.key = k := by
  rcases h with ⟨f, rest, hgs, hk⟩
  dsimp only [Compose.checkChangedSlot]
  rw [hgs]
  dsimp only
  split
  · split <;> exact ⟨_, rest, rfl, hk⟩
  · exact ⟨f, rest, hgs, hk⟩

private theorem groupStack_head_readRemember (m : Compose.ComposerModel JvmVal)
    (k : Int32) (h : ∃ f rest, m.groupStack = f :: rest ∧ f.key = k) :
    ∃ f rest, (Compose.readRememberSlot m).2.groupStack = f :: rest ∧ f.key = k := by
  rcases h with ⟨f, rest, hgs, hk⟩
  dsimp only [Compose.readRememberSlot]
  rw [hgs]
  dsimp only
  split
  · exact ⟨_, rest, rfl, hk⟩
  · exact ⟨f, rest, hgs, hk⟩

private theorem groupStack_head_writeRemember (m : Compose.ComposerModel JvmVal) (v : JvmVal)
    (k : Int32) (h : ∃ f rest, m.groupStack = f :: rest ∧ f.key = k) :
    ∃ f rest, (Compose.writeRememberSlot m v).groupStack = f :: rest ∧ f.key = k := by
  rcases h with ⟨f, rest, hgs, hk⟩
  dsimp only [Compose.writeRememberSlot]
  rw [hgs]
  dsimp only
  split
  · exact ⟨_, rest, rfl, hk⟩
  · exact ⟨f, rest, hgs, hk⟩

private theorem endRestartGroup_fst_readRemember (m : Compose.ComposerModel JvmVal)
    (k : Int32) (h : ∃ f rest, m.groupStack = f :: rest ∧ f.key = k) :
    (Compose.endRestartGroup (Compose.readRememberSlot m).2).1 = some k := by
  rcases groupStack_head_readRemember m k h with ⟨f, rest, hgs, hk⟩
  dsimp only [Compose.endRestartGroup]
  rw [hgs]
  simp [hk]

private theorem endRestartGroup_fst_writeRemember (m : Compose.ComposerModel JvmVal) (v : JvmVal)
    (k : Int32) (h : ∃ f rest, m.groupStack = f :: rest ∧ f.key = k) :
    (Compose.endRestartGroup (Compose.writeRememberSlot m v)).1 = some k := by
  rcases groupStack_head_writeRemember m v k h with ⟨f, rest, hgs, hk⟩
  dsimp only [Compose.endRestartGroup]
  rw [hgs]
  simp [hk]

/-- Execute `CalculatorScreen` in initial insertion mode (`ch = 432`, `defF = 0`),
creating the `onKeyEvent` wrapper closure, emitting the Mosaic tree, and registering group `2094116101`. -/
theorem CalculatorScreen_initial_equiv (d subFuel fuel : Nat)
    (hd : 3 ≤ d) (hsub : 110 ≤ subFuel) (hf : 150 ≤ fuel)
    (cSt : CalculatorState) (onKey : JvmVal) (honKey : onKey.isNull = false)
    (hp : CalcHeap) (jh : Jvm.JvmHeap CalcExt)
    (htrace : hp.composer.traceEnabled = false)
    (hGroups : hp.composer.groups = [] ∨
      ∃ gApp, hp.composer.groups = [gApp] ∧ gApp.key = (54337357 : Int32))
    (herrSwitch : ∃ errAddr,
      jh.getStatic? "com/alexvanyo/composelife/mosaiccalculator/CalculatorEngineKt$WhenMappings"
        "$EnumSwitchMapping$1" = some (.heapRef errAddr) ∧
      jh.get? errAddr = some (.intArray #[1, 2]))
    (hstat : ∀ cls fld,
      cls ≠ "com/alexvanyo/composelife/mosaiccalculator/CalculatorEngineKt$WhenMappings" →
      cls ≠ "ComposableSingletons$CalculatorScreenKt" →
      jh.getStatic? cls fld = none)
    (hsing : HasSingletonRowLambdas jh hp.closures) :
    let modV : JvmVal := .ext (.modifier none)
    let cidKey := hp.closures.size
    let cidCol := cidKey + 1
    let cidRestart := cidCol + 1
    let r1 := Compose.startRestartGroup hp.composer 2094116101
    let r2 := (Compose.checkChangedSlot (Jvm.JvmVal.beqVal beqCalcExt) r1 (.ext (.calcState cSt))).2
    let r3 := (Compose.readRememberSlot r2).2
    let r4 := Compose.writeRememberSlot r3 (.ext (.closureRef cidKey))
    let r5 := (Compose.endRestartGroup r4).2
    let compEnd := Compose.setGroupRestartClosure r5 2094116101 (.ext (.closureRef cidRestart))
    let closuresEnd :=
      ((hp.closures.push ("CalculatorScreenKt.CalculatorScreen$lambda$0$0", [onKey])).push
        ("CalculatorScreenKt.CalculatorScreen$lambda$1", [.ext (.calcState cSt)])).push
        ("CalculatorScreenKt.CalculatorScreen$lambda$2",
          [.ext (.calcState cSt), onKey, modV, .i32 432, .i32 0])
    let hpCol := { hp with
      composer := r4
      closures := (hp.closures.push ("CalculatorScreenKt.CalculatorScreen$lambda$0$0", [onKey])).push
        ("CalculatorScreenKt.CalculatorScreen$lambda$1", [.ext (.calcState cSt)]) }
    let node := calculatorScreenMosaicNode cSt cidKey
    ∃ endSt,
      Jvm.runJvmRes (mkCalcHooks calcProgLookup d subFuel) fuel CalculatorScreen_prog
          (initCalcJvmState
            [(0, .ext (.calcState cSt)), (1, onKey), (2, modV), (3, .ext .composer),
             (4, .i32 432), (5, .i32 0)]
            hp jh) =
        some (.unit, endSt) ∧
      endSt.jvmHeap = jh ∧
      endSt.heap = { emitMosaicNode hpCol node with composer := compEnd, closures := closuresEnd } := by
  obtain ⟨d', rfl⟩ := Nat.exists_eq_add_of_le' hd
  obtain ⟨kF, rfl⟩ := Nat.exists_eq_add_of_le' hf
  have hcompStatic : jh.getStatic? "androidx/compose/runtime/Composer" "Companion" = none :=
    hstat _ _ (by decide) (by decide)
  let modV : JvmVal := .ext (.modifier none)
  let r1 := Compose.startRestartGroup hp.composer 2094116101
  let r2 := (Compose.checkChangedSlot (Jvm.JvmVal.beqVal beqCalcExt) r1 (.ext (.calcState cSt))).2
  let r3 := (Compose.readRememberSlot r2).2
  let cidKey := hp.closures.size
  let r4 := Compose.writeRememberSlot r3 (.ext (.closureRef cidKey))
  let hpMid : CalcHeap := { hp with
    composer := r4
    closures := (hp.closures.push ("CalculatorScreenKt.CalculatorScreen$lambda$0$0", [onKey])).push
      ("CalculatorScreenKt.CalculatorScreen$lambda$1", [.ext (.calcState cSt)]) }
  have hChg1 : (Compose.checkChangedSlot (Jvm.JvmVal.beqVal beqCalcExt) r1 (.ext (.calcState cSt))).1 = true := by
    dsimp only [r1, Compose.startRestartGroup, Compose.checkChangedSlot]
    rcases hGroups with hg | ⟨gApp, hg, hgk⟩
    · rw [hg]
      unfold_locals_priv
      unfold_locals_priv
      rfl
    · rw [hg]
      have hne : (gApp.key == (2094116101 : Int32)) = false := by rw [hgk]; decide
      unfold_locals_priv
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      unfold_locals_priv
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      unfold_locals_priv
      rfl
  have hEmpty1 : (Compose.readRememberSlot r2).1 = none := by
    dsimp only [r2, r1, Compose.startRestartGroup, Compose.checkChangedSlot, Compose.readRememberSlot]
    rcases hGroups with hg | ⟨gApp, hg, hgk⟩
    · rw [hg]
      unfold_locals_priv
      unfold_locals_priv
      unfold_locals_priv; try dsimp only
      rfl
    · rw [hg]
      have hne : (gApp.key == (2094116101 : Int32)) = false := by rw [hgk]; decide
      have heSelf : ((2094116101 : Int32) == (2094116101 : Int32)) = true := rfl
      unfold_locals_priv
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      unfold_locals_priv; try dsimp only
      simp only [hne, Bool.false_eq_true, ↓reduceIte, heSelf, List.getElem?_nil]
      unfold_locals_priv; try dsimp only
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      unfold_locals_priv; try dsimp only
      simp only [heSelf, ↓reduceIte]
      rfl
  have htr2 : r2.traceEnabled = false := by
    dsimp only [r2, r1, Compose.startRestartGroup, Compose.checkChangedSlot]
    rcases hGroups with hg | ⟨gApp, hg, hgk⟩
    · rw [hg]
      unfold_locals_priv
      unfold_locals_priv; try dsimp only
      exact htrace
    · rw [hg]
      have hne : (gApp.key == (2094116101 : Int32)) = false := by rw [hgk]; decide
      unfold_locals_priv
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      unfold_locals_priv; try dsimp only
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      exact htrace
  have htr4 : hpMid.composer.traceEnabled = false := by
    dsimp only [hpMid, r4, r3]
    rw [traceEnabled_writeRemember, traceEnabled_readRemember]
    exact htr2
  have hsingMid : HasSingletonRowLambdas jh hpMid.closures := by
    obtain ⟨id0, id1, id2, id3, hs0, hs1, hs2, hs3, hc0, hc1, hc2, hc3⟩ := hsing
    have hlt0 : id0 < hp.closures.size := (Array.getElem?_eq_some_iff.mp hc0).1
    have hlt1 : id1 < hp.closures.size := (Array.getElem?_eq_some_iff.mp hc1).1
    have hlt2 : id2 < hp.closures.size := (Array.getElem?_eq_some_iff.mp hc2).1
    have hlt3 : id3 < hp.closures.size := (Array.getElem?_eq_some_iff.mp hc3).1
    refine ⟨id0, id1, id2, id3, hs0, hs1, hs2, hs3, ?_, ?_, ?_, ?_⟩
    · dsimp only [hpMid]
      rw [Array.getElem?_push_lt (by simp; omega), Array.getElem_push_lt hlt0, ← Array.getElem?_eq_getElem hlt0]
      exact hc0
    · dsimp only [hpMid]
      rw [Array.getElem?_push_lt (by simp; omega), Array.getElem_push_lt hlt1, ← Array.getElem?_eq_getElem hlt1]
      exact hc1
    · dsimp only [hpMid]
      rw [Array.getElem?_push_lt (by simp; omega), Array.getElem_push_lt hlt2, ← Array.getElem?_eq_getElem hlt2]
      exact hc2
    · dsimp only [hpMid]
      rw [Array.getElem?_push_lt (by simp; omega), Array.getElem_push_lt hlt3, ← Array.getElem?_eq_getElem hlt3]
      exact hc3
  have hLambda1 := CalculatorScreen_lambda_1_equiv (d' + 2) subFuel subFuel (by omega) (by omega) hsub
    cSt jh { hpMid with nodeStack := ([], some cidKey) :: hpMid.nodeStack } htr4
    [] (some cidKey) hpMid.nodeStack rfl herrSwitch hstat hsingMid
  suffices h : ∃ endSt,
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d' + 3) subFuel) (kF + 150)
          CalculatorScreen_prog 0 CalculatorScreen_prog
          (initCalcJvmState
            [(0, .ext (.calcState cSt)), (1, onKey), (2, modV), (3, .ext .composer),
             (4, .i32 432), (5, .i32 0)]
            hp jh) =
        some (.unit, endSt) ∧
      endSt.jvmHeap = jh ∧
      endSt.heap = { emitMosaicNode hpMid (calculatorScreenMosaicNode cSt cidKey) with
        composer := Compose.setGroupRestartClosure (Compose.endRestartGroup r4).2 2094116101
          (.ext (.closureRef (hp.closures.size + 2)))
        closures := hpMid.closures.push
          ("CalculatorScreenKt.CalculatorScreen$lambda$2",
            [.ext (.calcState cSt), onKey, modV, .i32 432, .i32 0]) } by
    obtain ⟨endSt, h1, h2, h3⟩ := h
    exact ⟨endSt, Jvm.runJvmRes_of_runJvmResFast0 _ _ _ _ _ rfl h1, h2, h3⟩
  dsimp only [initCalcJvmState, Jvm.initJvmState, List.foldl]
  let locs0 : Nat → JvmVal :=
    @setLocal CalcExt
      (@setLocal CalcExt
        (@setLocal CalcExt
          (@setLocal CalcExt
            (@setLocal CalcExt
              (@setLocal CalcExt (fun _ => .i32 0) 0 (.ext (.calcState cSt)))
              1 onKey)
            2 modV)
          3 (.ext .composer))
        4 (.i32 432))
      5 (.i32 0)
  have hl0 : locs0 0 = .ext (.calcState cSt) := rfl
  have hl1 : locs0 1 = onKey := rfl
  have hl2 : locs0 2 = modV := rfl
  have hl3 : locs0 3 = .ext .composer := rfl
  have hl4 : locs0 4 = .i32 432 := rfl
  have hl5 : locs0 5 = .i32 0 := rfl
  change ∃ endSt,
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d' + 3) subFuel) (kF + 150)
          CalculatorScreen_prog 0 CalculatorScreen_prog ⟨0, [], locs0, jh, hp⟩ =
        some (.unit, endSt) ∧
      endSt.jvmHeap = jh ∧
      endSt.heap = { emitMosaicNode hpMid (calculatorScreenMosaicNode cSt cidKey) with
        composer := Compose.setGroupRestartClosure (Compose.endRestartGroup r4).2 2094116101
          (.ext (.closureRef (hp.closures.size + 2)))
        closures := hpMid.closures.push
          ("CalculatorScreenKt.CalculatorScreen$lambda$2",
            [.ext (.calcState cSt), onKey, modV, .i32 432, .i32 0]) }
  dsimp only [CalculatorScreen_prog]
  rw [runFast_aload, hl0, runFast_ldcStr, runFast_checkNotNullParam]
  rw [runFast_aload, hl1, runFast_ldcStr, runFast_checkNotNull' (d' + 2) subFuel _ _ _ honKey]
  rw [runFast_aload, hl3, runFast_iconst, runFast_startRestartGroup, runFast_astore]
  rw [runFast_aload]; peel_loc; rw [runFast_ldcStr, runFast_sourceInfo]
  rw [runFast_iload]; peel_loc; rw [hl4, runFast_istore]
  rw [runFast_iload]; peel_loc; rw [hl4, runFast_iconst, runFast_iand, runFast_ifne_zero']
  rw [runFast_iload]; peel_loc; rw [runFast_iload]; peel_loc; rw [hl4, runFast_iconst, runFast_iand, runFast_ifne_zero']
  rw [runFast_aload]; peel_loc; rw [runFast_aload]; peel_loc; rw [hl0, runFast_composerChanged]
  dsimp only
  rw [show Compose.startRestartGroup hp.composer (UInt32.toInt32 2094116101) = r1 from rfl]
  rw [hChg1]
  simp only [↓reduceIte]
  rw [runFast_goto']
  dsimp only [CalculatorScreen_prog, List.drop]
  rw [runFast_ifeq_nonzero (by decide)]
  rw [runFast_iconst, runFast_goto']
  dsimp only [CalculatorScreen_prog, List.drop]
  rw [runFast_ior, runFast_istore]
  rw [runFast_iload]; peel_loc; rw [hl4, runFast_iconst, runFast_iand, runFast_ifne_nonzero' (by decide)]
  dsimp only [CalculatorScreen_prog, List.drop]
  rw [runFast_iload]; peel_loc; rw [hl5, runFast_iconst, runFast_iand, runFast_ifeq_zero]
  dsimp only [CalculatorScreen_prog, List.drop]
  rw [runFast_iload]; peel_loc; rw [hl4, runFast_iconst, runFast_iand, runFast_ifne_nonzero' (by decide)]
  dsimp only [CalculatorScreen_prog, List.drop]
  rw [runFast_aload]; peel_loc; rw [runFast_iload]; peel_loc; rw [runFast_iconst, runFast_iand, runFast_iconst]
  rw [runFast_if_icmpeq_ne (by decide)]
  rw [runFast_iconst, runFast_goto']
  dsimp only [CalculatorScreen_prog, List.drop]
  rw [runFast_iload]; peel_loc; rw [runFast_iconst, runFast_iand, runFast_shouldExecute']
  dsimp only
  have hsh : Compose.shouldExecute r2 (((1 : UInt32) != 0)) ((432 ||| 4) &&& (1 : UInt32)).toInt32 = true := by
    simp [Compose.shouldExecute]
  rw [show (Compose.checkChangedSlot (Jvm.JvmVal.beqVal beqCalcExt) r1 (.ext (.calcState cSt))).2 = r2 from rfl, hsh]
  simp only [↓reduceIte]
  rw [runFast_ifeq_nonzero (by decide)]
  rw [runFast_iload]; peel_loc; rw [hl5, runFast_iconst, runFast_iand, runFast_ifeq_zero]
  dsimp only [CalculatorScreen_prog, List.drop]
  rw [runFast_isTraceInProgress' (d' + 2) subFuel _ _ _ htr2, runFast_ifeq_zero]
  dsimp only [CalculatorScreen_prog, List.drop]
  rw [runFast_aload]; peel_loc; rw [hl2, runFast_aload]; peel_loc; rw [runFast_iconst, runFast_ldcStr, runFast_sourceInfoMarkerStart]
  rw [runFast_aload]; peel_loc; rw [runFast_astore, runFast_iload]; peel_loc; rw [runFast_iconst, runFast_iand, runFast_iconst]
  rw [runFast_if_icmpne_ne' (by decide)]
  dsimp only [CalculatorScreen_prog, List.drop]
  rw [runFast_iconst]
  rw [runFast_istore, runFast_iconst, runFast_istore]
  rw [runFast_aload]; peel_loc; rw [runFast_rememberedValue]
  dsimp only
  rw [hEmpty1]
  dsimp only [Option.getD]
  rw [runFast_astore, runFast_iconst, runFast_istore]
  rw [runFast_iload]; peel_loc; rw [runFast_ifne_zero']
  rw [runFast_aload]; peel_loc; rw [runFast_getComposerCompanion hcompStatic, runFast_getEmpty']
  rw [runFast_if_acmpne_ext rfl]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [runFast_astore, runFast_iconst, runFast_istore, runFast_aload]; peel_loc; rw [hl1]
  rw [runFast_invokedynamic_bsm1 parseTags_bsm00 bsm_CalculatorScreen_lambda_0_0]
  dsimp only [allocClosure]
  rw [runFast_aload]; peel_loc; rw [runFast_swap, runFast_astore]
  rw [runFast_aload]; peel_loc; rw [runFast_aload]; peel_loc; rw [runFast_updateRememberedValue]
  rw [runFast_aload]; peel_loc; rw [runFast_goto']
  dsimp only [CalculatorScreen_prog, List.drop]
  rw [runFast_nop, runFast_nop, runFast_checkCast_ext rfl, runFast_astore]
  rw [runFast_aload]; peel_loc; rw [runFast_sourceInfoMarkerEnd]
  rw [runFast_aload]; peel_loc; rw [runFast_onKeyEvent]
  rw [runFast_aconstNull, runFast_aconstNull, runFast_iconst, runFast_iconst, runFast_aload]; peel_loc; rw [hl0]
  rw [runFast_invokedynamic_bsm1 parseTags_bsm1 bsm_CalculatorScreen_lambda_1]
  dsimp only [allocClosure]
  rw [runFast_aload]; peel_loc; rw [runFast_iconst, runFast_rememberComposableLambda, runFast_checkCast_ext rfl]
  rw [runFast_aload]; peel_loc; rw [runFast_iconst, runFast_iconst]
  rw [runFast_column_lambda1 (d' + 2) subFuel _ _ (hp.closures.push
      ("CalculatorScreenKt.CalculatorScreen$lambda$0$0", [onKey])).size
      (lookup_screen_colBody hp.closures onKey cSt) hLambda1 rfl]
  simp only [List.nil_append]
  rw [show (emitMosaicNode hpMid (.column
      [ .text "=== Calculator ==="
      , .text s!"> {formatDisplayLineModel cSt}"
      , .row [.text "[7] [8] [9] [/]"] none
      , .row [.text "[4] [5] [6] [*]"] none
      , .row [.text "[1] [2] [3] [-]"] none
      , .row [.text "[0] [C] [=] [+]"] none
      ] (some cidKey))) = emitMosaicNode hpMid (calculatorScreenMosaicNode cSt cidKey) from rfl]
  rw [runFast_isTraceInProgress' (d' + 2) subFuel _ _ _
    (by dsimp only [emitMosaicNode, hpMid]; cases hp.nodeStack <;> exact htr4), runFast_ifeq_zero]
  dsimp only [CalculatorScreen_prog, List.drop]
  rw [runFast_aload]; peel_loc; rw [runFast_endRestartGroup]
  dsimp only
  have hr4End : (Compose.endRestartGroup r4).1 = some 2094116101 := by
    dsimp only [r4]
    exact endRestartGroup_fst_writeRemember r3 (.ext (.closureRef cidKey)) 2094116101
      (groupStack_head_readRemember r2 2094116101
        (groupStack_head_checkChanged r1 (.ext (.calcState cSt)) 2094116101 ⟨_, _, rfl, rfl⟩))
  have hKeyEnd : (Compose.endRestartGroup (emitMosaicNode hpMid (calculatorScreenMosaicNode cSt cidKey)).composer).1 =
      some 2094116101 := by
    dsimp only [emitMosaicNode, hpMid]
    cases hp.nodeStack <;> exact hr4End
  rw [hKeyEnd]
  dsimp only
  rw [runFast_dup, runFast_ifnull_fallthrough' rfl]
  rw [runFast_aload]; peel_loc; rw [hl0, runFast_aload]; peel_loc; rw [hl1, runFast_aload]; peel_loc; rw [hl2]
  rw [runFast_iload]; peel_loc; rw [hl4, runFast_iload]; peel_loc; rw [hl5]
  rw [runFast_invokedynamic_bsm5 parseTags_bsm2 bsm_CalculatorScreen_lambda_2]
  dsimp only [allocClosure]
  rw [runFast_updateScope, runFast_goto']
  dsimp only [CalculatorScreen_prog, List.drop]
  rw [runFast_vreturn']
  refine ⟨_, rfl, rfl, ?_⟩
  cases hns : hp.nodeStack <;>
    (dsimp only [emitMosaicNode, hpMid, calculatorScreenMosaicNode, cidKey]
     rw [hns]
     dsimp only
     rw [Array.size_push, Array.size_push])

/-- Recompose `CalculatorScreen` (`comp.inserting = false`, `ch = 432`, `defF = 0`);
reuses the remembered key handler closure slot and re-emits the updated Mosaic tree. -/
theorem CalculatorScreen_recompose_equiv (d subFuel fuel : Nat)
    (hd : 3 ≤ d) (hsub : 110 ≤ subFuel) (hf : 150 ≤ fuel)
    (oldSt cSt : CalculatorState) (hne : oldSt ≠ cSt) (onKey : JvmVal) (honKey : onKey.isNull = false) (cidKey : Nat)
    (hp : CalcHeap) (jh : Jvm.JvmHeap CalcExt)
    (_hins : hp.composer.inserting = false)
    (htrace : hp.composer.traceEnabled = false)
    (gScr : Compose.GroupEntry JvmVal)
    (hgScrKey : gScr.key = (2094116101 : Int32))
    (hgScrSlots : gScr.slots = [.ext (.calcState oldSt), .ext (.closureRef cidKey)])
    (hGroups : hp.composer.groups = [gScr] ∨
      ∃ gApp, hp.composer.groups = [gApp, gScr] ∧ gApp.key = (54337357 : Int32))
    (herrSwitch : ∃ errAddr,
      jh.getStatic? "com/alexvanyo/composelife/mosaiccalculator/CalculatorEngineKt$WhenMappings"
        "$EnumSwitchMapping$1" = some (.heapRef errAddr) ∧
      jh.get? errAddr = some (.intArray #[1, 2]))
    (hstat : ∀ cls fld,
      cls ≠ "com/alexvanyo/composelife/mosaiccalculator/CalculatorEngineKt$WhenMappings" →
      cls ≠ "ComposableSingletons$CalculatorScreenKt" →
      jh.getStatic? cls fld = none)
    (hsing : HasSingletonRowLambdas jh hp.closures) :
    let modV : JvmVal := .ext (.modifier none)
    let r1 := Compose.startRestartGroup hp.composer 2094116101
    let r2 := (Compose.checkChangedSlot (Jvm.JvmVal.beqVal beqCalcExt) r1 (.ext (.calcState cSt))).2
    let r3 := (Compose.readRememberSlot r2).2
    let r4 := (Compose.endRestartGroup r3).2
    let compEnd := Compose.setGroupRestartClosure r4 2094116101 (.ext (.closureRef (hp.closures.size + 1)))
    let hpMid : CalcHeap := { hp with
      composer := r3
      closures := hp.closures.push ("CalculatorScreenKt.CalculatorScreen$lambda$1", [.ext (.calcState cSt)]) }
    let closuresEnd := hpMid.closures.push
      ("CalculatorScreenKt.CalculatorScreen$lambda$2", [.ext (.calcState cSt), onKey, modV, .i32 432, .i32 0])
    ∃ endSt,
      Jvm.runJvmRes (mkCalcHooks calcProgLookup d subFuel) fuel CalculatorScreen_prog
          (initCalcJvmState
            [(0, .ext (.calcState cSt)), (1, onKey), (2, modV), (3, .ext .composer),
             (4, .i32 432), (5, .i32 0)]
            hp jh) =
        some (.unit, endSt) ∧
      endSt.jvmHeap = jh ∧
      endSt.heap = { emitMosaicNode hpMid (calculatorScreenMosaicNode cSt cidKey) with
        composer := compEnd, closures := closuresEnd } := by
  obtain ⟨d', rfl⟩ := Nat.exists_eq_add_of_le' hd
  obtain ⟨kF, rfl⟩ := Nat.exists_eq_add_of_le' hf
  have hcompStatic : jh.getStatic? "androidx/compose/runtime/Composer" "Companion" = none :=
    hstat _ _ (by decide) (by decide)
  let modV : JvmVal := .ext (.modifier none)
  let r1 := Compose.startRestartGroup hp.composer 2094116101
  let r2 := (Compose.checkChangedSlot (Jvm.JvmVal.beqVal beqCalcExt) r1 (.ext (.calcState cSt))).2
  let r3 := (Compose.readRememberSlot r2).2
  let hpMid : CalcHeap := { hp with
    composer := r3
    closures := hp.closures.push ("CalculatorScreenKt.CalculatorScreen$lambda$1", [.ext (.calcState cSt)]) }
  have hChgVal : (Compose.checkChangedSlot (Jvm.JvmVal.beqVal beqCalcExt) r1 (.ext (.calcState cSt))).1 =
      !(oldSt == cSt) := by
    dsimp only [Compose.checkChangedSlot, r1, Compose.startRestartGroup]
    rcases hGroups with hg | ⟨gApp, hg, hgk⟩
    · rw [hg]
      have he : (gScr.key == (2094116101 : Int32)) = true := by rw [hgScrKey]; decide
      unfold_locals_priv
      simp only [he, ↓reduceIte]
      unfold_locals_priv; try dsimp only
      simp only [he, ↓reduceIte, hgScrSlots, List.getElem?_cons_zero, Jvm.JvmVal.beqVal, beqCalcExt]
      by_cases h : oldSt = cSt <;> simp [h]
    · rw [hg]
      have hne : (gApp.key == (2094116101 : Int32)) = false := by rw [hgk]; decide
      have he : (gScr.key == (2094116101 : Int32)) = true := by rw [hgScrKey]; decide
      unfold_locals_priv
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      unfold_locals_priv
      simp only [he, ↓reduceIte]
      unfold_locals_priv
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      unfold_locals_priv
      simp only [he, ↓reduceIte, hgScrSlots, List.getElem?_cons_zero, Jvm.JvmVal.beqVal, beqCalcExt]
      by_cases h : oldSt = cSt <;> simp [h]
  have hReadKey : (Compose.readRememberSlot r2).1 = some (.ext (.closureRef cidKey)) := by
    dsimp only [Compose.readRememberSlot, r2, Compose.checkChangedSlot, r1, Compose.startRestartGroup]
    rcases hGroups with hg | ⟨gApp, hg, hgk⟩
    · rw [hg]
      have he : (gScr.key == (2094116101 : Int32)) = true := by rw [hgScrKey]; decide
      unfold_locals_priv
      simp only [he, ↓reduceIte]
      unfold_locals_priv
      simp only [he, ↓reduceIte, hgScrSlots, List.getElem?_cons_zero]
      unfold_locals_priv; try dsimp only
      simp only [he, ↓reduceIte]
      unfold_locals_priv
      unfold_locals_priv; try dsimp only
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero]
    · rw [hg]
      have hne : (gApp.key == (2094116101 : Int32)) = false := by rw [hgk]; decide
      have he : (gScr.key == (2094116101 : Int32)) = true := by rw [hgScrKey]; decide
      unfold_locals_priv
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      unfold_locals_priv
      simp only [he, ↓reduceIte]
      unfold_locals_priv; try dsimp only
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      unfold_locals_priv
      simp only [he, ↓reduceIte, hgScrSlots, List.getElem?_cons_zero]
      unfold_locals_priv; try dsimp only
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      unfold_locals_priv
      simp only [he, ↓reduceIte]
      unfold_locals_priv; try dsimp only
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hShTrue : Compose.shouldExecute r2 ((1 : UInt32) != 0)
      ((432 ||| (if !(oldSt == cSt) then (4 : UInt32) else (2 : UInt32))) &&& (1 : UInt32)).toInt32 = true := by
    simp [Compose.shouldExecute]
  have htr2 : r2.traceEnabled = false := by
    dsimp only [r2, Compose.checkChangedSlot, r1, Compose.startRestartGroup]
    rcases hGroups with hg | ⟨gApp, hg, hgk⟩
    · rw [hg]
      have he : (gScr.key == (2094116101 : Int32)) = true := by rw [hgScrKey]; decide
      unfold_locals_priv
      simp only [he, ↓reduceIte]
      unfold_locals_priv; try dsimp only
      simp only [he, ↓reduceIte, hgScrSlots, List.getElem?_cons_zero]
      exact htrace
    · rw [hg]
      have hne : (gApp.key == (2094116101 : Int32)) = false := by rw [hgk]; decide
      have he : (gScr.key == (2094116101 : Int32)) = true := by rw [hgScrKey]; decide
      unfold_locals_priv
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      unfold_locals_priv
      simp only [he, ↓reduceIte]
      unfold_locals_priv; try dsimp only
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      unfold_locals_priv
      simp only [he, ↓reduceIte, hgScrSlots, List.getElem?_cons_zero]
      exact htrace
  have htr3 : hpMid.composer.traceEnabled = false := by
    dsimp only [hpMid, r3, Compose.readRememberSlot, r2, Compose.checkChangedSlot, r1, Compose.startRestartGroup]
    rcases hGroups with hg | ⟨gApp, hg, hgk⟩
    · rw [hg]
      have he : (gScr.key == (2094116101 : Int32)) = true := by rw [hgScrKey]; decide
      unfold_locals_priv
      simp only [he, ↓reduceIte]
      unfold_locals_priv
      simp only [he, ↓reduceIte, hgScrSlots, List.getElem?_cons_zero]
      unfold_locals_priv; try dsimp only
      simp only [he, ↓reduceIte]
      unfold_locals_priv
      exact htrace
    · rw [hg]
      have hne : (gApp.key == (2094116101 : Int32)) = false := by rw [hgk]; decide
      have he : (gScr.key == (2094116101 : Int32)) = true := by rw [hgScrKey]; decide
      unfold_locals_priv
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      unfold_locals_priv
      simp only [he, ↓reduceIte]
      unfold_locals_priv; try dsimp only
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      unfold_locals_priv
      simp only [he, ↓reduceIte, hgScrSlots, List.getElem?_cons_zero]
      unfold_locals_priv; try dsimp only
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      unfold_locals_priv
      simp only [he, ↓reduceIte]
      exact htrace
  have hsingMid : HasSingletonRowLambdas jh hpMid.closures := by
    obtain ⟨id0, id1, id2, id3, hs0, hs1, hs2, hs3, hc0, hc1, hc2, hc3⟩ := hsing
    have hlt0 : id0 < hp.closures.size := (Array.getElem?_eq_some_iff.mp hc0).1
    have hlt1 : id1 < hp.closures.size := (Array.getElem?_eq_some_iff.mp hc1).1
    have hlt2 : id2 < hp.closures.size := (Array.getElem?_eq_some_iff.mp hc2).1
    have hlt3 : id3 < hp.closures.size := (Array.getElem?_eq_some_iff.mp hc3).1
    refine ⟨id0, id1, id2, id3, hs0, hs1, hs2, hs3, ?_, ?_, ?_, ?_⟩
    · dsimp only [hpMid]; rw [Array.getElem?_push_lt hlt0, ← Array.getElem?_eq_getElem hlt0]; exact hc0
    · dsimp only [hpMid]; rw [Array.getElem?_push_lt hlt1, ← Array.getElem?_eq_getElem hlt1]; exact hc1
    · dsimp only [hpMid]; rw [Array.getElem?_push_lt hlt2, ← Array.getElem?_eq_getElem hlt2]; exact hc2
    · dsimp only [hpMid]; rw [Array.getElem?_push_lt hlt3, ← Array.getElem?_eq_getElem hlt3]; exact hc3
  have hLambda1 := CalculatorScreen_lambda_1_equiv (d' + 2) subFuel subFuel (by omega) (by omega) hsub
    cSt jh { hpMid with nodeStack := ([], some cidKey) :: hpMid.nodeStack } htr3
    [] (some cidKey) hpMid.nodeStack rfl herrSwitch hstat hsingMid
  suffices h : ∃ endSt,
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d' + 3) subFuel) (kF + 150)
          CalculatorScreen_prog 0 CalculatorScreen_prog
          (initCalcJvmState
            [(0, .ext (.calcState cSt)), (1, onKey), (2, modV), (3, .ext .composer),
             (4, .i32 432), (5, .i32 0)]
            hp jh) =
        some (.unit, endSt) ∧
      endSt.jvmHeap = jh ∧
      endSt.heap = { emitMosaicNode hpMid (calculatorScreenMosaicNode cSt cidKey) with
        composer := Compose.setGroupRestartClosure (Compose.endRestartGroup r3).2 2094116101
          (.ext (.closureRef (hp.closures.size + 1)))
        closures := hpMid.closures.push
          ("CalculatorScreenKt.CalculatorScreen$lambda$2",
            [.ext (.calcState cSt), onKey, modV, .i32 432, .i32 0]) } by
    obtain ⟨endSt, h1, h2, h3⟩ := h
    exact ⟨endSt, Jvm.runJvmRes_of_runJvmResFast0 _ _ _ _ _ rfl h1, h2, h3⟩
  dsimp only [initCalcJvmState, Jvm.initJvmState, List.foldl]
  let locs0 : Nat → JvmVal :=
    @setLocal CalcExt
      (@setLocal CalcExt
        (@setLocal CalcExt
          (@setLocal CalcExt
            (@setLocal CalcExt
              (@setLocal CalcExt (fun _ => .i32 0) 0 (.ext (.calcState cSt)))
              1 onKey)
            2 modV)
          3 (.ext .composer))
        4 (.i32 432))
      5 (.i32 0)
  have hl0 : locs0 0 = .ext (.calcState cSt) := rfl
  have hl1 : locs0 1 = onKey := rfl
  have hl2 : locs0 2 = modV := rfl
  have hl3 : locs0 3 = .ext .composer := rfl
  have hl4 : locs0 4 = .i32 432 := rfl
  have hl5 : locs0 5 = .i32 0 := rfl
  change ∃ endSt,
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d' + 3) subFuel) (kF + 150)
          CalculatorScreen_prog 0 CalculatorScreen_prog ⟨0, [], locs0, jh, hp⟩ =
        some (.unit, endSt) ∧
      endSt.jvmHeap = jh ∧
      endSt.heap = { emitMosaicNode hpMid (calculatorScreenMosaicNode cSt cidKey) with
        composer := Compose.setGroupRestartClosure (Compose.endRestartGroup r3).2 2094116101
          (.ext (.closureRef (hp.closures.size + 1)))
        closures := hpMid.closures.push
          ("CalculatorScreenKt.CalculatorScreen$lambda$2",
            [.ext (.calcState cSt), onKey, modV, .i32 432, .i32 0]) }
  dsimp only [CalculatorScreen_prog]
  rw [runFast_aload, hl0, runFast_ldcStr, runFast_checkNotNullParam]
  rw [runFast_aload, hl1, runFast_ldcStr, runFast_checkNotNull' (d' + 2) subFuel _ _ _ honKey]
  rw [runFast_aload, hl3, runFast_iconst, runFast_startRestartGroup, runFast_astore]
  rw [runFast_aload]; peel_loc; rw [runFast_ldcStr, runFast_sourceInfo]
  rw [runFast_iload]; peel_loc; rw [hl4, runFast_istore]
  rw [runFast_iload]; peel_loc; rw [hl4, runFast_iconst, runFast_iand, runFast_ifne_zero']
  rw [runFast_iload]; peel_loc; rw [runFast_iload]; peel_loc; rw [hl4, runFast_iconst, runFast_iand, runFast_ifne_zero']
  rw [runFast_aload]; peel_loc; rw [runFast_aload]; peel_loc; rw [hl0, runFast_composerChanged]
  dsimp only
  rw [show Compose.startRestartGroup hp.composer (UInt32.toInt32 2094116101) = r1 from rfl]
  rw [hChgVal]
  let dirtyV : UInt32 := if !(oldSt == cSt) then 436 else 434
  have hBody88 : ∀ (fuel88 : Nat), 80 ≤ fuel88 →
      ∀ (stk88 : Nat → JvmVal) (h6 : stk88 6 = .i32 dirtyV)
        (h0 : stk88 0 = .ext (.calcState cSt)) (h1 : stk88 1 = onKey) (h2 : stk88 2 = modV)
        (h3 : stk88 3 = .ext .composer) (h4 : stk88 4 = .i32 432) (h5 : stk88 5 = .i32 0),
      ∃ endSt,
        Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d' + 3) subFuel) fuel88
            CalculatorScreen_prog 88 (CalculatorScreen_prog.drop 88)
            ⟨88, [], stk88, jh, { hp with composer := r2 }⟩ =
          some (.unit, endSt) ∧
        endSt.jvmHeap = jh ∧
        endSt.heap = { emitMosaicNode hpMid (calculatorScreenMosaicNode cSt cidKey) with
          composer := Compose.setGroupRestartClosure (Compose.endRestartGroup r3).2 2094116101
            (.ext (.closureRef (hp.closures.size + 1)))
          closures := hpMid.closures.push
            ("CalculatorScreenKt.CalculatorScreen$lambda$2",
              [.ext (.calcState cSt), onKey, modV, .i32 432, .i32 0]) } := by
    intro fuel88 hf88 stk88 h6 h0 h1 h2 h3 h4 h5
    obtain ⟨k88, rfl⟩ := Nat.exists_eq_add_of_le' hf88
    have hmask : (dirtyV &&& (112 : UInt32)) ≠ (32 : UInt32) := by
      dsimp only [dirtyV]; split <;> decide
    dsimp only [CalculatorScreen_prog, List.drop]
    rw [runFast_iload, h5, runFast_iconst, runFast_iand, runFast_ifeq_zero]
    dsimp only [CalculatorScreen_prog, List.drop]
    rw [runFast_isTraceInProgress' (d' + 2) subFuel _ _ _ htr2, runFast_ifeq_zero]
    dsimp only [CalculatorScreen_prog, List.drop]
    rw [runFast_aload, h2, runFast_aload, h3, runFast_iconst, runFast_ldcStr, runFast_sourceInfoMarkerStart]
    rw [runFast_aload]; peel_loc; rw [h3, runFast_astore, runFast_iload]; peel_loc; rw [h6, runFast_iconst, runFast_iand, runFast_iconst]
    rw [runFast_if_icmpne_ne' hmask]
    dsimp only [CalculatorScreen_prog, List.drop]
    rw [runFast_iconst]
    rw [runFast_istore, runFast_iconst, runFast_istore]
    rw [runFast_aload]; peel_loc; rw [runFast_rememberedValue]
    dsimp only
    rw [hReadKey]
    dsimp only [Option.getD]
    rw [runFast_astore, runFast_iconst, runFast_istore]
    rw [runFast_iload]; peel_loc; rw [runFast_ifne_zero']
    rw [runFast_aload]; peel_loc; rw [runFast_getComposerCompanion hcompStatic, runFast_getEmpty']
    rw [runFast_if_acmpne_ext rfl]
    simp only [Bool.not_false, ↓reduceIte]
    dsimp only [CalculatorScreen_prog, List.drop]
    rw [runFast_aload]; peel_loc; rw [runFast_nop, runFast_nop, runFast_checkCast_ext rfl, runFast_astore]
    rw [runFast_aload]; peel_loc; rw [h3, runFast_sourceInfoMarkerEnd]
    rw [runFast_aload]; peel_loc; rw [runFast_onKeyEvent]
    rw [runFast_aconstNull, runFast_aconstNull, runFast_iconst, runFast_iconst, runFast_aload]; peel_loc; rw [h0]
    rw [runFast_invokedynamic_bsm1 parseTags_bsm1 bsm_CalculatorScreen_lambda_1]
    dsimp only [allocClosure]
    rw [runFast_aload]; peel_loc; rw [h3, runFast_iconst, runFast_rememberComposableLambda, runFast_checkCast_ext rfl]
    rw [runFast_aload]; peel_loc; rw [h3, runFast_iconst, runFast_iconst]
    rw [runFast_column_lambda1 (d' + 2) subFuel _ _ hp.closures.size
      (by
        dsimp only [hpMid]
        have hsz : hp.closures.size <
            (hp.closures.push ("CalculatorScreenKt.CalculatorScreen$lambda$1", [.ext (.calcState cSt)])).size := by
          simp
        rw [Array.getElem?_eq_getElem hsz, Array.getElem_push_eq])
      hLambda1 rfl]
    simp only [List.nil_append]
    rw [show (emitMosaicNode hpMid (.column
        [ .text "=== Calculator ==="
        , .text s!"> {formatDisplayLineModel cSt}"
        , .row [.text "[7] [8] [9] [/]"] none
        , .row [.text "[4] [5] [6] [*]"] none
        , .row [.text "[1] [2] [3] [-]"] none
        , .row [.text "[0] [C] [=] [+]"] none
        ] (some cidKey))) = emitMosaicNode hpMid (calculatorScreenMosaicNode cSt cidKey) from rfl]
    have htrMid : (emitMosaicNode hpMid (calculatorScreenMosaicNode cSt cidKey)).composer.traceEnabled = false := by
      dsimp only [emitMosaicNode]; cases hpMid.nodeStack <;> exact htr3
    rw [runFast_isTraceInProgress' (d' + 2) subFuel _ _ _ htrMid, runFast_ifeq_zero]
    dsimp only [CalculatorScreen_prog, List.drop]
    rw [runFast_aload]; peel_loc; rw [h3, runFast_endRestartGroup]
    dsimp only
    have hKeyEnd : (Compose.endRestartGroup (emitMosaicNode hpMid (calculatorScreenMosaicNode cSt cidKey)).composer).1 =
        some 2094116101 := by
      have hr3End : (Compose.endRestartGroup r3).1 = some 2094116101 := by
        dsimp only [r3]
        exact endRestartGroup_fst_readRemember r2 2094116101
          (groupStack_head_checkChanged r1 (.ext (.calcState cSt)) 2094116101 ⟨_, _, rfl, rfl⟩)
      dsimp only [emitMosaicNode, hpMid]
      cases hp.nodeStack <;> exact hr3End
    rw [hKeyEnd]
    dsimp only
    rw [runFast_dup, runFast_ifnull_fallthrough' rfl]
    rw [runFast_aload]; peel_loc; rw [h0, runFast_aload]; peel_loc; rw [h1, runFast_aload]; peel_loc; rw [h2]
    rw [runFast_iload]; peel_loc; rw [h4, runFast_iload]; peel_loc; rw [h5]
    rw [runFast_invokedynamic_bsm5 parseTags_bsm2 bsm_CalculatorScreen_lambda_2]
    dsimp only [allocClosure]
    rw [runFast_updateScope, runFast_goto']
    dsimp only [CalculatorScreen_prog, List.drop]
    rw [runFast_vreturn']
    refine ⟨_, rfl, rfl, ?_⟩
    cases hns : hp.nodeStack <;>
      (dsimp only [emitMosaicNode, hpMid, calculatorScreenMosaicNode]
       rw [hns]
       dsimp only
       rw [Array.size_push])
  have hbc : (oldSt == cSt) = false := beq_false_of_ne hne
  rw [hbc]
  simp only [Bool.not_false, ↓reduceIte]
  rw [runFast_goto']
  dsimp only [CalculatorScreen_prog, List.drop]
  rw [runFast_ifeq_nonzero (by decide), runFast_iconst, runFast_goto']
  dsimp only [CalculatorScreen_prog, List.drop]
  rw [runFast_ior, runFast_istore]
  rw [runFast_iload]; peel_loc; rw [hl4, runFast_iconst, runFast_iand, runFast_ifne_nonzero' (by decide)]
  dsimp only [CalculatorScreen_prog, List.drop]
  rw [runFast_iload]; peel_loc; rw [hl5, runFast_iconst, runFast_iand, runFast_ifeq_zero]
  dsimp only [CalculatorScreen_prog, List.drop]
  rw [runFast_iload]; peel_loc; rw [hl4, runFast_iconst, runFast_iand, runFast_ifne_nonzero' (by decide)]
  dsimp only [CalculatorScreen_prog, List.drop]
  rw [runFast_aload]; peel_loc; rw [runFast_iload]; peel_loc; rw [runFast_iconst, runFast_iand, runFast_iconst]
  rw [runFast_if_icmpeq_ne (by decide), runFast_iconst, runFast_goto']
  dsimp only [CalculatorScreen_prog, List.drop]
  rw [runFast_iload]; peel_loc; rw [runFast_iconst, runFast_iand, runFast_shouldExecute']
  dsimp only
  rw [hbc] at hShTrue
  simp only [Bool.not_false, ↓reduceIte] at hShTrue
  rw [show (Compose.checkChangedSlot (Jvm.JvmVal.beqVal beqCalcExt) r1 (.ext (.calcState cSt))).2 = r2 from rfl, hShTrue]
  simp only [↓reduceIte]
  rw [runFast_ifeq_nonzero (by decide)]
  exact hBody88 _ (by omega) _ (by peel_loc; dsimp only [dirtyV]; rw [hbc]; rfl)
    (by peel_loc; exact hl0) (by peel_loc; exact hl1) (by peel_loc; exact hl2)
    (by peel_loc) (by peel_loc; exact hl4) (by peel_loc; exact hl5)

/-- Parametric `skipToGroupEnd` equivalence for `CalculatorScreen` (`ch = 176 ∨ ch = 432`, `defF = 0`). -/
theorem CalculatorScreen_skip_equiv_ch (d subFuel fuel : Nat)
    (hd : 1 ≤ d) (hf : 80 ≤ fuel)
    (ch : UInt32) (hch : ch = 176 ∨ ch = 432)
    (cSt : CalculatorState) (onKey : JvmVal) (honKey : onKey.isNull = false) (cidKey : Nat)
    (hp : CalcHeap) (jh : Jvm.JvmHeap CalcExt)
    (hins : hp.composer.inserting = false)
    (gScr : Compose.GroupEntry JvmVal)
    (hgScrKey : gScr.key = (2094116101 : Int32))
    (hgScrSlots : gScr.slots = [.ext (.calcState cSt), .ext (.closureRef cidKey)])
    (hgScrClean : gScr.dirty = false)
    (hGroups : hp.composer.groups = [gScr] ∨
      ∃ gApp, hp.composer.groups = [gApp, gScr] ∧ gApp.key = (54337357 : Int32)) :
    let modV : JvmVal := .ext (.modifier none)
    let r1 := Compose.startRestartGroup hp.composer 2094116101
    let r2 := (Compose.checkChangedSlot (Jvm.JvmVal.beqVal beqCalcExt) r1 (.ext (.calcState cSt))).2
    let r3 := Compose.skipToGroupEnd r2
    let r4 := (Compose.endRestartGroup r3).2
    let compEnd := Compose.setGroupRestartClosure r4 2094116101 (.ext (.closureRef hp.closures.size))
    let closuresEnd := hp.closures.push
      ("CalculatorScreenKt.CalculatorScreen$lambda$2", [.ext (.calcState cSt), onKey, modV, .i32 ch, .i32 0])
    ∃ endSt,
      Jvm.runJvmRes (mkCalcHooks calcProgLookup d subFuel) fuel CalculatorScreen_prog
          (initCalcJvmState
            [(0, .ext (.calcState cSt)), (1, onKey), (2, modV), (3, .ext .composer),
             (4, .i32 ch), (5, .i32 0)]
            hp jh) =
        some (.unit, endSt) ∧
      endSt.jvmHeap = jh ∧
      endSt.heap = { hp with composer := compEnd, closures := closuresEnd } := by
  obtain ⟨d', rfl⟩ := Nat.exists_eq_add_of_le' hd
  obtain ⟨kF, rfl⟩ := Nat.exists_eq_add_of_le' hf
  let modV : JvmVal := .ext (.modifier none)
  let r1 := Compose.startRestartGroup hp.composer 2094116101
  let r2 := (Compose.checkChangedSlot (Jvm.JvmVal.beqVal beqCalcExt) r1 (.ext (.calcState cSt))).2
  let r3 := Compose.skipToGroupEnd r2
  have hChgFalse : (Compose.checkChangedSlot (Jvm.JvmVal.beqVal beqCalcExt) r1 (.ext (.calcState cSt))).1 = false := by
    dsimp only [Compose.checkChangedSlot, r1, Compose.startRestartGroup]
    rcases hGroups with hg | ⟨gApp, hg, hgk⟩
    · rw [hg]
      have he : (gScr.key == (2094116101 : Int32)) = true := by rw [hgScrKey]; decide
      unfold_locals_priv
      simp only [he, ↓reduceIte]
      unfold_locals_priv; try dsimp only
      simp only [he, ↓reduceIte, hgScrSlots, List.getElem?_cons_zero, Jvm.JvmVal.beqVal, beqCalcExt]
      simp
    · rw [hg]
      have hne : (gApp.key == (2094116101 : Int32)) = false := by rw [hgk]; decide
      have he : (gScr.key == (2094116101 : Int32)) = true := by rw [hgScrKey]; decide
      unfold_locals_priv
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      unfold_locals_priv
      simp only [he, ↓reduceIte]
      unfold_locals_priv
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      unfold_locals_priv
      simp only [he, ↓reduceIte, hgScrSlots, List.getElem?_cons_zero, Jvm.JvmVal.beqVal, beqCalcExt]
      simp
  have hShFalse : Compose.shouldExecute r2 false ((ch ||| (2 : UInt32)) &&& (1 : UInt32)).toInt32 = false := by
    dsimp only [Compose.shouldExecute, Compose.currentGroup?, r2, Compose.checkChangedSlot, r1,
      Compose.startRestartGroup]
    rcases hGroups with hg | ⟨gApp, hg, hgk⟩
    · rw [hg]
      have he : (gScr.key == (2094116101 : Int32)) = true := by rw [hgScrKey]; decide
      unfold_locals_priv
      simp only [hins, he, ↓reduceIte]
      unfold_locals_priv
      simp only [he, ↓reduceIte, hgScrSlots, List.getElem?_cons_zero]
      unfold_locals_priv
      simp only [he, ↓reduceIte]
      unfold_locals_priv
      simp only [hgScrClean]
      rcases hch with rfl | rfl <;> rfl
    · rw [hg]
      have hne : (gApp.key == (2094116101 : Int32)) = false := by rw [hgk]; decide
      have he : (gScr.key == (2094116101 : Int32)) = true := by rw [hgScrKey]; decide
      unfold_locals_priv
      simp only [hins, hne, Bool.false_eq_true, ↓reduceIte]
      unfold_locals_priv
      simp only [he, ↓reduceIte]
      unfold_locals_priv; try dsimp only
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      unfold_locals_priv
      simp only [he, ↓reduceIte, hgScrSlots, List.getElem?_cons_zero]
      unfold_locals_priv; try dsimp only
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      unfold_locals_priv
      simp only [he, ↓reduceIte]
      unfold_locals_priv; try dsimp only
      unfold_locals_priv; try dsimp only
      simp only [hgScrClean]
      rcases hch with rfl | rfl <;> rfl
  have hKeyEnd : (Compose.endRestartGroup r3).1 = some 2094116101 := by
    dsimp only [r3, Compose.skipToGroupEnd, r2, Compose.checkChangedSlot, r1, Compose.startRestartGroup]
    rcases hGroups with hg | ⟨gApp, hg, hgk⟩
    · rw [hg]
      have he : (gScr.key == (2094116101 : Int32)) = true := by rw [hgScrKey]; decide
      unfold_locals_priv
      simp only [he, ↓reduceIte]
      unfold_locals_priv; try dsimp only
      simp only [he, ↓reduceIte, hgScrSlots, List.getElem?_cons_zero]
      rfl
    · rw [hg]
      have hne : (gApp.key == (2094116101 : Int32)) = false := by rw [hgk]; decide
      have he : (gScr.key == (2094116101 : Int32)) = true := by rw [hgScrKey]; decide
      unfold_locals_priv
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      unfold_locals_priv
      simp only [he, ↓reduceIte]
      unfold_locals_priv; try dsimp only
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      unfold_locals_priv
      simp only [he, ↓reduceIte, hgScrSlots, List.getElem?_cons_zero]
      rfl
  suffices h : ∃ endSt,
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d' + 1) subFuel) (kF + 80)
          CalculatorScreen_prog 0 CalculatorScreen_prog
          (initCalcJvmState
            [(0, .ext (.calcState cSt)), (1, onKey), (2, modV), (3, .ext .composer),
             (4, .i32 ch), (5, .i32 0)]
            hp jh) =
        some (.unit, endSt) ∧
      endSt.jvmHeap = jh ∧
      endSt.heap = { hp with
        composer := Compose.setGroupRestartClosure (Compose.endRestartGroup r3).2 2094116101
          (.ext (.closureRef hp.closures.size))
        closures := hp.closures.push
          ("CalculatorScreenKt.CalculatorScreen$lambda$2",
            [.ext (.calcState cSt), onKey, modV, .i32 ch, .i32 0]) } by
    obtain ⟨endSt, h1, h2, h3⟩ := h
    exact ⟨endSt, Jvm.runJvmRes_of_runJvmResFast0 _ _ _ _ _ rfl h1, h2, h3⟩
  dsimp only [initCalcJvmState, Jvm.initJvmState, List.foldl]
  let locs0 : Nat → JvmVal :=
    @setLocal CalcExt
      (@setLocal CalcExt
        (@setLocal CalcExt
          (@setLocal CalcExt
            (@setLocal CalcExt
              (@setLocal CalcExt (fun _ => .i32 0) 0 (.ext (.calcState cSt)))
              1 onKey)
            2 modV)
          3 (.ext .composer))
        4 (.i32 ch))
      5 (.i32 0)
  have hl0 : locs0 0 = .ext (.calcState cSt) := rfl
  have hl1 : locs0 1 = onKey := rfl
  have hl2 : locs0 2 = modV := rfl
  have hl3 : locs0 3 = .ext .composer := rfl
  have hl4 : locs0 4 = .i32 ch := rfl
  have hl5 : locs0 5 = .i32 0 := rfl
  change ∃ endSt,
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d' + 1) subFuel) (kF + 80)
          CalculatorScreen_prog 0 CalculatorScreen_prog ⟨0, [], locs0, jh, hp⟩ =
        some (.unit, endSt) ∧
      endSt.jvmHeap = jh ∧
      endSt.heap = { hp with
        composer := Compose.setGroupRestartClosure (Compose.endRestartGroup r3).2 2094116101
          (.ext (.closureRef hp.closures.size))
        closures := hp.closures.push
          ("CalculatorScreenKt.CalculatorScreen$lambda$2",
            [.ext (.calcState cSt), onKey, modV, .i32 ch, .i32 0]) }
  dsimp only [CalculatorScreen_prog]
  rw [runFast_aload, hl0, runFast_ldcStr, runFast_checkNotNullParam]
  rw [runFast_aload, hl1, runFast_ldcStr, runFast_checkNotNull' d' subFuel _ _ _ honKey]
  rw [runFast_aload, hl3, runFast_iconst, runFast_startRestartGroup, runFast_astore]
  rw [runFast_aload]; peel_loc; rw [runFast_ldcStr, runFast_sourceInfo]
  rw [runFast_iload]; peel_loc; rw [hl4, runFast_istore]
  rw [runFast_iload]; peel_loc; rw [hl4, runFast_iconst, runFast_iand,
    runFast_ifne_zero' (by rcases hch with rfl | rfl <;> decide)]
  rw [runFast_iload]; peel_loc; rw [runFast_iload]; peel_loc; rw [hl4, runFast_iconst, runFast_iand,
    runFast_ifne_zero' (by rcases hch with rfl | rfl <;> decide)]
  rw [runFast_aload]; peel_loc; rw [runFast_aload]; peel_loc; rw [hl0, runFast_composerChanged]
  dsimp only
  rw [show Compose.startRestartGroup hp.composer (UInt32.toInt32 2094116101) = r1 from rfl]
  rw [hChgFalse]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [runFast_goto']
  dsimp only [CalculatorScreen_prog, List.drop]
  rw [runFast_ifeq_zero]
  dsimp only [CalculatorScreen_prog, List.drop]
  rw [runFast_iconst, runFast_ior, runFast_istore]
  rw [runFast_iload]; peel_loc; rw [hl4, runFast_iconst, runFast_iand,
    runFast_ifne_nonzero' (by rcases hch with rfl | rfl <;> decide)]
  dsimp only [CalculatorScreen_prog, List.drop]
  rw [runFast_iload]; peel_loc; rw [hl5, runFast_iconst, runFast_iand, runFast_ifeq_zero]
  dsimp only [CalculatorScreen_prog, List.drop]
  rw [runFast_iload]; peel_loc; rw [hl4, runFast_iconst, runFast_iand,
    runFast_ifne_nonzero' (by rcases hch with rfl | rfl <;> decide)]
  dsimp only [CalculatorScreen_prog, List.drop]
  rw [runFast_aload]; peel_loc; rw [runFast_iload]; peel_loc; rw [runFast_iconst, runFast_iand, runFast_iconst]
  rw [runFast_if_icmpeq_eq' (by rcases hch with rfl | rfl <;> decide)]
  dsimp only [CalculatorScreen_prog, List.drop]
  rw [runFast_iconst]
  rw [runFast_iload]; peel_loc; rw [runFast_iconst, runFast_iand, runFast_shouldExecute']
  dsimp only
  rw [show ((0 : UInt32) != 0) = false from rfl]
  rw [show (Compose.checkChangedSlot (Jvm.JvmVal.beqVal beqCalcExt) r1 (.ext (.calcState cSt))).2 = r2 from rfl, hShFalse]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [runFast_ifeq_zero]
  dsimp only [CalculatorScreen_prog, List.drop]
  rw [runFast_aload]; peel_loc; rw [runFast_skipToGroupEnd]
  rw [runFast_aload]; peel_loc; rw [runFast_endRestartGroup]
  dsimp only
  rw [show Compose.skipToGroupEnd r2 = r3 from rfl, hKeyEnd]
  dsimp only
  rw [runFast_dup, runFast_ifnull_fallthrough' rfl]
  rw [runFast_aload]; peel_loc; rw [hl0, runFast_aload]; peel_loc; rw [hl1, runFast_aload]; peel_loc; rw [hl2]
  rw [runFast_iload]; peel_loc; rw [hl4, runFast_iload]; peel_loc; rw [hl5]
  rw [runFast_invokedynamic_bsm5 parseTags_bsm2 bsm_CalculatorScreen_lambda_2]
  dsimp only [allocClosure]
  rw [runFast_updateScope, runFast_goto']
  dsimp only [CalculatorScreen_prog, List.drop]
  rw [runFast_vreturn']
  exact ⟨_, rfl, rfl, rfl⟩

/-- When `CalculatorScreen` recomposes with an unchanged `state` and clean group `2094116101`
(`comp.inserting = false`, `ch = 176`, `defF = 0`), it calls `skipToGroupEnd` and leaves `nodeStack` and `emittedRoot?`
untouched. -/
theorem CalculatorScreen_skip_equiv (d subFuel fuel : Nat)
    (hd : 1 ≤ d) (hf : 80 ≤ fuel)
    (cSt : CalculatorState) (onKey : JvmVal) (honKey : onKey.isNull = false) (cidKey : Nat)
    (hp : CalcHeap) (jh : Jvm.JvmHeap CalcExt)
    (hins : hp.composer.inserting = false)
    (gScr : Compose.GroupEntry JvmVal)
    (hgScrKey : gScr.key = (2094116101 : Int32))
    (hgScrSlots : gScr.slots = [.ext (.calcState cSt), .ext (.closureRef cidKey)])
    (hgScrClean : gScr.dirty = false)
    (hGroups : hp.composer.groups = [gScr] ∨
      ∃ gApp, hp.composer.groups = [gApp, gScr] ∧ gApp.key = (54337357 : Int32)) :
    let modV : JvmVal := .ext (.modifier none)
    let r1 := Compose.startRestartGroup hp.composer 2094116101
    let r2 := (Compose.checkChangedSlot (Jvm.JvmVal.beqVal beqCalcExt) r1 (.ext (.calcState cSt))).2
    let r3 := Compose.skipToGroupEnd r2
    let r4 := (Compose.endRestartGroup r3).2
    let compEnd := Compose.setGroupRestartClosure r4 2094116101 (.ext (.closureRef hp.closures.size))
    let closuresEnd := hp.closures.push
      ("CalculatorScreenKt.CalculatorScreen$lambda$2", [.ext (.calcState cSt), onKey, modV, .i32 176, .i32 0])
    ∃ endSt,
      Jvm.runJvmRes (mkCalcHooks calcProgLookup d subFuel) fuel CalculatorScreen_prog
          (initCalcJvmState
            [(0, .ext (.calcState cSt)), (1, onKey), (2, modV), (3, .ext .composer),
             (4, .i32 176), (5, .i32 0)]
            hp jh) =
        some (.unit, endSt) ∧
      endSt.jvmHeap = jh ∧
      endSt.heap = { hp with composer := compEnd, closures := closuresEnd } :=
  CalculatorScreen_skip_equiv_ch d subFuel fuel hd hf 176 (Or.inl rfl)
    cSt onKey honKey cidKey hp jh hins gScr hgScrKey hgScrSlots hgScrClean hGroups

end MosaicCalculator.KotlinJvmVerification

