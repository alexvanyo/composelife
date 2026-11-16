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

import proofs.KotlinJvmEquiv.EasingLambda
import proofs.KotlinJvmEquiv.EasingSort

/-!
# `Easing(easing, vararg easings)` (`EasingPiecewiseKt.Easing`)
-/

namespace UiCommon.KotlinJvmVerification

open UiCommon.JvmVerification
open UiCommon.KotlinJvmBytecode
open UiCommon.Model

/-- A `Pair<Float, Easing>` element of the `easings` vararg array. -/
def encodeEasingPair (p : Float32 × UiEasing) : JvmVal :=
  .pair (.ext (.boxedFloat p.1)) (.ext (.easing p.2))

theorem decodePairArray_encode (ps : List (Float32 × UiEasing)) :
    decodePairArray (ps.map encodeEasingPair).toArray = some ps := by
  unfold decodePairArray
  rw [List.toList_toArray]
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨k, e⟩
    simp [List.mapM_cons, encodeEasingPair, decodePairElem] at ih ⊢
    rw [ih]
    rfl

theorem float32_ofBits_zero : Float32.ofBits 0 = (0.0 : Float32) := by decide

section HookSteps
variable {r : String → Option (List JvmInstr)} {d sf f pc pc0 : Nat} {prog rest : List JvmInstr}
  {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap UiExt} {hp : UiHeap}

theorem runFast_sortedWith {addr : Nat} {cls : String} {elems : Array JvmVal}
    {ps : List (Float32 × UiEasing)}
    (hget : jh.get? addr = some (.objArray cls elems)) (hdec : decodePairArray elems = some ps) :
    Jvm.runJvmResFast (mkUiCommonHooks r d sf) (f + 1) prog pc
        (.invokestatic "kotlin/collections/ArraysKt" "sortedWith"
          "([Ljava/lang/Object;Ljava/util/Comparator;)Ljava/util/List;" :: rest)
        ⟨pc0, .ext .sortedByComparator :: .heapRef addr :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkUiCommonHooks r d sf) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.pairList (sortPairsByKeyframe ps)) :: stk, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_invokestatic_step _ ?_
  have key : Jvm.stepInvokeStaticGeneric (mkUiCommonHooks r d sf)
      ⟨pc, .ext .sortedByComparator :: .heapRef addr :: stk, locs, jh, hp⟩
      "kotlin/collections/ArraysKt" "sortedWith" "([Ljava/lang/Object;Ljava/util/Comparator;)Ljava/util/List;" =
      match jh.get? addr with
      | some (.objArray _ elems) =>
        match decodePairArray elems with
        | some pairs =>
          .inl (some ⟨pc + 1, .ext (.pairList (sortPairsByKeyframe pairs)) :: stk, locs, jh, hp⟩)
        | none => .inr none
      | _ => .inr none := by
    cases d <;> rfl
  rw [key, hget]
  dsimp only
  rw [hdec]

theorem runFast_arraysToList {addr : Nat} {cls : String} {elems : Array JvmVal}
    {ps : List (Float32 × UiEasing)}
    (hget : jh.get? addr = some (.objArray cls elems)) (hdec : decodePairArray elems = some ps) :
    Jvm.runJvmResFast (mkUiCommonHooks r d sf) (f + 1) prog pc
        (.invokestatic "kotlin/collections/ArraysKt" "toList" "([Ljava/lang/Object;)Ljava/util/List;" :: rest)
        ⟨pc0, .heapRef addr :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkUiCommonHooks r d sf) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.pairList ps) :: stk, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_invokestatic_step _ ?_
  have key : Jvm.stepInvokeStaticGeneric (mkUiCommonHooks r d sf)
      ⟨pc, .heapRef addr :: stk, locs, jh, hp⟩
      "kotlin/collections/ArraysKt" "toList" "([Ljava/lang/Object;)Ljava/util/List;" =
      match jh.get? addr with
      | some (.objArray _ elems) =>
        match decodePairArray elems with
        | some pairs => .inl (some ⟨pc + 1, .ext (.pairList pairs) :: stk, locs, jh, hp⟩)
        | none => .inr none
      | _ => .inr none := by
    cases d <;> rfl
  rw [key, hget]
  dsimp only
  rw [hdec]

theorem runFast_areEqual {a b : JvmVal}
    (ha : a.equalsModeled jh = true := by rfl) (hb : b.equalsModeled jh = true := by rfl) :
    Jvm.runJvmResFast (mkUiCommonHooks r d sf) (f + 1) prog pc
        (.invokestatic "kotlin/jvm/internal/Intrinsics" "areEqual" "(Ljava/lang/Object;Ljava/lang/Object;)Z" :: rest)
        ⟨pc0, b :: a :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkUiCommonHooks r d sf) f prog (pc + 1) rest
        ⟨pc + 1, .bool (Jvm.JvmVal.beqVal beqUiExt a b) :: stk, locs, jh, hp⟩ := by
  have hs := Jvm.stepInstr_areEqual (mkUiCommonHooks r d sf) (pc := pc) (stkRest := stk) (locs := locs)
    (hp := hp) ha hb
  rw [mkUiCommonHooks_beqExt] at hs
  exact Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) hs rfl

theorem runFast_mapPut {fs : Array (JvmVal → Option JvmVal)} {es : Array (Float32 → Float32)}
    {ms : Array (List (Float32 × UiEasing))} {cs : Array (String × List JvmVal)}
    {mid : Nat} {m : List (Float32 × UiEasing)} {k : Float32} {e : UiEasing}
    (hm : ms[mid]? = some m) :
    Jvm.runJvmResFast (mkUiCommonHooks r d sf) (f + 1) prog pc
        (.invokeinterface "java/util/Map" "put" "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" :: rest)
        ⟨pc0, .ext (.easing e) :: .ext (.boxedFloat k) :: .ext (.mapRef mid) :: stk, locs, jh, ⟨fs, es, ms, cs⟩⟩ =
      Jvm.runJvmResFast (mkUiCommonHooks r d sf) f prog (pc + 1) rest
        ⟨pc + 1, .null :: stk, locs, jh, ⟨fs, es, ms.set! mid (putKeyMap m k e), cs⟩⟩ := by
  refine Jvm.runJvmResFast_invokeinterface_step _ ?_
  have key : Jvm.stepInvokeInterfaceGeneric (mkUiCommonHooks r d sf)
      ⟨pc, .ext (.easing e) :: .ext (.boxedFloat k) :: .ext (.mapRef mid) :: stk, locs, jh, ⟨fs, es, ms, cs⟩⟩
      "java/util/Map" "put" "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" =
      match ms[mid]? with
      | some m =>
        .inl (some ⟨pc + 1, .null :: stk, locs, jh, ⟨fs, es, ms.set! mid (putKeyMap m k e), cs⟩⟩)
      | none => .inr none := by
    cases d <;> rfl
  rw [key, hm]

theorem runFast_putAll {fs : Array (JvmVal → Option JvmVal)} {es : Array (Float32 → Float32)}
    {ms : Array (List (Float32 × UiEasing))} {cs : Array (String × List JvmVal)}
    {addr mid : Nat} {cls : String} {elems : Array JvmVal} {ps m : List (Float32 × UiEasing)}
    (hget : jh.get? addr = some (.objArray cls elems)) (hdec : decodePairArray elems = some ps)
    (hm : ms[mid]? = some m) :
    Jvm.runJvmResFast (mkUiCommonHooks r d sf) (f + 1) prog pc
        (.invokestatic "kotlin/collections/MapsKt" "putAll" "(Ljava/util/Map;[Lkotlin/Pair;)V" :: rest)
        ⟨pc0, .heapRef addr :: .ext (.mapRef mid) :: stk, locs, jh, ⟨fs, es, ms, cs⟩⟩ =
      Jvm.runJvmResFast (mkUiCommonHooks r d sf) f prog (pc + 1) rest
        ⟨pc + 1, stk, locs, jh, ⟨fs, es, ms.set! mid (ps.foldl (fun acc (k, e) => putKeyMap acc k e) m), cs⟩⟩ := by
  refine Jvm.runJvmResFast_invokestatic_step _ ?_
  have key : Jvm.stepInvokeStaticGeneric (mkUiCommonHooks r d sf)
      ⟨pc, .heapRef addr :: .ext (.mapRef mid) :: stk, locs, jh, ⟨fs, es, ms, cs⟩⟩
      "kotlin/collections/MapsKt" "putAll" "(Ljava/util/Map;[Lkotlin/Pair;)V" =
      match jh.get? addr, ms[mid]? with
      | some (.objArray _ elems), some m =>
        match decodePairArray elems with
        | some pairs =>
          .inl (some ⟨pc + 1, stk, locs, jh,
            ⟨fs, es, ms.set! mid (pairs.foldl (fun acc (k, e) => putKeyMap acc k e) m), cs⟩⟩)
        | none => .inr none
      | _, _ => .inr none := by
    cases d <;> rfl
  rw [key, hget, hm]
  dsimp only
  rw [hdec]

theorem runFast_mapSize {fs : Array (JvmVal → Option JvmVal)} {es : Array (Float32 → Float32)}
    {ms : Array (List (Float32 × UiEasing))} {cs : Array (String × List JvmVal)}
    {mid : Nat} {m : List (Float32 × UiEasing)} (hm : ms[mid]? = some m) :
    Jvm.runJvmResFast (mkUiCommonHooks r d sf) (f + 1) prog pc
        (.invokeinterface "java/util/Map" "size" "()I" :: rest)
        ⟨pc0, .ext (.mapRef mid) :: stk, locs, jh, ⟨fs, es, ms, cs⟩⟩ =
      Jvm.runJvmResFast (mkUiCommonHooks r d sf) f prog (pc + 1) rest
        ⟨pc + 1, .i32 (UInt32.ofNat m.length) :: stk, locs, jh, ⟨fs, es, ms, cs⟩⟩ := by
  refine Jvm.runJvmResFast_invokeinterface_step _ ?_
  have key : Jvm.stepInvokeInterfaceGeneric (mkUiCommonHooks r d sf)
      ⟨pc, .ext (.mapRef mid) :: stk, locs, jh, ⟨fs, es, ms, cs⟩⟩ "java/util/Map" "size" "()I" =
      match ms[mid]? with
      | some m => .inl (some ⟨pc + 1, .i32 (UInt32.ofNat m.length) :: stk, locs, jh, ⟨fs, es, ms, cs⟩⟩)
      | none => .inr none := by
    cases d <;> rfl
  rw [key, hm]

theorem runFast_keySet {fs : Array (JvmVal → Option JvmVal)} {es : Array (Float32 → Float32)}
    {ms : Array (List (Float32 × UiEasing))} {cs : Array (String × List JvmVal)}
    {mid : Nat} {m : List (Float32 × UiEasing)} (hm : ms[mid]? = some m) :
    Jvm.runJvmResFast (mkUiCommonHooks r d sf) (f + 1) prog pc
        (.invokeinterface "java/util/Map" "keySet" "()Ljava/util/Set;" :: rest)
        ⟨pc0, .ext (.mapRef mid) :: stk, locs, jh, ⟨fs, es, ms, cs⟩⟩ =
      Jvm.runJvmResFast (mkUiCommonHooks r d sf) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.floatList (m.map Prod.fst)) :: stk, locs, jh, ⟨fs, es, ms, cs⟩⟩ := by
  refine Jvm.runJvmResFast_invokeinterface_step _ ?_
  have key : Jvm.stepInvokeInterfaceGeneric (mkUiCommonHooks r d sf)
      ⟨pc, .ext (.mapRef mid) :: stk, locs, jh, ⟨fs, es, ms, cs⟩⟩ "java/util/Map" "keySet" "()Ljava/util/Set;" =
      match ms[mid]? with
      | some m => .inl (some ⟨pc + 1, .ext (.floatList (m.map Prod.fst)) :: stk, locs, jh, ⟨fs, es, ms, cs⟩⟩)
      | none => .inr none := by
    cases d <;> rfl
  rw [key, hm]

theorem runFast_values {fs : Array (JvmVal → Option JvmVal)} {es : Array (Float32 → Float32)}
    {ms : Array (List (Float32 × UiEasing))} {cs : Array (String × List JvmVal)}
    {mid : Nat} {m : List (Float32 × UiEasing)} (hm : ms[mid]? = some m) :
    Jvm.runJvmResFast (mkUiCommonHooks r d sf) (f + 1) prog pc
        (.invokeinterface "java/util/Map" "values" "()Ljava/util/Collection;" :: rest)
        ⟨pc0, .ext (.mapRef mid) :: stk, locs, jh, ⟨fs, es, ms, cs⟩⟩ =
      Jvm.runJvmResFast (mkUiCommonHooks r d sf) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.easingList (m.map Prod.snd)) :: stk, locs, jh, ⟨fs, es, ms, cs⟩⟩ := by
  refine Jvm.runJvmResFast_invokeinterface_step _ ?_
  have key : Jvm.stepInvokeInterfaceGeneric (mkUiCommonHooks r d sf)
      ⟨pc, .ext (.mapRef mid) :: stk, locs, jh, ⟨fs, es, ms, cs⟩⟩ "java/util/Map" "values" "()Ljava/util/Collection;" =
      match ms[mid]? with
      | some m => .inl (some ⟨pc + 1, .ext (.easingList (m.map Prod.snd)) :: stk, locs, jh, ⟨fs, es, ms, cs⟩⟩)
      | none => .inr none := by
    cases d <;> rfl
  rw [key, hm]

theorem runFast_sortedByInit {c1 c2 : String} :
    Jvm.runJvmResFast (mkUiCommonHooks r d sf) (f + 1) prog pc
        (.invokespecial "com/alexvanyo/composelife/ui/util/EasingPiecewiseKt$Easing$$inlined$sortedBy$1"
          "<init>" "()V" :: rest)
        ⟨pc0, .allocRef c1 :: .allocRef c2 :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkUiCommonHooks r d sf) f prog (pc + 1) rest
        ⟨pc + 1, .ext .sortedByComparator :: stk, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_invokespecial_step _ ?_
  cases d <;> rfl

theorem runFast_athrow {st : JvmState} :
    Jvm.runJvmResFast (mkUiCommonHooks r d sf) (f + 1) prog pc (.athrow :: rest) st = none := by
  rw [Jvm.runJvmResFast_step_nonbranch _ f prog pc _ rest _ rfl (by simp)]
  rfl

theorem runFast_newClass_other {cls : String}
    (h0 : cls ≠ "java/lang/StringBuilder")
    (h1 : normalizeUiCommonClass cls ≠ "TargetState$Single")
    (h2 : normalizeUiCommonClass cls ≠ "TargetState$InProgress") :
    Jvm.runJvmResFast (mkUiCommonHooks r d sf) (f + 1) prog pc (.newClass cls :: rest)
        ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkUiCommonHooks r d sf) f prog (pc + 1) rest
        ⟨pc + 1, .allocRef cls :: stk, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  unfold Jvm.stepInstr
  simp [h0, mkUiCommonHooks_stepNewClass_other r d sf ⟨pc, stk, locs, jh, hp⟩ cls h1 h2]

theorem runFast_ifne_bool_branch {target : Nat} {b : Bool} (hb : b = true) :
    Jvm.runJvmResFast (mkUiCommonHooks r d sf) (f + 1) prog pc (.ifne target :: rest)
        ⟨pc, .bool b :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkUiCommonHooks r d sf) f prog target (prog.drop target) ⟨target, stk, locs, jh, hp⟩ := by
  subst hb
  rw [Jvm.runJvmResFast_at_branch_cons _ (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch, mkUiCommonHooks_isZero?]

theorem runFast_ifne_bool_fallthrough {target : Nat} {b : Bool} (hb : b = false) :
    Jvm.runJvmResFast (mkUiCommonHooks r d sf) (f + 1) prog pc (.ifne target :: rest)
        ⟨pc, .bool b :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkUiCommonHooks r d sf) f prog (pc + 1) rest ⟨pc + 1, stk, locs, jh, hp⟩ := by
  subst hb
  rw [Jvm.runJvmResFast_at_branch_cons _ (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch, mkUiCommonHooks_isZero?]

theorem runFast_areturn {v : JvmVal} :
    Jvm.runJvmResFast (mkUiCommonHooks r d sf) (f + 1) prog pc (.areturn :: rest) ⟨pc0, v :: stk, locs, jh, hp⟩ =
      some (v, ⟨pc, v :: stk, locs, jh, hp⟩) := by
  rw [Jvm.runJvmResFast_step_nonbranch _ f prog pc .areturn rest _ rfl (by simp)]
  rfl

end HookSteps

/-- Steps one hook instruction whose result `cases d <;> rfl` computes, then continues with `ui_step_blk`. -/
macro "ui_drfl_step " d:ident : tactic => `(tactic| (
  first
    | rw [Jvm.runJvmResFast_invokestatic_step _ (by cases $d:ident <;> rfl)]
    | rw [Jvm.runJvmResFast_invokeinterface_step _ (by cases $d:ident <;> rfl)]
    | rw [Jvm.runJvmResFast_invokevirtual_step _ (by cases $d:ident <;> rfl)]
    | rw [Jvm.runJvmResFast_invokespecial_step _ (by cases $d:ident <;> rfl)]
    | rw [Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) (by cases $d:ident <;> rfl) rfl]
  ui_step_blk))

/-! ### Model-side facts -/

theorem array_push_set {α : Type} (a : Array α) (x y : α) : (a.push x).set! a.size y = a.push y := by
  rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds_def]
  simp [Array.set_push]

theorem putKeyMap_length_le' {E : Type} (m : List (Float32 × E)) (k : Float32) (e : E) :
    (putKeyMap m k e).length ≤ m.length + 1 := by
  induction m with
  | nil => simp [putKeyMap]
  | cons hd tl ih =>
    rcases hd with ⟨k0, e0⟩
    unfold putKeyMap
    split <;> simp <;> omega

theorem foldl_putKeyMap_length_le {E : Type} (acc : List (Float32 × E)) (xs : List (Float32 × E)) :
    (xs.foldl (fun m p => putKeyMap m p.1 p.2) acc).length ≤ acc.length + xs.length := by
  induction xs generalizing acc with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.length_cons]
    have h1 := ih (putKeyMap acc hd.1 hd.2)
    have h2 := putKeyMap_length_le' acc hd.1 hd.2
    omega

/-- The map the bytecode builds (`put(0f, easing)` then `putAll(easings)`) is `buildKeyframeMap`. -/
theorem bytecode_keyframeMap_eq (e0 : UiEasing) (ps : List (Float32 × UiEasing)) :
    ps.foldl (fun acc (k, e) => putKeyMap acc k e) (putKeyMap [] (Float32.ofBits 0) e0) =
      buildKeyframeMap e0 ps := by
  unfold buildKeyframeMap
  rw [float32_ofBits_zero]
  rfl

theorem u32_ofNat_inj {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) (h : UInt32.ofNat a = UInt32.ofNat b) :
    a = b := by
  have := congrArg UInt32.toNat h
  rw [Jvm.ui32_ofNat_toNat_of_lt a ha, Jvm.ui32_ofNat_toNat_of_lt b hb] at this
  exact this

/-! ### `Easing(easing, vararg easings)` -/

/-- Steps `Easing` from its entry up to the `ifne` that tests `sortedBy { it.first } == toList()`. -/
macro "easing_prefix " d:ident hget:ident hdec:ident : tactic => `(tactic| (
  conv => lhs; arg 5; dsimp only [EasingPiecewiseKt_Easing_prog]
  ui_step_blk
  ui_rfl_step
  ui_rfl_step
  rw [runFast_newClass_other (by decide) (by decide) (by decide)]
  ui_step_blk
  rw [runFast_sortedByInit]
  ui_drfl_step $d
  rw [runFast_sortedWith $hget $hdec]
  ui_step_blk
  rw [runFast_arraysToList $hget $hdec, runFast_areEqual]))

/-- Steps the sorted branch of `Easing` from `createMapBuilder` up to the `if_icmpne` size check. -/
macro "easing_build " d:ident hget:ident hdec:ident hm1:ident hm2:ident hm3:ident : tactic => `(tactic| (
  conv => lhs; arg 5; dsimp only [EasingPiecewiseKt_Easing_prog, List.drop]
  ui_drfl_step $d
  ui_drfl_step $d
  dsimp only
  rw [runFast_mapPut $hm1, array_push_set]
  ui_step_blk
  rw [runFast_putAll $hget $hdec $hm2, array_push_set, bytecode_keyframeMap_eq]
  ui_step_blk
  ui_drfl_step $d
  rw [runFast_mapSize $hm3]
  ui_step_blk
  rw [Jvm.runJvmResFast_arraylength_obj _ $hget]
  ui_step_blk))

/-- Steps a failed `require` (`IllegalArgumentException(message.toString())`) to its `athrow`. -/
macro "easing_throw " d:ident : tactic => `(tactic| (
  ui_step_blk
  rw [runFast_newClass_other (by decide) (by decide) (by decide)]
  ui_step_blk
  ui_drfl_step $d
  ui_drfl_step $d
  exact runFast_athrow))

set_option maxRecDepth 8192 in
/-- `Easing(easing, vararg easings)` on an array of `Pair<Float, Easing>` returns a fresh piecewise easing closure
capturing the key and easing lists of `validateEasingKeyframes`, after storing the `buildMap` result in a new map,
and traps exactly when `validateEasingKeyframes` rejects the keyframes (unsorted, or a duplicate key). -/
theorem Easing_equiv (resolveProg : String → Option (List JvmInstr)) (d sf fuel : Nat)
    (e0 : UiEasing) (ps : List (Float32 × UiEasing)) (arrAddr : Nat) (cls : String)
    (hp : UiHeap) (jh : Jvm.JvmHeap UiExt)
    (hget : jh.get? arrAddr = some (.objArray cls (ps.map encodeEasingPair).toArray))
    (hlen : ps.length < 2 ^ 30) (hf : 90 ≤ fuel) :
    (Jvm.runJvmRes (mkUiCommonHooks resolveProg d sf) fuel EasingPiecewiseKt_Easing_prog
        (initUiJvmState [(0, .ext (.easing e0)), (1, .heapRef arrAddr)] hp jh)).map
      (fun r => (r.1, r.2.jvmHeap, r.2.heap)) =
      (validateEasingKeyframes e0 ps).map (fun ke =>
        (.ext (.easing (.piecewise hp.closures.size)), jh,
          { hp with
            maps := hp.maps.push (buildKeyframeMap e0 ps)
            closures := hp.closures.push
              ("EasingPiecewiseKt.Easing$lambda$3", [.ext (.floatList ke.1), .ext (.easingList ke.2)]) })) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  have hdec := decodePairArray_encode ps
  have hbeq : Jvm.JvmVal.beqVal beqUiExt (.ext (.pairList (sortPairsByKeyframe ps))) (.ext (.pairList ps)) =
      isSortedByKeyframe ps := beqUiExt_sortPairs_eq_isSorted ps
  rw [runJvmRes_eq_runJvmResFast0 _ _ rfl _ _ rfl]
  simp only [initUiJvmState, Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
  by_cases hs : isSortedByKeyframe ps = false
  · have hm : validateEasingKeyframes e0 ps = none := by simp [validateEasingKeyframes, hs]
    rw [hm, Option.map_none, Option.map_eq_none_iff]
    easing_prefix d hget hdec
    rw [hbeq, runFast_ifne_bool_fallthrough hs]
    easing_throw d
  have hs' : isSortedByKeyframe ps = true := by simpa using hs
  have hmlen := foldl_putKeyMap_length_le [((0.0 : Float32), e0)] ps
  change (buildKeyframeMap e0 ps).length ≤ _ at hmlen
  simp only [List.length_cons, List.length_nil] at hmlen
  have hm1 : (hp.maps.push ([] : List (Float32 × UiEasing)))[hp.maps.size]? = some [] := by simp
  have hm2 : (hp.maps.push (putKeyMap [] (Float32.ofBits 0) e0))[hp.maps.size]? =
      some (putKeyMap [] (Float32.ofBits 0) e0) := by simp
  have hm3 : (hp.maps.push (buildKeyframeMap e0 ps))[hp.maps.size]? = some (buildKeyframeMap e0 ps) := by simp
  by_cases hsz : (buildKeyframeMap e0 ps).length = ps.length + 1
  · have hm : validateEasingKeyframes e0 ps =
        some ((buildKeyframeMap e0 ps).map Prod.fst, (buildKeyframeMap e0 ps).map Prod.snd) := by
      simp [validateEasingKeyframes, hs', hsz]
    have hab : UInt32.ofNat (buildKeyframeMap e0 ps).length =
        UInt32.ofNat (List.map encodeEasingPair ps).toArray.size + 1 := by
      rw [hsz]; simp [UInt32.ofNat_add]
    rw [hm, Option.map_some, Option.map_eq_some_iff]
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · easing_prefix d hget hdec
      rw [hbeq, runFast_ifne_bool_branch hs']
      easing_build d hget hdec hm1 hm2 hm3
      rw [Jvm.runJvmResFast_if_icmpne_fallthrough _ hab]
      ui_step_blk
      rw [Jvm.runJvmResFast_ifne_branch _ (by decide)]
      conv => lhs; arg 5; dsimp only [EasingPiecewiseKt_Easing_prog, List.drop]
      ui_step_blk
      rw [runFast_keySet hm3]
      ui_drfl_step d
      ui_drfl_step d
      rw [runFast_values hm3]
      ui_drfl_step d
      ui_drfl_step d
      ui_drfl_step d
      rw [runFast_areturn]
    · rfl
  · have hm : validateEasingKeyframes e0 ps = none := by
      simp [validateEasingKeyframes, hs', hsz]
    have hab : UInt32.ofNat (buildKeyframeMap e0 ps).length ≠
        UInt32.ofNat (List.map encodeEasingPair ps).toArray.size + 1 := by
      intro h
      apply hsz
      apply u32_ofNat_inj (by omega) (by omega)
      rw [h]; simp [UInt32.ofNat_add]
    rw [hm, Option.map_none, Option.map_eq_none_iff]
    easing_prefix d hget hdec
    rw [hbeq, runFast_ifne_bool_branch hs']
    easing_build d hget hdec hm1 hm2 hm3
    rw [Jvm.runJvmResFast_if_icmpne_branch _ hab]
    conv => lhs; arg 5; dsimp only [EasingPiecewiseKt_Easing_prog, List.drop]
    ui_step_blk
    rw [Jvm.runJvmResFast_ifne_fallthrough _ rfl]
    easing_throw d

end UiCommon.KotlinJvmVerification
