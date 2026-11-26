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

import proofs.KotlinJvmEquiv.EasingPiecewise
import proofs.KotlinJvmEquiv.TargetState
import proofs.KotlinJvmEquiv.FastExecEq

/-!
# The piecewise `Easing` lambda (`EasingPiecewiseKt.Easing$lambda$3`)
-/

namespace UiCommon.KotlinJvmVerification

open UiCommon.JvmVerification
open UiCommon.KotlinJvmBytecode
open UiCommon.Model

set_option maxRecDepth 8192 in
theorem stepInstr_invokeFloorBinarySearch (r : String → Option (List JvmInstr)) (d sf pc : Nat)
    (keys : List Float32) (t : Float32) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    Jvm.stepInstr (mkUiCommonHooks r (d + 1) sf)
        (.invokestatic "com/alexvanyo/composelife/ui/util/EasingPiecewiseKt" "floorBinarySearch" "(Ljava/util/List;Ljava/lang/Comparable;)I")
        ⟨pc, .ext (.boxedFloat t) :: .ext (.floatList keys) :: stk, locs, jh, hp⟩ =
      match r "EasingPiecewiseKt.floorBinarySearch" with
      | some prog =>
        match Jvm.runJvmRes (mkUiCommonHooks r d sf) sf prog
            (initUiJvmState [(0, .ext (.floatList keys)), (1, .ext (.boxedFloat t))] hp jh) with
        | some (res, endSt) => .inl (some ⟨pc + 1, res :: stk, locs, endSt.jvmHeap, endSt.heap⟩)
        | none => .inr none
      | none => .inr none := by
  have hE : ∀ st : JvmState, Jvm.stepInstr (mkUiCommonHooks r (d + 1) sf)
      (.invokestatic "com/alexvanyo/composelife/ui/util/EasingPiecewiseKt" "floorBinarySearch" "(Ljava/util/List;Ljava/lang/Comparable;)I") st =
      (mkUiCommonHooks r (d + 1) sf).stepInvokeStatic st "EasingPiecewiseKt" "floorBinarySearch"
        "(Ljava/util/List;Ljava/lang/Comparable;)I" :=
    fun _ => rfl
  have ht : Jvm.parseMethodParamTags "(Ljava/util/List;Ljava/lang/Comparable;)I" = ['L', 'L'] := by decide
  have hstr : "EasingPiecewiseKt" ++ "." ++ "floorBinarySearch" = "EasingPiecewiseKt.floorBinarySearch" := rfl
  have hvoid : isVoidTarget "EasingPiecewiseKt.floorBinarySearch" = false := rfl
  have hn : normalizeUiCommonClass "EasingPiecewiseKt" = "EasingPiecewiseKt" := rfl
  rw [hE]
  conv => lhs; unfold mkUiCommonHooks
  dsimp only
  rw [hn]
  simp only [beq_self_eq_true, Bool.or_true, ↓reduceIte, ht, hstr, hvoid, List.length_cons, List.length_nil,
    Nat.not_lt_of_ge (Nat.le_add_left 2 stk.length), List.take_succ_cons, List.take_zero, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append, List.drop_succ_cons, List.drop_zero,
    Bool.false_eq_true]
  have hinit : (⟨0, [], List.foldl (fun loc x => setLocal loc x.fst x.snd) (fun _ => Jvm.JvmVal.i32 0)
        (assignParamLocalsAux 0 ['L', 'L'] [.ext (.floatList keys), .ext (.boxedFloat t)]), jh, hp⟩ : JvmState) =
      initUiJvmState [(0, .ext (.floatList keys)), (1, .ext (.boxedFloat t))] hp jh := rfl
  rw [hinit]
  cases r "EasingPiecewiseKt.floorBinarySearch" with
  | none => rfl
  | some prog =>
    dsimp only
    cases Jvm.runJvmRes (mkUiCommonHooks r d sf) sf prog
      (initUiJvmState [(0, .ext (.floatList keys)), (1, .ext (.boxedFloat t))] hp jh) <;> rfl

theorem float32_ofBits_one : Float32.ofBits 1065353216 = (1.0 : Float32) := by decide

/-- The `Easing.transform` the hooks implement for registered constant easings. -/
def constEasingTransform (hp : UiHeap) : UiEasing → Float32 → Float32
  | .const eid, x => (hp.easings[eid]?.getD id) x
  | .piecewise _, x => x

instance (r : String → Option (List JvmInstr)) (d sf : Nat) : Jvm.HasDefaultIsZero (mkUiCommonHooks r d sf) :=
  ⟨mkUiCommonHooks_isZero? r d sf⟩

section GenericSteps
variable {hooks : Jvm.JvmHooks UiExt UiHeap}

theorem runFast_if_icmpgt_fallthrough {f1 pc target : Nat} {prog rest : List JvmInstr}
    {a b : UInt32} {srest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap UiExt} {hp : UiHeap}
    (h : b.toBitVec.slt a.toBitVec = false) :
    Jvm.runJvmResFast hooks (f1 + 1) prog pc (.if_icmpgt target :: rest)
        ⟨pc, .i32 b :: .i32 a :: srest, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f1 prog (pc + 1) rest ⟨pc + 1, srest, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch, h]

theorem runFast_freturn {f pc pc0 : Nat} {prog rest : List JvmInstr} {x : Float32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap UiExt} {hp : UiHeap} :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.freturn :: rest) ⟨pc0, .f32 x :: stk, locs, jh, hp⟩ =
      some (.f32 x, ⟨pc, .f32 x :: stk, locs, jh, hp⟩) := by
  rw [Jvm.runJvmResFast_step_nonbranch _ f prog pc .freturn rest _ rfl (by simp)]
  rfl

end GenericSteps

theorem runFast_invokeFloor {r : String → Option (List JvmInstr)} {d sf f pc pc0 : Nat}
    {prog rest : List JvmInstr} {keys : List Float32} {t : Float32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap UiExt} {hp : UiHeap}
    {v : JvmVal} {endSt : JvmState}
    (hprog : r "EasingPiecewiseKt.floorBinarySearch" = some EasingPiecewiseKt_floorBinarySearch_prog)
    (hrun : Jvm.runJvmRes (mkUiCommonHooks r d sf) sf EasingPiecewiseKt_floorBinarySearch_prog
      (initUiJvmState [(0, .ext (.floatList keys)), (1, .ext (.boxedFloat t))] hp jh) = some (v, endSt)) :
    Jvm.runJvmResFast (mkUiCommonHooks r (d + 1) sf) (f + 1) prog pc
        (.invokestatic "com/alexvanyo/composelife/ui/util/EasingPiecewiseKt" "floorBinarySearch" "(Ljava/util/List;Ljava/lang/Comparable;)I" :: rest)
        ⟨pc0, .ext (.boxedFloat t) :: .ext (.floatList keys) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkUiCommonHooks r (d + 1) sf) f prog (pc + 1) rest
        ⟨pc + 1, v :: stk, locs, endSt.jvmHeap, endSt.heap⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  rw [stepInstr_invokeFloorBinarySearch, hprog]
  dsimp only
  rw [hrun]

theorem runFast_invokeFloor_trap {r : String → Option (List JvmInstr)} {d sf f pc pc0 : Nat}
    {prog rest : List JvmInstr} {keys : List Float32} {t : Float32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap UiExt} {hp : UiHeap}
    (hprog : r "EasingPiecewiseKt.floorBinarySearch" = some EasingPiecewiseKt_floorBinarySearch_prog)
    (hrun : Jvm.runJvmRes (mkUiCommonHooks r d sf) sf EasingPiecewiseKt_floorBinarySearch_prog
      (initUiJvmState [(0, .ext (.floatList keys)), (1, .ext (.boxedFloat t))] hp jh) = none) :
    Jvm.runJvmResFast (mkUiCommonHooks r (d + 1) sf) (f + 1) prog pc
        (.invokestatic "com/alexvanyo/composelife/ui/util/EasingPiecewiseKt" "floorBinarySearch" "(Ljava/util/List;Ljava/lang/Comparable;)I" :: rest)
        ⟨pc0, .ext (.boxedFloat t) :: .ext (.floatList keys) :: stk, locs, jh, hp⟩ = none := by
  rw [Jvm.runJvmResFast_step_nonbranch _ f prog pc _ rest _ rfl (by simp)]
  have h := stepInstr_invokeFloorBinarySearch r d sf pc keys t stk locs jh hp
  rw [hprog] at h
  dsimp only at h
  rw [hrun] at h
  simp only [h]

theorem runFast_floatList_get_neg {resolveProg : String → Option (List JvmInstr)}
    {d sf f pc pc0 : Nat} {prog rest : List JvmInstr} {xs : List Float32} {idx : UInt32}
    (hneg : idx.toBitVec.slt 0#32 = true)
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap UiExt} {hp : UiHeap} :
    Jvm.runJvmResFast (mkUiCommonHooks resolveProg d sf) (f + 1) prog pc
        (.invokeinterface "java/util/List" "get" "(I)Ljava/lang/Object;" :: rest)
        ⟨pc0, .i32 idx :: .ext (.floatList xs) :: stk, locs, jh, hp⟩ = none := by
  rw [Jvm.runJvmResFast_step_nonbranch _ f prog pc _ rest _ rfl (by simp)]
  have key : Jvm.stepInstr (mkUiCommonHooks resolveProg d sf)
      (.invokeinterface "java/util/List" "get" "(I)Ljava/lang/Object;")
      ⟨pc, .i32 idx :: .ext (.floatList xs) :: stk, locs, jh, hp⟩ =
      if idx.toBitVec.slt 0#32 then .inr none
      else if h : idx.toNat < xs.length then
        .inl (some ⟨pc + 1, .ext (.boxedFloat xs[idx.toNat]) :: stk, locs, jh, hp⟩)
      else .inr none := by
    cases d <;> rfl
  simp only [key, hneg, ↓reduceIte]

theorem runFast_floatList_get_empty {resolveProg : String → Option (List JvmInstr)}
    {d sf f pc pc0 : Nat} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap UiExt} {hp : UiHeap} :
    Jvm.runJvmResFast (mkUiCommonHooks resolveProg d sf) (f + 1) prog pc
        (.invokeinterface "java/util/List" "get" "(I)Ljava/lang/Object;" :: rest)
        ⟨pc0, .i32 0 :: .ext (.floatList []) :: stk, locs, jh, hp⟩ = none := by
  rw [Jvm.runJvmResFast_step_nonbranch _ f prog pc _ rest _ rfl (by simp)]
  cases d <;> rfl

theorem runFast_easingList_get {resolveProg : String → Option (List JvmInstr)}
    {d sf f pc pc0 : Nat} {prog rest : List JvmInstr} {xs : List UiEasing} {i : Nat}
    (hi : i < xs.length) (hi31 : i < 2 ^ 31)
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap UiExt} {hp : UiHeap} :
    Jvm.runJvmResFast (mkUiCommonHooks resolveProg d sf) (f + 1) prog pc
        (.invokeinterface "java/util/List" "get" "(I)Ljava/lang/Object;" :: rest)
        ⟨pc0, .i32 (UInt32.ofNat i) :: .ext (.easingList xs) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkUiCommonHooks resolveProg d sf) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.easing xs[i]) :: stk, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_invokeinterface_step _ ?_
  have hs := Jvm.ui32_slt_zero_of_lt i hi31
  have ht := Jvm.ui32_ofNat_toNat_of_lt i hi31
  have key : Jvm.stepInvokeInterfaceGeneric (mkUiCommonHooks resolveProg d sf)
      ⟨pc, .i32 (UInt32.ofNat i) :: .ext (.easingList xs) :: stk, locs, jh, hp⟩
      "java/util/List" "get" "(I)Ljava/lang/Object;" =
      if (UInt32.ofNat i).toBitVec.slt 0#32 then .inr none
      else if h : (UInt32.ofNat i).toNat < xs.length then
        .inl (some ⟨pc + 1, .ext (.easing xs[(UInt32.ofNat i).toNat]) :: stk, locs, jh, hp⟩)
      else .inr none := by
    cases d <;> rfl
  rw [key]
  simp only [hs, Bool.false_eq_true, ↓reduceIte, ht, hi, ↓reduceDIte]

theorem runFast_easingList_get_oob {resolveProg : String → Option (List JvmInstr)}
    {d sf f pc pc0 : Nat} {prog rest : List JvmInstr} {xs : List UiEasing} {i : Nat}
    (hi : xs.length ≤ i) (hi31 : i < 2 ^ 31)
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap UiExt} {hp : UiHeap} :
    Jvm.runJvmResFast (mkUiCommonHooks resolveProg d sf) (f + 1) prog pc
        (.invokeinterface "java/util/List" "get" "(I)Ljava/lang/Object;" :: rest)
        ⟨pc0, .i32 (UInt32.ofNat i) :: .ext (.easingList xs) :: stk, locs, jh, hp⟩ = none := by
  rw [Jvm.runJvmResFast_step_nonbranch _ f prog pc _ rest _ rfl (by simp)]
  have hs := Jvm.ui32_slt_zero_of_lt i hi31
  have ht := Jvm.ui32_ofNat_toNat_of_lt i hi31
  have key : Jvm.stepInstr (mkUiCommonHooks resolveProg d sf)
      (.invokeinterface "java/util/List" "get" "(I)Ljava/lang/Object;")
      ⟨pc, .i32 (UInt32.ofNat i) :: .ext (.easingList xs) :: stk, locs, jh, hp⟩ =
      if (UInt32.ofNat i).toBitVec.slt 0#32 then .inr none
      else if h : (UInt32.ofNat i).toNat < xs.length then
        .inl (some ⟨pc + 1, .ext (.easing xs[(UInt32.ofNat i).toNat]) :: stk, locs, jh, hp⟩)
      else .inr none := by
    cases d <;> rfl
  rw [key]
  simp only [hs, Bool.false_eq_true, ↓reduceIte, ht, show ¬ i < xs.length by omega, ↓reduceDIte]

theorem runFast_transform_const {resolveProg : String → Option (List JvmInstr)}
    {d sf f pc pc0 : Nat} {prog rest : List JvmInstr} {eid : Nat} {g : Float32 → Float32} {x : Float32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap UiExt} {hp : UiHeap}
    (hg : hp.easings[eid]? = some g) :
    Jvm.runJvmResFast (mkUiCommonHooks resolveProg d sf) (f + 1) prog pc
        (.invokeinterface "androidx/compose/animation/core/Easing" "transform" "(F)F" :: rest)
        ⟨pc0, .f32 x :: .ext (.easing (.const eid)) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkUiCommonHooks resolveProg d sf) f prog (pc + 1) rest
        ⟨pc + 1, .f32 (g x) :: stk, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_invokeinterface_step _ ?_
  have key : Jvm.stepInvokeInterfaceGeneric (mkUiCommonHooks resolveProg d sf)
      ⟨pc, .f32 x :: .ext (.easing (.const eid)) :: stk, locs, jh, hp⟩
      "androidx/compose/animation/core/Easing" "transform" "(F)F" =
      match hp.easings[eid]? with
      | some g => .inl (some ⟨pc + 1, .f32 (g x) :: stk, locs, jh, hp⟩)
      | none => .inr none := by
    cases d <;> rfl
  rw [key, hg]

theorem floorBinarySearch_empty_trap (resolveProg : String → Option (List JvmInstr)) (d sf fuel : Nat)
    (hf : 10 ≤ fuel) (t : Float32) (hp : UiHeap) (jh : Jvm.JvmHeap UiExt) :
    Jvm.runJvmRes (mkUiCommonHooks resolveProg d sf) fuel EasingPiecewiseKt_floorBinarySearch_prog
      (initUiJvmState [(0, .ext (.floatList [])), (1, .ext (.boxedFloat t))] hp jh) = none := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  rw [runJvmRes_eq_runJvmResFast0 _ _ rfl _ _ rfl]
  simp only [initUiJvmState, Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
  conv => lhs; arg 5; dsimp only [EasingPiecewiseKt_floorBinarySearch_prog]
  rw [show k + 10 = (k + 1) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
  ui_step_blk
  rw [runFast_list_size_float]
  ui_step_blk
  exact runFast_floatList_get_empty

macro "lambda_prefix" : tactic => `(tactic| (
  conv => lhs; arg 5; dsimp only [EasingPiecewiseKt_Easing_lambda_3_prog]
  ui_step_blk
  rw [Jvm.runJvmResFast_invokestatic_step _ (by rfl)]
  rw [runFast_checkcast_comparable]))

/-- The piecewise easing lambda computes `evalPiecewiseEasing` over its captured key and easing lists, with
`Easing.transform` of each registered constant easing, and leaves both heaps unchanged. It traps exactly when the
model returns `none` (an input before the first key reads `keyList[-1]`; an empty key list or an easing list shorter
than the selected segment index reads out of bounds). The nested `floorBinarySearch` call needs one level of
recursion depth and `21 * keys.length + 20` steps of sub-call fuel. -/
theorem Easing_lambda_3_equiv (resolveProg : String → Option (List JvmInstr)) (d sf fuel : Nat)
    (hext : ExtendsUiProgs resolveProg) (keys : List Float32) (es : List UiEasing) (t : Float32)
    (hp : UiHeap) (jh : Jvm.JvmHeap UiExt) (hlen : keys.length < 2 ^ 30)
    (hes : ∀ e ∈ es, ∃ eid, e = .const eid ∧ eid < hp.easings.size)
    (hsf : 21 * keys.length + 20 ≤ sf) (hf : 60 ≤ fuel) :
    (Jvm.runJvmRes (mkUiCommonHooks resolveProg (d + 1) sf) fuel EasingPiecewiseKt_Easing_lambda_3_prog
        (initUiJvmState [(0, .ext (.floatList keys)), (1, .ext (.easingList es)), (2, .f32 t)] hp jh)).map
      (fun r => (r.1, r.2.jvmHeap, r.2.heap)) =
      (evalPiecewiseEasing (constEasingTransform hp) keys es t).map (fun v => (.f32 v, jh, hp)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  have hprog := hext "EasingPiecewiseKt.floorBinarySearch" EasingPiecewiseKt_floorBinarySearch_prog rfl
  rw [runJvmRes_eq_runJvmResFast0 _ _ rfl _ _ rfl]
  simp only [initUiJvmState, Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
  by_cases hk : keys = []
  · subst hk
    have hm : evalPiecewiseEasing (constEasingTransform hp) [] es t = none := by
      simp [evalPiecewiseEasing, piecewiseSegment, floorBinarySearch]
    rw [hm, Option.map_none, Option.map_eq_none_iff]
    lambda_prefix
    exact runFast_invokeFloor_trap hprog (floorBinarySearch_empty_trap resolveProg d sf sf (by omega) t hp jh)
  have hpos : 0 < keys.length := List.length_pos_iff.mpr hk
  obtain ⟨endSt, hrun, hjh, hhp⟩ := floorBinarySearch_equiv resolveProg d sf sf keys t hk hlen hsf hp jh
  by_cases hneg : floatCompare t keys[0] < 0
  · have hidx : floorBinarySearch keys t = -1 := (floorBinarySearch_neg_one_iff keys t hpos).mpr hneg
    have hm : evalPiecewiseEasing (constEasingTransform hp) keys es t = none := by
      simp [evalPiecewiseEasing, piecewiseSegment, hidx]
    rw [hm, Option.map_none, Option.map_eq_none_iff]
    lambda_prefix
    rw [runFast_invokeFloor hprog hrun, hjh, hhp, hidx]
    ui_step_blk
    exact runFast_floatList_get_neg (by decide)
  obtain ⟨i, hidx, hilt, -, -⟩ := floorBinarySearch_nonneg_bounds keys t hpos hneg
  have hi31 : i + 1 < 2 ^ 31 := by omega
  by_cases hies : ¬ i < es.length
  · have hm : evalPiecewiseEasing (constEasingTransform hp) keys es t = none := by
      simp [evalPiecewiseEasing, piecewiseSegment, hidx, hilt, show es.length ≤ i by omega]
    rw [hm, Option.map_none, Option.map_eq_none_iff]
    lambda_prefix
    rw [runFast_invokeFloor hprog hrun, hjh, hhp, hidx, i32_ofInt_nat]
    ui_step_blk
    rw [runFast_floatList_get hilt (by omega)]
    ui_rfl_step
    ui_rfl_step
    exact runFast_easingList_get_oob (by omega) (by omega)
  rw [Decidable.not_not] at hies
  obtain ⟨eid, he, heid⟩ := hes es[i] (List.getElem_mem hies)
  have hg : hp.easings[eid]? = some hp.easings[eid] := Array.getElem?_eq_getElem heid
  have hgt : (UInt32.ofNat (i + 1)).toBitVec.slt (0 : UInt32).toBitVec = false :=
    Jvm.ui32_slt_zero_of_lt (i + 1) hi31
  by_cases hnext : i + 1 < keys.length
  · have hm : evalPiecewiseEasing (constEasingTransform hp) keys es t =
        some (hp.easings[eid] ((t - keys[i]) / (keys[i + 1] - keys[i]))) := by
      simp [evalPiecewiseEasing, piecewiseSegment, hidx, hilt, hies, hnext, he, constEasingTransform, hg]
    rw [hm, Option.map_some, Option.map_eq_some_iff]
    apply Exists.intro
    refine ⟨?_, ?_⟩
    lambda_prefix
    rw [runFast_invokeFloor hprog hrun, hjh, hhp, hidx, i32_ofInt_nat]
    ui_step_blk
    rw [runFast_floatList_get hilt (by omega)]
    ui_rfl_step
    ui_rfl_step
    rw [runFast_easingList_get hies (by omega), he]
    ui_rfl_step
    rw [show UInt32.ofNat i + 1 = UInt32.ofNat (i + 1) from (UInt32.ofNat_add i 1).symm]
    rw [runFast_if_icmpgt_fallthrough hgt]
    ui_step_blk
    rw [runFast_list_size_float]
    rw [runFast_if_icmpge_fallthrough (by rw [u32_sle_ofNat _ _ (by omega) hi31]; simp; omega)]
    ui_step_blk
    rw [Jvm.runJvmResFast_ifeq_fallthrough _ (by decide)]
    ui_step_blk
    rw [runFast_floatList_get hnext hi31]
    ui_step_blk
    ui_rfl_step
    ui_rfl_step
    rw [runFast_transform_const hg, runFast_freturn]
    rfl
  · have hm : evalPiecewiseEasing (constEasingTransform hp) keys es t =
        some (hp.easings[eid] ((t - keys[i]) / (1.0 - keys[i]))) := by
      simp [evalPiecewiseEasing, piecewiseSegment, hidx, hilt, hies, hnext, he, constEasingTransform, hg]
    rw [hm, Option.map_some, Option.map_eq_some_iff]
    apply Exists.intro
    refine ⟨?_, ?_⟩
    lambda_prefix
    rw [runFast_invokeFloor hprog hrun, hjh, hhp, hidx, i32_ofInt_nat]
    ui_step_blk
    rw [runFast_floatList_get hilt (by omega)]
    ui_rfl_step
    ui_rfl_step
    rw [runFast_easingList_get hies (by omega), he]
    ui_rfl_step
    rw [show UInt32.ofNat i + 1 = UInt32.ofNat (i + 1) from (UInt32.ofNat_add i 1).symm]
    rw [runFast_if_icmpgt_fallthrough hgt]
    ui_step_blk
    rw [runFast_list_size_float]
    rw [runFast_if_icmpge_branch (by rw [u32_sle_ofNat _ _ (by omega) hi31]; simp; omega)]
    conv => lhs; arg 5; dsimp only [EasingPiecewiseKt_Easing_lambda_3_prog, List.drop]
    ui_step_blk
    rw [Jvm.runJvmResFast_ifeq_branch _ (by decide)]
    conv => lhs; arg 5; dsimp only [EasingPiecewiseKt_Easing_lambda_3_prog, List.drop]
    ui_step_blk
    ui_rfl_step
    ui_rfl_step
    ui_rfl_step
    rw [runFast_transform_const hg, runFast_freturn, float32_ofBits_one]
    rfl

end UiCommon.KotlinJvmVerification
