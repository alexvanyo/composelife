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
import JvmSemantics
import KotlinJvmBytecode
import models.TargetStateModel

namespace UiCommon.KotlinJvmVerification

open UiCommon.JvmVerification
open UiCommon.KotlinJvmBytecode
open UiCommon.Model

/-! ### Shared Bytecode Program Lookup & Hooks -/

/-- Bytecode lookup table across all lifted `:ui-common` classes (`TargetState` + `EasingPiecewise`). -/
def uiProgLookup (fnTag : String) : Option (List JvmInstr) :=
  match fnTag with
  | "TargetStateKt.isInProgress" => some TargetStateKt_isInProgress_prog
  | "TargetStateKt.getProgressToTrue" => some TargetStateKt_getProgressToTrue_prog
  | "TargetStateKt.not" => some TargetStateKt_not_prog
  | "TargetStateKt.and" => some TargetStateKt_and_prog
  | "TargetStateKt.or" => some TargetStateKt_or_prog
  | "TargetStateKt.map" => some TargetStateKt_map_prog
  | "TargetState$InProgress.<init>" => some TargetState_InProgress_init_prog
  | "TargetState$InProgress.getCurrent" => some TargetState_InProgress_getCurrent_prog
  | "TargetState$InProgress.getProvisional" => some TargetState_InProgress_getProvisional_prog
  | "TargetState$InProgress.getProgress" => some TargetState_InProgress_getProgress_prog
  | "TargetState$InProgress.getMetadata" => some TargetState_InProgress_getMetadata_prog
  | "TargetState$InProgress.component1" => some TargetState_InProgress_component1_prog
  | "TargetState$InProgress.component2" => some TargetState_InProgress_component2_prog
  | "TargetState$InProgress.component3" => some TargetState_InProgress_component3_prog
  | "TargetState$InProgress.component4" => some TargetState_InProgress_component4_prog
  | "TargetState$InProgress.copy" => some TargetState_InProgress_copy_prog
  | "TargetState$InProgress.copy$default" => some TargetState_InProgress_copy_default_prog
  | "TargetState$InProgress.toString" => some TargetState_InProgress_toString_prog
  | "TargetState$InProgress.hashCode" => some TargetState_InProgress_hashCode_prog
  | "TargetState$InProgress.equals" => some TargetState_InProgress_equals_prog
  | "EasingPiecewiseKt.Easing" => some EasingPiecewiseKt_Easing_prog
  | "EasingPiecewiseKt.floorBinarySearch" => some EasingPiecewiseKt_floorBinarySearch_prog
  | "EasingPiecewiseKt.Easing$lambda$3" => some EasingPiecewiseKt_Easing_lambda_3_prog
  | _ => none

abbrev uiHooks (depth subFuel : Nat) : Jvm.JvmHooks UiExt UiHeap :=
  mkUiCommonHooks uiProgLookup depth subFuel

def ExtendsUiProgs (resolveProg : String → Option (List JvmInstr)) : Prop :=
  ∀ fnTag prog, uiProgLookup fnTag = some prog → resolveProg fnTag = some prog

theorem uiProgLookup_extends : ExtendsUiProgs uiProgLookup :=
  fun _ _ h => h

/-! ### Non-Looping Projection Lemmas for `mkUiCommonHooks` -/

theorem mkUiCommonHooks_beqExt (r : String → Option (List JvmInstr)) (d sf : Nat) :
    (mkUiCommonHooks r d sf).beqExt = beqUiExt := by cases d <;> rfl

theorem mkUiCommonHooks_beqRefExt (r : String → Option (List JvmInstr)) (d sf : Nat) :
    (mkUiCommonHooks r d sf).beqRefExt = beqRefUiExt := by cases d <;> rfl

theorem mkUiCommonHooks_isSubtypeOf (r : String → Option (List JvmInstr)) (d sf : Nat) :
    (mkUiCommonHooks r d sf).isSubtypeOf = isUiCommonSubtypeOf := by cases d <;> rfl

theorem mkUiCommonHooks_isZero? (r : String → Option (List JvmInstr)) (d sf : Nat) :
    (mkUiCommonHooks r d sf).isZero? = fun v => v.asI32?.map (· == 0) := by cases d <;> rfl

theorem mkUiCommonHooks_ireturnVal (r : String → Option (List JvmInstr)) (d sf : Nat) :
    (mkUiCommonHooks r d sf).ireturnVal = id := by cases d <;> rfl

theorem mkUiCommonHooks_stepNewClass_single (r : String → Option (List JvmInstr)) (d sf : Nat)
    (st : JvmState) :
    (mkUiCommonHooks r d sf).stepNewClass st "com/alexvanyo/composelife/ui/util/TargetState$Single" =
      let (addr, jh') := st.jvmHeap.alloc (.instance "com/alexvanyo/composelife/ui/util/TargetState$Single" [])
      .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: st.stack, jvmHeap := jh' }) := by
  cases d <;> rfl

theorem mkUiCommonHooks_stepNewClass_inProgress (r : String → Option (List JvmInstr)) (d sf : Nat)
    (st : JvmState) :
    (mkUiCommonHooks r d sf).stepNewClass st "com/alexvanyo/composelife/ui/util/TargetState$InProgress" =
      let (addr, jh') := st.jvmHeap.alloc (.instance "com/alexvanyo/composelife/ui/util/TargetState$InProgress" [])
      .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: st.stack, jvmHeap := jh' }) := by
  cases d <;> rfl

theorem mkUiCommonHooks_stepNewClass_other (r : String → Option (List JvmInstr)) (d sf : Nat)
    (st : JvmState) (cls : String)
    (h1 : normalizeUiCommonClass cls ≠ "TargetState$Single")
    (h2 : normalizeUiCommonClass cls ≠ "TargetState$InProgress") :
    (mkUiCommonHooks r d sf).stepNewClass st cls =
      Sum.inl (some { st with pc := st.pc + 1, stack := .allocRef cls :: st.stack }) := by
  cases d <;>
  · change (match normalizeUiCommonClass cls with
      | "TargetState$Single" | "TargetState$InProgress" =>
        let (addr, jh') := st.jvmHeap.alloc (.instance cls [])
        Sum.inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: st.stack, jvmHeap := jh' })
      | _ => Sum.inl (some { st with pc := st.pc + 1, stack := .allocRef cls :: st.stack })) = _
    split
    · next heq => exact absurd heq h1
    · next heq => exact absurd heq h2
    · rfl

theorem mkUiCommonHooks_stepInvokeSpecial_objInit_heapRef (r : String → Option (List JvmInstr))
    (d sf pc : Nat) (addr : Nat) (rest : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    (mkUiCommonHooks r d sf).stepInvokeSpecial ⟨pc, .heapRef addr :: rest, locs, jh, hp⟩
        "java/lang/Object" "<init>" "()V" =
      .inl (some ⟨pc + 1, rest, locs, jh, hp⟩) := by
  cases d <;> rfl

theorem mkUiCommonHooks_stepInvokeSpecial_companion (r : String → Option (List JvmInstr))
    (d sf pc : Nat) (marker : JvmVal) (c1 c2 : String) (rest : List JvmVal)
    (locs : Nat → JvmVal) (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    (mkUiCommonHooks r d sf).stepInvokeSpecial
        ⟨pc, marker :: .allocRef c1 :: .allocRef c2 :: rest, locs, jh, hp⟩
        "com/alexvanyo/composelife/ui/util/TargetState$InProgress$Companion"
        "<init>" "(Lkotlin/jvm/internal/DefaultConstructorMarker;)V" =
      .inl (some ⟨pc + 1, .ext (.companion "TargetState$InProgress$Companion") :: rest,
        locs, jh, hp⟩) := by
  cases d <;> rfl

theorem mkUiCommonHooks_stepInvokeVirtual_single_getCurrent (r : String → Option (List JvmInstr))
    (d sf pc : Nat) (addr : Nat) (rest : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    (mkUiCommonHooks r d sf).stepInvokeVirtual ⟨pc, .heapRef addr :: rest, locs, jh, hp⟩
        "com/alexvanyo/composelife/ui/util/TargetState$Single" "getCurrent" "()Ljava/lang/Object;" =
      match jh.get? addr >>= fun obj => obj.getField? isUiCommonSubtypeOf "TargetState$Single" "current" with
      | some v => .inl (some ⟨pc + 1, v :: rest, locs, jh, hp⟩)
      | none => .inr none := by
  cases d <;> rfl

theorem mkUiCommonHooks_stepInvokeVirtual_obj_hashCode (r : String → Option (List JvmInstr))
    (d sf pc : Nat) (v : JvmVal) (rest : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    (mkUiCommonHooks r d sf).stepInvokeVirtual ⟨pc, v :: rest, locs, jh, hp⟩
        "java/lang/Object" "hashCode" "()I" =
      match jvmValHashCode v with
      | some h => .inl (some ⟨pc + 1, .i32 h :: rest, locs, jh, hp⟩)
      | none => .inr none := by
  cases d <;> rfl

theorem mkUiCommonHooks_stepInvokeStatic_float_hashCode (r : String → Option (List JvmInstr))
    (d sf pc : Nat) (f : Float32) (rest : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    (mkUiCommonHooks r d sf).stepInvokeStatic ⟨pc, .f32 f :: rest, locs, jh, hp⟩
        "java/lang/Float" "hashCode" "(F)I" =
      .inl (some ⟨pc + 1, .i32 (floatHashCode f) :: rest, locs, jh, hp⟩) := by
  cases d <;> rfl

theorem mkUiCommonHooks_stepInvokeStatic_float_compare (r : String → Option (List JvmInstr))
    (d sf pc : Nat) (a b : Float32) (rest : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    (mkUiCommonHooks r d sf).stepInvokeStatic ⟨pc, .f32 b :: .f32 a :: rest, locs, jh, hp⟩
        "java/lang/Float" "compare" "(FF)I" =
      .inl (some ⟨pc + 1, .i32 (Model.floatCompare a b).toUInt32 :: rest, locs, jh, hp⟩) := by
  cases d <;> rfl

theorem mkUiCommonHooks_stepInvokeSpecial_single_init (r : String → Option (List JvmInstr))
    (d sf pc addr : Nat) (arg : JvmVal) (rest : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    (mkUiCommonHooks r d sf).stepInvokeSpecial ⟨pc, arg :: .heapRef addr :: rest, locs, jh, hp⟩
        "com/alexvanyo/composelife/ui/util/TargetState$Single" "<init>" "(Ljava/lang/Object;)V" =
      match jh.get? addr with
      | some (.instance objCls fields) =>
        if isUiCommonSubtypeOf objCls "TargetState$Single" then
          let fields' := ("current", arg) :: fields.filter (fun (f, _) => f != "current")
          .inl (some ⟨pc + 1, rest, locs, jh.set addr (.instance objCls fields'), hp⟩)
        else .inr none
      | _ => .inr none := by
  cases d <;> rfl

theorem mkUiCommonHooks_resolveStatic (r : String → Option (List JvmInstr)) (d sf : Nat) :
    (mkUiCommonHooks r d sf).resolveStatic = resolveUiStatic := by
  cases d <;> rfl

theorem mkUiCommonHooks_checkInstanceOf (r : String → Option (List JvmInstr)) (d sf : Nat) :
    (mkUiCommonHooks r d sf).checkInstanceOf = checkUiInstanceOf := by
  cases d <;> rfl

theorem mkUiCommonHooks_checkCast (r : String → Option (List JvmInstr)) (d sf : Nat) :
    (mkUiCommonHooks r d sf).checkCast = checkUiCast := by
  cases d <;> rfl

/-! ### Heap Representation Predicates for `TargetState.Single` and `TargetState.InProgress` -/

def singleInstance (c : JvmVal) : Jvm.HeapObj UiExt :=
  .instance "com/alexvanyo/composelife/ui/util/TargetState$Single" [("current", c)]

def inProgressInstance (c p : JvmVal) (pr : Float32) (m : JvmVal) : Jvm.HeapObj UiExt :=
  .instance "com/alexvanyo/composelife/ui/util/TargetState$InProgress"
    [("metadata", m), ("progress", .f32 pr), ("provisional", p), ("current", c)]

def HasSingleFields (jh : Jvm.JvmHeap UiExt) (addr : Nat) (c : JvmVal) : Prop :=
  ∃ cls fields,
    jh.get? addr = some (.instance cls fields) ∧
    (cls = "com/alexvanyo/composelife/ui/util/TargetState$Single" ∨ cls = "TargetState$Single") ∧
    (fields.find? (fun (f, _) => f == "current")).map Prod.snd = some c

def HasInProgressFields (jh : Jvm.JvmHeap UiExt) (addr : Nat)
    (c p : JvmVal) (pr : Float32) (m : JvmVal) : Prop :=
  ∃ cls fields,
    jh.get? addr = some (.instance cls fields) ∧
    (cls = "com/alexvanyo/composelife/ui/util/TargetState$InProgress" ∨ cls = "TargetState$InProgress") ∧
    (fields.find? (fun (f, _) => f == "current")).map Prod.snd = some c ∧
    (fields.find? (fun (f, _) => f == "provisional")).map Prod.snd = some p ∧
    (fields.find? (fun (f, _) => f == "progress")).map Prod.snd = some (.f32 pr) ∧
    (fields.find? (fun (f, _) => f == "metadata")).map Prod.snd = some m

theorem hasSingleFields_singleInstance (jh : Jvm.JvmHeap UiExt) (addr : Nat) (c : JvmVal)
    (h : jh.get? addr = some (singleInstance c)) :
    HasSingleFields jh addr c :=
  ⟨"com/alexvanyo/composelife/ui/util/TargetState$Single", [("current", c)],
    h, Or.inl rfl, rfl⟩

theorem hasInProgressFields_inProgressInstance (jh : Jvm.JvmHeap UiExt) (addr : Nat)
    (c p : JvmVal) (pr : Float32) (m : JvmVal)
    (h : jh.get? addr = some (inProgressInstance c p pr m)) :
    HasInProgressFields jh addr c p pr m :=
  ⟨"com/alexvanyo/composelife/ui/util/TargetState$InProgress",
    [("metadata", m), ("progress", .f32 pr), ("provisional", p), ("current", c)],
    h, Or.inl rfl, rfl, rfl, rfl, rfl⟩

theorem hasSingleFields_alloc {jh : Jvm.JvmHeap UiExt} {addr : Nat} {c : JvmVal}
    (hs : HasSingleFields jh addr c) (obj : Jvm.HeapObj UiExt) :
    HasSingleFields (jh.alloc obj).2 addr c := by
  rcases hs with ⟨cls, fields, hget, hcls, h3⟩
  have hlt : addr < jh.objects.size := Jvm.jvmHeap_get?_some_lt hget
  refine ⟨cls, fields, ?_, hcls, h3⟩
  rw [Jvm.jvmHeap_get?_alloc_old jh obj hlt]
  exact hget

theorem hasInProgressFields_alloc {jh : Jvm.JvmHeap UiExt} {addr : Nat}
    {c p : JvmVal} {pr : Float32} {m : JvmVal}
    (hi : HasInProgressFields jh addr c p pr m) (obj : Jvm.HeapObj UiExt) :
    HasInProgressFields (jh.alloc obj).2 addr c p pr m := by
  rcases hi with ⟨cls, fields, hget, hcls, hc, hp, hpr, hm⟩
  have hlt : addr < jh.objects.size := Jvm.jvmHeap_get?_some_lt hget
  refine ⟨cls, fields, ?_, hcls, hc, hp, hpr, hm⟩
  rw [Jvm.jvmHeap_get?_alloc_old jh obj hlt]
  exact hget

/-! ### Step Helpers -/

private theorem checkInstanceOf_single (resolveProg : String → Option (List JvmInstr))
    (d sf : Nat) {jh : Jvm.JvmHeap UiExt} {addr : Nat} {c : JvmVal}
    (hs : HasSingleFields jh addr c) :
    jh.checkInstanceOf "com/alexvanyo/composelife/ui/util/TargetState$Single" addr
        (mkUiCommonHooks resolveProg d sf).isSubtypeOf = true := by
  rcases hs with ⟨cls, fields, hget, hcls, _⟩
  rw [mkUiCommonHooks_isSubtypeOf]
  rcases hcls with rfl | rfl <;>
    simp [Jvm.JvmHeap.checkInstanceOf, hget, Jvm.HeapObj.matchesType, isUiCommonSubtypeOf,
      normalizeUiCommonClass]

private theorem checkInstanceOf_single_not_inProgress (resolveProg : String → Option (List JvmInstr))
    (d sf : Nat) {jh : Jvm.JvmHeap UiExt} {addr : Nat} {c : JvmVal}
    (hs : HasSingleFields jh addr c) :
    jh.checkInstanceOf "com/alexvanyo/composelife/ui/util/TargetState$InProgress" addr
        (mkUiCommonHooks resolveProg d sf).isSubtypeOf = false := by
  rcases hs with ⟨cls, fields, hget, hcls, _⟩
  rw [mkUiCommonHooks_isSubtypeOf]
  rcases hcls with rfl | rfl <;>
    simp [Jvm.JvmHeap.checkInstanceOf, hget, Jvm.HeapObj.matchesType, isUiCommonSubtypeOf,
      normalizeUiCommonClass, Jvm.defaultIsSubtypeOf]

private theorem checkInstanceOf_inProgress (resolveProg : String → Option (List JvmInstr))
    (d sf : Nat) {jh : Jvm.JvmHeap UiExt} {addr : Nat} {c p : JvmVal} {pr : Float32} {m : JvmVal}
    (hi : HasInProgressFields jh addr c p pr m) :
    jh.checkInstanceOf "com/alexvanyo/composelife/ui/util/TargetState$InProgress" addr
        (mkUiCommonHooks resolveProg d sf).isSubtypeOf = true := by
  rcases hi with ⟨cls, fields, hget, hcls, _⟩
  rw [mkUiCommonHooks_isSubtypeOf]
  rcases hcls with rfl | rfl <;>
    simp [Jvm.JvmHeap.checkInstanceOf, hget, Jvm.HeapObj.matchesType, isUiCommonSubtypeOf,
      normalizeUiCommonClass]

private theorem checkInstanceOf_inProgress_not_single (resolveProg : String → Option (List JvmInstr))
    (d sf : Nat) {jh : Jvm.JvmHeap UiExt} {addr : Nat} {c p : JvmVal} {pr : Float32} {m : JvmVal}
    (hi : HasInProgressFields jh addr c p pr m) :
    jh.checkInstanceOf "com/alexvanyo/composelife/ui/util/TargetState$Single" addr
        (mkUiCommonHooks resolveProg d sf).isSubtypeOf = false := by
  rcases hi with ⟨cls, fields, hget, hcls, _⟩
  rw [mkUiCommonHooks_isSubtypeOf]
  rcases hcls with rfl | rfl <;>
    simp [Jvm.JvmHeap.checkInstanceOf, hget, Jvm.HeapObj.matchesType, isUiCommonSubtypeOf,
      normalizeUiCommonClass, Jvm.defaultIsSubtypeOf]

private theorem evalCheckCast_single (resolveProg : String → Option (List JvmInstr))
    (d sf : Nat) {jh : Jvm.JvmHeap UiExt} {addr : Nat} {c : JvmVal}
    (hs : HasSingleFields jh addr c) :
    Jvm.evalCheckCast (mkUiCommonHooks resolveProg d sf) jh
        "com/alexvanyo/composelife/ui/util/TargetState$Single" (.heapRef addr) =
      some (.heapRef addr) := by
  simp [Jvm.evalCheckCast, Jvm.JvmHeap.checkCast, checkInstanceOf_single resolveProg d sf hs]

private theorem evalCheckCast_inProgress (resolveProg : String → Option (List JvmInstr))
    (d sf : Nat) {jh : Jvm.JvmHeap UiExt} {addr : Nat} {c p : JvmVal} {pr : Float32} {m : JvmVal}
    (hi : HasInProgressFields jh addr c p pr m) :
    Jvm.evalCheckCast (mkUiCommonHooks resolveProg d sf) jh
        "com/alexvanyo/composelife/ui/util/TargetState$InProgress" (.heapRef addr) =
      some (.heapRef addr) := by
  simp [Jvm.evalCheckCast, Jvm.JvmHeap.checkCast, checkInstanceOf_inProgress resolveProg d sf hi]

private theorem evalCheckCast_targetState_of_single (resolveProg : String → Option (List JvmInstr))
    (d sf : Nat) {jh : Jvm.JvmHeap UiExt} {addr : Nat} {c : JvmVal}
    (hs : HasSingleFields jh addr c) :
    Jvm.evalCheckCast (mkUiCommonHooks resolveProg d sf) jh
        "com/alexvanyo/composelife/ui/util/TargetState" (.heapRef addr) =
      some (.heapRef addr) := by
  rcases hs with ⟨cls, fields, hget, hcls, _⟩
  rcases hcls with rfl | rfl <;>
    simp [Jvm.evalCheckCast, Jvm.JvmHeap.checkCast, Jvm.JvmHeap.checkInstanceOf,
      hget, Jvm.HeapObj.matchesType, mkUiCommonHooks_isSubtypeOf, isUiCommonSubtypeOf,
      normalizeUiCommonClass]

private theorem evalCheckCast_targetState_of_inProgress (resolveProg : String → Option (List JvmInstr))
    (d sf : Nat) {jh : Jvm.JvmHeap UiExt} {addr : Nat} {c p : JvmVal} {pr : Float32} {m : JvmVal}
    (hi : HasInProgressFields jh addr c p pr m) :
    Jvm.evalCheckCast (mkUiCommonHooks resolveProg d sf) jh
        "com/alexvanyo/composelife/ui/util/TargetState" (.heapRef addr) =
      some (.heapRef addr) := by
  rcases hi with ⟨cls, fields, hget, hcls, _⟩
  rcases hcls with rfl | rfl <;>
    simp [Jvm.evalCheckCast, Jvm.JvmHeap.checkCast, Jvm.JvmHeap.checkInstanceOf,
      hget, Jvm.HeapObj.matchesType, mkUiCommonHooks_isSubtypeOf, isUiCommonSubtypeOf,
      normalizeUiCommonClass]

private theorem stepInvokeVirtual_single_getCurrent (resolveProg : String → Option (List JvmInstr))
    (d sf pc : Nat) {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap UiExt} {hp : UiHeap}
    {addr : Nat} {c : JvmVal} (hs : HasSingleFields jh addr c) :
    Jvm.stepInvokeVirtualGeneric (mkUiCommonHooks resolveProg d sf)
        ⟨pc, .heapRef addr :: stk, locs, jh, hp⟩
        "com/alexvanyo/composelife/ui/util/TargetState$Single" "getCurrent" "()Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, c :: stk, locs, jh, hp⟩) := by
  rcases hs with ⟨cls, fields, hget, hcls, hc⟩
  dsimp [Jvm.stepInvokeVirtualGeneric]
  rw [mkUiCommonHooks_stepInvokeVirtual_single_getCurrent _ _ _ _ addr stk]
  rcases hcls with rfl | rfl <;>
    simp [hget, Jvm.HeapObj.getField?, isUiCommonSubtypeOf, normalizeUiCommonClass, hc]

private theorem stepInstr_getfield_instance (hooks : Jvm.JvmHooks UiExt UiHeap)
    {pc addr : Nat} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap UiExt} {hp : UiHeap} {objCls cls fld desc : String}
    {fields : List (String × JvmVal)} {v : JvmVal}
    (hget : jh.get? addr = some (.instance objCls fields))
    (hsub : (objCls == cls || hooks.isSubtypeOf objCls cls) = true)
    (hfld : (fields.find? (fun (f, _) => f == fld)).map Prod.snd = some v) :
    Jvm.stepInstr hooks (.getfield cls fld desc) ⟨pc, .heapRef addr :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, v :: stk, locs, jh, hp⟩) := by
  unfold Jvm.stepInstr
  simp [hget, hsub, hfld]

private theorem stepGetField_inProgress (resolveProg : String → Option (List JvmInstr))
    (d sf pc : Nat) {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap UiExt} {hp : UiHeap}
    {addr : Nat} {c p : JvmVal} {pr : Float32} {m : JvmVal}
    (hi : HasInProgressFields jh addr c p pr m) :
    (Jvm.stepInstr (mkUiCommonHooks resolveProg d sf) (.getfield "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "current" "Ljava/lang/Object;")
        ⟨pc, .heapRef addr :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, c :: stk, locs, jh, hp⟩)) ∧
    (Jvm.stepInstr (mkUiCommonHooks resolveProg d sf) (.getfield "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "provisional" "Ljava/lang/Object;")
        ⟨pc, .heapRef addr :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, p :: stk, locs, jh, hp⟩)) ∧
    (Jvm.stepInstr (mkUiCommonHooks resolveProg d sf) (.getfield "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "progress" "F")
        ⟨pc, .heapRef addr :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .f32 pr :: stk, locs, jh, hp⟩)) ∧
    (Jvm.stepInstr (mkUiCommonHooks resolveProg d sf) (.getfield "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "metadata" "Ljava/lang/Object;")
        ⟨pc, .heapRef addr :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, m :: stk, locs, jh, hp⟩)) := by
  rcases hi with ⟨cls, fields, hget, hcls, hc, hp_, hpr, hm⟩
  have hsub : (cls == "com/alexvanyo/composelife/ui/util/TargetState$InProgress" ||
      (mkUiCommonHooks resolveProg d sf).isSubtypeOf cls "com/alexvanyo/composelife/ui/util/TargetState$InProgress") = true := by
    rw [mkUiCommonHooks_isSubtypeOf]
    rcases hcls with rfl | rfl <;> rfl
  exact ⟨stepInstr_getfield_instance _ hget hsub hc,
    stepInstr_getfield_instance _ hget hsub hp_,
    stepInstr_getfield_instance _ hget hsub hpr,
    stepInstr_getfield_instance _ hget hsub hm⟩

/-! ### `TargetState$InProgress` Method Equivalence Theorems (15 methods) -/

private theorem stepInstr_newClass_other (r : String → Option (List JvmInstr))
    (d sf pc : Nat) (cls : String) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap)
    (h0 : cls ≠ "java/lang/StringBuilder")
    (h1 : normalizeUiCommonClass cls ≠ "TargetState$Single")
    (h2 : normalizeUiCommonClass cls ≠ "TargetState$InProgress") :
    Jvm.stepInstr (mkUiCommonHooks r d sf) (.newClass cls) ⟨pc, stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .allocRef cls :: stk, locs, jh, hp⟩) := by
  unfold Jvm.stepInstr
  simp [h0, mkUiCommonHooks_stepNewClass_other r d sf ⟨pc, stk, locs, jh, hp⟩ cls h1 h2]

private theorem stepInstr_invokespecial_companion (r : String → Option (List JvmInstr))
    (d sf pc : Nat) (marker : JvmVal) (c1 c2 : String) (rest : List JvmVal)
    (locs : Nat → JvmVal) (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    Jvm.stepInstr (mkUiCommonHooks r d sf)
        (.invokespecial "com/alexvanyo/composelife/ui/util/TargetState$InProgress$Companion"
          "<init>" "(Lkotlin/jvm/internal/DefaultConstructorMarker;)V")
        ⟨pc, marker :: .allocRef c1 :: .allocRef c2 :: rest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .ext (.companion "TargetState$InProgress$Companion") :: rest, locs, jh, hp⟩) := by
  cases d <;> rfl

private theorem stepInstr_dup (hooks : Jvm.JvmHooks UiExt UiHeap)
    (pc : Nat) (v : JvmVal) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    Jvm.stepInstr hooks .dup ⟨pc, v :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, v :: v :: stk, locs, jh, hp⟩) := rfl

private theorem stepInstr_aconstNull (hooks : Jvm.JvmHooks UiExt UiHeap)
    (pc : Nat) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    Jvm.stepInstr hooks .aconstNull ⟨pc, stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .null :: stk, locs, jh, hp⟩) := rfl

private theorem stepInstr_putstatic (r : String → Option (List JvmInstr)) (d sf : Nat)
    (pc : Nat) (cls fld desc : String) (v : JvmVal) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    Jvm.stepInstr (mkUiCommonHooks r d sf) (.putstatic cls fld desc) ⟨pc, v :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, stk, locs, jh.setStatic cls fld v, hp⟩) := by
  cases d <;> rfl

private theorem stepInstr_aload (hooks : Jvm.JvmHooks UiExt UiHeap)
    (pc idx : Nat) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    Jvm.stepInstr hooks (.aload idx) ⟨pc, stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, locs idx :: stk, locs, jh, hp⟩) := rfl

private theorem stepInstr_fload_f32 (hooks : Jvm.JvmHooks UiExt UiHeap)
    (pc idx : Nat) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) (v : Float32) (hloc : locs idx = .f32 v) :
    Jvm.stepInstr hooks (.fload idx) ⟨pc, stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .f32 v :: stk, locs, jh, hp⟩) := by
  unfold Jvm.stepInstr; simp [hloc]

private theorem stepInstr_iconst (hooks : Jvm.JvmHooks UiExt UiHeap)
    (pc : Nat) (n : UInt32) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    Jvm.stepInstr hooks (.iconst n) ⟨pc, stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 n :: stk, locs, jh, hp⟩) := rfl

private theorem stepInstr_istore_i32 (hooks : Jvm.JvmHooks UiExt UiHeap)
    (pc idx : Nat) (n : UInt32) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    Jvm.stepInstr hooks (.istore idx) ⟨pc, .i32 n :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, stk, setLocal locs idx (.i32 n), jh, hp⟩) := by
  unfold Jvm.stepInstr; simp

private theorem stepInstr_astore (hooks : Jvm.JvmHooks UiExt UiHeap)
    (pc idx : Nat) (v : JvmVal) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    Jvm.stepInstr hooks (.astore idx) ⟨pc, v :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, stk, setLocal locs idx v, jh, hp⟩) := rfl

private theorem stepInstr_ldcStr (hooks : Jvm.JvmHooks UiExt UiHeap)
    (pc : Nat) (s : String) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    Jvm.stepInstr hooks (.ldcStr s) ⟨pc, stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .str s :: stk, locs, jh, hp⟩) := rfl

private theorem stepInstr_nop (hooks : Jvm.JvmHooks UiExt UiHeap)
    (pc : Nat) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    Jvm.stepInstr hooks .nop ⟨pc, stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, stk, locs, jh, hp⟩) := rfl

private theorem stepInstr_vreturn (hooks : Jvm.JvmHooks UiExt UiHeap)
    (pc : Nat) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    Jvm.stepInstr hooks .vreturn ⟨pc, stk, locs, jh, hp⟩ = .inr (some .unit) := rfl

private theorem stepInstr_areturn (hooks : Jvm.JvmHooks UiExt UiHeap)
    (pc : Nat) (v : JvmVal) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    Jvm.stepInstr hooks .areturn ⟨pc, v :: stk, locs, jh, hp⟩ = .inr (some v) := rfl

private theorem stepInstr_freturn (hooks : Jvm.JvmHooks UiExt UiHeap)
    (pc : Nat) (v : Float32) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    Jvm.stepInstr hooks .freturn ⟨pc, .f32 v :: stk, locs, jh, hp⟩ = .inr (some (.f32 v)) := rfl

private theorem stepInstr_invokeVirtual_obj_toString_str (hooks : Jvm.JvmHooks UiExt UiHeap)
    (pc : Nat) (s : String) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    Jvm.stepInstr hooks (.invokevirtual "java/lang/Object" "toString" "()Ljava/lang/String;")
        ⟨pc, .str s :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .str s :: stk, locs, jh, hp⟩) := rfl

private theorem stepInstr_invokeSpecial_iae_init (hooks : Jvm.JvmHooks UiExt UiHeap)
    (pc : Nat) (msg : JvmVal) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    Jvm.stepInstr hooks (.invokespecial "java/lang/IllegalArgumentException" "<init>" "(Ljava/lang/String;)V")
        ⟨pc, msg :: .allocRef "java/lang/IllegalArgumentException" ::
          .allocRef "java/lang/IllegalArgumentException" :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .allocRef "java/lang/IllegalArgumentException" :: stk, locs, jh, hp⟩) := rfl

theorem clinit_TargetState_InProgress_equiv (resolveProg : String → Option (List JvmInstr))
    (depth sf fuel : Nat) (hf : 10 ≤ fuel) (hp : UiHeap) (jh : Jvm.JvmHeap UiExt) :
    ∃ st',
      Jvm.runJvmRes (mkUiCommonHooks resolveProg depth sf) fuel
          TargetState_InProgress_clinit_prog (initUiJvmState [] hp jh) =
        some (.unit, st') ∧
      st'.jvmHeap.getStatic? "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "Companion" =
        some (.ext (.companion "TargetState$InProgress$Companion")) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  refine ⟨⟨5, [], (initUiJvmState [] hp jh).locals,
      jh.setStatic "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "Companion"
        (.ext (.companion "TargetState$InProgress$Companion")), hp⟩, ?_, ?_⟩
  · dsimp only [initUiJvmState, Jvm.initJvmState]
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.newClass "com/alexvanyo/composelife/ui/util/TargetState$InProgress$Companion") (by rfl) rfl]
    rw [stepInstr_newClass_other _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide)]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ .dup (by rfl) rfl]
    rw [stepInstr_dup]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ .aconstNull (by rfl) rfl]
    rw [stepInstr_aconstNull]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokespecial "com/alexvanyo/composelife/ui/util/TargetState$InProgress$Companion" "<init>" "(Lkotlin/jvm/internal/DefaultConstructorMarker;)V") (by rfl) rfl]
    rw [stepInstr_invokespecial_companion]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.putstatic "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "Companion" "Lcom/alexvanyo/composelife/ui/util/TargetState$InProgress$Companion;") (by rfl) rfl]
    rw [stepInstr_putstatic]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ .vreturn (by rfl) rfl]
    rw [stepInstr_vreturn]
  · simp [Jvm.JvmHeap.setStatic, Jvm.JvmHeap.getStatic?]

theorem getCurrent_equiv (resolveProg : String → Option (List JvmInstr))
    (depth sf fuel : Nat) (hf : 5 ≤ fuel)
    {jh : Jvm.JvmHeap UiExt} {addr : Nat} {c p : JvmVal} {pr : Float32} {m : JvmVal}
    (hi : HasInProgressFields jh addr c p pr m) (hp : UiHeap) :
    ∃ st',
      Jvm.runJvmRes (mkUiCommonHooks resolveProg depth sf) fuel
          TargetState_InProgress_getCurrent_prog (initUiJvmState [(0, .heapRef addr)] hp jh) =
        some (c, st') ∧
      st'.jvmHeap = jh ∧ st'.heap = hp := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  refine ⟨⟨2, [c], (initUiJvmState [(0, .heapRef addr)] hp jh).locals, jh, hp⟩, ?_, rfl, rfl⟩
  dsimp only [initUiJvmState, Jvm.initJvmState]
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]
  rw [stepInstr_aload]; simp only [List.foldl_cons, List.foldl_nil, Jvm.setLocal, ↓reduceIte]
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.getfield "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "current" "Ljava/lang/Object;") (by rfl) rfl]
  rw [(stepGetField_inProgress resolveProg depth sf 1 hi).1]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ .areturn (by rfl) rfl]
  rw [stepInstr_areturn]

theorem getProvisional_equiv (resolveProg : String → Option (List JvmInstr))
    (depth sf fuel : Nat) (hf : 5 ≤ fuel)
    {jh : Jvm.JvmHeap UiExt} {addr : Nat} {c p : JvmVal} {pr : Float32} {m : JvmVal}
    (hi : HasInProgressFields jh addr c p pr m) (hp : UiHeap) :
    ∃ st',
      Jvm.runJvmRes (mkUiCommonHooks resolveProg depth sf) fuel
          TargetState_InProgress_getProvisional_prog (initUiJvmState [(0, .heapRef addr)] hp jh) =
        some (p, st') ∧
      st'.jvmHeap = jh ∧ st'.heap = hp := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  refine ⟨⟨2, [p], (initUiJvmState [(0, .heapRef addr)] hp jh).locals, jh, hp⟩, ?_, rfl, rfl⟩
  dsimp only [initUiJvmState, Jvm.initJvmState]
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]
  rw [stepInstr_aload]; simp only [List.foldl_cons, List.foldl_nil, Jvm.setLocal, ↓reduceIte]
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.getfield "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "provisional" "Ljava/lang/Object;") (by rfl) rfl]
  rw [(stepGetField_inProgress resolveProg depth sf 1 hi).2.1]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ .areturn (by rfl) rfl]
  rw [stepInstr_areturn]

theorem getProgress_equiv (resolveProg : String → Option (List JvmInstr))
    (depth sf fuel : Nat) (hf : 5 ≤ fuel)
    {jh : Jvm.JvmHeap UiExt} {addr : Nat} {c p : JvmVal} {pr : Float32} {m : JvmVal}
    (hi : HasInProgressFields jh addr c p pr m) (hp : UiHeap) :
    ∃ st',
      Jvm.runJvmRes (mkUiCommonHooks resolveProg depth sf) fuel
          TargetState_InProgress_getProgress_prog (initUiJvmState [(0, .heapRef addr)] hp jh) =
        some (.f32 pr, st') ∧
      st'.jvmHeap = jh ∧ st'.heap = hp := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  refine ⟨⟨2, [.f32 pr], (initUiJvmState [(0, .heapRef addr)] hp jh).locals, jh, hp⟩, ?_, rfl, rfl⟩
  dsimp only [initUiJvmState, Jvm.initJvmState]
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]
  rw [stepInstr_aload]; simp only [List.foldl_cons, List.foldl_nil, Jvm.setLocal, ↓reduceIte]
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.getfield "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "progress" "F") (by rfl) rfl]
  rw [(stepGetField_inProgress resolveProg depth sf 1 hi).2.2.1]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ .freturn (by rfl) rfl]
  rw [stepInstr_freturn]

theorem getMetadata_equiv (resolveProg : String → Option (List JvmInstr))
    (depth sf fuel : Nat) (hf : 5 ≤ fuel)
    {jh : Jvm.JvmHeap UiExt} {addr : Nat} {c p : JvmVal} {pr : Float32} {m : JvmVal}
    (hi : HasInProgressFields jh addr c p pr m) (hp : UiHeap) :
    ∃ st',
      Jvm.runJvmRes (mkUiCommonHooks resolveProg depth sf) fuel
          TargetState_InProgress_getMetadata_prog (initUiJvmState [(0, .heapRef addr)] hp jh) =
        some (m, st') ∧
      st'.jvmHeap = jh ∧ st'.heap = hp := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  refine ⟨⟨2, [m], (initUiJvmState [(0, .heapRef addr)] hp jh).locals, jh, hp⟩, ?_, rfl, rfl⟩
  dsimp only [initUiJvmState, Jvm.initJvmState]
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]
  rw [stepInstr_aload]; simp only [List.foldl_cons, List.foldl_nil, Jvm.setLocal, ↓reduceIte]
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.getfield "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "metadata" "Ljava/lang/Object;") (by rfl) rfl]
  rw [(stepGetField_inProgress resolveProg depth sf 1 hi).2.2.2]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ .areturn (by rfl) rfl]
  rw [stepInstr_areturn]

theorem component1_equiv (resolveProg : String → Option (List JvmInstr))
    (depth sf fuel : Nat) (hf : 5 ≤ fuel)
    {jh : Jvm.JvmHeap UiExt} {addr : Nat} {c p : JvmVal} {pr : Float32} {m : JvmVal}
    (hi : HasInProgressFields jh addr c p pr m) (hp : UiHeap) :
    ∃ st',
      Jvm.runJvmRes (mkUiCommonHooks resolveProg depth sf) fuel
          TargetState_InProgress_component1_prog (initUiJvmState [(0, .heapRef addr)] hp jh) =
        some (c, st') ∧
      st'.jvmHeap = jh ∧ st'.heap = hp :=
  getCurrent_equiv resolveProg depth sf fuel hf hi hp

theorem component2_equiv (resolveProg : String → Option (List JvmInstr))
    (depth sf fuel : Nat) (hf : 5 ≤ fuel)
    {jh : Jvm.JvmHeap UiExt} {addr : Nat} {c p : JvmVal} {pr : Float32} {m : JvmVal}
    (hi : HasInProgressFields jh addr c p pr m) (hp : UiHeap) :
    ∃ st',
      Jvm.runJvmRes (mkUiCommonHooks resolveProg depth sf) fuel
          TargetState_InProgress_component2_prog (initUiJvmState [(0, .heapRef addr)] hp jh) =
        some (p, st') ∧
      st'.jvmHeap = jh ∧ st'.heap = hp :=
  getProvisional_equiv resolveProg depth sf fuel hf hi hp

theorem component3_equiv (resolveProg : String → Option (List JvmInstr))
    (depth sf fuel : Nat) (hf : 5 ≤ fuel)
    {jh : Jvm.JvmHeap UiExt} {addr : Nat} {c p : JvmVal} {pr : Float32} {m : JvmVal}
    (hi : HasInProgressFields jh addr c p pr m) (hp : UiHeap) :
    ∃ st',
      Jvm.runJvmRes (mkUiCommonHooks resolveProg depth sf) fuel
          TargetState_InProgress_component3_prog (initUiJvmState [(0, .heapRef addr)] hp jh) =
        some (.f32 pr, st') ∧
      st'.jvmHeap = jh ∧ st'.heap = hp :=
  getProgress_equiv resolveProg depth sf fuel hf hi hp

theorem component4_equiv (resolveProg : String → Option (List JvmInstr))
    (depth sf fuel : Nat) (hf : 5 ≤ fuel)
    {jh : Jvm.JvmHeap UiExt} {addr : Nat} {c p : JvmVal} {pr : Float32} {m : JvmVal}
    (hi : HasInProgressFields jh addr c p pr m) (hp : UiHeap) :
    ∃ st',
      Jvm.runJvmRes (mkUiCommonHooks resolveProg depth sf) fuel
          TargetState_InProgress_component4_prog (initUiJvmState [(0, .heapRef addr)] hp jh) =
        some (m, st') ∧
      st'.jvmHeap = jh ∧ st'.heap = hp :=
  getMetadata_equiv resolveProg depth sf fuel hf hi hp

/-! ### `TargetState$InProgress` Constructor, `copy`, `toString`, `hashCode`, `equals` -/

private theorem hasInProgressFields_of_set4 {jh : Jvm.JvmHeap UiExt} {addr : Nat}
    {cls : String} {fields : List (String × JvmVal)}
    (hget : jh.get? addr = some (.instance cls fields))
    (hcls : cls = "com/alexvanyo/composelife/ui/util/TargetState$InProgress" ∨
      cls = "TargetState$InProgress")
    (c p : JvmVal) (pr : Float32) (m : JvmVal) :
    let jh1 := jh.set addr (.instance cls (("current", c) :: fields.filter (fun (f, _) => f != "current")))
    let jh2 := jh1.set addr (.instance cls (("provisional", p) ::
      (("current", c) :: fields.filter (fun (f, _) => f != "current")).filter (fun (f, _) => f != "provisional")))
    let jh3 := jh2.set addr (.instance cls (("progress", .f32 pr) ::
      (("provisional", p) :: (("current", c) ::
        fields.filter (fun (f, _) => f != "current")).filter (fun (f, _) => f != "provisional")).filter
        (fun (f, _) => f != "progress")))
    let jh4 := jh3.set addr (.instance cls (("metadata", m) ::
      (("progress", .f32 pr) :: (("provisional", p) :: (("current", c) ::
        fields.filter (fun (f, _) => f != "current")).filter (fun (f, _) => f != "provisional")).filter
        (fun (f, _) => f != "progress")).filter (fun (f, _) => f != "metadata")))
    HasInProgressFields jh4 addr c p pr m := by
  intro jh1 jh2 jh3 jh4
  have hg1 : jh1.get? addr = some (.instance cls
      (("current", c) :: fields.filter (fun (f, _) => f != "current"))) :=
    Jvm.jvmHeap_get?_set_self hget
  have hg2 : jh2.get? addr = some (.instance cls
      (("provisional", p) :: (("current", c) ::
        fields.filter (fun (f, _) => f != "current")).filter (fun (f, _) => f != "provisional"))) :=
    Jvm.jvmHeap_get?_set_self hg1
  have hg3 : jh3.get? addr = some (.instance cls
      (("progress", .f32 pr) :: (("provisional", p) :: (("current", c) ::
        fields.filter (fun (f, _) => f != "current")).filter (fun (f, _) => f != "provisional")).filter
        (fun (f, _) => f != "progress"))) :=
    Jvm.jvmHeap_get?_set_self hg2
  have hg4 : jh4.get? addr = some (.instance cls
      (("metadata", m) :: (("progress", .f32 pr) :: (("provisional", p) :: (("current", c) ::
        fields.filter (fun (f, _) => f != "current")).filter (fun (f, _) => f != "provisional")).filter
        (fun (f, _) => f != "progress")).filter (fun (f, _) => f != "metadata"))) :=
    Jvm.jvmHeap_get?_set_self hg3
  refine ⟨cls, _, hg4, hcls, ?_, ?_, ?_, ?_⟩ <;> rfl

private theorem stepInstr_putfield_instance (hooks : Jvm.JvmHooks UiExt UiHeap)
    (pc : Nat) (cls fld desc : String) (v : JvmVal) (addr : Nat)
    (stk : List JvmVal) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap UiExt) (hp : UiHeap)
    (objCls : String) (fields : List (String × JvmVal))
    (hget : jh.get? addr = some (.instance objCls fields))
    (hsub : (objCls == cls || hooks.isSubtypeOf objCls cls) = true) :
    Jvm.stepInstr hooks (.putfield cls fld desc)
        ⟨pc, v :: .heapRef addr :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, stk, locs,
        jh.set addr (.instance objCls ((fld, v) :: fields.filter (fun (f, _) => f != fld))), hp⟩) := by
  unfold Jvm.stepInstr
  simp [Jvm.HeapObj.setField, hget, hsub]

private theorem stepPutField_instance (resolveProg : String → Option (List JvmInstr))
    (d sf pc : Nat) (cls fld desc : String) (v : JvmVal) (addr : Nat)
    (stk : List JvmVal) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap UiExt) (hp : UiHeap)
    (objCls : String) (fields : List (String × JvmVal))
    (hget : jh.get? addr = some (.instance objCls fields))
    (hsub : (objCls == cls || isUiCommonSubtypeOf objCls cls) = true) :
    Jvm.stepInstr (mkUiCommonHooks resolveProg d sf) (.putfield cls fld desc)
        ⟨pc, v :: .heapRef addr :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, stk, locs,
        jh.set addr (.instance objCls ((fld, v) :: fields.filter (fun (f, _) => f != fld))), hp⟩) :=
  stepInstr_putfield_instance (mkUiCommonHooks resolveProg d sf) pc cls fld desc v addr stk locs jh hp
    objCls fields hget (by rw [mkUiCommonHooks_isSubtypeOf]; exact hsub)

private theorem stepInstr_invokespecial_objInit_heapRef (resolveProg : String → Option (List JvmInstr))
    (d sf pc : Nat) (addr : Nat) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    Jvm.stepInstr (mkUiCommonHooks resolveProg d sf) (.invokespecial "java/lang/Object" "<init>" "()V")
        ⟨pc, .heapRef addr :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, stk, locs, jh, hp⟩) :=
  mkUiCommonHooks_stepInvokeSpecial_objInit_heapRef resolveProg d sf pc addr stk locs jh hp

private theorem parseTags_obj_obj :
    Jvm.parseMethodParamTags "(Ljava/lang/Object;)Ljava/lang/Object;" = ['L'] := by
  decide

private theorem assignParamLocals_L1 (v : JvmVal) :
    assignParamLocalsAux 0 ['L'] [v] = [(0, v)] := by
  simp [assignParamLocalsAux]

private theorem mkUiCommonHooks_stepInvokeVirtual_inProgress_getCurrent
    (r : String → Option (List JvmInstr)) (d sf pc addr : Nat)
    (stk : List JvmVal) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    Jvm.stepInvokeVirtualGeneric (mkUiCommonHooks r (d + 1) sf)
        ⟨pc, .heapRef addr :: stk, locs, jh, hp⟩
        "TargetState$InProgress" "getCurrent" "()Ljava/lang/Object;" =
      match r "TargetState$InProgress.getCurrent" with
      | some prog =>
        match Jvm.runJvmRes (mkUiCommonHooks r d sf) sf prog
            (initUiJvmState [(0, .heapRef addr)] hp jh) with
        | some (res, endSt) => .inl (some ⟨pc + 1, res :: stk, locs, endSt.jvmHeap, endSt.heap⟩)
        | none => .inr none
      | none => .inr none := by
  rw [show Jvm.stepInvokeVirtualGeneric (mkUiCommonHooks r (d + 1) sf)
        ⟨pc, .heapRef addr :: stk, locs, jh, hp⟩
        "TargetState$InProgress" "getCurrent" "()Ljava/lang/Object;" =
      match (match r "TargetState$InProgress.getCurrent" with
        | some prog =>
          match Jvm.runJvmRes (mkUiCommonHooks r d sf) sf prog
              { pc := 0, stack := [],
                locals := (assignParamLocalsAux 0
                  (Jvm.parseMethodParamTags "(Ljava/lang/Object;)Ljava/lang/Object;")
                  [.heapRef addr]).foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal)),
                jvmHeap := jh, heap := hp } with
          | some (res, endSt) => some (res, (⟨pc, .heapRef addr :: stk, locs, endSt.jvmHeap, endSt.heap⟩ : JvmState))
          | none => none
        | none => none) with
      | some (res, st') => Sum.inl (some { st' with pc := pc + 1, stack := res :: stk })
      | none => Sum.inr none from rfl]
  rw [parseTags_obj_obj, assignParamLocals_L1]
  cases r "TargetState$InProgress.getCurrent" with
  | none => rfl
  | some prog =>
    dsimp only [initUiJvmState, Jvm.initJvmState] at *
    cases Jvm.runJvmRes (mkUiCommonHooks r d sf) sf prog
        { pc := 0, stack := [],
          locals := List.foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal)) [(0, .heapRef addr)],
          jvmHeap := jh, heap := hp } <;> rfl

private theorem stepInvokeVirtual_inProgress_getCurrent (resolveProg : String → Option (List JvmInstr))
    (d sf pc : Nat) (hext : ExtendsUiProgs resolveProg) (hsf : 5 ≤ sf)
    {jh : Jvm.JvmHeap UiExt} {addr : Nat} {c p : JvmVal} {pr : Float32} {m : JvmVal}
    (hi : HasInProgressFields jh addr c p pr m)
    (stk : List JvmVal) (locs : Nat → JvmVal) (hp : UiHeap) :
    Jvm.stepInvokeVirtualGeneric (mkUiCommonHooks resolveProg (d + 1) sf)
        ⟨pc, .heapRef addr :: stk, locs, jh, hp⟩
        "TargetState$InProgress" "getCurrent" "()Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, c :: stk, locs, jh, hp⟩) := by
  have hprog := hext "TargetState$InProgress.getCurrent" TargetState_InProgress_getCurrent_prog rfl
  rcases getCurrent_equiv resolveProg d sf sf hsf hi hp with ⟨stCur, hcurRun, hcurJh, hcurHp⟩
  rw [mkUiCommonHooks_stepInvokeVirtual_inProgress_getCurrent, hprog]
  dsimp only
  rw [hcurRun]
  change Sum.inl (some ({ pc := pc + 1, stack := c :: stk, locals := locs, jvmHeap := stCur.jvmHeap, heap := stCur.heap } : JvmState)) = _
  rw [hcurJh, hcurHp]

private theorem stepAreEqual (resolveProg : String → Option (List JvmInstr))
    (d sf pc : Nat) (a b : JvmVal) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap)
    (ha : a.equalsModeled jh = true) (hb : b.equalsModeled jh = true) :
    Jvm.stepInvokeStaticGeneric (mkUiCommonHooks resolveProg d sf)
        ⟨pc, b :: a :: stk, locs, jh, hp⟩
        "kotlin/jvm/internal/Intrinsics" "areEqual" "(Ljava/lang/Object;Ljava/lang/Object;)Z" =
      .inl (some ⟨pc + 1, .bool (Jvm.JvmVal.beqVal beqUiExt a b) :: stk, locs, jh, hp⟩) := by
  simp [Jvm.stepInvokeStaticGeneric, mkUiCommonHooks_beqExt, ha, hb]

private theorem runJvmRes_goto {Ext Heap : Type} (hooks : Jvm.JvmHooks Ext Heap)
    (fuel : Nat) (prog : List JvmInstr) (st : Jvm.JvmState Ext Heap) (target : Nat)
    (hget : prog[st.pc]? = some (.goto target)) :
    Jvm.runJvmRes hooks (fuel + 1) prog st = Jvm.runJvmRes hooks fuel prog { st with pc := target } := by
  cases st; simp [Jvm.runJvmRes, hget]; rfl

private theorem runJvmRes_ifne_i32 (hooks : Jvm.JvmHooks UiExt UiHeap)
    (fuel : Nat) (prog : List JvmInstr) (pc target : Nat) (n : UInt32) (stk : List JvmVal)
    (locs : Nat → JvmVal) (jh : Jvm.JvmHeap UiExt) (hp : UiHeap)
    (hget : prog[pc]? = some (.ifne target))
    (hisZ : hooks.isZero? = fun v => v.asI32?.map (· == 0)) :
    Jvm.runJvmRes hooks (fuel + 1) prog ⟨pc, .i32 n :: stk, locs, jh, hp⟩ =
      if n != 0 then Jvm.runJvmRes hooks fuel prog ⟨target, stk, locs, jh, hp⟩
      else Jvm.runJvmRes hooks fuel prog ⟨pc + 1, stk, locs, jh, hp⟩ := by
  by_cases hn : n = 0
  · subst hn; simp [Jvm.runJvmRes, hget, hisZ, Jvm.JvmVal.asI32?]
  · have hn0 : (n == 0) = false := beq_false_of_ne hn
    simp [Jvm.runJvmRes, hget, hisZ, Jvm.JvmVal.asI32?, hn0, hn]

private theorem runJvmRes_ifne_bool (hooks : Jvm.JvmHooks UiExt UiHeap)
    (fuel : Nat) (prog : List JvmInstr) (pc target : Nat) (b : Bool) (stk : List JvmVal)
    (locs : Nat → JvmVal) (jh : Jvm.JvmHeap UiExt) (hp : UiHeap)
    (hget : prog[pc]? = some (.ifne target))
    (hisZ : hooks.isZero? = fun v => v.asI32?.map (· == 0)) :
    Jvm.runJvmRes hooks (fuel + 1) prog ⟨pc, .bool b :: stk, locs, jh, hp⟩ =
      if b then Jvm.runJvmRes hooks fuel prog ⟨target, stk, locs, jh, hp⟩
      else Jvm.runJvmRes hooks fuel prog ⟨pc + 1, stk, locs, jh, hp⟩ := by
  cases b <;> simp [Jvm.runJvmRes, hget, hisZ, Jvm.JvmVal.asI32?]

private theorem stepInstr_invokeVirtual_inProgress_getCurrent (resolveProg : String → Option (List JvmInstr))
    (d sf pc : Nat) (hext : ExtendsUiProgs resolveProg) (hsf : 5 ≤ sf)
    {jh : Jvm.JvmHeap UiExt} {addr : Nat} {c p : JvmVal} {pr : Float32} {m : JvmVal}
    (hi : HasInProgressFields jh addr c p pr m)
    (stk : List JvmVal) (locs : Nat → JvmVal) (hp : UiHeap) :
    Jvm.stepInstr (mkUiCommonHooks resolveProg (d + 1) sf)
        (.invokevirtual "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "getCurrent" "()Ljava/lang/Object;")
        ⟨pc, .heapRef addr :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, c :: stk, locs, jh, hp⟩) :=
  stepInvokeVirtual_inProgress_getCurrent resolveProg d sf pc hext hsf hi stk locs hp

private theorem stepInstr_areEqual (resolveProg : String → Option (List JvmInstr))
    (d sf pc : Nat) (a b : JvmVal) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap)
    (ha : a.equalsModeled jh = true := by rfl) (hb : b.equalsModeled jh = true := by rfl) :
    Jvm.stepInstr (mkUiCommonHooks resolveProg d sf)
        (.invokestatic "kotlin/jvm/internal/Intrinsics" "areEqual" "(Ljava/lang/Object;Ljava/lang/Object;)Z")
        ⟨pc, b :: a :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .bool (Jvm.JvmVal.beqVal beqUiExt a b) :: stk, locs, jh, hp⟩) :=
  stepAreEqual resolveProg d sf pc a b stk locs jh hp ha hb

private theorem initUiJvmState_5_locals (a b c d e : JvmVal) :
    ([(0, a), (1, b), (2, c), (3, d), (4, e)]).foldl
        (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal)) =
      setLocal (setLocal (setLocal (setLocal (setLocal (fun (_ : Nat) => (.i32 0 : JvmVal)) 0 a) 1 b) 2 c) 3 d) 4 e := rfl

private theorem setLocal_5_eval (a b c d e : JvmVal) :
    (setLocal (setLocal (setLocal (setLocal (setLocal (fun (_ : Nat) => (.i32 0 : JvmVal)) 0 a) 1 b) 2 c) 3 d) 4 e 0 = a) ∧
    (setLocal (setLocal (setLocal (setLocal (setLocal (fun (_ : Nat) => (.i32 0 : JvmVal)) 0 a) 1 b) 2 c) 3 d) 4 e 1 = b) ∧
    (setLocal (setLocal (setLocal (setLocal (setLocal (fun (_ : Nat) => (.i32 0 : JvmVal)) 0 a) 1 b) 2 c) 3 d) 4 e 2 = c) ∧
    (setLocal (setLocal (setLocal (setLocal (setLocal (fun (_ : Nat) => (.i32 0 : JvmVal)) 0 a) 1 b) 2 c) 3 d) 4 e 3 = d) ∧
    (setLocal (setLocal (setLocal (setLocal (setLocal (fun (_ : Nat) => (.i32 0 : JvmVal)) 0 a) 1 b) 2 c) 3 d) 4 e 4 = e) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem inProgress_ctor_prefix (resolveProg : String → Option (List JvmInstr))
    (d sf k : Nat) (hext : ExtendsUiProgs resolveProg) (hsf : 5 ≤ sf)
    (jh : Jvm.JvmHeap UiExt) (addr : Nat) (cls : String) (fields : List (String × JvmVal))
    (hget : jh.get? addr = some (.instance cls fields))
    (hcls : cls = "com/alexvanyo/composelife/ui/util/TargetState$InProgress" ∨
      cls = "TargetState$InProgress")
    (c p : JvmVal) (pr : Float32) (m : JvmVal) (hp : UiHeap)
    (hcm : c.equalsModeled jh = true) (hpm : p.equalsModeled jh = true) :
    ∃ jhFinal locsFinal,
      Jvm.runJvmRes (mkUiCommonHooks resolveProg (d + 1) sf) (k + 45)
          TargetState_InProgress_init_prog
          (initUiJvmState [(0, .heapRef addr), (1, c), (2, p), (3, .f32 pr), (4, m)] hp jh) =
        Jvm.runJvmRes (mkUiCommonHooks resolveProg (d + 1) sf) (k + 25)
          TargetState_InProgress_init_prog
          ⟨20, [.bool (Jvm.JvmVal.beqVal beqUiExt c p)], locsFinal, jhFinal, hp⟩ ∧
      HasInProgressFields jhFinal addr c p pr m := by
  have hsub : (cls == "com/alexvanyo/composelife/ui/util/TargetState$InProgress" || isUiCommonSubtypeOf cls "com/alexvanyo/composelife/ui/util/TargetState$InProgress") = true := by
    rcases hcls with rfl | rfl <;> simp [isUiCommonSubtypeOf, normalizeUiCommonClass]
  have hi4 := hasInProgressFields_of_set4 hget hcls c p pr m
  let jh1 := jh.set addr (.instance cls (("current", c) :: fields.filter (fun (f, _) => f != "current")))
  let jh2 := jh1.set addr (.instance cls (("provisional", p) ::
    (("current", c) :: fields.filter (fun (f, _) => f != "current")).filter (fun (f, _) => f != "provisional")))
  let jh3 := jh2.set addr (.instance cls (("progress", .f32 pr) ::
    (("provisional", p) :: (("current", c) ::
      fields.filter (fun (f, _) => f != "current")).filter (fun (f, _) => f != "provisional")).filter
      (fun (f, _) => f != "progress")))
  let jh4 := jh3.set addr (.instance cls (("metadata", m) ::
    (("progress", .f32 pr) :: (("provisional", p) :: (("current", c) ::
      fields.filter (fun (f, _) => f != "current")).filter (fun (f, _) => f != "provisional")).filter
      (fun (f, _) => f != "progress")).filter (fun (f, _) => f != "metadata")))
  have hg1 : jh1.get? addr = some (.instance cls
      (("current", c) :: fields.filter (fun (f, _) => f != "current"))) :=
    Jvm.jvmHeap_get?_set_self hget
  have hg2 : jh2.get? addr = some (.instance cls
      (("provisional", p) :: (("current", c) ::
        fields.filter (fun (f, _) => f != "current")).filter (fun (f, _) => f != "provisional"))) :=
    Jvm.jvmHeap_get?_set_self hg1
  have hg3 : jh3.get? addr = some (.instance cls
      (("progress", .f32 pr) :: (("provisional", p) :: (("current", c) ::
        fields.filter (fun (f, _) => f != "current")).filter (fun (f, _) => f != "provisional")).filter
        (fun (f, _) => f != "progress"))) :=
    Jvm.jvmHeap_get?_set_self hg2
  have hm4 : ∀ v : JvmVal, v.equalsModeled jh4 = v.equalsModeled jh := fun v =>
    (Jvm.jvmVal_equalsModeled_set_instance hg3 v).trans ((Jvm.jvmVal_equalsModeled_set_instance hg2 v).trans
      ((Jvm.jvmVal_equalsModeled_set_instance hg1 v).trans (Jvm.jvmVal_equalsModeled_set_instance hget v)))
  refine ⟨jh4, (initUiJvmState [(0, .heapRef addr), (1, c), (2, p), (3, .f32 pr), (4, m)] hp jh).locals,
    ?_, hi4⟩
  dsimp only [initUiJvmState, Jvm.initJvmState]
  rw [initUiJvmState_5_locals]
  have hloc := setLocal_5_eval (.heapRef addr) c p (.f32 pr) m
  -- 0: aload 0
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]
  rw [stepInstr_aload, hloc.1]; dsimp only
  -- 1: invokespecial Object.<init>
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokespecial "java/lang/Object" "<init>" "()V") (by rfl) rfl]
  rw [stepInstr_invokespecial_objInit_heapRef resolveProg (d + 1) sf 1 addr [] _ jh hp]
  dsimp only
  -- 2..4: aload 0; aload 1; putfield current
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, hloc.1]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 1) (by rfl) rfl]; rw [stepInstr_aload, hloc.2.1]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.putfield "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "current" "Ljava/lang/Object;") (by rfl) rfl]
  rw [stepPutField_instance resolveProg (d + 1) sf 4 _ _ _ c addr _ _ jh hp cls fields hget hsub]; dsimp only
  -- 5..7: aload 0; aload 2; putfield provisional
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, hloc.1]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 2) (by rfl) rfl]; rw [stepInstr_aload, hloc.2.2.1]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.putfield "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "provisional" "Ljava/lang/Object;") (by rfl) rfl]
  rw [stepPutField_instance resolveProg (d + 1) sf 7 _ _ _ p addr _ _ jh1 hp cls _ hg1 hsub]; dsimp only
  -- 8..10: aload 0; fload 3; putfield progress
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, hloc.1]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.fload 3) (by rfl) rfl]
  rw [stepInstr_fload_f32 _ _ _ _ _ _ _ _ hloc.2.2.2.1]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.putfield "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "progress" "F") (by rfl) rfl]
  rw [stepPutField_instance resolveProg (d + 1) sf 10 _ _ _ (.f32 pr) addr _ _ jh2 hp cls _ hg2 hsub]; dsimp only
  -- 11..13: aload 0; aload 4; putfield metadata
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, hloc.1]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 4) (by rfl) rfl]; rw [stepInstr_aload, hloc.2.2.2.2]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.putfield "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "metadata" "Ljava/lang/Object;") (by rfl) rfl]
  rw [stepPutField_instance resolveProg (d + 1) sf 13 _ _ _ m addr _ _ jh3 hp cls _ hg3 hsub]; dsimp only
  -- 14: nop
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ .nop (by rfl) rfl]; rw [stepInstr_nop]; dsimp only
  -- 15..16: aload 0; invokevirtual getCurrent
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, hloc.1]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokevirtual "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "getCurrent" "()Ljava/lang/Object;") (by rfl) rfl]
  rw [stepInstr_invokeVirtual_inProgress_getCurrent resolveProg d sf 16 hext hsf hi4]; dsimp only
  -- 17..18: aload 0; getfield provisional
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, hloc.1]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.getfield "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "provisional" "Ljava/lang/Object;") (by rfl) rfl]
  rw [(stepGetField_inProgress resolveProg (d + 1) sf 18 hi4).2.1]; dsimp only
  -- 19: invokestatic Intrinsics.areEqual
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokestatic "kotlin/jvm/internal/Intrinsics" "areEqual" "(Ljava/lang/Object;Ljava/lang/Object;)Z") (by rfl) rfl]
  rw [stepInstr_areEqual (ha := (hm4 c).trans hcm) (hb := (hm4 p).trans hpm)]

theorem inProgress_ctor_valid_equiv (resolveProg : String → Option (List JvmInstr))
    (d sf fuel : Nat) (hext : ExtendsUiProgs resolveProg) (hsf : 5 ≤ sf) (hf : 45 ≤ fuel)
    (jh : Jvm.JvmHeap UiExt) (addr : Nat) (cls : String) (fields : List (String × JvmVal))
    (hget : jh.get? addr = some (.instance cls fields))
    (hcls : cls = "com/alexvanyo/composelife/ui/util/TargetState$InProgress" ∨
      cls = "TargetState$InProgress")
    (c p : JvmVal) (pr : Float32) (m : JvmVal) (hp : UiHeap)
    (hne : Jvm.JvmVal.beqVal beqUiExt c p = false)
    (hcm : c.equalsModeled jh = true) (hpm : p.equalsModeled jh = true) :
    ∃ st',
      Jvm.runJvmRes (mkUiCommonHooks resolveProg (d + 1) sf) fuel
          TargetState_InProgress_init_prog
          (initUiJvmState [(0, .heapRef addr), (1, c), (2, p), (3, .f32 pr), (4, m)] hp jh) =
        some (.unit, st') ∧
      HasInProgressFields st'.jvmHeap addr c p pr m ∧
      st'.heap = hp := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  rcases inProgress_ctor_prefix resolveProg d sf k hext hsf jh addr cls fields
    hget hcls c p pr m hp hcm hpm with ⟨jhFinal, locsFinal, hpre, hiFinal⟩
  refine ⟨⟨36, [], locsFinal, jhFinal, hp⟩, ?_, hiFinal, rfl⟩
  rw [hpre, hne]
  rw [runJvmRes_ifne_bool _ _ _ 20 23 false _ _ _ _ (by rfl) (mkUiCommonHooks_isZero? _ _ _)]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.iconst 1) (by rfl) rfl]; rw [stepInstr_iconst]; dsimp only
  rw [runJvmRes_goto _ _ _ _ 24 (by rfl)]; dsimp only
  rw [runJvmRes_ifne_i32 _ _ _ 24 35 1 _ _ _ _ (by rfl) (mkUiCommonHooks_isZero? _ _ _)]
  simp only [show ((1 : UInt32) != 0) = true from rfl, ↓reduceIte]
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ .nop (by rfl) rfl]; rw [stepInstr_nop]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ .vreturn (by rfl) rfl]
  rw [stepInstr_vreturn]

private theorem stepInstr_athrow (hooks : Jvm.JvmHooks UiExt UiHeap)
    (pc : Nat) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    Jvm.stepInstr hooks .athrow ⟨pc, stk, locs, jh, hp⟩ = .inr none := rfl

theorem inProgress_ctor_trap_equiv (resolveProg : String → Option (List JvmInstr))
    (d sf fuel : Nat) (hext : ExtendsUiProgs resolveProg) (hsf : 5 ≤ sf) (hf : 45 ≤ fuel)
    (jh : Jvm.JvmHeap UiExt) (addr : Nat) (cls : String) (fields : List (String × JvmVal))
    (hget : jh.get? addr = some (.instance cls fields))
    (hcls : cls = "com/alexvanyo/composelife/ui/util/TargetState$InProgress" ∨
      cls = "TargetState$InProgress")
    (c p : JvmVal) (pr : Float32) (m : JvmVal) (hp : UiHeap)
    (heq : Jvm.JvmVal.beqVal beqUiExt c p = true)
    (hcm : c.equalsModeled jh = true) (hpm : p.equalsModeled jh = true) :
    Jvm.runJvmRes (mkUiCommonHooks resolveProg (d + 1) sf) fuel
        TargetState_InProgress_init_prog
        (initUiJvmState [(0, .heapRef addr), (1, c), (2, p), (3, .f32 pr), (4, m)] hp jh) =
      none := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  rcases inProgress_ctor_prefix resolveProg d sf k hext hsf jh addr cls fields
    hget hcls c p pr m hp hcm hpm with ⟨jhFinal, locsFinal, hpre, _⟩
  rw [hpre, heq]
  rw [runJvmRes_ifne_bool _ _ _ 20 23 true _ _ _ _ (by rfl) (mkUiCommonHooks_isZero? _ _ _)]
  simp only [↓reduceIte]
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.iconst 0) (by rfl) rfl]; rw [stepInstr_iconst]; dsimp only
  rw [runJvmRes_ifne_i32 _ _ _ 24 35 0 _ _ _ _ (by rfl) (mkUiCommonHooks_isZero? _ _ _)]
  simp only [show ((0 : UInt32) != 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.iconst 0) (by rfl) rfl]; rw [stepInstr_iconst]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.istore 5) (by rfl) rfl]; rw [stepInstr_istore_i32]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.ldcStr "current is the same as provisional, should be using TargetState.Single instead") (by rfl) rfl]
  rw [stepInstr_ldcStr]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.astore 5) (by rfl) rfl]; rw [stepInstr_astore]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.newClass "java/lang/IllegalArgumentException") (by rfl) rfl]
  rw [stepInstr_newClass_other _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide)]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ .dup (by rfl) rfl]
  rw [stepInstr_dup]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 5) (by rfl) rfl]
  rw [stepInstr_aload]; simp only [Jvm.setLocal, ↓reduceIte]
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokevirtual "java/lang/Object" "toString" "()Ljava/lang/String;") (by rfl) rfl]
  rw [stepInstr_invokeVirtual_obj_toString_str]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokespecial "java/lang/IllegalArgumentException" "<init>" "(Ljava/lang/String;)V") (by rfl) rfl]
  rw [stepInstr_invokeSpecial_iae_init]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ .athrow (by rfl) rfl]
  rw [stepInstr_athrow]

/-! ### Additional Step Helpers & Branch Lemmas -/

private theorem stepInstr_iload (hooks : Jvm.JvmHooks UiExt UiHeap)
    (pc idx : Nat) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    Jvm.stepInstr hooks (.iload idx) ⟨pc, stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, locs idx :: stk, locs, jh, hp⟩) := rfl

private theorem stepInstr_fload (hooks : Jvm.JvmHooks UiExt UiHeap)
    (pc idx : Nat) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    Jvm.stepInstr hooks (.fload idx) ⟨pc, stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, locs idx :: stk, locs, jh, hp⟩) := rfl

private theorem stepInstr_fstore (hooks : Jvm.JvmHooks UiExt UiHeap)
    (pc idx : Nat) (v : JvmVal) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    Jvm.stepInstr hooks (.fstore idx) ⟨pc, v :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, stk, setLocal locs idx v, jh, hp⟩) := rfl

private theorem stepInstr_fconst (hooks : Jvm.JvmHooks UiExt UiHeap)
    (pc : Nat) (bits : UInt32) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    Jvm.stepInstr hooks (.fconst bits) ⟨pc, stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .f32 (Float32.ofBits bits) :: stk, locs, jh, hp⟩) := rfl

private theorem stepInstr_pop (hooks : Jvm.JvmHooks UiExt UiHeap)
    (pc : Nat) (v : JvmVal) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    Jvm.stepInstr hooks .pop ⟨pc, v :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, stk, locs, jh, hp⟩) := rfl

private theorem stepInstr_swap (hooks : Jvm.JvmHooks UiExt UiHeap)
    (pc : Nat) (a b : JvmVal) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) (ha : a.isCat2 = false) (hb : b.isCat2 = false) :
    Jvm.stepInstr hooks .swap ⟨pc, a :: b :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, b :: a :: stk, locs, jh, hp⟩) := by
  unfold Jvm.stepInstr; simp [ha, hb]

private theorem stepInstr_ireturn (r : String → Option (List JvmInstr)) (d sf : Nat)
    (pc : Nat) (v : JvmVal) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    Jvm.stepInstr (mkUiCommonHooks r d sf) .ireturn ⟨pc, v :: stk, locs, jh, hp⟩ =
      .inr (some v) := by
  unfold Jvm.stepInstr; rw [mkUiCommonHooks_ireturnVal]; rfl

private theorem stepInstr_iand_i32 (hooks : Jvm.JvmHooks UiExt UiHeap)
    (pc : Nat) (a b : UInt32) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    Jvm.stepInstr hooks .iand ⟨pc, .i32 b :: .i32 a :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 (a &&& b) :: stk, locs, jh, hp⟩) := by
  unfold Jvm.stepInstr; simp [Jvm.JvmVal.asI32?]

private theorem stepInstr_iadd_i32 (hooks : Jvm.JvmHooks UiExt UiHeap)
    (pc : Nat) (a b : UInt32) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    Jvm.stepInstr hooks .iadd ⟨pc, .i32 b :: .i32 a :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 (a + b) :: stk, locs, jh, hp⟩) := by
  unfold Jvm.stepInstr; simp [Jvm.JvmVal.asI32?]

private theorem stepInstr_imul_i32 (hooks : Jvm.JvmHooks UiExt UiHeap)
    (pc : Nat) (a b : UInt32) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    Jvm.stepInstr hooks .imul ⟨pc, .i32 b :: .i32 a :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 (a * b) :: stk, locs, jh, hp⟩) := by
  unfold Jvm.stepInstr; simp [Jvm.JvmVal.asI32?]

private theorem stepInstr_fsub_f32 (hooks : Jvm.JvmHooks UiExt UiHeap)
    (pc : Nat) (a b : Float32) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    Jvm.stepInstr hooks .fsub ⟨pc, .f32 b :: .f32 a :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .f32 (a - b) :: stk, locs, jh, hp⟩) := by
  unfold Jvm.stepInstr; simp [Jvm.JvmVal.asF32?]

private theorem stepInstr_newClass_inProgress (r : String → Option (List JvmInstr)) (d sf : Nat)
    (pc : Nat) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    Jvm.stepInstr (mkUiCommonHooks r d sf)
        (.newClass "com/alexvanyo/composelife/ui/util/TargetState$InProgress")
        ⟨pc, stk, locs, jh, hp⟩ =
      let (addr, jh') := jh.alloc (.instance "com/alexvanyo/composelife/ui/util/TargetState$InProgress" [])
      .inl (some ⟨pc + 1, .heapRef addr :: stk, locs, jh', hp⟩) := by
  unfold Jvm.stepInstr
  exact mkUiCommonHooks_stepNewClass_inProgress r d sf ⟨pc, stk, locs, jh, hp⟩

private theorem stepInstr_newClass_single (r : String → Option (List JvmInstr)) (d sf : Nat)
    (pc : Nat) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    Jvm.stepInstr (mkUiCommonHooks r d sf)
        (.newClass "com/alexvanyo/composelife/ui/util/TargetState$Single")
        ⟨pc, stk, locs, jh, hp⟩ =
      let (addr, jh') := jh.alloc (.instance "com/alexvanyo/composelife/ui/util/TargetState$Single" [])
      .inl (some ⟨pc + 1, .heapRef addr :: stk, locs, jh', hp⟩) := by
  unfold Jvm.stepInstr
  exact mkUiCommonHooks_stepNewClass_single r d sf ⟨pc, stk, locs, jh, hp⟩

private theorem runJvmRes_ifeq_i32 (hooks : Jvm.JvmHooks UiExt UiHeap)
    (fuel : Nat) (prog : List JvmInstr) (pc target : Nat) (n : UInt32) (stk : List JvmVal)
    (locs : Nat → JvmVal) (jh : Jvm.JvmHeap UiExt) (hp : UiHeap)
    (hget : prog[pc]? = some (.ifeq target))
    (hisZ : hooks.isZero? = fun v => v.asI32?.map (· == 0)) :
    Jvm.runJvmRes hooks (fuel + 1) prog ⟨pc, .i32 n :: stk, locs, jh, hp⟩ =
      if n == 0 then Jvm.runJvmRes hooks fuel prog ⟨target, stk, locs, jh, hp⟩
      else Jvm.runJvmRes hooks fuel prog ⟨pc + 1, stk, locs, jh, hp⟩ := by
  by_cases hn : n = 0
  · subst hn; simp [Jvm.runJvmRes, hget, hisZ, Jvm.JvmVal.asI32?]
  · have hn0 : (n == 0) = false := beq_false_of_ne hn
    simp [Jvm.runJvmRes, hget, hisZ, Jvm.JvmVal.asI32?, hn0]

private theorem runJvmRes_ifeq_bool (hooks : Jvm.JvmHooks UiExt UiHeap)
    (fuel : Nat) (prog : List JvmInstr) (pc target : Nat) (b : Bool) (stk : List JvmVal)
    (locs : Nat → JvmVal) (jh : Jvm.JvmHeap UiExt) (hp : UiHeap)
    (hget : prog[pc]? = some (.ifeq target))
    (hisZ : hooks.isZero? = fun v => v.asI32?.map (· == 0)) :
    Jvm.runJvmRes hooks (fuel + 1) prog ⟨pc, .bool b :: stk, locs, jh, hp⟩ =
      if b then Jvm.runJvmRes hooks fuel prog ⟨pc + 1, stk, locs, jh, hp⟩
      else Jvm.runJvmRes hooks fuel prog ⟨target, stk, locs, jh, hp⟩ := by
  cases b <;> simp [Jvm.runJvmRes, hget, hisZ, Jvm.JvmVal.asI32?]

private theorem runJvmRes_ifnonnull (hooks : Jvm.JvmHooks UiExt UiHeap)
    (fuel : Nat) (prog : List JvmInstr) (pc target : Nat) (v : JvmVal) (stk : List JvmVal)
    (locs : Nat → JvmVal) (jh : Jvm.JvmHeap UiExt) (hp : UiHeap)
    (hget : prog[pc]? = some (.ifnonnull target)) :
    Jvm.runJvmRes hooks (fuel + 1) prog ⟨pc, v :: stk, locs, jh, hp⟩ =
      if !v.isNull then Jvm.runJvmRes hooks fuel prog ⟨target, stk, locs, jh, hp⟩
      else Jvm.runJvmRes hooks fuel prog ⟨pc + 1, stk, locs, jh, hp⟩ := by
  cases hb : v.isNull <;> simp [Jvm.runJvmRes, hget, hb]

private theorem runJvmRes_if_acmpne_heapRef (hooks : Jvm.JvmHooks UiExt UiHeap)
    (fuel : Nat) (prog : List JvmInstr) (pc target : Nat) (a b : Nat) (stk : List JvmVal)
    (locs : Nat → JvmVal) (jh : Jvm.JvmHeap UiExt) (hp : UiHeap)
    (hget : prog[pc]? = some (.if_acmpne target)) :
    Jvm.runJvmRes hooks (fuel + 1) prog ⟨pc, .heapRef b :: .heapRef a :: stk, locs, jh, hp⟩ =
      if a == b then Jvm.runJvmRes hooks fuel prog ⟨pc + 1, stk, locs, jh, hp⟩
      else Jvm.runJvmRes hooks fuel prog ⟨target, stk, locs, jh, hp⟩ := by
  by_cases hab : a = b
  · subst hab; simp [Jvm.runJvmRes, hget, Jvm.JvmVal.refEq?]
  · simp [Jvm.runJvmRes, hget, Jvm.JvmVal.refEq?, beq_false_of_ne hab]

private theorem runJvmRes_if_acmpne_heapRef_null (hooks : Jvm.JvmHooks UiExt UiHeap)
    (fuel : Nat) (prog : List JvmInstr) (pc target : Nat) (a : Nat) (stk : List JvmVal)
    (locs : Nat → JvmVal) (jh : Jvm.JvmHeap UiExt) (hp : UiHeap)
    (hget : prog[pc]? = some (.if_acmpne target)) :
    Jvm.runJvmRes hooks (fuel + 1) prog ⟨pc, .null :: .heapRef a :: stk, locs, jh, hp⟩ =
      Jvm.runJvmRes hooks fuel prog ⟨target, stk, locs, jh, hp⟩ := by
  simp [Jvm.runJvmRes, hget, Jvm.JvmVal.refEq?, Jvm.JvmVal.isRef]

private theorem parseTags_inProgress_init :
    Jvm.parseMethodParamTags "(Ljava/lang/Object;Ljava/lang/Object;Ljava/lang/Object;FLjava/lang/Object;)V" =
      ['L', 'L', 'L', 'F', 'L'] := by
  decide

private theorem assignParamLocals_5 (a b c d e : JvmVal) :
    assignParamLocalsAux 0 ['L', 'L', 'L', 'F', 'L'] [a, b, c, d, e] =
      [(0, a), (1, b), (2, c), (3, d), (4, e)] := rfl

private theorem mkUiCommonHooks_stepInvokeSpecial_inProgress_init
    (r : String → Option (List JvmInstr)) (d sf pc addr : Nat)
    (c p : JvmVal) (pr : Float32) (m : JvmVal)
    (stk : List JvmVal) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    Jvm.stepInstr (mkUiCommonHooks r (d + 1) sf)
        (.invokespecial "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "<init>" "(Ljava/lang/Object;Ljava/lang/Object;FLjava/lang/Object;)V")
        ⟨pc, m :: .f32 pr :: p :: c :: .heapRef addr :: stk, locs, jh, hp⟩ =
      match r "TargetState$InProgress.<init>" with
      | some prog =>
        match Jvm.runJvmRes (mkUiCommonHooks r d sf) sf prog
            (initUiJvmState [(0, .heapRef addr), (1, c), (2, p), (3, .f32 pr), (4, m)] hp jh) with
        | some (_, endSt) => .inl (some ⟨pc + 1, stk, locs, endSt.jvmHeap, endSt.heap⟩)
        | none => .inr none
      | none => .inr none := by
  rw [show Jvm.stepInstr (mkUiCommonHooks r (d + 1) sf)
        (.invokespecial "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "<init>" "(Ljava/lang/Object;Ljava/lang/Object;FLjava/lang/Object;)V")
        ⟨pc, m :: .f32 pr :: p :: c :: .heapRef addr :: stk, locs, jh, hp⟩ =
      match (match r "TargetState$InProgress.<init>" with
        | some prog =>
          match Jvm.runJvmRes (mkUiCommonHooks r d sf) sf prog
              { pc := 0, stack := [],
                locals := (assignParamLocalsAux 0
                  (Jvm.parseMethodParamTags "(Ljava/lang/Object;Ljava/lang/Object;Ljava/lang/Object;FLjava/lang/Object;)V")
                  [.heapRef addr, c, p, .f32 pr, m]).foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal)),
                jvmHeap := jh, heap := hp } with
          | some (res, endSt) =>
            some (res, (⟨pc, m :: .f32 pr :: p :: c :: .heapRef addr :: stk, locs, endSt.jvmHeap, endSt.heap⟩ : JvmState))
          | none => none
        | none => none) with
      | some (_, st') => Sum.inl (some { st' with pc := pc + 1, stack := stk })
      | none => Sum.inr none from rfl]
  rw [parseTags_inProgress_init, assignParamLocals_5]
  cases r "TargetState$InProgress.<init>" with
  | none => rfl
  | some prog =>
    dsimp only [initUiJvmState, Jvm.initJvmState] at *
    cases Jvm.runJvmRes (mkUiCommonHooks r d sf) sf prog
        { pc := 0, stack := [],
          locals := List.foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal))
            [(0, .heapRef addr), (1, c), (2, p), (3, .f32 pr), (4, m)],
          jvmHeap := jh, heap := hp } <;> rfl

theorem copy_valid_equiv (resolveProg : String → Option (List JvmInstr))
    (d sf fuel : Nat) (hext : ExtendsUiProgs resolveProg) (hsf : 45 ≤ sf) (hf : 10 ≤ fuel)
    (thisVal c p : JvmVal) (pr : Float32) (m : JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap)
    (hne : Jvm.JvmVal.beqVal beqUiExt c p = false)
    (hcm : c.equalsModeled jh = true) (hpm : p.equalsModeled jh = true) :
    ∃ st',
      Jvm.runJvmRes (mkUiCommonHooks resolveProg (d + 2) sf) fuel
          TargetState_InProgress_copy_prog (initUiJvmState [(0, thisVal), (1, c), (2, p), (3, .f32 pr), (4, m)] hp jh) =
        some (.heapRef jh.objects.size, st') ∧
      HasInProgressFields st'.jvmHeap jh.objects.size c p pr m ∧
      st'.heap = hp := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  have hprog := hext "TargetState$InProgress.<init>" TargetState_InProgress_init_prog rfl
  let obj0 : Jvm.HeapObj UiExt := .instance "com/alexvanyo/composelife/ui/util/TargetState$InProgress" []
  let newAddr := jh.objects.size
  let jh0 := (jh.alloc obj0).2
  have hget0 : jh0.get? newAddr = some (.instance "com/alexvanyo/composelife/ui/util/TargetState$InProgress" []) :=
    Jvm.jvmHeap_get?_alloc_self jh obj0
  rcases inProgress_ctor_valid_equiv resolveProg d sf sf hext (by omega) hsf jh0 newAddr
    "com/alexvanyo/composelife/ui/util/TargetState$InProgress" [] hget0 (Or.inl rfl) c p pr m hp hne
    (Jvm.jvmVal_equalsModeled_alloc _ c hcm) (Jvm.jvmVal_equalsModeled_alloc _ p hpm) with
    ⟨stCtor, hctorRun, hctorHi, hctorHp⟩
  refine ⟨⟨7, [.heapRef newAddr], (initUiJvmState [(0, thisVal), (1, c), (2, p), (3, .f32 pr), (4, m)] hp jh).locals,
      stCtor.jvmHeap, stCtor.heap⟩, ?_, hctorHi, hctorHp⟩
  dsimp only [initUiJvmState, Jvm.initJvmState]
  rw [initUiJvmState_5_locals]
  have hloc := setLocal_5_eval thisVal c p (.f32 pr) m
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.newClass "com/alexvanyo/composelife/ui/util/TargetState$InProgress") (by rfl) rfl]
  rw [stepInstr_newClass_inProgress]; dsimp only
  change Jvm.runJvmRes (mkUiCommonHooks resolveProg (d + 2) sf) (k + 9) TargetState_InProgress_copy_prog
      ⟨1, [.heapRef newAddr], _, jh0, hp⟩ = _
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ .dup (by rfl) rfl]; rw [stepInstr_dup]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 1) (by rfl) rfl]; rw [stepInstr_aload, hloc.2.1]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 2) (by rfl) rfl]; rw [stepInstr_aload, hloc.2.2.1]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.fload 3) (by rfl) rfl]; rw [stepInstr_fload, hloc.2.2.2.1]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 4) (by rfl) rfl]; rw [stepInstr_aload, hloc.2.2.2.2]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokespecial "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "<init>" "(Ljava/lang/Object;Ljava/lang/Object;FLjava/lang/Object;)V") (by rfl) rfl]
  rw [mkUiCommonHooks_stepInvokeSpecial_inProgress_init, hprog]; dsimp only
  rw [hctorRun]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ .areturn (by rfl) rfl]
  rw [stepInstr_areturn]

theorem copy_trap_equiv (resolveProg : String → Option (List JvmInstr))
    (d sf fuel : Nat) (hext : ExtendsUiProgs resolveProg) (hsf : 45 ≤ sf) (hf : 10 ≤ fuel)
    (thisVal c p : JvmVal) (pr : Float32) (m : JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap)
    (heq : Jvm.JvmVal.beqVal beqUiExt c p = true)
    (hcm : c.equalsModeled jh = true) (hpm : p.equalsModeled jh = true) :
    Jvm.runJvmRes (mkUiCommonHooks resolveProg (d + 2) sf) fuel
        TargetState_InProgress_copy_prog (initUiJvmState [(0, thisVal), (1, c), (2, p), (3, .f32 pr), (4, m)] hp jh) =
      none := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  have hprog := hext "TargetState$InProgress.<init>" TargetState_InProgress_init_prog rfl
  let obj0 : Jvm.HeapObj UiExt := .instance "com/alexvanyo/composelife/ui/util/TargetState$InProgress" []
  let newAddr := jh.objects.size
  let jh0 := (jh.alloc obj0).2
  have hget0 : jh0.get? newAddr = some (.instance "com/alexvanyo/composelife/ui/util/TargetState$InProgress" []) :=
    Jvm.jvmHeap_get?_alloc_self jh obj0
  have hctorTrap := inProgress_ctor_trap_equiv resolveProg d sf sf hext (by omega) hsf jh0 newAddr
    "com/alexvanyo/composelife/ui/util/TargetState$InProgress" [] hget0 (Or.inl rfl) c p pr m hp heq
    (Jvm.jvmVal_equalsModeled_alloc _ c hcm) (Jvm.jvmVal_equalsModeled_alloc _ p hpm)
  dsimp only [initUiJvmState, Jvm.initJvmState]
  rw [initUiJvmState_5_locals]
  have hloc := setLocal_5_eval thisVal c p (.f32 pr) m
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.newClass "com/alexvanyo/composelife/ui/util/TargetState$InProgress") (by rfl) rfl]
  rw [stepInstr_newClass_inProgress]; dsimp only
  change Jvm.runJvmRes (mkUiCommonHooks resolveProg (d + 2) sf) (k + 9) TargetState_InProgress_copy_prog
      ⟨1, [.heapRef newAddr], _, jh0, hp⟩ = none
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ .dup (by rfl) rfl]; rw [stepInstr_dup]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 1) (by rfl) rfl]; rw [stepInstr_aload, hloc.2.1]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 2) (by rfl) rfl]; rw [stepInstr_aload, hloc.2.2.1]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.fload 3) (by rfl) rfl]; rw [stepInstr_fload, hloc.2.2.2.1]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 4) (by rfl) rfl]; rw [stepInstr_aload, hloc.2.2.2.2]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokespecial "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "<init>" "(Ljava/lang/Object;Ljava/lang/Object;FLjava/lang/Object;)V") (by rfl) rfl]
  rw [mkUiCommonHooks_stepInvokeSpecial_inProgress_init, hprog]; dsimp only
  rw [hctorTrap]

private theorem mkUiCommonHooks_stepInvokeVirtual_inProgress_copy
    (r : String → Option (List JvmInstr)) (d sf pc addr : Nat)
    (c p : JvmVal) (pr : Float32) (m : JvmVal)
    (stk : List JvmVal) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    Jvm.stepInstr (mkUiCommonHooks r (d + 1) sf)
        (.invokevirtual "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "copy"
          "(Ljava/lang/Object;Ljava/lang/Object;FLjava/lang/Object;)Lcom/alexvanyo/composelife/ui/util/TargetState$InProgress;")
        ⟨pc, m :: .f32 pr :: p :: c :: .heapRef addr :: stk, locs, jh, hp⟩ =
      match r "TargetState$InProgress.copy" with
      | some prog =>
        match Jvm.runJvmRes (mkUiCommonHooks r d sf) sf prog
            (initUiJvmState [(0, .heapRef addr), (1, c), (2, p), (3, .f32 pr), (4, m)] hp jh) with
        | some (res, endSt) => .inl (some ⟨pc + 1, res :: stk, locs, endSt.jvmHeap, endSt.heap⟩)
        | none => .inr none
      | none => .inr none := by
  rw [show Jvm.stepInstr (mkUiCommonHooks r (d + 1) sf)
        (.invokevirtual "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "copy"
          "(Ljava/lang/Object;Ljava/lang/Object;FLjava/lang/Object;)Lcom/alexvanyo/composelife/ui/util/TargetState$InProgress;")
        ⟨pc, m :: .f32 pr :: p :: c :: .heapRef addr :: stk, locs, jh, hp⟩ =
      match (match r "TargetState$InProgress.copy" with
        | some prog =>
          match Jvm.runJvmRes (mkUiCommonHooks r d sf) sf prog
              { pc := 0, stack := [],
                locals := (assignParamLocalsAux 0
                  (Jvm.parseMethodParamTags "(Ljava/lang/Object;Ljava/lang/Object;Ljava/lang/Object;FLjava/lang/Object;)Ljava/lang/Object;")
                  [.heapRef addr, c, p, .f32 pr, m]).foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal)),
                jvmHeap := jh, heap := hp } with
          | some (res, endSt) =>
            some (res, (⟨pc, m :: .f32 pr :: p :: c :: .heapRef addr :: stk, locs, endSt.jvmHeap, endSt.heap⟩ : JvmState))
          | none => none
        | none => none) with
      | some (res, st') => Sum.inl (some { st' with pc := pc + 1, stack := res :: stk })
      | none => Sum.inr none from rfl]
  rw [show Jvm.parseMethodParamTags
      "(Ljava/lang/Object;Ljava/lang/Object;Ljava/lang/Object;FLjava/lang/Object;)Ljava/lang/Object;" =
      ['L', 'L', 'L', 'F', 'L'] from by decide, assignParamLocals_5]
  cases r "TargetState$InProgress.copy" with
  | none => rfl
  | some prog =>
    dsimp only [initUiJvmState, Jvm.initJvmState] at *
    cases Jvm.runJvmRes (mkUiCommonHooks r d sf) sf prog
        { pc := 0, stack := [],
          locals := List.foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal))
            [(0, .heapRef addr), (1, c), (2, p), (3, .f32 pr), (4, m)],
          jvmHeap := jh, heap := hp } <;> rfl

private theorem copy_default_cps (resolveProg : String → Option (List JvmInstr))
    (d sf fuel : Nat)
    {jh : Jvm.JvmHeap UiExt} {addr : Nat} {cOld pOld : JvmVal} {prOld : Float32} {mOld : JvmVal}
    (hi : HasInProgressFields jh addr cOld pOld prOld mOld)
    (cArg pArg : JvmVal) (prArg : Float32) (mArg : JvmVal) (mask : UInt32) (handler : JvmVal)
    (hp : UiHeap) (P : Option (JvmVal × JvmState) → Prop)
    (hf : 36 ≤ fuel)
    (hcont : ∀ f' locs', 8 ≤ f' →
      locs' 0 = .heapRef addr →
      locs' 1 = (if (mask &&& 1) == 0 then cArg else cOld) →
      locs' 2 = (if (mask &&& 2) == 0 then pArg else pOld) →
      locs' 3 = .f32 (if (mask &&& 4) == 0 then prArg else prOld) →
      locs' 4 = (if (mask &&& 8) == 0 then mArg else mOld) →
      P (Jvm.runJvmRes (mkUiCommonHooks resolveProg (d + 3) sf) f' TargetState_InProgress_copy_default_prog ⟨28, [], locs', jh, hp⟩)) :
    P (Jvm.runJvmRes (mkUiCommonHooks resolveProg (d + 3) sf) fuel TargetState_InProgress_copy_default_prog
      (initUiJvmState [(0, .heapRef addr), (1, cArg), (2, pArg), (3, .f32 prArg),
        (4, mArg), (5, .i32 mask), (6, handler)] hp jh)) := by
  let cRes := if (mask &&& 1) == 0 then cArg else cOld
  let pRes := if (mask &&& 2) == 0 then pArg else pOld
  let prRes := if (mask &&& 4) == 0 then prArg else prOld
  let mRes := if (mask &&& 8) == 0 then mArg else mOld
  have hStep3 : ∀ f3 locs3, 15 ≤ f3 →
      locs3 0 = .heapRef addr → locs3 1 = cRes → locs3 2 = pRes →
      locs3 3 = .f32 prRes → locs3 4 = mArg → locs3 5 = .i32 mask →
      P (Jvm.runJvmRes (mkUiCommonHooks resolveProg (d + 3) sf) f3 TargetState_InProgress_copy_default_prog ⟨21, [], locs3, jh, hp⟩) := by
    intro f3 locs3 hf3 hl0 hl1 hl2 hl3 hl4 hl5
    obtain ⟨k3, rfl⟩ := Nat.exists_eq_add_of_le' hf3
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.iload 5) (by rfl) rfl]; rw [stepInstr_iload, hl5]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.iconst 8) (by rfl) rfl]; rw [stepInstr_iconst]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ .iand (by rfl) rfl]; rw [stepInstr_iand_i32]; dsimp only
    rw [runJvmRes_ifeq_i32 _ _ _ 24 28 (mask &&& 8) _ _ _ _ (by rfl) (mkUiCommonHooks_isZero? _ _ _)]
    by_cases h8 : (mask &&& 8) = 0
    · simp only [h8, beq_self_eq_true, ↓reduceIte]
      exact hcont (k3 + 11) locs3 (by omega) hl0
        (by simpa [cRes] using hl1) (by simpa [pRes] using hl2)
        (by simpa [prRes] using hl3) (by simp [h8, hl4])
    · simp only [beq_false_of_ne h8, Bool.false_eq_true, ↓reduceIte]
      rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, hl0]; dsimp only
      rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.getfield "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "metadata" "Ljava/lang/Object;") (by rfl) rfl]
      rw [(stepGetField_inProgress resolveProg (d + 3) sf 26 hi).2.2.2]; dsimp only
      rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.astore 4) (by rfl) rfl]; rw [stepInstr_astore]; dsimp only
      exact hcont (k3 + 8) _ (by omega)
        (by simp [setLocal, hl0]) (by simpa [setLocal, cRes] using hl1)
        (by simpa [setLocal, pRes] using hl2) (by simpa [setLocal, prRes] using hl3)
        (by simp [setLocal, beq_false_of_ne h8])
  have hStep2 : ∀ f2 locs2, 22 ≤ f2 →
      locs2 0 = .heapRef addr → locs2 1 = cRes → locs2 2 = pRes →
      locs2 3 = .f32 prArg → locs2 4 = mArg → locs2 5 = .i32 mask →
      P (Jvm.runJvmRes (mkUiCommonHooks resolveProg (d + 3) sf) f2 TargetState_InProgress_copy_default_prog ⟨14, [], locs2, jh, hp⟩) := by
    intro f2 locs2 hf2 hl0 hl1 hl2 hl3 hl4 hl5
    obtain ⟨k2, rfl⟩ := Nat.exists_eq_add_of_le' hf2
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.iload 5) (by rfl) rfl]; rw [stepInstr_iload, hl5]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.iconst 4) (by rfl) rfl]; rw [stepInstr_iconst]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ .iand (by rfl) rfl]; rw [stepInstr_iand_i32]; dsimp only
    rw [runJvmRes_ifeq_i32 _ _ _ 17 21 (mask &&& 4) _ _ _ _ (by rfl) (mkUiCommonHooks_isZero? _ _ _)]
    by_cases h4 : (mask &&& 4) = 0
    · simp only [h4, beq_self_eq_true, ↓reduceIte]
      exact hStep3 (k2 + 18) locs2 (by omega) hl0 hl1 hl2 (by simpa [prRes, h4] using hl3) hl4 hl5
    · simp only [beq_false_of_ne h4, Bool.false_eq_true, ↓reduceIte]
      rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, hl0]; dsimp only
      rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.getfield "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "progress" "F") (by rfl) rfl]
      rw [(stepGetField_inProgress resolveProg (d + 3) sf 19 hi).2.2.1]; dsimp only
      rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.fstore 3) (by rfl) rfl]; rw [stepInstr_fstore]; dsimp only
      exact hStep3 (k2 + 15) _ (by omega)
        (by simp [setLocal, hl0]) (by simp [setLocal, hl1])
        (by simp [setLocal, hl2]) (by simp [setLocal, prRes, beq_false_of_ne h4])
        (by simp [setLocal, hl4]) (by simp [setLocal, hl5])
  have hStep1 : ∀ f1 locs1, 29 ≤ f1 →
      locs1 0 = .heapRef addr → locs1 1 = cRes → locs1 2 = pArg →
      locs1 3 = .f32 prArg → locs1 4 = mArg → locs1 5 = .i32 mask →
      P (Jvm.runJvmRes (mkUiCommonHooks resolveProg (d + 3) sf) f1 TargetState_InProgress_copy_default_prog ⟨7, [], locs1, jh, hp⟩) := by
    intro f1 locs1 hf1 hl0 hl1 hl2 hl3 hl4 hl5
    obtain ⟨k1, rfl⟩ := Nat.exists_eq_add_of_le' hf1
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.iload 5) (by rfl) rfl]; rw [stepInstr_iload, hl5]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.iconst 2) (by rfl) rfl]; rw [stepInstr_iconst]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ .iand (by rfl) rfl]; rw [stepInstr_iand_i32]; dsimp only
    rw [runJvmRes_ifeq_i32 _ _ _ 10 14 (mask &&& 2) _ _ _ _ (by rfl) (mkUiCommonHooks_isZero? _ _ _)]
    by_cases h2 : (mask &&& 2) = 0
    · simp only [h2, beq_self_eq_true, ↓reduceIte]
      exact hStep2 (k1 + 25) locs1 (by omega) hl0 hl1 (by simpa [pRes, h2] using hl2) hl3 hl4 hl5
    · simp only [beq_false_of_ne h2, Bool.false_eq_true, ↓reduceIte]
      rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, hl0]; dsimp only
      rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.getfield "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "provisional" "Ljava/lang/Object;") (by rfl) rfl]
      rw [(stepGetField_inProgress resolveProg (d + 3) sf 12 hi).2.1]; dsimp only
      rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.astore 2) (by rfl) rfl]; rw [stepInstr_astore]; dsimp only
      exact hStep2 (k1 + 22) _ (by omega)
        (by simp [setLocal, hl0]) (by simp [setLocal, hl1])
        (by simp [setLocal, pRes, beq_false_of_ne h2])
        (by simp [setLocal, hl3]) (by simp [setLocal, hl4]) (by simp [setLocal, hl5])
  obtain ⟨k0, rfl⟩ := Nat.exists_eq_add_of_le' hf
  dsimp only [initUiJvmState, Jvm.initJvmState]
  have hLoc0 :
      let locs0 := ([(0, .heapRef addr), (1, cArg), (2, pArg), (3, .f32 prArg),
        (4, mArg), (5, .i32 mask), (6, handler)]).foldl
        (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal))
      locs0 0 = .heapRef addr ∧ locs0 1 = cArg ∧ locs0 2 = pArg ∧
      locs0 3 = .f32 prArg ∧ locs0 4 = mArg ∧ locs0 5 = .i32 mask :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.iload 5) (by rfl) rfl]; rw [stepInstr_iload, hLoc0.2.2.2.2.2]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.iconst 1) (by rfl) rfl]; rw [stepInstr_iconst]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ .iand (by rfl) rfl]; rw [stepInstr_iand_i32]; dsimp only
  rw [runJvmRes_ifeq_i32 _ _ _ 3 7 (mask &&& 1) _ _ _ _ (by rfl) (mkUiCommonHooks_isZero? _ _ _)]
  by_cases h1 : (mask &&& 1) = 0
  · simp only [h1, beq_self_eq_true, ↓reduceIte]
    exact hStep1 (k0 + 32) _ (by omega) hLoc0.1 (by simpa [cRes, h1] using hLoc0.2.1)
      hLoc0.2.2.1 hLoc0.2.2.2.1 hLoc0.2.2.2.2.1 hLoc0.2.2.2.2.2
  · simp only [beq_false_of_ne h1, Bool.false_eq_true, ↓reduceIte]
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, hLoc0.1]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.getfield "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "current" "Ljava/lang/Object;") (by rfl) rfl]
    rw [(stepGetField_inProgress resolveProg (d + 3) sf 5 hi).1]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.astore 1) (by rfl) rfl]; rw [stepInstr_astore]; dsimp only
    exact hStep1 (k0 + 29) _ (by omega)
      (by simp [setLocal, hLoc0.1]) (by simp [setLocal, cRes, beq_false_of_ne h1])
      (by simp [setLocal, hLoc0.2.2.1]) (by simp [setLocal, hLoc0.2.2.2.1])
      (by simp [setLocal, hLoc0.2.2.2.2.1]) (by simp [setLocal, hLoc0.2.2.2.2.2])

theorem copy_default_valid_equiv (resolveProg : String → Option (List JvmInstr))
    (d sf fuel : Nat) (hext : ExtendsUiProgs resolveProg) (hsf : 45 ≤ sf) (hf : 36 ≤ fuel)
    {jh : Jvm.JvmHeap UiExt} {addr : Nat} {cOld pOld : JvmVal} {prOld : Float32} {mOld : JvmVal}
    (hi : HasInProgressFields jh addr cOld pOld prOld mOld)
    (cArg pArg : JvmVal) (prArg : Float32) (mArg : JvmVal) (mask : UInt32) (handler : JvmVal)
    (hp : UiHeap)
    (hne : Jvm.JvmVal.beqVal beqUiExt
      (if (mask &&& 1) == 0 then cArg else cOld)
      (if (mask &&& 2) == 0 then pArg else pOld) = false)
    (hcm : (if (mask &&& 1) == 0 then cArg else cOld).equalsModeled jh = true)
    (hpm : (if (mask &&& 2) == 0 then pArg else pOld).equalsModeled jh = true) :
    let cRes := if (mask &&& 1) == 0 then cArg else cOld
    let pRes := if (mask &&& 2) == 0 then pArg else pOld
    let prRes := if (mask &&& 4) == 0 then prArg else prOld
    let mRes := if (mask &&& 8) == 0 then mArg else mOld
    ∃ st',
      Jvm.runJvmRes (mkUiCommonHooks resolveProg (d + 3) sf) fuel
          TargetState_InProgress_copy_default_prog
          (initUiJvmState [(0, .heapRef addr), (1, cArg), (2, pArg), (3, .f32 prArg),
            (4, mArg), (5, .i32 mask), (6, handler)] hp jh) =
        some (.heapRef jh.objects.size, st') ∧
      HasInProgressFields st'.jvmHeap jh.objects.size cRes pRes prRes mRes ∧
      st'.heap = hp := by
  let cRes := if (mask &&& 1) == 0 then cArg else cOld
  let pRes := if (mask &&& 2) == 0 then pArg else pOld
  let prRes := if (mask &&& 4) == 0 then prArg else prOld
  let mRes := if (mask &&& 8) == 0 then mArg else mOld
  have hcopyProg := hext "TargetState$InProgress.copy" TargetState_InProgress_copy_prog rfl
  rcases copy_valid_equiv resolveProg d sf sf hext hsf (by omega) (.heapRef addr)
    cRes pRes prRes mRes jh hp hne hcm hpm with ⟨stCopy, hcopyRun, hcopyHi, hcopyHp⟩
  apply copy_default_cps resolveProg d sf fuel hi cArg pArg prArg mArg mask handler hp
    (fun r => ∃ st', r = some (.heapRef jh.objects.size, st') ∧
      HasInProgressFields st'.jvmHeap jh.objects.size cRes pRes prRes mRes ∧ st'.heap = hp)
    hf
  intro f' locs' hf' hl0 hl1 hl2 hl3 hl4
  obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le' hf'
  refine ⟨⟨34, [.heapRef jh.objects.size], locs', stCopy.jvmHeap, stCopy.heap⟩, ?_, hcopyHi, hcopyHp⟩
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, hl0]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 1) (by rfl) rfl]; rw [stepInstr_aload, hl1]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 2) (by rfl) rfl]; rw [stepInstr_aload, hl2]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.fload 3) (by rfl) rfl]; rw [stepInstr_fload, hl3]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 4) (by rfl) rfl]; rw [stepInstr_aload, hl4]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokevirtual "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "copy"
    "(Ljava/lang/Object;Ljava/lang/Object;FLjava/lang/Object;)Lcom/alexvanyo/composelife/ui/util/TargetState$InProgress;")
    (by rfl) rfl]
  rw [mkUiCommonHooks_stepInvokeVirtual_inProgress_copy, hcopyProg]; dsimp only
  rw [hcopyRun]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ .areturn (by rfl) rfl]
  rw [stepInstr_areturn]

theorem copy_default_trap_equiv (resolveProg : String → Option (List JvmInstr))
    (d sf fuel : Nat) (hext : ExtendsUiProgs resolveProg) (hsf : 45 ≤ sf) (hf : 36 ≤ fuel)
    {jh : Jvm.JvmHeap UiExt} {addr : Nat} {cOld pOld : JvmVal} {prOld : Float32} {mOld : JvmVal}
    (hi : HasInProgressFields jh addr cOld pOld prOld mOld)
    (cArg pArg : JvmVal) (prArg : Float32) (mArg : JvmVal) (mask : UInt32) (handler : JvmVal)
    (hp : UiHeap)
    (heq : Jvm.JvmVal.beqVal beqUiExt
      (if (mask &&& 1) == 0 then cArg else cOld)
      (if (mask &&& 2) == 0 then pArg else pOld) = true)
    (hcm : (if (mask &&& 1) == 0 then cArg else cOld).equalsModeled jh = true)
    (hpm : (if (mask &&& 2) == 0 then pArg else pOld).equalsModeled jh = true) :
    Jvm.runJvmRes (mkUiCommonHooks resolveProg (d + 3) sf) fuel
        TargetState_InProgress_copy_default_prog
        (initUiJvmState [(0, .heapRef addr), (1, cArg), (2, pArg), (3, .f32 prArg),
          (4, mArg), (5, .i32 mask), (6, handler)] hp jh) =
      none := by
  let cRes := if (mask &&& 1) == 0 then cArg else cOld
  let pRes := if (mask &&& 2) == 0 then pArg else pOld
  let prRes := if (mask &&& 4) == 0 then prArg else prOld
  let mRes := if (mask &&& 8) == 0 then mArg else mOld
  have hcopyProg := hext "TargetState$InProgress.copy" TargetState_InProgress_copy_prog rfl
  have hcopyTrap := copy_trap_equiv resolveProg d sf sf hext hsf (by omega) (.heapRef addr)
    cRes pRes prRes mRes jh hp heq hcm hpm
  apply copy_default_cps resolveProg d sf fuel hi cArg pArg prArg mArg mask handler hp
    (fun r => r = none) hf
  intro f' locs' hf' hl0 hl1 hl2 hl3 hl4
  obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le' hf'
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, hl0]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 1) (by rfl) rfl]; rw [stepInstr_aload, hl1]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 2) (by rfl) rfl]; rw [stepInstr_aload, hl2]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.fload 3) (by rfl) rfl]; rw [stepInstr_fload, hl3]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 4) (by rfl) rfl]; rw [stepInstr_aload, hl4]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokevirtual "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "copy"
    "(Ljava/lang/Object;Ljava/lang/Object;FLjava/lang/Object;)Lcom/alexvanyo/composelife/ui/util/TargetState$InProgress;")
    (by rfl) rfl]
  rw [mkUiCommonHooks_stepInvokeVirtual_inProgress_copy, hcopyProg]; dsimp only
  rw [hcopyTrap]

private theorem evalMakeConcat_inProgress_toString_none (c p m : JvmVal) (pr : Float32) :
    Jvm.evalMakeConcatWithConstants
      "InProgress(current=\x01, provisional=\x01, progress=\x01, metadata=\x01)"
      "(Ljava/lang/Object;Ljava/lang/Object;FLjava/lang/Object;)Ljava/lang/String;"
      [m, .f32 pr, p, c] = none := by
  dsimp only [Jvm.evalMakeConcatWithConstants]
  rw [show Jvm.parseMethodParamTags "(Ljava/lang/Object;Ljava/lang/Object;FLjava/lang/Object;)Ljava/lang/String;" =
      ['L', 'L', 'F', 'L'] from by decide]
  rw [show String.toList "InProgress(current=\x01, provisional=\x01, progress=\x01, metadata=\x01)" =
      ['I','n','P','r','o','g','r','e','s','s','(','c','u','r','r','e','n','t','=','\x01',',',' ',
       'p','r','o','v','i','s','i','o','n','a','l','=','\x01',',',' ','p','r','o','g','r','e','s','s','=',
       '\x01',',',' ','m','e','t','a','d','a','t','a','=','\x01',')'] from by decide]
  cases c <;> (try rfl) <;> (cases p <;> rfl)

theorem toString_halts_equiv (resolveProg : String → Option (List JvmInstr))
    (depth sf fuel : Nat) (hf : 10 ≤ fuel)
    {jh : Jvm.JvmHeap UiExt} {addr : Nat} {c p : JvmVal} {pr : Float32} {m : JvmVal}
    (hi : HasInProgressFields jh addr c p pr m) (hp : UiHeap) :
    Jvm.runJvmRes (mkUiCommonHooks resolveProg depth sf) fuel
        TargetState_InProgress_toString_prog (initUiJvmState [(0, .heapRef addr)] hp jh) =
      none := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  dsimp only [initUiJvmState, Jvm.initJvmState]
  have h0 : ([(0, Jvm.JvmVal.heapRef addr)]).foldl (fun loc (i, v) => setLocal loc i v)
      (fun (_ : Nat) => (.i32 0 : JvmVal)) 0 = .heapRef addr := rfl
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, h0]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.getfield "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "current" "Ljava/lang/Object;") (by rfl) rfl]
  rw [(stepGetField_inProgress resolveProg depth sf 1 hi).1]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, h0]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.getfield "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "provisional" "Ljava/lang/Object;") (by rfl) rfl]
  rw [(stepGetField_inProgress resolveProg depth sf 3 hi).2.1]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, h0]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.getfield "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "progress" "F") (by rfl) rfl]
  rw [(stepGetField_inProgress resolveProg depth sf 5 hi).2.2.1]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, h0]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.getfield "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "metadata" "Ljava/lang/Object;") (by rfl) rfl]
  rw [(stepGetField_inProgress resolveProg depth sf 7 hi).2.2.2]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokedynamic "makeConcatWithConstants"
    "InProgress(current=\x01, provisional=\x01, progress=\x01, metadata=\x01)"
    "(Ljava/lang/Object;Ljava/lang/Object;FLjava/lang/Object;)Ljava/lang/String;") (by rfl) rfl]
  unfold Jvm.stepInstr
  simp [evalMakeConcat_inProgress_toString_none c p m pr]

def uiNullableHashCode (v : JvmVal) : Option UInt32 :=
  match v with
  | .null => some 0
  | _ => jvmValHashCode v

private theorem stepInstr_invokeVirtual_obj_hashCode (r : String → Option (List JvmInstr))
    (d sf pc : Nat) (v : JvmVal) (h : UInt32) (hh : jvmValHashCode v = some h)
    (stk : List JvmVal) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    Jvm.stepInstr (mkUiCommonHooks r d sf) (.invokevirtual "java/lang/Object" "hashCode" "()I")
        ⟨pc, v :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 h :: stk, locs, jh, hp⟩) := by
  unfold Jvm.stepInstr Jvm.stepInvokeVirtualGeneric
  dsimp only
  rw [mkUiCommonHooks_stepInvokeVirtual_obj_hashCode, hh]
  rfl

private theorem stepInstr_invokeStatic_float_hashCode (r : String → Option (List JvmInstr))
    (d sf pc : Nat) (f : Float32) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    Jvm.stepInstr (mkUiCommonHooks r d sf) (.invokestatic "java/lang/Float" "hashCode" "(F)I")
        ⟨pc, .f32 f :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 (floatHashCode f) :: stk, locs, jh, hp⟩) := by
  unfold Jvm.stepInstr Jvm.stepInvokeStaticGeneric
  dsimp only
  rw [mkUiCommonHooks_stepInvokeStatic_float_hashCode]
  rfl

private theorem stepInstr_invokeStatic_float_compare (r : String → Option (List JvmInstr))
    (d sf pc : Nat) (a b : Float32) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    Jvm.stepInstr (mkUiCommonHooks r d sf) (.invokestatic "java/lang/Float" "compare" "(FF)I")
        ⟨pc, .f32 b :: .f32 a :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 (Model.floatCompare a b).toUInt32 :: stk, locs, jh, hp⟩) := by
  unfold Jvm.stepInstr Jvm.stepInvokeStaticGeneric
  dsimp only
  rw [mkUiCommonHooks_stepInvokeStatic_float_compare]
  rfl

theorem hashCode_equiv (resolveProg : String → Option (List JvmInstr))
    (depth sf fuel : Nat) (hf : 45 ≤ fuel)
    {jh : Jvm.JvmHeap UiExt} {addr : Nat} {c p : JvmVal} {pr : Float32} {m : JvmVal}
    (hi : HasInProgressFields jh addr c p pr m) (hp : UiHeap)
    {hc hp' hm : UInt32}
    (hhc : uiNullableHashCode c = some hc)
    (hhp : uiNullableHashCode p = some hp')
    (hhm : uiNullableHashCode m = some hm) :
    let expected := (((hc * 31 + hp') * 31 + floatHashCode pr) * 31) + hm
    ∃ st',
      Jvm.runJvmRes (mkUiCommonHooks resolveProg depth sf) fuel
          TargetState_InProgress_hashCode_prog (initUiJvmState [(0, .heapRef addr)] hp jh) =
        some (.i32 expected, st') ∧
      st'.jvmHeap = jh ∧ st'.heap = hp := by
  let expected := (((hc * 31 + hp') * 31 + floatHashCode pr) * 31) + hm
  have hTail : ∀ f3 locs3, 2 ≤ f3 → locs3 1 = .i32 expected →
      ∃ st', Jvm.runJvmRes (mkUiCommonHooks resolveProg depth sf) f3 TargetState_InProgress_hashCode_prog
          ⟨43, [], locs3, jh, hp⟩ = some (.i32 expected, st') ∧
        st'.jvmHeap = jh ∧ st'.heap = hp := by
    intro f3 locs3 hf3 hl1
    obtain ⟨k3, rfl⟩ := Nat.exists_eq_add_of_le' hf3
    refine ⟨⟨44, [.i32 expected], locs3, jh, hp⟩, ?_, rfl, rfl⟩
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.iload 1) (by rfl) rfl]; rw [stepInstr_iload, hl1]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ .ireturn (by rfl) rfl]
    rw [stepInstr_ireturn]
  have hMeta : ∀ f2 locs2, 16 ≤ f2 →
      locs2 0 = .heapRef addr →
      locs2 1 = .i32 ((hc * 31 + hp') * 31 + floatHashCode pr) →
      ∃ st', Jvm.runJvmRes (mkUiCommonHooks resolveProg depth sf) f2 TargetState_InProgress_hashCode_prog
          ⟨30, [], locs2, jh, hp⟩ = some (.i32 expected, st') ∧
        st'.jvmHeap = jh ∧ st'.heap = hp := by
    intro f2 locs2 hf2 hl0 hl1
    obtain ⟨k2, rfl⟩ := Nat.exists_eq_add_of_le' hf2
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.iload 1) (by rfl) rfl]; rw [stepInstr_iload, hl1]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.iconst 31) (by rfl) rfl]; rw [stepInstr_iconst]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ .imul (by rfl) rfl]; rw [stepInstr_imul_i32]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, hl0]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.getfield "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "metadata" "Ljava/lang/Object;") (by rfl) rfl]
    rw [(stepGetField_inProgress resolveProg depth sf 34 hi).2.2.2]; dsimp only
    rw [runJvmRes_ifnonnull _ _ _ 35 38 m _ _ _ _ (by rfl)]
    cases hmNull : m.isNull with
    | true =>
      have hmEq : m = .null := by cases m <;> simp [Jvm.JvmVal.isNull] at hmNull; rfl
      subst hmEq
      have hmz : hm = 0 := by simpa [uiNullableHashCode] using hhm.symm
      subst hmz
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.iconst 0) (by rfl) rfl]; rw [stepInstr_iconst]; dsimp only
      rw [runJvmRes_goto _ _ _ _ 41 (by rfl)]; dsimp only
      rw [Jvm.runJvmRes_nonbranch _ _ _ _ .iadd (by rfl) rfl]; rw [stepInstr_iadd_i32]; dsimp only
      rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.istore 1) (by rfl) rfl]; rw [stepInstr_istore_i32]; dsimp only
      exact hTail (k2 + 7) _ (by omega) (by simp [setLocal, expected])
    | false =>
      have hmj : jvmValHashCode m = some hm := by
        cases m <;> simp [Jvm.JvmVal.isNull] at hmNull <;> simpa [uiNullableHashCode] using hhm
      simp only [Bool.not_false, ↓reduceIte]
      rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, hl0]; dsimp only
      rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.getfield "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "metadata" "Ljava/lang/Object;") (by rfl) rfl]
      rw [(stepGetField_inProgress resolveProg depth sf 39 hi).2.2.2]; dsimp only
      rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokevirtual "java/lang/Object" "hashCode" "()I") (by rfl) rfl]
      rw [stepInstr_invokeVirtual_obj_hashCode resolveProg depth sf 40 m hm hmj]; dsimp only
      rw [Jvm.runJvmRes_nonbranch _ _ _ _ .iadd (by rfl) rfl]; rw [stepInstr_iadd_i32]; dsimp only
      rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.istore 1) (by rfl) rfl]; rw [stepInstr_istore_i32]; dsimp only
      exact hTail (k2 + 5) _ (by omega) (by simp [setLocal, expected])
  have hProg : ∀ f1 locs1, 24 ≤ f1 →
      locs1 0 = .heapRef addr → locs1 1 = .i32 (hc * 31 + hp') →
      ∃ st', Jvm.runJvmRes (mkUiCommonHooks resolveProg depth sf) f1 TargetState_InProgress_hashCode_prog
          ⟨22, [], locs1, jh, hp⟩ = some (.i32 expected, st') ∧
        st'.jvmHeap = jh ∧ st'.heap = hp := by
    intro f1 locs1 hf1 hl0 hl1
    obtain ⟨k1, rfl⟩ := Nat.exists_eq_add_of_le' hf1
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.iload 1) (by rfl) rfl]; rw [stepInstr_iload, hl1]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.iconst 31) (by rfl) rfl]; rw [stepInstr_iconst]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ .imul (by rfl) rfl]; rw [stepInstr_imul_i32]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, hl0]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.getfield "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "progress" "F") (by rfl) rfl]
    rw [(stepGetField_inProgress resolveProg depth sf 26 hi).2.2.1]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokestatic "java/lang/Float" "hashCode" "(F)I") (by rfl) rfl]
    rw [stepInstr_invokeStatic_float_hashCode]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ .iadd (by rfl) rfl]; rw [stepInstr_iadd_i32]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.istore 1) (by rfl) rfl]; rw [stepInstr_istore_i32]; dsimp only
    exact hMeta (k1 + 16) _ (by omega) (by simp [setLocal, hl0]) (by simp [setLocal])
  have hProv : ∀ f0 locs0, 36 ≤ f0 →
      locs0 0 = .heapRef addr → locs0 1 = .i32 hc →
      ∃ st', Jvm.runJvmRes (mkUiCommonHooks resolveProg depth sf) f0 TargetState_InProgress_hashCode_prog
          ⟨9, [], locs0, jh, hp⟩ = some (.i32 expected, st') ∧
        st'.jvmHeap = jh ∧ st'.heap = hp := by
    intro f0 locs0 hf0 hl0 hl1
    obtain ⟨k0, rfl⟩ := Nat.exists_eq_add_of_le' hf0
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.iload 1) (by rfl) rfl]; rw [stepInstr_iload, hl1]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.iconst 31) (by rfl) rfl]; rw [stepInstr_iconst]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ .imul (by rfl) rfl]; rw [stepInstr_imul_i32]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, hl0]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.getfield "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "provisional" "Ljava/lang/Object;") (by rfl) rfl]
    rw [(stepGetField_inProgress resolveProg depth sf 13 hi).2.1]; dsimp only
    rw [runJvmRes_ifnonnull _ _ _ 14 17 p _ _ _ _ (by rfl)]
    cases hpNull : p.isNull with
    | true =>
      have hpEq : p = .null := by cases p <;> simp [Jvm.JvmVal.isNull] at hpNull; rfl
      subst hpEq
      have hpz : hp' = 0 := by simpa [uiNullableHashCode] using hhp.symm
      subst hpz
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.iconst 0) (by rfl) rfl]; rw [stepInstr_iconst]; dsimp only
      rw [runJvmRes_goto _ _ _ _ 20 (by rfl)]; dsimp only
      rw [Jvm.runJvmRes_nonbranch _ _ _ _ .iadd (by rfl) rfl]; rw [stepInstr_iadd_i32]; dsimp only
      rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.istore 1) (by rfl) rfl]; rw [stepInstr_istore_i32]; dsimp only
      exact hProg (k0 + 26) _ (by omega) (by simp [setLocal, hl0]) (by simp [setLocal])
    | false =>
      have hpj : jvmValHashCode p = some hp' := by
        cases p <;> simp [Jvm.JvmVal.isNull] at hpNull <;> simpa [uiNullableHashCode] using hhp
      simp only [Bool.not_false, ↓reduceIte]
      rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, hl0]; dsimp only
      rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.getfield "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "provisional" "Ljava/lang/Object;") (by rfl) rfl]
      rw [(stepGetField_inProgress resolveProg depth sf 18 hi).2.1]; dsimp only
      rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokevirtual "java/lang/Object" "hashCode" "()I") (by rfl) rfl]
      rw [stepInstr_invokeVirtual_obj_hashCode resolveProg depth sf 19 p hp' hpj]; dsimp only
      rw [Jvm.runJvmRes_nonbranch _ _ _ _ .iadd (by rfl) rfl]; rw [stepInstr_iadd_i32]; dsimp only
      rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.istore 1) (by rfl) rfl]; rw [stepInstr_istore_i32]; dsimp only
      exact hProg (k0 + 25) _ (by omega) (by simp [setLocal, hl0]) (by simp [setLocal])
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  dsimp only [initUiJvmState, Jvm.initJvmState]
  have h0 : ([(0, Jvm.JvmVal.heapRef addr)]).foldl (fun loc (i, v) => setLocal loc i v)
      (fun (_ : Nat) => (.i32 0 : JvmVal)) 0 = .heapRef addr := rfl
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, h0]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.getfield "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "current" "Ljava/lang/Object;") (by rfl) rfl]
  rw [(stepGetField_inProgress resolveProg depth sf 1 hi).1]; dsimp only
  rw [runJvmRes_ifnonnull _ _ _ 2 5 c _ _ _ _ (by rfl)]
  cases hcNull : c.isNull with
  | true =>
    have hcEq : c = .null := by cases c <;> simp [Jvm.JvmVal.isNull] at hcNull; rfl
    subst hcEq
    have hcz : hc = 0 := by simpa [uiNullableHashCode] using hhc.symm
    subst hcz
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.iconst 0) (by rfl) rfl]; rw [stepInstr_iconst]; dsimp only
    rw [runJvmRes_goto _ _ _ _ 8 (by rfl)]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.istore 1) (by rfl) rfl]; rw [stepInstr_istore_i32]; dsimp only
    exact hProv (k + 39) _ (by omega) (by simp [setLocal, h0]) (by simp [setLocal])
  | false =>
    have hcj : jvmValHashCode c = some hc := by
      cases c <;> simp [Jvm.JvmVal.isNull] at hcNull <;> simpa [uiNullableHashCode] using hhc
    simp only [Bool.not_false, ↓reduceIte]
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, h0]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.getfield "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "current" "Ljava/lang/Object;") (by rfl) rfl]
    rw [(stepGetField_inProgress resolveProg depth sf 6 hi).1]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokevirtual "java/lang/Object" "hashCode" "()I") (by rfl) rfl]
    rw [stepInstr_invokeVirtual_obj_hashCode resolveProg depth sf 7 c hc hcj]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.istore 1) (by rfl) rfl]; rw [stepInstr_istore_i32]; dsimp only
    exact hProv (k + 38) _ (by omega) (by simp [setLocal, h0]) (by simp [setLocal])

private theorem stepInstr_instanceof_val (hooks : Jvm.JvmHooks UiExt UiHeap)
    (pc : Nat) (cls : String) (v : JvmVal) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    Jvm.stepInstr hooks (.instanceof cls) ⟨pc, v :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 (if Jvm.evalInstanceOf hooks jh cls v then 1 else 0) :: stk, locs, jh, hp⟩) := rfl

private theorem stepInstr_checkcast_some (hooks : Jvm.JvmHooks UiExt UiHeap)
    (pc : Nat) (cls : String) (v v' : JvmVal) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) (hcc : Jvm.evalCheckCast hooks jh cls v = some v') :
    Jvm.stepInstr hooks (.checkcast cls) ⟨pc, v :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, v' :: stk, locs, jh, hp⟩) := by
  unfold Jvm.stepInstr; simp [hcc]

theorem equals_sameRef_equiv (resolveProg : String → Option (List JvmInstr))
    (depth sf fuel : Nat) (hf : 6 ≤ fuel)
    (addr : Nat) (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    ∃ st',
      Jvm.runJvmRes (mkUiCommonHooks resolveProg depth sf) fuel
          TargetState_InProgress_equals_prog (initUiJvmState [(0, .heapRef addr), (1, .heapRef addr)] hp jh) =
        some (.i32 1, st') ∧
      st'.jvmHeap = jh ∧ st'.heap = hp := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  refine ⟨⟨4, [.i32 1], (initUiJvmState [(0, .heapRef addr), (1, .heapRef addr)] hp jh).locals, jh, hp⟩, ?_, rfl, rfl⟩
  dsimp only [initUiJvmState, Jvm.initJvmState]
  have h0 : ([(0, Jvm.JvmVal.heapRef addr), (1, .heapRef addr)]).foldl
      (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal)) 0 = .heapRef addr := rfl
  have h1 : ([(0, Jvm.JvmVal.heapRef addr), (1, .heapRef addr)]).foldl
      (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal)) 1 = .heapRef addr := rfl
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, h0]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 1) (by rfl) rfl]; rw [stepInstr_aload, h1]; dsimp only
  rw [runJvmRes_if_acmpne_heapRef _ _ _ 2 5 addr addr _ _ _ _ (by rfl)]
  simp only [beq_self_eq_true, ↓reduceIte]
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.iconst 1) (by rfl) rfl]; rw [stepInstr_iconst]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ .ireturn (by rfl) rfl]
  rw [stepInstr_ireturn]

theorem equals_null_equiv (resolveProg : String → Option (List JvmInstr))
    (depth sf fuel : Nat) (hf : 10 ≤ fuel)
    (addr : Nat) (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    ∃ st',
      Jvm.runJvmRes (mkUiCommonHooks resolveProg depth sf) fuel
          TargetState_InProgress_equals_prog (initUiJvmState [(0, .heapRef addr), (1, .null)] hp jh) =
        some (.i32 0, st') ∧
      st'.jvmHeap = jh ∧ st'.heap = hp := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  refine ⟨⟨9, [.i32 0], (initUiJvmState [(0, .heapRef addr), (1, .null)] hp jh).locals, jh, hp⟩,
    ?_, rfl, rfl⟩
  dsimp only [initUiJvmState, Jvm.initJvmState]
  have h0 : ([(0, Jvm.JvmVal.heapRef addr), (1, .null)]).foldl
      (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal)) 0 = .heapRef addr := rfl
  have h1 : ([(0, Jvm.JvmVal.heapRef addr), (1, .null)]).foldl
      (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal)) 1 = .null := rfl
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, h0]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 1) (by rfl) rfl]; rw [stepInstr_aload, h1]; dsimp only
  rw [runJvmRes_if_acmpne_heapRef_null _ _ _ 2 5 addr _ _ _ _ (by rfl)]
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 1) (by rfl) rfl]; rw [stepInstr_aload, h1]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.instanceof "com/alexvanyo/composelife/ui/util/TargetState$InProgress") (by rfl) rfl]
  rw [stepInstr_instanceof_val]
  simp only [Jvm.evalInstanceOf, Bool.false_eq_true, ↓reduceIte]
  rw [runJvmRes_ifne_i32 _ _ _ 7 10 0 _ _ _ _ (by rfl) (mkUiCommonHooks_isZero? _ _ _)]
  simp only [show ((0 : UInt32) != 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.iconst 0) (by rfl) rfl]; rw [stepInstr_iconst]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ .ireturn (by rfl) rfl]
  rw [stepInstr_ireturn]

theorem equals_single_equiv (resolveProg : String → Option (List JvmInstr))
    (depth sf fuel : Nat) (hf : 10 ≤ fuel)
    {jh : Jvm.JvmHeap UiExt} {addr1 addr2 : Nat} {c2 : JvmVal}
    (hne : addr1 ≠ addr2) (hs2 : HasSingleFields jh addr2 c2) (hp : UiHeap) :
    ∃ st',
      Jvm.runJvmRes (mkUiCommonHooks resolveProg depth sf) fuel
          TargetState_InProgress_equals_prog (initUiJvmState [(0, .heapRef addr1), (1, .heapRef addr2)] hp jh) =
        some (.i32 0, st') ∧
      st'.jvmHeap = jh ∧ st'.heap = hp := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  refine ⟨⟨9, [.i32 0], (initUiJvmState [(0, .heapRef addr1), (1, .heapRef addr2)] hp jh).locals, jh, hp⟩,
    ?_, rfl, rfl⟩
  dsimp only [initUiJvmState, Jvm.initJvmState]
  have h0 : ([(0, Jvm.JvmVal.heapRef addr1), (1, .heapRef addr2)]).foldl
      (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal)) 0 = .heapRef addr1 := rfl
  have h1 : ([(0, Jvm.JvmVal.heapRef addr1), (1, .heapRef addr2)]).foldl
      (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal)) 1 = .heapRef addr2 := rfl
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, h0]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 1) (by rfl) rfl]; rw [stepInstr_aload, h1]; dsimp only
  rw [runJvmRes_if_acmpne_heapRef _ _ _ 2 5 addr1 addr2 _ _ _ _ (by rfl)]
  simp only [beq_false_of_ne hne, Bool.false_eq_true, ↓reduceIte]
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 1) (by rfl) rfl]; rw [stepInstr_aload, h1]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.instanceof "com/alexvanyo/composelife/ui/util/TargetState$InProgress") (by rfl) rfl]
  rw [stepInstr_instanceof_val]
  simp only [Jvm.evalInstanceOf, checkInstanceOf_single_not_inProgress resolveProg depth sf hs2,
    Bool.false_eq_true, ↓reduceIte]
  rw [runJvmRes_ifne_i32 _ _ _ 7 10 0 _ _ _ _ (by rfl) (mkUiCommonHooks_isZero? _ _ _)]
  simp only [show ((0 : UInt32) != 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.iconst 0) (by rfl) rfl]; rw [stepInstr_iconst]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ .ireturn (by rfl) rfl]
  rw [stepInstr_ireturn]

theorem equals_inProgress_equiv (resolveProg : String → Option (List JvmInstr))
    (depth sf fuel : Nat) (hf : 48 ≤ fuel)
    {jh : Jvm.JvmHeap UiExt} {addr1 addr2 : Nat}
    {c1 p1 c2 p2 : JvmVal} {pr1 pr2 : Float32} {m1 m2 : JvmVal}
    (hne : addr1 ≠ addr2)
    (hi1 : HasInProgressFields jh addr1 c1 p1 pr1 m1)
    (hi2 : HasInProgressFields jh addr2 c2 p2 pr2 m2) (hp : UiHeap)
    (hmod : [c1, p1, m1, c2, p2, m2].all (·.equalsModeled jh) = true) :
    let eqBool :=
      Jvm.JvmVal.beqVal beqUiExt c1 c2 &&
      Jvm.JvmVal.beqVal beqUiExt p1 p2 &&
      (Model.floatCompare pr1 pr2 == 0) &&
      Jvm.JvmVal.beqVal beqUiExt m1 m2
    ∃ st',
      Jvm.runJvmRes (mkUiCommonHooks resolveProg depth sf) fuel
          TargetState_InProgress_equals_prog (initUiJvmState [(0, .heapRef addr1), (1, .heapRef addr2)] hp jh) =
        some (.i32 (if eqBool then 1 else 0), st') ∧
      st'.jvmHeap = jh ∧ st'.heap = hp := by
  intro eqBool
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hmod
  obtain ⟨hc1, hp1, hm1, hc2, hp2, hm2⟩ := hmod
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  dsimp only [initUiJvmState, Jvm.initJvmState]
  have h0 : ([(0, Jvm.JvmVal.heapRef addr1), (1, .heapRef addr2)]).foldl
      (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal)) 0 = .heapRef addr1 := rfl
  have h1 : ([(0, Jvm.JvmVal.heapRef addr1), (1, .heapRef addr2)]).foldl
      (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal)) 1 = .heapRef addr2 := rfl
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, h0]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 1) (by rfl) rfl]; rw [stepInstr_aload, h1]; dsimp only
  rw [runJvmRes_if_acmpne_heapRef _ _ _ 2 5 addr1 addr2 _ _ _ _ (by rfl)]
  simp only [beq_false_of_ne hne, Bool.false_eq_true, ↓reduceIte]
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 1) (by rfl) rfl]; rw [stepInstr_aload, h1]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.instanceof "com/alexvanyo/composelife/ui/util/TargetState$InProgress") (by rfl) rfl]
  rw [stepInstr_instanceof_val]; dsimp only [Jvm.evalInstanceOf]
  simp only [checkInstanceOf_inProgress resolveProg depth sf hi2, ↓reduceIte]
  rw [runJvmRes_ifne_i32 _ _ _ 7 10 1 _ _ _ _ (by rfl) (mkUiCommonHooks_isZero? _ _ _)]
  simp only [show ((1 : UInt32) != 0) = true from rfl, ↓reduceIte]
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 1) (by rfl) rfl]; rw [stepInstr_aload, h1]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.checkcast "com/alexvanyo/composelife/ui/util/TargetState$InProgress") (by rfl) rfl]
  rw [stepInstr_checkcast_some _ _ _ _ _ _ _ _ _ (evalCheckCast_inProgress resolveProg depth sf hi2)]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.astore 2) (by rfl) rfl]; rw [stepInstr_astore]; dsimp only
  have hl0 : setLocal (([(0, Jvm.JvmVal.heapRef addr1), (1, .heapRef addr2)]).foldl
      (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal))) 2 (.heapRef addr2) 0 =
      .heapRef addr1 := rfl
  have hl2 : setLocal (([(0, Jvm.JvmVal.heapRef addr1), (1, .heapRef addr2)]).foldl
      (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal))) 2 (.heapRef addr2) 2 =
      .heapRef addr2 := rfl
  let locs2 := setLocal (([(0, Jvm.JvmVal.heapRef addr1), (1, .heapRef addr2)]).foldl
      (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal))) 2 (.heapRef addr2)
  -- Compare current
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, hl0]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.getfield "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "current" "Ljava/lang/Object;") (by rfl) rfl]
  rw [(stepGetField_inProgress resolveProg depth sf 14 hi1).1]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 2) (by rfl) rfl]; rw [stepInstr_aload, hl2]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.getfield "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "current" "Ljava/lang/Object;") (by rfl) rfl]
  rw [(stepGetField_inProgress resolveProg depth sf 16 hi2).1]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokestatic "kotlin/jvm/internal/Intrinsics" "areEqual" "(Ljava/lang/Object;Ljava/lang/Object;)Z") (by rfl) rfl]
  rw [stepInstr_areEqual (ha := hc1) (hb := hc2)]; dsimp only
  rw [runJvmRes_ifne_bool _ _ _ 18 21 (Jvm.JvmVal.beqVal beqUiExt c1 c2) _ _ _ _ (by rfl) (mkUiCommonHooks_isZero? _ _ _)]
  cases hcEq : Jvm.JvmVal.beqVal beqUiExt c1 c2 with
  | false =>
    refine ⟨⟨20, [.i32 0], locs2, jh, hp⟩, ?_, rfl, rfl⟩
    simp only [Bool.false_eq_true, ↓reduceIte, hcEq, Bool.false_and, eqBool]
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.iconst 0) (by rfl) rfl]; rw [stepInstr_iconst]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ .ireturn (by rfl) rfl]; rw [stepInstr_ireturn]
  | true =>
    simp only [↓reduceIte]
    -- Compare provisional
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, hl0]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.getfield "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "provisional" "Ljava/lang/Object;") (by rfl) rfl]
    rw [(stepGetField_inProgress resolveProg depth sf 22 hi1).2.1]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 2) (by rfl) rfl]; rw [stepInstr_aload, hl2]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.getfield "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "provisional" "Ljava/lang/Object;") (by rfl) rfl]
    rw [(stepGetField_inProgress resolveProg depth sf 24 hi2).2.1]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokestatic "kotlin/jvm/internal/Intrinsics" "areEqual" "(Ljava/lang/Object;Ljava/lang/Object;)Z") (by rfl) rfl]
    rw [stepInstr_areEqual (ha := hp1) (hb := hp2)]; dsimp only
    rw [runJvmRes_ifne_bool _ _ _ 26 29 (Jvm.JvmVal.beqVal beqUiExt p1 p2) _ _ _ _ (by rfl) (mkUiCommonHooks_isZero? _ _ _)]
    cases hpEq : Jvm.JvmVal.beqVal beqUiExt p1 p2 with
    | false =>
      refine ⟨⟨28, [.i32 0], locs2, jh, hp⟩, ?_, rfl, rfl⟩
      simp only [Bool.false_eq_true, ↓reduceIte, hcEq, hpEq, Bool.true_and, Bool.false_and, eqBool]
      rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.iconst 0) (by rfl) rfl]; rw [stepInstr_iconst]; dsimp only
      rw [Jvm.runJvmRes_nonbranch _ _ _ _ .ireturn (by rfl) rfl]; rw [stepInstr_ireturn]
    | true =>
      simp only [↓reduceIte]
      -- Compare progress via Float.compare == 0
      rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, hl0]; dsimp only
      rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.getfield "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "progress" "F") (by rfl) rfl]
      rw [(stepGetField_inProgress resolveProg depth sf 30 hi1).2.2.1]; dsimp only
      rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 2) (by rfl) rfl]; rw [stepInstr_aload, hl2]; dsimp only
      rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.getfield "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "progress" "F") (by rfl) rfl]
      rw [(stepGetField_inProgress resolveProg depth sf 32 hi2).2.2.1]; dsimp only
      rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokestatic "java/lang/Float" "compare" "(FF)I") (by rfl) rfl]
      rw [stepInstr_invokeStatic_float_compare]; dsimp only
      rw [runJvmRes_ifeq_i32 _ _ _ 34 37 (Model.floatCompare pr1 pr2).toUInt32 _ _ _ _ (by rfl) (mkUiCommonHooks_isZero? _ _ _)]
      have hCmpIff : ((Model.floatCompare pr1 pr2).toUInt32 == 0) = (Model.floatCompare pr1 pr2 == 0) := by
        cases hcmp : Model.floatCompare pr1 pr2 with
        | ofUInt32 u =>
          by_cases hu : u = 0
          · subst hu; rfl
          · have hne : ({ toUInt32 := u } : Int32) ≠ 0 := fun h => hu (congrArg Int32.toUInt32 h)
            simp [beq_false_of_ne hu, beq_false_of_ne hne]
      rw [hCmpIff]
      cases hprEq : (Model.floatCompare pr1 pr2 == 0) with
      | false =>
        refine ⟨⟨36, [.i32 0], locs2, jh, hp⟩, ?_, rfl, rfl⟩
        simp only [Bool.false_eq_true, ↓reduceIte, hcEq, hpEq, hprEq, Bool.true_and, Bool.false_and, eqBool]
        rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.iconst 0) (by rfl) rfl]; rw [stepInstr_iconst]; dsimp only
        rw [Jvm.runJvmRes_nonbranch _ _ _ _ .ireturn (by rfl) rfl]; rw [stepInstr_ireturn]
      | true =>
        simp only [↓reduceIte]
        -- Compare metadata
        rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, hl0]; dsimp only
        rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.getfield "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "metadata" "Ljava/lang/Object;") (by rfl) rfl]
        rw [(stepGetField_inProgress resolveProg depth sf 38 hi1).2.2.2]; dsimp only
        rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 2) (by rfl) rfl]; rw [stepInstr_aload, hl2]; dsimp only
        rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.getfield "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "metadata" "Ljava/lang/Object;") (by rfl) rfl]
        rw [(stepGetField_inProgress resolveProg depth sf 40 hi2).2.2.2]; dsimp only
        rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokestatic "kotlin/jvm/internal/Intrinsics" "areEqual" "(Ljava/lang/Object;Ljava/lang/Object;)Z") (by rfl) rfl]
        rw [stepInstr_areEqual (ha := hm1) (hb := hm2)]; dsimp only
        rw [runJvmRes_ifne_bool _ _ _ 42 45 (Jvm.JvmVal.beqVal beqUiExt m1 m2) _ _ _ _ (by rfl) (mkUiCommonHooks_isZero? _ _ _)]
        cases hmEq : Jvm.JvmVal.beqVal beqUiExt m1 m2 with
        | false =>
          refine ⟨⟨44, [.i32 0], locs2, jh, hp⟩, ?_, rfl, rfl⟩
          simp only [Bool.false_eq_true, ↓reduceIte, hcEq, hpEq, hprEq, hmEq, Bool.true_and, eqBool]
          rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.iconst 0) (by rfl) rfl]; rw [stepInstr_iconst]; dsimp only
          rw [Jvm.runJvmRes_nonbranch _ _ _ _ .ireturn (by rfl) rfl]; rw [stepInstr_ireturn]
        | true =>
          refine ⟨⟨46, [.i32 1], locs2, jh, hp⟩, ?_, rfl, rfl⟩
          simp only [↓reduceIte, hcEq, hpEq, hprEq, hmEq, Bool.true_and, eqBool]
          rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.iconst 1) (by rfl) rfl]; rw [stepInstr_iconst]; dsimp only
          rw [Jvm.runJvmRes_nonbranch _ _ _ _ .ireturn (by rfl) rfl]; rw [stepInstr_ireturn]

/-! ### `TargetStateKt` Helpers & Equivalence Theorems -/

private theorem stepInstr_checkNotNullParam_heapRef (hooks : Jvm.JvmHooks UiExt UiHeap)
    (pc addr : Nat) (msg : String) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    Jvm.stepInstr hooks
        (.invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter"
          "(Ljava/lang/Object;Ljava/lang/String;)V")
        ⟨pc, .str msg :: .heapRef addr :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, stk, locs, jh, hp⟩) := rfl

private theorem stepInstr_checkNotNullParam_ext (hooks : Jvm.JvmHooks UiExt UiHeap)
    (pc : Nat) (ext : UiExt) (msg : String) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    Jvm.stepInstr hooks
        (.invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter"
          "(Ljava/lang/Object;Ljava/lang/String;)V")
        ⟨pc, .str msg :: .ext ext :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, stk, locs, jh, hp⟩) := rfl

private theorem hasSingleFields_init_of_new (jh : Jvm.JvmHeap UiExt) (c : JvmVal) :
    let obj0 : Jvm.HeapObj UiExt := .instance "com/alexvanyo/composelife/ui/util/TargetState$Single" []
    let newAddr := jh.objects.size
    let jh0 := (jh.alloc obj0).2
    let jh1 := jh0.set newAddr (.instance "com/alexvanyo/composelife/ui/util/TargetState$Single" [("current", c)])
    HasSingleFields jh1 newAddr c := by
  intro obj0 newAddr jh0 jh1
  have hget0 : jh0.get? newAddr = some obj0 := Jvm.jvmHeap_get?_alloc_self jh obj0
  have hget1 : jh1.get? newAddr =
      some (.instance "com/alexvanyo/composelife/ui/util/TargetState$Single" [("current", c)]) :=
    Jvm.jvmHeap_get?_set_self hget0
  exact ⟨"com/alexvanyo/composelife/ui/util/TargetState$Single", [("current", c)], hget1, Or.inl rfl, rfl⟩

private theorem stepInstr_invokeSpecial_single_init_alloc (resolveProg : String → Option (List JvmInstr))
    (d sf pc addr : Nat) (arg : JvmVal) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap)
    (hget : jh.get? addr = some (.instance "com/alexvanyo/composelife/ui/util/TargetState$Single" [])) :
    Jvm.stepInstr (mkUiCommonHooks resolveProg d sf)
        (.invokespecial "com/alexvanyo/composelife/ui/util/TargetState$Single" "<init>" "(Ljava/lang/Object;)V")
        ⟨pc, arg :: .heapRef addr :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, stk, locs,
        jh.set addr (.instance "com/alexvanyo/composelife/ui/util/TargetState$Single" [("current", arg)]), hp⟩) := by
  unfold Jvm.stepInstr Jvm.stepInvokeSpecialGeneric
  dsimp only
  rw [mkUiCommonHooks_stepInvokeSpecial_single_init]
  rw [hget]
  simp [isUiCommonSubtypeOf, normalizeUiCommonClass]

private theorem stepInstr_invokeStatic_boolean_valueOf (resolveProg : String → Option (List JvmInstr))
    (d sf pc : Nat) (b : Bool) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    Jvm.stepInstr (mkUiCommonHooks resolveProg d sf)
        (.invokestatic "java/lang/Boolean" "valueOf" "(Z)Ljava/lang/Boolean;")
        ⟨pc, .i32 (if b then 1 else 0) :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .boxedBool b :: stk, locs, jh, hp⟩) := by
  unfold Jvm.stepInstr Jvm.stepInvokeStaticGeneric
  cases b <;> rfl

private theorem stepInstr_invokeVirtual_boolean_booleanValue (resolveProg : String → Option (List JvmInstr))
    (d sf pc : Nat) (b : Bool) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    Jvm.stepInstr (mkUiCommonHooks resolveProg d sf)
        (.invokevirtual "java/lang/Boolean" "booleanValue" "()Z")
        ⟨pc, .boxedBool b :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 (if b then 1 else 0) :: stk, locs, jh, hp⟩) := by
  unfold Jvm.stepInstr Jvm.stepInvokeVirtualGeneric
  dsimp only
  cases d <;> rfl

private theorem evalCheckCast_boolean (hooks : Jvm.JvmHooks UiExt UiHeap)
    (jh : Jvm.JvmHeap UiExt) (b : Bool)
    (hcc : hooks.checkCast = checkUiCast) :
    Jvm.evalCheckCast hooks jh "java/lang/Boolean" (.boxedBool b) = some (.boxedBool b) := by
  simp [Jvm.evalCheckCast, hcc, checkUiCast, normalizeUiCommonClass, Jvm.defaultCheckCast]
  cases b <;> decide

private theorem evalCheckCast_function1 (hooks : Jvm.JvmHooks UiExt UiHeap)
    (jh : Jvm.JvmHeap UiExt) (v : JvmVal)
    (hcc : hooks.checkCast = checkUiCast)
    (hfn : v = .ext .notLambda ∨ ∃ fid, v = .ext (.fn1Ref fid)) :
    Jvm.evalCheckCast hooks jh "kotlin/jvm/functions/Function1" v = some v := by
  rcases hfn with rfl | ⟨fid, rfl⟩ <;>
    simp [Jvm.evalCheckCast, hcc, checkUiCast, normalizeUiCommonClass]

private theorem stepInstr_getstatic_notLambda (resolveProg : String → Option (List JvmInstr))
    (d sf pc : Nat) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap UiExt) (hp : UiHeap)
    (hstat : jh.getStatic? "com/alexvanyo/composelife/ui/util/TargetStateKt$not$1" "INSTANCE" = none ∨
      jh.getStatic? "com/alexvanyo/composelife/ui/util/TargetStateKt$not$1" "INSTANCE" = some (.ext .notLambda)) :
    Jvm.stepInstr (mkUiCommonHooks resolveProg d sf)
        (.getstatic "com/alexvanyo/composelife/ui/util/TargetStateKt$not$1" "INSTANCE"
          "Lcom/alexvanyo/composelife/ui/util/TargetStateKt$not$1;")
        ⟨pc, stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .ext .notLambda :: stk, locs, jh, hp⟩) := by
  unfold Jvm.stepInstr
  dsimp only
  rcases hstat with hnone | hsome
  · rw [hnone, mkUiCommonHooks_resolveStatic]
    rfl
  · rw [hsome]

private theorem stepInstr_invokeVirtual_single_getCurrent (resolveProg : String → Option (List JvmInstr))
    (d sf pc : Nat) {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap UiExt} {hp : UiHeap}
    {addr : Nat} {c : JvmVal} (hs : HasSingleFields jh addr c) :
    Jvm.stepInstr (mkUiCommonHooks resolveProg d sf)
        (.invokevirtual "com/alexvanyo/composelife/ui/util/TargetState$Single" "getCurrent" "()Ljava/lang/Object;")
        ⟨pc, .heapRef addr :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, c :: stk, locs, jh, hp⟩) := by
  unfold Jvm.stepInstr
  exact stepInvokeVirtual_single_getCurrent resolveProg d sf pc hs

private theorem parseTags_obj_obj_bool :
    Jvm.parseMethodParamTags "(Lcom/alexvanyo/composelife/ui/util/TargetState;Lkotlin/jvm/functions/Function1;)Lcom/alexvanyo/composelife/ui/util/TargetState;" =
      ['L', 'L'] := by
  decide +kernel

private theorem assignParamLocals_L2 (a b : JvmVal) :
    assignParamLocalsAux 0 ['L', 'L'] [a, b] = [(0, a), (1, b)] := rfl

private theorem mkUiCommonHooks_stepInvokeVirtual_inProgress_getProvisional
    (r : String → Option (List JvmInstr)) (d sf pc addr : Nat)
    (stk : List JvmVal) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    Jvm.stepInvokeVirtualGeneric (mkUiCommonHooks r (d + 1) sf)
        ⟨pc, .heapRef addr :: stk, locs, jh, hp⟩
        "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "getProvisional" "()Ljava/lang/Object;" =
      match r "TargetState$InProgress.getProvisional" with
      | some prog =>
        match Jvm.runJvmRes (mkUiCommonHooks r d sf) sf prog
            (initUiJvmState [(0, .heapRef addr)] hp jh) with
        | some (res, endSt) => .inl (some ⟨pc + 1, res :: stk, locs, endSt.jvmHeap, endSt.heap⟩)
        | none => .inr none
      | none => .inr none := by
  rw [show Jvm.stepInvokeVirtualGeneric (mkUiCommonHooks r (d + 1) sf)
        ⟨pc, .heapRef addr :: stk, locs, jh, hp⟩
        "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "getProvisional" "()Ljava/lang/Object;" =
      match (match r "TargetState$InProgress.getProvisional" with
        | some prog =>
          match Jvm.runJvmRes (mkUiCommonHooks r d sf) sf prog
              { pc := 0, stack := [],
                locals := (assignParamLocalsAux 0
                  (Jvm.parseMethodParamTags "(Ljava/lang/Object;)Ljava/lang/Object;")
                  [.heapRef addr]).foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal)),
                jvmHeap := jh, heap := hp } with
          | some (res, endSt) => some (res, (⟨pc, .heapRef addr :: stk, locs, endSt.jvmHeap, endSt.heap⟩ : JvmState))
          | none => none
        | none => none) with
      | some (res, st') => Sum.inl (some { st' with pc := pc + 1, stack := res :: stk })
      | none => Sum.inr none from rfl]
  rw [parseTags_obj_obj, assignParamLocals_L1]
  cases r "TargetState$InProgress.getProvisional" with
  | none => rfl
  | some prog =>
    dsimp only [initUiJvmState, Jvm.initJvmState] at *
    cases Jvm.runJvmRes (mkUiCommonHooks r d sf) sf prog
        { pc := 0, stack := [],
          locals := List.foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal)) [(0, .heapRef addr)],
          jvmHeap := jh, heap := hp } <;> rfl

private theorem mkUiCommonHooks_stepInvokeVirtual_inProgress_getProgress
    (r : String → Option (List JvmInstr)) (d sf pc addr : Nat)
    (stk : List JvmVal) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    Jvm.stepInvokeVirtualGeneric (mkUiCommonHooks r (d + 1) sf)
        ⟨pc, .heapRef addr :: stk, locs, jh, hp⟩
        "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "getProgress" "()F" =
      match r "TargetState$InProgress.getProgress" with
      | some prog =>
        match Jvm.runJvmRes (mkUiCommonHooks r d sf) sf prog
            (initUiJvmState [(0, .heapRef addr)] hp jh) with
        | some (res, endSt) => .inl (some ⟨pc + 1, res :: stk, locs, endSt.jvmHeap, endSt.heap⟩)
        | none => .inr none
      | none => .inr none := by
  rw [show Jvm.stepInvokeVirtualGeneric (mkUiCommonHooks r (d + 1) sf)
        ⟨pc, .heapRef addr :: stk, locs, jh, hp⟩
        "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "getProgress" "()F" =
      match (match r "TargetState$InProgress.getProgress" with
        | some prog =>
          match Jvm.runJvmRes (mkUiCommonHooks r d sf) sf prog
              { pc := 0, stack := [],
                locals := (assignParamLocalsAux 0
                  (Jvm.parseMethodParamTags "(Ljava/lang/Object;)F")
                  [.heapRef addr]).foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal)),
                jvmHeap := jh, heap := hp } with
          | some (res, endSt) => some (res, (⟨pc, .heapRef addr :: stk, locs, endSt.jvmHeap, endSt.heap⟩ : JvmState))
          | none => none
        | none => none) with
      | some (res, st') => Sum.inl (some { st' with pc := pc + 1, stack := res :: stk })
      | none => Sum.inr none from rfl]
  rw [show Jvm.parseMethodParamTags "(Ljava/lang/Object;)F" = ['L'] from by decide, assignParamLocals_L1]
  cases r "TargetState$InProgress.getProgress" with
  | none => rfl
  | some prog =>
    dsimp only [initUiJvmState, Jvm.initJvmState] at *
    cases Jvm.runJvmRes (mkUiCommonHooks r d sf) sf prog
        { pc := 0, stack := [],
          locals := List.foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal)) [(0, .heapRef addr)],
          jvmHeap := jh, heap := hp } <;> rfl

private theorem mkUiCommonHooks_stepInvokeVirtual_inProgress_getMetadata
    (r : String → Option (List JvmInstr)) (d sf pc addr : Nat)
    (stk : List JvmVal) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    Jvm.stepInvokeVirtualGeneric (mkUiCommonHooks r (d + 1) sf)
        ⟨pc, .heapRef addr :: stk, locs, jh, hp⟩
        "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "getMetadata" "()Ljava/lang/Object;" =
      match r "TargetState$InProgress.getMetadata" with
      | some prog =>
        match Jvm.runJvmRes (mkUiCommonHooks r d sf) sf prog
            (initUiJvmState [(0, .heapRef addr)] hp jh) with
        | some (res, endSt) => .inl (some ⟨pc + 1, res :: stk, locs, endSt.jvmHeap, endSt.heap⟩)
        | none => .inr none
      | none => .inr none := by
  rw [show Jvm.stepInvokeVirtualGeneric (mkUiCommonHooks r (d + 1) sf)
        ⟨pc, .heapRef addr :: stk, locs, jh, hp⟩
        "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "getMetadata" "()Ljava/lang/Object;" =
      match (match r "TargetState$InProgress.getMetadata" with
        | some prog =>
          match Jvm.runJvmRes (mkUiCommonHooks r d sf) sf prog
              { pc := 0, stack := [],
                locals := (assignParamLocalsAux 0
                  (Jvm.parseMethodParamTags "(Ljava/lang/Object;)Ljava/lang/Object;")
                  [.heapRef addr]).foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal)),
                jvmHeap := jh, heap := hp } with
          | some (res, endSt) => some (res, (⟨pc, .heapRef addr :: stk, locs, endSt.jvmHeap, endSt.heap⟩ : JvmState))
          | none => none
        | none => none) with
      | some (res, st') => Sum.inl (some { st' with pc := pc + 1, stack := res :: stk })
      | none => Sum.inr none from rfl]
  rw [parseTags_obj_obj, assignParamLocals_L1]
  cases r "TargetState$InProgress.getMetadata" with
  | none => rfl
  | some prog =>
    dsimp only [initUiJvmState, Jvm.initJvmState] at *
    cases Jvm.runJvmRes (mkUiCommonHooks r d sf) sf prog
        { pc := 0, stack := [],
          locals := List.foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal)) [(0, .heapRef addr)],
          jvmHeap := jh, heap := hp } <;> rfl

private theorem mkUiCommonHooks_stepInvokeVirtual_inProgress_getCurrent_full
    (r : String → Option (List JvmInstr)) (d sf pc addr : Nat)
    (stk : List JvmVal) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    Jvm.stepInvokeVirtualGeneric (mkUiCommonHooks r (d + 1) sf)
        ⟨pc, .heapRef addr :: stk, locs, jh, hp⟩
        "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "getCurrent" "()Ljava/lang/Object;" =
      match r "TargetState$InProgress.getCurrent" with
      | some prog =>
        match Jvm.runJvmRes (mkUiCommonHooks r d sf) sf prog
            (initUiJvmState [(0, .heapRef addr)] hp jh) with
        | some (res, endSt) => .inl (some ⟨pc + 1, res :: stk, locs, endSt.jvmHeap, endSt.heap⟩)
        | none => .inr none
      | none => .inr none := by
  exact mkUiCommonHooks_stepInvokeVirtual_inProgress_getCurrent r d sf pc addr stk locs jh hp

private theorem stepInstr_invokeVirtual_inProgress_getCurrent_fq (resolveProg : String → Option (List JvmInstr))
    (d sf pc : Nat) (hext : ExtendsUiProgs resolveProg) (hsf : 5 ≤ sf)
    {jh : Jvm.JvmHeap UiExt} {addr : Nat} {c p : JvmVal} {pr : Float32} {m : JvmVal}
    (hi : HasInProgressFields jh addr c p pr m)
    (stk : List JvmVal) (locs : Nat → JvmVal) (hp : UiHeap) :
    Jvm.stepInstr (mkUiCommonHooks resolveProg (d + 1) sf)
        (.invokevirtual "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "getCurrent" "()Ljava/lang/Object;")
        ⟨pc, .heapRef addr :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, c :: stk, locs, jh, hp⟩) := by
  have hprog := hext "TargetState$InProgress.getCurrent" TargetState_InProgress_getCurrent_prog rfl
  rcases getCurrent_equiv resolveProg d sf sf hsf hi hp with ⟨stCur, hcurRun, hcurJh, hcurHp⟩
  unfold Jvm.stepInstr
  dsimp only
  change Jvm.stepInvokeVirtualGeneric (mkUiCommonHooks resolveProg (d + 1) sf)
      ⟨pc, .heapRef addr :: stk, locs, jh, hp⟩
      "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "getCurrent" "()Ljava/lang/Object;" = _
  rw [mkUiCommonHooks_stepInvokeVirtual_inProgress_getCurrent_full, hprog]
  dsimp only
  rw [hcurRun]
  change Sum.inl (some ({ pc := pc + 1, stack := c :: stk, locals := locs, jvmHeap := stCur.jvmHeap, heap := stCur.heap } : JvmState)) = _
  rw [hcurJh, hcurHp]

private theorem stepInstr_invokeVirtual_inProgress_getProvisional (resolveProg : String → Option (List JvmInstr))
    (d sf pc : Nat) (hext : ExtendsUiProgs resolveProg) (hsf : 5 ≤ sf)
    {jh : Jvm.JvmHeap UiExt} {addr : Nat} {c p : JvmVal} {pr : Float32} {m : JvmVal}
    (hi : HasInProgressFields jh addr c p pr m)
    (stk : List JvmVal) (locs : Nat → JvmVal) (hp : UiHeap) :
    Jvm.stepInstr (mkUiCommonHooks resolveProg (d + 1) sf)
        (.invokevirtual "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "getProvisional" "()Ljava/lang/Object;")
        ⟨pc, .heapRef addr :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, p :: stk, locs, jh, hp⟩) := by
  have hprog := hext "TargetState$InProgress.getProvisional" TargetState_InProgress_getProvisional_prog rfl
  rcases getProvisional_equiv resolveProg d sf sf hsf hi hp with ⟨stCur, hcurRun, hcurJh, hcurHp⟩
  unfold Jvm.stepInstr
  dsimp only
  change Jvm.stepInvokeVirtualGeneric (mkUiCommonHooks resolveProg (d + 1) sf)
      ⟨pc, .heapRef addr :: stk, locs, jh, hp⟩
      "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "getProvisional" "()Ljava/lang/Object;" = _
  rw [mkUiCommonHooks_stepInvokeVirtual_inProgress_getProvisional, hprog]
  dsimp only
  rw [hcurRun]
  change Sum.inl (some ({ pc := pc + 1, stack := p :: stk, locals := locs, jvmHeap := stCur.jvmHeap, heap := stCur.heap } : JvmState)) = _
  rw [hcurJh, hcurHp]

private theorem stepInstr_invokeVirtual_inProgress_getProgress (resolveProg : String → Option (List JvmInstr))
    (d sf pc : Nat) (hext : ExtendsUiProgs resolveProg) (hsf : 5 ≤ sf)
    {jh : Jvm.JvmHeap UiExt} {addr : Nat} {c p : JvmVal} {pr : Float32} {m : JvmVal}
    (hi : HasInProgressFields jh addr c p pr m)
    (stk : List JvmVal) (locs : Nat → JvmVal) (hp : UiHeap) :
    Jvm.stepInstr (mkUiCommonHooks resolveProg (d + 1) sf)
        (.invokevirtual "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "getProgress" "()F")
        ⟨pc, .heapRef addr :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .f32 pr :: stk, locs, jh, hp⟩) := by
  have hprog := hext "TargetState$InProgress.getProgress" TargetState_InProgress_getProgress_prog rfl
  rcases getProgress_equiv resolveProg d sf sf hsf hi hp with ⟨stCur, hcurRun, hcurJh, hcurHp⟩
  unfold Jvm.stepInstr
  dsimp only
  change Jvm.stepInvokeVirtualGeneric (mkUiCommonHooks resolveProg (d + 1) sf)
      ⟨pc, .heapRef addr :: stk, locs, jh, hp⟩
      "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "getProgress" "()F" = _
  rw [mkUiCommonHooks_stepInvokeVirtual_inProgress_getProgress, hprog]
  dsimp only
  rw [hcurRun]
  change Sum.inl (some ({ pc := pc + 1, stack := .f32 pr :: stk, locals := locs, jvmHeap := stCur.jvmHeap, heap := stCur.heap } : JvmState)) = _
  rw [hcurJh, hcurHp]

private theorem stepInstr_invokeVirtual_inProgress_getMetadata (resolveProg : String → Option (List JvmInstr))
    (d sf pc : Nat) (hext : ExtendsUiProgs resolveProg) (hsf : 5 ≤ sf)
    {jh : Jvm.JvmHeap UiExt} {addr : Nat} {c p : JvmVal} {pr : Float32} {m : JvmVal}
    (hi : HasInProgressFields jh addr c p pr m)
    (stk : List JvmVal) (locs : Nat → JvmVal) (hp : UiHeap) :
    Jvm.stepInstr (mkUiCommonHooks resolveProg (d + 1) sf)
        (.invokevirtual "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "getMetadata" "()Ljava/lang/Object;")
        ⟨pc, .heapRef addr :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, m :: stk, locs, jh, hp⟩) := by
  have hprog := hext "TargetState$InProgress.getMetadata" TargetState_InProgress_getMetadata_prog rfl
  rcases getMetadata_equiv resolveProg d sf sf hsf hi hp with ⟨stCur, hcurRun, hcurJh, hcurHp⟩
  unfold Jvm.stepInstr
  dsimp only
  change Jvm.stepInvokeVirtualGeneric (mkUiCommonHooks resolveProg (d + 1) sf)
      ⟨pc, .heapRef addr :: stk, locs, jh, hp⟩
      "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "getMetadata" "()Ljava/lang/Object;" = _
  rw [mkUiCommonHooks_stepInvokeVirtual_inProgress_getMetadata, hprog]
  dsimp only
  rw [hcurRun]
  change Sum.inl (some ({ pc := pc + 1, stack := m :: stk, locals := locs, jvmHeap := stCur.jvmHeap, heap := stCur.heap } : JvmState)) = _
  rw [hcurJh, hcurHp]

private theorem mkUiCommonHooks_stepInvokeSpecial_inProgress_init_fq
    (r : String → Option (List JvmInstr)) (d sf pc addr : Nat)
    (c p : JvmVal) (pr : Float32) (m : JvmVal)
    (stk : List JvmVal) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    Jvm.stepInstr (mkUiCommonHooks r (d + 1) sf)
        (.invokespecial "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "<init>" "(Ljava/lang/Object;Ljava/lang/Object;FLjava/lang/Object;)V")
        ⟨pc, m :: .f32 pr :: p :: c :: .heapRef addr :: stk, locs, jh, hp⟩ =
      match r "TargetState$InProgress.<init>" with
      | some prog =>
        match Jvm.runJvmRes (mkUiCommonHooks r d sf) sf prog
            (initUiJvmState [(0, .heapRef addr), (1, c), (2, p), (3, .f32 pr), (4, m)] hp jh) with
        | some (_, endSt) => .inl (some ⟨pc + 1, stk, locs, endSt.jvmHeap, endSt.heap⟩)
        | none => .inr none
      | none => .inr none := by
  exact mkUiCommonHooks_stepInvokeSpecial_inProgress_init r d sf pc addr c p pr m stk locs jh hp

def HasFn1Behavior (hp : UiHeap) (fnVal : JvmVal) (f : JvmVal → Option JvmVal) : Prop :=
  match fnVal with
  | .ext .notLambda => ∀ v, f v = match v with | .boxedBool b => some (.boxedBool (!b)) | _ => none
  | .ext (.fn1Ref fid) => hp.fn1s[fid]? = some f
  | _ => False

private theorem stepInstr_invokeInterface_fn1 (resolveProg : String → Option (List JvmInstr))
    (d sf pc : Nat) (fnVal arg res : JvmVal) (f : JvmVal → Option JvmVal)
    (stk : List JvmVal) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap UiExt) (hp : UiHeap)
    (hfn : HasFn1Behavior hp fnVal f) (hfarg : f arg = some res) :
    Jvm.stepInstr (mkUiCommonHooks resolveProg d sf)
        (.invokeinterface "kotlin/jvm/functions/Function1" "invoke" "(Ljava/lang/Object;)Ljava/lang/Object;")
        ⟨pc, arg :: fnVal :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, res :: stk, locs, jh, hp⟩) := by
  cases fnVal with
  | ext ext =>
    cases ext with
    | notLambda =>
      have hEq := hfn arg
      rw [hfarg] at hEq
      cases arg with
      | boxedBool b =>
        have hb : res = .boxedBool (!b) := by simpa using hEq
        subst hb
        unfold Jvm.stepInstr Jvm.stepInvokeInterfaceGeneric
        dsimp only
        rw [show (mkUiCommonHooks resolveProg d sf).stepInvokeInterface
              ⟨pc, .boxedBool b :: .ext .notLambda :: stk, locs, jh, hp⟩
              "kotlin/jvm/functions/Function1" "invoke" "(Ljava/lang/Object;)Ljava/lang/Object;" =
            .inl (some ⟨pc + 1, .boxedBool (!b) :: stk, locs, jh, hp⟩) by cases d <;> rfl]
        rfl
      | _ => simp at hEq
    | fn1Ref fid =>
      have hfid : hp.fn1s[fid]? = some f := hfn
      unfold Jvm.stepInstr Jvm.stepInvokeInterfaceGeneric
      dsimp only
      rw [show (mkUiCommonHooks resolveProg d sf).stepInvokeInterface
            ⟨pc, arg :: .ext (.fn1Ref fid) :: stk, locs, jh, hp⟩
            "kotlin/jvm/functions/Function1" "invoke" "(Ljava/lang/Object;)Ljava/lang/Object;" =
          .inl (some ⟨pc + 1, res :: stk, locs, jh, hp⟩) by
        cases d <;> dsimp [mkUiCommonHooks] <;> simp [hfid, hfarg]]
      rfl
    | _ => simp [HasFn1Behavior] at hfn
  | _ => simp [HasFn1Behavior] at hfn

theorem isInProgress_single_equiv (resolveProg : String → Option (List JvmInstr))
    (depth sf fuel : Nat) (hf : 11 ≤ fuel)
    {jh : Jvm.JvmHeap UiExt} {addr : Nat} {c : JvmVal}
    (hs : HasSingleFields jh addr c) (hp : UiHeap) :
    ∃ st',
      Jvm.runJvmRes (mkUiCommonHooks resolveProg depth sf) fuel
          TargetStateKt_isInProgress_prog (initUiJvmState [(0, .heapRef addr)] hp jh) =
        some (.i32 0, st') ∧
      TargetState.isInProgress (.single c : TargetState JvmVal Unit) = false ∧
      st'.jvmHeap = jh ∧ st'.heap = hp := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  have hlocs : (List.foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal))
      [(0, Jvm.JvmVal.heapRef addr)]) 0 = .heapRef addr := rfl
  let locs1 := setLocal (List.foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal))
      [(0, Jvm.JvmVal.heapRef addr)]) 1 (.heapRef addr)
  refine ⟨⟨19, [.i32 0], locs1, jh, hp⟩, ?_, rfl, rfl, rfl⟩
  dsimp only [initUiJvmState, Jvm.initJvmState]
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, hlocs]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.ldcStr "<this>") (by rfl) rfl]; rw [stepInstr_ldcStr]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter" "(Ljava/lang/Object;Ljava/lang/String;)V") (by rfl) rfl]
  rw [stepInstr_checkNotNullParam_heapRef]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, hlocs]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.astore 1) (by rfl) rfl]; rw [stepInstr_astore]; dsimp only
  have h1 : setLocal (List.foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal))
      [(0, Jvm.JvmVal.heapRef addr)]) 1 (.heapRef addr) 1 = .heapRef addr := rfl
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 1) (by rfl) rfl]; rw [stepInstr_aload, h1]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.instanceof "com/alexvanyo/composelife/ui/util/TargetState$Single") (by rfl) rfl]
  rw [stepInstr_instanceof_val]
  simp only [Jvm.evalInstanceOf, checkInstanceOf_single resolveProg depth sf hs, ↓reduceIte]
  rw [runJvmRes_ifeq_i32 _ _ _ 7 10 1 _ _ _ _ (by rfl) (mkUiCommonHooks_isZero? _ _ _)]
  simp only [show ((1 : UInt32) == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.iconst 0) (by rfl) rfl]; rw [stepInstr_iconst]; dsimp only
  rw [runJvmRes_goto _ _ _ _ 19 (by rfl)]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ .ireturn (by rfl) rfl]; rw [stepInstr_ireturn]

theorem isInProgress_inProgress_equiv (resolveProg : String → Option (List JvmInstr))
    (depth sf fuel : Nat) (hf : 14 ≤ fuel)
    {jh : Jvm.JvmHeap UiExt} {addr : Nat} {c p : JvmVal} {pr : Float32} {m : JvmVal}
    (hi : HasInProgressFields jh addr c p pr m) (hp : UiHeap) :
    ∃ st',
      Jvm.runJvmRes (mkUiCommonHooks resolveProg depth sf) fuel
          TargetStateKt_isInProgress_prog (initUiJvmState [(0, .heapRef addr)] hp jh) =
        some (.i32 1, st') ∧
      TargetState.isInProgress (.inProgress c p pr m : TargetState JvmVal JvmVal) = true ∧
      st'.jvmHeap = jh ∧ st'.heap = hp := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  have hlocs : (List.foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal))
      [(0, Jvm.JvmVal.heapRef addr)]) 0 = .heapRef addr := rfl
  let locs1 := setLocal (List.foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal))
      [(0, Jvm.JvmVal.heapRef addr)]) 1 (.heapRef addr)
  refine ⟨⟨19, [.i32 1], locs1, jh, hp⟩, ?_, rfl, rfl, rfl⟩
  dsimp only [initUiJvmState, Jvm.initJvmState]
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, hlocs]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.ldcStr "<this>") (by rfl) rfl]; rw [stepInstr_ldcStr]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter" "(Ljava/lang/Object;Ljava/lang/String;)V") (by rfl) rfl]
  rw [stepInstr_checkNotNullParam_heapRef]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, hlocs]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.astore 1) (by rfl) rfl]; rw [stepInstr_astore]; dsimp only
  have h1 : setLocal (List.foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal))
      [(0, Jvm.JvmVal.heapRef addr)]) 1 (.heapRef addr) 1 = .heapRef addr := rfl
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 1) (by rfl) rfl]; rw [stepInstr_aload, h1]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.instanceof "com/alexvanyo/composelife/ui/util/TargetState$Single") (by rfl) rfl]
  rw [stepInstr_instanceof_val]
  simp only [Jvm.evalInstanceOf, checkInstanceOf_inProgress_not_single resolveProg depth sf hi,
    Bool.false_eq_true, ↓reduceIte]
  rw [runJvmRes_ifeq_i32 _ _ _ 7 10 0 _ _ _ _ (by rfl) (mkUiCommonHooks_isZero? _ _ _)]
  simp only [show ((0 : UInt32) == 0) = true from rfl, ↓reduceIte]
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 1) (by rfl) rfl]; rw [stepInstr_aload, h1]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.instanceof "com/alexvanyo/composelife/ui/util/TargetState$InProgress") (by rfl) rfl]
  rw [stepInstr_instanceof_val]
  simp only [Jvm.evalInstanceOf, checkInstanceOf_inProgress resolveProg depth sf hi, ↓reduceIte]
  rw [runJvmRes_ifeq_i32 _ _ _ 12 15 1 _ _ _ _ (by rfl) (mkUiCommonHooks_isZero? _ _ _)]
  simp only [show ((1 : UInt32) == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.iconst 1) (by rfl) rfl]; rw [stepInstr_iconst]; dsimp only
  rw [runJvmRes_goto _ _ _ _ 19 (by rfl)]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ .ireturn (by rfl) rfl]; rw [stepInstr_ireturn]

theorem getProgressToTrue_inProgress_equiv (resolveProg : String → Option (List JvmInstr))
    (d sf fuel : Nat) (hext : ExtendsUiProgs resolveProg) (hsf : 5 ≤ sf) (hf : 21 ≤ fuel)
    {jh : Jvm.JvmHeap UiExt} {addr : Nat} {c : JvmVal} {cb pb : Bool} {pr : Float32} {m : JvmVal}
    (hi : HasInProgressFields jh addr c (.boxedBool pb) pr m) (hp : UiHeap) :
    let expected := TargetState.progressToTrue (.inProgress cb pb pr () : TargetState Bool Unit)
    ∃ st',
      Jvm.runJvmRes (mkUiCommonHooks resolveProg (d + 1) sf) fuel
          TargetStateKt_getProgressToTrue_prog (initUiJvmState [(0, .heapRef addr)] hp jh) =
        some (.f32 expected, st') ∧
      st'.jvmHeap = jh ∧ st'.heap = hp := by
  intro expected
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  have h0 : (List.foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal))
      [(0, Jvm.JvmVal.heapRef addr)]) 0 = .heapRef addr := rfl
  have hl0 : setLocal (List.foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal))
      [(0, Jvm.JvmVal.heapRef addr)]) 1 (.heapRef addr) 0 = .heapRef addr := rfl
  have hl1 : setLocal (List.foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal))
      [(0, Jvm.JvmVal.heapRef addr)]) 1 (.heapRef addr) 1 = .heapRef addr := rfl
  let locs1 := setLocal (List.foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal))
      [(0, Jvm.JvmVal.heapRef addr)]) 1 (.heapRef addr)
  dsimp only [initUiJvmState, Jvm.initJvmState]
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, h0]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.ldcStr "<this>") (by rfl) rfl]; rw [stepInstr_ldcStr]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter" "(Ljava/lang/Object;Ljava/lang/String;)V") (by rfl) rfl]
  rw [stepInstr_checkNotNullParam_heapRef]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, h0]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.astore 1) (by rfl) rfl]; rw [stepInstr_astore]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 1) (by rfl) rfl]; rw [stepInstr_aload, hl1]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.instanceof "com/alexvanyo/composelife/ui/util/TargetState$InProgress") (by rfl) rfl]
  rw [stepInstr_instanceof_val]
  simp only [Jvm.evalInstanceOf, checkInstanceOf_inProgress resolveProg (d + 1) sf hi, ↓reduceIte]
  rw [runJvmRes_ifeq_i32 _ _ _ 7 24 1 _ _ _ _ (by rfl) (mkUiCommonHooks_isZero? _ _ _)]
  simp only [show ((1 : UInt32) == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, hl0]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.checkcast "com/alexvanyo/composelife/ui/util/TargetState$InProgress") (by rfl) rfl]
  rw [stepInstr_checkcast_some _ _ _ _ _ _ _ _ _ (evalCheckCast_inProgress resolveProg (d + 1) sf hi)]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokevirtual "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "getProvisional" "()Ljava/lang/Object;") (by rfl) rfl]
  rw [stepInstr_invokeVirtual_inProgress_getProvisional resolveProg d sf 10 hext hsf hi]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.checkcast "java/lang/Boolean") (by rfl) rfl]
  rw [stepInstr_checkcast_some _ _ _ _ _ _ _ _ _
    (evalCheckCast_boolean (mkUiCommonHooks resolveProg (d + 1) sf) jh pb (mkUiCommonHooks_checkCast _ _ _))]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokevirtual "java/lang/Boolean" "booleanValue" "()Z") (by rfl) rfl]
  rw [stepInstr_invokeVirtual_boolean_booleanValue]; dsimp only
  cases pb with
  | true =>
    refine ⟨⟨41, [.f32 pr], locs1, jh, hp⟩, ?_, rfl, rfl⟩
    simp only [↓reduceIte, expected, TargetState.progressToTrue]
    rw [runJvmRes_ifeq_i32 _ _ _ 13 18 1 _ _ _ _ (by rfl) (mkUiCommonHooks_isZero? _ _ _)]
    simp only [show ((1 : UInt32) == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, hl0]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.checkcast "com/alexvanyo/composelife/ui/util/TargetState$InProgress") (by rfl) rfl]
    rw [stepInstr_checkcast_some _ _ _ _ _ _ _ _ _ (evalCheckCast_inProgress resolveProg (d + 1) sf hi)]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokevirtual "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "getProgress" "()F") (by rfl) rfl]
    rw [stepInstr_invokeVirtual_inProgress_getProgress resolveProg d sf 16 hext hsf hi]; dsimp only
    rw [runJvmRes_goto _ _ _ _ 41 (by rfl)]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ .freturn (by rfl) rfl]; rw [stepInstr_freturn]
  | false =>
    refine ⟨⟨41, [.f32 (Float32.ofBits 1065353216 - pr)], locs1, jh, hp⟩, ?_, rfl, rfl⟩
    simp only [Bool.false_eq_true, ↓reduceIte, expected, TargetState.progressToTrue,
      show (1.0 : Float32) = Float32.ofBits 1065353216 from by decide]
    rw [runJvmRes_ifeq_i32 _ _ _ 13 18 0 _ _ _ _ (by rfl) (mkUiCommonHooks_isZero? _ _ _)]
    simp only [show ((0 : UInt32) == 0) = true from rfl, ↓reduceIte]
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.fconst 1065353216) (by rfl) rfl]; rw [stepInstr_fconst]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, hl0]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.checkcast "com/alexvanyo/composelife/ui/util/TargetState$InProgress") (by rfl) rfl]
    rw [stepInstr_checkcast_some _ _ _ _ _ _ _ _ _ (evalCheckCast_inProgress resolveProg (d + 1) sf hi)]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokevirtual "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "getProgress" "()F") (by rfl) rfl]
    rw [stepInstr_invokeVirtual_inProgress_getProgress resolveProg d sf 21 hext hsf hi]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ .fsub (by rfl) rfl]; rw [stepInstr_fsub_f32]; dsimp only
    rw [runJvmRes_goto _ _ _ _ 41 (by rfl)]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ .freturn (by rfl) rfl]; rw [stepInstr_freturn]

theorem getProgressToTrue_single_equiv (resolveProg : String → Option (List JvmInstr))
    (depth sf fuel : Nat) (hf : 20 ≤ fuel)
    {jh : Jvm.JvmHeap UiExt} {addr : Nat} {cb : Bool}
    (hs : HasSingleFields jh addr (.boxedBool cb)) (hp : UiHeap) :
    let expected := TargetState.progressToTrue (.single cb : TargetState Bool Unit)
    ∃ st',
      Jvm.runJvmRes (mkUiCommonHooks resolveProg depth sf) fuel
          TargetStateKt_getProgressToTrue_prog (initUiJvmState [(0, .heapRef addr)] hp jh) =
        some (.f32 expected, st') ∧
      st'.jvmHeap = jh ∧ st'.heap = hp := by
  intro expected
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  have h0 : (List.foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal))
      [(0, Jvm.JvmVal.heapRef addr)]) 0 = .heapRef addr := rfl
  have hl0 : setLocal (List.foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal))
      [(0, Jvm.JvmVal.heapRef addr)]) 1 (.heapRef addr) 0 = .heapRef addr := rfl
  have hl1 : setLocal (List.foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal))
      [(0, Jvm.JvmVal.heapRef addr)]) 1 (.heapRef addr) 1 = .heapRef addr := rfl
  let locs1 := setLocal (List.foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal))
      [(0, Jvm.JvmVal.heapRef addr)]) 1 (.heapRef addr)
  dsimp only [initUiJvmState, Jvm.initJvmState]
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, h0]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.ldcStr "<this>") (by rfl) rfl]; rw [stepInstr_ldcStr]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter" "(Ljava/lang/Object;Ljava/lang/String;)V") (by rfl) rfl]
  rw [stepInstr_checkNotNullParam_heapRef]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, h0]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.astore 1) (by rfl) rfl]; rw [stepInstr_astore]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 1) (by rfl) rfl]; rw [stepInstr_aload, hl1]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.instanceof "com/alexvanyo/composelife/ui/util/TargetState$InProgress") (by rfl) rfl]
  rw [stepInstr_instanceof_val]
  simp only [Jvm.evalInstanceOf, checkInstanceOf_single_not_inProgress resolveProg depth sf hs,
    Bool.false_eq_true, ↓reduceIte]
  rw [runJvmRes_ifeq_i32 _ _ _ 7 24 0 _ _ _ _ (by rfl) (mkUiCommonHooks_isZero? _ _ _)]
  simp only [show ((0 : UInt32) == 0) = true from rfl, ↓reduceIte]
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 1) (by rfl) rfl]; rw [stepInstr_aload, hl1]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.instanceof "com/alexvanyo/composelife/ui/util/TargetState$Single") (by rfl) rfl]
  rw [stepInstr_instanceof_val]
  simp only [Jvm.evalInstanceOf, checkInstanceOf_single resolveProg depth sf hs, ↓reduceIte]
  rw [runJvmRes_ifeq_i32 _ _ _ 26 37 1 _ _ _ _ (by rfl) (mkUiCommonHooks_isZero? _ _ _)]
  simp only [show ((1 : UInt32) == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, hl0]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.checkcast "com/alexvanyo/composelife/ui/util/TargetState$Single") (by rfl) rfl]
  rw [stepInstr_checkcast_some _ _ _ _ _ _ _ _ _ (evalCheckCast_single resolveProg depth sf hs)]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokevirtual "com/alexvanyo/composelife/ui/util/TargetState$Single" "getCurrent" "()Ljava/lang/Object;") (by rfl) rfl]
  rw [stepInstr_invokeVirtual_single_getCurrent resolveProg depth sf 29 hs]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.checkcast "java/lang/Boolean") (by rfl) rfl]
  rw [stepInstr_checkcast_some _ _ _ _ _ _ _ _ _
    (evalCheckCast_boolean (mkUiCommonHooks resolveProg depth sf) jh cb (mkUiCommonHooks_checkCast _ _ _))]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokevirtual "java/lang/Boolean" "booleanValue" "()Z") (by rfl) rfl]
  rw [stepInstr_invokeVirtual_boolean_booleanValue]; dsimp only
  cases cb with
  | true =>
    refine ⟨⟨41, [.f32 (Float32.ofBits 1065353216)], locs1, jh, hp⟩, ?_, rfl, rfl⟩
    simp only [↓reduceIte, expected, TargetState.progressToTrue,
      show (1.0 : Float32) = Float32.ofBits 1065353216 from by decide]
    rw [runJvmRes_ifeq_i32 _ _ _ 32 35 1 _ _ _ _ (by rfl) (mkUiCommonHooks_isZero? _ _ _)]
    simp only [show ((1 : UInt32) == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.fconst 1065353216) (by rfl) rfl]; rw [stepInstr_fconst]; dsimp only
    rw [runJvmRes_goto _ _ _ _ 41 (by rfl)]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ .freturn (by rfl) rfl]; rw [stepInstr_freturn]
  | false =>
    refine ⟨⟨41, [.f32 (Float32.ofBits 0)], locs1, jh, hp⟩, ?_, rfl, rfl⟩
    simp only [Bool.false_eq_true, ↓reduceIte, expected, TargetState.progressToTrue,
      show (0.0 : Float32) = Float32.ofBits 0 from by decide]
    rw [runJvmRes_ifeq_i32 _ _ _ 32 35 0 _ _ _ _ (by rfl) (mkUiCommonHooks_isZero? _ _ _)]
    simp only [show ((0 : UInt32) == 0) = true from rfl, ↓reduceIte]
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.fconst 0) (by rfl) rfl]; rw [stepInstr_fconst]; dsimp only
    rw [runJvmRes_goto _ _ _ _ 41 (by rfl)]; dsimp only
    rw [Jvm.runJvmRes_nonbranch _ _ _ _ .freturn (by rfl) rfl]; rw [stepInstr_freturn]

theorem and_true_equiv (resolveProg : String → Option (List JvmInstr))
    (depth sf fuel : Nat) (hf : 9 ≤ fuel)
    (addr : Nat) (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    ∃ st',
      Jvm.runJvmRes (mkUiCommonHooks resolveProg depth sf) fuel
          TargetStateKt_and_prog (initUiJvmState [(0, .heapRef addr), (1, .bool true)] hp jh) =
        some (.heapRef addr, st') ∧
      st'.jvmHeap = jh ∧ st'.heap = hp := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  have h0 : (List.foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal))
      [(0, Jvm.JvmVal.heapRef addr), (1, .bool true)]) 0 = .heapRef addr := rfl
  have h1 : (List.foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal))
      [(0, Jvm.JvmVal.heapRef addr), (1, .bool true)]) 1 = .bool true := rfl
  refine ⟨⟨13, [.heapRef addr], (initUiJvmState [(0, .heapRef addr), (1, .bool true)] hp jh).locals, jh, hp⟩,
    ?_, rfl, rfl⟩
  dsimp only [initUiJvmState, Jvm.initJvmState]
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, h0]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.ldcStr "<this>") (by rfl) rfl]; rw [stepInstr_ldcStr]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter" "(Ljava/lang/Object;Ljava/lang/String;)V") (by rfl) rfl]
  rw [stepInstr_checkNotNullParam_heapRef]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.iload 1) (by rfl) rfl]; rw [stepInstr_iload, h1]; dsimp only
  rw [runJvmRes_ifeq_bool _ _ _ 4 7 true _ _ _ _ (by rfl) (mkUiCommonHooks_isZero? _ _ _)]
  simp only [↓reduceIte]
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, h0]; dsimp only
  rw [runJvmRes_goto _ _ _ _ 13 (by rfl)]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ .areturn (by rfl) rfl]; rw [stepInstr_areturn]

theorem and_false_equiv (resolveProg : String → Option (List JvmInstr))
    (depth sf fuel : Nat) (hf : 13 ≤ fuel)
    (addr : Nat) (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    ∃ st',
      Jvm.runJvmRes (mkUiCommonHooks resolveProg depth sf) fuel
          TargetStateKt_and_prog (initUiJvmState [(0, .heapRef addr), (1, .bool false)] hp jh) =
        some (.heapRef jh.objects.size, st') ∧
      HasSingleFields st'.jvmHeap jh.objects.size (.boxedBool false) ∧
      st'.heap = hp := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  have h0 : (List.foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal))
      [(0, Jvm.JvmVal.heapRef addr), (1, .bool false)]) 0 = .heapRef addr := rfl
  have h1 : (List.foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal))
      [(0, Jvm.JvmVal.heapRef addr), (1, .bool false)]) 1 = .bool false := rfl
  let obj0 : Jvm.HeapObj UiExt := .instance "com/alexvanyo/composelife/ui/util/TargetState$Single" []
  let newAddr := jh.objects.size
  let jh0 := (jh.alloc obj0).2
  let jh1 := jh0.set newAddr (.instance "com/alexvanyo/composelife/ui/util/TargetState$Single" [("current", .boxedBool false)])
  have hget0 : jh0.get? newAddr = some obj0 := Jvm.jvmHeap_get?_alloc_self jh obj0
  have hs1 : HasSingleFields jh1 newAddr (.boxedBool false) := hasSingleFields_init_of_new jh (.boxedBool false)
  refine ⟨⟨13, [.heapRef newAddr], (initUiJvmState [(0, .heapRef addr), (1, .bool false)] hp jh).locals, jh1, hp⟩,
    ?_, hs1, rfl⟩
  dsimp only [initUiJvmState, Jvm.initJvmState]
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, h0]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.ldcStr "<this>") (by rfl) rfl]; rw [stepInstr_ldcStr]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter" "(Ljava/lang/Object;Ljava/lang/String;)V") (by rfl) rfl]
  rw [stepInstr_checkNotNullParam_heapRef]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.iload 1) (by rfl) rfl]; rw [stepInstr_iload, h1]; dsimp only
  rw [runJvmRes_ifeq_bool _ _ _ 4 7 false _ _ _ _ (by rfl) (mkUiCommonHooks_isZero? _ _ _)]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.newClass "com/alexvanyo/composelife/ui/util/TargetState$Single") (by rfl) rfl]
  rw [stepInstr_newClass_single]; dsimp only
  change Jvm.runJvmRes (mkUiCommonHooks resolveProg depth sf) (k + 7) TargetStateKt_and_prog
      ⟨8, [.heapRef newAddr], _, jh0, hp⟩ = _
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ .dup (by rfl) rfl]; rw [stepInstr_dup]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.iconst 0) (by rfl) rfl]; rw [stepInstr_iconst]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokestatic "java/lang/Boolean" "valueOf" "(Z)Ljava/lang/Boolean;") (by rfl) rfl]
  rw [show (0 : UInt32) = (if false then 1 else 0) from rfl]
  rw [stepInstr_invokeStatic_boolean_valueOf resolveProg depth sf 10 false]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokespecial "com/alexvanyo/composelife/ui/util/TargetState$Single" "<init>" "(Ljava/lang/Object;)V") (by rfl) rfl]
  rw [stepInstr_invokeSpecial_single_init_alloc resolveProg depth sf 11 newAddr (.boxedBool false) _ _ jh0 hp hget0]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.checkcast "com/alexvanyo/composelife/ui/util/TargetState") (by rfl) rfl]
  rw [stepInstr_checkcast_some _ _ _ _ _ _ _ _ _ (evalCheckCast_targetState_of_single resolveProg depth sf hs1)]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ .areturn (by rfl) rfl]; rw [stepInstr_areturn]

theorem or_true_equiv (resolveProg : String → Option (List JvmInstr))
    (depth sf fuel : Nat) (hf : 14 ≤ fuel)
    (addr : Nat) (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    ∃ st',
      Jvm.runJvmRes (mkUiCommonHooks resolveProg depth sf) fuel
          TargetStateKt_or_prog (initUiJvmState [(0, .heapRef addr), (1, .bool true)] hp jh) =
        some (.heapRef jh.objects.size, st') ∧
      HasSingleFields st'.jvmHeap jh.objects.size (.boxedBool true) ∧
      st'.heap = hp := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  have h0 : (List.foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal))
      [(0, Jvm.JvmVal.heapRef addr), (1, .bool true)]) 0 = .heapRef addr := rfl
  have h1 : (List.foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal))
      [(0, Jvm.JvmVal.heapRef addr), (1, .bool true)]) 1 = .bool true := rfl
  let obj0 : Jvm.HeapObj UiExt := .instance "com/alexvanyo/composelife/ui/util/TargetState$Single" []
  let newAddr := jh.objects.size
  let jh0 := (jh.alloc obj0).2
  let jh1 := jh0.set newAddr (.instance "com/alexvanyo/composelife/ui/util/TargetState$Single" [("current", .boxedBool true)])
  have hget0 : jh0.get? newAddr = some obj0 := Jvm.jvmHeap_get?_alloc_self jh obj0
  have hs1 : HasSingleFields jh1 newAddr (.boxedBool true) := hasSingleFields_init_of_new jh (.boxedBool true)
  refine ⟨⟨13, [.heapRef newAddr], (initUiJvmState [(0, .heapRef addr), (1, .bool true)] hp jh).locals, jh1, hp⟩,
    ?_, hs1, rfl⟩
  dsimp only [initUiJvmState, Jvm.initJvmState]
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, h0]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.ldcStr "<this>") (by rfl) rfl]; rw [stepInstr_ldcStr]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter" "(Ljava/lang/Object;Ljava/lang/String;)V") (by rfl) rfl]
  rw [stepInstr_checkNotNullParam_heapRef]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.iload 1) (by rfl) rfl]; rw [stepInstr_iload, h1]; dsimp only
  rw [runJvmRes_ifeq_bool _ _ _ 4 12 true _ _ _ _ (by rfl) (mkUiCommonHooks_isZero? _ _ _)]
  simp only [↓reduceIte]
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.newClass "com/alexvanyo/composelife/ui/util/TargetState$Single") (by rfl) rfl]
  rw [stepInstr_newClass_single]; dsimp only
  change Jvm.runJvmRes (mkUiCommonHooks resolveProg depth sf) (k + 8) TargetStateKt_or_prog
      ⟨6, [.heapRef newAddr], _, jh0, hp⟩ = _
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ .dup (by rfl) rfl]; rw [stepInstr_dup]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.iconst 1) (by rfl) rfl]; rw [stepInstr_iconst]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokestatic "java/lang/Boolean" "valueOf" "(Z)Ljava/lang/Boolean;") (by rfl) rfl]
  rw [show (1 : UInt32) = (if true then 1 else 0) from rfl]
  rw [stepInstr_invokeStatic_boolean_valueOf resolveProg depth sf 8 true]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokespecial "com/alexvanyo/composelife/ui/util/TargetState$Single" "<init>" "(Ljava/lang/Object;)V") (by rfl) rfl]
  rw [stepInstr_invokeSpecial_single_init_alloc resolveProg depth sf 9 newAddr (.boxedBool true) _ _ jh0 hp hget0]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.checkcast "com/alexvanyo/composelife/ui/util/TargetState") (by rfl) rfl]
  rw [stepInstr_checkcast_some _ _ _ _ _ _ _ _ _ (evalCheckCast_targetState_of_single resolveProg depth sf hs1)]; dsimp only
  rw [runJvmRes_goto _ _ _ _ 13 (by rfl)]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ .areturn (by rfl) rfl]; rw [stepInstr_areturn]

theorem or_false_equiv (resolveProg : String → Option (List JvmInstr))
    (depth sf fuel : Nat) (hf : 8 ≤ fuel)
    (addr : Nat) (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    ∃ st',
      Jvm.runJvmRes (mkUiCommonHooks resolveProg depth sf) fuel
          TargetStateKt_or_prog (initUiJvmState [(0, .heapRef addr), (1, .bool false)] hp jh) =
        some (.heapRef addr, st') ∧
      st'.jvmHeap = jh ∧ st'.heap = hp := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  have h0 : (List.foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal))
      [(0, Jvm.JvmVal.heapRef addr), (1, .bool false)]) 0 = .heapRef addr := rfl
  have h1 : (List.foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal))
      [(0, Jvm.JvmVal.heapRef addr), (1, .bool false)]) 1 = .bool false := rfl
  refine ⟨⟨13, [.heapRef addr], (initUiJvmState [(0, .heapRef addr), (1, .bool false)] hp jh).locals, jh, hp⟩,
    ?_, rfl, rfl⟩
  dsimp only [initUiJvmState, Jvm.initJvmState]
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, h0]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.ldcStr "<this>") (by rfl) rfl]; rw [stepInstr_ldcStr]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter" "(Ljava/lang/Object;Ljava/lang/String;)V") (by rfl) rfl]
  rw [stepInstr_checkNotNullParam_heapRef]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.iload 1) (by rfl) rfl]; rw [stepInstr_iload, h1]; dsimp only
  rw [runJvmRes_ifeq_bool _ _ _ 4 12 false _ _ _ _ (by rfl) (mkUiCommonHooks_isZero? _ _ _)]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, h0]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ .areturn (by rfl) rfl]; rw [stepInstr_areturn]

theorem map_single_equiv (resolveProg : String → Option (List JvmInstr))
    (depth sf fuel : Nat) (hf : 23 ≤ fuel)
    {jh : Jvm.JvmHeap UiExt} {addr : Nat} {c c' : JvmVal}
    (hs : HasSingleFields jh addr c) (hc : c.isCat2 = false) (hp : UiHeap)
    {fnVal : JvmVal} {f : JvmVal → Option JvmVal}
    (hfn : HasFn1Behavior hp fnVal f) (hfc : f c = some c') :
    ∃ st',
      Jvm.runJvmRes (mkUiCommonHooks resolveProg depth sf) fuel
          TargetStateKt_map_prog (initUiJvmState [(0, .heapRef addr), (1, fnVal)] hp jh) =
        some (.heapRef jh.objects.size, st') ∧
      HasSingleFields st'.jvmHeap jh.objects.size c' ∧
      st'.heap = hp := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  have h0 : (List.foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal))
      [(0, Jvm.JvmVal.heapRef addr), (1, fnVal)]) 0 = .heapRef addr := rfl
  have h1 : (List.foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal))
      [(0, Jvm.JvmVal.heapRef addr), (1, fnVal)]) 1 = fnVal := rfl
  let obj0 : Jvm.HeapObj UiExt := .instance "com/alexvanyo/composelife/ui/util/TargetState$Single" []
  let newAddr := jh.objects.size
  let jh0 := (jh.alloc obj0).2
  let jh1 := jh0.set newAddr (.instance "com/alexvanyo/composelife/ui/util/TargetState$Single" [("current", c')])
  have hget0 : jh0.get? newAddr = some obj0 := Jvm.jvmHeap_get?_alloc_self jh obj0
  have hs0 : HasSingleFields jh0 addr c := hasSingleFields_alloc hs obj0
  have hsNew : HasSingleFields jh1 newAddr c' := hasSingleFields_init_of_new jh c'
  let locs2 := setLocal (List.foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal))
      [(0, Jvm.JvmVal.heapRef addr), (1, fnVal)]) 2 (.heapRef addr)
  refine ⟨⟨52, [.heapRef newAddr], locs2, jh1, hp⟩, ?_, hsNew, rfl⟩
  dsimp only [initUiJvmState, Jvm.initJvmState]
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, h0]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.ldcStr "<this>") (by rfl) rfl]; rw [stepInstr_ldcStr]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter" "(Ljava/lang/Object;Ljava/lang/String;)V") (by rfl) rfl]
  rw [stepInstr_checkNotNullParam_heapRef]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 1) (by rfl) rfl]; rw [stepInstr_aload, h1]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.ldcStr "lambda") (by rfl) rfl]; rw [stepInstr_ldcStr]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter" "(Ljava/lang/Object;Ljava/lang/String;)V") (by rfl) rfl]
  have ⟨fnExt, hfnExt⟩ : ∃ e, fnVal = .ext e := by
    cases fnVal <;> simp [HasFn1Behavior] at hfn
    exact ⟨_, rfl⟩
  rw [hfnExt, stepInstr_checkNotNullParam_ext]
  rw [← hfnExt]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, h0]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.astore 2) (by rfl) rfl]; rw [stepInstr_astore]; dsimp only
  have hl0 : setLocal (List.foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal))
      [(0, Jvm.JvmVal.heapRef addr), (1, fnVal)]) 2 (.heapRef addr) 0 = .heapRef addr := rfl
  have hl1 : setLocal (List.foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal))
      [(0, Jvm.JvmVal.heapRef addr), (1, fnVal)]) 2 (.heapRef addr) 1 = fnVal := rfl
  have hl2 : setLocal (List.foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal))
      [(0, Jvm.JvmVal.heapRef addr), (1, fnVal)]) 2 (.heapRef addr) 2 = .heapRef addr := rfl
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 2) (by rfl) rfl]; rw [stepInstr_aload, hl2]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.instanceof "com/alexvanyo/composelife/ui/util/TargetState$Single") (by rfl) rfl]
  rw [stepInstr_instanceof_val]
  simp only [Jvm.evalInstanceOf, checkInstanceOf_single resolveProg depth sf hs, ↓reduceIte]
  rw [runJvmRes_ifeq_i32 _ _ _ 10 22 1 _ _ _ _ (by rfl) (mkUiCommonHooks_isZero? _ _ _)]
  simp only [show ((1 : UInt32) == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.newClass "com/alexvanyo/composelife/ui/util/TargetState$Single") (by rfl) rfl]
  rw [stepInstr_newClass_single]; dsimp only
  change Jvm.runJvmRes (mkUiCommonHooks resolveProg depth sf) (k + 11) TargetStateKt_map_prog
      ⟨12, [.heapRef newAddr], _, jh0, hp⟩ = _
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ .dup (by rfl) rfl]; rw [stepInstr_dup]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, hl0]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.checkcast "com/alexvanyo/composelife/ui/util/TargetState$Single") (by rfl) rfl]
  rw [stepInstr_checkcast_some _ _ _ _ _ _ _ _ _ (evalCheckCast_single resolveProg depth sf hs0)]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokevirtual "com/alexvanyo/composelife/ui/util/TargetState$Single" "getCurrent" "()Ljava/lang/Object;") (by rfl) rfl]
  rw [stepInstr_invokeVirtual_single_getCurrent resolveProg depth sf 15 hs0]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 1) (by rfl) rfl]; rw [stepInstr_aload, hl1]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ .swap (by rfl) rfl]; rw [stepInstr_swap (ha := by rw [hfnExt]; rfl) (hb := hc)]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokeinterface "kotlin/jvm/functions/Function1" "invoke" "(Ljava/lang/Object;)Ljava/lang/Object;") (by rfl) rfl]
  rw [stepInstr_invokeInterface_fn1 resolveProg depth sf 18 fnVal c c' f _ _ _ hp hfn hfc]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokespecial "com/alexvanyo/composelife/ui/util/TargetState$Single" "<init>" "(Ljava/lang/Object;)V") (by rfl) rfl]
  rw [stepInstr_invokeSpecial_single_init_alloc resolveProg depth sf 19 newAddr c' _ _ jh0 hp hget0]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.checkcast "com/alexvanyo/composelife/ui/util/TargetState") (by rfl) rfl]
  rw [stepInstr_checkcast_some _ _ _ _ _ _ _ _ _ (evalCheckCast_targetState_of_single resolveProg depth sf hsNew)]; dsimp only
  rw [runJvmRes_goto _ _ _ _ 52 (by rfl)]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ .areturn (by rfl) rfl]; rw [stepInstr_areturn]

private theorem map_inProgress_prefix (resolveProg : String → Option (List JvmInstr))
    (d sf k : Nat) (hext : ExtendsUiProgs resolveProg) (hsf : 45 ≤ sf)
    {jh : Jvm.JvmHeap UiExt} {addr : Nat} {c p : JvmVal} {pr : Float32} {m c' p' fnVal : JvmVal}
    {f : JvmVal → Option JvmVal}
    (hi : HasInProgressFields jh addr c p pr m) (hc : c.isCat2 = false) (hpv : p.isCat2 = false)
    (hp : UiHeap) (hfn : HasFn1Behavior hp fnVal f) (hfc : f c = some c') (hfp : f p = some p') :
    let obj0 : Jvm.HeapObj UiExt := .instance "com/alexvanyo/composelife/ui/util/TargetState$InProgress" []
    let newAddr := jh.objects.size
    let jh0 := (jh.alloc obj0).2
    let locs2 := setLocal (List.foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal))
      [(0, Jvm.JvmVal.heapRef addr), (1, fnVal)]) 2 (.heapRef addr)
    Jvm.runJvmRes (mkUiCommonHooks resolveProg (d + 2) sf) (k + 38) TargetStateKt_map_prog
        (initUiJvmState [(0, .heapRef addr), (1, fnVal)] hp jh) =
      Jvm.runJvmRes (mkUiCommonHooks resolveProg (d + 2) sf) (k + 4) TargetStateKt_map_prog
        ⟨45, [m, .f32 pr, p', c', .heapRef newAddr, .heapRef newAddr], locs2, jh0, hp⟩ := by
  intro obj0 newAddr jh0 locs2
  have h0 : (List.foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal))
      [(0, Jvm.JvmVal.heapRef addr), (1, fnVal)]) 0 = .heapRef addr := rfl
  have h1 : (List.foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal))
      [(0, Jvm.JvmVal.heapRef addr), (1, fnVal)]) 1 = fnVal := rfl
  have hl0 : setLocal (List.foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal))
      [(0, Jvm.JvmVal.heapRef addr), (1, fnVal)]) 2 (.heapRef addr) 0 = .heapRef addr := rfl
  have hl1 : setLocal (List.foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal))
      [(0, Jvm.JvmVal.heapRef addr), (1, fnVal)]) 2 (.heapRef addr) 1 = fnVal := rfl
  have hl2 : setLocal (List.foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal))
      [(0, Jvm.JvmVal.heapRef addr), (1, fnVal)]) 2 (.heapRef addr) 2 = .heapRef addr := rfl
  have hi0 : HasInProgressFields jh0 addr c p pr m := hasInProgressFields_alloc hi obj0
  dsimp only [initUiJvmState, Jvm.initJvmState]
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, h0]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.ldcStr "<this>") (by rfl) rfl]; rw [stepInstr_ldcStr]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter" "(Ljava/lang/Object;Ljava/lang/String;)V") (by rfl) rfl]
  rw [stepInstr_checkNotNullParam_heapRef]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 1) (by rfl) rfl]; rw [stepInstr_aload, h1]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.ldcStr "lambda") (by rfl) rfl]; rw [stepInstr_ldcStr]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter" "(Ljava/lang/Object;Ljava/lang/String;)V") (by rfl) rfl]
  have ⟨fnExt, hfnExt⟩ : ∃ e, fnVal = .ext e := by
    cases fnVal <;> simp [HasFn1Behavior] at hfn
    exact ⟨_, rfl⟩
  rw [hfnExt, stepInstr_checkNotNullParam_ext]
  rw [← hfnExt]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, h0]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.astore 2) (by rfl) rfl]; rw [stepInstr_astore]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 2) (by rfl) rfl]; rw [stepInstr_aload, hl2]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.instanceof "com/alexvanyo/composelife/ui/util/TargetState$Single") (by rfl) rfl]
  rw [stepInstr_instanceof_val]
  simp only [Jvm.evalInstanceOf, checkInstanceOf_inProgress_not_single resolveProg (d + 2) sf hi,
    Bool.false_eq_true, ↓reduceIte]
  rw [runJvmRes_ifeq_i32 _ _ _ 10 22 0 _ _ _ _ (by rfl) (mkUiCommonHooks_isZero? _ _ _)]
  simp only [show ((0 : UInt32) == 0) = true from rfl, ↓reduceIte]
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 2) (by rfl) rfl]; rw [stepInstr_aload, hl2]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.instanceof "com/alexvanyo/composelife/ui/util/TargetState$InProgress") (by rfl) rfl]
  rw [stepInstr_instanceof_val]
  simp only [Jvm.evalInstanceOf, checkInstanceOf_inProgress resolveProg (d + 2) sf hi, ↓reduceIte]
  rw [runJvmRes_ifeq_i32 _ _ _ 24 48 1 _ _ _ _ (by rfl) (mkUiCommonHooks_isZero? _ _ _)]
  simp only [show ((1 : UInt32) == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.newClass "com/alexvanyo/composelife/ui/util/TargetState$InProgress") (by rfl) rfl]
  rw [stepInstr_newClass_inProgress]; dsimp only
  change Jvm.runJvmRes (mkUiCommonHooks resolveProg (d + 2) sf) (k + 23) TargetStateKt_map_prog
      ⟨26, [.heapRef newAddr], locs2, jh0, hp⟩ = _
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ .dup (by rfl) rfl]; rw [stepInstr_dup]; dsimp only
  -- f current
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, show locs2 0 = .heapRef addr from hl0]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.checkcast "com/alexvanyo/composelife/ui/util/TargetState$InProgress") (by rfl) rfl]
  rw [stepInstr_checkcast_some _ _ _ _ _ _ _ _ _ (evalCheckCast_inProgress resolveProg (d + 2) sf hi0)]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokevirtual "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "getCurrent" "()Ljava/lang/Object;") (by rfl) rfl]
  rw [stepInstr_invokeVirtual_inProgress_getCurrent_fq resolveProg (d + 1) sf 29 hext (by omega) hi0]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 1) (by rfl) rfl]; rw [stepInstr_aload, show locs2 1 = fnVal from hl1]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ .swap (by rfl) rfl]; rw [stepInstr_swap (ha := by rw [hfnExt]; rfl) (hb := hc)]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokeinterface "kotlin/jvm/functions/Function1" "invoke" "(Ljava/lang/Object;)Ljava/lang/Object;") (by rfl) rfl]
  rw [stepInstr_invokeInterface_fn1 resolveProg (d + 2) sf 32 fnVal c c' f _ _ _ hp hfn hfc]; dsimp only
  -- f provisional
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, show locs2 0 = .heapRef addr from hl0]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.checkcast "com/alexvanyo/composelife/ui/util/TargetState$InProgress") (by rfl) rfl]
  rw [stepInstr_checkcast_some _ _ _ _ _ _ _ _ _ (evalCheckCast_inProgress resolveProg (d + 2) sf hi0)]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokevirtual "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "getProvisional" "()Ljava/lang/Object;") (by rfl) rfl]
  rw [stepInstr_invokeVirtual_inProgress_getProvisional resolveProg (d + 1) sf 35 hext (by omega) hi0]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 1) (by rfl) rfl]; rw [stepInstr_aload, show locs2 1 = fnVal from hl1]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ .swap (by rfl) rfl]; rw [stepInstr_swap (ha := by rw [hfnExt]; rfl) (hb := hpv)]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokeinterface "kotlin/jvm/functions/Function1" "invoke" "(Ljava/lang/Object;)Ljava/lang/Object;") (by rfl) rfl]
  rw [stepInstr_invokeInterface_fn1 resolveProg (d + 2) sf 38 fnVal p p' f _ _ _ hp hfn hfp]; dsimp only
  -- progress & metadata
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, show locs2 0 = .heapRef addr from hl0]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.checkcast "com/alexvanyo/composelife/ui/util/TargetState$InProgress") (by rfl) rfl]
  rw [stepInstr_checkcast_some _ _ _ _ _ _ _ _ _ (evalCheckCast_inProgress resolveProg (d + 2) sf hi0)]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokevirtual "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "getProgress" "()F") (by rfl) rfl]
  rw [stepInstr_invokeVirtual_inProgress_getProgress resolveProg (d + 1) sf 41 hext (by omega) hi0]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, show locs2 0 = .heapRef addr from hl0]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.checkcast "com/alexvanyo/composelife/ui/util/TargetState$InProgress") (by rfl) rfl]
  rw [stepInstr_checkcast_some _ _ _ _ _ _ _ _ _ (evalCheckCast_inProgress resolveProg (d + 2) sf hi0)]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokevirtual "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "getMetadata" "()Ljava/lang/Object;") (by rfl) rfl]
  rw [stepInstr_invokeVirtual_inProgress_getMetadata resolveProg (d + 1) sf 44 hext (by omega) hi0]

theorem map_inProgress_valid_equiv (resolveProg : String → Option (List JvmInstr))
    (d sf fuel : Nat) (hext : ExtendsUiProgs resolveProg) (hsf : 45 ≤ sf) (hf : 38 ≤ fuel)
    {jh : Jvm.JvmHeap UiExt} {addr : Nat} {c p : JvmVal} {pr : Float32} {m c' p' fnVal : JvmVal}
    {f : JvmVal → Option JvmVal}
    (hi : HasInProgressFields jh addr c p pr m) (hc : c.isCat2 = false) (hpv : p.isCat2 = false)
    (hp : UiHeap) (hfn : HasFn1Behavior hp fnVal f) (hfc : f c = some c') (hfp : f p = some p')
    (hne : Jvm.JvmVal.beqVal beqUiExt c' p' = false)
    (hcm : c'.equalsModeled jh = true) (hpm : p'.equalsModeled jh = true) :
    ∃ st',
      Jvm.runJvmRes (mkUiCommonHooks resolveProg (d + 2) sf) fuel
          TargetStateKt_map_prog (initUiJvmState [(0, .heapRef addr), (1, fnVal)] hp jh) =
        some (.heapRef jh.objects.size, st') ∧
      HasInProgressFields st'.jvmHeap jh.objects.size c' p' pr m ∧
      st'.heap = hp := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  have hprog := hext "TargetState$InProgress.<init>" TargetState_InProgress_init_prog rfl
  let obj0 : Jvm.HeapObj UiExt := .instance "com/alexvanyo/composelife/ui/util/TargetState$InProgress" []
  let newAddr := jh.objects.size
  let jh0 := (jh.alloc obj0).2
  have hget0 : jh0.get? newAddr = some (.instance "com/alexvanyo/composelife/ui/util/TargetState$InProgress" []) :=
    Jvm.jvmHeap_get?_alloc_self jh obj0
  rcases inProgress_ctor_valid_equiv resolveProg d sf sf hext (by omega) hsf jh0 newAddr
    "com/alexvanyo/composelife/ui/util/TargetState$InProgress" [] hget0 (Or.inl rfl) c' p' pr m hp hne
    (Jvm.jvmVal_equalsModeled_alloc _ c' hcm) (Jvm.jvmVal_equalsModeled_alloc _ p' hpm) with
    ⟨stCtor, hctorRun, hctorHi, hctorHp⟩
  let locs2 := setLocal (List.foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal))
      [(0, Jvm.JvmVal.heapRef addr), (1, fnVal)]) 2 (.heapRef addr)
  refine ⟨⟨52, [.heapRef newAddr], locs2, stCtor.jvmHeap, stCtor.heap⟩, ?_, hctorHi, hctorHp⟩
  rw [map_inProgress_prefix resolveProg d sf k hext hsf hi hc hpv hp hfn hfc hfp]
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokespecial "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "<init>" "(Ljava/lang/Object;Ljava/lang/Object;FLjava/lang/Object;)V") (by rfl) rfl]
  rw [mkUiCommonHooks_stepInvokeSpecial_inProgress_init_fq, hprog]; dsimp only
  rw [hctorRun]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.checkcast "com/alexvanyo/composelife/ui/util/TargetState") (by rfl) rfl]
  rw [stepInstr_checkcast_some _ _ _ _ _ _ _ _ _
    (evalCheckCast_targetState_of_inProgress resolveProg (d + 2) sf hctorHi)]; dsimp only
  rw [runJvmRes_goto _ _ _ _ 52 (by rfl)]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ .areturn (by rfl) rfl]; rw [stepInstr_areturn]

theorem map_inProgress_trap_equiv (resolveProg : String → Option (List JvmInstr))
    (d sf fuel : Nat) (hext : ExtendsUiProgs resolveProg) (hsf : 45 ≤ sf) (hf : 38 ≤ fuel)
    {jh : Jvm.JvmHeap UiExt} {addr : Nat} {c p : JvmVal} {pr : Float32} {m c' p' fnVal : JvmVal}
    {f : JvmVal → Option JvmVal}
    (hi : HasInProgressFields jh addr c p pr m) (hc : c.isCat2 = false) (hpv : p.isCat2 = false)
    (hp : UiHeap) (hfn : HasFn1Behavior hp fnVal f) (hfc : f c = some c') (hfp : f p = some p')
    (heq : Jvm.JvmVal.beqVal beqUiExt c' p' = true)
    (hcm : c'.equalsModeled jh = true) (hpm : p'.equalsModeled jh = true) :
    Jvm.runJvmRes (mkUiCommonHooks resolveProg (d + 2) sf) fuel
        TargetStateKt_map_prog (initUiJvmState [(0, .heapRef addr), (1, fnVal)] hp jh) =
      none := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  have hprog := hext "TargetState$InProgress.<init>" TargetState_InProgress_init_prog rfl
  let obj0 : Jvm.HeapObj UiExt := .instance "com/alexvanyo/composelife/ui/util/TargetState$InProgress" []
  let newAddr := jh.objects.size
  let jh0 := (jh.alloc obj0).2
  have hget0 : jh0.get? newAddr = some (.instance "com/alexvanyo/composelife/ui/util/TargetState$InProgress" []) :=
    Jvm.jvmHeap_get?_alloc_self jh obj0
  have hctorTrap := inProgress_ctor_trap_equiv resolveProg d sf sf hext (by omega) hsf jh0 newAddr
    "com/alexvanyo/composelife/ui/util/TargetState$InProgress" [] hget0 (Or.inl rfl) c' p' pr m hp heq
    (Jvm.jvmVal_equalsModeled_alloc _ c' hcm) (Jvm.jvmVal_equalsModeled_alloc _ p' hpm)
  rw [map_inProgress_prefix resolveProg d sf k hext hsf hi hc hpv hp hfn hfc hfp]
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokespecial "com/alexvanyo/composelife/ui/util/TargetState$InProgress" "<init>" "(Ljava/lang/Object;Ljava/lang/Object;FLjava/lang/Object;)V") (by rfl) rfl]
  rw [mkUiCommonHooks_stepInvokeSpecial_inProgress_init_fq, hprog]; dsimp only
  rw [hctorTrap]

set_option maxRecDepth 8192 in
private theorem mkUiCommonHooks_stepInvokeStatic_targetState_map
    (r : String → Option (List JvmInstr)) (d sf pc : Nat) (ts fnVal : JvmVal)
    (stk : List JvmVal) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap UiExt) (hp : UiHeap) :
    Jvm.stepInstr (mkUiCommonHooks r (d + 1) sf)
        (.invokestatic "com/alexvanyo/composelife/ui/util/TargetStateKt" "map"
          "(Lcom/alexvanyo/composelife/ui/util/TargetState;Lkotlin/jvm/functions/Function1;)Lcom/alexvanyo/composelife/ui/util/TargetState;")
        ⟨pc, fnVal :: ts :: stk, locs, jh, hp⟩ =
      match r "TargetStateKt.map" with
      | some prog =>
        match Jvm.runJvmRes (mkUiCommonHooks r d sf) sf prog
            (initUiJvmState [(0, ts), (1, fnVal)] hp jh) with
        | some (res, endSt) => .inl (some ⟨pc + 1, res :: stk, locs, endSt.jvmHeap, endSt.heap⟩)
        | none => .inr none
      | none => .inr none := by
  have hE : ∀ st : JvmState, Jvm.stepInstr (mkUiCommonHooks r (d + 1) sf)
      (.invokestatic "com/alexvanyo/composelife/ui/util/TargetStateKt" "map"
          "(Lcom/alexvanyo/composelife/ui/util/TargetState;Lkotlin/jvm/functions/Function1;)Lcom/alexvanyo/composelife/ui/util/TargetState;") st =
      (mkUiCommonHooks r (d + 1) sf).stepInvokeStatic st "TargetStateKt" "map"
          "(Lcom/alexvanyo/composelife/ui/util/TargetState;Lkotlin/jvm/functions/Function1;)Lcom/alexvanyo/composelife/ui/util/TargetState;" :=
    fun _ => rfl
  have ht : Jvm.parseMethodParamTags
      "(Lcom/alexvanyo/composelife/ui/util/TargetState;Lkotlin/jvm/functions/Function1;)Lcom/alexvanyo/composelife/ui/util/TargetState;" =
      ['L', 'L'] := by decide
  have hstr : "TargetStateKt" ++ "." ++ "map" = "TargetStateKt.map" := rfl
  have hvoid : isVoidTarget "TargetStateKt.map" = false := rfl
  have hn : normalizeUiCommonClass "TargetStateKt" = "TargetStateKt" := rfl
  rw [hE]
  conv => lhs; unfold mkUiCommonHooks
  dsimp only
  rw [hn]
  simp only [beq_self_eq_true, Bool.true_or, ↓reduceIte, ht, hstr, hvoid, List.length_cons, List.length_nil,
    Nat.not_lt_of_ge (Nat.le_add_left 2 stk.length), List.take_succ_cons, List.take_zero, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append, List.drop_succ_cons, List.drop_zero,
    Bool.false_eq_true]
  have hinit : (⟨0, [], List.foldl (fun loc x => setLocal loc x.fst x.snd) (fun _ => Jvm.JvmVal.i32 0)
        (assignParamLocalsAux 0 ['L', 'L'] [ts, fnVal]), jh, hp⟩ : JvmState) =
      initUiJvmState [(0, ts), (1, fnVal)] hp jh := rfl
  rw [hinit]
  cases r "TargetStateKt.map" with
  | none => rfl
  | some prog =>
    dsimp only
    cases Jvm.runJvmRes (mkUiCommonHooks r d sf) sf prog (initUiJvmState [(0, ts), (1, fnVal)] hp jh) <;> rfl

theorem not_single_equiv (resolveProg : String → Option (List JvmInstr))
    (d sf fuel : Nat) (hext : ExtendsUiProgs resolveProg) (hsf : 23 ≤ sf) (hf : 8 ≤ fuel)
    {jh : Jvm.JvmHeap UiExt} {addr : Nat} {cb : Bool}
    (hs : HasSingleFields jh addr (.boxedBool cb)) (hp : UiHeap)
    (hstat : jh.getStatic? "com/alexvanyo/composelife/ui/util/TargetStateKt$not$1" "INSTANCE" = none ∨
      jh.getStatic? "com/alexvanyo/composelife/ui/util/TargetStateKt$not$1" "INSTANCE" = some (.ext .notLambda)) :
    ∃ st',
      Jvm.runJvmRes (mkUiCommonHooks resolveProg (d + 1) sf) fuel
          TargetStateKt_not_prog (initUiJvmState [(0, .heapRef addr)] hp jh) =
        some (.heapRef jh.objects.size, st') ∧
      HasSingleFields st'.jvmHeap jh.objects.size (.boxedBool (!cb)) ∧
      st'.heap = hp := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  have hprog := hext "TargetStateKt.map" TargetStateKt_map_prog rfl
  let fnot : JvmVal → Option JvmVal := fun v => match v with | .boxedBool b => some (.boxedBool (!b)) | _ => none
  rcases map_single_equiv resolveProg d sf sf hsf hs rfl hp (fnVal := .ext .notLambda) (f := fnot)
    (fun _ => rfl) rfl with ⟨stMap, hmapRun, hmapHs, hmapHp⟩
  have h0 : (List.foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal))
      [(0, Jvm.JvmVal.heapRef addr)]) 0 = .heapRef addr := rfl
  refine ⟨⟨7, [.heapRef jh.objects.size],
      (initUiJvmState [(0, Jvm.JvmVal.heapRef addr)] hp jh).locals, stMap.jvmHeap, stMap.heap⟩,
    ?_, hmapHs, hmapHp⟩
  dsimp only [initUiJvmState, Jvm.initJvmState]
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, h0]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.ldcStr "<this>") (by rfl) rfl]; rw [stepInstr_ldcStr]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter" "(Ljava/lang/Object;Ljava/lang/String;)V") (by rfl) rfl]
  rw [stepInstr_checkNotNullParam_heapRef]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, h0]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.getstatic "com/alexvanyo/composelife/ui/util/TargetStateKt$not$1" "INSTANCE" "Lcom/alexvanyo/composelife/ui/util/TargetStateKt$not$1;") (by rfl) rfl]
  rw [stepInstr_getstatic_notLambda _ _ _ _ _ _ _ _ hstat]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.checkcast "kotlin/jvm/functions/Function1") (by rfl) rfl]
  rw [stepInstr_checkcast_some _ _ _ _ _ _ _ _ _
    (evalCheckCast_function1 (mkUiCommonHooks resolveProg (d + 1) sf) jh (.ext .notLambda)
      (mkUiCommonHooks_checkCast _ _ _) (Or.inl rfl))]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokestatic "com/alexvanyo/composelife/ui/util/TargetStateKt" "map" "(Lcom/alexvanyo/composelife/ui/util/TargetState;Lkotlin/jvm/functions/Function1;)Lcom/alexvanyo/composelife/ui/util/TargetState;") (by rfl) rfl]
  rw [mkUiCommonHooks_stepInvokeStatic_targetState_map, hprog]; dsimp only
  rw [hmapRun]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ .areturn (by rfl) rfl]; rw [stepInstr_areturn]

theorem not_inProgress_equiv (resolveProg : String → Option (List JvmInstr))
    (d sf fuel : Nat) (hext : ExtendsUiProgs resolveProg) (hsf : 45 ≤ sf) (hf : 8 ≤ fuel)
    {jh : Jvm.JvmHeap UiExt} {addr : Nat} {cb pb : Bool} {pr : Float32} {m : JvmVal}
    (hi : HasInProgressFields jh addr (.boxedBool cb) (.boxedBool pb) pr m)
    (hne : cb ≠ pb) (hp : UiHeap)
    (hstat : jh.getStatic? "com/alexvanyo/composelife/ui/util/TargetStateKt$not$1" "INSTANCE" = none ∨
      jh.getStatic? "com/alexvanyo/composelife/ui/util/TargetStateKt$not$1" "INSTANCE" = some (.ext .notLambda)) :
    ∃ st',
      Jvm.runJvmRes (mkUiCommonHooks resolveProg (d + 3) sf) fuel
          TargetStateKt_not_prog (initUiJvmState [(0, .heapRef addr)] hp jh) =
        some (.heapRef jh.objects.size, st') ∧
      HasInProgressFields st'.jvmHeap jh.objects.size (.boxedBool (!cb)) (.boxedBool (!pb)) pr m ∧
      st'.heap = hp := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  have hprog := hext "TargetStateKt.map" TargetStateKt_map_prog rfl
  let fnot : JvmVal → Option JvmVal := fun v => match v with | .boxedBool b => some (.boxedBool (!b)) | _ => none
  have hneNot : Jvm.JvmVal.beqVal beqUiExt (.boxedBool (!cb)) (.boxedBool (!pb)) = false := by
    cases cb <;> cases pb <;> first | exact absurd rfl hne | rfl
  rcases map_inProgress_valid_equiv resolveProg d sf sf hext hsf (by omega) hi rfl rfl hp
    (fnVal := .ext .notLambda) (f := fnot) (fun _ => rfl) rfl rfl hneNot rfl rfl with
    ⟨stMap, hmapRun, hmapHi, hmapHp⟩
  have h0 : (List.foldl (fun loc (i, v) => setLocal loc i v) (fun (_ : Nat) => (.i32 0 : JvmVal))
      [(0, Jvm.JvmVal.heapRef addr)]) 0 = .heapRef addr := rfl
  refine ⟨⟨7, [.heapRef jh.objects.size],
      (initUiJvmState [(0, Jvm.JvmVal.heapRef addr)] hp jh).locals, stMap.jvmHeap, stMap.heap⟩,
    ?_, hmapHi, hmapHp⟩
  dsimp only [initUiJvmState, Jvm.initJvmState]
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, h0]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.ldcStr "<this>") (by rfl) rfl]; rw [stepInstr_ldcStr]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter" "(Ljava/lang/Object;Ljava/lang/String;)V") (by rfl) rfl]
  rw [stepInstr_checkNotNullParam_heapRef]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.aload 0) (by rfl) rfl]; rw [stepInstr_aload, h0]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.getstatic "com/alexvanyo/composelife/ui/util/TargetStateKt$not$1" "INSTANCE" "Lcom/alexvanyo/composelife/ui/util/TargetStateKt$not$1;") (by rfl) rfl]
  rw [stepInstr_getstatic_notLambda _ _ _ _ _ _ _ _ hstat]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.checkcast "kotlin/jvm/functions/Function1") (by rfl) rfl]
  rw [stepInstr_checkcast_some _ _ _ _ _ _ _ _ _
    (evalCheckCast_function1 (mkUiCommonHooks resolveProg (d + 3) sf) jh (.ext .notLambda)
      (mkUiCommonHooks_checkCast _ _ _) (Or.inl rfl))]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ (.invokestatic "com/alexvanyo/composelife/ui/util/TargetStateKt" "map" "(Lcom/alexvanyo/composelife/ui/util/TargetState;Lkotlin/jvm/functions/Function1;)Lcom/alexvanyo/composelife/ui/util/TargetState;") (by rfl) rfl]
  rw [mkUiCommonHooks_stepInvokeStatic_targetState_map, hprog]; dsimp only
  rw [hmapRun]; dsimp only
  rw [Jvm.runJvmRes_nonbranch _ _ _ _ .areturn (by rfl) rfl]; rw [stepInstr_areturn]

end UiCommon.KotlinJvmVerification
