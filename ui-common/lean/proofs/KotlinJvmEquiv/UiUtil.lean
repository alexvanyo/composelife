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
import KotlinJvmBytecode
import models.UiUtilModel
import theorems.UiUtilModelTheorems

namespace UiCommon.KotlinJvmVerification
open UiCommon.KotlinJvmBytecode
open UiCommon.KotlinModel

set_option maxRecDepth 4000

private abbrev UtilVal := Jvm.JvmVal Empty
private abbrev UtilState := Jvm.JvmState Empty Unit

private def initUtilState (slots : List (Nat × UtilVal)) (jh : Jvm.JvmHeap Empty := {}) : UtilState :=
  Jvm.initJvmState slots (.i32 0) () jh

private def wiLerpCls : String := "com/alexvanyo/composelife/ui/util/WindowInsetsLerpKt$lerp$1"
private def padPlusCls : String := "com/alexvanyo/composelife/ui/util/PaddingValuesExtensionsKt$plus$1"
private def nnLongCls : String := "com/alexvanyo/composelife/ui/util/NonNegativeLong"
private def nnDoubleCls : String := "com/alexvanyo/composelife/ui/util/NonNegativeDouble"

private def utilIsSubtype (sub sup : String) : Bool :=
  sub == sup ||
  (sub == wiLerpCls && sup == "androidx/compose/foundation/layout/WindowInsets") ||
  (sub == padPlusCls && sup == "androidx/compose/foundation/layout/PaddingValues") ||
  (sub == nnLongCls && sup == "androidx/compose/foundation/text/input/InputTransformation") ||
  (sub == nnDoubleCls && sup == "androidx/compose/foundation/text/input/InputTransformation") ||
  sup == "java/lang/Object"

def utilGetField? (h : Jvm.JvmHeap Empty) (addr : Nat) (cls field : String) : Option UtilVal :=
  match h.get? addr with
  | some obj => obj.getField? utilIsSubtype cls field
  | none => none

private def utilSetField (h : Jvm.JvmHeap Empty) (addr : Nat) (cls field : String) (v : UtilVal) : Jvm.JvmHeap Empty :=
  match h.get? addr with
  | some obj =>
    match obj.setField utilIsSubtype cls field v with
    | some obj' => h.set addr obj'
    | none => h
  | none => h

/--
Hooks for `WindowInsetsLerpKt`, `PaddingValuesExtensionsKt`, `NonNegativeLong`, and `NonNegativeDouble`.
- `insetsVal` models `WindowInsets.get{Left,Top,Right,Bottom}` for `"start"` vs `"stop"`.
- `padVal` models `PaddingValues.calculate{Left,Top,Right,Bottom}Padding` for `"a"` vs `"b"`.
- `lerpInt` models `MathHelpersKt.lerp(IIF)I`.
- `parseLong` / `parseDouble` model `StringsKt.toLongOrNull` / `StringsKt.toDoubleOrNull`.
- `TextFieldBuffer` is a heap instance storing `"text"` (`.str s`) and `"reverted"` (`.i32 0` or `1`).
-/
def mkUiUtilHooks
    (insetsStart insetsStop : UInt32 × UInt32 × UInt32 × UInt32 := (0, 0, 0, 0))
    (padA padB : Float32 × Float32 × Float32 × Float32 := (0.0, 0.0, 0.0, 0.0))
    (lerpInt : UInt32 → UInt32 → Float32 → UInt32 := fun a _ _ => a)
    (parseLong : String → Option UInt64 := fun _ => none)
    (parseDouble : String → Option Float := fun _ => none) :
    Jvm.JvmHooks Empty Unit where
  isSubtypeOf := utilIsSubtype
  checkCast cls v :=
    match cls, v with
    | "androidx/compose/foundation/text/input/InputTransformation",
        .allocRef "com/alexvanyo/composelife/ui/util/NonNegativeLong" => some v
    | "androidx/compose/foundation/text/input/InputTransformation",
        .allocRef "com/alexvanyo/composelife/ui/util/NonNegativeDouble" => some v
    | _, _ => Jvm.defaultCheckCast (fun _ a => nomatch a) cls v
  resolveStatic _st cls field _desc :=
    match cls, field with
    | "androidx/compose/ui/text/input/KeyboardType", "Companion" =>
      some (.allocRef "androidx/compose/ui/text/input/KeyboardType$Companion")
    | "com/alexvanyo/composelife/ui/util/NonNegativeLong", "INSTANCE" =>
      some (.allocRef nnLongCls)
    | "com/alexvanyo/composelife/ui/util/NonNegativeDouble", "INSTANCE" =>
      some (.allocRef nnDoubleCls)
    | _, _ => none
  stepNewClass st cls :=
    let (addr, h') := st.jvmHeap.alloc (.instance cls [])
    .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: st.stack, jvmHeap := h' })
  stepInvokeSpecial st cls method desc :=
    match cls, method, desc, st.stack with
    | "java/lang/Object", "<init>", "()V", _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := rest })
    | "com/alexvanyo/composelife/ui/util/WindowInsetsLerpKt$lerp$1", "<init>",
        "(Landroidx/compose/foundation/layout/WindowInsets;Landroidx/compose/foundation/layout/WindowInsets;F)V",
        frac :: stop :: start :: .heapRef addr :: rest =>
      let h1 := utilSetField st.jvmHeap addr wiLerpCls "$start" start
      let h2 := utilSetField h1 addr wiLerpCls "$stop" stop
      let h3 := utilSetField h2 addr wiLerpCls "$fraction" frac
      .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h3 })
    | "com/alexvanyo/composelife/ui/util/PaddingValuesExtensionsKt$plus$1", "<init>",
        "(Landroidx/compose/foundation/layout/PaddingValues;Landroidx/compose/foundation/layout/PaddingValues;)V",
        other :: self :: .heapRef addr :: rest =>
      let h1 := utilSetField st.jvmHeap addr padPlusCls "$this_plus" self
      let h2 := utilSetField h1 addr padPlusCls "$other" other
      .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h2 })
    | "com/alexvanyo/composelife/ui/util/NonNegativeLong", "<init>", "()V", _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := rest })
    | "com/alexvanyo/composelife/ui/util/NonNegativeDouble", "<init>", "()V", _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := rest })
    | "androidx/compose/foundation/text/input/InputTransformation", "applySemantics",
        "(Landroidx/compose/ui/semantics/SemanticsPropertyReceiver;)V", _ :: _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := rest })
    | "androidx/compose/foundation/text/KeyboardOptions", "<init>",
        "(ILjava/lang/Boolean;IILandroidx/compose/ui/text/input/PlatformImeOptions;Ljava/lang/Boolean;Landroidx/compose/ui/text/intl/LocaleList;ILkotlin/jvm/internal/DefaultConstructorMarker;)V",
        _ :: _ :: _ :: _ :: _ :: _ :: kt :: _ :: _ :: .heapRef addr :: rest =>
      let h' := utilSetField st.jvmHeap addr "androidx/compose/foundation/text/KeyboardOptions" "keyboardType" kt
      .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
    | _, _, _, _ => .inr none
  stepInvokeVirtual st cls method desc :=
    match cls, method, desc, st.stack with
    | "androidx/compose/ui/text/input/KeyboardType$Companion", "getNumber-PjHm6EE", "()I", _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 3 :: rest })
    | "androidx/compose/ui/text/input/KeyboardType$Companion", "getDecimal-PjHm6EE", "()I", _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 8 :: rest })
    | "androidx/compose/foundation/text/input/TextFieldBuffer", "asCharSequence", "()Ljava/lang/CharSequence;",
        .heapRef bufAddr :: rest =>
      match utilGetField? st.jvmHeap bufAddr "TextFieldBuffer" "text" with
      | some s => .inl (some { st with pc := st.pc + 1, stack := s :: rest })
      | none => .inr none
    | "androidx/compose/foundation/text/input/TextFieldBuffer", "revertAllChanges", "()V",
        .heapRef bufAddr :: rest =>
      let h' := utilSetField st.jvmHeap bufAddr "TextFieldBuffer" "reverted" (.i32 1)
      .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
    | "java/lang/Object", "toString", "()Ljava/lang/String;", .str s :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .str s :: rest })
    | "java/lang/Long", "longValue", "()J", .boxedLong v :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i64 v :: rest })
    | "java/lang/Double", "doubleValue", "()D", .f64 d :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .f64 d :: rest })
    | _, _, _, _ => .inr none
  stepInvokeInterface st cls method desc :=
    match cls, method, desc, st.stack with
    | "androidx/compose/foundation/layout/WindowInsets", "getLeft",
        "(Landroidx/compose/ui/unit/Density;Landroidx/compose/ui/unit/LayoutDirection;)I",
        _ :: _ :: .allocRef tag :: rest =>
      let v := if tag == "start" then insetsStart.1 else insetsStop.1
      .inl (some { st with pc := st.pc + 1, stack := .i32 v :: rest })
    | "androidx/compose/foundation/layout/WindowInsets", "getTop",
        "(Landroidx/compose/ui/unit/Density;)I", _ :: .allocRef tag :: rest =>
      let v := if tag == "start" then insetsStart.2.1 else insetsStop.2.1
      .inl (some { st with pc := st.pc + 1, stack := .i32 v :: rest })
    | "androidx/compose/foundation/layout/WindowInsets", "getRight",
        "(Landroidx/compose/ui/unit/Density;Landroidx/compose/ui/unit/LayoutDirection;)I",
        _ :: _ :: .allocRef tag :: rest =>
      let v := if tag == "start" then insetsStart.2.2.1 else insetsStop.2.2.1
      .inl (some { st with pc := st.pc + 1, stack := .i32 v :: rest })
    | "androidx/compose/foundation/layout/WindowInsets", "getBottom",
        "(Landroidx/compose/ui/unit/Density;)I", _ :: .allocRef tag :: rest =>
      let v := if tag == "start" then insetsStart.2.2.2 else insetsStop.2.2.2
      .inl (some { st with pc := st.pc + 1, stack := .i32 v :: rest })
    | "androidx/compose/foundation/layout/PaddingValues", "calculateLeftPadding-u2uoSUM",
        "(Landroidx/compose/ui/unit/LayoutDirection;)F", _ :: .allocRef tag :: rest =>
      let v := if tag == "a" then padA.1 else padB.1
      .inl (some { st with pc := st.pc + 1, stack := .f32 v :: rest })
    | "androidx/compose/foundation/layout/PaddingValues", "calculateTopPadding-D9Ej5fM",
        "()F", .allocRef tag :: rest =>
      let v := if tag == "a" then padA.2.1 else padB.2.1
      .inl (some { st with pc := st.pc + 1, stack := .f32 v :: rest })
    | "androidx/compose/foundation/layout/PaddingValues", "calculateRightPadding-u2uoSUM",
        "(Landroidx/compose/ui/unit/LayoutDirection;)F", _ :: .allocRef tag :: rest =>
      let v := if tag == "a" then padA.2.2.1 else padB.2.2.1
      .inl (some { st with pc := st.pc + 1, stack := .f32 v :: rest })
    | "androidx/compose/foundation/layout/PaddingValues", "calculateBottomPadding-D9Ej5fM",
        "()F", .allocRef tag :: rest =>
      let v := if tag == "a" then padA.2.2.2 else padB.2.2.2
      .inl (some { st with pc := st.pc + 1, stack := .f32 v :: rest })
    | "java/lang/CharSequence", "length", "()I", .str s :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 (UInt32.ofNat s.length) :: rest })
    | _, _, _, _ => .inr none
  stepInvokeStatic st cls method desc :=
    match cls, method, desc, st.stack with
    | "androidx/compose/ui/util/MathHelpersKt", "lerp", "(IIF)I", f :: b :: a :: rest =>
      match a.asI32?, b.asI32?, f.asF32? with
      | some va, some vb, some vf =>
        .inl (some { st with pc := st.pc + 1, stack := .i32 (lerpInt va vb vf) :: rest })
      | _, _, _ => .inr none
    | "androidx/compose/ui/unit/Dp", "constructor-impl", "(F)F", _ =>
      .inl (some { st with pc := st.pc + 1 })
    | "kotlin/text/StringsKt", "toLongOrNull", "(Ljava/lang/String;)Ljava/lang/Long;", .str s :: rest =>
      let v : UtilVal := match parseLong s with | some l => .boxedLong l | none => .null
      .inl (some { st with pc := st.pc + 1, stack := v :: rest })
    | "kotlin/text/StringsKt", "toDoubleOrNull", "(Ljava/lang/String;)Ljava/lang/Double;", .str s :: rest =>
      let v : UtilVal := match parseDouble s with | some d => .f64 d | none => .null
      .inl (some { st with pc := st.pc + 1, stack := v :: rest })
    | "java/lang/Double", "isNaN", "(D)Z", d :: rest =>
      match d.asF64? with
      | some vd => .inl (some { st with pc := st.pc + 1, stack := .i32 (if vd.isNaN then 1 else 0) :: rest })
      | none => .inr none
    | "com/alexvanyo/composelife/ui/util/TrimWhitespaceKt", "trimWhitespace",
        "(Landroidx/compose/foundation/text/input/InputTransformation;)Landroidx/compose/foundation/text/input/InputTransformation;",
        x :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .pair (.str "trim") x :: rest })
    | "androidx/compose/foundation/text/input/InputTransformationKt", "then",
        "(Landroidx/compose/foundation/text/input/InputTransformation;Landroidx/compose/foundation/text/input/InputTransformation;)Landroidx/compose/foundation/text/input/InputTransformation;",
        b :: a :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .pair a b :: rest })
    | _, _, _, _ => .inr none

abbrev uiUtilHooks : Jvm.JvmHooks Empty Unit := mkUiUtilHooks

/-! ### WindowInsetsLerpKt -/

theorem windowInsetsLerp_lerp_equiv (frac : Float32) :
    ∃ addr endSt,
      Jvm.runJvmRes uiUtilHooks 20 WindowInsetsLerpKt_lerp_prog
        (initUtilState [(0, .allocRef "start"), (1, .allocRef "stop"), (2, .f32 frac)]) =
        some (.heapRef addr, endSt) ∧
      utilGetField? endSt.jvmHeap addr wiLerpCls "$fraction" = some (.f32 frac) :=
  ⟨0, _, rfl, rfl⟩

theorem windowInsetsLerp_1_init_equiv (frac : Float32) :
    let (addr, h) := ({} : Jvm.JvmHeap Empty).alloc (.instance wiLerpCls [])
    ∃ endSt,
      Jvm.runJvmRes uiUtilHooks 20 WindowInsetsLerpKt_lerp_1_init_prog
        (initUtilState [(0, .heapRef addr), (1, .allocRef "start"), (2, .allocRef "stop"), (3, .f32 frac)] h) =
        some (.unit, endSt) ∧
      utilGetField? endSt.jvmHeap addr wiLerpCls "$fraction" = some (.f32 frac) :=
  ⟨_, rfl, rfl⟩

theorem windowInsetsLerp_1_sides_equiv
    (s t : UInt32 × UInt32 × UInt32 × UInt32)
    (lerpInt : UInt32 → UInt32 → Float32 → UInt32) (frac : Float32) :
    let (addr, h) := ({} : Jvm.JvmHeap Empty).alloc (.instance wiLerpCls
      [("$start", .allocRef "start"), ("$stop", .allocRef "stop"), ("$fraction", .f32 frac)])
    let hooks := mkUiUtilHooks (insetsStart := s) (insetsStop := t) (lerpInt := lerpInt)
    Jvm.runJvm hooks 25 WindowInsetsLerpKt_lerp_1_getLeft_prog
      (initUtilState [(0, .heapRef addr), (1, .allocRef "D"), (2, .allocRef "LD")] h) =
      some (.i32 (lerpInt s.1 t.1 frac)) ∧
    Jvm.runJvm hooks 25 WindowInsetsLerpKt_lerp_1_getTop_prog
      (initUtilState [(0, .heapRef addr), (1, .allocRef "D")] h) =
      some (.i32 (lerpInt s.2.1 t.2.1 frac)) ∧
    Jvm.runJvm hooks 25 WindowInsetsLerpKt_lerp_1_getRight_prog
      (initUtilState [(0, .heapRef addr), (1, .allocRef "D"), (2, .allocRef "LD")] h) =
      some (.i32 (lerpInt s.2.2.1 t.2.2.1 frac)) ∧
    Jvm.runJvm hooks 25 WindowInsetsLerpKt_lerp_1_getBottom_prog
      (initUtilState [(0, .heapRef addr), (1, .allocRef "D")] h) =
      some (.i32 (lerpInt s.2.2.2 t.2.2.2 frac)) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### PaddingValuesExtensionsKt -/

theorem paddingValues_plus_equiv :
    ∃ addr endSt,
      Jvm.runJvmRes uiUtilHooks 20 PaddingValuesExtensionsKt_plus_prog
        (initUtilState [(0, .allocRef "a"), (1, .allocRef "b")]) = some (.heapRef addr, endSt) ∧
      utilGetField? endSt.jvmHeap addr padPlusCls "$this_plus" = some (.allocRef "a") :=
  ⟨0, _, rfl, rfl⟩

theorem paddingValues_plus_1_init_equiv :
    let (addr, h) := ({} : Jvm.JvmHeap Empty).alloc (.instance padPlusCls [])
    ∃ endSt,
      Jvm.runJvmRes uiUtilHooks 20 PaddingValuesExtensionsKt_plus_1_init_prog
        (initUtilState [(0, .heapRef addr), (1, .allocRef "a"), (2, .allocRef "b")] h) =
        some (.unit, endSt) ∧
      utilGetField? endSt.jvmHeap addr padPlusCls "$other" = some (.allocRef "b") :=
  ⟨_, rfl, rfl⟩

theorem paddingValues_plus_1_sides_equiv (a b : Float32 × Float32 × Float32 × Float32) :
    let (addr, h) := ({} : Jvm.JvmHeap Empty).alloc (.instance padPlusCls
      [("$this_plus", .allocRef "a"), ("$other", .allocRef "b")])
    let hooks := mkUiUtilHooks (padA := a) (padB := b)
    Jvm.runJvm hooks 30 PaddingValuesExtensionsKt_plus_1_calculateLeftPadding_prog
      (initUtilState [(0, .heapRef addr), (1, .allocRef "LD")] h) = some (.f32 (a.1 + b.1 + (0.0 : Float32))) ∧
    Jvm.runJvm hooks 30 PaddingValuesExtensionsKt_plus_1_calculateTopPadding_prog
      (initUtilState [(0, .heapRef addr)] h) = some (.f32 (a.2.1 + b.2.1 + (0.0 : Float32))) ∧
    Jvm.runJvm hooks 30 PaddingValuesExtensionsKt_plus_1_calculateRightPadding_prog
      (initUtilState [(0, .heapRef addr), (1, .allocRef "LD")] h) = some (.f32 (a.2.2.1 + b.2.2.1 + (0.0 : Float32))) ∧
    Jvm.runJvm hooks 30 PaddingValuesExtensionsKt_plus_1_calculateBottomPadding_prog
      (initUtilState [(0, .heapRef addr)] h) = some (.f32 (a.2.2.2 + b.2.2.2 + (0.0 : Float32))) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### NonNegativeLong & NonNegativeDouble -/

theorem nonNegativeLong_basics_equiv :
    Jvm.runJvm uiUtilHooks 10 NonNegativeLong_init_prog (initUtilState [(0, .allocRef nnLongCls)]) = some .unit ∧
    Jvm.runJvm uiUtilHooks 10 NonNegativeLong_applySemantics_prog
      (initUtilState [(0, .allocRef nnLongCls), (1, .allocRef "S")]) = some .unit ∧
    (∃ endSt,
      Jvm.runJvmRes uiUtilHooks 30 NonNegativeLong_clinit_prog (initUtilState []) = some (.unit, endSt) ∧
      endSt.jvmHeap.getStatic? nnLongCls "keyboardOptions" = some (.heapRef 1)) ∧
    (let h := ({} : Jvm.JvmHeap Empty).setStatic nnLongCls "keyboardOptions" (.allocRef "KO")
     Jvm.runJvm uiUtilHooks 10 NonNegativeLong_getKeyboardOptions_prog (initUtilState [] h) = some (.allocRef "KO")) ∧
    Jvm.runJvm uiUtilHooks 15 NonNegativeLongKt_nonNegativeLong_prog
      (initUtilState [(0, .allocRef "T")]) =
      some (.pair (.pair (.str "trim") (.allocRef "T")) (.allocRef nnLongCls)) :=
  ⟨rfl, rfl, ⟨_, rfl, rfl⟩, rfl, rfl⟩

theorem nonNegativeLong_transformInput_equiv :
    (let (buf, h) := ({} : Jvm.JvmHeap Empty).alloc (.instance "TextFieldBuffer" [("text", .str ""), ("reverted", .i32 0)])
     ∃ endSt, Jvm.runJvmRes uiUtilHooks 40 NonNegativeLong_transformInput_prog
       (initUtilState [(0, .allocRef nnLongCls), (1, .heapRef buf)] h) = some (.unit, endSt) ∧
       utilGetField? endSt.jvmHeap buf "TextFieldBuffer" "reverted" = some (.i32 0)) ∧
    (let (buf, h) := ({} : Jvm.JvmHeap Empty).alloc (.instance "TextFieldBuffer" [("text", .str "abc"), ("reverted", .i32 0)])
     ∃ endSt, Jvm.runJvmRes (mkUiUtilHooks (parseLong := fun _ => none)) 40 NonNegativeLong_transformInput_prog
       (initUtilState [(0, .allocRef nnLongCls), (1, .heapRef buf)] h) = some (.unit, endSt) ∧
       utilGetField? endSt.jvmHeap buf "TextFieldBuffer" "reverted" = some (.i32 1)) ∧
    (let (buf, h) := ({} : Jvm.JvmHeap Empty).alloc (.instance "TextFieldBuffer" [("text", .str "-1"), ("reverted", .i32 0)])
     ∃ endSt, Jvm.runJvmRes (mkUiUtilHooks (parseLong := fun _ => some ((-1 : Int64).toUInt64))) 40 NonNegativeLong_transformInput_prog
       (initUtilState [(0, .allocRef nnLongCls), (1, .heapRef buf)] h) = some (.unit, endSt) ∧
       utilGetField? endSt.jvmHeap buf "TextFieldBuffer" "reverted" = some (.i32 1)) ∧
    (let (buf, h) := ({} : Jvm.JvmHeap Empty).alloc (.instance "TextFieldBuffer" [("text", .str "42"), ("reverted", .i32 0)])
     ∃ endSt, Jvm.runJvmRes (mkUiUtilHooks (parseLong := fun _ => some 42)) 40 NonNegativeLong_transformInput_prog
       (initUtilState [(0, .allocRef nnLongCls), (1, .heapRef buf)] h) = some (.unit, endSt) ∧
       utilGetField? endSt.jvmHeap buf "TextFieldBuffer" "reverted" = some (.i32 0)) :=
  ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩

theorem nonNegativeDouble_basics_equiv :
    Jvm.runJvm uiUtilHooks 10 NonNegativeDouble_init_prog (initUtilState [(0, .allocRef nnDoubleCls)]) = some .unit ∧
    Jvm.runJvm uiUtilHooks 10 NonNegativeDouble_applySemantics_prog
      (initUtilState [(0, .allocRef nnDoubleCls), (1, .allocRef "S")]) = some .unit ∧
    (∃ endSt,
      Jvm.runJvmRes uiUtilHooks 30 NonNegativeDouble_clinit_prog (initUtilState []) = some (.unit, endSt) ∧
      endSt.jvmHeap.getStatic? nnDoubleCls "keyboardOptions" = some (.heapRef 1)) ∧
    (let h := ({} : Jvm.JvmHeap Empty).setStatic nnDoubleCls "keyboardOptions" (.allocRef "KO")
     Jvm.runJvm uiUtilHooks 10 NonNegativeDouble_getKeyboardOptions_prog (initUtilState [] h) = some (.allocRef "KO")) ∧
    Jvm.runJvm uiUtilHooks 15 NonNegativeDoubleKt_nonNegativeDouble_prog
      (initUtilState [(0, .allocRef "T")]) =
      some (.pair (.pair (.str "trim") (.allocRef "T")) (.allocRef nnDoubleCls)) :=
  ⟨rfl, rfl, ⟨_, rfl, rfl⟩, rfl, rfl⟩

theorem nonNegativeDouble_transformInput_equiv :
    (let (buf, h) := ({} : Jvm.JvmHeap Empty).alloc (.instance "TextFieldBuffer" [("text", .str ""), ("reverted", .i32 0)])
     ∃ endSt, Jvm.runJvmRes uiUtilHooks 40 NonNegativeDouble_transformInput_prog
       (initUtilState [(0, .allocRef nnDoubleCls), (1, .heapRef buf)] h) = some (.unit, endSt) ∧
       utilGetField? endSt.jvmHeap buf "TextFieldBuffer" "reverted" = some (.i32 0)) ∧
    (let (buf, h) := ({} : Jvm.JvmHeap Empty).alloc (.instance "TextFieldBuffer" [("text", .str "NaN"), ("reverted", .i32 0)])
     ∃ endSt, Jvm.runJvmRes (mkUiUtilHooks (parseDouble := fun _ => some (0.0 / 0.0))) 50 NonNegativeDouble_transformInput_prog
       (initUtilState [(0, .allocRef nnDoubleCls), (1, .heapRef buf)] h) = some (.unit, endSt) ∧
       utilGetField? endSt.jvmHeap buf "TextFieldBuffer" "reverted" = some (.i32 1)) ∧
    (let (buf, h) := ({} : Jvm.JvmHeap Empty).alloc (.instance "TextFieldBuffer" [("text", .str "-1.5"), ("reverted", .i32 0)])
     ∃ endSt, Jvm.runJvmRes (mkUiUtilHooks (parseDouble := fun _ => some (-1.5))) 50 NonNegativeDouble_transformInput_prog
       (initUtilState [(0, .allocRef nnDoubleCls), (1, .heapRef buf)] h) = some (.unit, endSt) ∧
       utilGetField? endSt.jvmHeap buf "TextFieldBuffer" "reverted" = some (.i32 1)) ∧
    (let (buf, h) := ({} : Jvm.JvmHeap Empty).alloc (.instance "TextFieldBuffer" [("text", .str "3.5"), ("reverted", .i32 0)])
     ∃ endSt, Jvm.runJvmRes (mkUiUtilHooks (parseDouble := fun _ => some 3.5)) 50 NonNegativeDouble_transformInput_prog
       (initUtilState [(0, .allocRef nnDoubleCls), (1, .heapRef buf)] h) = some (.unit, endSt) ∧
       utilGetField? endSt.jvmHeap buf "TextFieldBuffer" "reverted" = some (.i32 0)) :=
  ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩

end UiCommon.KotlinJvmVerification
