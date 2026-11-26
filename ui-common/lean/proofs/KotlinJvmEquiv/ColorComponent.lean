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
import models.ColorComponentModel
import theorems.ColorComponentModelTheorems

namespace UiCommon.KotlinJvmVerification
open UiCommon.KotlinJvmBytecode
open UiCommon.KotlinModel

private abbrev CcVal := Jvm.JvmVal Empty
private abbrev CcState := Jvm.JvmState Empty Unit

private def initCcState (slots : List (Nat × CcVal)) (jh : Jvm.JvmHeap Empty := {}) : CcState :=
  Jvm.initJvmState slots (.i32 0) () jh

/-- Encode `RgbComponent` as its JVM singleton `INSTANCE` reference. -/
def rgbCompVal : RgbComponent → CcVal
  | .red => .str "com/alexvanyo/composelife/ui/util/ColorComponent$RgbIntComponent$Red"
  | .green => .str "com/alexvanyo/composelife/ui/util/ColorComponent$RgbIntComponent$Green"
  | .blue => .str "com/alexvanyo/composelife/ui/util/ColorComponent$RgbIntComponent$Blue"

/--
Hooks for `ColorComponentKt`:
- `Color` (`ULong` / `Long`) is represented by its 32-bit ARGB payload in the low 32 bits (`toArgb-8_81llA`
  returns `color.toUInt32`; `ColorKt.Color(r, g, b, a)` returns `(packArgb r g b a).toUInt64`).
- `ColorComponentKt.get-DxMtmZc` delegates to `getColorComponent`.
-/
def colorCompHooks : Jvm.JvmHooks Empty Unit where
  checkCast cls v :=
    match cls, v with
    | "com/alexvanyo/composelife/ui/util/ColorComponent$RgbIntComponent",
        .str "com/alexvanyo/composelife/ui/util/ColorComponent$RgbIntComponent$Red" => some v
    | "com/alexvanyo/composelife/ui/util/ColorComponent$RgbIntComponent",
        .str "com/alexvanyo/composelife/ui/util/ColorComponent$RgbIntComponent$Green" => some v
    | "com/alexvanyo/composelife/ui/util/ColorComponent$RgbIntComponent",
        .str "com/alexvanyo/composelife/ui/util/ColorComponent$RgbIntComponent$Blue" => some v
    | _, _ => Jvm.defaultCheckCast (fun _ a => nomatch a) cls v
  resolveStatic _st cls field _desc :=
    match cls, field with
    | "com/alexvanyo/composelife/ui/util/ColorComponent$RgbIntComponent$Red", "INSTANCE" =>
      some (rgbCompVal .red)
    | "com/alexvanyo/composelife/ui/util/ColorComponent$RgbIntComponent$Green", "INSTANCE" =>
      some (rgbCompVal .green)
    | "com/alexvanyo/composelife/ui/util/ColorComponent$RgbIntComponent$Blue", "INSTANCE" =>
      some (rgbCompVal .blue)
    | _, _ => none
  stepInvokeStatic st cls method desc :=
    match cls, method, desc, st.stack with
    | "androidx/compose/ui/graphics/ColorKt", "toArgb-8_81llA", "(J)I", v :: rest =>
      match v.asI64? with
      | some c => .inl (some { st with pc := st.pc + 1, stack := .i32 c.toUInt32 :: rest })
      | none => .inr none
    | "androidx/compose/ui/graphics/ColorKt", "Color", "(IIII)J", a :: b :: g :: r :: rest =>
      match r.asI32?, g.asI32?, b.asI32?, a.asI32? with
      | some vr, some vg, some vb, some va =>
        .inl (some { st with pc := st.pc + 1, stack := .i64 (packArgb vr vg vb va).toUInt64 :: rest })
      | _, _, _, _ => .inr none
    | "com/alexvanyo/composelife/ui/util/ColorComponentKt", "get-DxMtmZc",
        "(JLcom/alexvanyo/composelife/ui/util/ColorComponent$RgbIntComponent;)I",
        comp :: c :: rest =>
      match c.asI64? with
      | some vc =>
        match comp with
        | .str "com/alexvanyo/composelife/ui/util/ColorComponent$RgbIntComponent$Red" =>
          .inl (some { st with pc := st.pc + 1, stack := .i32 (getColorComponent vc.toUInt32 .red) :: rest })
        | .str "com/alexvanyo/composelife/ui/util/ColorComponent$RgbIntComponent$Green" =>
          .inl (some { st with pc := st.pc + 1, stack := .i32 (getColorComponent vc.toUInt32 .green) :: rest })
        | .str "com/alexvanyo/composelife/ui/util/ColorComponent$RgbIntComponent$Blue" =>
          .inl (some { st with pc := st.pc + 1, stack := .i32 (getColorComponent vc.toUInt32 .blue) :: rest })
        | _ => .inr none
      | none => .inr none
    | _, _, _, _ => .inr none

/-! ### Channel extractors -/

theorem colorComponent_getAlpha_equiv (argb : UInt32) :
    Jvm.runJvm colorCompHooks 15 ColorComponentKt_getAlpha_prog
      (initCcState [(0, .i32 argb)]) = some (.i32 (argbAlpha argb)) := rfl

theorem colorComponent_getRed_equiv (argb : UInt32) :
    Jvm.runJvm colorCompHooks 15 ColorComponentKt_getRed_prog
      (initCcState [(0, .i32 argb)]) = some (.i32 (argbRed argb)) := rfl

theorem colorComponent_getGreen_equiv (argb : UInt32) :
    Jvm.runJvm colorCompHooks 15 ColorComponentKt_getGreen_prog
      (initCcState [(0, .i32 argb)]) = some (.i32 (argbGreen argb)) := rfl

theorem colorComponent_getBlue_equiv (argb : UInt32) :
    Jvm.runJvm colorCompHooks 15 ColorComponentKt_getBlue_prog
      (initCcState [(0, .i32 argb)]) = some (.i32 (argbBlue argb)) := rfl

/-! ### get(RgbIntComponent) & withComponent(RgbIntComponent, Int) -/

set_option maxRecDepth 4000

private theorem cc_hiteZ (v : CcVal) (t e : Option CcVal) :
    colorCompHooks.iteZero? v t e =
      match colorCompHooks.isZero? v with | some true => t | some false => e | none => none := by
  dsimp only [colorCompHooks]
  cases v.asI32? with
  | none => rfl
  | some x => cases h : (x == 0) <;> simp [h, Jvm.defaultIteVal] <;> split <;> rfl

private theorem cc_hiteNZ (v : CcVal) (t e : Option CcVal) :
    colorCompHooks.iteNonZero? v t e =
      match colorCompHooks.isZero? v with | some true => e | some false => t | none => none := by
  dsimp only [colorCompHooks]
  cases v.asI32? with
  | none => rfl
  | some x => cases h : (x == 0) <;> simp [h, Jvm.defaultIteVal] <;> split <;> rfl

theorem colorComponent_get_equiv (argb : UInt32) (c : RgbComponent) :
    Jvm.runJvm colorCompHooks 40 ColorComponentKt_get_prog
      (initCcState [(0, .i64 argb.toUInt64), (2, rgbCompVal c)]) =
      some (.i32 (getColorComponent argb c)) := by
  have hcast : argb.toUInt64.toUInt32 = argb := by
    apply UInt32.eq_of_toBitVec_eq; simp
  have hfast :
      Jvm.runJvmValFast colorCompHooks 40 ColorComponentKt_get_prog 0 ColorComponentKt_get_prog
        (initCcState [(0, .i64 argb.toUInt64), (2, rgbCompVal c)]) =
        some (.i32 (getColorComponent argb.toUInt64.toUInt32 c)) := by
    cases c <;> rfl
  rw [hcast] at hfast
  exact Jvm.runJvm_of_runJvmValFast0 colorCompHooks cc_hiteZ cc_hiteNZ 40 _ _ _ rfl hfast

theorem colorComponent_withComponent_equiv (argb : UInt32) (c : RgbComponent) (v : UInt32) :
    Jvm.runJvm colorCompHooks 60 ColorComponentKt_withComponent_prog
      (initCcState [(0, .i64 argb.toUInt64), (2, rgbCompVal c), (3, .i32 v)]) =
      some (.i64 (withColorComponent argb c v).toUInt64) := by
  have hcast : argb.toUInt64.toUInt32 = argb := by
    apply UInt32.eq_of_toBitVec_eq; simp
  have hfast :
      Jvm.runJvmValFast colorCompHooks 60 ColorComponentKt_withComponent_prog 0 ColorComponentKt_withComponent_prog
        (initCcState [(0, .i64 argb.toUInt64), (2, rgbCompVal c), (3, .i32 v)]) =
        some (.i64 (withColorComponent argb.toUInt64.toUInt32 c v).toUInt64) := by
    cases c <;> rfl
  rw [hcast] at hfast
  exact Jvm.runJvm_of_runJvmValFast0 colorCompHooks cc_hiteZ cc_hiteNZ 60 _ _ _ rfl hfast

end UiCommon.KotlinJvmVerification
