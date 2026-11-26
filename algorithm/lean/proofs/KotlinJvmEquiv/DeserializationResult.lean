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
import models.DeserializationResultModel
import theorems.DeserializationResultModelTheorems

namespace Algorithm.KotlinJvmVerification
open Algorithm.KotlinJvmBytecode
open Algorithm.KotlinModel

private abbrev DrVal := Jvm.JvmVal Empty
private abbrev DrState := Jvm.JvmState Empty Unit

private def initDrState (slots : List (Nat × DrVal)) (jh : Jvm.JvmHeap Empty := {}) : DrState :=
  Jvm.initJvmState slots (.i32 0) () jh

private def drGetField? (h : Jvm.JvmHeap Empty) (addr : Nat) (cls field : String) : Option DrVal :=
  match h.get? addr with
  | some obj => obj.getField? (fun a b => a == b) cls field
  | none => none

private def drSetField (h : Jvm.JvmHeap Empty) (addr : Nat) (cls field : String) (v : DrVal) : Jvm.JvmHeap Empty :=
  match h.get? addr with
  | some obj =>
    match obj.setField (fun a b => a == b) cls field v with
    | some obj' => h.set addr obj'
    | none => h
  | none => h

/-- Java `String.hashCode()` for ASCII strings (`h = 31 * h + c`). -/
def javaStringHashCode (s : String) : UInt32 :=
  s.toList.foldl (fun h c => h * 31 + UInt32.ofNat c.toNat) 0

private def deserCls : String := "com/alexvanyo/composelife/model/DeserializationResult"
private def succCls : String := "com/alexvanyo/composelife/model/DeserializationResult$Successful"
private def unsuccCls : String := "com/alexvanyo/composelife/model/DeserializationResult$Unsuccessful"

/-- Encode `CellStateFormatModel` as its JVM singleton `INSTANCE` reference. -/
def formatVal : CellStateFormatModel → DrVal
  | .plaintext => .allocRef "com/alexvanyo/composelife/model/CellStateFormat$FixedFormat$Plaintext"
  | .life => .allocRef "com/alexvanyo/composelife/model/CellStateFormat$Life"
  | .runLengthEncoding => .allocRef "com/alexvanyo/composelife/model/CellStateFormat$FixedFormat$RunLengthEncoding"
  | .macrocell => .allocRef "com/alexvanyo/composelife/model/CellStateFormat$FixedFormat$Macrocell"
  | .unknown => .allocRef "com/alexvanyo/composelife/model/CellStateFormat$Unknown"

/-- Encode `DeserResultModel` onto the JVM heap as a `Successful` or `Unsuccessful` instance. -/
def allocDeserResult (jh : Jvm.JvmHeap Empty) : DeserResultModel → Nat × Jvm.JvmHeap Empty
  | .successful clean id =>
    jh.alloc (.instance succCls [("warningsEmpty", .i32 (if clean then 1 else 0)), ("id", .i32 (UInt32.ofNat id))])
  | .unsuccessful id =>
    jh.alloc (.instance unsuccCls [("id", .i32 (UInt32.ofNat id))])

/-- Hooks for `DeserializationResultKt` and `CellStateFormatKt`. -/
def deserHooks : Jvm.JvmHooks Empty Unit where
  isSubtypeOf sub sup :=
    sub == sup ||
    (sub == succCls && sup == deserCls) ||
    (sub == unsuccCls && sup == deserCls) ||
    sup == "java/lang/Object"
  checkCast cls v :=
    match cls, v with
    | "com/alexvanyo/composelife/model/CellStateFormat",
        .allocRef "com/alexvanyo/composelife/model/CellStateFormat$FixedFormat$Plaintext" => some v
    | "com/alexvanyo/composelife/model/CellStateFormat",
        .allocRef "com/alexvanyo/composelife/model/CellStateFormat$Life" => some v
    | "com/alexvanyo/composelife/model/CellStateFormat",
        .allocRef "com/alexvanyo/composelife/model/CellStateFormat$FixedFormat$RunLengthEncoding" => some v
    | "com/alexvanyo/composelife/model/CellStateFormat",
        .allocRef "com/alexvanyo/composelife/model/CellStateFormat$FixedFormat$Macrocell" => some v
    | "com/alexvanyo/composelife/model/CellStateFormat",
        .allocRef "com/alexvanyo/composelife/model/CellStateFormat$Unknown" => some v
    | _, _ => Jvm.defaultCheckCast (fun _ a => nomatch a) cls v
  resolveStatic _st cls field _desc :=
    match cls, field with
    | "com/alexvanyo/composelife/model/CellStateFormat$FixedFormat$Plaintext", "INSTANCE" =>
      some (formatVal .plaintext)
    | "com/alexvanyo/composelife/model/CellStateFormat$Life", "INSTANCE" =>
      some (formatVal .life)
    | "com/alexvanyo/composelife/model/CellStateFormat$FixedFormat$RunLengthEncoding", "INSTANCE" =>
      some (formatVal .runLengthEncoding)
    | "com/alexvanyo/composelife/model/CellStateFormat$FixedFormat$Macrocell", "INSTANCE" =>
      some (formatVal .macrocell)
    | "com/alexvanyo/composelife/model/CellStateFormat$Unknown", "INSTANCE" =>
      some (formatVal .unknown)
    | _, _ => none
  stepNewClass st cls :=
    let (addr, h') := st.jvmHeap.alloc (.instance cls [])
    .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: st.stack, jvmHeap := h' })
  stepInvokeSpecial st cls method desc :=
    match cls, method, desc, st.stack with
    | "java/lang/UnsupportedOperationException", "<init>", "(Ljava/lang/String;)V", _ :: _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := rest })
    | "kotlin/NoWhenBranchMatchedException", "<init>", "()V", _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := rest })
    | _, _, _, _ => .inr none
  stepInvokeVirtual st cls method desc :=
    match cls, method, desc, st.stack with
    | "com/alexvanyo/composelife/model/DeserializationResult$Successful", "getWarnings",
        "()Ljava/util/List;", .heapRef addr :: rest =>
      match drGetField? st.jvmHeap addr succCls "warningsEmpty" with
      | some w => .inl (some { st with pc := st.pc + 1, stack := w :: rest })
      | none => .inr none
    | "java/lang/String", "hashCode", "()I", .str s :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 (javaStringHashCode s) :: rest })
    | "java/lang/String", "equals", "(Ljava/lang/Object;)Z", .str b :: .str a :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 (if a == b then 1 else 0) :: rest })
    | _, _, _, _ => .inr none
  stepInvokeInterface st cls method desc :=
    match cls, method, desc, st.stack with
    | "java/util/List", "isEmpty", "()Z", .i32 flag :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 flag :: rest })
    | "java/lang/Iterable", "iterator", "()Ljava/util/Iterator;", .heapRef listAddr :: rest =>
      let (itAddr, h') := st.jvmHeap.alloc (.instance "Iterator" [("list", .heapRef listAddr), ("idx", .i32 0)])
      .inl (some { st with pc := st.pc + 1, stack := .heapRef itAddr :: rest, jvmHeap := h' })
    | "java/util/Iterator", "hasNext", "()Z", .heapRef itAddr :: rest =>
      match drGetField? st.jvmHeap itAddr "Iterator" "list", drGetField? st.jvmHeap itAddr "Iterator" "idx" with
      | some (.heapRef listAddr), some (.i32 idx) =>
        match st.jvmHeap.get? listAddr with
        | some (.objArray _ elems) =>
          .inl (some { st with pc := st.pc + 1, stack := .i32 (if idx.toNat < elems.size then 1 else 0) :: rest })
        | _ => .inr none
      | _, _ => .inr none
    | "java/util/Iterator", "next", "()Ljava/lang/Object;", .heapRef itAddr :: rest =>
      match drGetField? st.jvmHeap itAddr "Iterator" "list", drGetField? st.jvmHeap itAddr "Iterator" "idx" with
      | some (.heapRef listAddr), some (.i32 idx) =>
        match st.jvmHeap.get? listAddr with
        | some (.objArray _ elems) =>
          match elems[idx.toNat]? with
          | some elem =>
            let h' := drSetField st.jvmHeap itAddr "Iterator" "idx" (.i32 (idx + 1))
            .inl (some { st with pc := st.pc + 1, stack := elem :: rest, jvmHeap := h' })
          | none => .inr none
        | _ => .inr none
      | _, _ => .inr none
    | _, _, _, _ => .inr none

/-! ### DeserializationResultKt.isSuccessful -/

theorem deserializationResult_isSuccessful_equiv (r : DeserResultModel) :
    let (addr, h) := allocDeserResult {} r
    Jvm.runJvm deserHooks 30 DeserializationResultKt_isSuccessful_prog
      (initDrState [(0, .heapRef addr)] h) =
      some (.i32 (if r.isSuccessful then 1 else 0)) := by
  cases r with
  | successful clean id => cases clean <;> rfl
  | unsuccessful id => rfl

/-! ### DeserializationResultKt.reduceToSuccessful -/

theorem deserializationResult_reduceToSuccessful_empty_throws :
    let (listAddr, h) := ({} : Jvm.JvmHeap Empty).alloc (.objArray "java/lang/Iterable" #[])
    Jvm.runJvm deserHooks 40 DeserializationResultKt_reduceToSuccessful_prog
      (initDrState [(0, .heapRef listAddr)] h) = none := rfl

theorem deserializationResult_reduceToSuccessful_singleton_equiv (r : DeserResultModel) :
    let (a0, h0) := allocDeserResult {} r
    let (listAddr, h1) := h0.alloc (.objArray "java/lang/Iterable" #[.heapRef a0])
    Jvm.runJvm deserHooks 60 DeserializationResultKt_reduceToSuccessful_prog
      (initDrState [(0, .heapRef listAddr)] h1) = some (.heapRef a0) := by
  cases r with
  | successful clean id => cases clean <;> rfl
  | unsuccessful id => rfl

private theorem dr_hiteZ (v : DrVal) (t e : Option DrVal) :
    deserHooks.iteZero? v t e =
      match deserHooks.isZero? v with | some true => t | some false => e | none => none := by
  dsimp only [deserHooks]
  cases v.asI32? with
  | none => rfl
  | some x => cases h : (x == 0) <;> simp [h, Jvm.defaultIteVal] <;> split <;> rfl

private theorem dr_hiteNZ (v : DrVal) (t e : Option DrVal) :
    deserHooks.iteNonZero? v t e =
      match deserHooks.isZero? v with | some true => e | some false => t | none => none := by
  dsimp only [deserHooks]
  cases v.asI32? with
  | none => rfl
  | some x => cases h : (x == 0) <;> simp [h, Jvm.defaultIteVal] <;> split <;> rfl

set_option maxRecDepth 4000 in
theorem deserializationResult_reduceToSuccessful_pair_unsuccessful_equiv (idA : Nat) (b : DeserResultModel) :
    let a : DeserResultModel := .unsuccessful idA
    let (a0, h0) := allocDeserResult {} a
    let (a1, h1) := allocDeserResult h0 b
    let (listAddr, h2) := h1.alloc (.objArray "java/lang/Iterable" #[.heapRef a0, .heapRef a1])
    Jvm.runJvm deserHooks 120 DeserializationResultKt_reduceToSuccessful_prog
      (initDrState [(0, .heapRef listAddr)] h2) =
      some (.heapRef (if reduceToSuccessfulPicksFirst a b then a0 else a1)) := by
  apply Jvm.runJvm_of_runJvmValFast0 deserHooks dr_hiteZ dr_hiteNZ 120 _ _ _ rfl
  cases b with
  | unsuccessful idB => rfl
  | successful cleanB idB => cases cleanB <;> rfl

set_option maxRecDepth 4000 in
set_option maxHeartbeats 400000 in
theorem deserializationResult_reduceToSuccessful_pair_successful_clean_equiv (idA : Nat) (b : DeserResultModel) :
    let a : DeserResultModel := .successful true idA
    let (a0, h0) := allocDeserResult {} a
    let (a1, h1) := allocDeserResult h0 b
    let (listAddr, h2) := h1.alloc (.objArray "java/lang/Iterable" #[.heapRef a0, .heapRef a1])
    Jvm.runJvm deserHooks 120 DeserializationResultKt_reduceToSuccessful_prog
      (initDrState [(0, .heapRef listAddr)] h2) =
      some (.heapRef (if reduceToSuccessfulPicksFirst a b then a0 else a1)) := by
  apply Jvm.runJvm_of_runJvmValFast0 deserHooks dr_hiteZ dr_hiteNZ 120 _ _ _ rfl
  cases b with
  | unsuccessful idB => rfl
  | successful cleanB idB => cases cleanB <;> rfl

set_option maxRecDepth 4000 in
set_option maxHeartbeats 400000 in
theorem deserializationResult_reduceToSuccessful_pair_successful_warn_equiv (idA : Nat) (b : DeserResultModel) :
    let a : DeserResultModel := .successful false idA
    let (a0, h0) := allocDeserResult {} a
    let (a1, h1) := allocDeserResult h0 b
    let (listAddr, h2) := h1.alloc (.objArray "java/lang/Iterable" #[.heapRef a0, .heapRef a1])
    Jvm.runJvm deserHooks 120 DeserializationResultKt_reduceToSuccessful_prog
      (initDrState [(0, .heapRef listAddr)] h2) =
      some (.heapRef (if reduceToSuccessfulPicksFirst a b then a0 else a1)) := by
  apply Jvm.runJvm_of_runJvmValFast0 deserHooks dr_hiteZ dr_hiteNZ 120 _ _ _ rfl
  cases b with
  | unsuccessful idB => rfl
  | successful cleanB idB => cases cleanB <;> rfl

theorem deserializationResult_reduceToSuccessful_pair_equiv (a b : DeserResultModel) :
    let (a0, h0) := allocDeserResult {} a
    let (a1, h1) := allocDeserResult h0 b
    let (listAddr, h2) := h1.alloc (.objArray "java/lang/Iterable" #[.heapRef a0, .heapRef a1])
    Jvm.runJvm deserHooks 120 DeserializationResultKt_reduceToSuccessful_prog
      (initDrState [(0, .heapRef listAddr)] h2) =
      some (.heapRef (if reduceToSuccessfulPicksFirst a b then a0 else a1)) := by
  cases a with
  | unsuccessful idA => exact deserializationResult_reduceToSuccessful_pair_unsuccessful_equiv idA b
  | successful cleanA idA =>
    cases cleanA
    · exact deserializationResult_reduceToSuccessful_pair_successful_warn_equiv idA b
    · exact deserializationResult_reduceToSuccessful_pair_successful_clean_equiv idA b

/-! ### CellStateFormatKt.fromFileExtension -/

theorem cellStateFormat_fromFileExtension_null_equiv :
    Jvm.runJvm deserHooks 40 CellStateFormatKt_fromFileExtension_prog
      (initDrState [(0, .allocRef "Companion"), (1, .null)]) = some (formatVal .unknown) := rfl

theorem cellStateFormat_fromFileExtension_known_equiv :
    Jvm.runJvm deserHooks 40 CellStateFormatKt_fromFileExtension_prog
      (initDrState [(0, .allocRef "Companion"), (1, .str "cells")]) = some (formatVal .plaintext) ∧
    Jvm.runJvm deserHooks 40 CellStateFormatKt_fromFileExtension_prog
      (initDrState [(0, .allocRef "Companion"), (1, .str "lif")]) = some (formatVal .life) ∧
    Jvm.runJvm deserHooks 40 CellStateFormatKt_fromFileExtension_prog
      (initDrState [(0, .allocRef "Companion"), (1, .str "life")]) = some (formatVal .life) ∧
    Jvm.runJvm deserHooks 40 CellStateFormatKt_fromFileExtension_prog
      (initDrState [(0, .allocRef "Companion"), (1, .str "rle")]) = some (formatVal .runLengthEncoding) ∧
    Jvm.runJvm deserHooks 40 CellStateFormatKt_fromFileExtension_prog
      (initDrState [(0, .allocRef "Companion"), (1, .str "mc")]) = some (formatVal .macrocell) ∧
    Jvm.runJvm deserHooks 40 CellStateFormatKt_fromFileExtension_prog
      (initDrState [(0, .allocRef "Companion"), (1, .str "txt")]) = some (formatVal .unknown) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Algorithm.KotlinJvmVerification
