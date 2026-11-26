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
import models.BackstackStateModel
import theorems.BackstackStateModelTheorems

namespace Navigation.KotlinJvmVerification

open Navigation.KotlinJvmBytecode
open Navigation.KotlinModel

set_option maxRecDepth 4000

private abbrev BsVal := Jvm.JvmVal Empty
private abbrev BsState := Jvm.JvmState Empty Unit

private abbrev entryCls : String := "com/alexvanyo/composelife/navigation/BackstackEntry"
private abbrev surrCls : String := "com/alexvanyo/composelife/navigation/BackstackEntrySurrogate"
private abbrev navStateCls : String := "com/alexvanyo/composelife/navigation/NavigationState"
private abbrev ctrlCls : String := "com/alexvanyo/composelife/navigation/MutableBackstackNavigationController"
private abbrev bsStateCls : String := "com/alexvanyo/composelife/navigation/BackstackState"

private def bsIsSubtype (sub sup : String) : Bool :=
  sub == sup ||
  (sub == ctrlCls && sup == navStateCls) ||
  (sub == ctrlCls && sup == bsStateCls) ||
  (sub == bsStateCls && sup == navStateCls) ||
  (sub == "java/util/List" && (sup == "java/util/Collection" || sup == "java/lang/Iterable")) ||
  (sub == "java/util/Set" && (sup == "java/util/Collection" || sup == "java/lang/Iterable")) ||
  (sub == "java/util/LinkedHashMap" && sup == "java/util/Map") ||
  (sub == "androidx/compose/runtime/snapshots/SnapshotStateMap" && sup == "java/util/Map") ||
  (sub == "androidx/compose/runtime/MutableState" && sup == "androidx/compose/runtime/State") ||
  (sub == "com/alexvanyo/composelife/navigation/BackstackEntry$iterator$1" && sup == "kotlin/jvm/functions/Function2") ||
  (sub == "com/alexvanyo/composelife/navigation/BackstackStateKt$BackstackMapSerializer$$inlined$SurrogatingSerializer$1" &&
    sup == "kotlinx/serialization/KSerializer") ||
  (sub == "com/alexvanyo/composelife/navigation/MutableBackstackNavigationControllerKt$rememberMutableBackstackNavigationController$2$1" &&
    sup == ctrlCls) ||
  sup == "java/lang/Object"

private def bsSetHeapAt (h : Jvm.JvmHeap Empty) (addr : Nat) (obj : Jvm.HeapObj Empty) : Jvm.JvmHeap Empty :=
  { h with objects := Array.mk (h.objects.toList.set addr obj) }

private def heapGetField? (h : Jvm.JvmHeap Empty) (addr : Nat) (cls field : String) : Option BsVal :=
  match h.get? addr with
  | some obj => obj.getField? bsIsSubtype cls field
  | none => none

private def heapSetField (h : Jvm.JvmHeap Empty) (addr : Nat) (cls field : String) (v : BsVal) : Jvm.JvmHeap Empty :=
  match h.get? addr with
  | some obj =>
    match obj.setField bsIsSubtype cls field v with
    | some obj' => bsSetHeapAt h addr obj'
    | none => h
  | none => h

private def bsValEq : BsVal → BsVal → Bool
  | .str a, .str b => a == b
  | .heapRef a, .heapRef b => a == b
  | .i32 a, .i32 b => a == b
  | .null, .null => true
  | _, _ => false

/-- Allocate a `List` / `Set` wrapper pointing to a backing `.objArray`. -/
private def allocColl (h : Jvm.JvmHeap Empty) (cls : String) (elems : Array BsVal) : Nat × Jvm.JvmHeap Empty :=
  let (arrAddr, h1) := h.alloc (.objArray "java/lang/Object" elems)
  h1.alloc (.instance cls [("arr", .heapRef arrAddr)])

private def getColl? (h : Jvm.JvmHeap Empty) (addr : Nat) (cls : String) : Option (Array BsVal) :=
  match heapGetField? h addr cls "arr" with
  | some (.heapRef arrAddr) =>
    match h.get? arrAddr with
    | some (.objArray _ elems) => some elems
    | _ => none
  | _ => none

private def setColl (h : Jvm.JvmHeap Empty) (addr : Nat) (cls : String) (elems : Array BsVal) : Jvm.JvmHeap Empty :=
  match heapGetField? h addr cls "arr" with
  | some (.heapRef arrAddr) => bsSetHeapAt h arrAddr (.objArray "java/lang/Object" elems)
  | _ => h

/-- Allocate a `Map` wrapper represented as an instance with an `"entries"` backing `.objArray` of `.pair`. -/
private def allocMap (h : Jvm.JvmHeap Empty) (cls : String := "java/util/Map")
    (entries : Array (BsVal × BsVal) := #[]) : Nat × Jvm.JvmHeap Empty :=
  let pairs := Array.mk (entries.toList.map fun (k, v) => Jvm.JvmVal.pair k v)
  let (arrAddr, h1) := h.alloc (.objArray "java/lang/Object" pairs)
  h1.alloc (.instance cls [("entries", .heapRef arrAddr)])

private def getMapEntries? (h : Jvm.JvmHeap Empty) (addr : Nat) : Option (Array (BsVal × BsVal)) :=
  match heapGetField? h addr "java/util/Map" "entries" with
  | some (.heapRef arrAddr) =>
    match h.get? arrAddr with
    | some (.objArray _ elems) =>
      some (Array.mk (elems.toList.filterMap fun v => match v with | .pair k val => some (k, val) | _ => none))
    | _ => none
  | _ => none

private def mapLookup? (entries : Array (BsVal × BsVal)) (key : BsVal) : Option BsVal :=
  match entries.toList.find? fun (k, _) => bsValEq k key with
  | some (_, v) => some v
  | none => none

private def mapPut (h : Jvm.JvmHeap Empty) (addr : Nat) (key val : BsVal) : Jvm.JvmHeap Empty :=
  match heapGetField? h addr "java/util/Map" "entries" with
  | some (.heapRef arrAddr) =>
    match h.get? arrAddr with
    | some (.objArray cls elems) =>
      let filtered := elems.toList.filter fun v =>
        match v with | .pair k _ => !bsValEq k key | _ => true
      bsSetHeapAt h arrAddr (.objArray cls (Array.mk (filtered ++ [.pair key val])))
    | _ => h
  | _ => h

private def initSt (locals : List (Nat × BsVal)) (h : Jvm.JvmHeap Empty := {}) : BsState :=
  Jvm.initJvmState locals (.i32 0) () h

/--
Hooks for `BackstackEntry`, `MutableBackstackNavigationControllerKt`, and `BackstackStateKt`.
-/
def mkBackstackStateHooks
    (randomUuid : String := "rand-uuid")
    (backstackNavResult : String := "next-id")
    (predResult : Bool := true)
    (surrConvert : BsVal → BsVal := fun v => v)
    (surrRestore : BsVal → BsVal → BsVal := fun s _ => s)
    (blockResult : BsVal := .unit) :
    Jvm.JvmHooks Empty Unit where
  isSubtypeOf := bsIsSubtype
  checkCast cls v :=
    match cls, v with
    | "kotlin/uuid/Uuid", .str _ => some v
    | "kotlin/uuid/Uuid", .null => some .null
    | "java/lang/Boolean", .boxedBool _ => some v
    | "kotlin/jvm/functions/Function0", .str _ => some v
    | "kotlin/jvm/functions/Function1", .str _ => some v
    | "kotlin/reflect/KFunction", .str _ => some v
    | "kotlinx/serialization/KSerializer", .str _ => some v
    | "com/alexvanyo/composelife/navigation/BackstackValueSurrogate", _ => some v
    | "com/alexvanyo/composelife/navigation/BackstackEntry", .null => some .null
    | _, _ => Jvm.defaultCheckCast (fun _ a => nomatch a) cls v
  resolveStatic _st cls field _desc :=
    match cls, field with
    | "kotlin/uuid/Uuid", "Companion" => some (.str "Uuid$Companion")
    | "kotlin/Unit", "INSTANCE" => some .unit
    | "androidx/compose/runtime/Composer", "Companion" => some (.str "Composer$Companion")
    | "com/alexvanyo/composelife/navigation/ValueAsSurrogate", "Companion" => some (.str "ValueAsSurrogate$Companion")
    | "com/alexvanyo/composelife/navigation/BackstackEntrySurrogate", "Companion" =>
      some (.str "BackstackEntrySurrogate$Companion")
    | "com/alexvanyo/composelife/navigation/MutableBackstackNavigationControllerKt$rememberMutableBackstackNavigationController$$inlined$cache$lambda$1",
        "INSTANCE" => some (.str "cache$lambda$1")
    | "com/alexvanyo/composelife/navigation/BackstackStateKt$rememberBackstackMap$$inlined$cache$lambda$1",
        "INSTANCE" => some (.str "cache$lambda$1")
    | _, _ => none
  stepNewClass st cls :=
    match cls with
    | "java/util/LinkedHashMap" =>
      let (addr, h') := allocMap st.jvmHeap "java/util/LinkedHashMap" #[]
      .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: st.stack, jvmHeap := h' })
    | _ =>
      let (addr, h') := st.jvmHeap.alloc (.instance cls [])
      .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: st.stack, jvmHeap := h' })
  stepInvokeDynamic st name bsmArg desc :=
    match name, bsmArg, desc, st.stack with
    | "makeConcatWithConstants", _, _, _ :: _ :: _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .str "BackstackEntry(...)" :: rest })
    | "LambdaMetafactory", tag, "()Lkotlin/jvm/functions/Function1;", rest =>
      .inl (some { st with pc := st.pc + 1, stack := .str tag :: rest })
    | "LambdaMetafactory", tag, _, _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .str tag :: rest })
    | _, _, _, _ => .inr none
  stepInvokeSpecial st cls method desc :=
    match cls, method, desc, st.stack with
    | "java/lang/Object", "<init>", "()V", _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := rest })
    | "java/lang/IllegalArgumentException", "<init>", "(Ljava/lang/String;)V", _ :: _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := rest })
    | "java/util/LinkedHashMap", "<init>", "(I)V", _ :: _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := rest })
    | "com/alexvanyo/composelife/navigation/BackstackEntry", "<init>",
        "(Ljava/lang/Object;Lcom/alexvanyo/composelife/navigation/BackstackEntry;Lkotlin/uuid/Uuid;)V",
        id :: prev :: val :: .heapRef addr :: rest =>
      let h1 := heapSetField st.jvmHeap addr entryCls "value" val
      let h2 := heapSetField h1 addr entryCls "previous" prev
      let h3 := heapSetField h2 addr entryCls "id" id
      .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h3 })
    | "com/alexvanyo/composelife/navigation/BackstackEntry$iterator$1", "<init>",
        "(Lcom/alexvanyo/composelife/navigation/BackstackEntry;Lkotlin/coroutines/Continuation;)V",
        _ :: _ :: _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := rest })
    | "com/alexvanyo/composelife/navigation/BackstackEntrySurrogate", "<init>",
        "(Lkotlin/uuid/Uuid;Lkotlin/uuid/Uuid;Ljava/lang/Object;)V",
        surr :: prevId :: id :: .heapRef addr :: rest =>
      let h1 := heapSetField st.jvmHeap addr surrCls "id" id
      let h2 := heapSetField h1 addr surrCls "previousId" prevId
      let h3 := heapSetField h2 addr surrCls "surrogate" surr
      .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h3 })
    | "com/alexvanyo/composelife/navigation/BackstackStateKt$BackstackMapSerializer$$inlined$SurrogatingSerializer$1",
        "<init>", "(Ljava/lang/String;Lkotlinx/serialization/KSerializer;Lkotlin/jvm/functions/Function1;Lkotlin/jvm/functions/Function1;)V",
        _ :: _ :: _ :: _ :: _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := rest })
    | "com/alexvanyo/composelife/navigation/MutableBackstackNavigationControllerKt$rememberMutableBackstackNavigationController$2$1",
        "<init>", "(Ljava/util/Map;Landroidx/compose/runtime/MutableState;)V",
        _ :: _ :: _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := rest })
    | _, _, _, _ => .inr none
  stepInvokeVirtual st cls method desc :=
    match cls, method, desc, st.stack with
    | "java/lang/Object", "toString", "()Ljava/lang/String;", .str s :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .str s :: rest })
    | "kotlin/uuid/Uuid$Companion", "random", "()Lkotlin/uuid/Uuid;", _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .str randomUuid :: rest })
    | "androidx/compose/runtime/Composer$Companion", "getEmpty", "()Ljava/lang/Object;", _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .null :: rest })
    | "com/alexvanyo/composelife/navigation/ValueAsSurrogate$Companion", "serializer",
        "(Lkotlinx/serialization/KSerializer;)Lkotlinx/serialization/KSerializer;", _ :: _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .str "ValueAsSurrogateSerializer" :: rest })
    | "com/alexvanyo/composelife/navigation/BackstackEntrySurrogate$Companion", "serializer",
        "(Lkotlinx/serialization/KSerializer;)Lkotlinx/serialization/KSerializer;", _ :: _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .str "BackstackEntrySurrogateSerializer" :: rest })
    | "androidx/compose/runtime/snapshots/SnapshotStateMap", "putAll", "(Ljava/util/Map;)V",
        .heapRef srcMap :: .heapRef dstMap :: rest =>
      match getMapEntries? st.jvmHeap srcMap with
      | some entries =>
        let h' := entries.toList.foldl (fun acc (k, v) => mapPut acc dstMap k v) st.jvmHeap
        .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
      | none => .inr none
    | "com/alexvanyo/composelife/navigation/BackstackEntry", "getId", "()Lkotlin/uuid/Uuid;",
        .heapRef addr :: rest =>
      match heapGetField? st.jvmHeap addr entryCls "id" with
      | some v => .inl (some { st with pc := st.pc + 1, stack := v :: rest })
      | none => .inr none
    | "com/alexvanyo/composelife/navigation/BackstackEntry", "getValue", "()Ljava/lang/Object;",
        .heapRef addr :: rest =>
      match heapGetField? st.jvmHeap addr entryCls "value" with
      | some v => .inl (some { st with pc := st.pc + 1, stack := v :: rest })
      | none => .inr none
    | "com/alexvanyo/composelife/navigation/BackstackEntry", "getPrevious",
        "()Lcom/alexvanyo/composelife/navigation/BackstackEntry;", .heapRef addr :: rest =>
      match heapGetField? st.jvmHeap addr entryCls "previous" with
      | some v => .inl (some { st with pc := st.pc + 1, stack := v :: rest })
      | none => .inr none
    | "com/alexvanyo/composelife/navigation/BackstackEntrySurrogate", "getId", "()Lkotlin/uuid/Uuid;",
        .heapRef addr :: rest =>
      match heapGetField? st.jvmHeap addr surrCls "id" with
      | some v => .inl (some { st with pc := st.pc + 1, stack := v :: rest })
      | none => .inr none
    | "com/alexvanyo/composelife/navigation/BackstackEntrySurrogate", "getPreviousId", "()Lkotlin/uuid/Uuid;",
        .heapRef addr :: rest =>
      match heapGetField? st.jvmHeap addr surrCls "previousId" with
      | some v => .inl (some { st with pc := st.pc + 1, stack := v :: rest })
      | none => .inr none
    | "com/alexvanyo/composelife/navigation/BackstackEntrySurrogate", "getSurrogate", "()Ljava/lang/Object;",
        .heapRef addr :: rest =>
      match heapGetField? st.jvmHeap addr surrCls "surrogate" with
      | some v => .inl (some { st with pc := st.pc + 1, stack := v :: rest })
      | none => .inr none
    | _, _, _, _ => .inr none
  stepInvokeInterface st cls method desc :=
    match cls, method, desc, st.stack with
    | "androidx/compose/runtime/Composer", "rememberedValue", "()Ljava/lang/Object;", _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .null :: rest })
    | "androidx/compose/runtime/Composer", "updateRememberedValue", "(Ljava/lang/Object;)V", _ :: _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := rest })
    | "androidx/compose/runtime/Composer", "changedInstance", "(Ljava/lang/Object;)Z", _ :: _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 0 :: rest })
    | "androidx/compose/runtime/State", "getValue", "()Ljava/lang/Object;", .heapRef sAddr :: rest =>
      match heapGetField? st.jvmHeap sAddr "androidx/compose/runtime/State" "value" with
      | some v => .inl (some { st with pc := st.pc + 1, stack := v :: rest })
      | none => .inr none
    | "androidx/compose/runtime/MutableState", "setValue", "(Ljava/lang/Object;)V", v :: .heapRef sAddr :: rest =>
      let h' := heapSetField st.jvmHeap sAddr "androidx/compose/runtime/MutableState" "value" v
      .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
    | "com/alexvanyo/composelife/navigation/NavigationState", "getCurrentEntryId", "()Lkotlin/uuid/Uuid;",
        .heapRef addr :: rest =>
      match heapGetField? st.jvmHeap addr ctrlCls "currentEntryId" with
      | some v => .inl (some { st with pc := st.pc + 1, stack := v :: rest })
      | none =>
        match heapGetField? st.jvmHeap addr bsStateCls "currentEntryId" with
        | some v => .inl (some { st with pc := st.pc + 1, stack := v :: rest })
        | none => .inr none
    | "com/alexvanyo/composelife/navigation/MutableBackstackNavigationController", "getCurrentEntryId",
        "()Lkotlin/uuid/Uuid;", .heapRef addr :: rest =>
      match heapGetField? st.jvmHeap addr ctrlCls "currentEntryId" with
      | some v => .inl (some { st with pc := st.pc + 1, stack := v :: rest })
      | none => .inr none
    | "com/alexvanyo/composelife/navigation/MutableBackstackNavigationController", "setCurrentEntryId",
        "(Lkotlin/uuid/Uuid;)V", id :: .heapRef addr :: rest =>
      let h' := heapSetField st.jvmHeap addr ctrlCls "currentEntryId" id
      .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
    | "com/alexvanyo/composelife/navigation/MutableBackstackNavigationController", "getEntryMap",
        "()Ljava/util/Map;", .heapRef addr :: rest =>
      match heapGetField? st.jvmHeap addr ctrlCls "entryMap" with
      | some v => .inl (some { st with pc := st.pc + 1, stack := v :: rest })
      | none => .inr none
    | "com/alexvanyo/composelife/navigation/BackstackState", "getEntryMap", "()Ljava/util/Map;",
        .heapRef addr :: rest =>
      match heapGetField? st.jvmHeap addr bsStateCls "entryMap" with
      | some v => .inl (some { st with pc := st.pc + 1, stack := v :: rest })
      | none => .inr none
    | "java/util/Map", "get", "(Ljava/lang/Object;)Ljava/lang/Object;", key :: .heapRef mapAddr :: rest =>
      match getMapEntries? st.jvmHeap mapAddr with
      | some entries =>
        let res := (mapLookup? entries key).getD .null
        .inl (some { st with pc := st.pc + 1, stack := res :: rest })
      | none => .inr none
    | "java/util/Map", "put", "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;",
        val :: key :: .heapRef mapAddr :: rest =>
      let h' := mapPut st.jvmHeap mapAddr key val
      .inl (some { st with pc := st.pc + 1, stack := .null :: rest, jvmHeap := h' })
    | "java/util/Map", "keySet", "()Ljava/util/Set;", .heapRef mapAddr :: rest =>
      match getMapEntries? st.jvmHeap mapAddr with
      | some entries =>
        let keys := Array.mk (entries.toList.map Prod.fst)
        let (setAddr, h') := allocColl st.jvmHeap "java/util/Set" keys
        .inl (some { st with pc := st.pc + 1, stack := .heapRef setAddr :: rest, jvmHeap := h' })
      | none => .inr none
    | "java/util/Collection", "isEmpty", "()Z", .heapRef addr :: rest =>
      match getColl? st.jvmHeap addr "java/util/Collection" with
      | some elems => .inl (some { st with pc := st.pc + 1, stack := .i32 (if elems.isEmpty then 1 else 0) :: rest })
      | none => .inr none
    | "java/util/Set", "contains", "(Ljava/lang/Object;)Z", elem :: .heapRef addr :: rest =>
      match getColl? st.jvmHeap addr "java/util/Set" with
      | some elems =>
        let found := elems.toList.any fun x => bsValEq x elem
        .inl (some { st with pc := st.pc + 1, stack := .i32 (if found then 1 else 0) :: rest })
      | none => .inr none
    | "java/util/Set", "remove", "(Ljava/lang/Object;)Z", elem :: .heapRef addr :: rest =>
      match getColl? st.jvmHeap addr "java/util/Set" with
      | some elems =>
        let filtered := Array.mk (elems.toList.filter fun x => !bsValEq x elem)
        let h' := setColl st.jvmHeap addr "java/util/Set" filtered
        .inl (some { st with pc := st.pc + 1, stack := .i32 1 :: rest, jvmHeap := h' })
      | none => .inr none
    | "java/util/List", "add", "(Ljava/lang/Object;)Z", elem :: .heapRef addr :: rest =>
      match getColl? st.jvmHeap addr "java/util/List" with
      | some elems =>
        let h' := setColl st.jvmHeap addr "java/util/List" (Array.mk (elems.toList ++ [elem]))
        .inl (some { st with pc := st.pc + 1, stack := .i32 1 :: rest, jvmHeap := h' })
      | none => .inr none
    | "java/lang/Iterable", "iterator", "()Ljava/util/Iterator;", .heapRef listAddr :: rest =>
      match heapGetField? st.jvmHeap listAddr "java/lang/Iterable" "arr" with
      | some (.heapRef arrAddr) =>
        let (itAddr, h') := st.jvmHeap.alloc (.instance "java/util/Iterator" [("arr", .heapRef arrAddr), ("idx", .i32 0)])
        .inl (some { st with pc := st.pc + 1, stack := .heapRef itAddr :: rest, jvmHeap := h' })
      | _ => .inr none
    | "java/util/Iterator", "hasNext", "()Z", .heapRef itAddr :: rest =>
      match heapGetField? st.jvmHeap itAddr "java/util/Iterator" "arr",
            heapGetField? st.jvmHeap itAddr "java/util/Iterator" "idx" with
      | some (.heapRef arrAddr), some (.i32 idx) =>
        match st.jvmHeap.get? arrAddr with
        | some (.objArray _ elems) =>
          .inl (some { st with pc := st.pc + 1, stack := .i32 (if idx.toNat < elems.size then 1 else 0) :: rest })
        | _ => .inr none
      | _, _ => .inr none
    | "java/util/Iterator", "next", "()Ljava/lang/Object;", .heapRef itAddr :: rest =>
      match heapGetField? st.jvmHeap itAddr "java/util/Iterator" "arr",
            heapGetField? st.jvmHeap itAddr "java/util/Iterator" "idx" with
      | some (.heapRef arrAddr), some (.i32 idx) =>
        match st.jvmHeap.get? arrAddr with
        | some (.objArray _ elems) =>
          match elems[idx.toNat]? with
          | some e =>
            let h' := bsSetHeapAt st.jvmHeap itAddr (.instance "java/util/Iterator" [("arr", .heapRef arrAddr), ("idx", .i32 (idx + 1))])
            .inl (some { st with pc := st.pc + 1, stack := e :: rest, jvmHeap := h' })
          | none => .inr none
        | _ => .inr none
      | _, _ => .inr none
    | "kotlin/jvm/functions/Function1", "invoke", "(Ljava/lang/Object;)Ljava/lang/Object;",
        arg :: fn :: rest =>
      match fn with
      | .str "pred" =>
        .inl (some { st with pc := st.pc + 1, stack := .boxedBool predResult :: rest })
      | _ =>
        .inl (some { st with pc := st.pc + 1, stack := surrConvert arg :: rest })
    | "kotlin/jvm/functions/Function2", "invoke", "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;",
        _ :: _ :: _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := blockResult :: rest })
    | "com/alexvanyo/composelife/navigation/BackstackValueSurrogate", "createFromSurrogate",
        "(Lcom/alexvanyo/composelife/navigation/BackstackEntry;)Ljava/lang/Object;",
        prev :: surr :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := surrRestore surr prev :: rest })
    | _, _, _, _ => .inr none
  stepInvokeStatic st cls method desc :=
    match cls, method, desc, st.stack with
    | "androidx/compose/runtime/ComposerKt", "sourceInformationMarkerStart",
        "(Landroidx/compose/runtime/Composer;ILjava/lang/String;)V", _ :: _ :: _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := rest })
    | "androidx/compose/runtime/ComposerKt", "sourceInformationMarkerEnd",
        "(Landroidx/compose/runtime/Composer;)V", _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := rest })
    | "androidx/compose/runtime/ComposerKt", "isTraceInProgress", "()Z", rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 0 :: rest })
    | "kotlin/jvm/internal/Intrinsics", "reifiedOperationMarker", "(ILjava/lang/String;)V", _ :: _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := rest })
    | "kotlin/jvm/internal/Intrinsics", "needClassReification", "()V", rest =>
      .inl (some { st with pc := st.pc + 1, stack := rest })
    | "kotlin/jvm/internal/MagicApiIntrinsics", "voidMagicApiCall", "(Ljava/lang/Object;)V", _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := rest })
    | "kotlinx/serialization/SerializersKt", "serializer",
        "(Lkotlin/reflect/KType;)Lkotlinx/serialization/KSerializer;", _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .str "KSerializer" :: rest })
    | "kotlinx/serialization/builtins/BuiltinSerializersKt", "ListSerializer",
        "(Lkotlinx/serialization/KSerializer;)Lkotlinx/serialization/KSerializer;", _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .str "ListSerializer" :: rest })
    | "com/alexvanyo/composelife/serialization/UuidSaverKt", "getUuidSaver",
        "()Landroidx/compose/runtime/saveable/Saver;", rest =>
      .inl (some { st with pc := st.pc + 1, stack := .str "UuidSaver" :: rest })
    | "androidx/compose/runtime/saveable/RememberSaveableKt", "rememberSaveable",
        "([Ljava/lang/Object;Landroidx/compose/runtime/saveable/Saver;Lkotlin/jvm/functions/Function0;Landroidx/compose/runtime/Composer;I)Landroidx/compose/runtime/MutableState;",
        _ :: _ :: _ :: _ :: _ :: rest =>
      let (sAddr, h') := st.jvmHeap.alloc (.instance "androidx/compose/runtime/MutableState" [("value", .str "a")])
      .inl (some { st with pc := st.pc + 1, stack := .heapRef sAddr :: rest, jvmHeap := h' })
    | "androidx/compose/runtime/saveable/RememberSerializableKt", "rememberSerializable",
        "([Ljava/lang/Object;Lkotlinx/serialization/KSerializer;Landroidx/savedstate/serialization/SavedStateConfiguration;Lkotlin/jvm/functions/Function0;Landroidx/compose/runtime/Composer;II)Ljava/lang/Object;",
        _ :: _ :: _ :: _ :: _ :: _ :: _ :: rest =>
      let (mAddr, h') := allocMap st.jvmHeap "java/util/Map" #[]
      .inl (some { st with pc := st.pc + 1, stack := .heapRef mAddr :: rest, jvmHeap := h' })
    | "androidx/compose/runtime/SnapshotStateKt", "mutableStateOf$default",
        "(Ljava/lang/Object;Landroidx/compose/runtime/SnapshotMutationPolicy;ILjava/lang/Object;)Landroidx/compose/runtime/MutableState;",
        _ :: _ :: _ :: v :: rest =>
      let (sAddr, h') := st.jvmHeap.alloc (.instance "androidx/compose/runtime/MutableState" [("value", v)])
      .inl (some { st with pc := st.pc + 1, stack := .heapRef sAddr :: rest, jvmHeap := h' })
    | "androidx/compose/runtime/SnapshotStateKt", "mutableStateMapOf",
        "()Landroidx/compose/runtime/snapshots/SnapshotStateMap;", rest =>
      let (addr, h') := allocMap st.jvmHeap "androidx/compose/runtime/snapshots/SnapshotStateMap" #[]
      .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
    | "kotlin/sequences/SequencesKt", "iterator", "(Lkotlin/jvm/functions/Function2;)Ljava/util/Iterator;",
        fn :: rest =>
      let (itAddr, h') := st.jvmHeap.alloc (.instance "java/util/Iterator" [("fn", fn)])
      .inl (some { st with pc := st.pc + 1, stack := .heapRef itAddr :: rest, jvmHeap := h' })
    | "com/alexvanyo/composelife/navigation/NavigationStateKt", "getCurrentEntry",
        "(Lcom/alexvanyo/composelife/navigation/NavigationState;)Lcom/alexvanyo/composelife/navigation/NavigationEntry;",
        .heapRef addr :: rest =>
      let getEntry (c : String) :=
        match heapGetField? st.jvmHeap addr c "entryMap", heapGetField? st.jvmHeap addr c "currentEntryId" with
        | some (.heapRef mapAddr), some curId =>
          match getMapEntries? st.jvmHeap mapAddr with
          | some entries => mapLookup? entries curId
          | none => none
        | _, _ => none
      match (getEntry ctrlCls).orElse (fun _ => getEntry bsStateCls) with
      | some e => .inl (some { st with pc := st.pc + 1, stack := e :: rest })
      | none => .inr none
    | "com/alexvanyo/composelife/navigation/BackstackStateKt", "getPreviousEntryId",
        "(Lcom/alexvanyo/composelife/navigation/BackstackState;)Lkotlin/uuid/Uuid;",
        .heapRef addr :: rest =>
      match heapGetField? st.jvmHeap addr bsStateCls "entryMap",
            heapGetField? st.jvmHeap addr bsStateCls "currentEntryId" with
      | some (.heapRef mapAddr), some curId =>
        match getMapEntries? st.jvmHeap mapAddr with
        | some entries =>
          match mapLookup? entries curId with
          | some (.heapRef eAddr) =>
            match heapGetField? st.jvmHeap eAddr entryCls "previous" with
            | some (.heapRef pAddr) =>
              match heapGetField? st.jvmHeap pAddr entryCls "id" with
              | some pid => .inl (some { st with pc := st.pc + 1, stack := pid :: rest })
              | none => .inr none
            | some .null => .inl (some { st with pc := st.pc + 1, stack := .null :: rest })
            | _ => .inr none
          | _ => .inr none
        | none => .inr none
      | _, _ => .inr none
    | "com/alexvanyo/composelife/navigation/BackstackStateKt", "BackstackMapSerializer",
        "(Lkotlin/jvm/functions/Function1;Lkotlinx/serialization/KSerializer;)Lkotlinx/serialization/KSerializer;",
        _ :: _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .str "BackstackMapSerializer" :: rest })
    | "com/alexvanyo/composelife/navigation/BackstackStateKt", "rememberBackstackMap",
        "(Ljava/util/List;Lkotlinx/serialization/KSerializer;Landroidx/compose/runtime/Composer;I)Ljava/util/Map;",
        _ :: _ :: _ :: _ :: rest =>
      let (mAddr, h') := allocMap st.jvmHeap "java/util/Map" #[]
      .inl (some { st with pc := st.pc + 1, stack := .heapRef mAddr :: rest, jvmHeap := h' })
    | "com/alexvanyo/composelife/navigation/MutableBackstackNavigationControllerKt",
        "rememberMutableBackstackNavigationController",
        "(Ljava/util/List;Lkotlinx/serialization/KSerializer;Landroidx/compose/runtime/Composer;I)Lcom/alexvanyo/composelife/navigation/MutableBackstackNavigationController;",
        _ :: _ :: _ :: _ :: rest =>
      let (cAddr, h') := st.jvmHeap.alloc (.instance ctrlCls [])
      .inl (some { st with pc := st.pc + 1, stack := .heapRef cAddr :: rest, jvmHeap := h' })
    | "com/alexvanyo/composelife/navigation/MutableBackstackNavigationControllerKt",
        "rememberMutableBackstackNavigationController$lambda$2",
        "(Landroidx/compose/runtime/MutableState;)Lkotlin/uuid/Uuid;", .heapRef sAddr :: rest =>
      match heapGetField? st.jvmHeap sAddr "androidx/compose/runtime/MutableState" "value" with
      | some v => .inl (some { st with pc := st.pc + 1, stack := v :: rest })
      | none => .inr none
    | "com/alexvanyo/composelife/navigation/MutableBackstackNavigationControllerKt",
        "rememberMutableBackstackNavigationController$lambda$3",
        "(Landroidx/compose/runtime/MutableState;Lkotlin/uuid/Uuid;)V", v :: .heapRef sAddr :: rest =>
      let h' := heapSetField st.jvmHeap sAddr "androidx/compose/runtime/MutableState" "value" v
      .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
    | "com/alexvanyo/composelife/navigation/BackstackNavigationKt", "popUpTo",
        "(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/jvm/functions/Function1;Z)Lkotlin/uuid/Uuid;",
        _ :: _ :: _ :: _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .str backstackNavResult :: rest })
    | "com/alexvanyo/composelife/navigation/BackstackNavigationKt", "navigate",
        "(Ljava/util/Map;Lkotlin/uuid/Uuid;Lkotlin/jvm/functions/Function1;Lkotlin/uuid/Uuid;)Lkotlin/uuid/Uuid;",
        id :: _ :: _ :: _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := id :: rest })
    | "com/alexvanyo/composelife/navigation/BackstackNavigationKt", "popBackstack",
        "(Ljava/util/Map;Lkotlin/uuid/Uuid;)Lkotlin/uuid/Uuid;",
        _ :: _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .str backstackNavResult :: rest })
    | "com/alexvanyo/composelife/navigation/MutableBackstackNavigationControllerKt", "popUpTo",
        "(Lcom/alexvanyo/composelife/navigation/MutableBackstackNavigationController;Lkotlin/jvm/functions/Function1;Z)V",
        _ :: _ :: .heapRef ctrlAddr :: rest =>
      let h' := heapSetField st.jvmHeap ctrlAddr ctrlCls "currentEntryId" (.str backstackNavResult)
      .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
    | "com/alexvanyo/composelife/navigation/MutableBackstackNavigationControllerKt", "popUpTo",
        "(Lcom/alexvanyo/composelife/navigation/MutableBackstackNavigationController;Lkotlin/uuid/Uuid;Z)V",
        _ :: _ :: .heapRef ctrlAddr :: rest =>
      let h' := heapSetField st.jvmHeap ctrlAddr ctrlCls "currentEntryId" (.str backstackNavResult)
      .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
    | "com/alexvanyo/composelife/navigation/MutableBackstackNavigationControllerKt", "popUpToValue",
        "(Lcom/alexvanyo/composelife/navigation/MutableBackstackNavigationController;Lkotlin/jvm/functions/Function1;Z)V",
        _ :: _ :: .heapRef ctrlAddr :: rest =>
      let h' := heapSetField st.jvmHeap ctrlAddr ctrlCls "currentEntryId" (.str backstackNavResult)
      .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
    | "com/alexvanyo/composelife/navigation/MutableBackstackNavigationControllerKt", "navigate",
        "(Lcom/alexvanyo/composelife/navigation/MutableBackstackNavigationController;Lkotlin/jvm/functions/Function1;Lkotlin/uuid/Uuid;)V",
        id :: _ :: .heapRef ctrlAddr :: rest =>
      let h' := heapSetField st.jvmHeap ctrlAddr ctrlCls "currentEntryId" id
      .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
    | "com/alexvanyo/composelife/navigation/MutableBackstackNavigationControllerKt", "navigate",
        "(Lcom/alexvanyo/composelife/navigation/MutableBackstackNavigationController;Ljava/lang/Object;Lkotlin/uuid/Uuid;)V",
        id :: _ :: .heapRef ctrlAddr :: rest =>
      let h' := heapSetField st.jvmHeap ctrlAddr ctrlCls "currentEntryId" id
      .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
    | "kotlin/collections/CollectionsKt", "createListBuilder", "()Ljava/util/List;", rest =>
      let (addr, h') := allocColl st.jvmHeap "java/util/List" #[]
      .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
    | "kotlin/collections/CollectionsKt", "build", "(Ljava/util/List;)Ljava/util/List;", l :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := l :: rest })
    | "kotlin/collections/CollectionsKt", "toMutableSet", "(Ljava/lang/Iterable;)Ljava/util/Set;", s :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := s :: rest })
    | "kotlin/collections/CollectionsKt", "first", "(Ljava/lang/Iterable;)Ljava/lang/Object;",
        .heapRef addr :: rest =>
      match getColl? st.jvmHeap addr "java/lang/Iterable" with
      | some elems =>
        match elems[0]? with
        | some e => .inl (some { st with pc := st.pc + 1, stack := e :: rest })
        | none => .inr none
      | none => .inr none
    | "kotlin/collections/CollectionsKt", "last", "(Ljava/util/List;)Ljava/lang/Object;",
        .heapRef addr :: rest =>
      match getColl? st.jvmHeap addr "java/util/List" with
      | some elems =>
        match elems[elems.size - 1]? with
        | some e => .inl (some { st with pc := st.pc + 1, stack := e :: rest })
        | none => .inr none
      | none => .inr none
    | "kotlin/collections/MapsKt", "mapCapacity", "(I)I", n :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := n :: rest })
    | "kotlin/ranges/RangesKt", "coerceAtLeast", "(II)I", minV :: _v :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := minV :: rest })
    | "kotlin/collections/MapsKt", "getValue", "(Ljava/util/Map;Ljava/lang/Object;)Ljava/lang/Object;",
        key :: .heapRef mapAddr :: rest =>
      match getMapEntries? st.jvmHeap mapAddr with
      | some entries =>
        match mapLookup? entries key with
        | some v => .inl (some { st with pc := st.pc + 1, stack := v :: rest })
        | none => .inr none
      | none => .inr none
    | "com/alexvanyo/composelife/navigation/BackstackStateKt", "BackstackMapSerializer$lambda$0$0$addEntry",
        "(Ljava/util/Set;Ljava/util/Map;Ljava/util/List;Lkotlin/jvm/functions/Function1;Lkotlin/uuid/Uuid;)V",
        id :: _ :: listRef :: mapRef :: setRef :: rest =>
      match setRef, mapRef, listRef with
      | .heapRef setAddr, .heapRef mapAddr, .heapRef listAddr =>
        match getColl? st.jvmHeap setAddr "java/util/Set",
              getMapEntries? st.jvmHeap mapAddr,
              getColl? st.jvmHeap listAddr "java/util/List" with
        | some rem, some entries, some outList =>
          if rem.toList.any (fun x => bsValEq x id) then
            match mapLookup? entries id with
            | some (.heapRef eAddr) =>
              let prevId := match heapGetField? st.jvmHeap eAddr entryCls "previous" with
                | some (.heapRef pAddr) => (heapGetField? st.jvmHeap pAddr entryCls "id").getD .null
                | _ => .null
              let val := (heapGetField? st.jvmHeap eAddr entryCls "value").getD .null
              let (sAddr, h1) := st.jvmHeap.alloc (.instance surrCls [("id", id), ("previousId", prevId), ("surrogate", surrConvert val)])
              let h2 := setColl h1 listAddr "java/util/List" (Array.mk (outList.toList ++ [.heapRef sAddr]))
              let h3 := setColl h2 setAddr "java/util/Set" (Array.mk (rem.toList.filter fun x => !bsValEq x id))
              .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h3 })
            | _ => .inr none
          else .inl (some { st with pc := st.pc + 1, stack := rest })
        | _, _, _ => .inr none
      | _, _, _ => .inr none
    | _, _, _, _ => .inr none

abbrev bsHooks : Jvm.JvmHooks Empty Unit := mkBackstackStateHooks

private theorem bs_hiteZ (v : BsVal) (t e : Option BsVal) :
    bsHooks.iteZero? v t e =
      match bsHooks.isZero? v with | some true => t | some false => e | none => none := by
  dsimp only [bsHooks, mkBackstackStateHooks]
  cases v.asI32? with
  | none => rfl
  | some x => cases h : (x == 0) <;> simp [h, Jvm.defaultIteVal] <;> split <;> rfl

private theorem bs_hiteNZ (v : BsVal) (t e : Option BsVal) :
    bsHooks.iteNonZero? v t e =
      match bsHooks.isZero? v with | some true => e | some false => t | none => none := by
  dsimp only [bsHooks, mkBackstackStateHooks]
  cases v.asI32? with
  | none => rfl
  | some x => cases h : (x == 0) <;> simp [h, Jvm.defaultIteVal] <;> split <;> rfl

/-! ### BackstackEntry proofs (8 programs) -/

theorem backstackEntry_clinit_equiv :
    Jvm.runJvm bsHooks 10 BackstackEntry_clinit_prog (initSt []) = some .unit := rfl

theorem backstackEntry_init_equiv (val prev : BsVal) (id : String) :
    let (addr, h0) := ({} : Jvm.JvmHeap Empty).alloc (.instance entryCls [])
    ∃ endSt,
      Jvm.runJvmRes bsHooks 30 BackstackEntry_init_prog
        (initSt [(0, .heapRef addr), (1, val), (2, prev), (3, .str id)] h0) = some (.unit, endSt) ∧
      heapGetField? endSt.jvmHeap addr entryCls "value" = some val ∧
      heapGetField? endSt.jvmHeap addr entryCls "previous" = some prev ∧
      heapGetField? endSt.jvmHeap addr entryCls "id" = some (.str id) :=
  ⟨_, rfl, rfl, rfl, rfl⟩

theorem backstackEntry_init_1_default_id_equiv (val prev : BsVal) (rand : String) :
    let (addr, h0) := ({} : Jvm.JvmHeap Empty).alloc (.instance entryCls [])
    ∃ endSt,
      Jvm.runJvmRes (mkBackstackStateHooks (randomUuid := rand)) 30 BackstackEntry_init_1_prog
        (initSt [(0, .heapRef addr), (1, val), (2, prev), (3, .null), (4, .i32 4)] h0) = some (.unit, endSt) ∧
      heapGetField? endSt.jvmHeap addr entryCls "id" = some (.str rand) :=
  ⟨_, rfl, rfl⟩

theorem backstackEntry_init_1_explicit_id_equiv (val prev : BsVal) (id : String) :
    let (addr, h0) := ({} : Jvm.JvmHeap Empty).alloc (.instance entryCls [])
    ∃ endSt,
      Jvm.runJvmRes bsHooks 30 BackstackEntry_init_1_prog
        (initSt [(0, .heapRef addr), (1, val), (2, prev), (3, .str id), (4, .i32 0)] h0) = some (.unit, endSt) ∧
      heapGetField? endSt.jvmHeap addr entryCls "id" = some (.str id) :=
  ⟨_, rfl, rfl⟩

theorem backstackEntry_getValue_equiv (val prev : BsVal) (id : String) :
    let (addr, h0) := ({} : Jvm.JvmHeap Empty).alloc (.instance entryCls [("value", val), ("previous", prev), ("id", .str id)])
    Jvm.runJvm bsHooks 10 BackstackEntry_getValue_prog (initSt [(0, .heapRef addr)] h0) = some val := rfl

theorem backstackEntry_getPrevious_equiv (val prev : BsVal) (id : String) :
    let (addr, h0) := ({} : Jvm.JvmHeap Empty).alloc (.instance entryCls [("value", val), ("previous", prev), ("id", .str id)])
    Jvm.runJvm bsHooks 10 BackstackEntry_getPrevious_prog (initSt [(0, .heapRef addr)] h0) = some prev := rfl

theorem backstackEntry_getId_equiv (val prev : BsVal) (id : String) :
    let (addr, h0) := ({} : Jvm.JvmHeap Empty).alloc (.instance entryCls [("value", val), ("previous", prev), ("id", .str id)])
    Jvm.runJvm bsHooks 10 BackstackEntry_getId_prog (initSt [(0, .heapRef addr)] h0) = some (.str id) := rfl

theorem backstackEntry_iterator_equiv (id : String) :
    let (addr, h0) := ({} : Jvm.JvmHeap Empty).alloc (.instance entryCls [("value", .str "v"), ("previous", .null), ("id", .str id)])
    ∃ itAddr endSt,
      Jvm.runJvmRes bsHooks 20 BackstackEntry_iterator_prog (initSt [(0, .heapRef addr)] h0) =
        some (.heapRef itAddr, endSt) :=
  ⟨2, _, rfl⟩

theorem backstackEntry_toString_equiv :
    let (addr, h0) := ({} : Jvm.JvmHeap Empty).alloc (.instance entryCls [("value", .str "v1"), ("previous", .null), ("id", .str "id1")])
    Jvm.runJvm bsHooks 20 BackstackEntry_toString_prog (initSt [(0, .heapRef addr)] h0) =
      some (.str "BackstackEntry(id=id1, value=v1, previous=null)") := rfl

/-! ### MutableBackstackNavigationControllerKt proofs (23 programs) -/

theorem controller_getCanNavigateBack_equiv :
    (let (e0, h0) := ({} : Jvm.JvmHeap Empty).alloc (.instance entryCls [("id", .str "a"), ("previous", .null)])
     let (mAddr, h1) := allocMap h0 "java/util/Map" #[(.str "a", .heapRef e0)]
     let (cAddr, h2) := h1.alloc (.instance ctrlCls [("entryMap", .heapRef mAddr), ("currentEntryId", .str "a")])
     Jvm.runJvm bsHooks 30 MutableBackstackNavigationControllerKt_getCanNavigateBack_prog
       (initSt [(0, .heapRef cAddr)] h2) = some (.i32 0)) ∧
    (let (e0, h0) := ({} : Jvm.JvmHeap Empty).alloc (.instance entryCls [("id", .str "a"), ("previous", .null)])
     let (e1, h1) := h0.alloc (.instance entryCls [("id", .str "b"), ("previous", .heapRef e0)])
     let (mAddr, h2) := allocMap h1 "java/util/Map" #[(.str "a", .heapRef e0), (.str "b", .heapRef e1)]
     let (cAddr, h3) := h2.alloc (.instance ctrlCls [("entryMap", .heapRef mAddr), ("currentEntryId", .str "b")])
     Jvm.runJvm bsHooks 30 MutableBackstackNavigationControllerKt_getCanNavigateBack_prog
       (initSt [(0, .heapRef cAddr)] h3) = some (.i32 1)) :=
  ⟨rfl, rfl⟩

theorem controller_withExpectedActor_equiv :
    (let (e0, h0) := ({} : Jvm.JvmHeap Empty).alloc (.instance entryCls [("id", .str "a"), ("previous", .null)])
     let (mAddr, h1) := allocMap h0 "java/util/Map" #[(.str "a", .heapRef e0)]
     let (cAddr, h2) := h1.alloc (.instance ctrlCls [("entryMap", .heapRef mAddr), ("currentEntryId", .str "a")])
     Jvm.runJvm bsHooks 40 MutableBackstackNavigationControllerKt_withExpectedActor_prog
       (initSt [(0, .heapRef cAddr), (1, .null), (2, .str "block")] h2) =
       some (.i32 (if withExpectedActorModel "a" none then 1 else 0))) ∧
    (let (e0, h0) := ({} : Jvm.JvmHeap Empty).alloc (.instance entryCls [("id", .str "a"), ("previous", .null)])
     let (mAddr, h1) := allocMap h0 "java/util/Map" #[(.str "a", .heapRef e0)]
     let (cAddr, h2) := h1.alloc (.instance ctrlCls [("entryMap", .heapRef mAddr), ("currentEntryId", .str "a")])
     Jvm.runJvm bsHooks 40 MutableBackstackNavigationControllerKt_withExpectedActor_prog
       (initSt [(0, .heapRef cAddr), (1, .str "a"), (2, .str "block")] h2) =
       some (.i32 (if withExpectedActorModel "a" (some "a") then 1 else 0))) ∧
    (let (e0, h0) := ({} : Jvm.JvmHeap Empty).alloc (.instance entryCls [("id", .str "a"), ("previous", .null)])
     let (mAddr, h1) := allocMap h0 "java/util/Map" #[(.str "a", .heapRef e0)]
     let (cAddr, h2) := h1.alloc (.instance ctrlCls [("entryMap", .heapRef mAddr), ("currentEntryId", .str "a")])
     Jvm.runJvm bsHooks 40 MutableBackstackNavigationControllerKt_withExpectedActor_prog
       (initSt [(0, .heapRef cAddr), (1, .str "b"), (2, .str "block")] h2) =
       some (.i32 (if withExpectedActorModel "a" (some "b") then 1 else 0))) :=
  ⟨rfl, rfl, rfl⟩

theorem controller_popUpTo_and_navigate_equiv (nextId newId rand : String) :
    let (mAddr, h0) := allocMap {} "java/util/Map" #[]
    let (cAddr, h1) := h0.alloc (.instance ctrlCls [("entryMap", .heapRef mAddr), ("currentEntryId", .str "a")])
    (∃ endSt,
      Jvm.runJvmRes (mkBackstackStateHooks (backstackNavResult := nextId)) 30
        MutableBackstackNavigationControllerKt_popUpTo_prog
        (initSt [(0, .heapRef cAddr), (1, .str "pred"), (2, .i32 0)] h1) = some (.unit, endSt) ∧
      heapGetField? endSt.jvmHeap cAddr ctrlCls "currentEntryId" = some (.str nextId)) ∧
    Jvm.runJvm bsHooks 30 MutableBackstackNavigationControllerKt_popUpTo_default_prog
      (initSt [(0, .heapRef cAddr), (1, .str "pred"), (2, .i32 1), (3, .i32 2)] h1) = some .unit ∧
    Jvm.runJvm bsHooks 30 MutableBackstackNavigationControllerKt_popUpTo_1_prog
      (initSt [(0, .heapRef cAddr), (1, .str "a"), (2, .i32 0)] h1) = some .unit ∧
    Jvm.runJvm bsHooks 30 MutableBackstackNavigationControllerKt_popUpTo_default_1_prog
      (initSt [(0, .heapRef cAddr), (1, .str "a"), (2, .i32 1), (3, .i32 2)] h1) = some .unit ∧
    Jvm.runJvm bsHooks 30 MutableBackstackNavigationControllerKt_popUpToValue_prog
      (initSt [(0, .heapRef cAddr), (1, .str "pred"), (2, .i32 0)] h1) = some .unit ∧
    Jvm.runJvm bsHooks 30 MutableBackstackNavigationControllerKt_popUpToValue_default_prog
      (initSt [(0, .heapRef cAddr), (1, .str "pred"), (2, .i32 1), (3, .i32 2)] h1) = some .unit ∧
    (∃ endSt,
      Jvm.runJvmRes bsHooks 30 MutableBackstackNavigationControllerKt_navigate_prog
        (initSt [(0, .heapRef cAddr), (1, .str "factory"), (2, .str newId)] h1) = some (.unit, endSt) ∧
      heapGetField? endSt.jvmHeap cAddr ctrlCls "currentEntryId" = some (.str newId)) ∧
    (∃ endSt,
      Jvm.runJvmRes (mkBackstackStateHooks (randomUuid := rand)) 30
        MutableBackstackNavigationControllerKt_navigate_default_prog
        (initSt [(0, .heapRef cAddr), (1, .str "factory"), (2, .null), (3, .i32 2)] h1) = some (.unit, endSt) ∧
      heapGetField? endSt.jvmHeap cAddr ctrlCls "currentEntryId" = some (.str rand)) ∧
    Jvm.runJvm bsHooks 30 MutableBackstackNavigationControllerKt_navigate_1_prog
      (initSt [(0, .heapRef cAddr), (1, .str "val"), (2, .str newId)] h1) = some .unit ∧
    Jvm.runJvm (mkBackstackStateHooks (randomUuid := rand)) 30
      MutableBackstackNavigationControllerKt_navigate_default_1_prog
      (initSt [(0, .heapRef cAddr), (1, .str "val"), (2, .null), (3, .i32 2)] h1) = some .unit ∧
    Jvm.runJvm (mkBackstackStateHooks (backstackNavResult := nextId)) 30
      MutableBackstackNavigationControllerKt_popBackstack_prog
      (initSt [(0, .heapRef cAddr)] h1) = some .unit :=
  ⟨⟨_, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, rfl, rfl, rfl⟩

theorem controller_lambdas_equiv (v : BsVal) (res : Bool) :
    (let (eAddr, h0) := ({} : Jvm.JvmHeap Empty).alloc (.instance entryCls [("id", .str "a")])
     Jvm.runJvm bsHooks 20 MutableBackstackNavigationControllerKt_popUpTo_lambda_0_prog
       (initSt [(0, .str "a"), (1, .heapRef eAddr)] h0) = some (.bool true)) ∧
    (let (eAddr, h0) := ({} : Jvm.JvmHeap Empty).alloc (.instance entryCls [("value", .str "v")])
     Jvm.runJvm (mkBackstackStateHooks (predResult := res)) 20
       MutableBackstackNavigationControllerKt_popUpTo_lambda_1_prog
       (initSt [(0, .str "pred"), (1, .heapRef eAddr)] h0) = some (.i32 (if res then 1 else 0))) ∧
    (let (eAddr, h0) := ({} : Jvm.JvmHeap Empty).alloc (.instance entryCls [("id", .str "a")])
     Jvm.runJvm bsHooks 20 MutableBackstackNavigationControllerKt_navigate_lambda_0_prog
       (initSt [(0, v), (1, .heapRef eAddr)] h0) = some v) := by
  refine ⟨rfl, ?_, rfl⟩
  cases res <;> rfl

theorem controller_remember_helpers_equiv :
    (let (sAddr, h0) := ({} : Jvm.JvmHeap Empty).alloc (.instance "androidx/compose/runtime/MutableState" [("value", .str "a")])
     Jvm.runJvm bsHooks 25 MutableBackstackNavigationControllerKt_rememberMutableBackstackNavigationController_lambda_2_prog
       (initSt [(0, .heapRef sAddr)] h0) = some (.str "a")) ∧
    (let (sAddr, h0) := ({} : Jvm.JvmHeap Empty).alloc (.instance "androidx/compose/runtime/MutableState" [("value", .str "a")])
     ∃ endSt,
       Jvm.runJvmRes bsHooks 25 MutableBackstackNavigationControllerKt_rememberMutableBackstackNavigationController_lambda_3_prog
         (initSt [(0, .heapRef sAddr), (1, .str "b")] h0) = some (.unit, endSt) ∧
       heapGetField? endSt.jvmHeap sAddr "androidx/compose/runtime/MutableState" "value" = some (.str "b")) ∧
    (let (eAddr, h0) := ({} : Jvm.JvmHeap Empty).alloc (.instance entryCls [("id", .str "a")])
     let (lAddr, h1) := allocColl h0 "java/util/List" #[.heapRef eAddr]
     ∃ sAddr endSt,
       Jvm.runJvmRes bsHooks 25 MutableBackstackNavigationControllerKt_rememberMutableBackstackNavigationController_lambda_1_0_prog
         (initSt [(0, .heapRef lAddr)] h1) = some (.heapRef sAddr, endSt)) ∧
    (let (sAddr, h0) := ({} : Jvm.JvmHeap Empty).alloc (.instance "androidx/compose/runtime/MutableState" [("value", .str "a")])
     Jvm.runJvm bsHooks 15 MutableBackstackNavigationControllerKt_access_rememberMutableBackstackNavigationController_lambda_2_prog
       (initSt [(0, .heapRef sAddr)] h0) = some (.str "a")) ∧
    (let (sAddr, h0) := ({} : Jvm.JvmHeap Empty).alloc (.instance "androidx/compose/runtime/MutableState" [("value", .str "a")])
     Jvm.runJvm bsHooks 15 MutableBackstackNavigationControllerKt_access_rememberMutableBackstackNavigationController_lambda_3_prog
       (initSt [(0, .heapRef sAddr), (1, .str "b")] h0) = some .unit) :=
  ⟨rfl, ⟨_, rfl, rfl⟩, ⟨3, _, rfl⟩, rfl, rfl⟩

theorem controller_remember_main_equiv :
    let (eAddr, h0) := ({} : Jvm.JvmHeap Empty).alloc (.instance entryCls [("id", .str "a")])
    let (lAddr, h1) := allocColl h0 "java/util/List" #[.heapRef eAddr]
    (Jvm.runJvm bsHooks 100 MutableBackstackNavigationControllerKt_rememberMutableBackstackNavigationController_prog
      (initSt [(0, .heapRef lAddr), (1, .str "ser"), (2, .str "composer"), (3, .i32 0), (4, .i32 0)] h1) =
      some (.heapRef 3)) ∧
    (Jvm.runJvm bsHooks 200 MutableBackstackNavigationControllerKt_rememberMutableBackstackNavigationController_1_prog
      (initSt [(0, .heapRef lAddr), (1, .str "mapSer"), (2, .str "composer"), (3, .i32 0)] h1) =
      some (.heapRef 7)) := by
  constructor
  · exact Jvm.runJvm_of_runJvmValFast0 bsHooks bs_hiteZ bs_hiteNZ 100 _ _ _ rfl rfl
  · exact Jvm.runJvm_of_runJvmValFast0 bsHooks bs_hiteZ bs_hiteNZ 200 _ _ _ rfl rfl

/-! ### BackstackStateKt proofs (10 programs) -/

theorem backstackState_previous_equiv :
    (let (e0, h0) := ({} : Jvm.JvmHeap Empty).alloc (.instance entryCls [("id", .str "a"), ("previous", .null)])
     let (mAddr, h1) := allocMap h0 "java/util/Map" #[(.str "a", .heapRef e0)]
     let (sAddr, h2) := h1.alloc (.instance bsStateCls [("entryMap", .heapRef mAddr), ("currentEntryId", .str "a")])
     Jvm.runJvm bsHooks 30 BackstackStateKt_getPreviousEntryId_prog
       (initSt [(0, .heapRef sAddr)] h2) = some .null) ∧
    (let (e0, h0) := ({} : Jvm.JvmHeap Empty).alloc (.instance entryCls [("id", .str "a"), ("previous", .null)])
     let (e1, h1) := h0.alloc (.instance entryCls [("id", .str "b"), ("previous", .heapRef e0)])
     let (mAddr, h2) := allocMap h1 "java/util/Map" #[(.str "a", .heapRef e0), (.str "b", .heapRef e1)]
     let (sAddr, h3) := h2.alloc (.instance bsStateCls [("entryMap", .heapRef mAddr), ("currentEntryId", .str "b")])
     Jvm.runJvm bsHooks 30 BackstackStateKt_getPreviousEntryId_prog
       (initSt [(0, .heapRef sAddr)] h3) = some (.str "a")) ∧
    (let (e0, h0) := ({} : Jvm.JvmHeap Empty).alloc (.instance entryCls [("id", .str "a"), ("previous", .null)])
     let (e1, h1) := h0.alloc (.instance entryCls [("id", .str "b"), ("previous", .heapRef e0)])
     let (mAddr, h2) := allocMap h1 "java/util/Map" #[(.str "a", .heapRef e0), (.str "b", .heapRef e1)]
     let (sAddr, h3) := h2.alloc (.instance bsStateCls [("entryMap", .heapRef mAddr), ("currentEntryId", .str "b")])
     Jvm.runJvm bsHooks 30 BackstackStateKt_getPreviousEntry_prog
       (initSt [(0, .heapRef sAddr)] h3) = some (.heapRef e0)) :=
  ⟨rfl, rfl, rfl⟩

theorem backstackState_remember_and_serializer_equiv :
    let (e0, h0) := ({} : Jvm.JvmHeap Empty).alloc (.instance entryCls [("id", .str "a"), ("previous", .null), ("value", .str "v0")])
    let (lAddr, h1) := allocColl h0 "java/util/List" #[.heapRef e0]
    (Jvm.runJvm bsHooks 100 BackstackStateKt_rememberBackstackMap_prog
      (initSt [(0, .heapRef lAddr), (1, .str "ser"), (2, .str "composer"), (3, .i32 0), (4, .i32 0)] h1) =
      some (.heapRef 4)) ∧
    (Jvm.runJvm bsHooks 150 BackstackStateKt_rememberBackstackMap_1_prog
      (initSt [(0, .heapRef lAddr), (1, .str "mapSer"), (2, .str "composer"), (3, .i32 0)] h1) =
      some (.heapRef 5)) ∧
    (Jvm.runJvm bsHooks 30 BackstackStateKt_BackstackMapSerializer_prog
      (initSt [(0, .str "conv")] h1) = some (.str "BackstackMapSerializer")) ∧
    (Jvm.runJvm bsHooks 40 BackstackStateKt_BackstackMapSerializer_1_prog
      (initSt [(0, .str "conv"), (1, .str "ser")] h1) = some (.heapRef 3)) := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · exact Jvm.runJvm_of_runJvmValFast0 bsHooks bs_hiteZ bs_hiteNZ 100 _ _ _ rfl rfl
  · exact Jvm.runJvm_of_runJvmValFast0 bsHooks bs_hiteZ bs_hiteNZ 150 _ _ _ rfl rfl

theorem backstackState_rememberBackstackMap_lambda_1_0_equiv :
    let (e0, h0) := ({} : Jvm.JvmHeap Empty).alloc (.instance entryCls [("id", .str "a"), ("previous", .null), ("value", .str "v0")])
    let (lAddr, h1) := allocColl h0 "java/util/List" #[.heapRef e0]
    ∃ mapAddr endSt,
      Jvm.runJvmRes bsHooks 120 BackstackStateKt_rememberBackstackMap_lambda_1_0_prog
        (initSt [(0, .heapRef lAddr)] h1) = some (.heapRef mapAddr, endSt) ∧
      (getMapEntries? endSt.jvmHeap mapAddr).map Array.size = some 1 := by
  have hfast :
      let (e0, h0) := ({} : Jvm.JvmHeap Empty).alloc (.instance entryCls [("id", .str "a"), ("previous", .null), ("value", .str "v0")])
      let (lAddr, h1) := allocColl h0 "java/util/List" #[.heapRef e0]
      ∃ mapAddr endSt,
        Jvm.runJvmResFast bsHooks 120 BackstackStateKt_rememberBackstackMap_lambda_1_0_prog 0
          BackstackStateKt_rememberBackstackMap_lambda_1_0_prog
          (initSt [(0, .heapRef lAddr)] h1) = some (.heapRef mapAddr, endSt) ∧
        (getMapEntries? endSt.jvmHeap mapAddr).map Array.size = some 1 :=
    ⟨4, _, rfl, rfl⟩
  dsimp only at hfast ⊢
  rcases hfast with ⟨mapAddr, endSt, hrun, hsz⟩
  exact ⟨mapAddr, endSt, Jvm.runJvmRes_of_runJvmResFast0 bsHooks 120 _ _ _ rfl hrun, hsz⟩

theorem backstackMapSerializer_addEntry_root_equiv :
    let (e0, h0) := ({} : Jvm.JvmHeap Empty).alloc (.instance entryCls [("id", .str "a"), ("previous", .null), ("value", .str "v0")])
    let (mAddr, h1) := allocMap h0 "java/util/Map" #[(.str "a", .heapRef e0)]
    let (remAddr, h2) := allocColl h1 "java/util/Set" #[.str "a"]
    let (listAddr, h3) := allocColl h2 "java/util/List" #[]
    ∃ endSt,
      Jvm.runJvmRes bsHooks 80 BackstackStateKt_BackstackMapSerializer_lambda_0_0_addEntry_prog
        (initSt [(0, .heapRef remAddr), (1, .heapRef mAddr), (2, .heapRef listAddr), (3, .str "conv"), (4, .str "a")] h3) =
        some (.unit, endSt) ∧
      getColl? endSt.jvmHeap remAddr "java/util/Set" = some #[] := by
  have hfast :
      let (e0, h0) := ({} : Jvm.JvmHeap Empty).alloc (.instance entryCls [("id", .str "a"), ("previous", .null), ("value", .str "v0")])
      let (mAddr, h1) := allocMap h0 "java/util/Map" #[(.str "a", .heapRef e0)]
      let (remAddr, h2) := allocColl h1 "java/util/Set" #[.str "a"]
      let (listAddr, h3) := allocColl h2 "java/util/List" #[]
      ∃ endSt,
        Jvm.runJvmResFast bsHooks 80 BackstackStateKt_BackstackMapSerializer_lambda_0_0_addEntry_prog 0
          BackstackStateKt_BackstackMapSerializer_lambda_0_0_addEntry_prog
          (initSt [(0, .heapRef remAddr), (1, .heapRef mAddr), (2, .heapRef listAddr), (3, .str "conv"), (4, .str "a")] h3) =
          some (.unit, endSt) ∧
        getColl? endSt.jvmHeap remAddr "java/util/Set" = some #[] :=
    ⟨_, rfl, rfl⟩
  dsimp only at hfast ⊢
  rcases hfast with ⟨endSt, hrun, hrem⟩
  exact ⟨endSt, Jvm.runJvmRes_of_runJvmResFast0 bsHooks 80 _ _ _ rfl hrun, hrem⟩

theorem backstackMapSerializer_lambda_0_equiv :
    let (e0, h0) := ({} : Jvm.JvmHeap Empty).alloc (.instance entryCls [("id", .str "a"), ("previous", .null), ("value", .str "v0")])
    let (mAddr, h1) := allocMap h0 "java/util/Map" #[(.str "a", .heapRef e0)]
    ∃ listAddr endSt,
      Jvm.runJvmRes bsHooks 80 BackstackStateKt_BackstackMapSerializer_lambda_0_prog
        (initSt [(0, .str "conv"), (1, .heapRef mAddr)] h1) = some (.heapRef listAddr, endSt) ∧
      (getColl? endSt.jvmHeap listAddr "java/util/List").map Array.size = some 1 := by
  have hfast :
      let (e0, h0) := ({} : Jvm.JvmHeap Empty).alloc (.instance entryCls [("id", .str "a"), ("previous", .null), ("value", .str "v0")])
      let (mAddr, h1) := allocMap h0 "java/util/Map" #[(.str "a", .heapRef e0)]
      ∃ listAddr endSt,
        Jvm.runJvmResFast bsHooks 80 BackstackStateKt_BackstackMapSerializer_lambda_0_prog 0
          BackstackStateKt_BackstackMapSerializer_lambda_0_prog
          (initSt [(0, .str "conv"), (1, .heapRef mAddr)] h1) = some (.heapRef listAddr, endSt) ∧
        (getColl? endSt.jvmHeap listAddr "java/util/List").map Array.size = some 1 :=
    ⟨4, _, rfl, rfl⟩
  dsimp only at hfast ⊢
  rcases hfast with ⟨listAddr, endSt, hrun, hsz⟩
  exact ⟨listAddr, endSt, Jvm.runJvmRes_of_runJvmResFast0 bsHooks 80 _ _ _ rfl hrun, hsz⟩

theorem backstackMapSerializer_lambda_1_equiv :
    let (s0, h0) := ({} : Jvm.JvmHeap Empty).alloc (.instance surrCls [("id", .str "a"), ("previousId", .null), ("surrogate", .str "v0")])
    let (s1, h1) := h0.alloc (.instance surrCls [("id", .str "b"), ("previousId", .str "a"), ("surrogate", .str "v1")])
    let (listAddr, h2) := allocColl h1 "java/util/List" #[.heapRef s0, .heapRef s1]
    ∃ mapAddr endSt,
      Jvm.runJvmRes bsHooks 120 BackstackStateKt_BackstackMapSerializer_lambda_1_prog
        (initSt [(0, .heapRef listAddr)] h2) = some (.heapRef mapAddr, endSt) ∧
      (getMapEntries? endSt.jvmHeap mapAddr).map Array.size = some 2 := by
  have hfast :
      let (s0, h0) := ({} : Jvm.JvmHeap Empty).alloc (.instance surrCls [("id", .str "a"), ("previousId", .null), ("surrogate", .str "v0")])
      let (s1, h1) := h0.alloc (.instance surrCls [("id", .str "b"), ("previousId", .str "a"), ("surrogate", .str "v1")])
      let (listAddr, h2) := allocColl h1 "java/util/List" #[.heapRef s0, .heapRef s1]
      ∃ mapAddr endSt,
        Jvm.runJvmResFast bsHooks 120 BackstackStateKt_BackstackMapSerializer_lambda_1_prog 0
          BackstackStateKt_BackstackMapSerializer_lambda_1_prog
          (initSt [(0, .heapRef listAddr)] h2) = some (.heapRef mapAddr, endSt) ∧
        (getMapEntries? endSt.jvmHeap mapAddr).map Array.size = some 2 :=
    ⟨5, _, rfl, rfl⟩
  dsimp only at hfast ⊢
  rcases hfast with ⟨mapAddr, endSt, hrun, hsz⟩
  exact ⟨mapAddr, endSt, Jvm.runJvmRes_of_runJvmResFast0 bsHooks 120 _ _ _ rfl hrun, hsz⟩

end Navigation.KotlinJvmVerification
