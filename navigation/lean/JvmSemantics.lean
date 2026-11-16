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

import Jvm
import models.BackstackNavigationModel

namespace Navigation.JvmVerification

export Jvm (JvmInstr setLocal initJvmState)

/-- Generic entry value payload representable in `BackstackEntry<T>` on the JVM. -/
inductive NavValue where
  | null
  | bool (b : Bool)
  | int (v : UInt32)
  | long (v : UInt64)
  | str (s : String)
  | obj (n : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Navigation domain-specific extension values on the JVM stack and locals. -/
inductive NavExt where
  | uuid (id : Model.EntryId)
  | entry (e : Model.BackstackEntry NavValue)
  | mapRef (mapId : Nat)
  | closureRef (closureId : Nat)
  | companion (cls : String)
  | obj (n : Nat)
  deriving DecidableEq, Repr, Inhabited

abbrev JvmVal := Jvm.JvmVal NavExt

def NavValue.toJvmVal : NavValue → JvmVal
  | .null => .null
  | .bool b => .boxedBool b
  | .int v => .boxedInt v
  | .long v => .boxedLong v
  | .str s => .str s
  | .obj n => .ext (.obj n)

def NavValue.ofJvmVal? : JvmVal → Option NavValue
  | .null => some .null
  | .boxedBool b => some (.bool b)
  | .boxedInt v => some (.int v)
  | .boxedLong v => some (.long v)
  | .str s => some (.str s)
  | .ext (.obj n) => some (.obj n)
  | _ => none

@[simp] theorem NavValue.ofJvmVal?_toJvmVal (v : NavValue) :
    NavValue.ofJvmVal? v.toJvmVal = some v := by
  cases v <;> rfl

/-- Closure representation supporting both bytecode lambdas and host model functions. -/
inductive NavClosure where
  | bytecode (fnTag : String) (captures : List JvmVal) (boxBool : Bool := false)
  | host (fn : JvmVal → Option JvmVal)

instance : Inhabited NavClosure := ⟨.host (fun _ => none)⟩

/-- Construct a host closure for `entryPredicate : BackstackEntry NavValue → Bool`. -/
def mkEntryPredClosure (p : Model.BackstackEntry NavValue → Bool) : NavClosure :=
  .host fun v =>
    match v with
    | .ext (.entry e) => some (.boxedBool (p e))
    | _ => none

/-- Construct a host closure for `predicate : NavValue → Bool`. -/
def mkValuePredClosure (p : NavValue → Bool) : NavClosure :=
  .host fun v =>
    match NavValue.ofJvmVal? v with
    | some nv => some (.boxedBool (p nv))
    | none => none

/-- Construct a host closure for `valueFactory : BackstackEntry NavValue → NavValue`. -/
def mkValueFactoryClosure (f : Model.BackstackEntry NavValue → NavValue) : NavClosure :=
  .host fun v =>
    match v with
    | .ext (.entry e) => some (f e).toJvmVal
    | _ => none

/-- Simulated mutable heap storing `MutableBackstackMap`s, closures, and `Uuid.random()` counter. -/
structure NavHeap where
  maps : Array (Model.BackstackMap NavValue) := #[]
  closures : Array NavClosure := #[]
  nextRandomId : Model.EntryId := 1000
  deriving Inhabited

abbrev JvmState := Jvm.JvmState NavExt NavHeap

def normalizeNavClass : String → String
  | "com/alexvanyo/composelife/navigation/BackstackNavigationKt" => "BackstackNavigationKt"
  | "com/alexvanyo/composelife/navigation/BackstackEntry" => "BackstackEntry"
  | cls => cls

def beqNavExt : NavExt → NavExt → Bool :=
  fun a b => decide (a = b)

def beqRefNavExt : NavExt → NavExt → Option Bool
  | .uuid a, .uuid b => some (a == b)
  | .mapRef a, .mapRef b => some (a == b)
  | .closureRef a, .closureRef b => some (a == b)
  | .obj a, .obj b => some (a == b)
  | .entry a, .entry b => some (a == b)
  | _, _ => none

def initNavJvmState (slots : List (Nat × JvmVal))
    (heap : NavHeap := {}) (jvmHeap : Jvm.JvmHeap NavExt := {}) : JvmState :=
  Jvm.initJvmState slots (.i32 0) heap jvmHeap

def allocClosure (h : NavHeap) (c : NavClosure) : Nat × NavHeap :=
  let id := h.closures.size
  (id, { h with closures := h.closures.push c })

def assignLinearLocals (idx : Nat) : List JvmVal → List (Nat × JvmVal)
  | [] => []
  | v :: vs => (idx, v) :: assignLinearLocals (idx + 1) vs

def assignParamLocalsAux (idx : Nat) : List Char → List JvmVal → List (Nat × JvmVal)
  | 'J' :: tags, v :: vs | 'D' :: tags, v :: vs => (idx, v) :: assignParamLocalsAux (idx + 2) tags vs
  | _ :: tags, v :: vs => (idx, v) :: assignParamLocalsAux (idx + 1) tags vs
  | _, _ => []

/-- Extract `(fnTag, boxBoolReturn)` from a `LambdaMetafactory` bootstrap method handle. -/
def extractBsmTarget : String → Option (String × Bool)
  | "REF_invokeStatic com/alexvanyo/composelife/navigation/BackstackNavigationKt.popUpTo$lambda$2:(Lkotlin/uuid/Uuid;Lcom/alexvanyo/composelife/navigation/BackstackEntry;)Z" =>
    some ("BackstackNavigationKt.popUpTo$lambda$2:(Lkotlin/uuid/Uuid;Lcom/alexvanyo/composelife/navigation/BackstackEntry;)Z", true)
  | "REF_invokeStatic com/alexvanyo/composelife/navigation/BackstackNavigationKt.popUpTo$lambda$3:(Lkotlin/jvm/functions/Function1;Lcom/alexvanyo/composelife/navigation/BackstackEntry;)Z" =>
    some ("BackstackNavigationKt.popUpTo$lambda$3:(Lkotlin/jvm/functions/Function1;Lcom/alexvanyo/composelife/navigation/BackstackEntry;)Z", true)
  | "REF_invokeStatic com/alexvanyo/composelife/navigation/BackstackNavigationKt.navigate$lambda$0:(Ljava/lang/Object;Lcom/alexvanyo/composelife/navigation/BackstackEntry;)Ljava/lang/Object;" =>
    some ("BackstackNavigationKt.navigate$lambda$0:(Ljava/lang/Object;Lcom/alexvanyo/composelife/navigation/BackstackEntry;)Ljava/lang/Object;", false)
  | _ => none

private def resolveNavStatic (_st : JvmState) (cls field _desc : String) : Option JvmVal :=
  match cls, field with
  | "kotlin/uuid/Uuid", "Companion" => some (.ext (.companion "kotlin/uuid/Uuid$Companion"))
  | _, _ => none

private def checkNavInstanceOf (cls : String) (v : JvmVal) : Bool :=
  match normalizeNavClass cls, v with
  | "BackstackEntry", .ext (.entry _) => true
  | "kotlin/uuid/Uuid", .ext (.uuid _) => true
  | "java/util/Map", .ext (.mapRef _) => true
  | "kotlin/jvm/functions/Function1", .ext (.closureRef _) => true
  | "java/lang/Object", .ext _ => true
  | _, _ => Jvm.defaultCheckInstanceOf (fun _ _ => false) cls v

private def checkNavCast (cls : String) (v : JvmVal) : Option JvmVal :=
  match normalizeNavClass cls, v with
  | "BackstackEntry", .ext (.entry _) => some v
  | "kotlin/uuid/Uuid", .ext (.uuid _) => some v
  | "java/util/Map", .ext (.mapRef _) => some v
  | "kotlin/jvm/functions/Function1", .ext (.closureRef _) => some v
  | "java/lang/Object", .ext _ => some v
  | _, _ => Jvm.defaultCheckCast (fun _ _ => none) cls v

def boxBoolIfNeeded (boxBool : Bool) (v : JvmVal) : Option JvmVal :=
  if boxBool then
    match v with
    | .i32 n => some (.boxedBool (n != 0))
    | .bool b => some (.boxedBool b)
    | .boxedBool b => some (.boxedBool b)
    | _ => none
  else
    some v

/-- Hook builder parameterized by bytecode lookup (`resolveProg`) and bounded recursion depth/fuel. -/
def mkNavHooks (resolveProg : String → Option (List JvmInstr)) (depth fuel : Nat) :
    Jvm.JvmHooks NavExt NavHeap :=
  match depth with
  | 0 => {
      beqExt := beqNavExt
      beqRefExt := beqRefNavExt
      checkInstanceOf := checkNavInstanceOf
      checkCast := checkNavCast
      resolveStatic := resolveNavStatic
    }
  | d + 1 =>
    let invokeClosure : JvmState → Nat → List JvmVal → Option (JvmVal × JvmState) :=
      fun st cid args =>
        match st.heap.closures[cid]? with
        | some (.host fn) =>
          match args with
          | [a0] => (fn a0).map (fun r => (r, st))
          | _ => none
        | some (.bytecode fnTag captures boxBool) =>
          match resolveProg fnTag with
          | some prog =>
            let hooks := mkNavHooks resolveProg d fuel
            let subSt : JvmState := {
              pc := 0
              stack := []
              locals := (assignLinearLocals 0 (captures ++ args)).foldl
                (fun loc (i, v) => setLocal loc i v) (fun _ => .i32 0)
              jvmHeap := st.jvmHeap
              heap := st.heap
            }
            match Jvm.runJvmRes hooks fuel prog subSt with
            | some (res, endSt) =>
              match boxBoolIfNeeded boxBool res with
              | some res' => some (res', { st with jvmHeap := endSt.jvmHeap, heap := endSt.heap })
              | none => none
            | none => none
          | none => none
        | none => none
    let invokeProg : JvmState → String → String → List JvmVal → Option (JvmVal × JvmState) :=
      fun st fnTag desc args =>
        match resolveProg fnTag with
        | some prog =>
          let hooks := mkNavHooks resolveProg d fuel
          let tags := Jvm.parseMethodParamTags desc
          let subSt : JvmState := {
            pc := 0
            stack := []
            locals := (assignParamLocalsAux 0 tags args).foldl
              (fun loc (i, v) => setLocal loc i v) (fun _ => .i32 0)
            jvmHeap := st.jvmHeap
            heap := st.heap
          }
          match Jvm.runJvmRes hooks fuel prog subSt with
          | some (res, endSt) => some (res, { st with jvmHeap := endSt.jvmHeap, heap := endSt.heap })
          | none => none
        | none => none
    {
      beqExt := beqNavExt
      beqRefExt := beqRefNavExt
      checkInstanceOf := checkNavInstanceOf
      checkCast := checkNavCast
      resolveStatic := resolveNavStatic
      stepInvokeSpecial := fun st cls method desc =>
        match normalizeNavClass cls, method, desc, st.stack with
        | "BackstackEntry", "<init>",
            "(Ljava/lang/Object;Lcom/alexvanyo/composelife/navigation/BackstackEntry;Lkotlin/uuid/Uuid;)V",
            .ext (.uuid id) :: prevVal :: valJvm :: .allocRef _ :: .allocRef _ :: rest =>
          let prev? : Option (Option (Model.BackstackEntry NavValue)) :=
            match prevVal with
            | .null => some none
            | .ext (.entry p) => some (some p)
            | _ => none
          match prev?, NavValue.ofJvmVal? valJvm with
          | some prevOpt, some nv =>
            let entry := Model.BackstackEntry.mk nv prevOpt id
            .inl (some { st with pc := st.pc + 1, stack := .ext (.entry entry) :: rest })
          | _, _ => .inr none
        | _, _, _, _ => .inr none
      stepInvokeVirtual := fun st cls method desc =>
        match normalizeNavClass cls, method, desc, st.stack with
        | "BackstackEntry", "getId", "()Lkotlin/uuid/Uuid;", .ext (.entry e) :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := .ext (.uuid e.id) :: rest })
        | "BackstackEntry", "getPrevious", "()Lcom/alexvanyo/composelife/navigation/BackstackEntry;",
            .ext (.entry e) :: rest =>
          let pv : JvmVal := match e.previous with | none => .null | some p => .ext (.entry p)
          .inl (some { st with pc := st.pc + 1, stack := pv :: rest })
        | "BackstackEntry", "getValue", "()Ljava/lang/Object;", .ext (.entry e) :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := e.value.toJvmVal :: rest })
        | "kotlin/uuid/Uuid$Companion", "random", "()Lkotlin/uuid/Uuid;",
            .ext (.companion "kotlin/uuid/Uuid$Companion") :: rest =>
          let newId := st.heap.nextRandomId
          let heap' := { st.heap with nextRandomId := newId + 1 }
          .inl (some { st with pc := st.pc + 1, stack := .ext (.uuid newId) :: rest, heap := heap' })
        | _, _, _, _ => .inr none
      stepInvokeStatic := fun st cls method desc =>
        match normalizeNavClass cls, method, desc, st.stack with
        | "kotlin/collections/MapsKt", "getValue", "(Ljava/util/Map;Ljava/lang/Object;)Ljava/lang/Object;",
            .ext (.uuid keyId) :: .ext (.mapRef mid) :: rest =>
          match st.heap.maps[mid]? with
          | some m =>
            match Model.mapLookup m keyId with
            | some entry => .inl (some { st with pc := st.pc + 1, stack := .ext (.entry entry) :: rest })
            | none => .inr none
          | none => .inr none
        | nCls, _, _, stackNow =>
          let nArgs := (Jvm.parseMethodParamTags desc).length
          if stackNow.length < nArgs then .inr none
          else
            let popped := stackNow.take nArgs
            let rest := stackNow.drop nArgs
            let fnTag := nCls ++ "." ++ method ++ ":" ++ desc
            match invokeProg st fnTag desc popped.reverse with
            | some (res, st') => .inl (some { st' with pc := st.pc + 1, stack := res :: rest })
            | none => .inr none
      stepInvokeInterface := fun st cls method desc =>
        match cls, method, desc, st.stack with
        | "java/util/Map", "put", "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;",
            .ext (.entry e) :: .ext (.uuid k) :: .ext (.mapRef mid) :: rest =>
          if h : mid < st.heap.maps.size then
            let m := st.heap.maps[mid]
            let prevVal : JvmVal := match Model.mapLookup m k with | some p => .ext (.entry p) | none => .null
            let heap' := { st.heap with maps := st.heap.maps.set mid (Model.mapPut m k e) h }
            .inl (some { st with pc := st.pc + 1, stack := prevVal :: rest, heap := heap' })
          else .inr none
        | "java/util/Map", "remove", "(Ljava/lang/Object;)Ljava/lang/Object;",
            .ext (.uuid k) :: .ext (.mapRef mid) :: rest =>
          if h : mid < st.heap.maps.size then
            let m := st.heap.maps[mid]
            let prevVal : JvmVal := match Model.mapLookup m k with | some p => .ext (.entry p) | none => .null
            let heap' := { st.heap with maps := st.heap.maps.set mid (Model.mapRemove m k) h }
            .inl (some { st with pc := st.pc + 1, stack := prevVal :: rest, heap := heap' })
          else .inr none
        | "kotlin/jvm/functions/Function1", "invoke", "(Ljava/lang/Object;)Ljava/lang/Object;",
            a0 :: .ext (.closureRef cid) :: rest =>
          match invokeClosure st cid [a0] with
          | some (res, st') => .inl (some { st' with pc := st.pc + 1, stack := res :: rest })
          | none => .inr none
        | _, _, _, _ => .inr none
      stepInvokeDynamic := fun st bsmKind bsmArg desc =>
        if bsmKind == "LambdaMetafactory" then
          let nCaps := (Jvm.parseMethodParamTags desc).length
          if st.stack.length < nCaps then .inr none
          else
            match extractBsmTarget bsmArg with
            | some (fnTag, boxBool) =>
              let caps := (st.stack.take nCaps).reverse
              let rest := st.stack.drop nCaps
              let (cid, heap') := allocClosure st.heap (.bytecode fnTag caps boxBool)
              .inl (some { st with pc := st.pc + 1, stack := .ext (.closureRef cid) :: rest, heap := heap' })
            | none => .inr none
        else .inr none
    }

end Navigation.JvmVerification
