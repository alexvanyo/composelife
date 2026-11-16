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
import models.ResourceStateModel

namespace ResourceState.JvmVerification

export Jvm (JvmInstr setLocal initJvmState)

/-- Concrete non-null Kotlin payload values carried inside `ResourceState.Success`. -/
inductive RsVal where
  | str (s : String)
  | int (v : UInt32)
  | long (v : UInt64)
  | bool (b : Bool)
  | unit
  | obj (id : Nat)
  | pair (fst snd : RsVal)
  deriving DecidableEq, Repr, Inhabited

/-- Domain-specific extension values on the JVM stack and in locals. -/
inductive RsExt where
  | res (r : Model.ResourceState RsVal)
  | throwable (t : Model.ThrowableModel)
  | objRef (id : Nat)
  | valList (xs : List RsVal)
  | flow (tr : Model.FlowTrace RsVal)
  | resFlow (tr : Model.FlowTrace (Model.ResourceState RsVal))
  | transformStub (kind : String) (resFlow? : Option (Model.FlowTrace (Model.ResourceState RsVal)))
  | continuation
  | composer
  | composeState (value : Model.ResourceState RsVal)
  | closureRef (cid : Nat)
  | unit
  deriving DecidableEq, Repr, Inhabited

abbrev JvmVal := Jvm.JvmVal RsExt

def RsVal.toJvmVal : RsVal → JvmVal
  | .str s => .str s
  | .int v => .boxedInt v
  | .long v => .boxedLong v
  | .bool b => .boxedBool b
  | .unit => .ext .unit
  | .obj id => .ext (.objRef id)
  | .pair a b => .pair a.toJvmVal b.toJvmVal

def RsVal.ofJvmVal? : JvmVal → Option RsVal
  | .str s => some (.str s)
  | .boxedInt v => some (.int v)
  | .boxedLong v => some (.long v)
  | .boxedBool b => some (.bool b)
  | .ext .unit => some .unit
  | .ext (.objRef id) => some (.obj id)
  | .pair a b =>
    match RsVal.ofJvmVal? a, RsVal.ofJvmVal? b with
    | some pa, some pb => some (.pair pa pb)
    | _, _ => none
  | _ => none

@[simp] theorem RsVal.ofJvmVal?_toJvmVal (v : RsVal) :
    RsVal.ofJvmVal? v.toJvmVal = some v := by
  induction v with
  | str _ => rfl
  | int _ => rfl
  | long _ => rfl
  | bool _ => rfl
  | unit => rfl
  | obj _ => rfl
  | pair a b iha ihb => simp [RsVal.toJvmVal, RsVal.ofJvmVal?, iha, ihb]

/-- Closure representations stored in `RsHeap` for `Function1`/`Function2`/`Function3`. -/
inductive RsClosure where
  | fn1 (f : JvmVal → Option JvmVal)
  | listFn1 (f : List RsVal → RsVal)
  | fn2 (f : JvmVal → JvmVal → Option JvmVal)
  | fn3 (f : JvmVal → JvmVal → JvmVal → Option JvmVal)

instance : Inhabited RsClosure := ⟨.fn1 (fun _ => none)⟩

/-- Verification heap holding transform closures and Compose tracing flag. -/
structure RsHeap where
  closures : Array RsClosure := #[]
  traceEnabled : Bool := false
  deriving Inhabited

abbrev JvmState := Jvm.JvmState RsExt RsHeap

def normalizeRsClass : String → String
  | "com/alexvanyo/composelife/resourcestate/ResourceStateKt" => "ResourceStateKt"
  | "com/alexvanyo/composelife/resourcestate/ResourceState" => "ResourceState"
  | "com/alexvanyo/composelife/resourcestate/ResourceState$Loading" => "ResourceState$Loading"
  | "com/alexvanyo/composelife/resourcestate/ResourceState$Success" => "ResourceState$Success"
  | "com/alexvanyo/composelife/resourcestate/ResourceState$Failure" => "ResourceState$Failure"
  | "com/alexvanyo/composelife/resourcestate/CompositeException" => "CompositeException"
  | "com/alexvanyo/composelife/resourcestate/ResourceStateKt$successes$$inlined$transform$1" =>
    "ResourceStateKt$successes$$inlined$transform$1"
  | "com/alexvanyo/composelife/resourcestate/ResourceStateKt$asResourceState$$inlined$map$1" =>
    "ResourceStateKt$asResourceState$$inlined$map$1"
  | "com/alexvanyo/composelife/resourcestate/ResourceStateKt$asResourceState$2" =>
    "ResourceStateKt$asResourceState$2"
  | cls => cls

def beqRsExt : RsExt → RsExt → Bool :=
  fun a b => decide (a = b)

def beqRefRsExt : RsExt → RsExt → Option Bool
  | .res .loading, .res .loading => some true
  | .res .loading, .res (.success _) | .res (.success _), .res .loading => some false
  | .res .loading, .res (.failure _) | .res (.failure _), .res .loading => some false
  | .closureRef a, .closureRef b => some (a == b)
  | .composer, .composer => some true
  | .unit, .unit => some true
  | _, _ => none

def initRsJvmState (slots : List (Nat × JvmVal))
    (heap : RsHeap := {}) (jvmHeap : Jvm.JvmHeap RsExt := {}) : JvmState :=
  Jvm.initJvmState slots (.i32 0) heap jvmHeap

def allocFn1Closure (h : RsHeap) (f : RsVal → RsVal) : Nat × RsHeap :=
  let id := h.closures.size
  let cl : RsClosure := .fn1 (fun v => (RsVal.ofJvmVal? v).map (fun x => (f x).toJvmVal))
  (id, { h with closures := h.closures.push cl })

def allocFlatMapClosure (h : RsHeap) (f : RsVal → Model.ResourceState RsVal) : Nat × RsHeap :=
  let id := h.closures.size
  let cl : RsClosure := .fn1 (fun v => (RsVal.ofJvmVal? v).map (fun x => .ext (.res (f x))))
  (id, { h with closures := h.closures.push cl })

def allocListFn1Closure (h : RsHeap) (f : List RsVal → RsVal) : Nat × RsHeap :=
  let id := h.closures.size
  (id, { h with closures := h.closures.push (.listFn1 f) })

def allocFn2Closure (h : RsHeap) (f : RsVal → RsVal → RsVal) : Nat × RsHeap :=
  let id := h.closures.size
  let cl : RsClosure := .fn2 (fun a b =>
    match RsVal.ofJvmVal? a, RsVal.ofJvmVal? b with
    | some pa, some pb => some (f pa pb).toJvmVal
    | _, _ => none)
  (id, { h with closures := h.closures.push cl })

def allocFn3Closure (h : RsHeap) (f : RsVal → RsVal → RsVal → RsVal) : Nat × RsHeap :=
  let id := h.closures.size
  let cl : RsClosure := .fn3 (fun a b c =>
    match RsVal.ofJvmVal? a, RsVal.ofJvmVal? b, RsVal.ofJvmVal? c with
    | some pa, some pb, some pc => some (f pa pb pc).toJvmVal
    | _, _, _ => none)
  (id, { h with closures := h.closures.push cl })

private def resolveRsStatic (_st : JvmState) (cls field _desc : String) : Option JvmVal :=
  match normalizeRsClass cls, field with
  | "ResourceState$Loading", "INSTANCE" => some (.ext (.res .loading))
  | "kotlin/Unit", "INSTANCE" => some (.ext .unit)
  | _, _ => none

private def checkRsInstanceOf (cls : String) (v : JvmVal) : Bool :=
  match normalizeRsClass cls, v with
  | "ResourceState$Loading", .ext (.res .loading) => true
  | "ResourceState$Success", .ext (.res (.success _)) => true
  | "ResourceState$Failure", .ext (.res (.failure _)) => true
  | "ResourceState", .ext (.res _) => true
  | "CompositeException", .ext (.throwable (.composite _)) => true
  | "java/lang/Throwable", .ext (.throwable _) => true
  | "java/lang/Object", .ext _ => true
  | _, _ => false

private def checkRsCast (cls : String) (v : JvmVal) : Option JvmVal :=
  match normalizeRsClass cls, v with
  | "ResourceState$Loading", .ext (.res .loading) => some v
  | "ResourceState$Success", .ext (.res (.success _)) => some v
  | "ResourceState$Failure", .ext (.res (.failure _)) => some v
  | "ResourceState", .ext (.res _) => some v
  | "CompositeException", .ext (.throwable (.composite _)) => some v
  | "java/lang/Throwable", .ext (.throwable _) => some v
  | "kotlinx/coroutines/flow/Flow", .ext (.flow _) => some v
  | "kotlinx/coroutines/flow/Flow", .ext (.resFlow _) => some v
  | "kotlin/jvm/functions/Function1", .ext (.closureRef _) => some v
  | "kotlin/jvm/functions/Function2", .ext (.closureRef _) => some v
  | "kotlin/jvm/functions/Function2", .ext (.transformStub _ _) => some v
  | "kotlin/jvm/functions/Function3", .ext (.closureRef _) => some v
  | "kotlin/jvm/functions/Function3", .ext (.transformStub _ _) => some v
  | "java/lang/Object", .ext _ => some v
  | _, _ => Jvm.defaultCheckCast (fun _ _ => none) cls v

def extractThrowableList? (jh : Jvm.JvmHeap RsExt) (addr : Nat) :
    Option (List Model.ThrowableModel) :=
  match Jvm.extractListArray? jh addr with
  | some elems =>
    elems.toList.mapM fun
      | .ext (.throwable t) => some t
      | _ => none
  | none => none

def extractRsValList? (jh : Jvm.JvmHeap RsExt) (addr : Nat) : Option (List RsVal) :=
  match Jvm.extractListArray? jh addr with
  | some elems => elems.toList.mapM RsVal.ofJvmVal?
  | none => none

def invokeRsClosure (st : JvmState) (cid : Nat) (args : List JvmVal) : Option JvmVal :=
  match st.heap.closures[cid]? with
  | some (.fn1 f) =>
    match args with
    | [a0] => f a0
    | _ => none
  | some (.listFn1 f) =>
    match args with
    | [.heapRef listAddr] =>
      (extractRsValList? st.jvmHeap listAddr).map (fun xs => (f xs).toJvmVal)
    | _ => none
  | some (.fn2 f) =>
    match args with
    | [a0, a1] => f a0 a1
    | _ => none
  | some (.fn3 f) =>
    match args with
    | [a0, a1, a2] => f a0 a1 a2
    | _ => none
  | none => none

def assignParamLocalsAux (idx : Nat) : List Char → List JvmVal → List (Nat × JvmVal)
  | 'J' :: tags, v :: vs | 'D' :: tags, v :: vs => (idx, v) :: assignParamLocalsAux (idx + 2) tags vs
  | _ :: tags, v :: vs => (idx, v) :: assignParamLocalsAux (idx + 1) tags vs
  | _, _ => []

/-- Configurable JVM hooks parameterized by a program lookup table and bounded sub-call depth/fuel. -/
def mkRsHooks (resolveProg : String → Option (List JvmInstr)) (depth fuel : Nat) :
    Jvm.JvmHooks RsExt RsHeap :=
  match depth with
  | 0 => {
      beqExt := beqRsExt
      beqRefExt := beqRefRsExt
      checkInstanceOf := checkRsInstanceOf
      checkCast := checkRsCast
      resolveStatic := resolveRsStatic
    }
  | d + 1 =>
    let invokeProg : JvmState → String → String → List JvmVal → Option (JvmVal × JvmState) :=
      fun st fnTag desc args =>
        match resolveProg fnTag with
        | some prog =>
          let hooks := mkRsHooks resolveProg d fuel
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
      beqExt := beqRsExt
      beqRefExt := beqRefRsExt
      checkInstanceOf := checkRsInstanceOf
      checkCast := checkRsCast
      resolveStatic := resolveRsStatic
      stepInvokeSpecial := fun st cls method desc =>
        match normalizeRsClass cls, method, desc, st.stack with
        | "ResourceState$Success", "<init>", "(Ljava/lang/Object;)V",
            v :: .allocRef _ :: .allocRef _ :: rest =>
          match RsVal.ofJvmVal? v with
          | some pv =>
            .inl (some { st with pc := st.pc + 1, stack := .ext (.res (.success pv)) :: rest })
          | none => .inr none
        | "ResourceState$Failure", "<init>", "(Ljava/lang/Throwable;)V",
            .ext (.throwable t) :: .allocRef _ :: .allocRef _ :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := .ext (.res (.failure t)) :: rest })
        | "CompositeException", "<init>", "(Ljava/util/List;)V",
            .heapRef listAddr :: .allocRef _ :: .allocRef _ :: rest =>
          match extractThrowableList? st.jvmHeap listAddr with
          | some ts =>
            if 2 ≤ ts.length then
              .inl (some {
                st with
                pc := st.pc + 1
                stack := .ext (.throwable (.composite ts)) :: rest
              })
            else .inr none
          | none => .inr none
        | "ResourceStateKt$successes$$inlined$transform$1", "<init>", _,
            _cont :: .ext (.resFlow tr) :: .allocRef _ :: .allocRef _ :: rest =>
          .inl (some {
            st with
            pc := st.pc + 1
            stack := .ext (.transformStub "successes" (some tr)) :: rest
          })
        | "ResourceStateKt$asResourceState$$inlined$map$1", "<init>", _,
            .ext (.flow tr) :: .allocRef _ :: .allocRef _ :: rest =>
          let mapped : Model.FlowTrace (Model.ResourceState RsVal) :=
            { emissions := tr.emissions.map Model.ResourceState.success, terminalFailure? := tr.terminalFailure? }
          .inl (some { st with pc := st.pc + 1, stack := .ext (.resFlow mapped) :: rest })
        | "ResourceStateKt$asResourceState$2", "<init>", _,
            _cont :: .allocRef _ :: .allocRef _ :: rest =>
          .inl (some {
            st with
            pc := st.pc + 1
            stack := .ext (.transformStub "asResourceState$catch" none) :: rest
          })
        | _, _, _, _ => .inr none
      stepInvokeVirtual := fun st cls method _desc =>
        match normalizeRsClass cls, method, st.stack with
        | "ResourceState$Success", "getValue", .ext (.res (.success v)) :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := v.toJvmVal :: rest })
        | "ResourceState$Failure", "getThrowable", .ext (.res (.failure t)) :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := .ext (.throwable t) :: rest })
        | _, _, _ => .inr none
      stepInvokeStatic := fun st cls method desc =>
        match normalizeRsClass cls, method, desc, st.stack with
        | "kotlin/collections/CollectionsKt", "first", "(Ljava/util/List;)Ljava/lang/Object;",
            .heapRef listAddr :: rest =>
          match Jvm.extractListArray? st.jvmHeap listAddr with
          | some elems =>
            if h : 0 < elems.size then
              .inl (some { st with pc := st.pc + 1, stack := elems[0] :: rest })
            else .inr none
          | none => .inr none
        | "kotlinx/coroutines/flow/FlowKt", "flow", _,
            .ext (.transformStub "successes" (some tr)) :: rest =>
          .inl (some {
            st with
            pc := st.pc + 1
            stack := .ext (.resFlow (Model.successesFlow tr)) :: rest
          })
        | "kotlinx/coroutines/flow/FlowKt", "first", _,
            _cont :: .ext (.resFlow tr) :: rest =>
          match tr.emissions.head? with
          | some headRes =>
            .inl (some { st with pc := st.pc + 1, stack := .ext (.res headRes) :: rest })
          | none => .inr none
        | "kotlinx/coroutines/flow/FlowKt", "catch", _,
            .ext (.transformStub "asResourceState$catch" none) :: .ext (.resFlow mapped) :: rest =>
          let caught : Model.FlowTrace (Model.ResourceState RsVal) :=
            match mapped.terminalFailure? with
            | some t => { emissions := mapped.emissions ++ [.failure t], terminalFailure? := none }
            | none => { emissions := mapped.emissions, terminalFailure? := none }
          .inl (some { st with pc := st.pc + 1, stack := .ext (.resFlow caught) :: rest })
        | "androidx/compose/runtime/ComposerKt", "sourceInformationMarkerStart", _,
            _info :: _key :: .ext .composer :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := rest })
        | "androidx/compose/runtime/ComposerKt", "sourceInformationMarkerEnd", _,
            .ext .composer :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := rest })
        | "androidx/compose/runtime/ComposerKt", "isTraceInProgress", "()Z", rest =>
          let v : UInt32 := if st.heap.traceEnabled then 1 else 0
          .inl (some { st with pc := st.pc + 1, stack := .i32 v :: rest })
        | "androidx/compose/runtime/ComposerKt", "traceEventStart", _,
            _sig :: _dirty :: _changed :: _key :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := rest })
        | "androidx/compose/runtime/ComposerKt", "traceEventEnd", "()V", rest =>
          .inl (some { st with pc := st.pc + 1, stack := rest })
        | "androidx/compose/runtime/SnapshotStateKt", "collectAsState", _,
            _default :: _changed :: .ext .composer :: _policy :: _ctx ::
              .ext (.res initVal) :: .ext (.resFlow tr) :: rest =>
          let cur := tr.emissions.getLast?.getD initVal
          .inl (some { st with pc := st.pc + 1, stack := .ext (.composeState cur) :: rest })
        | nCls, _, _, stackNow =>
          let nArgs := (Jvm.parseMethodParamTags desc).length
          if stackNow.length < nArgs then .inr none
          else
            let popped := stackNow.take nArgs
            let rest := stackNow.drop nArgs
            let fnTag := nCls ++ "." ++ method
            match invokeProg st fnTag desc popped.reverse with
            | some (res, st') =>
              .inl (some { st' with pc := st.pc + 1, stack := res :: rest })
            | none => .inr none
      stepInvokeInterface := fun st cls method desc =>
        match cls, method, desc, st.stack with
        | "java/util/Collection", "isEmpty", "()Z", .heapRef listAddr :: rest =>
          match Jvm.extractListArray? st.jvmHeap listAddr with
          | some elems =>
            .inl (some {
              st with
              pc := st.pc + 1
              stack := .i32 (if elems.isEmpty then 1 else 0) :: rest
            })
          | none => .inr none
        | "java/util/List", "size", "()I", .heapRef listAddr :: rest =>
          match Jvm.extractListArray? st.jvmHeap listAddr with
          | some elems =>
            .inl (some {
              st with
              pc := st.pc + 1
              stack := .i32 (UInt32.ofNat elems.size) :: rest
            })
          | none => .inr none
        | "java/util/List", "get", "(I)Ljava/lang/Object;", idxVal :: .heapRef listAddr :: rest =>
          match idxVal.asI32?, Jvm.extractListArray? st.jvmHeap listAddr with
          | some idx, some elems =>
            if idx.toBitVec.slt 0#32 then .inr none
            else if h : idx.toNat < elems.size then
              .inl (some { st with pc := st.pc + 1, stack := elems[idx.toNat] :: rest })
            else .inr none
          | _, _ => .inr none
        | "kotlin/jvm/functions/Function1", "invoke", _, a0 :: .ext (.closureRef cid) :: rest =>
          match invokeRsClosure st cid [a0] with
          | some res => .inl (some { st with pc := st.pc + 1, stack := res :: rest })
          | none => .inr none
        | "kotlin/jvm/functions/Function2", "invoke", _, a1 :: a0 :: .ext (.closureRef cid) :: rest =>
          match invokeRsClosure st cid [a0, a1] with
          | some res => .inl (some { st with pc := st.pc + 1, stack := res :: rest })
          | none => .inr none
        | "kotlin/jvm/functions/Function3", "invoke", _,
            a2 :: a1 :: a0 :: .ext (.closureRef cid) :: rest =>
          match invokeRsClosure st cid [a0, a1, a2] with
          | some res => .inl (some { st with pc := st.pc + 1, stack := res :: rest })
          | none => .inr none
        | _, _, _, _ => .inr none
    }

def rsHooks : Jvm.JvmHooks RsExt RsHeap :=
  mkRsHooks (fun _ => none) 2 64

abbrev runJvm (fuel : Nat) (prog : List JvmInstr) (st : JvmState) : Option JvmVal :=
  Jvm.runJvm rsHooks fuel prog st

abbrev runJvmRes (fuel : Nat) (prog : List JvmInstr) (st : JvmState) : Option (JvmVal × JvmState) :=
  Jvm.runJvmRes rsHooks fuel prog st

/-- Build a JVM `Array<ResourceState<*>>` on `jh` from a `List (Model.ResourceState RsVal)`. -/
def allocResourceStateArray (jh : Jvm.JvmHeap RsExt) (states : List (Model.ResourceState RsVal)) :
    Nat × Jvm.JvmHeap RsExt :=
  let elems := (states.map fun r => (.ext (.res r) : JvmVal)).toArray
  jh.alloc (.objArray "com/alexvanyo/composelife/resourcestate/ResourceState" elems)

end ResourceState.JvmVerification
