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
import ComposeSemantics
import MosaicSemantics
import models.CalculatorModel

namespace MosaicCalculator.JvmVerification

export Jvm (JvmInstr setLocal initJvmState)

/-- Calculator + Compose + Mosaic domain-specific extension values on JVM stack/locals. -/
inductive CalcExt where
  | calcOp (op : Model.CalculatorOp)
  | calcErr (err : Model.CalculatorError)
  | calcKey (k : Model.CalculatorKey)
  | calcState (st : Model.CalculatorState)
  | evalRes (r : Model.CheckedEvalResult)
  | keyEvent (key : String)
  | composerEmpty
  | composer
  | scopeUpdateScope (groupKey : Int32)
  | stateRef (stateId : Nat)
  | modifier (onKeyHandlerId? : Option Nat)
  | closureRef (closureId : Nat)
  | companion (cls : String)
  | unit
  deriving DecidableEq, Repr, Inhabited

abbrev JvmVal := Jvm.JvmVal CalcExt

/-- Combined Compose slot-table + closure table + Mosaic node builder heap state. -/
structure CalcHeap where
  composer : Compose.ComposerModel JvmVal := {}
  closures : Array (String × List JvmVal) := #[]
  nodeStack : List (List Mosaic.MosaicNode × Option Nat) := []
  emittedRoot? : Option Mosaic.MosaicNode := none
  deriving Inhabited

abbrev JvmState := Jvm.JvmState CalcExt CalcHeap

/-- Exact Java `String.hashCode()` over UTF-16 code units matching `lookupswitch` tables. -/
def javaStringHashCode (s : String) : UInt32 :=
  s.toList.foldl (fun h c => h * 31 + UInt32.ofNat c.toNat) 0

/-- Strip the calculator package prefix consistently via pattern matching for fast kernel reduction. -/
def normalizeCalcClass : String → String
  | "com/alexvanyo/composelife/mosaiccalculator/CalculatorEngineKt" => "CalculatorEngineKt"
  | "com/alexvanyo/composelife/mosaiccalculator/CalculatorScreenKt" => "CalculatorScreenKt"
  | "com/alexvanyo/composelife/mosaiccalculator/ComposableSingletons$CalculatorScreenKt" =>
    "ComposableSingletons$CalculatorScreenKt"
  | "com/alexvanyo/composelife/mosaiccalculator/CalculatorOp" => "CalculatorOp"
  | "com/alexvanyo/composelife/mosaiccalculator/CalculatorError" => "CalculatorError"
  | "com/alexvanyo/composelife/mosaiccalculator/CalculatorKey" => "CalculatorKey"
  | "com/alexvanyo/composelife/mosaiccalculator/CalculatorKey$Digit" => "CalculatorKey$Digit"
  | "com/alexvanyo/composelife/mosaiccalculator/CalculatorKey$Op" => "CalculatorKey$Op"
  | "com/alexvanyo/composelife/mosaiccalculator/CalculatorKey$Equals" => "CalculatorKey$Equals"
  | "com/alexvanyo/composelife/mosaiccalculator/CalculatorKey$Clear" => "CalculatorKey$Clear"
  | "com/alexvanyo/composelife/mosaiccalculator/CalculatorKey$Backspace" => "CalculatorKey$Backspace"
  | "com/alexvanyo/composelife/mosaiccalculator/CalculatorState" => "CalculatorState"
  | "com/alexvanyo/composelife/mosaiccalculator/CalculatorState$Companion" => "CalculatorState$Companion"
  | "com/alexvanyo/composelife/mosaiccalculator/CheckedEvalResult" => "CheckedEvalResult"
  | "com/alexvanyo/composelife/mosaiccalculator/CheckedEvalResult$Value" => "CheckedEvalResult$Value"
  | "com/alexvanyo/composelife/mosaiccalculator/CheckedEvalResult$Error" => "CheckedEvalResult$Error"
  | cls => cls

/-- Equality on `CalcExt` values used by `Intrinsics.areEqual` and Compose `changed` slots. -/
def beqCalcExt : CalcExt → CalcExt → Bool :=
  fun a b => decide (a = b)

/-- Reference identity on `CalcExt` used by `if_acmpeq` / `if_acmpne`. -/
def beqRefCalcExt : CalcExt → CalcExt → Option Bool
  | .composerEmpty, .composerEmpty => some true
  | .composerEmpty, .stateRef _ => some false
  | .stateRef _, .composerEmpty => some false
  | .composerEmpty, .closureRef _ => some false
  | .closureRef _, .composerEmpty => some false
  | .composerEmpty, .composer => some false
  | .composer, .composerEmpty => some false
  | .stateRef a, .stateRef b => some (a == b)
  | .closureRef a, .closureRef b => some (a == b)
  | .composer, .composer => some true
  | .calcKey a, .calcKey b =>
    match a, b with
    | .clear, .clear | .equals, .equals | .backspace, .backspace => some true
    | .clear, _ | _, .clear | .equals, _ | _, .equals | .backspace, _ | _, .backspace => some false
    | _, _ => none
  | .calcOp a, .calcOp b => some (a == b)
  | .calcErr a, .calcErr b => some (a == b)
  | .modifier a, .modifier b => some (a == b)
  | .unit, .unit => some true
  | _, _ => none

/-- Initial JVM heap populated with `CalculatorEngineKt$WhenMappings` enum switch arrays. -/
def calcInitJvmHeap : Jvm.JvmHeap CalcExt :=
  let h0 : Jvm.JvmHeap CalcExt := {}
  let (opArrAddr, h1) := h0.alloc (.intArray #[1, 2, 3, 4])
  let (errArrAddr, h2) := h1.alloc (.intArray #[1, 2])
  let wmCls := "com/alexvanyo/composelife/mosaiccalculator/CalculatorEngineKt$WhenMappings"
  let h3 := h2.setStatic wmCls "$EnumSwitchMapping$0" (.heapRef opArrAddr)
  h3.setStatic wmCls "$EnumSwitchMapping$1" (.heapRef errArrAddr)

/-- Initial JVM execution state preloaded with enum switch mappings and `calcInitHeap`. -/
def initCalcJvmState (slots : List (Nat × JvmVal))
    (heap : CalcHeap := {}) (jvmHeap : Jvm.JvmHeap CalcExt := calcInitJvmHeap) : JvmState :=
  Jvm.initJvmState slots (.i32 0) heap jvmHeap

/-- Allocate a closure `(fnTag, captures)` in `CalcHeap` and return `(closureId, updatedHeap)`. -/
def allocClosure (h : CalcHeap) (fnTag : String) (captures : List JvmVal) : Nat × CalcHeap :=
  let id := h.closures.size
  (id, { h with closures := h.closures.push (fnTag, captures) })

/-- Append a completed `MosaicNode` child either to the open container frame or `emittedRoot?`. -/
def emitMosaicNode (h : CalcHeap) (node : Mosaic.MosaicNode) : CalcHeap :=
  match h.nodeStack with
  | (children, handler?) :: rest =>
    { h with nodeStack := (children ++ [node], handler?) :: rest }
  | [] =>
    { h with emittedRoot? := some node }

private def assignParamLocalsAux (idx : Nat) : List Char → List JvmVal → List (Nat × JvmVal)
  | 'J' :: tags, v :: vs | 'D' :: tags, v :: vs => (idx, v) :: assignParamLocalsAux (idx + 2) tags vs
  | _ :: tags, v :: vs => (idx, v) :: assignParamLocalsAux (idx + 1) tags vs
  | _, _ => []

private def assignLinearLocals (idx : Nat) : List JvmVal → List (Nat × JvmVal)
  | [] => []
  | v :: vs => (idx, v) :: assignLinearLocals (idx + 1) vs

/-- Extract the target method identifier from a `LambdaMetafactory` bootstrap handle string. -/
def extractBsmTarget : String → Option String
  | "REF_invokeStatic com/alexvanyo/composelife/mosaiccalculator/CalculatorScreenKt.CalculatorApp$lambda$3$0:(Landroidx/compose/runtime/MutableState;Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorKey;)Lkotlin/Unit;" =>
    some "CalculatorScreenKt.CalculatorApp$lambda$3$0"
  | "REF_invokeStatic com/alexvanyo/composelife/mosaiccalculator/CalculatorScreenKt.CalculatorApp$lambda$4:(Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorState;Lcom/jakewharton/mosaic/modifier/Modifier;IILandroidx/compose/runtime/Composer;I)Lkotlin/Unit;" =>
    some "CalculatorScreenKt.CalculatorApp$lambda$4"
  | "REF_invokeStatic com/alexvanyo/composelife/mosaiccalculator/CalculatorScreenKt.CalculatorScreen$lambda$0$0:(Lkotlin/jvm/functions/Function1;Lcom/jakewharton/mosaic/layout/KeyEvent;)Z" =>
    some "CalculatorScreenKt.CalculatorScreen$lambda$0$0"
  | "REF_invokeStatic com/alexvanyo/composelife/mosaiccalculator/CalculatorScreenKt.CalculatorScreen$lambda$1:(Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorState;Lcom/jakewharton/mosaic/ui/ColumnScope;Landroidx/compose/runtime/Composer;I)Lkotlin/Unit;" =>
    some "CalculatorScreenKt.CalculatorScreen$lambda$1"
  | "REF_invokeStatic com/alexvanyo/composelife/mosaiccalculator/CalculatorScreenKt.CalculatorScreen$lambda$2:(Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorState;Lkotlin/jvm/functions/Function1;Lcom/jakewharton/mosaic/modifier/Modifier;IILandroidx/compose/runtime/Composer;I)Lkotlin/Unit;" =>
    some "CalculatorScreenKt.CalculatorScreen$lambda$2"
  | "REF_invokeStatic com/alexvanyo/composelife/mosaiccalculator/ComposableSingletons$CalculatorScreenKt.lambda_125313259$lambda$0:(Lcom/jakewharton/mosaic/ui/RowScope;Landroidx/compose/runtime/Composer;I)Lkotlin/Unit;" =>
    some "ComposableSingletons$CalculatorScreenKt.lambda_125313259$lambda$0"
  | "REF_invokeStatic com/alexvanyo/composelife/mosaiccalculator/ComposableSingletons$CalculatorScreenKt.lambda_9509460$lambda$0:(Lcom/jakewharton/mosaic/ui/RowScope;Landroidx/compose/runtime/Composer;I)Lkotlin/Unit;" =>
    some "ComposableSingletons$CalculatorScreenKt.lambda_9509460$lambda$0"
  | "REF_invokeStatic com/alexvanyo/composelife/mosaiccalculator/ComposableSingletons$CalculatorScreenKt.lambda_2033009011$lambda$0:(Lcom/jakewharton/mosaic/ui/RowScope;Landroidx/compose/runtime/Composer;I)Lkotlin/Unit;" =>
    some "ComposableSingletons$CalculatorScreenKt.lambda_2033009011$lambda$0"
  | "REF_invokeStatic com/alexvanyo/composelife/mosaiccalculator/ComposableSingletons$CalculatorScreenKt.lambda__238458734$lambda$0:(Lcom/jakewharton/mosaic/ui/RowScope;Landroidx/compose/runtime/Composer;I)Lkotlin/Unit;" =>
    some "ComposableSingletons$CalculatorScreenKt.lambda__238458734$lambda$0"
  | _ => none

private def isVoidStaticTarget : String → Bool
  | "CalculatorScreenKt.CalculatorApp" => true
  | "CalculatorScreenKt.CalculatorScreen" => true
  | "CalculatorScreenKt.CalculatorApp$lambda$2" => true
  | _ => false

private def applyCalculatorStateCtor (base? : Option Model.CalculatorState) (mask : UInt32)
    (dVal : UInt64) (pOpndV pOpV entV errV : JvmVal) : Option Model.CalculatorState :=
  let d := dVal.toInt64
  let pOpnd? : Option (Option Int64) :=
    match pOpndV with
    | .null => some none
    | .boxedLong x => some (some x.toInt64)
    | _ => none
  let pOp? : Option (Option Model.CalculatorOp) :=
    match pOpV with
    | .null => some none
    | .ext (.calcOp op) => some (some op)
    | _ => none
  let ent? : Option Bool :=
    match entV with
    | .i32 v => some (v != 0)
    | .bool b => some b
    | _ => none
  let err? : Option (Option Model.CalculatorError) :=
    match errV with
    | .null => some none
    | .ext (.calcErr e) => some (some e)
    | _ => none
  match pOpnd?, pOp?, ent?, err? with
  | some pOpnd, some pOp, some ent, some err =>
    match base? with
    | some base =>
      some {
        displayValue := if (mask &&& 1) != 0 then base.displayValue else d
        pendingOperand := if (mask &&& 2) != 0 then base.pendingOperand else pOpnd
        pendingOp := if (mask &&& 4) != 0 then base.pendingOp else pOp
        enteringNewNumber := if (mask &&& 8) != 0 then base.enteringNewNumber else ent
        error := if (mask &&& 16) != 0 then base.error else err
      }
    | none =>
      some {
        displayValue := if (mask &&& 1) != 0 then 0 else d
        pendingOperand := if (mask &&& 2) != 0 then none else pOpnd
        pendingOp := if (mask &&& 4) != 0 then none else pOp
        enteringNewNumber := if (mask &&& 8) != 0 then true else ent
        error := if (mask &&& 16) != 0 then none else err
      }
  | _, _, _, _ => none

private def resolveCalcStatic (_st : JvmState) (cls field _desc : String) : Option JvmVal :=
  match normalizeCalcClass cls, field with
  | "CalculatorError", "DivideByZero" => some (.ext (.calcErr .divideByZero))
  | "CalculatorError", "Overflow" => some (.ext (.calcErr .overflow))
  | "CalculatorOp", "Add" => some (.ext (.calcOp .add))
  | "CalculatorOp", "Sub" => some (.ext (.calcOp .sub))
  | "CalculatorOp", "Mul" => some (.ext (.calcOp .mul))
  | "CalculatorOp", "Div" => some (.ext (.calcOp .div))
  | "CalculatorKey$Clear", "INSTANCE" => some (.ext (.calcKey .clear))
  | "CalculatorKey$Equals", "INSTANCE" => some (.ext (.calcKey .equals))
  | "CalculatorKey$Backspace", "INSTANCE" => some (.ext (.calcKey .backspace))
  | "CalculatorState", "Companion" => some (.ext (.companion "CalculatorState$Companion"))
  | "CalculatorState", "$stable" => some (.i32 0)
  | "androidx/compose/runtime/Composer", "Companion" => some (.ext (.companion "Composer$Companion"))
  | "com/jakewharton/mosaic/modifier/Modifier", "Companion" => some (.ext (.modifier none))
  | "kotlin/Unit", "INSTANCE" => some (.ext .unit)
  | "ComposableSingletons$CalculatorScreenKt", "INSTANCE" =>
    some (.ext (.companion "ComposableSingletons$CalculatorScreenKt"))
  | _, _ => none

private def checkCalcInstanceOf (cls : String) (v : JvmVal) : Bool :=
  match normalizeCalcClass cls, v with
  | "CalculatorKey$Clear", .ext (.calcKey .clear) => true
  | "CalculatorKey$Equals", .ext (.calcKey .equals) => true
  | "CalculatorKey$Backspace", .ext (.calcKey .backspace) => true
  | "CalculatorKey$Digit", .ext (.calcKey (.digit _)) => true
  | "CalculatorKey$Op", .ext (.calcKey (.op _)) => true
  | "CalculatorKey", .ext (.calcKey _) => true
  | "CheckedEvalResult$Error", .ext (.evalRes (.error _)) => true
  | "CheckedEvalResult$Value", .ext (.evalRes (.value _)) => true
  | "CheckedEvalResult", .ext (.evalRes _) => true
  | "CalculatorState", .ext (.calcState _) => true
  | "java/lang/Object", .ext _ => true
  | _, _ => false

private def checkCalcCast (cls : String) (v : JvmVal) : Option JvmVal :=
  match normalizeCalcClass cls, v with
  | "CalculatorKey$Digit", .ext (.calcKey (.digit _)) => some v
  | "CalculatorKey$Op", .ext (.calcKey (.op _)) => some v
  | "CalculatorKey", .ext (.calcKey _) => some v
  | "CheckedEvalResult$Error", .ext (.evalRes (.error _)) => some v
  | "CheckedEvalResult$Value", .ext (.evalRes (.value _)) => some v
  | "CheckedEvalResult", .ext (.evalRes _) => some v
  | "CalculatorState", .ext (.calcState _) => some v
  | "com/jakewharton/mosaic/modifier/Modifier", .ext (.modifier _) => some v
  | "androidx/compose/runtime/MutableState", .ext (.stateRef _) => some v
  | "androidx/compose/runtime/State", .ext (.stateRef _) => some v
  | "kotlin/jvm/functions/Function1", .ext (.closureRef _) => some v
  | "kotlin/jvm/functions/Function2", .ext (.closureRef _) => some v
  | "kotlin/jvm/functions/Function3", .ext (.closureRef _) => some v
  | "java/lang/Object", .ext _ => some v
  | _, _ => Jvm.defaultCheckCast (fun _ _ => none) cls v

private def singletonLambdaFnTag? (method : String) : Option String :=
  match method with
  | "getLambda$125313259$ComposeLife_mosaic_calculator" =>
    some "ComposableSingletons$CalculatorScreenKt.lambda_125313259$lambda$0"
  | "getLambda$9509460$ComposeLife_mosaic_calculator" =>
    some "ComposableSingletons$CalculatorScreenKt.lambda_9509460$lambda$0"
  | "getLambda$2033009011$ComposeLife_mosaic_calculator" =>
    some "ComposableSingletons$CalculatorScreenKt.lambda_2033009011$lambda$0"
  | "getLambda$-238458734$ComposeLife_mosaic_calculator" =>
    some "ComposableSingletons$CalculatorScreenKt.lambda__238458734$lambda$0"
  | _ => none

private def stepComposerInterface (st : JvmState) (method _desc : String) :
    Option JvmState ⊕ Option JvmVal :=
  match method, st.stack with
  | "startRestartGroup", keyVal :: .ext .composer :: rest =>
    match keyVal.asI32? with
    | some k =>
      let comp' := Compose.startRestartGroup st.heap.composer k.toInt32
      .inl (some { st with pc := st.pc + 1, stack := .ext .composer :: rest, heap := { st.heap with composer := comp' } })
    | none => .inr none
  | "shouldExecute", flagsVal :: paramsVal :: .ext .composer :: rest =>
    match paramsVal.asI32?, flagsVal.asI32? with
    | some p, some f =>
      let res := Compose.shouldExecute st.heap.composer (p != 0) f.toInt32
      .inl (some { st with pc := st.pc + 1, stack := .i32 (if res then 1 else 0) :: rest })
    | _, _ => .inr none
  | "startDefaults", .ext .composer :: rest =>
    let comp' := Compose.startDefaults st.heap.composer
    .inl (some { st with pc := st.pc + 1, stack := rest, heap := { st.heap with composer := comp' } })
  | "getDefaultsInvalid", .ext .composer :: rest =>
    let b := Compose.getDefaultsInvalid st.heap.composer
    .inl (some { st with pc := st.pc + 1, stack := .i32 (if b then 1 else 0) :: rest })
  | "endDefaults", .ext .composer :: rest =>
    let comp' := Compose.endDefaults st.heap.composer
    .inl (some { st with pc := st.pc + 1, stack := rest, heap := { st.heap with composer := comp' } })
  | "skipToGroupEnd", .ext .composer :: rest =>
    let comp' := Compose.skipToGroupEnd st.heap.composer
    .inl (some { st with pc := st.pc + 1, stack := rest, heap := { st.heap with composer := comp' } })
  | "endRestartGroup", .ext .composer :: rest =>
    let (k?, comp') := Compose.endRestartGroup st.heap.composer
    let scopeVal : JvmVal := match k? with | some k => .ext (.scopeUpdateScope k) | none => .null
    .inl (some { st with pc := st.pc + 1, stack := scopeVal :: rest, heap := { st.heap with composer := comp' } })
  | "changed", v :: .ext .composer :: rest | "changedInstance", v :: .ext .composer :: rest =>
    let (changed, comp') := Compose.checkChangedSlot (Jvm.JvmVal.beqVal beqCalcExt) st.heap.composer v
    .inl (some { st with
      pc := st.pc + 1
      stack := .i32 (if changed then 1 else 0) :: rest
      heap := { st.heap with composer := comp' }
    })
  | "rememberedValue", .ext .composer :: rest =>
    let (v?, comp') := Compose.readRememberSlot st.heap.composer
    let outVal := v?.getD (.ext .composerEmpty)
    .inl (some { st with pc := st.pc + 1, stack := outVal :: rest, heap := { st.heap with composer := comp' } })
  | "updateRememberedValue", v :: .ext .composer :: rest =>
    let comp' := Compose.writeRememberSlot st.heap.composer v
    .inl (some { st with pc := st.pc + 1, stack := rest, heap := { st.heap with composer := comp' } })
  | _, _ => .inr none

/-- Hook builder parameterized by bytecode lookup (`resolveProg`) and bounded recursion depth/fuel. -/
def mkCalcHooks (resolveProg : String → Option (List JvmInstr)) (depth fuel : Nat) :
    Jvm.JvmHooks CalcExt CalcHeap :=
  match depth with
  | 0 => {
      beqExt := beqCalcExt
      beqRefExt := beqRefCalcExt
      checkInstanceOf := checkCalcInstanceOf
      checkCast := checkCalcCast
      resolveStatic := resolveCalcStatic
    }
  | d + 1 =>
    let invokeClosure : JvmState → Nat → List JvmVal → Option (JvmVal × JvmState) :=
      fun st cid args =>
        match st.heap.closures[cid]? with
        | some (fnTag, captures) =>
          match resolveProg fnTag with
          | some prog =>
            let hooks := mkCalcHooks resolveProg d fuel
            let subSt : JvmState := {
              pc := 0
              stack := []
              locals := (assignLinearLocals 0 (captures ++ args)).foldl
                (fun loc (i, v) => setLocal loc i v) (fun _ => .i32 0)
              jvmHeap := st.jvmHeap
              heap := st.heap
            }
            match Jvm.runJvmRes hooks fuel prog subSt with
            | some (res, endSt) => some (res, { st with jvmHeap := endSt.jvmHeap, heap := endSt.heap })
            | none => none
          | none => none
        | none => none
    let invokeProg : JvmState → String → String → List JvmVal → Option (JvmVal × JvmState) :=
      fun st fnTag desc args =>
        match resolveProg fnTag with
        | some prog =>
          let hooks := mkCalcHooks resolveProg d fuel
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
      beqExt := beqCalcExt
      beqRefExt := beqRefCalcExt
      checkInstanceOf := checkCalcInstanceOf
      checkCast := checkCalcCast
      resolveStatic := resolveCalcStatic
      stepInvokeSpecial := fun st cls method desc =>
        match normalizeCalcClass cls, method, desc, st.stack with
        | "CheckedEvalResult$Error", "<init>", _, .ext (.calcErr e) :: .allocRef _ :: .allocRef _ :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := .ext (.evalRes (.error e)) :: rest })
        | "CheckedEvalResult$Value", "<init>", "(J)V", v :: .allocRef _ :: .allocRef _ :: rest =>
          match v.asI64? with
          | some n => .inl (some { st with pc := st.pc + 1, stack := .ext (.evalRes (.value n.toInt64)) :: rest })
          | none => .inr none
        | "CalculatorKey$Digit", "<init>", "(I)V", v :: .allocRef _ :: .allocRef _ :: rest =>
          match v.asI32? with
          | some n => .inl (some { st with pc := st.pc + 1, stack := .ext (.calcKey (.digit n)) :: rest })
          | none => .inr none
        | "CalculatorKey$Op", "<init>", _, .ext (.calcOp op) :: .allocRef _ :: .allocRef _ :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := .ext (.calcKey (.op op)) :: rest })
        | "CalculatorState", "<init>",
            "(JLjava/lang/Long;Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorOp;ZLcom/alexvanyo/composelife/mosaiccalculator/CalculatorError;ILkotlin/jvm/internal/DefaultConstructorMarker;)V",
            _marker :: maskVal :: errV :: entV :: pOpV :: pOpndV :: dVal :: .allocRef _ :: .allocRef _ :: rest =>
          match dVal.asI64?, maskVal.asI32? with
          | some dv, some mask =>
            match applyCalculatorStateCtor none mask dv pOpndV pOpV entV errV with
            | some cSt => .inl (some { st with pc := st.pc + 1, stack := .ext (.calcState cSt) :: rest })
            | none => .inr none
          | _, _ => .inr none
        | "ComposableSingletons$CalculatorScreenKt", "<init>", "()V", .allocRef _ :: .allocRef _ :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := .ext (.companion "ComposableSingletons$CalculatorScreenKt") :: rest })
        | "java/lang/Object", "<init>", "()V", .allocRef _ :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := rest })
        | _, _, _, _ => .inr none
      stepInvokeVirtual := fun st cls method desc =>
        match normalizeCalcClass cls, method, desc, st.stack with
        | "java/lang/String", "hashCode", "()I", .str s :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := .i32 (javaStringHashCode s) :: rest })
        | "java/lang/String", "equals", "(Ljava/lang/Object;)Z", arg :: .str s :: rest =>
          let eq := match arg with | .str s2 => s == s2 | _ => false
          .inl (some { st with pc := st.pc + 1, stack := .i32 (if eq then 1 else 0) :: rest })
        | "CalculatorOp", "ordinal", "()I", .ext (.calcOp op) :: rest =>
          let ord : UInt32 := match op with | .add => 0 | .sub => 1 | .mul => 2 | .div => 3
          .inl (some { st with pc := st.pc + 1, stack := .i32 ord :: rest })
        | "CalculatorOp", "getSymbol", "()Ljava/lang/String;", .ext (.calcOp op) :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := .str op.symbol :: rest })
        | "CalculatorError", "ordinal", "()I", .ext (.calcErr err) :: rest =>
          let ord : UInt32 := match err with | .divideByZero => 0 | .overflow => 1
          .inl (some { st with pc := st.pc + 1, stack := .i32 ord :: rest })
        | "CalculatorKey$Digit", "getDigit", "()I", .ext (.calcKey (.digit d)) :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := .i32 d :: rest })
        | "CalculatorKey$Op", "getOp", _, .ext (.calcKey (.op op)) :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := .ext (.calcOp op) :: rest })
        | "CheckedEvalResult$Error", "getError", _, .ext (.evalRes (.error e)) :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := .ext (.calcErr e) :: rest })
        | "CheckedEvalResult$Value", "getValue", "()J", .ext (.evalRes (.value v)) :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := .i64 v.toUInt64 :: rest })
        | "CalculatorState", "getDisplayValue", "()J", .ext (.calcState cSt) :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := .i64 cSt.displayValue.toUInt64 :: rest })
        | "CalculatorState", "getPendingOperand", "()Ljava/lang/Long;", .ext (.calcState cSt) :: rest =>
          let ov : JvmVal := match cSt.pendingOperand with | some x => .boxedLong x.toUInt64 | none => .null
          .inl (some { st with pc := st.pc + 1, stack := ov :: rest })
        | "CalculatorState", "getPendingOp", _, .ext (.calcState cSt) :: rest =>
          let ov : JvmVal := match cSt.pendingOp with | some o => .ext (.calcOp o) | none => .null
          .inl (some { st with pc := st.pc + 1, stack := ov :: rest })
        | "CalculatorState", "getEnteringNewNumber", "()Z", .ext (.calcState cSt) :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := .i32 (if cSt.enteringNewNumber then 1 else 0) :: rest })
        | "CalculatorState", "getError", _, .ext (.calcState cSt) :: rest =>
          let ov : JvmVal := match cSt.error with | some e => .ext (.calcErr e) | none => .null
          .inl (some { st with pc := st.pc + 1, stack := ov :: rest })
        | "CalculatorState$Companion", "getInitial", _, .ext (.companion "CalculatorState$Companion") :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := .ext (.calcState Model.CalculatorState.initial) :: rest })
        | "androidx/compose/runtime/Composer$Companion", "getEmpty", _, .ext (.companion "Composer$Companion") :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := .ext .composerEmpty :: rest })
        | "com/jakewharton/mosaic/layout/KeyEvent", "getKey", "()Ljava/lang/String;", .ext (.keyEvent k) :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := .str k :: rest })
        | "ComposableSingletons$CalculatorScreenKt", _, "()Lkotlin/jvm/functions/Function3;",
            .ext (.companion "ComposableSingletons$CalculatorScreenKt") :: rest =>
          let fnTag := "ComposableSingletons$CalculatorScreenKt." ++ method
          match invokeProg st fnTag "()Lkotlin/jvm/functions/Function3;" [] with
          | some (res, st') => .inl (some { st' with pc := st.pc + 1, stack := res :: rest })
          | none =>
            match singletonLambdaFnTag? method with
            | some targetTag =>
              let (cid, heap') := allocClosure st.heap targetTag []
              .inl (some { st with pc := st.pc + 1, stack := .ext (.closureRef cid) :: rest, heap := heap' })
            | none => .inr none
        | _, _, _, _ => .inr none
      stepInvokeStatic := fun st cls method desc =>
        match normalizeCalcClass cls, method, desc, st.stack with
        | "java/lang/Long", "valueOf", "(J)Ljava/lang/Long;", v :: rest =>
          match v.asI64? with
          | some x => .inl (some { st with pc := st.pc + 1, stack := .boxedLong x :: rest })
          | none => .inr none
        | "java/lang/String", "valueOf", "(J)Ljava/lang/String;", v :: rest =>
          match v.asI64? with
          | some x => .inl (some { st with pc := st.pc + 1, stack := .str (Jvm.i64ToDecimalString x) :: rest })
          | none => .inr none
        | "CalculatorState", "copy$default", _,
            _marker :: maskVal :: errV :: entV :: pOpV :: pOpndV :: dVal :: .ext (.calcState base) :: rest =>
          match dVal.asI64?, maskVal.asI32? with
          | some dv, some mask =>
            match applyCalculatorStateCtor (some base) mask dv pOpndV pOpV entV errV with
            | some cSt => .inl (some { st with pc := st.pc + 1, stack := .ext (.calcState cSt) :: rest })
            | none => .inr none
          | _, _ => .inr none
        | "androidx/compose/runtime/ComposerKt", "sourceInformation", _, _info :: .ext .composer :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := rest })
        | "androidx/compose/runtime/ComposerKt", "sourceInformationMarkerStart", _,
            _info :: _key :: .ext .composer :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := rest })
        | "androidx/compose/runtime/ComposerKt", "sourceInformationMarkerEnd", _, .ext .composer :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := rest })
        | "androidx/compose/runtime/ComposerKt", "isTraceInProgress", "()Z", rest =>
          let v : UInt32 := if st.heap.composer.traceEnabled then 1 else 0
          .inl (some { st with pc := st.pc + 1, stack := .i32 v :: rest })
        | "androidx/compose/runtime/ComposerKt", "traceEventStart", _, _s :: _d :: _c :: _k :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := rest })
        | "androidx/compose/runtime/ComposerKt", "traceEventEnd", "()V", rest =>
          .inl (some { st with pc := st.pc + 1, stack := rest })
        | "androidx/compose/runtime/RecomposeScopeImplKt", "updateChangedFlags", "(I)I", v :: rest =>
          match v.asI32? with
          | some f => .inl (some { st with pc := st.pc + 1, stack := .i32 (Compose.updateChangedFlags f) :: rest })
          | none => .inr none
        | "androidx/compose/runtime/SnapshotStateKt", "mutableStateOf$default", _,
            _marker :: _mask :: _policy :: initial :: rest =>
          let (sid, comp') := Compose.allocMutableState st.heap.composer initial
          .inl (some { st with
            pc := st.pc + 1
            stack := .ext (.stateRef sid) :: rest
            heap := { st.heap with composer := comp' }
          })
        | "androidx/compose/runtime/internal/ComposableLambdaKt", "composableLambdaInstance", _,
            block :: _tracked :: _key :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := block :: rest })
        | "androidx/compose/runtime/internal/ComposableLambdaKt", "rememberComposableLambda", _,
            _changed :: .ext .composer :: block :: _tracked :: _key :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := block :: rest })
        | "com/jakewharton/mosaic/layout/KeyModifierKt", "onKeyEvent", _,
            .ext (.closureRef cid) :: .ext (.modifier _) :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := .ext (.modifier (some cid)) :: rest })
        | "com/jakewharton/mosaic/ui/Text", "Text-cbmis8g", _,
            _dflt :: _ch :: .ext .composer :: _a6 :: _a5 :: _a4 :: _a3 :: _a2 :: _mod :: .str text :: rest =>
          let heap' := emitMosaicNode st.heap (.text text)
          .inl (some { st with pc := st.pc + 1, stack := rest, heap := heap' })
        | "com/jakewharton/mosaic/ui/Row", "Row", _,
            _dflt :: _ch :: .ext .composer :: .ext (.closureRef cid) :: _align :: _arr :: modV :: rest =>
          let handler? := match modV with | .ext (.modifier h?) => h? | _ => none
          let stOpen : JvmState := { st with heap := { st.heap with nodeStack := ([], handler?) :: st.heap.nodeStack } }
          match invokeClosure stOpen cid [.ext .unit, .ext .composer, .i32 6] with
          | some (_res, stBody) =>
            match stBody.heap.nodeStack with
            | (children, h?) :: parentFrames =>
              let stPopped := { stBody with heap := { stBody.heap with nodeStack := parentFrames } }
              let heapFinal := emitMosaicNode stPopped.heap (.row children h?)
              .inl (some { stPopped with pc := st.pc + 1, stack := rest, heap := heapFinal })
            | [] => .inr none
          | none => .inr none
        | "com/jakewharton/mosaic/ui/Column", "Column", _,
            _dflt :: _ch :: .ext .composer :: .ext (.closureRef cid) :: _align :: _arr :: modV :: rest =>
          let handler? := match modV with | .ext (.modifier h?) => h? | _ => none
          let stOpen : JvmState := { st with heap := { st.heap with nodeStack := ([], handler?) :: st.heap.nodeStack } }
          match invokeClosure stOpen cid [.ext .unit, .ext .composer, .i32 6] with
          | some (_res, stBody) =>
            match stBody.heap.nodeStack with
            | (children, h?) :: parentFrames =>
              let stPopped := { stBody with heap := { stBody.heap with nodeStack := parentFrames } }
              let heapFinal := emitMosaicNode stPopped.heap (.column children h?)
              .inl (some { stPopped with pc := st.pc + 1, stack := rest, heap := heapFinal })
            | [] => .inr none
          | none => .inr none
        | nCls, _, _, stackNow =>
          let nArgs := (Jvm.parseMethodParamTags desc).length
          if stackNow.length < nArgs then .inr none
          else
            let popped := stackNow.take nArgs
            let rest := stackNow.drop nArgs
            let fnTag := nCls ++ "." ++ method
            match invokeProg st fnTag desc popped.reverse with
            | some (res, st') =>
              let retStack := if isVoidStaticTarget fnTag then rest else res :: rest
              .inl (some { st' with pc := st.pc + 1, stack := retStack })
            | none => .inr none
      stepInvokeInterface := fun st cls method desc =>
        match stepComposerInterface st method desc with
        | .inl (some st') => .inl (some st')
        | .inl none => .inr none
        | .inr (some res) => .inr (some res)
        | .inr none =>
          match cls, method, st.stack with
          | "androidx/compose/runtime/State", "getValue", .ext (.stateRef sid) :: rest
          | "androidx/compose/runtime/MutableState", "getValue", .ext (.stateRef sid) :: rest =>
            match Compose.readMutableState st.heap.composer sid with
            | some (v, comp') =>
              .inl (some { st with pc := st.pc + 1, stack := v :: rest, heap := { st.heap with composer := comp' } })
            | none => .inr none
          | "androidx/compose/runtime/MutableState", "setValue", newVal :: .ext (.stateRef sid) :: rest =>
            match Compose.writeMutableState (Jvm.JvmVal.beqVal beqCalcExt) st.heap.composer sid newVal with
            | some comp' =>
              .inl (some { st with pc := st.pc + 1, stack := rest, heap := { st.heap with composer := comp' } })
            | none => .inr none
          | "androidx/compose/runtime/ScopeUpdateScope", "updateScope",
              closureVal :: .ext (.scopeUpdateScope gk) :: rest =>
            let comp' := Compose.setGroupRestartClosure st.heap.composer gk closureVal
            .inl (some { st with pc := st.pc + 1, stack := rest, heap := { st.heap with composer := comp' } })
          | "kotlin/jvm/functions/Function1", "invoke", a0 :: .ext (.closureRef cid) :: rest =>
            match invokeClosure st cid [a0] with
            | some (res, st') => .inl (some { st' with pc := st.pc + 1, stack := res :: rest })
            | none => .inr none
          | "kotlin/jvm/functions/Function2", "invoke", a1 :: a0 :: .ext (.closureRef cid) :: rest =>
            match invokeClosure st cid [a0, a1] with
            | some (res, st') => .inl (some { st' with pc := st.pc + 1, stack := res :: rest })
            | none => .inr none
          | "kotlin/jvm/functions/Function3", "invoke", a2 :: a1 :: a0 :: .ext (.closureRef cid) :: rest =>
            match invokeClosure st cid [a0, a1, a2] with
            | some (res, st') => .inl (some { st' with pc := st.pc + 1, stack := res :: rest })
            | none => .inr none
          | _, _, _ => .inr none
      stepInvokeDynamic := fun st bsmKind bsmArg desc =>
        if bsmKind == "LambdaMetafactory" then
          let nCaps := (Jvm.parseMethodParamTags desc).length
          if st.stack.length < nCaps then .inr none
          else
            match extractBsmTarget bsmArg with
            | some fnTag =>
              let caps := (st.stack.take nCaps).reverse
              let rest := st.stack.drop nCaps
              let (cid, heap') := allocClosure st.heap fnTag caps
              .inl (some { st with pc := st.pc + 1, stack := .ext (.closureRef cid) :: rest, heap := heap' })
            | none => .inr none
        else .inr none
    }

/-- Default fuel-bounded hooks for leaf arithmetic methods without nested bytecode calls. -/
def calcHooks : Jvm.JvmHooks CalcExt CalcHeap :=
  mkCalcHooks (fun _ => none) 4 64

abbrev runJvm (fuel : Nat) (prog : List JvmInstr) (st : JvmState) : Option JvmVal :=
  Jvm.runJvm calcHooks fuel prog st

abbrev runJvmRes (fuel : Nat) (prog : List JvmInstr) (st : JvmState) : Option (JvmVal × JvmState) :=
  Jvm.runJvmRes calcHooks fuel prog st

/-- Dispatch a terminal key string into the `onKeyEvent` handler attached to `heap.emittedRoot?`. -/
def dispatchKeyEventJvm (resolveProg : String → Option (List JvmInstr)) (depth fuel : Nat)
    (keyStr : String) (st : JvmState) : Option (Bool × JvmState) :=
  match st.heap.emittedRoot?.bind Mosaic.findKeyHandler? with
  | some cid =>
    match st.heap.closures[cid]? with
    | some (fnTag, captures) =>
      match resolveProg fnTag with
      | some prog =>
        let hooks := mkCalcHooks resolveProg depth fuel
        let subSt : JvmState := {
          pc := 0
          stack := []
          locals := (assignLinearLocals 0 (captures ++ [.ext (.keyEvent keyStr)])).foldl
            (fun loc (i, v) => setLocal loc i v) (fun _ => .i32 0)
          jvmHeap := st.jvmHeap
          heap := st.heap
        }
        match Jvm.runJvmRes hooks fuel prog subSt with
        | some (res, endSt) =>
          let handled := match res.asI32? with | some v => v != 0 | none => false
          some (handled, { st with jvmHeap := endSt.jvmHeap, heap := endSt.heap })
        | none => none
      | none => none
    | none => none
  | none => none

/-- Recompose the root group registered on `heap.composer` via its stored `ScopeUpdateScope` closure. -/
def recomposeAppJvm (resolveProg : String → Option (List JvmInstr)) (depth fuel : Nat)
    (st : JvmState) : Option JvmState :=
  let compRecomp := Compose.beginRecompose st.heap.composer
  match Compose.rootRestartClosure? compRecomp with
  | some (.ext (.closureRef cid)) =>
    match st.heap.closures[cid]? with
    | some (fnTag, captures) =>
      match resolveProg fnTag with
      | some prog =>
        let hooks := mkCalcHooks resolveProg depth fuel
        let subSt : JvmState := {
          pc := 0
          stack := []
          locals := (assignLinearLocals 0 (captures ++ [.ext .composer, .i32 0])).foldl
            (fun loc (i, v) => setLocal loc i v) (fun _ => .i32 0)
          jvmHeap := st.jvmHeap
          heap := { st.heap with composer := compRecomp, nodeStack := [] }
        }
        match Jvm.runJvmRes hooks fuel prog subSt with
        | some (_, endSt) => some { st with jvmHeap := endSt.jvmHeap, heap := endSt.heap }
        | none => none
      | none => none
    | none => none
  | _ => none

end MosaicCalculator.JvmVerification
