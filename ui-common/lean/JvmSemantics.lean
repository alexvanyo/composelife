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
import models.TargetStateModel
import models.EasingPiecewiseModel

namespace UiCommon.JvmVerification

export Jvm (JvmInstr setLocal)

/-- Easing function values stored in JVM registers/lists without nested `JvmVal` recursion. -/
inductive UiEasing where
  | const (id : Nat)
  | piecewise (closureId : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Domain-specific JVM extension values for `:ui-common` (`TargetState` + `EasingPiecewise`). -/
inductive UiExt where
  | boxedFloat (v : Float32)
  | notLambda
  | fn1Ref (id : Nat)
  | easing (e : UiEasing)
  | sortedByComparator
  | mapRef (id : Nat)
  | floatList (xs : List Float32)
  | easingList (xs : List UiEasing)
  | pairList (xs : List (Float32 × UiEasing))
  | companion (cls : String)
  deriving Inhabited

abbrev JvmVal := Jvm.JvmVal UiExt

/-- Domain heap holding `Function1` implementations, primitive `Easing` transforms, maps, and closures. -/
structure UiHeap where
  fn1s : Array (JvmVal → Option JvmVal) := #[]
  easings : Array (Float32 → Float32) := #[]
  maps : Array (List (Float32 × UiEasing)) := #[]
  closures : Array (String × List JvmVal) := #[]
  deriving Inhabited

abbrev JvmState := Jvm.JvmState UiExt UiHeap

/-- Map package-qualified `:ui-common` internal names to the short names the hooks dispatch on. -/
def normalizeUiCommonClass : String → String
  | "com/alexvanyo/composelife/ui/util/TargetState" => "TargetState"
  | "com/alexvanyo/composelife/ui/util/TargetState$Single" => "TargetState$Single"
  | "com/alexvanyo/composelife/ui/util/TargetState$InProgress" => "TargetState$InProgress"
  | "com/alexvanyo/composelife/ui/util/TargetState$InProgress$Companion" => "TargetState$InProgress$Companion"
  | "com/alexvanyo/composelife/ui/util/TargetStateKt" => "TargetStateKt"
  | "com/alexvanyo/composelife/ui/util/TargetStateKt$not$1" => "TargetStateKt$not$1"
  | "com/alexvanyo/composelife/ui/util/EasingPiecewiseKt" => "EasingPiecewiseKt"
  | "com/alexvanyo/composelife/ui/util/EasingPiecewiseKt$Easing$$inlined$sortedBy$1" =>
    "EasingPiecewiseKt$Easing$$inlined$sortedBy$1"
  | cls => cls

/-- Subtype relation for `:ui-common` classes and short/long internal class names. -/
def isUiCommonSubtypeOf (subCls supCls : String) : Bool :=
  let nSub := normalizeUiCommonClass subCls
  let nSup := normalizeUiCommonClass supCls
  subCls == supCls || nSub == nSup || supCls == "java/lang/Object" ||
    ((nSub == "TargetState$Single" || nSub == "TargetState$InProgress") && nSup == "TargetState") ||
    Jvm.defaultIsSubtypeOf subCls supCls

/-- Structural equality on `UiExt` matching JVM `Object.equals` for boxed floats and pair lists. -/
def beqUiExt : UiExt → UiExt → Bool
  | .boxedFloat a, .boxedFloat b => Model.floatKeyEq a b
  | .notLambda, .notLambda => true
  | .fn1Ref a, .fn1Ref b => a == b
  | .easing a, .easing b => a == b
  | .sortedByComparator, .sortedByComparator => true
  | .mapRef a, .mapRef b => a == b
  | .floatList xs, .floatList ys =>
    xs.length == ys.length && (xs.zip ys).all (fun (a, b) => Model.floatKeyEq a b)
  | .easingList xs, .easingList ys => xs == ys
  | .pairList xs, .pairList ys =>
    xs.length == ys.length &&
      (xs.zip ys).all (fun ((k1, e1), (k2, e2)) => Model.floatKeyEq k1 k2 && e1 == e2)
  | .companion a, .companion b => a == b
  | _, _ => false

/-- Reference identity on `UiExt` for `if_acmpeq` / `if_acmpne`. -/
def beqRefUiExt : UiExt → UiExt → Option Bool
  | .notLambda, .notLambda => some true
  | .sortedByComparator, .sortedByComparator => some true
  | .fn1Ref a, .fn1Ref b => some (a == b)
  | .mapRef a, .mapRef b => some (a == b)
  | .companion a, .companion b => some (a == b)
  | _, _ => none

/-- Exact `java.lang.Float.floatToIntBits` / `Float.hashCode(float)` model. -/
def floatHashCode (v : Float32) : UInt32 :=
  if v.isNaN then 0x7fc00000 else v.toBits

/-- Minimal JVM `Object.hashCode` model for `TargetState$InProgress.hashCode` fields. -/
def jvmValHashCode : JvmVal → Option UInt32
  | .boxedBool b => some (if b then 1231 else 1237)
  | .boxedInt n => some n
  | .boxedLong n => some (n.toUInt32 ^^^ (n >>> 32).toUInt32)
  | .ext (.boxedFloat v) => some (floatHashCode v)
  | .str s => some (s.toList.foldl (fun h c => h * 31 + UInt32.ofNat c.toNat) 0)
  | _ => none

/-- Initial JVM state for `:ui-common` bytecode verification. -/
def initUiJvmState (slots : List (Nat × JvmVal))
    (heap : UiHeap := {}) (jvmHeap : Jvm.JvmHeap UiExt := {}) : JvmState :=
  Jvm.initJvmState slots (.i32 0) heap jvmHeap

/-- Stable insertion sort on `(Float32 × UiEasing)` pairs by `Model.floatCompare`, matching `ArraysKt.sortedWith`:
`x` precedes every element of the sorted tail whose key is not smaller, so equal keys keep their order. -/
def insertPairSorted (x : Float32 × UiEasing) : List (Float32 × UiEasing) → List (Float32 × UiEasing)
  | [] => [x]
  | y :: ys =>
    if Model.floatCompare x.1 y.1 ≤ 0 then x :: y :: ys
    else y :: insertPairSorted x ys

def sortPairsByKeyframe : List (Float32 × UiEasing) → List (Float32 × UiEasing)
  | [] => []
  | x :: xs => insertPairSorted x (sortPairsByKeyframe xs)

def decodePairElem : JvmVal → Option (Float32 × UiEasing)
  | .pair (.ext (.boxedFloat k)) (.ext (.easing e)) => some (k, e)
  | _ => none

def decodePairArray (elems : Array JvmVal) : Option (List (Float32 × UiEasing)) :=
  elems.toList.mapM decodePairElem

def assignParamLocalsAux (idx : Nat) : List Char → List JvmVal → List (Nat × JvmVal)
  | 'J' :: tags, v :: vs | 'D' :: tags, v :: vs => (idx, v) :: assignParamLocalsAux (idx + 2) tags vs
  | _ :: tags, v :: vs => (idx, v) :: assignParamLocalsAux (idx + 1) tags vs
  | _, _ => []

def assignLinearLocals (idx : Nat) : List JvmVal → List (Nat × JvmVal)
  | [] => []
  | v :: vs => (idx, v) :: assignLinearLocals (idx + 1) vs

def extractBsmTarget : String → Option String
  | "REF_invokeStatic com/alexvanyo/composelife/ui/util/EasingPiecewiseKt.Easing$lambda$3:(Ljava/util/List;Ljava/util/List;F)F" =>
    some "EasingPiecewiseKt.Easing$lambda$3"
  | _ => none

def isVoidTarget : String → Bool
  | "TargetState$InProgress.<init>" => true
  | _ => false

def resolveUiStatic (_st : JvmState) (cls field _desc : String) : Option JvmVal :=
  match normalizeUiCommonClass cls, field with
  | "TargetStateKt$not$1", "INSTANCE" => some (.ext .notLambda)
  | _, _ => none

def checkUiInstanceOf (cls : String) (v : JvmVal) : Bool :=
  match normalizeUiCommonClass cls, v with
  | "java/lang/Float", .ext (.boxedFloat _) => true
  | "java/lang/Number", .ext (.boxedFloat _) => true
  | "java/lang/Comparable", .ext (.boxedFloat _) => true
  | "java/lang/Object", .ext _ => true
  | "kotlin/jvm/functions/Function1", .ext .notLambda => true
  | "kotlin/jvm/functions/Function1", .ext (.fn1Ref _) => true
  | "androidx/compose/animation/core/Easing", .ext (.easing _) => true
  | "java/util/Comparator", .ext .sortedByComparator => true
  | "java/util/Map", .ext (.mapRef _) => true
  | "java/util/List", .ext (.floatList _) => true
  | "java/util/List", .ext (.easingList _) => true
  | "java/util/List", .ext (.pairList _) => true
  | "java/util/Set", .ext (.floatList _) => true
  | "java/util/Collection", .ext (.easingList _) => true
  | "java/lang/Iterable", .ext (.floatList _) => true
  | "java/lang/Iterable", .ext (.easingList _) => true
  | "java/lang/Iterable", .ext (.pairList _) => true
  | _, _ => Jvm.defaultCheckInstanceOf (fun _ _ => false) cls v

def checkUiCast (cls : String) (v : JvmVal) : Option JvmVal :=
  match normalizeUiCommonClass cls, v with
  | "java/lang/Float", .ext (.boxedFloat _) => some v
  | "java/lang/Number", .ext (.boxedFloat _) => some v
  | "java/lang/Comparable", .ext (.boxedFloat _) => some v
  | "kotlin/jvm/functions/Function1", .ext .notLambda => some v
  | "kotlin/jvm/functions/Function1", .ext (.fn1Ref _) => some v
  | "androidx/compose/animation/core/Easing", .ext (.easing _) => some v
  | "java/util/Comparator", .ext .sortedByComparator => some v
  | "java/util/Map", .ext (.mapRef _) => some v
  | "java/util/List", .ext (.floatList _) => some v
  | "java/util/List", .ext (.easingList _) => some v
  | "java/util/List", .ext (.pairList _) => some v
  | "java/util/Set", .ext (.floatList _) => some v
  | "java/util/Collection", .ext (.easingList _) => some v
  | "java/lang/Iterable", .ext (.floatList _) => some v
  | "java/lang/Iterable", .ext (.easingList _) => some v
  | "java/lang/Iterable", .ext (.pairList _) => some v
  | "java/lang/Object", .ext _ => some v
  | _, _ => Jvm.defaultCheckCast (fun _ _ => none) cls v

/-- Hook builder parameterized by bytecode lookup (`resolveProg`) and bounded recursion depth/fuel. -/
def mkUiCommonHooks (resolveProg : String → Option (List JvmInstr)) (depth fuel : Nat) :
    Jvm.JvmHooks UiExt UiHeap :=
  let stepNew : JvmState → String → Option JvmState ⊕ Option JvmVal :=
    fun st cls =>
      match normalizeUiCommonClass cls with
      | "TargetState$Single" | "TargetState$InProgress" =>
        let (addr, jh') := st.jvmHeap.alloc (.instance cls [])
        .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: st.stack, jvmHeap := jh' })
      | _ => .inl (some { st with pc := st.pc + 1, stack := .allocRef cls :: st.stack })
  let invokeProg : JvmState → String → String → List JvmVal → Option (JvmVal × JvmState) :=
    fun st fnTag desc args =>
      match depth with
      | 0 => none
      | d + 1 =>
        match resolveProg fnTag with
        | some prog =>
          let hooks := mkUiCommonHooks resolveProg d fuel
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
  let invokeClosure : JvmState → Nat → List JvmVal → Option (JvmVal × JvmState) :=
    fun st cid args =>
      match depth with
      | 0 => none
      | d + 1 =>
        match st.heap.closures[cid]? with
        | some (fnTag, captures) =>
          match resolveProg fnTag with
          | some prog =>
            let hooks := mkUiCommonHooks resolveProg d fuel
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
  let invokeStaticProg : JvmState → String → String → String → Option JvmState ⊕ Option JvmVal :=
    fun st nCls method desc =>
      let nArgs := (Jvm.parseMethodParamTags desc).length
      if st.stack.length < nArgs then .inr none
      else
        let popped := st.stack.take nArgs
        let rest := st.stack.drop nArgs
        let fnTag := nCls ++ "." ++ method
        match invokeProg st fnTag desc popped.reverse with
        | some (res, st') =>
          let retStack := if isVoidTarget fnTag then rest else res :: rest
          .inl (some { st' with pc := st.pc + 1, stack := retStack })
        | none => .inr none
  {
      beqExt := beqUiExt
      beqRefExt := beqRefUiExt
      isSubtypeOf := isUiCommonSubtypeOf
      stepNewClass := stepNew
      checkInstanceOf := checkUiInstanceOf
      checkCast := checkUiCast
      resolveStatic := resolveUiStatic
      stepInvokeSpecial := fun st cls method desc =>
        match normalizeUiCommonClass cls, method, desc, st.stack with
        | "java/lang/Object", "<init>", "()V", .heapRef _ :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := rest })
        | "java/lang/Object", "<init>", "()V", .allocRef _ :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := rest })
        | "TargetState$Single", "<init>", "(Ljava/lang/Object;)V", arg :: .heapRef addr :: rest =>
          match st.jvmHeap.get? addr with
          | some (.instance objCls fields) =>
            if isUiCommonSubtypeOf objCls "TargetState$Single" then
              let fields' := ("current", arg) :: fields.filter (fun (f, _) => f != "current")
              let jh' := st.jvmHeap.set addr (.instance objCls fields')
              .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := jh' })
            else .inr none
          | _ => .inr none
        | "TargetState$InProgress", "<init>", "(Ljava/lang/Object;Ljava/lang/Object;FLjava/lang/Object;)V",
            m :: pr :: p :: c :: .heapRef addr :: rest =>
          let fnTag := "TargetState$InProgress.<init>"
          match invokeProg st fnTag "(Ljava/lang/Object;Ljava/lang/Object;Ljava/lang/Object;FLjava/lang/Object;)V"
              [.heapRef addr, c, p, pr, m] with
          | some (_, st') => .inl (some { st' with pc := st.pc + 1, stack := rest })
          | none => .inr none
        | "TargetState$InProgress$Companion", "<init>", "(Lkotlin/jvm/internal/DefaultConstructorMarker;)V",
            _marker :: .allocRef _ :: .allocRef _ :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := .ext (.companion "TargetState$InProgress$Companion") :: rest })
        | "EasingPiecewiseKt$Easing$$inlined$sortedBy$1", "<init>", "()V",
            .allocRef _ :: .allocRef _ :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := .ext .sortedByComparator :: rest })
        | _, _, _, _ => .inr none
      stepInvokeVirtual := fun st cls method desc =>
        match normalizeUiCommonClass cls, method, desc, st.stack with
        | "TargetState$Single", "getCurrent", "()Ljava/lang/Object;", .heapRef addr :: rest =>
          match st.jvmHeap.get? addr >>= fun obj => obj.getField? isUiCommonSubtypeOf "TargetState$Single" "current" with
          | some v => .inl (some { st with pc := st.pc + 1, stack := v :: rest })
          | none => .inr none
        | "TargetState$InProgress", "getCurrent", "()Ljava/lang/Object;", .heapRef addr :: rest =>
          match invokeProg st "TargetState$InProgress.getCurrent" "(Ljava/lang/Object;)Ljava/lang/Object;" [.heapRef addr] with
          | some (res, st') => .inl (some { st' with pc := st.pc + 1, stack := res :: rest })
          | none => .inr none
        | "TargetState$InProgress", "getProvisional", "()Ljava/lang/Object;", .heapRef addr :: rest =>
          match invokeProg st "TargetState$InProgress.getProvisional" "(Ljava/lang/Object;)Ljava/lang/Object;" [.heapRef addr] with
          | some (res, st') => .inl (some { st' with pc := st.pc + 1, stack := res :: rest })
          | none => .inr none
        | "TargetState$InProgress", "getProgress", "()F", .heapRef addr :: rest =>
          match invokeProg st "TargetState$InProgress.getProgress" "(Ljava/lang/Object;)F" [.heapRef addr] with
          | some (res, st') => .inl (some { st' with pc := st.pc + 1, stack := res :: rest })
          | none => .inr none
        | "TargetState$InProgress", "getMetadata", "()Ljava/lang/Object;", .heapRef addr :: rest =>
          match invokeProg st "TargetState$InProgress.getMetadata" "(Ljava/lang/Object;)Ljava/lang/Object;" [.heapRef addr] with
          | some (res, st') => .inl (some { st' with pc := st.pc + 1, stack := res :: rest })
          | none => .inr none
        | "TargetState$InProgress", "copy", "(Ljava/lang/Object;Ljava/lang/Object;FLjava/lang/Object;)Lcom/alexvanyo/composelife/ui/util/TargetState$InProgress;",
            m :: pr :: p :: c :: .heapRef addr :: rest =>
          match invokeProg st "TargetState$InProgress.copy"
              "(Ljava/lang/Object;Ljava/lang/Object;Ljava/lang/Object;FLjava/lang/Object;)Ljava/lang/Object;"
              [.heapRef addr, c, p, pr, m] with
          | some (res, st') => .inl (some { st' with pc := st.pc + 1, stack := res :: rest })
          | none => .inr none
        | "java/lang/Number", "floatValue", "()F", .ext (.boxedFloat v) :: rest
        | "java/lang/Float", "floatValue", "()F", .ext (.boxedFloat v) :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := .f32 v :: rest })
        | "java/lang/Object", "hashCode", "()I", v :: rest =>
          match jvmValHashCode v with
          | some h => .inl (some { st with pc := st.pc + 1, stack := .i32 h :: rest })
          | none => .inr none
        | _, _, _, _ => .inr none
      stepInvokeStatic := fun st cls method desc =>
        let nCls := normalizeUiCommonClass cls
        if nCls == "TargetStateKt" || nCls == "EasingPiecewiseKt" then
          invokeStaticProg st nCls method desc
        else
        match nCls, method, desc, st.stack with
        | "java/lang/Float", "valueOf", "(F)Ljava/lang/Float;", v :: rest =>
          match v.asF32? with
          | some f => .inl (some { st with pc := st.pc + 1, stack := .ext (.boxedFloat f) :: rest })
          | none => .inr none
        | "java/lang/Float", "hashCode", "(F)I", v :: rest =>
          match v.asF32? with
          | some f => .inl (some { st with pc := st.pc + 1, stack := .i32 (floatHashCode f) :: rest })
          | none => .inr none
        | "java/lang/Float", "compare", "(FF)I", b :: a :: rest =>
          match a.asF32?, b.asF32? with
          | some va, some vb =>
            .inl (some { st with pc := st.pc + 1, stack := .i32 (Model.floatCompare va vb).toUInt32 :: rest })
          | _, _ => .inr none
        | "kotlin/collections/ArraysKt", "sortedWith", "([Ljava/lang/Object;Ljava/util/Comparator;)Ljava/util/List;",
            .ext .sortedByComparator :: .heapRef arrAddr :: rest =>
          match st.jvmHeap.get? arrAddr with
          | some (.objArray _ elems) =>
            match decodePairArray elems with
            | some pairs =>
              .inl (some { st with pc := st.pc + 1, stack := .ext (.pairList (sortPairsByKeyframe pairs)) :: rest })
            | none => .inr none
          | _ => .inr none
        | "kotlin/collections/ArraysKt", "toList", "([Ljava/lang/Object;)Ljava/util/List;",
            .heapRef arrAddr :: rest =>
          match st.jvmHeap.get? arrAddr with
          | some (.objArray _ elems) =>
            match decodePairArray elems with
            | some pairs =>
              .inl (some { st with pc := st.pc + 1, stack := .ext (.pairList pairs) :: rest })
            | none => .inr none
          | _ => .inr none
        | "kotlin/collections/MapsKt", "createMapBuilder", "()Ljava/util/Map;", rest =>
          let id := st.heap.maps.size
          let heap' := { st.heap with maps := st.heap.maps.push [] }
          .inl (some { st with pc := st.pc + 1, stack := .ext (.mapRef id) :: rest, heap := heap' })
        | "kotlin/collections/MapsKt", "putAll", "(Ljava/util/Map;[Lkotlin/Pair;)V",
            .heapRef arrAddr :: .ext (.mapRef mid) :: rest =>
          match st.jvmHeap.get? arrAddr, st.heap.maps[mid]? with
          | some (.objArray _ elems), some m =>
            match decodePairArray elems with
            | some pairs =>
              let m' := pairs.foldl (fun acc (k, e) => Model.putKeyMap acc k e) m
              let heap' := { st.heap with maps := st.heap.maps.set! mid m' }
              .inl (some { st with pc := st.pc + 1, stack := rest, heap := heap' })
            | none => .inr none
          | _, _ => .inr none
        | "kotlin/collections/MapsKt", "build", "(Ljava/util/Map;)Ljava/util/Map;",
            .ext (.mapRef mid) :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := .ext (.mapRef mid) :: rest })
        | "kotlin/collections/CollectionsKt", "toList", "(Ljava/lang/Iterable;)Ljava/util/List;",
            .ext (.floatList xs) :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := .ext (.floatList xs) :: rest })
        | "kotlin/collections/CollectionsKt", "toList", "(Ljava/lang/Iterable;)Ljava/util/List;",
            .ext (.easingList xs) :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := .ext (.easingList xs) :: rest })
        | nCls, _, _, _ => invokeStaticProg st nCls method desc
      stepInvokeInterface := fun st cls method desc =>
        match cls, method, desc, st.stack with
        | "kotlin/jvm/functions/Function1", "invoke", _, arg :: .ext .notLambda :: rest =>
          match arg with
          | .boxedBool b => .inl (some { st with pc := st.pc + 1, stack := .boxedBool (!b) :: rest })
          | _ => .inr none
        | "kotlin/jvm/functions/Function1", "invoke", _, arg :: .ext (.fn1Ref fid) :: rest =>
          match st.heap.fn1s[fid]? with
          | some fn =>
            match fn arg with
            | some res => .inl (some { st with pc := st.pc + 1, stack := res :: rest })
            | none => .inr none
          | none => .inr none
        | "java/util/Map", "put", _, .ext (.easing e) :: .ext (.boxedFloat k) :: .ext (.mapRef mid) :: rest =>
          match st.heap.maps[mid]? with
          | some m =>
            let m' := Model.putKeyMap m k e
            let heap' := { st.heap with maps := st.heap.maps.set! mid m' }
            .inl (some { st with pc := st.pc + 1, stack := .null :: rest, heap := heap' })
          | none => .inr none
        | "java/util/Map", "size", "()I", .ext (.mapRef mid) :: rest =>
          match st.heap.maps[mid]? with
          | some m => .inl (some { st with pc := st.pc + 1, stack := .i32 (UInt32.ofNat m.length) :: rest })
          | none => .inr none
        | "java/util/Map", "keySet", "()Ljava/util/Set;", .ext (.mapRef mid) :: rest =>
          match st.heap.maps[mid]? with
          | some m => .inl (some { st with pc := st.pc + 1, stack := .ext (.floatList (m.map Prod.fst)) :: rest })
          | none => .inr none
        | "java/util/Map", "values", "()Ljava/util/Collection;", .ext (.mapRef mid) :: rest =>
          match st.heap.maps[mid]? with
          | some m => .inl (some { st with pc := st.pc + 1, stack := .ext (.easingList (m.map Prod.snd)) :: rest })
          | none => .inr none
        | "java/util/List", "size", "()I", .ext (.floatList xs) :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := .i32 (UInt32.ofNat xs.length) :: rest })
        | "java/util/List", "size", "()I", .ext (.easingList xs) :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := .i32 (UInt32.ofNat xs.length) :: rest })
        | "java/util/List", "size", "()I", .heapRef listAddr :: rest =>
          match Jvm.extractListArray? st.jvmHeap listAddr with
          | some elems => .inl (some { st with pc := st.pc + 1, stack := .i32 (UInt32.ofNat elems.size) :: rest })
          | none => .inr none
        | "java/util/List", "get", "(I)Ljava/lang/Object;", idxVal :: .ext (.floatList xs) :: rest =>
          match idxVal.asI32? with
          | some idx =>
            if idx.toBitVec.slt 0#32 then .inr none
            else if h : idx.toNat < xs.length then
              .inl (some { st with pc := st.pc + 1, stack := .ext (.boxedFloat xs[idx.toNat]) :: rest })
            else .inr none
          | none => .inr none
        | "java/util/List", "get", "(I)Ljava/lang/Object;", idxVal :: .ext (.easingList xs) :: rest =>
          match idxVal.asI32? with
          | some idx =>
            if idx.toBitVec.slt 0#32 then .inr none
            else if h : idx.toNat < xs.length then
              .inl (some { st with pc := st.pc + 1, stack := .ext (.easing xs[idx.toNat]) :: rest })
            else .inr none
          | none => .inr none
        | "java/util/List", "get", "(I)Ljava/lang/Object;", idxVal :: .heapRef listAddr :: rest =>
          match Jvm.extractListArray? st.jvmHeap listAddr, idxVal.asI32? with
          | some elems, some idx =>
            if idx.toBitVec.slt 0#32 then .inr none
            else if h : idx.toNat < elems.size then
              .inl (some { st with pc := st.pc + 1, stack := elems[idx.toNat] :: rest })
            else .inr none
          | _, _ => .inr none
        | "java/lang/Comparable", "compareTo", "(Ljava/lang/Object;)I",
            .ext (.boxedFloat b) :: .ext (.boxedFloat a) :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := .i32 (Model.floatCompare a b).toUInt32 :: rest })
        | "androidx/compose/animation/core/Easing", "transform", "(F)F",
            xVal :: .ext (.easing e) :: rest =>
          match xVal.asF32? with
          | some x =>
            match e with
            | .const eid =>
              match st.heap.easings[eid]? with
              | some f => .inl (some { st with pc := st.pc + 1, stack := .f32 (f x) :: rest })
              | none => .inr none
            | .piecewise cid =>
              match invokeClosure st cid [.f32 x] with
              | some (res, st') => .inl (some { st' with pc := st.pc + 1, stack := res :: rest })
              | none => .inr none
          | none => .inr none
        | _, _, _, _ => .inr none
      stepInvokeDynamic := fun st bsmKind bsmArg desc =>
        if bsmKind == "LambdaMetafactory" then
          let nCaps := (Jvm.parseMethodParamTags desc).length
          if st.stack.length < nCaps then .inr none
          else
            match extractBsmTarget bsmArg with
            | some fnTag =>
              let caps := (st.stack.take nCaps).reverse
              let rest := st.stack.drop nCaps
              let cid := st.heap.closures.size
              let heap' := { st.heap with closures := st.heap.closures.push (fnTag, caps) }
              .inl (some { st with pc := st.pc + 1, stack := .ext (.easing (.piecewise cid)) :: rest, heap := heap' })
            | none => .inr none
        else .inr none
    }

/-- Default leaf hooks without nested bytecode program lookup. -/
def uiCommonHooks : Jvm.JvmHooks UiExt UiHeap :=
  mkUiCommonHooks (fun _ => none) 4 64

abbrev runJvm (fuel : Nat) (prog : List JvmInstr) (st : JvmState) : Option JvmVal :=
  Jvm.runJvm uiCommonHooks fuel prog st

abbrev runJvmRes (fuel : Nat) (prog : List JvmInstr) (st : JvmState) : Option (JvmVal × JvmState) :=
  Jvm.runJvmRes uiCommonHooks fuel prog st

end UiCommon.JvmVerification
