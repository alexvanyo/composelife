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

import Init.Data.UInt
import Jvm.Instr

namespace Jvm

/-- Generic JVM runtime value, parameterized by a module-specific extension type `Ext`. -/
inductive JvmVal (Ext : Type) where
  | i32 (v : UInt32)
  | i64 (v : UInt64)
  | f64 (v : Float)
  | bool (b : Bool)
  | boxedBool (b : Bool)
  | null
  | unit
  | uninit
  | str (s : String)
  | allocRef (cls : String)
  | heapRef (addr : Nat)
  | boxedByte (v : UInt32)
  | boxedUByte (v : UInt32)
  | boxedInt (v : UInt32)
  | boxedUInt (v : UInt32)
  | boxedLong (v : UInt64)
  | boxedULong (v : UInt64)
  | pair (fst snd : JvmVal Ext)
  | strArr (xs : Array String)
  | ext (v : Ext)

instance {Ext : Type} : Inhabited (JvmVal Ext) := ⟨.null⟩

def JvmVal.isNull {Ext : Type} : JvmVal Ext → Bool
  | .null => true
  | _ => false

def JvmVal.asI32 {Ext : Type} : JvmVal Ext → UInt32
  | .i32 v => v
  | .i64 v => v.toUInt32
  | .bool b => if b then 1 else 0
  | _ => 0

def JvmVal.asI64 {Ext : Type} : JvmVal Ext → UInt64
  | .i64 v => v
  | .i32 v => v.toUInt64
  | _ => 0

def JvmVal.asF64 {Ext : Type} : JvmVal Ext → Float
  | .f64 v => v
  | _ => 0.0

def JvmVal.beqVal {Ext : Type} (beqExt : Ext → Ext → Bool) : JvmVal Ext → JvmVal Ext → Bool
  | .null, .null => true
  | .unit, .unit => true
  | .uninit, .uninit => true
  | .bool a, .bool b => a == b
  | .boxedBool a, .boxedBool b => a == b
  | .boxedByte a, .boxedByte b => a == b
  | .boxedUByte a, .boxedUByte b => a == b
  | .i32 a, .i32 b => a == b
  | .boxedInt a, .boxedInt b => a == b
  | .boxedUInt a, .boxedUInt b => a == b
  | .i64 a, .i64 b => a == b
  | .boxedLong a, .boxedLong b => a == b
  | .boxedULong a, .boxedULong b => a == b
  | .f64 a, .f64 b => a == b
  | .str a, .str b => a == b
  | .pair a1 a2, .pair b1 b2 => beqVal beqExt a1 b1 && beqVal beqExt a2 b2
  | .heapRef a, .heapRef b => a == b
  | .ext a, .ext b => beqExt a b
  | _, _ => false

def JvmVal.refEq {Ext : Type} (beqExt : Ext → Ext → Bool) : JvmVal Ext → JvmVal Ext → Bool
  | .null, .null => true
  | .unit, .unit => true
  | .heapRef a, .heapRef b => a == b
  | .allocRef a, .allocRef b => a == b
  | .str a, .str b => a == b
  | .ext a, .ext b => beqExt a b
  | _, _ => false

def defaultIteVal {Ext : Type} (c : Bool) (t e : Option (JvmVal Ext)) : Option (JvmVal Ext) :=
  match t, e with
  | some (.i32 vt), some (.i32 ve) => some (.i32 (if c then vt else ve))
  | some (.i64 vt), some (.i64 ve) => some (.i64 (if c then vt else ve))
  | some (.f64 vt), some (.f64 ve) => some (.f64 (if c then vt else ve))
  | _, _ => if c then t else e

@[simp] theorem defaultIteVal_eq_if {Ext : Type} (c : Bool) (t e : Option (JvmVal Ext)) :
    defaultIteVal c t e = if c then t else e := by
  cases c <;> cases t with
  | none => simp [defaultIteVal]
  | some v => cases v <;> cases e with | none => simp [defaultIteVal] | some w => cases w <;> simp [defaultIteVal]

/-- Heap-allocated mutable JVM arrays, `StringBuilder` buffers, and object instances. -/
inductive HeapObj (Ext : Type) where
  | boolArray (elems : Array Bool)
  | byteArray (elems : Array UInt8)
  | charArray (elems : Array UInt16)
  | shortArray (elems : Array UInt16)
  | intArray (elems : Array UInt32)
  | longArray (elems : Array UInt64)
  | doubleArray (elems : Array Float)
  | objArray (cls : String) (elems : Array (JvmVal Ext))
  | stringBuilder (buf : String)
  | instance (cls : String) (fields : List (String × JvmVal Ext))
  deriving Inhabited

def HeapObj.arrayLength? {Ext : Type} : HeapObj Ext → Option Nat
  | .boolArray elems => some elems.size
  | .byteArray elems => some elems.size
  | .charArray elems => some elems.size
  | .shortArray elems => some elems.size
  | .intArray elems => some elems.size
  | .longArray elems => some elems.size
  | .doubleArray elems => some elems.size
  | .objArray _ elems => some elems.size
  | _ => none

def HeapObj.matchesType {Ext : Type} (cls : String) : HeapObj Ext → Bool
  | .boolArray _ => cls == "[Z" || cls == "java/lang/Object"
  | .byteArray _ => cls == "[B" || cls == "java/lang/Object"
  | .charArray _ => cls == "[C" || cls == "java/lang/Object"
  | .shortArray _ => cls == "[S" || cls == "java/lang/Object"
  | .intArray _ => cls == "[I" || cls == "java/lang/Object"
  | .longArray _ => cls == "[J" || cls == "java/lang/Object"
  | .doubleArray _ => cls == "[D" || cls == "java/lang/Object"
  | .objArray elemCls _ =>
    let arrCls := if elemCls.startsWith "[" then "[" ++ elemCls else "[L" ++ elemCls ++ ";"
    cls == arrCls || cls == "[Ljava/lang/Object;" || cls == "java/lang/Object"
  | .stringBuilder _ =>
    cls == "java/lang/StringBuilder" || cls == "java/lang/CharSequence" || cls == "java/lang/Object"
  | .instance objCls _ => cls == objCls || cls == "java/lang/Object"

def HeapObj.getField? {Ext : Type} (field : String) : HeapObj Ext → Option (JvmVal Ext)
  | .instance _ fields => (fields.find? (fun (f, _) => f == field)).map Prod.snd
  | _ => none

def HeapObj.setField {Ext : Type} (field : String) (v : JvmVal Ext) : HeapObj Ext → Option (HeapObj Ext)
  | .instance cls fields =>
    some (.instance cls ((field, v) :: fields.filter (fun (f, _) => f != field)))
  | _ => none

/-- Generic simulated JVM heap storing allocated objects/arrays and class static fields. -/
structure JvmHeap (Ext : Type) where
  objects : Array (HeapObj Ext) := #[]
  statics : List (String × String × JvmVal Ext) := []
  deriving Inhabited

def JvmHeap.alloc {Ext : Type} (h : JvmHeap Ext) (obj : HeapObj Ext) : Nat × JvmHeap Ext :=
  (h.objects.size, { h with objects := h.objects.push obj })

def JvmHeap.get? {Ext : Type} (h : JvmHeap Ext) (addr : Nat) : Option (HeapObj Ext) :=
  h.objects[addr]?

def JvmHeap.set {Ext : Type} (h : JvmHeap Ext) (addr : Nat) (obj : HeapObj Ext) : JvmHeap Ext :=
  if lt : addr < h.objects.size then { h with objects := h.objects.set addr obj lt } else h

def JvmHeap.getStatic? {Ext : Type} (h : JvmHeap Ext) (cls field : String) : Option (JvmVal Ext) :=
  (h.statics.find? (fun (c, f, _) => c == cls && f == field)).map (fun (_, _, v) => v)

def JvmHeap.setStatic {Ext : Type} (h : JvmHeap Ext) (cls field : String) (v : JvmVal Ext) : JvmHeap Ext :=
  { h with statics := (cls, field, v) :: h.statics.filter (fun (c, f, _) => !(c == cls && f == field)) }

def JvmHeap.checkInstanceOf {Ext : Type} (h : JvmHeap Ext) (cls : String) (addr : Nat) : Bool :=
  match h.get? addr with
  | some obj => obj.matchesType cls
  | none => false

def JvmHeap.checkCast {Ext : Type} (h : JvmHeap Ext) (cls : String) (addr : Nat) : Option (JvmVal Ext) :=
  if h.checkInstanceOf cls addr then some (.heapRef addr) else none

/-- Generic JVM execution state, parameterized by extension value `Ext` and heap `Heap`. -/
structure JvmState (Ext Heap : Type) where
  pc : Nat
  stack : List (JvmVal Ext)
  locals : Nat → JvmVal Ext
  jvmHeap : JvmHeap Ext := {}
  heap : Heap

def setLocal {Ext : Type} (locals : Nat → JvmVal Ext) (idx : Nat) (v : JvmVal Ext) : Nat → JvmVal Ext :=
  fun i => if i = idx then v else locals i

def initJvmState {Ext Heap : Type} (slots : List (Nat × JvmVal Ext))
    (defaultVal : JvmVal Ext := .i32 0) (heap : Heap) (jvmHeap : JvmHeap Ext := {}) : JvmState Ext Heap where
  pc := 0
  stack := []
  locals := slots.foldl (fun loc (idx, v) => setLocal loc idx v) (fun _ => defaultVal)
  jvmHeap := jvmHeap
  heap := heap

def coerceInI32 (v lo hi : UInt32) : UInt32 :=
  if v.toBitVec.slt lo.toBitVec then lo
  else if hi.toBitVec.slt v.toBitVec then hi
  else v

def nlz32 (x : UInt32) : UInt32 :=
  if x == 0 then 32 else 31 - x.log2

def i32ToDecimalString (v : UInt32) : String :=
  if v < 0x80000000 then toString v.toNat
  else "-" ++ toString (0x100000000 - v.toNat)

def i64ToDecimalString (v : UInt64) : String :=
  if v < 0x8000000000000000 then toString v.toNat
  else "-" ++ toString (0x10000000000000000 - v.toNat)

def i32ToFloat (v : UInt32) : Float :=
  v.toInt32.toFloat

theorem float_le_eq_lt_or_beq (a b : Float) :
    (decide (a ≤ b)) = (decide (a < b) || (a == b)) := by
  have h1 : decide (a ≤ b) = a.toModel.le b.toModel := by
    cases hb : a.toModel.le b.toModel with
    | true => exact decide_eq_true (show a.le b = true from decide_eq_true hb)
    | false =>
      apply decide_eq_false
      intro h
      have h' : decide (a.toModel.le b.toModel = true) = true := h
      rw [hb] at h'
      contradiction
  have h2 : decide (a < b) = a.toModel.lt b.toModel := by
    cases hb : a.toModel.lt b.toModel with
    | true => exact decide_eq_true (show a.lt b = true from decide_eq_true hb)
    | false =>
      apply decide_eq_false
      intro h
      have h' : decide (a.toModel.lt b.toModel = true) = true := h
      rw [hb] at h'
      contradiction
  rw [h1, h2]
  change (Option.any (·.isLE) (a.toModel.unpack.compare b.toModel.unpack)) =
    ((a.toModel.unpack.compare b.toModel.unpack == some .lt) ||
      (a.toModel.unpack.compare b.toModel.unpack == some .eq))
  cases a.toModel.unpack.compare b.toModel.unpack with
  | none => rfl
  | some o => cases o <;> rfl

def floatToI32 (x : Float) : UInt32 :=
  if x.isNaN then 0
  else if x >= 2147483647.0 then 0x7FFFFFFF
  else if x <= -2147483648.0 then 0x80000000
  else if x >= 0.0 then UInt32.ofNat x.toUInt64.toNat
  else UInt32.ofNat (0x100000000 - (-x).toUInt64.toNat)

def tableswitchTarget (key : UInt32) (low : Int32) (targets : List Nat) (defaultTarget : Nat) : Nat :=
  let offset := key.toBitVec.toInt - low.toInt
  if 0 ≤ offset ∧ offset < targets.length then targets[offset.toNat]! else defaultTarget

def lookupswitchTarget (key : UInt32) (cases : List (Int32 × Nat)) (defaultTarget : Nat) : Nat :=
  match cases.find? (fun (k, _) => k.toUInt32 == key) with
  | some (_, t) => t
  | none => defaultTarget

def defaultCheckInstanceOf {Ext : Type} (extFn : String → Ext → Bool) (cls : String) (v : JvmVal Ext) : Bool :=
  match cls, v with
  | _, .null => false
  | "java/lang/Object", .boxedBool _ => true
  | "java/lang/Object", .boxedByte _ => true
  | "java/lang/Object", .boxedInt _ => true
  | "java/lang/Object", .boxedLong _ => true
  | "java/lang/Object", .boxedUByte _ => true
  | "java/lang/Object", .boxedUInt _ => true
  | "java/lang/Object", .boxedULong _ => true
  | "java/lang/Object", .pair _ _ => true
  | "java/lang/Object", .str _ => true
  | "java/lang/Object", .strArr _ => true
  | "java/lang/Byte", .boxedByte _ => true
  | "java/lang/Boolean", .boxedBool _ => true
  | "java/lang/Integer", .boxedInt _ => true
  | "java/lang/Long", .boxedLong _ => true
  | "java/lang/Number", .boxedByte _ => true
  | "java/lang/Number", .boxedInt _ => true
  | "java/lang/Number", .boxedLong _ => true
  | "kotlin/Pair", .pair _ _ => true
  | "kotlin/UByte", .boxedUByte _ => true
  | "kotlin/UInt", .boxedUInt _ => true
  | "kotlin/ULong", .boxedULong _ => true
  | "java/lang/String", .str _ => true
  | "java/lang/CharSequence", .str _ => true
  | "java/io/Serializable", .str _ => true
  | "java/lang/Comparable", .str _ => true
  | "[Ljava/lang/String;", .strArr _ => true
  | "[Ljava/lang/Object;", .strArr _ => true
  | "java/lang/Cloneable", .strArr _ => true
  | "java/io/Serializable", .strArr _ => true
  | _, .ext e => extFn cls e
  | _, _ => false

def defaultCheckCast {Ext : Type} (extFn : String → Ext → Option (JvmVal Ext))
    (cls : String) (v : JvmVal Ext) : Option (JvmVal Ext) :=
  match cls, v with
  | _, .null => some .null
  | "java/lang/Object", .boxedBool _ => some v
  | "java/lang/Object", .boxedByte _ => some v
  | "java/lang/Object", .boxedInt _ => some v
  | "java/lang/Object", .boxedLong _ => some v
  | "java/lang/Object", .boxedUByte _ => some v
  | "java/lang/Object", .boxedUInt _ => some v
  | "java/lang/Object", .boxedULong _ => some v
  | "java/lang/Object", .pair _ _ => some v
  | "java/lang/Boolean", .boxedBool _ => some v
  | "java/lang/Byte", .boxedByte _ => some v
  | "java/lang/Integer", .boxedInt _ => some v
  | "java/lang/Long", .boxedLong _ => some v
  | "java/lang/Number", .boxedInt _ => some v
  | "java/lang/Number", .boxedByte _ => some v
  | "java/lang/Number", .boxedLong _ => some v
  | "kotlin/Pair", .pair _ _ => some v
  | "kotlin/UByte", .boxedUByte _ => some v
  | "kotlin/UInt", .boxedUInt _ => some v
  | "kotlin/ULong", .boxedULong _ => some v
  | _, .ext e => extFn cls e
  | _, _ => none

/-- Domain extension hooks configuring per-module types, calls, and heap interactions. -/
structure JvmHooks (Ext Heap : Type) where
  beqExt : Ext → Ext → Bool := fun _ _ => false
  iteVal : Bool → Option (JvmVal Ext) → Option (JvmVal Ext) → Option (JvmVal Ext) := defaultIteVal
  isZero : JvmVal Ext → Bool := fun v => v.asI32 == 0
  iteZero : JvmVal Ext → Option (JvmVal Ext) → Option (JvmVal Ext) → Option (JvmVal Ext) :=
    fun v jump fall => defaultIteVal (v.asI32 == 0) jump fall
  iteNonZero : JvmVal Ext → Option (JvmVal Ext) → Option (JvmVal Ext) → Option (JvmVal Ext) :=
    fun v jump fall => defaultIteVal (!(v.asI32 == 0)) jump fall
  ireturnVal : JvmVal Ext → JvmVal Ext := id
  stepNewClass : JvmState Ext Heap → String → Option (JvmState Ext Heap) ⊕ Option (JvmVal Ext) :=
    fun st cls => .inl (some { st with pc := st.pc + 1, stack := .allocRef cls :: st.stack })
  checkInstanceOf : String → JvmVal Ext → Bool := defaultCheckInstanceOf (fun _ _ => false)
  checkCast : String → JvmVal Ext → Option (JvmVal Ext) := defaultCheckCast (fun _ _ => none)
  isSubtypeOf : String → String → Bool := fun sub sup => sub == sup
  resolveStatic : JvmState Ext Heap → String → String → String → Option (JvmVal Ext) := fun _ _ _ _ => none
  stepInvokeVirtual : JvmState Ext Heap → String → String → String → Option (JvmState Ext Heap) ⊕ Option (JvmVal Ext) :=
    fun _ _ _ _ => .inr none
  stepInvokeSpecial : JvmState Ext Heap → String → String → String → Option (JvmState Ext Heap) ⊕ Option (JvmVal Ext) :=
    fun _ _ _ _ => .inr none
  stepInvokeStatic : JvmState Ext Heap → String → String → String → Option (JvmState Ext Heap) ⊕ Option (JvmVal Ext) :=
    fun _ _ _ _ => .inr none
  stepInvokeInterface : JvmState Ext Heap → String → String → String → Option (JvmState Ext Heap) ⊕ Option (JvmVal Ext) :=
    fun _ _ _ _ => .inr none
  stepInvokeDynamic : JvmState Ext Heap → String → String → String → Option (JvmState Ext Heap) ⊕ Option (JvmVal Ext) :=
    fun _ _ _ _ => .inr none
  stepGetField : JvmState Ext Heap → String → String → String → Option (JvmState Ext Heap) ⊕ Option (JvmVal Ext) :=
    fun _ _ _ _ => .inr none
  stepPutField : JvmState Ext Heap → String → String → String → Option (JvmState Ext Heap) ⊕ Option (JvmVal Ext) :=
    fun _ _ _ _ => .inr none
  stepPutStatic : JvmState Ext Heap → String → String → String → Option (JvmState Ext Heap) ⊕ Option (JvmVal Ext) :=
    fun _ _ _ _ => .inr none

private def parseParamTagsAux (inArr inClass : Bool := false) : List Char → List Char
  | [] => []
  | c :: rest =>
    if inClass then
      if c == ';' then 'L' :: parseParamTagsAux false false rest
      else parseParamTagsAux false true rest
    else if inArr then
      if c == '[' then parseParamTagsAux true false rest
      else if c == 'L' then parseParamTagsAux false true rest
      else 'L' :: parseParamTagsAux false false rest
    else
      match c with
      | ')' => []
      | 'L' => parseParamTagsAux false true rest
      | '[' => parseParamTagsAux true false rest
      | _ => c :: parseParamTagsAux false false rest

def parseMethodParamTags (desc : String) : List Char :=
  match desc.toList.dropWhile (· != '(') with
  | '(' :: rest => parseParamTagsAux false false rest
  | _ => []

def formatConcatArg {Ext : Type} (tag : Char) (v : JvmVal Ext) : String :=
  match tag with
  | 'I' | 'B' | 'S' => i32ToDecimalString v.asI32
  | 'J' => i64ToDecimalString v.asI64
  | 'D' => toString v.asF64
  | 'C' => String.singleton (Char.ofNat (v.asI32 &&& 0xFFFF).toNat)
  | 'Z' => if v.asI32 != 0 then "true" else "false"
  | _ =>
    match v with
    | .str s => s
    | .null => "null"
    | .boxedInt n => i32ToDecimalString n
    | .boxedLong n => i64ToDecimalString n
    | .boxedByte n => i32ToDecimalString (UInt32.ofBitVec ((n.toBitVec.setWidth 8).signExtend 32))
    | .boxedUByte n => Nat.repr (n &&& 0xFF).toNat
    | .boxedUInt n => Nat.repr n.toNat
    | .boxedULong n => Nat.repr n.toNat
    | .boxedBool b => if b then "true" else "false"
    | .i32 n => i32ToDecimalString n
    | .i64 n => i64ToDecimalString n
    | .f64 d => toString d
    | _ => "<obj>"

private def interpConcatRecipeAux {Ext : Type} : List Char → List (Char × JvmVal Ext) → String
  | [], _ => ""
  | c :: cs, tagged =>
    if c.toNat == 1 then
      match tagged with
      | (tag, v) :: tRest => formatConcatArg tag v ++ interpConcatRecipeAux cs tRest
      | [] => @interpConcatRecipeAux Ext cs []
    else
      String.singleton c ++ interpConcatRecipeAux cs tagged

def evalMakeConcatWithConstants {Ext : Type} (recipe desc : String)
    (stack : List (JvmVal Ext)) : Option (String × List (JvmVal Ext)) :=
  let tags := parseMethodParamTags desc
  let n := tags.length
  if stack.length < n then none
  else
    let args := (stack.take n).reverse
    let rest := stack.drop n
    some (interpConcatRecipeAux recipe.toList (tags.zip args), rest)

private def stepCopyOfRange {Ext Heap : Type} (st : JvmState Ext Heap)
    (addr : Nat) (fromIdx toIdx : Int) (rest : List (JvmVal Ext)) :
    Option (JvmState Ext Heap) ⊕ Option (JvmVal Ext) :=
  match st.jvmHeap.get? addr with
  | some (.byteArray elems) =>
    if fromIdx < 0 || toIdx < fromIdx || toIdx > elems.size then .inr none
    else
      let f := fromIdx.toNat
      let n := toIdx.toNat - f
      let sliced := Array.ofFn (n := n) (fun i => elems[f + i.val]!)
      let (newAddr, h') := st.jvmHeap.alloc (.byteArray sliced)
      .inl (some { st with pc := st.pc + 1, stack := .heapRef newAddr :: rest, jvmHeap := h' })
  | some (.longArray elems) =>
    if fromIdx < 0 || toIdx < fromIdx || toIdx > elems.size then .inr none
    else
      let f := fromIdx.toNat
      let n := toIdx.toNat - f
      let sliced := Array.ofFn (n := n) (fun i => elems[f + i.val]!)
      let (newAddr, h') := st.jvmHeap.alloc (.longArray sliced)
      .inl (some { st with pc := st.pc + 1, stack := .heapRef newAddr :: rest, jvmHeap := h' })
  | some (.intArray elems) =>
    if fromIdx < 0 || toIdx < fromIdx || toIdx > elems.size then .inr none
    else
      let f := fromIdx.toNat
      let n := toIdx.toNat - f
      let sliced := Array.ofFn (n := n) (fun i => elems[f + i.val]!)
      let (newAddr, h') := st.jvmHeap.alloc (.intArray sliced)
      .inl (some { st with pc := st.pc + 1, stack := .heapRef newAddr :: rest, jvmHeap := h' })
  | some (.objArray cls elems) =>
    if fromIdx < 0 || toIdx < fromIdx || toIdx > elems.size then .inr none
    else
      let f := fromIdx.toNat
      let n := toIdx.toNat - f
      let sliced := Array.ofFn (n := n) (fun i => elems[f + i.val]!)
      let (newAddr, h') := st.jvmHeap.alloc (.objArray cls sliced)
      .inl (some { st with pc := st.pc + 1, stack := .heapRef newAddr :: rest, jvmHeap := h' })
  | _ => .inr none

private def stepFillRange {Ext Heap : Type} (st : JvmState Ext Heap)
    (addr : Nat) (elem fromVal toVal maskVal : JvmVal Ext) (rest : List (JvmVal Ext)) :
    Option (JvmState Ext Heap) ⊕ Option (JvmVal Ext) :=
  let mask := maskVal.asI32
  match st.jvmHeap.get? addr with
  | some (.objArray cls elems) =>
    let fromIdx := if (mask &&& 2) != 0 then (0 : Int) else fromVal.asI32.toBitVec.toInt
    let toIdx := if (mask &&& 4) != 0 then (elems.size : Int) else toVal.asI32.toBitVec.toInt
    if fromIdx < 0 || toIdx < fromIdx || toIdx > elems.size then .inr none
    else
      let filled := Array.ofFn (n := elems.size) (fun i =>
        if fromIdx.toNat ≤ i.val && i.val < toIdx.toNat then elem else elems[i.val])
      let h' := st.jvmHeap.set addr (.objArray cls filled)
      .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
  | some (.byteArray elems) =>
    let fromIdx := if (mask &&& 2) != 0 then (0 : Int) else fromVal.asI32.toBitVec.toInt
    let toIdx := if (mask &&& 4) != 0 then (elems.size : Int) else toVal.asI32.toBitVec.toInt
    if fromIdx < 0 || toIdx < fromIdx || toIdx > elems.size then .inr none
    else
      let b := elem.asI32.toUInt8
      let filled := Array.ofFn (n := elems.size) (fun i =>
        if fromIdx.toNat ≤ i.val && i.val < toIdx.toNat then b else elems[i.val])
      let h' := st.jvmHeap.set addr (.byteArray filled)
      .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
  | some (.intArray elems) =>
    let fromIdx := if (mask &&& 2) != 0 then (0 : Int) else fromVal.asI32.toBitVec.toInt
    let toIdx := if (mask &&& 4) != 0 then (elems.size : Int) else toVal.asI32.toBitVec.toInt
    if fromIdx < 0 || toIdx < fromIdx || toIdx > elems.size then .inr none
    else
      let v := elem.asI32
      let filled := Array.ofFn (n := elems.size) (fun i =>
        if fromIdx.toNat ≤ i.val && i.val < toIdx.toNat then v else elems[i.val])
      let h' := st.jvmHeap.set addr (.intArray filled)
      .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
  | some (.longArray elems) =>
    let fromIdx := if (mask &&& 2) != 0 then (0 : Int) else fromVal.asI32.toBitVec.toInt
    let toIdx := if (mask &&& 4) != 0 then (elems.size : Int) else toVal.asI32.toBitVec.toInt
    if fromIdx < 0 || toIdx < fromIdx || toIdx > elems.size then .inr none
    else
      let v := elem.asI64
      let filled := Array.ofFn (n := elems.size) (fun i =>
        if fromIdx.toNat ≤ i.val && i.val < toIdx.toNat then v else elems[i.val])
      let h' := st.jvmHeap.set addr (.longArray filled)
      .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
  | _ => .inr none

def stepInvokeVirtualGeneric {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    (st : JvmState Ext Heap) (cls method desc : String) : Option (JvmState Ext Heap) ⊕ Option (JvmVal Ext) :=
  match cls with
  | "kotlin/UInt" =>
    match method, st.stack with
    | "unbox-impl", .boxedUInt v :: rest => .inl (some { st with pc := st.pc + 1, stack := .i32 v :: rest })
    | _, _ => hooks.stepInvokeVirtual st cls method desc
  | "kotlin/Pair" =>
    match method, st.stack with
    | "getFirst", .pair a _ :: rest => .inl (some { st with pc := st.pc + 1, stack := a :: rest })
    | "getSecond", .pair _ b :: rest => .inl (some { st with pc := st.pc + 1, stack := b :: rest })
    | _, _ => hooks.stepInvokeVirtual st cls method desc
  | "java/lang/Integer" =>
    match method, st.stack with
    | "intValue", .boxedInt v :: rest => .inl (some { st with pc := st.pc + 1, stack := .i32 v :: rest })
    | _, _ => hooks.stepInvokeVirtual st cls method desc
  | "java/lang/Byte" =>
    match method, st.stack with
    | "byteValue", .boxedByte v :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 (UInt32.ofBitVec ((v.toBitVec.setWidth 8).signExtend 32)) :: rest })
    | _, _ => hooks.stepInvokeVirtual st cls method desc
  | "java/lang/Long" =>
    match method, st.stack with
    | "longValue", .boxedLong v :: rest => .inl (some { st with pc := st.pc + 1, stack := .i64 v :: rest })
    | _, _ => hooks.stepInvokeVirtual st cls method desc
  | "java/lang/Number" =>
    match method, st.stack with
    | "byteValue", .boxedByte v :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 (UInt32.ofBitVec ((v.toBitVec.setWidth 8).signExtend 32)) :: rest })
    | "intValue", .boxedInt v :: rest => .inl (some { st with pc := st.pc + 1, stack := .i32 v :: rest })
    | "longValue", .boxedLong v :: rest => .inl (some { st with pc := st.pc + 1, stack := .i64 v :: rest })
    | _, _ => hooks.stepInvokeVirtual st cls method desc
  | "kotlin/UByte" =>
    match method, st.stack with
    | "unbox-impl", .boxedUByte v :: rest => .inl (some { st with pc := st.pc + 1, stack := .i32 v :: rest })
    | _, _ => hooks.stepInvokeVirtual st cls method desc
  | "kotlin/ULong" =>
    match method, st.stack with
    | "unbox-impl", .boxedULong v :: rest => .inl (some { st with pc := st.pc + 1, stack := .i64 v :: rest })
    | _, _ => hooks.stepInvokeVirtual st cls method desc
  | "java/lang/Boolean" =>
    match method, st.stack with
    | "booleanValue", .boxedBool b :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 (if b then 1 else 0) :: rest })
    | _, _ => hooks.stepInvokeVirtual st cls method desc
  | "java/lang/StringBuilder" =>
    match method, desc, st.stack with
    | "append", "(Ljava/lang/String;)Ljava/lang/StringBuilder;", arg :: .heapRef addr :: rest =>
      match st.jvmHeap.get? addr with
      | some (.stringBuilder buf) =>
        let s := match arg with | .str str => str | .null => "null" | _ => ""
        let h' := st.jvmHeap.set addr (.stringBuilder (buf ++ s))
        .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
      | _ => .inr none
    | "append", "(I)Ljava/lang/StringBuilder;", arg :: .heapRef addr :: rest =>
      match st.jvmHeap.get? addr with
      | some (.stringBuilder buf) =>
        let h' := st.jvmHeap.set addr (.stringBuilder (buf ++ i32ToDecimalString arg.asI32))
        .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
      | _ => .inr none
    | "append", "(C)Ljava/lang/StringBuilder;", arg :: .heapRef addr :: rest =>
      match st.jvmHeap.get? addr with
      | some (.stringBuilder buf) =>
        let ch := Char.ofNat (arg.asI32 &&& 0xFFFF).toNat
        let h' := st.jvmHeap.set addr (.stringBuilder (buf ++ String.singleton ch))
        .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
      | _ => .inr none
    | "append", "(J)Ljava/lang/StringBuilder;", arg :: .heapRef addr :: rest =>
      match st.jvmHeap.get? addr with
      | some (.stringBuilder buf) =>
        let h' := st.jvmHeap.set addr (.stringBuilder (buf ++ i64ToDecimalString arg.asI64))
        .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
      | _ => .inr none
    | "toString", "()Ljava/lang/String;", .heapRef addr :: rest =>
      match st.jvmHeap.get? addr with
      | some (.stringBuilder buf) =>
        .inl (some { st with pc := st.pc + 1, stack := .str buf :: rest })
      | _ => .inr none
    | _, _, _ => hooks.stepInvokeVirtual st cls method desc
  | "java/lang/Object" =>
    match method, desc, st.stack with
    | "toString", "()Ljava/lang/String;", .str s :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .str s :: rest })
    | "toString", "()Ljava/lang/String;", .heapRef addr :: rest =>
      match st.jvmHeap.get? addr with
      | some (.stringBuilder buf) => .inl (some { st with pc := st.pc + 1, stack := .str buf :: rest })
      | _ => hooks.stepInvokeVirtual st cls method desc
    | _, _, _ => hooks.stepInvokeVirtual st cls method desc
  | _ => hooks.stepInvokeVirtual st cls method desc

def stepInvokeSpecialGeneric {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    (st : JvmState Ext Heap) (cls method desc : String) : Option (JvmState Ext Heap) ⊕ Option (JvmVal Ext) :=
  match cls with
  | "kotlin/Pair" =>
    match method, st.stack with
    | "<init>", b :: a :: .allocRef "kotlin/Pair" :: .allocRef "kotlin/Pair" :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .pair a b :: rest })
    | "<init>", b :: a :: .uninit :: .uninit :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .pair a b :: rest })
    | _, _ => hooks.stepInvokeSpecial st cls method desc
  | "kotlin/NoWhenBranchMatchedException" =>
    match method, st.stack with
    | "<init>",
        .allocRef "kotlin/NoWhenBranchMatchedException" :: .allocRef "kotlin/NoWhenBranchMatchedException" :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .allocRef "kotlin/NoWhenBranchMatchedException" :: rest })
    | "<init>", .uninit :: .uninit :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .null :: rest })
    | _, _ => hooks.stepInvokeSpecial st cls method desc
  | "java/lang/IllegalArgumentException" =>
    match method, st.stack with
    | "<init>", _msg :: .allocRef "java/lang/IllegalArgumentException" :: .allocRef "java/lang/IllegalArgumentException" :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .allocRef "java/lang/IllegalArgumentException" :: rest })
    | "<init>", _msg :: .uninit :: .uninit :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .null :: rest })
    | _, _ => hooks.stepInvokeSpecial st cls method desc
  | "java/lang/IllegalStateException" =>
    match method, st.stack with
    | "<init>", _msg :: .allocRef "java/lang/IllegalStateException" :: .allocRef "java/lang/IllegalStateException" :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .allocRef "java/lang/IllegalStateException" :: rest })
    | "<init>", _msg :: .uninit :: .uninit :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .null :: rest })
    | _, _ => hooks.stepInvokeSpecial st cls method desc
  | "java/lang/StringBuilder" =>
    match method, desc, st.stack with
    | "<init>", "()V", .heapRef addr :: rest =>
      match st.jvmHeap.get? addr with
      | some (.stringBuilder _) =>
        let h' := st.jvmHeap.set addr (.stringBuilder "")
        .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
      | _ => .inr none
    | "<init>", "(Ljava/lang/String;)V", .str s :: .heapRef addr :: rest =>
      match st.jvmHeap.get? addr with
      | some (.stringBuilder _) =>
        let h' := st.jvmHeap.set addr (.stringBuilder s)
        .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
      | _ => .inr none
    | _, _, _ => hooks.stepInvokeSpecial st cls method desc
  | _ => hooks.stepInvokeSpecial st cls method desc

def stepInvokeStaticGeneric {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    (st : JvmState Ext Heap) (cls method desc : String) : Option (JvmState Ext Heap) ⊕ Option (JvmVal Ext) :=
  match cls with
  | "kotlin/UInt" =>
    match method, desc, st.stack with
    | "constructor-impl", "(I)I", _ => .inl (some { st with pc := st.pc + 1 })
    | "box-impl", "(I)Lkotlin/UInt;", v :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .boxedUInt v.asI32 :: rest })
    | _, _, _ => hooks.stepInvokeStatic st cls method desc
  | "kotlin/ULong" =>
    match method, desc, st.stack with
    | "constructor-impl", "(J)J", _ => .inl (some { st with pc := st.pc + 1 })
    | "box-impl", "(J)Lkotlin/ULong;", v :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .boxedULong v.asI64 :: rest })
    | _, _, _ => hooks.stepInvokeStatic st cls method desc
  | "kotlin/UByte" =>
    match method, desc, st.stack with
    | "constructor-impl", "(B)B", _ => .inl (some { st with pc := st.pc + 1 })
    | "box-impl", "(B)Lkotlin/UByte;", v :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .boxedUByte v.asI32 :: rest })
    | _, _, _ => hooks.stepInvokeStatic st cls method desc
  | "kotlin/ULongArray" =>
    match method, desc with
    | "constructor-impl", "([J)[J" => .inl (some { st with pc := st.pc + 1 })
    | _, _ => hooks.stepInvokeStatic st cls method desc
  | "kotlin/jvm/internal/Intrinsics" =>
    match method, desc, st.stack with
    | "compare", "(II)I", b :: a :: rest =>
      let va := a.asI32
      let vb := b.asI32
      let res : UInt32 := if va == vb then 0 else if va.toBitVec.slt vb.toBitVec then 4294967295 else 1
      .inl (some { st with pc := st.pc + 1, stack := .i32 res :: rest })
    | "areEqual", "(Ljava/lang/Object;Ljava/lang/Object;)Z", b :: a :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .bool (JvmVal.beqVal hooks.beqExt a b) :: rest })
    | "checkNotNull", "(Ljava/lang/Object;Ljava/lang/String;)V", _msg :: obj :: rest
    | "checkNotNullParameter", "(Ljava/lang/Object;Ljava/lang/String;)V", _msg :: obj :: rest
    | "checkNotNullExpressionValue", "(Ljava/lang/Object;Ljava/lang/String;)V", _msg :: obj :: rest =>
      if obj.isNull then .inr none
      else .inl (some { st with pc := st.pc + 1, stack := rest })
    | _, _, _ => hooks.stepInvokeStatic st cls method desc
  | "java/lang/Integer" =>
    match method, desc, st.stack with
    | "valueOf", "(I)Ljava/lang/Integer;", v :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .boxedInt v.asI32 :: rest })
    | "compareUnsigned", "(II)I", b :: a :: rest =>
      let va := a.asI32
      let vb := b.asI32
      let res : UInt32 := if va == vb then 0 else if va < vb then 4294967295 else 1
      .inl (some { st with pc := st.pc + 1, stack := .i32 res :: rest })
    | "divideUnsigned", "(II)I", b :: a :: rest =>
      if b.asI32 == 0 then .inr none
      else .inl (some { st with pc := st.pc + 1, stack := .i32 (a.asI32 / b.asI32) :: rest })
    | "remainderUnsigned", "(II)I", b :: a :: rest =>
      if b.asI32 == 0 then .inr none
      else .inl (some { st with pc := st.pc + 1, stack := .i32 (a.asI32 % b.asI32) :: rest })
    | "numberOfLeadingZeros", "(I)I", a :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 (nlz32 a.asI32) :: rest })
    | _, _, _ => hooks.stepInvokeStatic st cls method desc
  | "java/lang/Long" =>
    match method, desc, st.stack with
    | "compareUnsigned", "(JJ)I", b :: a :: rest =>
      let va := a.asI64
      let vb := b.asI64
      let res : UInt32 := if va == vb then 0 else if va < vb then 4294967295 else 1
      .inl (some { st with pc := st.pc + 1, stack := .i32 res :: rest })
    | _, _, _ => hooks.stepInvokeStatic st cls method desc
  | "java/lang/Math" =>
    match method, desc, st.stack with
    | "max", "(II)I", b :: a :: rest =>
      let va := a.asI32
      let vb := b.asI32
      let res : UInt32 := if va.toBitVec.slt vb.toBitVec then vb else va
      .inl (some { st with pc := st.pc + 1, stack := .i32 res :: rest })
    | _, _, _ => hooks.stepInvokeStatic st cls method desc
  | "kotlin/ranges/RangesKt" =>
    match method, desc, st.stack with
    | "coerceIn", "(III)I", hi :: lo :: v :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 (coerceInI32 v.asI32 lo.asI32 hi.asI32) :: rest })
    | _, _, _ => hooks.stepInvokeStatic st cls method desc
  | "kotlin/jvm/internal/TypeIntrinsics" =>
    match method, desc, st.stack with
    | "beforeCheckcastToFunctionOfArity", "(Ljava/lang/Object;I)Ljava/lang/Object;", _arity :: fnObj :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := fnObj :: rest })
    | _, _, _ => hooks.stepInvokeStatic st cls method desc
  | "kotlin/UByteArray" =>
    match method, desc, st.stack with
    | "constructor-impl", "(I)[B", sizeVal :: rest =>
      if sizeVal.asI32.toBitVec.slt 0#32 then .inr none
      else
        let (addr, h') := st.jvmHeap.alloc (.byteArray (Array.replicate sizeVal.asI32.toNat 0))
        .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
    | "get-w2LRezQ", "([BI)B", idxVal :: .heapRef addr :: rest =>
      let idx := idxVal.asI32
      if idx.toBitVec.slt 0#32 then .inr none
      else match st.jvmHeap.get? addr with
        | some (.byteArray elems) =>
          if h : idx.toNat < elems.size then
            let b := UInt32.ofBitVec (elems[idx.toNat].toBitVec.signExtend 32)
            .inl (some { st with pc := st.pc + 1, stack := .i32 b :: rest })
          else .inr none
        | _ => .inr none
    | "set-VurrAj0", "([BIB)V", val :: idxVal :: .heapRef addr :: rest =>
      let idx := idxVal.asI32
      if idx.toBitVec.slt 0#32 then .inr none
      else match st.jvmHeap.get? addr with
        | some (.byteArray elems) =>
          if h : idx.toNat < elems.size then
            let h' := st.jvmHeap.set addr (.byteArray (elems.set idx.toNat val.asI32.toUInt8 h))
            .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
          else .inr none
        | _ => .inr none
    | "getSize-impl", "([B)I", .heapRef addr :: rest =>
      match st.jvmHeap.get? addr with
      | some (.byteArray elems) =>
        .inl (some { st with pc := st.pc + 1, stack := .i32 (UInt32.ofNat elems.size) :: rest })
      | _ => .inr none
    | _, _, _ => hooks.stepInvokeStatic st cls method desc
  | "kotlin/UIntArray" =>
    match method, desc, st.stack with
    | "constructor-impl", "(I)[I", sizeVal :: rest =>
      if sizeVal.asI32.toBitVec.slt 0#32 then .inr none
      else
        let (addr, h') := st.jvmHeap.alloc (.intArray (Array.replicate sizeVal.asI32.toNat 0))
        .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
    | "get-pVg5ArA", "([II)I", idxVal :: .heapRef addr :: rest =>
      let idx := idxVal.asI32
      if idx.toBitVec.slt 0#32 then .inr none
      else match st.jvmHeap.get? addr with
        | some (.intArray elems) =>
          if h : idx.toNat < elems.size then
            .inl (some { st with pc := st.pc + 1, stack := .i32 elems[idx.toNat] :: rest })
          else .inr none
        | _ => .inr none
    | "set-VXSXFK8", "([III)V", val :: idxVal :: .heapRef addr :: rest =>
      let idx := idxVal.asI32
      if idx.toBitVec.slt 0#32 then .inr none
      else match st.jvmHeap.get? addr with
        | some (.intArray elems) =>
          if h : idx.toNat < elems.size then
            let h' := st.jvmHeap.set addr (.intArray (elems.set idx.toNat val.asI32 h))
            .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
          else .inr none
        | _ => .inr none
    | "getSize-impl", "([I)I", .heapRef addr :: rest =>
      match st.jvmHeap.get? addr with
      | some (.intArray elems) =>
        .inl (some { st with pc := st.pc + 1, stack := .i32 (UInt32.ofNat elems.size) :: rest })
      | _ => .inr none
    | _, _, _ => hooks.stepInvokeStatic st cls method desc
  | "java/lang/Boolean" =>
    match method, desc, st.stack with
    | "valueOf", "(Z)Ljava/lang/Boolean;", v :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .boxedBool (v.asI32 != 0) :: rest })
    | _, _, _ => hooks.stepInvokeStatic st cls method desc
  | "java/lang/String" =>
    match method, desc, st.stack with
    | "valueOf", "(I)Ljava/lang/String;", v :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .str (i32ToDecimalString v.asI32) :: rest })
    | _, _, _ => hooks.stepInvokeStatic st cls method desc
  | "java/util/Arrays" =>
    match method, desc, st.stack with
    | "copyOf", "([Ljava/lang/Object;I)[Ljava/lang/Object;", newLenVal :: .heapRef addr :: rest =>
      if newLenVal.asI32.toBitVec.slt 0#32 then .inr none
      else match st.jvmHeap.get? addr with
        | some (.objArray elemCls elems) =>
          let n := newLenVal.asI32.toNat
          let copied := Array.ofFn (n := n) (fun i => if h : i.val < elems.size then elems[i.val] else .null)
          let (newAddr, h') := st.jvmHeap.alloc (.objArray elemCls copied)
          .inl (some { st with pc := st.pc + 1, stack := .heapRef newAddr :: rest, jvmHeap := h' })
        | _ => .inr none
    | _, _, _ => hooks.stepInvokeStatic st cls method desc
  | "kotlin/collections/ArraysKt" =>
    match method, st.stack with
    | "copyOfRange", toVal :: fromVal :: .heapRef addr :: rest =>
      stepCopyOfRange st addr fromVal.asI32.toBitVec.toInt toVal.asI32.toBitVec.toInt rest
    | "fill$default", _handler :: maskVal :: toVal :: fromVal :: elem :: .heapRef addr :: rest =>
      stepFillRange st addr elem fromVal toVal maskVal rest
    | _, _ => hooks.stepInvokeStatic st cls method desc
  | "kotlin/collections/unsigned/UArraysKt" =>
    match method, st.stack with
    | "fill-WpHrYlw$default", _handler :: maskVal :: toVal :: fromVal :: elem :: .heapRef addr :: rest =>
      stepFillRange st addr elem fromVal toVal maskVal rest
    | _, _ => hooks.stepInvokeStatic st cls method desc
  | "kotlin/text/StringsKt" =>
    match method, desc, st.stack with
    | "concatToString", "([C)Ljava/lang/String;", .heapRef addr :: rest =>
      match st.jvmHeap.get? addr with
      | some (.charArray elems) =>
        let s := String.ofList (elems.toList.map fun c => Char.ofNat c.toNat)
        .inl (some { st with pc := st.pc + 1, stack := .str s :: rest })
      | _ => .inr none
    | "decodeToString", "([B)Ljava/lang/String;", .heapRef addr :: rest =>
      match st.jvmHeap.get? addr with
      | some (.byteArray elems) =>
        match String.fromUTF8? ⟨elems⟩ with
        | some s => .inl (some { st with pc := st.pc + 1, stack := .str s :: rest })
        | none => .inr none
      | _ => .inr none
    | "encodeToByteArray", "(Ljava/lang/String;)[B", .str s :: rest =>
      let (addr, h') := st.jvmHeap.alloc (.byteArray s.toUTF8.data)
      .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
    | _, _, _ => hooks.stepInvokeStatic st cls method desc
  | _ => hooks.stepInvokeStatic st cls method desc

private def stepNewArray {Ext Heap : Type} (st : JvmState Ext Heap) (elemType : String) :
    Option (JvmState Ext Heap) ⊕ Option (JvmVal Ext) :=
  match st.stack with
  | lenVal :: rest =>
    if lenVal.asI32.toBitVec.slt 0#32 then .inr none
    else
      let n := lenVal.asI32.toNat
      let obj? : Option (HeapObj Ext) :=
        match elemType with
        | "boolean" => some (.boolArray (Array.replicate n false))
        | "byte" => some (.byteArray (Array.replicate n 0))
        | "char" => some (.charArray (Array.replicate n 0))
        | "short" => some (.shortArray (Array.replicate n 0))
        | "int" => some (.intArray (Array.replicate n 0))
        | "long" => some (.longArray (Array.replicate n 0))
        | "double" => some (.doubleArray (Array.replicate n 0.0))
        | _ => none
      match obj? with
      | some obj =>
        let (addr, h') := st.jvmHeap.alloc obj
        .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
      | none => .inr none
  | _ => .inr none

private def stepArrayLoad {Ext Heap : Type} (st : JvmState Ext Heap) (kind : UInt8) :
    Option (JvmState Ext Heap) ⊕ Option (JvmVal Ext) :=
  match st.stack with
  | idxVal :: arrVal :: rest =>
    let idx := idxVal.asI32
    if idx.toBitVec.slt 0#32 then .inr none
    else match arrVal with
      | .heapRef addr =>
        match st.jvmHeap.get? addr, kind with
        | some (.objArray _ elems), 0 =>
          if h : idx.toNat < elems.size then .inl (some { st with pc := st.pc + 1, stack := elems[idx.toNat] :: rest })
          else .inr none
        | some (.byteArray elems), 1 =>
          if h : idx.toNat < elems.size then
            let v := UInt32.ofBitVec (elems[idx.toNat].toBitVec.signExtend 32)
            .inl (some { st with pc := st.pc + 1, stack := .i32 v :: rest })
          else .inr none
        | some (.boolArray elems), 1 =>
          if h : idx.toNat < elems.size then
            .inl (some { st with pc := st.pc + 1, stack := .i32 (if elems[idx.toNat] then 1 else 0) :: rest })
          else .inr none
        | some (.charArray elems), 2 =>
          if h : idx.toNat < elems.size then
            .inl (some { st with pc := st.pc + 1, stack := .i32 (UInt32.ofNat elems[idx.toNat].toNat) :: rest })
          else .inr none
        | some (.intArray elems), 3 =>
          if h : idx.toNat < elems.size then
            .inl (some { st with pc := st.pc + 1, stack := .i32 elems[idx.toNat] :: rest })
          else .inr none
        | some (.longArray elems), 4 =>
          if h : idx.toNat < elems.size then
            .inl (some { st with pc := st.pc + 1, stack := .i64 elems[idx.toNat] :: rest })
          else .inr none
        | some (.doubleArray elems), 5 =>
          if h : idx.toNat < elems.size then
            .inl (some { st with pc := st.pc + 1, stack := .f64 elems[idx.toNat] :: rest })
          else .inr none
        | _, _ => .inr none
      | .strArr xs =>
        if kind == 0 then
          if h : idx.toNat < xs.size then .inl (some { st with pc := st.pc + 1, stack := .str xs[idx.toNat] :: rest })
          else .inr none
        else .inr none
      | _ => .inr none
  | _ => .inr none

private def stepArrayStore {Ext Heap : Type} (st : JvmState Ext Heap) (kind : UInt8) :
    Option (JvmState Ext Heap) ⊕ Option (JvmVal Ext) :=
  match st.stack with
  | val :: idxVal :: .heapRef addr :: rest =>
    let idx := idxVal.asI32
    if idx.toBitVec.slt 0#32 then .inr none
    else match st.jvmHeap.get? addr, kind with
      | some (.objArray cls elems), 0 =>
        if h : idx.toNat < elems.size then
          let h' := st.jvmHeap.set addr (.objArray cls (elems.set idx.toNat val h))
          .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
        else .inr none
      | some (.byteArray elems), 1 =>
        if h : idx.toNat < elems.size then
          let h' := st.jvmHeap.set addr (.byteArray (elems.set idx.toNat val.asI32.toUInt8 h))
          .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
        else .inr none
      | some (.boolArray elems), 1 =>
        if h : idx.toNat < elems.size then
          let h' := st.jvmHeap.set addr (.boolArray (elems.set idx.toNat ((val.asI32 &&& 1) != 0) h))
          .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
        else .inr none
      | some (.charArray elems), 2 =>
        if h : idx.toNat < elems.size then
          let h' := st.jvmHeap.set addr (.charArray (elems.set idx.toNat val.asI32.toUInt16 h))
          .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
        else .inr none
      | some (.intArray elems), 3 =>
        if h : idx.toNat < elems.size then
          let h' := st.jvmHeap.set addr (.intArray (elems.set idx.toNat val.asI32 h))
          .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
        else .inr none
      | some (.longArray elems), 4 =>
        if h : idx.toNat < elems.size then
          let h' := st.jvmHeap.set addr (.longArray (elems.set idx.toNat val.asI64 h))
          .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
        else .inr none
      | some (.doubleArray elems), 5 =>
        if h : idx.toNat < elems.size then
          let h' := st.jvmHeap.set addr (.doubleArray (elems.set idx.toNat val.asF64 h))
          .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
        else .inr none
      | _, _ => .inr none
  | _ => .inr none

def stepInstr {Ext Heap : Type} (hooks : JvmHooks Ext Heap) (instr : JvmInstr) (st : JvmState Ext Heap) :
    Option (JvmState Ext Heap) ⊕ Option (JvmVal Ext) :=
  match instr with
  | .nop => .inl (some { st with pc := st.pc + 1 })
  | .aconstNull => .inl (some { st with pc := st.pc + 1, stack := .null :: st.stack })
  | .dup =>
    match st.stack with
    | v :: _ => .inl (some { st with pc := st.pc + 1, stack := v :: st.stack })
    | _ => .inr none
  | .pop =>
    match st.stack with
    | _ :: rest => .inl (some { st with pc := st.pc + 1, stack := rest })
    | _ => .inr none
  | .swap =>
    match st.stack with
    | a :: b :: rest => .inl (some { st with pc := st.pc + 1, stack := b :: a :: rest })
    | _ => .inr none
  | .athrow => .inr none
  | .iconst v => .inl (some { st with pc := st.pc + 1, stack := .i32 v :: st.stack })
  | .lconst v => .inl (some { st with pc := st.pc + 1, stack := .i64 v :: st.stack })
  | .dconst0 => .inl (some { st with pc := st.pc + 1, stack := .f64 0.0 :: st.stack })
  | .dconst1 => .inl (some { st with pc := st.pc + 1, stack := .f64 1.0 :: st.stack })
  | .ldcStr s => .inl (some { st with pc := st.pc + 1, stack := .str s :: st.stack })
  | .iload idx | .lload idx | .aload idx | .dload idx =>
    .inl (some { st with pc := st.pc + 1, stack := st.locals idx :: st.stack })
  | .istore idx | .lstore idx | .astore idx | .dstore idx =>
    match st.stack with
    | v :: rest => .inl (some { st with pc := st.pc + 1, stack := rest, locals := setLocal st.locals idx v })
    | _ => .inr none
  | .iinc idx delta =>
    let cur := (st.locals idx).asI32
    .inl (some { st with pc := st.pc + 1, locals := setLocal st.locals idx (.i32 (cur + delta.toUInt32)) })
  | .iadd =>
    match st.stack with
    | b :: a :: rest => .inl (some { st with pc := st.pc + 1, stack := .i32 (a.asI32 + b.asI32) :: rest })
    | _ => .inr none
  | .isub =>
    match st.stack with
    | b :: a :: rest => .inl (some { st with pc := st.pc + 1, stack := .i32 (a.asI32 - b.asI32) :: rest })
    | _ => .inr none
  | .imul =>
    match st.stack with
    | b :: a :: rest => .inl (some { st with pc := st.pc + 1, stack := .i32 (a.asI32 * b.asI32) :: rest })
    | _ => .inr none
  | .ineg =>
    match st.stack with
    | a :: rest => .inl (some { st with pc := st.pc + 1, stack := .i32 (-a.asI32) :: rest })
    | _ => .inr none
  | .iand =>
    match st.stack with
    | b :: a :: rest => .inl (some { st with pc := st.pc + 1, stack := .i32 (a.asI32 &&& b.asI32) :: rest })
    | _ => .inr none
  | .ior =>
    match st.stack with
    | b :: a :: rest => .inl (some { st with pc := st.pc + 1, stack := .i32 (a.asI32 ||| b.asI32) :: rest })
    | _ => .inr none
  | .ixor =>
    match st.stack with
    | b :: a :: rest => .inl (some { st with pc := st.pc + 1, stack := .i32 (a.asI32 ^^^ b.asI32) :: rest })
    | _ => .inr none
  | .ishl =>
    match st.stack with
    | b :: a :: rest => .inl (some { st with pc := st.pc + 1, stack := .i32 (a.asI32 <<< (b.asI32 &&& 31)) :: rest })
    | _ => .inr none
  | .ishr =>
    match st.stack with
    | b :: a :: rest =>
      let res := a.asI32.toBitVec.sshiftRight (b.asI32 &&& 31).toNat
      .inl (some { st with pc := st.pc + 1, stack := .i32 (UInt32.ofBitVec res) :: rest })
    | _ => .inr none
  | .iushr =>
    match st.stack with
    | b :: a :: rest => .inl (some { st with pc := st.pc + 1, stack := .i32 (a.asI32 >>> (b.asI32 &&& 31)) :: rest })
    | _ => .inr none
  | .ladd =>
    match st.stack with
    | b :: a :: rest => .inl (some { st with pc := st.pc + 1, stack := .i64 (a.asI64 + b.asI64) :: rest })
    | _ => .inr none
  | .lsub =>
    match st.stack with
    | b :: a :: rest => .inl (some { st with pc := st.pc + 1, stack := .i64 (a.asI64 - b.asI64) :: rest })
    | _ => .inr none
  | .lmul =>
    match st.stack with
    | b :: a :: rest => .inl (some { st with pc := st.pc + 1, stack := .i64 (a.asI64 * b.asI64) :: rest })
    | _ => .inr none
  | .land =>
    match st.stack with
    | b :: a :: rest => .inl (some { st with pc := st.pc + 1, stack := .i64 (a.asI64 &&& b.asI64) :: rest })
    | _ => .inr none
  | .lor =>
    match st.stack with
    | b :: a :: rest => .inl (some { st with pc := st.pc + 1, stack := .i64 (a.asI64 ||| b.asI64) :: rest })
    | _ => .inr none
  | .lxor =>
    match st.stack with
    | b :: a :: rest => .inl (some { st with pc := st.pc + 1, stack := .i64 (a.asI64 ^^^ b.asI64) :: rest })
    | _ => .inr none
  | .lshl =>
    match st.stack with
    | b :: a :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i64 (a.asI64 <<< (b.asI32 &&& 63).toUInt64) :: rest })
    | _ => .inr none
  | .lshr =>
    match st.stack with
    | b :: a :: rest =>
      let res := a.asI64.toBitVec.sshiftRight (b.asI32 &&& 63).toNat
      .inl (some { st with pc := st.pc + 1, stack := .i64 (UInt64.ofBitVec res) :: rest })
    | _ => .inr none
  | .lushr =>
    match st.stack with
    | b :: a :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i64 (a.asI64 >>> (b.asI32 &&& 63).toUInt64) :: rest })
    | _ => .inr none
  | .dadd =>
    match st.stack with
    | b :: a :: rest => .inl (some { st with pc := st.pc + 1, stack := .f64 (a.asF64 + b.asF64) :: rest })
    | _ => .inr none
  | .dsub =>
    match st.stack with
    | b :: a :: rest => .inl (some { st with pc := st.pc + 1, stack := .f64 (a.asF64 - b.asF64) :: rest })
    | _ => .inr none
  | .dmul =>
    match st.stack with
    | b :: a :: rest => .inl (some { st with pc := st.pc + 1, stack := .f64 (a.asF64 * b.asF64) :: rest })
    | _ => .inr none
  | .ddiv =>
    match st.stack with
    | b :: a :: rest => .inl (some { st with pc := st.pc + 1, stack := .f64 (a.asF64 / b.asF64) :: rest })
    | _ => .inr none
  | .dneg =>
    match st.stack with
    | a :: rest => .inl (some { st with pc := st.pc + 1, stack := .f64 (-a.asF64) :: rest })
    | _ => .inr none
  | .dcmpg =>
    match st.stack with
    | b :: a :: rest =>
      let res : UInt32 :=
        if a.asF64 < b.asF64 then 4294967295
        else if a.asF64 == b.asF64 then 0
        else 1
      .inl (some { st with pc := st.pc + 1, stack := .i32 res :: rest })
    | _ => .inr none
  | .dcmpl =>
    match st.stack with
    | b :: a :: rest =>
      let res : UInt32 :=
        if b.asF64 < a.asF64 then 1
        else if a.asF64 == b.asF64 then 0
        else 4294967295
      .inl (some { st with pc := st.pc + 1, stack := .i32 res :: rest })
    | _ => .inr none
  | .i2l =>
    match st.stack with
    | a :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i64 (UInt64.ofBitVec (a.asI32.toBitVec.signExtend 64)) :: rest })
    | _ => .inr none
  | .l2i =>
    match st.stack with
    | a :: rest => .inl (some { st with pc := st.pc + 1, stack := .i32 a.asI64.toUInt32 :: rest })
    | _ => .inr none
  | .i2b =>
    match st.stack with
    | a :: rest =>
      let res := UInt32.ofBitVec ((a.asI32.toBitVec.setWidth 8).signExtend 32)
      .inl (some { st with pc := st.pc + 1, stack := .i32 res :: rest })
    | _ => .inr none
  | .i2c =>
    match st.stack with
    | a :: rest => .inl (some { st with pc := st.pc + 1, stack := .i32 (a.asI32 &&& 0xFFFF) :: rest })
    | _ => .inr none
  | .i2d =>
    match st.stack with
    | a :: rest => .inl (some { st with pc := st.pc + 1, stack := .f64 (i32ToFloat a.asI32) :: rest })
    | _ => .inr none
  | .d2i =>
    match st.stack with
    | a :: rest => .inl (some { st with pc := st.pc + 1, stack := .i32 (floatToI32 a.asF64) :: rest })
    | _ => .inr none
  | .lcmp =>
    match st.stack with
    | b :: a :: rest =>
      let res : UInt32 :=
        if a.asI64 == b.asI64 then 0
        else if a.asI64.toBitVec.slt b.asI64.toBitVec then (4294967295 : UInt32)
        else 1
      .inl (some { st with pc := st.pc + 1, stack := .i32 res :: rest })
    | _ => .inr none
  | .goto target => .inl (some { st with pc := target })
  | .newClass cls =>
    if cls == "java/lang/StringBuilder" then
      let (addr, h') := st.jvmHeap.alloc (.stringBuilder "")
      .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: st.stack, jvmHeap := h' })
    else hooks.stepNewClass st cls
  | .newarray elemType => stepNewArray st elemType
  | .anewarray cls =>
    match st.stack with
    | lenVal :: rest =>
      if lenVal.asI32.toBitVec.slt 0#32 then .inr none
      else
        let (addr, h') := st.jvmHeap.alloc (.objArray cls (Array.replicate lenVal.asI32.toNat .null))
        .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
    | _ => .inr none
  | .arraylength =>
    match st.stack with
    | .heapRef addr :: rest =>
      match st.jvmHeap.get? addr >>= HeapObj.arrayLength? with
      | some len => .inl (some { st with pc := st.pc + 1, stack := .i32 (UInt32.ofNat len) :: rest })
      | none => .inr none
    | .strArr xs :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 (UInt32.ofNat xs.size) :: rest })
    | _ => .inr none
  | .aaload => stepArrayLoad st 0
  | .baload => stepArrayLoad st 1
  | .caload => stepArrayLoad st 2
  | .iaload => stepArrayLoad st 3
  | .laload => stepArrayLoad st 4
  | .daload => stepArrayLoad st 5
  | .aastore => stepArrayStore st 0
  | .bastore => stepArrayStore st 1
  | .castore => stepArrayStore st 2
  | .iastore => stepArrayStore st 3
  | .lastore => stepArrayStore st 4
  | .dastore => stepArrayStore st 5
  | .checkcast cls =>
    match st.stack with
    | v :: rest =>
      match v with
      | .heapRef addr =>
        match st.jvmHeap.checkCast cls addr with
        | some v' => .inl (some { st with pc := st.pc + 1, stack := v' :: rest })
        | none =>
          match st.jvmHeap.get? addr with
          | some (.instance objCls _) =>
            if hooks.isSubtypeOf objCls cls then .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest })
            else .inr none
          | _ => .inr none
      | .null => .inl (some { st with pc := st.pc + 1, stack := .null :: rest })
      | .str _ =>
        if cls == "java/lang/String" || cls == "java/lang/CharSequence" ||
            cls == "java/lang/Object" || cls == "java/io/Serializable" || cls == "java/lang/Comparable" then
          .inl (some { st with pc := st.pc + 1, stack := v :: rest })
        else .inr none
      | .strArr _ =>
        if cls == "[Ljava/lang/String;" || cls == "[Ljava/lang/Object;" || cls == "java/lang/Object" then
          .inl (some { st with pc := st.pc + 1, stack := v :: rest })
        else .inr none
      | _ =>
        match hooks.checkCast cls v with
        | some v' => .inl (some { st with pc := st.pc + 1, stack := v' :: rest })
        | none => .inr none
    | _ => .inr none
  | .instanceof cls =>
    match st.stack with
    | v :: rest =>
      let res :=
        match v with
        | .heapRef addr =>
          st.jvmHeap.checkInstanceOf cls addr ||
            match st.jvmHeap.get? addr with
            | some (.instance objCls _) => hooks.isSubtypeOf objCls cls
            | _ => false
        | _ => hooks.checkInstanceOf cls v
      .inl (some { st with pc := st.pc + 1, stack := .i32 (if res then 1 else 0) :: rest })
    | _ => .inr none
  | .invokevirtual cls method desc => stepInvokeVirtualGeneric hooks st cls method desc
  | .invokespecial cls method desc => stepInvokeSpecialGeneric hooks st cls method desc
  | .invokestatic cls method desc => stepInvokeStaticGeneric hooks st cls method desc
  | .invokeinterface cls method desc => hooks.stepInvokeInterface st cls method desc
  | .invokedynamic bsmKind bsmArg desc =>
    if bsmKind == "makeConcatWithConstants" then
      match evalMakeConcatWithConstants bsmArg desc st.stack with
      | some (s, rest) => .inl (some { st with pc := st.pc + 1, stack := .str s :: rest })
      | none => .inr none
    else hooks.stepInvokeDynamic st bsmKind bsmArg desc
  | .getfield cls field desc =>
    match st.stack with
    | .heapRef addr :: rest =>
      match st.jvmHeap.get? addr >>= (·.getField? field) with
      | some v => .inl (some { st with pc := st.pc + 1, stack := v :: rest })
      | none => hooks.stepGetField st cls field desc
    | _ => hooks.stepGetField st cls field desc
  | .putfield cls field desc =>
    match st.stack with
    | v :: .heapRef addr :: rest =>
      match st.jvmHeap.get? addr >>= (·.setField field v) with
      | some obj' =>
        let h' := st.jvmHeap.set addr obj'
        .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
      | none => hooks.stepPutField st cls field desc
    | _ => hooks.stepPutField st cls field desc
  | .getstatic cls field desc =>
    match st.jvmHeap.getStatic? cls field with
    | some v => .inl (some { st with pc := st.pc + 1, stack := v :: st.stack })
    | none =>
      match hooks.resolveStatic st cls field desc with
      | some v => .inl (some { st with pc := st.pc + 1, stack := v :: st.stack })
      | none => .inr none
  | .putstatic cls field desc =>
    match st.stack with
    | v :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := st.jvmHeap.setStatic cls field v })
    | _ => hooks.stepPutStatic st cls field desc
  | .ireturn =>
    match st.stack with
    | v :: _ => .inr (some (hooks.ireturnVal v))
    | _ => .inr none
  | .lreturn | .areturn | .dreturn =>
    match st.stack with
    | v :: _ => .inr (some v)
    | _ => .inr none
  | .vreturn => .inr (some .unit)
  | _ => .inr none

theorem stepInstr_aaload {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    {pc : Nat} {idx : UInt32} {addr : Nat} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    {cls : String} {elems : Array (JvmVal Ext)}
    (hget : jh.get? addr = some (.objArray cls elems))
    (hslt : idx.toBitVec.slt 0#32 = false)
    (hlt : idx.toNat < elems.size) :
    stepInstr hooks .aaload ⟨pc, .i32 idx :: .heapRef addr :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, elems[idx.toNat] :: stkRest, locs, jh, hp⟩) := by
  simp [stepInstr, stepArrayLoad, JvmVal.asI32, hget, hslt, hlt]

theorem stepInstr_baload {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    {pc : Nat} {idx : UInt32} {addr : Nat} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    {elems : Array UInt8}
    (hget : jh.get? addr = some (.byteArray elems))
    (hslt : idx.toBitVec.slt 0#32 = false)
    (hlt : idx.toNat < elems.size) :
    stepInstr hooks .baload ⟨pc, .i32 idx :: .heapRef addr :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 (UInt32.ofBitVec (elems[idx.toNat].toBitVec.signExtend 32)) :: stkRest,
        locs, jh, hp⟩) := by
  simp [stepInstr, stepArrayLoad, JvmVal.asI32, hget, hslt, hlt]

theorem stepInstr_bastore {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    {pc : Nat} {v idx : UInt32} {addr : Nat} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    {elems : Array UInt8}
    (hget : jh.get? addr = some (.byteArray elems))
    (hslt : idx.toBitVec.slt 0#32 = false)
    (hlt : idx.toNat < elems.size) :
    stepInstr hooks .bastore ⟨pc, .i32 v :: .i32 idx :: .heapRef addr :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, stkRest, locs, jh.set addr (.byteArray (elems.set idx.toNat v.toUInt8 hlt)), hp⟩) := by
  simp [stepInstr, stepArrayStore, JvmVal.asI32, hget, hslt, hlt]

theorem stepInstr_aastore {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    {pc : Nat} {v : JvmVal Ext} {idx : UInt32} {addr : Nat} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    {cls : String} {elems : Array (JvmVal Ext)}
    (hget : jh.get? addr = some (.objArray cls elems))
    (hslt : idx.toBitVec.slt 0#32 = false)
    (hlt : idx.toNat < elems.size) :
    stepInstr hooks .aastore ⟨pc, v :: .i32 idx :: .heapRef addr :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, stkRest, locs, jh.set addr (.objArray cls (elems.set idx.toNat v hlt)), hp⟩) := by
  simp [stepInstr, stepArrayStore, JvmVal.asI32, hget, hslt, hlt]

theorem stepInstr_newarray_byte {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    {pc : Nat} {n : UInt32} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    (hslt : n.toBitVec.slt 0#32 = false) :
    stepInstr hooks (.newarray "byte") ⟨pc, .i32 n :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .heapRef jh.objects.size :: stkRest, locs,
        (jh.alloc (.byteArray (Array.replicate n.toNat 0))).2, hp⟩) := by
  simp [stepInstr, stepNewArray, JvmVal.asI32, hslt, JvmHeap.alloc]

theorem stepInstr_anewarray {Ext Heap : Type} (hooks : JvmHooks Ext Heap) (cls : String)
    {pc : Nat} {n : UInt32} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    (hslt : n.toBitVec.slt 0#32 = false) :
    stepInstr hooks (.anewarray cls) ⟨pc, .i32 n :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .heapRef jh.objects.size :: stkRest, locs,
        (jh.alloc (.objArray cls (Array.replicate n.toNat .null))).2, hp⟩) := by
  simp [stepInstr, JvmVal.asI32, hslt, JvmHeap.alloc]

theorem stepInvokeStatic_arraysFillAll_obj {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    {pc : Nat} {handler elem : JvmVal Ext} {addr : Nat} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    {cls : String} {elems : Array (JvmVal Ext)} {desc : String}
    (hget : jh.get? addr = some (.objArray cls elems)) :
    stepInvokeStaticGeneric hooks
        ⟨pc, handler :: .i32 6 :: .i32 0 :: .i32 0 :: elem :: .heapRef addr :: stkRest, locs, jh, hp⟩
        "kotlin/collections/ArraysKt" "fill$default" desc =
      .inl (some ⟨pc + 1, stkRest, locs,
        jh.set addr (.objArray cls (Array.ofFn (n := elems.size) fun _ => elem)), hp⟩) := by
  simp +decide [stepInvokeStaticGeneric, stepFillRange, JvmVal.asI32, hget]

theorem stepInvokeStatic_uarraysFillAll_byte {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    {pc : Nat} {handler elem : JvmVal Ext} {addr : Nat} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    {elems : Array UInt8} {desc : String}
    (hget : jh.get? addr = some (.byteArray elems)) :
    stepInvokeStaticGeneric hooks
        ⟨pc, handler :: .i32 6 :: .i32 0 :: .i32 0 :: elem :: .heapRef addr :: stkRest, locs, jh, hp⟩
        "kotlin/collections/unsigned/UArraysKt" "fill-WpHrYlw$default" desc =
      .inl (some ⟨pc + 1, stkRest, locs,
        jh.set addr (.byteArray (Array.ofFn (n := elems.size) fun _ => elem.asI32.toUInt8)), hp⟩) := by
  simp +decide [stepInvokeStaticGeneric, stepFillRange, JvmVal.asI32, hget]

theorem stepInvokeStatic_arraysCopyOfRange_obj {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    {pc : Nat} {fromIdx toIdx : UInt32} {addr : Nat} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    {cls : String} {elems : Array (JvmVal Ext)} {desc : String}
    (hget : jh.get? addr = some (.objArray cls elems))
    (h1 : 0 ≤ fromIdx.toBitVec.toInt)
    (h2 : fromIdx.toBitVec.toInt ≤ toIdx.toBitVec.toInt)
    (h3 : toIdx.toBitVec.toInt ≤ elems.size) :
    stepInvokeStaticGeneric hooks
        ⟨pc, .i32 toIdx :: .i32 fromIdx :: .heapRef addr :: stkRest, locs, jh, hp⟩
        "kotlin/collections/ArraysKt" "copyOfRange" desc =
      let f := fromIdx.toBitVec.toInt.toNat
      let n := toIdx.toBitVec.toInt.toNat - f
      let sliced := Array.ofFn (n := n) (fun i => elems[f + i.val]!)
      .inl (some ⟨pc + 1, .heapRef jh.objects.size :: stkRest, locs, (jh.alloc (.objArray cls sliced)).2, hp⟩) := by
  have hn1 : ¬(fromIdx.toBitVec.toInt < 0) := by omega
  have hn2 : ¬(toIdx.toBitVec.toInt < fromIdx.toBitVec.toInt) := by omega
  have hn3 : ¬((elems.size : Int) < toIdx.toBitVec.toInt) := by omega
  simp [stepInvokeStaticGeneric, stepCopyOfRange, hget, JvmVal.asI32, hn1, hn2, hn3, JvmHeap.alloc]

theorem stepInvokeStatic_arraysCopyOfRange_byte {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    {pc : Nat} {fromIdx toIdx : UInt32} {addr : Nat} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    {elems : Array UInt8} {desc : String}
    (hget : jh.get? addr = some (.byteArray elems))
    (h1 : 0 ≤ fromIdx.toBitVec.toInt)
    (h2 : fromIdx.toBitVec.toInt ≤ toIdx.toBitVec.toInt)
    (h3 : toIdx.toBitVec.toInt ≤ elems.size) :
    stepInvokeStaticGeneric hooks
        ⟨pc, .i32 toIdx :: .i32 fromIdx :: .heapRef addr :: stkRest, locs, jh, hp⟩
        "kotlin/collections/ArraysKt" "copyOfRange" desc =
      let f := fromIdx.toBitVec.toInt.toNat
      let n := toIdx.toBitVec.toInt.toNat - f
      let sliced := Array.ofFn (n := n) (fun i => elems[f + i.val]!)
      .inl (some ⟨pc + 1, .heapRef jh.objects.size :: stkRest, locs, (jh.alloc (.byteArray sliced)).2, hp⟩) := by
  have hn1 : ¬(fromIdx.toBitVec.toInt < 0) := by omega
  have hn2 : ¬(toIdx.toBitVec.toInt < fromIdx.toBitVec.toInt) := by omega
  have hn3 : ¬((elems.size : Int) < toIdx.toBitVec.toInt) := by omega
  simp [stepInvokeStaticGeneric, stepCopyOfRange, hget, JvmVal.asI32, hn1, hn2, hn3, JvmHeap.alloc]

theorem stepInvokeStatic_stringsDecodeToString {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    {pc : Nat} {addr : Nat} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    {elems : Array UInt8} {s : String}
    (hget : jh.get? addr = some (.byteArray elems))
    (hutf8 : String.fromUTF8? ⟨elems⟩ = some s) :
    stepInvokeStaticGeneric hooks
        ⟨pc, .heapRef addr :: stkRest, locs, jh, hp⟩
        "kotlin/text/StringsKt" "decodeToString" "([B)Ljava/lang/String;" =
      .inl (some ⟨pc + 1, .str s :: stkRest, locs, jh, hp⟩) := by
  simp [stepInvokeStaticGeneric, hget, hutf8]

theorem stepInvokeStatic_ubyteArrayCtor {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    {pc : Nat} {n : UInt32} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    (hslt : n.toBitVec.slt 0#32 = false) :
    stepInvokeStaticGeneric hooks
        ⟨pc, .i32 n :: stkRest, locs, jh, hp⟩
        "kotlin/UByteArray" "constructor-impl" "(I)[B" =
      .inl (some ⟨pc + 1, .heapRef jh.objects.size :: stkRest, locs,
        (jh.alloc (.byteArray (Array.replicate n.toNat 0))).2, hp⟩) := by
  simp [stepInvokeStaticGeneric, JvmVal.asI32, hslt, JvmHeap.alloc]

theorem stepInvokeStatic_ubyteArrayGetSize {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    {pc : Nat} {addr : Nat} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap} {elems : Array UInt8}
    (hget : jh.get? addr = some (.byteArray elems)) :
    stepInvokeStaticGeneric hooks
        ⟨pc, .heapRef addr :: stkRest, locs, jh, hp⟩
        "kotlin/UByteArray" "getSize-impl" "([B)I" =
      .inl (some ⟨pc + 1, .i32 (UInt32.ofNat elems.size) :: stkRest, locs, jh, hp⟩) := by
  simp [stepInvokeStaticGeneric, hget]

theorem stepInvokeStatic_ubyteArrayGet {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    {pc : Nat} {idx : UInt32} {addr : Nat} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap} {elems : Array UInt8}
    (hget : jh.get? addr = some (.byteArray elems))
    (hslt : idx.toBitVec.slt 0#32 = false)
    (hlt : idx.toNat < elems.size) :
    stepInvokeStaticGeneric hooks
        ⟨pc, .i32 idx :: .heapRef addr :: stkRest, locs, jh, hp⟩
        "kotlin/UByteArray" "get-w2LRezQ" "([BI)B" =
      .inl (some ⟨pc + 1, .i32 (UInt32.ofBitVec (elems[idx.toNat].toBitVec.signExtend 32)) :: stkRest,
        locs, jh, hp⟩) := by
  simp [stepInvokeStaticGeneric, JvmVal.asI32, hget, hslt, hlt]

def runJvm {Ext Heap : Type} (hooks : JvmHooks Ext Heap) :
    Nat → List JvmInstr → JvmState Ext Heap → Option (JvmVal Ext)
  | 0, _, _ => none
  | fuel + 1, prog, st =>
    match prog[st.pc]? with
    | none => none
    | some (.ifeq target) =>
      match st.stack with
      | v :: rest =>
        hooks.iteZero v
          (runJvm hooks fuel prog { st with pc := target, stack := rest })
          (runJvm hooks fuel prog { st with pc := st.pc + 1, stack := rest })
      | _ => none
    | some (.ifne target) =>
      match st.stack with
      | v :: rest =>
        hooks.iteNonZero v
          (runJvm hooks fuel prog { st with pc := target, stack := rest })
          (runJvm hooks fuel prog { st with pc := st.pc + 1, stack := rest })
      | _ => none
    | some (.iflt target) =>
      match st.stack with
      | v :: rest =>
        hooks.iteVal (v.asI32.toBitVec.slt 0#32)
          (runJvm hooks fuel prog { st with pc := target, stack := rest })
          (runJvm hooks fuel prog { st with pc := st.pc + 1, stack := rest })
      | _ => none
    | some (.ifle target) =>
      match st.stack with
      | v :: rest =>
        hooks.iteVal (v.asI32.toBitVec.sle 0#32)
          (runJvm hooks fuel prog { st with pc := target, stack := rest })
          (runJvm hooks fuel prog { st with pc := st.pc + 1, stack := rest })
      | _ => none
    | some (.ifgt target) =>
      match st.stack with
      | v :: rest =>
        hooks.iteVal ((0#32).slt v.asI32.toBitVec)
          (runJvm hooks fuel prog { st with pc := target, stack := rest })
          (runJvm hooks fuel prog { st with pc := st.pc + 1, stack := rest })
      | _ => none
    | some (.ifge target) =>
      match st.stack with
      | v :: rest =>
        hooks.iteVal ((0#32).sle v.asI32.toBitVec)
          (runJvm hooks fuel prog { st with pc := target, stack := rest })
          (runJvm hooks fuel prog { st with pc := st.pc + 1, stack := rest })
      | _ => none
    | some (.ifnull target) =>
      match st.stack with
      | v :: rest =>
        if v.isNull then runJvm hooks fuel prog { st with pc := target, stack := rest }
        else runJvm hooks fuel prog { st with pc := st.pc + 1, stack := rest }
      | _ => none
    | some (.ifnonnull target) =>
      match st.stack with
      | v :: rest =>
        if !v.isNull then runJvm hooks fuel prog { st with pc := target, stack := rest }
        else runJvm hooks fuel prog { st with pc := st.pc + 1, stack := rest }
      | _ => none
    | some (.if_icmpeq target) =>
      match st.stack with
      | b :: a :: rest =>
        hooks.iteVal (a.asI32 == b.asI32)
          (runJvm hooks fuel prog { st with pc := target, stack := rest })
          (runJvm hooks fuel prog { st with pc := st.pc + 1, stack := rest })
      | _ => none
    | some (.if_icmpne target) =>
      match st.stack with
      | b :: a :: rest =>
        hooks.iteVal (!(a.asI32 == b.asI32))
          (runJvm hooks fuel prog { st with pc := target, stack := rest })
          (runJvm hooks fuel prog { st with pc := st.pc + 1, stack := rest })
      | _ => none
    | some (.if_icmplt target) =>
      match st.stack with
      | b :: a :: rest =>
        hooks.iteVal (a.asI32.toBitVec.slt b.asI32.toBitVec)
          (runJvm hooks fuel prog { st with pc := target, stack := rest })
          (runJvm hooks fuel prog { st with pc := st.pc + 1, stack := rest })
      | _ => none
    | some (.if_icmpge target) =>
      match st.stack with
      | b :: a :: rest =>
        hooks.iteVal (b.asI32.toBitVec.sle a.asI32.toBitVec)
          (runJvm hooks fuel prog { st with pc := target, stack := rest })
          (runJvm hooks fuel prog { st with pc := st.pc + 1, stack := rest })
      | _ => none
    | some (.if_icmpgt target) =>
      match st.stack with
      | b :: a :: rest =>
        hooks.iteVal (b.asI32.toBitVec.slt a.asI32.toBitVec)
          (runJvm hooks fuel prog { st with pc := target, stack := rest })
          (runJvm hooks fuel prog { st with pc := st.pc + 1, stack := rest })
      | _ => none
    | some (.if_icmple target) =>
      match st.stack with
      | b :: a :: rest =>
        hooks.iteVal (a.asI32.toBitVec.sle b.asI32.toBitVec)
          (runJvm hooks fuel prog { st with pc := target, stack := rest })
          (runJvm hooks fuel prog { st with pc := st.pc + 1, stack := rest })
      | _ => none
    | some (.if_acmpeq target) =>
      match st.stack with
      | b :: a :: rest =>
        if JvmVal.refEq hooks.beqExt a b then runJvm hooks fuel prog { st with pc := target, stack := rest }
        else runJvm hooks fuel prog { st with pc := st.pc + 1, stack := rest }
      | _ => none
    | some (.if_acmpne target) =>
      match st.stack with
      | b :: a :: rest =>
        if !JvmVal.refEq hooks.beqExt a b then runJvm hooks fuel prog { st with pc := target, stack := rest }
        else runJvm hooks fuel prog { st with pc := st.pc + 1, stack := rest }
      | _ => none
    | some (.tableswitch low targets defaultTarget) =>
      match st.stack with
      | key :: rest =>
        let target := tableswitchTarget key.asI32 low targets defaultTarget
        runJvm hooks fuel prog { st with pc := target, stack := rest }
      | _ => none
    | some (.lookupswitch cases defaultTarget) =>
      match st.stack with
      | key :: rest =>
        let target := lookupswitchTarget key.asI32 cases defaultTarget
        runJvm hooks fuel prog { st with pc := target, stack := rest }
      | _ => none
    | some instr =>
      match stepInstr hooks instr st with
      | .inl (some st') => runJvm hooks fuel prog st'
      | .inl none => none
      | .inr res => res

def runJvmRes {Ext Heap : Type} (hooks : JvmHooks Ext Heap) :
    Nat → List JvmInstr → JvmState Ext Heap → Option (JvmVal Ext × JvmState Ext Heap)
  | 0, _, _ => none
  | fuel + 1, prog, st =>
    match prog[st.pc]? with
    | none => none
    | some (.ifeq target) =>
      match st.stack with
      | v :: rest =>
        if hooks.isZero v then runJvmRes hooks fuel prog { st with pc := target, stack := rest }
        else runJvmRes hooks fuel prog { st with pc := st.pc + 1, stack := rest }
      | _ => none
    | some (.ifne target) =>
      match st.stack with
      | v :: rest =>
        if !hooks.isZero v then runJvmRes hooks fuel prog { st with pc := target, stack := rest }
        else runJvmRes hooks fuel prog { st with pc := st.pc + 1, stack := rest }
      | _ => none
    | some (.iflt target) =>
      match st.stack with
      | v :: rest =>
        if v.asI32.toBitVec.slt 0#32 then runJvmRes hooks fuel prog { st with pc := target, stack := rest }
        else runJvmRes hooks fuel prog { st with pc := st.pc + 1, stack := rest }
      | _ => none
    | some (.ifle target) =>
      match st.stack with
      | v :: rest =>
        if v.asI32.toBitVec.sle 0#32 then runJvmRes hooks fuel prog { st with pc := target, stack := rest }
        else runJvmRes hooks fuel prog { st with pc := st.pc + 1, stack := rest }
      | _ => none
    | some (.ifgt target) =>
      match st.stack with
      | v :: rest =>
        if (0#32).slt v.asI32.toBitVec then runJvmRes hooks fuel prog { st with pc := target, stack := rest }
        else runJvmRes hooks fuel prog { st with pc := st.pc + 1, stack := rest }
      | _ => none
    | some (.ifge target) =>
      match st.stack with
      | v :: rest =>
        if (0#32).sle v.asI32.toBitVec then runJvmRes hooks fuel prog { st with pc := target, stack := rest }
        else runJvmRes hooks fuel prog { st with pc := st.pc + 1, stack := rest }
      | _ => none
    | some (.ifnull target) =>
      match st.stack with
      | v :: rest =>
        if v.isNull then runJvmRes hooks fuel prog { st with pc := target, stack := rest }
        else runJvmRes hooks fuel prog { st with pc := st.pc + 1, stack := rest }
      | _ => none
    | some (.ifnonnull target) =>
      match st.stack with
      | v :: rest =>
        if !v.isNull then runJvmRes hooks fuel prog { st with pc := target, stack := rest }
        else runJvmRes hooks fuel prog { st with pc := st.pc + 1, stack := rest }
      | _ => none
    | some (.if_icmpeq target) =>
      match st.stack with
      | b :: a :: rest =>
        if a.asI32 == b.asI32 then runJvmRes hooks fuel prog { st with pc := target, stack := rest }
        else runJvmRes hooks fuel prog { st with pc := st.pc + 1, stack := rest }
      | _ => none
    | some (.if_icmpne target) =>
      match st.stack with
      | b :: a :: rest =>
        if !(a.asI32 == b.asI32) then runJvmRes hooks fuel prog { st with pc := target, stack := rest }
        else runJvmRes hooks fuel prog { st with pc := st.pc + 1, stack := rest }
      | _ => none
    | some (.if_icmplt target) =>
      match st.stack with
      | b :: a :: rest =>
        if a.asI32.toBitVec.slt b.asI32.toBitVec then runJvmRes hooks fuel prog { st with pc := target, stack := rest }
        else runJvmRes hooks fuel prog { st with pc := st.pc + 1, stack := rest }
      | _ => none
    | some (.if_icmpge target) =>
      match st.stack with
      | b :: a :: rest =>
        if b.asI32.toBitVec.sle a.asI32.toBitVec then runJvmRes hooks fuel prog { st with pc := target, stack := rest }
        else runJvmRes hooks fuel prog { st with pc := st.pc + 1, stack := rest }
      | _ => none
    | some (.if_icmpgt target) =>
      match st.stack with
      | b :: a :: rest =>
        if b.asI32.toBitVec.slt a.asI32.toBitVec then runJvmRes hooks fuel prog { st with pc := target, stack := rest }
        else runJvmRes hooks fuel prog { st with pc := st.pc + 1, stack := rest }
      | _ => none
    | some (.if_icmple target) =>
      match st.stack with
      | b :: a :: rest =>
        if a.asI32.toBitVec.sle b.asI32.toBitVec then runJvmRes hooks fuel prog { st with pc := target, stack := rest }
        else runJvmRes hooks fuel prog { st with pc := st.pc + 1, stack := rest }
      | _ => none
    | some (.if_acmpeq target) =>
      match st.stack with
      | b :: a :: rest =>
        if JvmVal.refEq hooks.beqExt a b then runJvmRes hooks fuel prog { st with pc := target, stack := rest }
        else runJvmRes hooks fuel prog { st with pc := st.pc + 1, stack := rest }
      | _ => none
    | some (.if_acmpne target) =>
      match st.stack with
      | b :: a :: rest =>
        if !JvmVal.refEq hooks.beqExt a b then runJvmRes hooks fuel prog { st with pc := target, stack := rest }
        else runJvmRes hooks fuel prog { st with pc := st.pc + 1, stack := rest }
      | _ => none
    | some (.tableswitch low targets defaultTarget) =>
      match st.stack with
      | key :: rest =>
        let target := tableswitchTarget key.asI32 low targets defaultTarget
        runJvmRes hooks fuel prog { st with pc := target, stack := rest }
      | _ => none
    | some (.lookupswitch cases defaultTarget) =>
      match st.stack with
      | key :: rest =>
        let target := lookupswitchTarget key.asI32 cases defaultTarget
        runJvmRes hooks fuel prog { st with pc := target, stack := rest }
      | _ => none
    | some instr =>
      match stepInstr hooks instr st with
      | .inl (some st') => runJvmRes hooks fuel prog st'
      | .inl none => none
      | .inr (some res) => some (res, st)
      | .inr none => none

end Jvm
