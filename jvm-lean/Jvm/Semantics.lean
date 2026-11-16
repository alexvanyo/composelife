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
  | f32 (v : Float32)
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

/-- Category-2 (two-slot) computational types: `long` and `double`. `Unit.INSTANCE` and
uninitialized `new` results are ordinary one-slot references. -/
def JvmVal.isCat2 {Ext : Type} : JvmVal Ext → Bool
  | .i64 _ | .f64 _ => true
  | _ => false

def JvmVal.isRef {Ext : Type} : JvmVal Ext → Bool
  | .null | .str _ | .strArr _ | .allocRef _ | .heapRef _
  | .boxedBool _ | .boxedByte _ | .boxedUByte _
  | .boxedInt _ | .boxedUInt _ | .boxedLong _ | .boxedULong _
  | .pair _ _ | .ext _ => true
  | _ => false

def JvmVal.asI32? {Ext : Type} : JvmVal Ext → Option UInt32
  | .i32 v => some v
  | .bool b => some (if b then 1 else 0)
  | _ => none

def JvmVal.asI64? {Ext : Type} : JvmVal Ext → Option UInt64
  | .i64 v => some v
  | _ => none

def JvmVal.asF32? {Ext : Type} : JvmVal Ext → Option Float32
  | .f32 v => some v
  | _ => none

def JvmVal.asF64? {Ext : Type} : JvmVal Ext → Option Float
  | .f64 v => some v
  | _ => none

@[simp] theorem JvmVal.asI32?_i32 {Ext : Type} (v : UInt32) :
    (JvmVal.i32 v : JvmVal Ext).asI32? = some v := rfl

@[simp] theorem JvmVal.asI32?_bool {Ext : Type} (b : Bool) :
    (JvmVal.bool b : JvmVal Ext).asI32? = some (if b then 1 else 0) := rfl

@[simp] theorem JvmVal.asI64?_i64 {Ext : Type} (v : UInt64) :
    (JvmVal.i64 v : JvmVal Ext).asI64? = some v := rfl

@[simp] theorem JvmVal.asF32?_f32 {Ext : Type} (v : Float32) :
    (JvmVal.f32 v : JvmVal Ext).asF32? = some v := rfl

@[simp] theorem JvmVal.asF64?_f64 {Ext : Type} (v : Float) :
    (JvmVal.f64 v : JvmVal Ext).asF64? = some v := rfl

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
  | .f32 a, .f32 b => (a.isNaN && b.isNaN) || a.toBits == b.toBits
  | .f64 a, .f64 b => (a.isNaN && b.isNaN) || a.toBits == b.toBits
  | .str a, .str b => a == b
  | .pair a1 a2, .pair b1 b2 => beqVal beqExt a1 b1 && beqVal beqExt a2 b2
  | .heapRef a, .heapRef b => a == b
  | .ext a, .ext b => beqExt a b
  | _, _ => false

/-- Decidable reference identity for `if_acmpeq`/`if_acmpne`; `none` when identity cannot be decided soundly. -/
def JvmVal.refEq? {Ext : Type} (beqRefExt : Ext → Ext → Option Bool) :
    JvmVal Ext → JvmVal Ext → Option Bool
  | .null, .null => some true
  | .null, v => if v.isRef then some false else none
  | v, .null => if v.isRef then some false else none
  | .unit, .unit => some true
  | .heapRef a, .heapRef b => some (a == b)
  | .heapRef _, .str _ | .str _, .heapRef _
  | .heapRef _, .strArr _ | .strArr _, .heapRef _
  | .str _, .strArr _ | .strArr _, .str _ => some false
  | .ext a, .ext b => beqRefExt a b
  | _, _ => none

def defaultIteVal {Ext : Type} (c : Bool) (t e : Option (JvmVal Ext)) : Option (JvmVal Ext) :=
  match t, e with
  | some (.i32 vt), some (.i32 ve) => some (.i32 (if c then vt else ve))
  | some (.i64 vt), some (.i64 ve) => some (.i64 (if c then vt else ve))
  | some (.f32 vt), some (.f32 ve) => some (.f32 (if c then vt else ve))
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
  | floatArray (elems : Array Float32)
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
  | .floatArray elems => some elems.size
  | .doubleArray elems => some elems.size
  | .objArray _ elems => some elems.size
  | _ => none

def jvmArrayTypeName (elemCls : String) : String :=
  if elemCls.startsWith "[" then "[" ++ elemCls else "[L" ++ elemCls ++ ";"

private def extractObjArrayElemClass? (cls : String) : Option String :=
  if cls.startsWith "[L" && cls.endsWith ";" && cls.length ≥ 3 then
    some ((cls.drop 2).dropEnd 1).toString
  else none

def HeapObj.matchesType {Ext : Type} (isSubtypeOf : String → String → Bool := fun a b => a == b)
    (cls : String) : HeapObj Ext → Bool
  | .boolArray _ =>
    cls == "[Z" || cls == "java/lang/Object" || cls == "java/lang/Cloneable" || cls == "java/io/Serializable"
  | .byteArray _ =>
    cls == "[B" || cls == "java/lang/Object" || cls == "java/lang/Cloneable" || cls == "java/io/Serializable"
  | .charArray _ =>
    cls == "[C" || cls == "java/lang/Object" || cls == "java/lang/Cloneable" || cls == "java/io/Serializable"
  | .shortArray _ =>
    cls == "[S" || cls == "java/lang/Object" || cls == "java/lang/Cloneable" || cls == "java/io/Serializable"
  | .intArray _ =>
    cls == "[I" || cls == "java/lang/Object" || cls == "java/lang/Cloneable" || cls == "java/io/Serializable"
  | .longArray _ =>
    cls == "[J" || cls == "java/lang/Object" || cls == "java/lang/Cloneable" || cls == "java/io/Serializable"
  | .floatArray _ =>
    cls == "[F" || cls == "java/lang/Object" || cls == "java/lang/Cloneable" || cls == "java/io/Serializable"
  | .doubleArray _ =>
    cls == "[D" || cls == "java/lang/Object" || cls == "java/lang/Cloneable" || cls == "java/io/Serializable"
  | .objArray elemCls _ =>
    let arrCls := jvmArrayTypeName elemCls
    let elemSub :=
      match extractObjArrayElemClass? cls with
      | some supElem => elemCls == supElem || isSubtypeOf elemCls supElem
      | none => false
    cls == arrCls || elemSub || cls == "[Ljava/lang/Object;" || cls == "java/lang/Object" ||
      cls == "java/lang/Cloneable" || cls == "java/io/Serializable"
  | .stringBuilder _ =>
    cls == "java/lang/StringBuilder" || cls == "java/lang/CharSequence" || cls == "java/lang/Object" ||
      isSubtypeOf "java/lang/StringBuilder" cls
  | .instance objCls _ => cls == objCls || cls == "java/lang/Object" || isSubtypeOf objCls cls

def HeapObj.getField? {Ext : Type} (isSubtypeOf : String → String → Bool := fun a b => a == b)
    (owner field : String) : HeapObj Ext → Option (JvmVal Ext)
  | .instance objCls fields =>
    if objCls == owner || isSubtypeOf objCls owner then
      (fields.find? (fun (f, _) => f == field)).map Prod.snd
    else none
  | _ => none

def HeapObj.setField {Ext : Type} (isSubtypeOf : String → String → Bool := fun a b => a == b)
    (owner field : String) (v : JvmVal Ext) : HeapObj Ext → Option (HeapObj Ext)
  | .instance objCls fields =>
    if objCls == owner || isSubtypeOf objCls owner then
      some (.instance objCls ((field, v) :: fields.filter (fun (f, _) => f != field)))
    else none
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

/-- Whether the generic model knows `v.equals(_)`: everything except references to `.instance` heap objects,
whose `equals` may be overridden (data classes, collections), so address identity is not their `equals`, and
dangling references. -/
def JvmVal.equalsModeled {Ext : Type} (h : JvmHeap Ext) : JvmVal Ext → Bool
  | .heapRef addr =>
    match h.get? addr with
    | some (.instance _ _) => false
    | some _ => true
    | none => false
  | .pair a b => equalsModeled h a && equalsModeled h b
  | _ => true

def JvmHeap.checkInstanceOf {Ext : Type} (h : JvmHeap Ext)
    (cls : String) (addr : Nat) (isSubtypeOf : String → String → Bool := fun a b => a == b) : Bool :=
  match h.get? addr with
  | some obj => obj.matchesType isSubtypeOf cls
  | none => false

def JvmHeap.checkCast {Ext : Type} (h : JvmHeap Ext)
    (cls : String) (addr : Nat) (isSubtypeOf : String → String → Bool := fun a b => a == b) :
    Option (JvmVal Ext) :=
  if h.checkInstanceOf cls addr isSubtypeOf then some (.heapRef addr) else none

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

/-- A JVM `char` (UTF-16 code unit, low 16 bits of `v`) as a Lean `Char`, or `none` for a surrogate:
a lone surrogate has no Lean `String` representation, and `Char.ofNat` would silently map it to `'\0'`. -/
def utf16UnitToChar? (v : UInt32) : Option Char :=
  let u := v &&& 0xFFFF
  if 0xD800 ≤ u && u ≤ 0xDFFF then none else some (Char.ofNat u.toNat)

/-- Decodes UTF-16 code units (a JVM `char[]`) into Lean characters, combining surrogate pairs;
`none` on an unpaired surrogate, which a Lean `String` cannot represent. -/
def decodeUtf16? : List UInt16 → Option (List Char)
  | [] => some []
  | hi :: rest =>
    if 0xD800 ≤ hi && hi ≤ 0xDBFF then
      match rest with
      | lo :: rest' =>
        if 0xDC00 ≤ lo && lo ≤ 0xDFFF then
          (decodeUtf16? rest').map
            (Char.ofNat (0x10000 + (hi.toNat - 0xD800) * 0x400 + (lo.toNat - 0xDC00)) :: ·)
        else none
      | [] => none
    else if 0xDC00 ≤ hi && hi ≤ 0xDFFF then none
    else (decodeUtf16? rest).map (Char.ofNat hi.toNat :: ·)

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

def i64ToFloat (v : UInt64) : Float :=
  if v.toBitVec.slt 0#64 then -(Float.ofNat (-v).toNat)
  else Float.ofNat v.toNat

def floatToI64 (x : Float) : UInt64 :=
  if x.isNaN then 0
  else if x >= 9223372036854775808.0 then 0x7FFFFFFFFFFFFFFF
  else if x <= -9223372036854775808.0 then 0x8000000000000000
  else if x >= 0.0 then x.toUInt64
  else UInt64.ofNat (0x10000000000000000 - (-x).toUInt64.toNat)

def i32ToFloat32 (v : UInt32) : Float32 :=
  (i32ToFloat v).toFloat32

def float32ToI32 (x : Float32) : UInt32 :=
  floatToI32 x.toFloat

def float32ToI64 (x : Float32) : UInt64 :=
  floatToI64 x.toFloat

/-- JVM `l2f`: rounds the signed 64-bit value to the nearest `float` once (JLS §5.1.2). Going through
`double` first rounds twice and differs from the JVM, e.g. `(1L shl 60) + (1L shl 36) + 1` is
`0x5d800001` on the JVM but `0x5d800000` via `double`. -/
def i64ToFloat32 (v : UInt64) : Float32 :=
  if v.toBitVec.slt 0#64 then -(Float32.ofNat (-v).toNat)
  else Float32.ofNat v.toNat

def jvmI32Div (a b : UInt32) : Option UInt32 :=
  if b == 0 then none else some (UInt32.ofBitVec (a.toBitVec.sdiv b.toBitVec))

def jvmI32Rem (a b : UInt32) : Option UInt32 :=
  if b == 0 then none else some (UInt32.ofBitVec (a.toBitVec.srem b.toBitVec))

def jvmI64Div (a b : UInt64) : Option UInt64 :=
  if b == 0 then none else some (UInt64.ofBitVec (a.toBitVec.sdiv b.toBitVec))

def jvmI64Rem (a b : UInt64) : Option UInt64 :=
  if b == 0 then none else some (UInt64.ofBitVec (a.toBitVec.srem b.toBitVec))

def tableswitchTarget (key : UInt32) (low : Int32) (targets : List Nat) (defaultTarget : Nat) : Nat :=
  let offset := key.toBitVec.toInt - low.toInt
  if 0 ≤ offset ∧ offset < targets.length then targets[offset.toNat]! else defaultTarget

def lookupswitchTarget (key : UInt32) (cases : List (Int32 × Nat)) (defaultTarget : Nat) : Nat :=
  match cases.find? (fun (k, _) => k.toUInt32 == key) with
  | some (_, t) => t
  | none => defaultTarget

def defaultIsSubtypeOf (subCls supCls : String) : Bool :=
  subCls == supCls || supCls == "java/lang/Object" ||
  match subCls, supCls with
  | "java/util/ArrayList", "java/util/List" => true
  | "java/util/ArrayList", "java/util/Collection" => true
  | "java/util/ArrayList", "java/lang/Iterable" => true
  | "java/util/List", "java/util/Collection" => true
  | "java/util/List", "java/lang/Iterable" => true
  | "java/util/Set", "java/util/Collection" => true
  | "java/util/Set", "java/lang/Iterable" => true
  | "java/lang/String", "java/lang/CharSequence" => true
  | "java/lang/String", "java/io/Serializable" => true
  | "java/lang/String", "java/lang/Comparable" => true
  | "java/lang/StringBuilder", "java/lang/CharSequence" => true
  | "java/lang/StringBuilder", "java/io/Serializable" => true
  | "java/lang/Byte", "java/lang/Number" => true
  | "java/lang/Byte", "java/io/Serializable" => true
  | "java/lang/Byte", "java/lang/Comparable" => true
  | "java/lang/Boolean", "java/io/Serializable" => true
  | "java/lang/Boolean", "java/lang/Comparable" => true
  | "java/lang/Integer", "java/lang/Number" => true
  | "java/lang/Integer", "java/io/Serializable" => true
  | "java/lang/Integer", "java/lang/Comparable" => true
  | "java/lang/Long", "java/lang/Number" => true
  | "java/lang/Long", "java/io/Serializable" => true
  | "java/lang/Long", "java/lang/Comparable" => true
  | "java/lang/Number", "java/io/Serializable" => true
  | "[Ljava/lang/String;", "[Ljava/lang/Object;" => true
  | "[Ljava/lang/String;", "java/lang/Cloneable" => true
  | "[Ljava/lang/String;", "java/io/Serializable" => true
  | _, _ => false

def defaultCheckInstanceOf {Ext : Type} (extFn : String → Ext → Bool) (cls : String) (v : JvmVal Ext) : Bool :=
  match v with
  | .null | .unit | .uninit | .i32 _ | .i64 _ | .f32 _ | .f64 _ | .bool _ | .heapRef _ | .allocRef _ => false
  | .boxedBool _ => defaultIsSubtypeOf "java/lang/Boolean" cls
  | .boxedByte _ => defaultIsSubtypeOf "java/lang/Byte" cls
  | .boxedInt _ => defaultIsSubtypeOf "java/lang/Integer" cls
  | .boxedLong _ => defaultIsSubtypeOf "java/lang/Long" cls
  | .boxedUByte _ => cls == "kotlin/UByte" || cls == "java/lang/Object" || cls == "java/lang/Comparable"
  | .boxedUInt _ => cls == "kotlin/UInt" || cls == "java/lang/Object" || cls == "java/lang/Comparable"
  | .boxedULong _ => cls == "kotlin/ULong" || cls == "java/lang/Object" || cls == "java/lang/Comparable"
  | .pair _ _ => cls == "kotlin/Pair" || cls == "java/lang/Object" || cls == "java/io/Serializable"
  | .str _ => defaultIsSubtypeOf "java/lang/String" cls
  | .strArr _ => defaultIsSubtypeOf "[Ljava/lang/String;" cls
  | .ext e => extFn cls e

def defaultCheckCast {Ext : Type} (extFn : String → Ext → Option (JvmVal Ext))
    (cls : String) (v : JvmVal Ext) : Option (JvmVal Ext) :=
  match v with
  | .null => some .null
  | .ext e => extFn cls e
  | _ => if defaultCheckInstanceOf (fun _ _ => false) cls v then some v else none

/-- Domain extension hooks configuring per-module types, calls, and heap interactions. -/
structure JvmHooks (Ext Heap : Type) where
  beqExt : Ext → Ext → Bool := fun _ _ => false
  beqRefExt : Ext → Ext → Option Bool := fun _ _ => none
  iteVal : Bool → Option (JvmVal Ext) → Option (JvmVal Ext) → Option (JvmVal Ext) := defaultIteVal
  isZero? : JvmVal Ext → Option Bool := fun v => v.asI32?.map (· == 0)
  iteZero? : JvmVal Ext → Option (JvmVal Ext) → Option (JvmVal Ext) → Option (JvmVal Ext) :=
    fun v jump fall => match v.asI32? with | some x => defaultIteVal (x == 0) jump fall | none => none
  iteNonZero? : JvmVal Ext → Option (JvmVal Ext) → Option (JvmVal Ext) → Option (JvmVal Ext) :=
    fun v jump fall => match v.asI32? with | some x => defaultIteVal (!(x == 0)) jump fall | none => none
  ireturnVal : JvmVal Ext → JvmVal Ext := id
  stepNewClass : JvmState Ext Heap → String → Option (JvmState Ext Heap) ⊕ Option (JvmVal Ext) :=
    fun st cls => .inl (some { st with pc := st.pc + 1, stack := .allocRef cls :: st.stack })
  checkInstanceOf : String → JvmVal Ext → Bool := defaultCheckInstanceOf (fun _ _ => false)
  checkCast : String → JvmVal Ext → Option (JvmVal Ext) := defaultCheckCast (fun _ _ => none)
  isSubtypeOf : String → String → Bool := defaultIsSubtypeOf
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

def formatConcatArg {Ext : Type} (tag : Char) (v : JvmVal Ext) : Option String :=
  match tag with
  | 'I' | 'B' | 'S' => v.asI32?.map i32ToDecimalString
  | 'J' => v.asI64?.map i64ToDecimalString
  | 'C' => v.asI32? >>= utf16UnitToChar? |>.map String.singleton
  | 'Z' => v.asI32?.map fun x => if x != 0 then "true" else "false"
  | 'D' | 'F' => none
  | _ =>
    match v with
    | .str s => some s
    | .null => some "null"
    | .boxedInt n => some (i32ToDecimalString n)
    | .boxedLong n => some (i64ToDecimalString n)
    | .boxedByte n => some (i32ToDecimalString (UInt32.ofBitVec ((n.toBitVec.setWidth 8).signExtend 32)))
    | .boxedUByte n => some (Nat.repr (n &&& 0xFF).toNat)
    | .boxedUInt n => some (Nat.repr n.toNat)
    | .boxedULong n => some (Nat.repr n.toNat)
    | .boxedBool b => some (if b then "true" else "false")
    | .i32 n => some (i32ToDecimalString n)
    | .i64 n => some (i64ToDecimalString n)
    | _ => none

private def interpConcatRecipeAux {Ext : Type} : List Char → List (Char × JvmVal Ext) → Option String
  | [], [] => some ""
  | [], _ :: _ => none
  | c :: cs, tagged =>
    -- `\u0002` splices a bootstrap-method constant, which the lifted recipe does not carry: fail closed.
    if c.toNat == 2 then none
    else if c.toNat == 1 then
      match tagged with
      | (tag, v) :: tRest =>
        match formatConcatArg tag v, interpConcatRecipeAux cs tRest with
        | some s1, some s2 => some (s1 ++ s2)
        | _, _ => none
      | [] => none
    else
      match interpConcatRecipeAux cs tagged with
      | some s2 => some (String.singleton c ++ s2)
      | none => none

def evalMakeConcatWithConstants {Ext : Type} (recipe desc : String)
    (stack : List (JvmVal Ext)) : Option (String × List (JvmVal Ext)) :=
  let tags := parseMethodParamTags desc
  let n := tags.length
  if stack.length < n then none
  else
    let args := (stack.take n).reverse
    let rest := stack.drop n
    match interpConcatRecipeAux recipe.toList (tags.zip args) with
    | some s => some (s, rest)
    | none => none

def evalInstanceOf {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    (jh : JvmHeap Ext) (cls : String) (v : JvmVal Ext) : Bool :=
  match v with
  | .null => false
  | .heapRef addr => jh.checkInstanceOf cls addr hooks.isSubtypeOf
  | _ => hooks.checkInstanceOf cls v

def evalCheckCast {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    (jh : JvmHeap Ext) (cls : String) (v : JvmVal Ext) : Option (JvmVal Ext) :=
  match v with
  | .null => some .null
  | .heapRef addr => jh.checkCast cls addr hooks.isSubtypeOf
  | _ => hooks.checkCast cls v

def isArrayElemCompat {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    (jh : JvmHeap Ext) (elemCls : String) (v : JvmVal Ext) : Bool :=
  match v with
  | .null => true
  | _ =>
    if elemCls == "java/lang/Object" then v.isRef
    else evalInstanceOf hooks jh elemCls v

def dedupJvmVals {Ext : Type} (beq : JvmVal Ext → JvmVal Ext → Bool)
    (xs : List (JvmVal Ext)) : List (JvmVal Ext) :=
  xs.foldl (fun acc x => if acc.any (fun y => beq x y) then acc else acc ++ [x]) []

def extractListArray? {Ext : Type} (h : JvmHeap Ext) (addr : Nat) : Option (Array (JvmVal Ext)) :=
  match h.get? addr with
  | some (.instance cls fields) =>
    if cls == "java/util/List" || cls == "java/util/ArrayList" || cls == "java/util/Set" then
      match (fields.find? (fun (f, _) => f == "arr")).map Prod.snd with
      | some (.heapRef arrAddr) =>
        match h.get? arrAddr with
        | some (.objArray _ elems) => some elems
        | _ => none
      | _ => none
    else none
  | _ => none

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

private def stepFillRange {Ext Heap : Type} (hooks : JvmHooks Ext Heap) (st : JvmState Ext Heap)
    (addr : Nat) (elem fromVal toVal maskVal : JvmVal Ext) (rest : List (JvmVal Ext)) :
    Option (JvmState Ext Heap) ⊕ Option (JvmVal Ext) :=
  match maskVal.asI32? with
  | none => .inr none
  | some mask =>
    let resolveBounds (size : Nat) : Option (Int × Int) :=
      let f? := if (mask &&& 2) != 0 then some (0 : Int) else fromVal.asI32?.map (·.toBitVec.toInt)
      let t? := if (mask &&& 4) != 0 then some (size : Int) else toVal.asI32?.map (·.toBitVec.toInt)
      match f?, t? with
      | some f, some t => if f < 0 || t < f || t > size then none else some (f, t)
      | _, _ => none
    match st.jvmHeap.get? addr with
    | some (.objArray cls elems) =>
      if !isArrayElemCompat hooks st.jvmHeap cls elem then .inr none
      else match resolveBounds elems.size with
        | none => .inr none
        | some (fromIdx, toIdx) =>
          let filled := Array.ofFn (n := elems.size) (fun i =>
            if fromIdx.toNat ≤ i.val && i.val < toIdx.toNat then elem else elems[i.val])
          let h' := st.jvmHeap.set addr (.objArray cls filled)
          .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
    | some (.byteArray elems) =>
      match resolveBounds elems.size, elem.asI32? with
      | some (fromIdx, toIdx), some ev =>
        let b := ev.toUInt8
        let filled := Array.ofFn (n := elems.size) (fun i =>
          if fromIdx.toNat ≤ i.val && i.val < toIdx.toNat then b else elems[i.val])
        let h' := st.jvmHeap.set addr (.byteArray filled)
        .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
      | _, _ => .inr none
    | some (.intArray elems) =>
      match resolveBounds elems.size, elem.asI32? with
      | some (fromIdx, toIdx), some v =>
        let filled := Array.ofFn (n := elems.size) (fun i =>
          if fromIdx.toNat ≤ i.val && i.val < toIdx.toNat then v else elems[i.val])
        let h' := st.jvmHeap.set addr (.intArray filled)
        .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
      | _, _ => .inr none
    | some (.longArray elems) =>
      match resolveBounds elems.size, elem.asI64? with
      | some (fromIdx, toIdx), some v =>
        let filled := Array.ofFn (n := elems.size) (fun i =>
          if fromIdx.toNat ≤ i.val && i.val < toIdx.toNat then v else elems[i.val])
        let h' := st.jvmHeap.set addr (.longArray filled)
        .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
      | _, _ => .inr none
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
    | "unbox-impl", .boxedUByte v :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 (UInt32.ofBitVec ((v.toBitVec.setWidth 8).signExtend 32)) :: rest })
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
        match arg with
        | .str str =>
          let h' := st.jvmHeap.set addr (.stringBuilder (buf ++ str))
          .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
        | .null =>
          let h' := st.jvmHeap.set addr (.stringBuilder (buf ++ "null"))
          .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
        | _ => .inr none
      | _ => .inr none
    | "append", "(I)Ljava/lang/StringBuilder;", arg :: .heapRef addr :: rest =>
      match st.jvmHeap.get? addr, arg.asI32? with
      | some (.stringBuilder buf), some v =>
        let h' := st.jvmHeap.set addr (.stringBuilder (buf ++ i32ToDecimalString v))
        .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
      | _, _ => .inr none
    | "append", "(C)Ljava/lang/StringBuilder;", arg :: .heapRef addr :: rest =>
      match st.jvmHeap.get? addr, arg.asI32? >>= utf16UnitToChar? with
      | some (.stringBuilder buf), some ch =>
        let h' := st.jvmHeap.set addr (.stringBuilder (buf ++ String.singleton ch))
        .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
      | _, _ => .inr none
    | "append", "(J)Ljava/lang/StringBuilder;", arg :: .heapRef addr :: rest =>
      match st.jvmHeap.get? addr, arg.asI64? with
      | some (.stringBuilder buf), some v =>
        let h' := st.jvmHeap.set addr (.stringBuilder (buf ++ i64ToDecimalString v))
        .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
      | _, _ => .inr none
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
      .inl (some { st with pc := st.pc + 1, stack := .allocRef "kotlin/NoWhenBranchMatchedException" :: rest })
    | _, _ => hooks.stepInvokeSpecial st cls method desc
  | "java/lang/IllegalArgumentException" =>
    match method, st.stack with
    | "<init>", _msg :: .allocRef "java/lang/IllegalArgumentException" :: .allocRef "java/lang/IllegalArgumentException" :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .allocRef "java/lang/IllegalArgumentException" :: rest })
    | "<init>", _msg :: .uninit :: .uninit :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .allocRef "java/lang/IllegalArgumentException" :: rest })
    | _, _ => hooks.stepInvokeSpecial st cls method desc
  | "java/lang/IllegalStateException" =>
    match method, st.stack with
    | "<init>", _msg :: .allocRef "java/lang/IllegalStateException" :: .allocRef "java/lang/IllegalStateException" :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .allocRef "java/lang/IllegalStateException" :: rest })
    | "<init>", _msg :: .uninit :: .uninit :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .allocRef "java/lang/IllegalStateException" :: rest })
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
  | "java/util/ArrayList" =>
    match method, desc, st.stack with
    | "<init>", "(I)V", capVal :: .allocRef "java/util/ArrayList" :: .allocRef "java/util/ArrayList" :: rest =>
      match capVal.asI32? with
      | some cap =>
        if cap.toBitVec.slt 0#32 then .inr none
        else
          let (arrAddr, h1) := st.jvmHeap.alloc (.objArray "java/lang/Object" #[])
          let (listAddr, h2) := h1.alloc (.instance "java/util/ArrayList" [("arr", .heapRef arrAddr)])
          .inl (some { st with pc := st.pc + 1, stack := .heapRef listAddr :: rest, jvmHeap := h2 })
      | none => .inr none
    | "<init>", "()V", .allocRef "java/util/ArrayList" :: .allocRef "java/util/ArrayList" :: rest =>
      let (arrAddr, h1) := st.jvmHeap.alloc (.objArray "java/lang/Object" #[])
      let (listAddr, h2) := h1.alloc (.instance "java/util/ArrayList" [("arr", .heapRef arrAddr)])
      .inl (some { st with pc := st.pc + 1, stack := .heapRef listAddr :: rest, jvmHeap := h2 })
    | _, _, _ => hooks.stepInvokeSpecial st cls method desc
  | _ => hooks.stepInvokeSpecial st cls method desc

def stepInvokeStaticGeneric {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    (st : JvmState Ext Heap) (cls method desc : String) : Option (JvmState Ext Heap) ⊕ Option (JvmVal Ext) :=
  match cls with
  | "kotlin/UInt" =>
    match method, desc, st.stack with
    | "constructor-impl", "(I)I", _ => .inl (some { st with pc := st.pc + 1 })
    | "box-impl", "(I)Lkotlin/UInt;", v :: rest =>
      match v.asI32? with
      | some x => .inl (some { st with pc := st.pc + 1, stack := .boxedUInt x :: rest })
      | none => .inr none
    | _, _, _ => hooks.stepInvokeStatic st cls method desc
  | "kotlin/ULong" =>
    match method, desc, st.stack with
    | "constructor-impl", "(J)J", _ => .inl (some { st with pc := st.pc + 1 })
    | "box-impl", "(J)Lkotlin/ULong;", v :: rest =>
      match v.asI64? with
      | some x => .inl (some { st with pc := st.pc + 1, stack := .boxedULong x :: rest })
      | none => .inr none
    | _, _, _ => hooks.stepInvokeStatic st cls method desc
  | "kotlin/UByte" =>
    match method, desc, st.stack with
    | "constructor-impl", "(B)B", _ => .inl (some { st with pc := st.pc + 1 })
    | "box-impl", "(B)Lkotlin/UByte;", v :: rest =>
      match v.asI32? with
      | some x => .inl (some { st with pc := st.pc + 1, stack := .boxedUByte (x &&& 0xFF) :: rest })
      | none => .inr none
    | _, _, _ => hooks.stepInvokeStatic st cls method desc
  | "kotlin/ULongArray" =>
    match method, desc with
    | "constructor-impl", "([J)[J" => .inl (some { st with pc := st.pc + 1 })
    | _, _ => hooks.stepInvokeStatic st cls method desc
  | "kotlin/jvm/internal/Intrinsics" =>
    match method, desc, st.stack with
    | "compare", "(II)I", b :: a :: rest =>
      match a.asI32?, b.asI32? with
      | some va, some vb =>
        let res : UInt32 := if va == vb then 0 else if va.toBitVec.slt vb.toBitVec then 4294967295 else 1
        .inl (some { st with pc := st.pc + 1, stack := .i32 res :: rest })
      | _, _ => .inr none
    | "areEqual", "(Ljava/lang/Object;Ljava/lang/Object;)Z", b :: a :: rest =>
      if a.equalsModeled st.jvmHeap && b.equalsModeled st.jvmHeap then
        .inl (some { st with pc := st.pc + 1, stack := .bool (JvmVal.beqVal hooks.beqExt a b) :: rest })
      else hooks.stepInvokeStatic st cls method desc
    | "checkNotNull", "(Ljava/lang/Object;Ljava/lang/String;)V", _msg :: obj :: rest
    | "checkNotNullParameter", "(Ljava/lang/Object;Ljava/lang/String;)V", _msg :: obj :: rest
    | "checkNotNullExpressionValue", "(Ljava/lang/Object;Ljava/lang/String;)V", _msg :: obj :: rest =>
      if obj.isNull then .inr none
      else .inl (some { st with pc := st.pc + 1, stack := rest })
    | _, _, _ => hooks.stepInvokeStatic st cls method desc
  | "java/lang/Integer" =>
    match method, desc, st.stack with
    | "valueOf", "(I)Ljava/lang/Integer;", v :: rest =>
      match v.asI32? with
      | some x => .inl (some { st with pc := st.pc + 1, stack := .boxedInt x :: rest })
      | none => .inr none
    | "compareUnsigned", "(II)I", b :: a :: rest =>
      match a.asI32?, b.asI32? with
      | some va, some vb =>
        let res : UInt32 := if va == vb then 0 else if va < vb then 4294967295 else 1
        .inl (some { st with pc := st.pc + 1, stack := .i32 res :: rest })
      | _, _ => .inr none
    | "divideUnsigned", "(II)I", b :: a :: rest =>
      match a.asI32?, b.asI32? with
      | some va, some vb =>
        if vb == 0 then .inr none
        else .inl (some { st with pc := st.pc + 1, stack := .i32 (va / vb) :: rest })
      | _, _ => .inr none
    | "remainderUnsigned", "(II)I", b :: a :: rest =>
      match a.asI32?, b.asI32? with
      | some va, some vb =>
        if vb == 0 then .inr none
        else .inl (some { st with pc := st.pc + 1, stack := .i32 (va % vb) :: rest })
      | _, _ => .inr none
    | "numberOfLeadingZeros", "(I)I", a :: rest =>
      match a.asI32? with
      | some va => .inl (some { st with pc := st.pc + 1, stack := .i32 (nlz32 va) :: rest })
      | none => .inr none
    | _, _, _ => hooks.stepInvokeStatic st cls method desc
  | "java/lang/Long" =>
    match method, desc, st.stack with
    | "compareUnsigned", "(JJ)I", b :: a :: rest =>
      match a.asI64?, b.asI64? with
      | some va, some vb =>
        let res : UInt32 := if va == vb then 0 else if va < vb then 4294967295 else 1
        .inl (some { st with pc := st.pc + 1, stack := .i32 res :: rest })
      | _, _ => .inr none
    | _, _, _ => hooks.stepInvokeStatic st cls method desc
  | "java/lang/Math" =>
    match method, desc, st.stack with
    | "abs", "(I)I", a :: rest =>
      match a.asI32? with
      | some va =>
        let res : UInt32 := if va.toBitVec.slt 0#32 then -va else va
        .inl (some { st with pc := st.pc + 1, stack := .i32 res :: rest })
      | none => .inr none
    | "max", "(II)I", b :: a :: rest =>
      match a.asI32?, b.asI32? with
      | some va, some vb =>
        let res : UInt32 := if va.toBitVec.slt vb.toBitVec then vb else va
        .inl (some { st with pc := st.pc + 1, stack := .i32 res :: rest })
      | _, _ => .inr none
    | _, _, _ => hooks.stepInvokeStatic st cls method desc
  | "kotlin/ranges/RangesKt" =>
    match method, desc, st.stack with
    | "coerceIn", "(III)I", hi :: lo :: v :: rest =>
      match v.asI32?, lo.asI32?, hi.asI32? with
      | some vv, some vlo, some vhi =>
        .inl (some { st with pc := st.pc + 1, stack := .i32 (coerceInI32 vv vlo vhi) :: rest })
      | _, _, _ => .inr none
    | _, _, _ => hooks.stepInvokeStatic st cls method desc
  | "kotlin/jvm/internal/TypeIntrinsics" =>
    match method, desc, st.stack with
    | "beforeCheckcastToFunctionOfArity", "(Ljava/lang/Object;I)Ljava/lang/Object;", arity :: fnObj :: rest =>
      -- Throws `ClassCastException` unless `fnObj` is null or a function of exactly this arity.
      match arity.asI32? with
      | some n =>
        if fnObj.isNull ||
            evalInstanceOf hooks st.jvmHeap ("kotlin/jvm/functions/Function" ++ toString n.toNat) fnObj then
          .inl (some { st with pc := st.pc + 1, stack := fnObj :: rest })
        else hooks.stepInvokeStatic st cls method desc
      | none => .inr none
    | _, _, _ => hooks.stepInvokeStatic st cls method desc
  | "kotlin/UByteArray" =>
    match method, desc, st.stack with
    | "constructor-impl", "(I)[B", sizeVal :: rest =>
      match sizeVal.asI32? with
      | some sz =>
        if sz.toBitVec.slt 0#32 then .inr none
        else
          let (addr, h') := st.jvmHeap.alloc (.byteArray (Array.replicate sz.toNat 0))
          .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
      | none => .inr none
    | "get-w2LRezQ", "([BI)B", idxVal :: .heapRef addr :: rest =>
      match idxVal.asI32? with
      | none => .inr none
      | some idx =>
        if idx.toBitVec.slt 0#32 then .inr none
        else match st.jvmHeap.get? addr with
          | some (.byteArray elems) =>
            if h : idx.toNat < elems.size then
              let b := UInt32.ofBitVec (elems[idx.toNat].toBitVec.signExtend 32)
              .inl (some { st with pc := st.pc + 1, stack := .i32 b :: rest })
            else .inr none
          | _ => .inr none
    | "set-VurrAj0", "([BIB)V", val :: idxVal :: .heapRef addr :: rest =>
      match idxVal.asI32?, val.asI32? with
      | some idx, some v =>
        if idx.toBitVec.slt 0#32 then .inr none
        else match st.jvmHeap.get? addr with
          | some (.byteArray elems) =>
            if h : idx.toNat < elems.size then
              let h' := st.jvmHeap.set addr (.byteArray (elems.set idx.toNat v.toUInt8 h))
              .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
            else .inr none
          | _ => .inr none
      | _, _ => .inr none
    | "getSize-impl", "([B)I", .heapRef addr :: rest =>
      match st.jvmHeap.get? addr with
      | some (.byteArray elems) =>
        .inl (some { st with pc := st.pc + 1, stack := .i32 (UInt32.ofNat elems.size) :: rest })
      | _ => .inr none
    | _, _, _ => hooks.stepInvokeStatic st cls method desc
  | "kotlin/UIntArray" =>
    match method, desc, st.stack with
    | "constructor-impl", "(I)[I", sizeVal :: rest =>
      match sizeVal.asI32? with
      | some sz =>
        if sz.toBitVec.slt 0#32 then .inr none
        else
          let (addr, h') := st.jvmHeap.alloc (.intArray (Array.replicate sz.toNat 0))
          .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
      | none => .inr none
    | "get-pVg5ArA", "([II)I", idxVal :: .heapRef addr :: rest =>
      match idxVal.asI32? with
      | none => .inr none
      | some idx =>
        if idx.toBitVec.slt 0#32 then .inr none
        else match st.jvmHeap.get? addr with
          | some (.intArray elems) =>
            if h : idx.toNat < elems.size then
              .inl (some { st with pc := st.pc + 1, stack := .i32 elems[idx.toNat] :: rest })
            else .inr none
          | _ => .inr none
    | "set-VXSXFK8", "([III)V", val :: idxVal :: .heapRef addr :: rest =>
      match idxVal.asI32?, val.asI32? with
      | some idx, some v =>
        if idx.toBitVec.slt 0#32 then .inr none
        else match st.jvmHeap.get? addr with
          | some (.intArray elems) =>
            if h : idx.toNat < elems.size then
              let h' := st.jvmHeap.set addr (.intArray (elems.set idx.toNat v h))
              .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
            else .inr none
          | _ => .inr none
      | _, _ => .inr none
    | "getSize-impl", "([I)I", .heapRef addr :: rest =>
      match st.jvmHeap.get? addr with
      | some (.intArray elems) =>
        .inl (some { st with pc := st.pc + 1, stack := .i32 (UInt32.ofNat elems.size) :: rest })
      | _ => .inr none
    | _, _, _ => hooks.stepInvokeStatic st cls method desc
  | "java/lang/Boolean" =>
    match method, desc, st.stack with
    | "valueOf", "(Z)Ljava/lang/Boolean;", v :: rest =>
      match v.asI32? with
      | some x => .inl (some { st with pc := st.pc + 1, stack := .boxedBool (x != 0) :: rest })
      | none => .inr none
    | _, _, _ => hooks.stepInvokeStatic st cls method desc
  | "java/lang/String" =>
    match method, desc, st.stack with
    | "valueOf", "(I)Ljava/lang/String;", v :: rest =>
      match v.asI32? with
      | some x => .inl (some { st with pc := st.pc + 1, stack := .str (i32ToDecimalString x) :: rest })
      | none => .inr none
    | _, _, _ => hooks.stepInvokeStatic st cls method desc
  | "java/util/Arrays" =>
    match method, desc, st.stack with
    | "copyOf", "([Ljava/lang/Object;I)[Ljava/lang/Object;", newLenVal :: .heapRef addr :: rest =>
      match newLenVal.asI32? with
      | none => .inr none
      | some newLen =>
        if newLen.toBitVec.slt 0#32 then .inr none
        else match st.jvmHeap.get? addr with
          | some (.objArray elemCls elems) =>
            let n := newLen.toNat
            let copied := Array.ofFn (n := n) (fun i => if h : i.val < elems.size then elems[i.val] else .null)
            let (newAddr, h') := st.jvmHeap.alloc (.objArray elemCls copied)
            .inl (some { st with pc := st.pc + 1, stack := .heapRef newAddr :: rest, jvmHeap := h' })
          | _ => .inr none
    | _, _, _ => hooks.stepInvokeStatic st cls method desc
  | "kotlin/collections/CollectionsKt" =>
    match method, desc, st.stack with
    | "listOf", "([Ljava/lang/Object;)Ljava/util/List;", .heapRef arrAddr :: rest =>
      match st.jvmHeap.get? arrAddr with
      | some (.objArray _ _) =>
        let (listAddr, h') := st.jvmHeap.alloc (.instance "java/util/List" [("arr", .heapRef arrAddr)])
        .inl (some { st with pc := st.pc + 1, stack := .heapRef listAddr :: rest, jvmHeap := h' })
      | _ => .inr none
    | "collectionSizeOrDefault", "(Ljava/lang/Iterable;I)I", _dflt :: .heapRef colAddr :: rest =>
      match extractListArray? st.jvmHeap colAddr with
      | some elems => .inl (some { st with pc := st.pc + 1, stack := .i32 (UInt32.ofNat elems.size) :: rest })
      | none => hooks.stepInvokeStatic st cls method desc
    | "toSet", "(Ljava/lang/Iterable;)Ljava/util/Set;", .heapRef colAddr :: rest =>
      match extractListArray? st.jvmHeap colAddr with
      | some elems =>
        if !elems.all (·.equalsModeled st.jvmHeap) then hooks.stepInvokeStatic st cls method desc else
        let dedup := (dedupJvmVals (JvmVal.beqVal hooks.beqExt) elems.toList).toArray
        let (arrAddr, h1) := st.jvmHeap.alloc (.objArray "java/lang/Object" dedup)
        let (setAddr, h2) := h1.alloc (.instance "java/util/Set" [("arr", .heapRef arrAddr)])
        .inl (some { st with pc := st.pc + 1, stack := .heapRef setAddr :: rest, jvmHeap := h2 })
      | none => hooks.stepInvokeStatic st cls method desc
    | _, _, _ => hooks.stepInvokeStatic st cls method desc
  | "kotlin/collections/ArraysKt" =>
    match method, st.stack with
    | "copyOfRange", toVal :: fromVal :: .heapRef addr :: rest =>
      match fromVal.asI32?, toVal.asI32? with
      | some f, some t => stepCopyOfRange st addr f.toBitVec.toInt t.toBitVec.toInt rest
      | _, _ => .inr none
    | "fill$default", _handler :: maskVal :: toVal :: fromVal :: elem :: .heapRef addr :: rest =>
      stepFillRange hooks st addr elem fromVal toVal maskVal rest
    | _, _ => hooks.stepInvokeStatic st cls method desc
  | "kotlin/collections/unsigned/UArraysKt" =>
    match method, st.stack with
    | "fill-WpHrYlw$default", _handler :: maskVal :: toVal :: fromVal :: elem :: .heapRef addr :: rest =>
      stepFillRange hooks st addr elem fromVal toVal maskVal rest
    | _, _ => hooks.stepInvokeStatic st cls method desc
  | "kotlin/text/StringsKt" =>
    match method, desc, st.stack with
    | "concatToString", "([C)Ljava/lang/String;", .heapRef addr :: rest =>
      match st.jvmHeap.get? addr with
      | some (.charArray elems) =>
        match decodeUtf16? elems.toList with
        | some cs => .inl (some { st with pc := st.pc + 1, stack := .str (String.ofList cs) :: rest })
        | none => .inr none
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

def stepInvokeInterfaceGeneric {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    (st : JvmState Ext Heap) (cls method desc : String) : Option (JvmState Ext Heap) ⊕ Option (JvmVal Ext) :=
  match cls, method, desc, st.stack with
  | "java/lang/Iterable", "iterator", "()Ljava/util/Iterator;", .heapRef colAddr :: rest =>
    match extractListArray? st.jvmHeap colAddr with
    | some _ =>
      match st.jvmHeap.get? colAddr with
      | some (.instance _ fields) =>
        match (fields.find? (fun (f, _) => f == "arr")).map Prod.snd with
        | some arrRef =>
          let (itAddr, h1) := st.jvmHeap.alloc (.instance "java/util/Iterator" [("arr", arrRef), ("idx", .i32 0)])
          .inl (some { st with pc := st.pc + 1, stack := .heapRef itAddr :: rest, jvmHeap := h1 })
        | none => .inr none
      | _ => .inr none
    | none => hooks.stepInvokeInterface st cls method desc
  | "java/util/Iterator", "hasNext", "()Z", .heapRef itAddr :: rest =>
    match st.jvmHeap.get? itAddr with
    | some (.instance "java/util/Iterator" fields) =>
      match (fields.find? (fun (f, _) => f == "arr")).map Prod.snd,
          (fields.find? (fun (f, _) => f == "idx")).map Prod.snd with
      | some (.heapRef arrAddr), some (.i32 idx) =>
        match st.jvmHeap.get? arrAddr with
        | some (.objArray _ elems) =>
          let has : UInt32 := if idx.toNat < elems.size then 1 else 0
          .inl (some { st with pc := st.pc + 1, stack := .i32 has :: rest })
        | _ => .inr none
      | _, _ => .inr none
    | _ => hooks.stepInvokeInterface st cls method desc
  | "java/util/Iterator", "next", "()Ljava/lang/Object;", .heapRef itAddr :: rest =>
    match st.jvmHeap.get? itAddr with
    | some (.instance "java/util/Iterator" fields) =>
      match (fields.find? (fun (f, _) => f == "arr")).map Prod.snd,
          (fields.find? (fun (f, _) => f == "idx")).map Prod.snd with
      | some (.heapRef arrAddr), some (.i32 idx) =>
        match st.jvmHeap.get? arrAddr with
        | some (.objArray _ elems) =>
          if h : idx.toNat < elems.size then
            let h1 := st.jvmHeap.set itAddr
              (.instance "java/util/Iterator" [("arr", .heapRef arrAddr), ("idx", .i32 (idx + 1))])
            .inl (some { st with pc := st.pc + 1, stack := elems[idx.toNat] :: rest, jvmHeap := h1 })
          else .inr none
        | _ => .inr none
      | _, _ => .inr none
    | _ => hooks.stepInvokeInterface st cls method desc
  | "java/util/Collection", "add", "(Ljava/lang/Object;)Z", elem :: .heapRef listAddr :: rest =>
    match st.jvmHeap.get? listAddr with
    | some (.instance "java/util/ArrayList" fields) =>
      match (fields.find? (fun (f, _) => f == "arr")).map Prod.snd with
      | some (.heapRef arrAddr) =>
        match st.jvmHeap.get? arrAddr with
        | some (.objArray arrCls elems) =>
          if isArrayElemCompat hooks st.jvmHeap arrCls elem then
            let h1 := st.jvmHeap.set arrAddr (.objArray arrCls (elems.push elem))
            .inl (some { st with pc := st.pc + 1, stack := .i32 1 :: rest, jvmHeap := h1 })
          else .inr none
        | _ => .inr none
      | _ => .inr none
    | _ => hooks.stepInvokeInterface st cls method desc
  | _, _, _, _ => hooks.stepInvokeInterface st cls method desc

private def stepNewArray {Ext Heap : Type} (st : JvmState Ext Heap) (elemType : String) :
    Option (JvmState Ext Heap) ⊕ Option (JvmVal Ext) :=
  match st.stack with
  | lenVal :: rest =>
    match lenVal.asI32? with
    | none => .inr none
    | some len =>
      if len.toBitVec.slt 0#32 then .inr none
      else
        let n := len.toNat
        let obj? : Option (HeapObj Ext) :=
          match elemType with
          | "boolean" => some (.boolArray (Array.replicate n false))
          | "byte" => some (.byteArray (Array.replicate n 0))
          | "char" => some (.charArray (Array.replicate n 0))
          | "short" => some (.shortArray (Array.replicate n 0))
          | "int" => some (.intArray (Array.replicate n 0))
          | "long" => some (.longArray (Array.replicate n 0))
          | "float" => some (.floatArray (Array.replicate n 0.0))
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
    match idxVal.asI32? with
    | none => .inr none
    | some idx =>
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
          | some (.shortArray elems), 6 =>
            if h : idx.toNat < elems.size then
              let v := UInt32.ofBitVec (elems[idx.toNat].toBitVec.signExtend 32)
              .inl (some { st with pc := st.pc + 1, stack := .i32 v :: rest })
            else .inr none
          | some (.floatArray elems), 7 =>
            if h : idx.toNat < elems.size then
              .inl (some { st with pc := st.pc + 1, stack := .f32 elems[idx.toNat] :: rest })
            else .inr none
          | _, _ => .inr none
        | .strArr xs =>
          if kind == 0 then
            if h : idx.toNat < xs.size then .inl (some { st with pc := st.pc + 1, stack := .str xs[idx.toNat] :: rest })
            else .inr none
          else .inr none
        | _ => .inr none
  | _ => .inr none

private def stepArrayStore {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    (st : JvmState Ext Heap) (kind : UInt8) :
    Option (JvmState Ext Heap) ⊕ Option (JvmVal Ext) :=
  match st.stack with
  | val :: idxVal :: .heapRef addr :: rest =>
    match idxVal.asI32? with
    | none => .inr none
    | some idx =>
      if idx.toBitVec.slt 0#32 then .inr none
      else match st.jvmHeap.get? addr, kind with
        | some (.objArray cls elems), 0 =>
          if isArrayElemCompat hooks st.jvmHeap cls val then
            if h : idx.toNat < elems.size then
              let h' := st.jvmHeap.set addr (.objArray cls (elems.set idx.toNat val h))
              .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
            else .inr none
          else .inr none
        | some (.byteArray elems), 1 =>
          match val.asI32? with
          | some v =>
            if h : idx.toNat < elems.size then
              let h' := st.jvmHeap.set addr (.byteArray (elems.set idx.toNat v.toUInt8 h))
              .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
            else .inr none
          | none => .inr none
        | some (.boolArray elems), 1 =>
          match val.asI32? with
          | some v =>
            if h : idx.toNat < elems.size then
              let h' := st.jvmHeap.set addr (.boolArray (elems.set idx.toNat ((v &&& 1) != 0) h))
              .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
            else .inr none
          | none => .inr none
        | some (.charArray elems), 2 =>
          match val.asI32? with
          | some v =>
            if h : idx.toNat < elems.size then
              let h' := st.jvmHeap.set addr (.charArray (elems.set idx.toNat v.toUInt16 h))
              .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
            else .inr none
          | none => .inr none
        | some (.intArray elems), 3 =>
          match val.asI32? with
          | some v =>
            if h : idx.toNat < elems.size then
              let h' := st.jvmHeap.set addr (.intArray (elems.set idx.toNat v h))
              .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
            else .inr none
          | none => .inr none
        | some (.longArray elems), 4 =>
          match val.asI64? with
          | some v =>
            if h : idx.toNat < elems.size then
              let h' := st.jvmHeap.set addr (.longArray (elems.set idx.toNat v h))
              .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
            else .inr none
          | none => .inr none
        | some (.doubleArray elems), 5 =>
          match val.asF64? with
          | some v =>
            if h : idx.toNat < elems.size then
              let h' := st.jvmHeap.set addr (.doubleArray (elems.set idx.toNat v h))
              .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
            else .inr none
          | none => .inr none
        | some (.shortArray elems), 6 =>
          match val.asI32? with
          | some v =>
            if h : idx.toNat < elems.size then
              let h' := st.jvmHeap.set addr (.shortArray (elems.set idx.toNat v.toUInt16 h))
              .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
            else .inr none
          | none => .inr none
        | some (.floatArray elems), 7 =>
          match val.asF32? with
          | some v =>
            if h : idx.toNat < elems.size then
              let h' := st.jvmHeap.set addr (.floatArray (elems.set idx.toNat v h))
              .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
            else .inr none
          | none => .inr none
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
    | a :: b :: rest =>
      if a.isCat2 || b.isCat2 then .inr none
      else .inl (some { st with pc := st.pc + 1, stack := b :: a :: rest })
    | _ => .inr none
  | .athrow => .inr none
  | .iconst v => .inl (some { st with pc := st.pc + 1, stack := .i32 v :: st.stack })
  | .lconst v => .inl (some { st with pc := st.pc + 1, stack := .i64 v :: st.stack })
  | .fconst bits => .inl (some { st with pc := st.pc + 1, stack := .f32 (Float32.ofBits bits) :: st.stack })
  | .dconst bits => .inl (some { st with pc := st.pc + 1, stack := .f64 (Float.ofBits bits) :: st.stack })
  | .dconst0 => .inl (some { st with pc := st.pc + 1, stack := .f64 0.0 :: st.stack })
  | .dconst1 => .inl (some { st with pc := st.pc + 1, stack := .f64 1.0 :: st.stack })
  | .ldcStr s => .inl (some { st with pc := st.pc + 1, stack := .str s :: st.stack })
  | .iload idx | .lload idx | .aload idx | .fload idx | .dload idx =>
    .inl (some { st with pc := st.pc + 1, stack := st.locals idx :: st.stack })
  | .istore idx | .lstore idx | .astore idx | .fstore idx | .dstore idx =>
    match st.stack with
    | v :: rest => .inl (some { st with pc := st.pc + 1, stack := rest, locals := setLocal st.locals idx v })
    | _ => .inr none
  | .iinc idx delta =>
    match (st.locals idx).asI32? with
    | some cur =>
      .inl (some { st with pc := st.pc + 1, locals := setLocal st.locals idx (.i32 (cur + delta.toUInt32)) })
    | none => .inr none
  | .iadd =>
    match st.stack with
    | b :: a :: rest =>
      match a.asI32?, b.asI32? with
      | some va, some vb => .inl (some { st with pc := st.pc + 1, stack := .i32 (va + vb) :: rest })
      | _, _ => .inr none
    | _ => .inr none
  | .isub =>
    match st.stack with
    | b :: a :: rest =>
      match a.asI32?, b.asI32? with
      | some va, some vb => .inl (some { st with pc := st.pc + 1, stack := .i32 (va - vb) :: rest })
      | _, _ => .inr none
    | _ => .inr none
  | .imul =>
    match st.stack with
    | b :: a :: rest =>
      match a.asI32?, b.asI32? with
      | some va, some vb => .inl (some { st with pc := st.pc + 1, stack := .i32 (va * vb) :: rest })
      | _, _ => .inr none
    | _ => .inr none
  | .idiv =>
    match st.stack with
    | b :: a :: rest =>
      match a.asI32?, b.asI32? with
      | some va, some vb =>
        match jvmI32Div va vb with
        | some res => .inl (some { st with pc := st.pc + 1, stack := .i32 res :: rest })
        | none => .inr none
      | _, _ => .inr none
    | _ => .inr none
  | .irem =>
    match st.stack with
    | b :: a :: rest =>
      match a.asI32?, b.asI32? with
      | some va, some vb =>
        match jvmI32Rem va vb with
        | some res => .inl (some { st with pc := st.pc + 1, stack := .i32 res :: rest })
        | none => .inr none
      | _, _ => .inr none
    | _ => .inr none
  | .ineg =>
    match st.stack with
    | a :: rest =>
      match a.asI32? with
      | some va => .inl (some { st with pc := st.pc + 1, stack := .i32 (-va) :: rest })
      | none => .inr none
    | _ => .inr none
  | .iand =>
    match st.stack with
    | b :: a :: rest =>
      match a.asI32?, b.asI32? with
      | some va, some vb => .inl (some { st with pc := st.pc + 1, stack := .i32 (va &&& vb) :: rest })
      | _, _ => .inr none
    | _ => .inr none
  | .ior =>
    match st.stack with
    | b :: a :: rest =>
      match a.asI32?, b.asI32? with
      | some va, some vb => .inl (some { st with pc := st.pc + 1, stack := .i32 (va ||| vb) :: rest })
      | _, _ => .inr none
    | _ => .inr none
  | .ixor =>
    match st.stack with
    | b :: a :: rest =>
      match a.asI32?, b.asI32? with
      | some va, some vb => .inl (some { st with pc := st.pc + 1, stack := .i32 (va ^^^ vb) :: rest })
      | _, _ => .inr none
    | _ => .inr none
  | .ishl =>
    match st.stack with
    | b :: a :: rest =>
      match a.asI32?, b.asI32? with
      | some va, some vb => .inl (some { st with pc := st.pc + 1, stack := .i32 (va <<< (vb &&& 31)) :: rest })
      | _, _ => .inr none
    | _ => .inr none
  | .ishr =>
    match st.stack with
    | b :: a :: rest =>
      match a.asI32?, b.asI32? with
      | some va, some vb =>
        let res := va.toBitVec.sshiftRight (vb &&& 31).toNat
        .inl (some { st with pc := st.pc + 1, stack := .i32 (UInt32.ofBitVec res) :: rest })
      | _, _ => .inr none
    | _ => .inr none
  | .iushr =>
    match st.stack with
    | b :: a :: rest =>
      match a.asI32?, b.asI32? with
      | some va, some vb => .inl (some { st with pc := st.pc + 1, stack := .i32 (va >>> (vb &&& 31)) :: rest })
      | _, _ => .inr none
    | _ => .inr none
  | .ladd =>
    match st.stack with
    | b :: a :: rest =>
      match a.asI64?, b.asI64? with
      | some va, some vb => .inl (some { st with pc := st.pc + 1, stack := .i64 (va + vb) :: rest })
      | _, _ => .inr none
    | _ => .inr none
  | .lsub =>
    match st.stack with
    | b :: a :: rest =>
      match a.asI64?, b.asI64? with
      | some va, some vb => .inl (some { st with pc := st.pc + 1, stack := .i64 (va - vb) :: rest })
      | _, _ => .inr none
    | _ => .inr none
  | .lmul =>
    match st.stack with
    | b :: a :: rest =>
      match a.asI64?, b.asI64? with
      | some va, some vb => .inl (some { st with pc := st.pc + 1, stack := .i64 (va * vb) :: rest })
      | _, _ => .inr none
    | _ => .inr none
  | .ldiv =>
    match st.stack with
    | b :: a :: rest =>
      match a.asI64?, b.asI64? with
      | some va, some vb =>
        match jvmI64Div va vb with
        | some res => .inl (some { st with pc := st.pc + 1, stack := .i64 res :: rest })
        | none => .inr none
      | _, _ => .inr none
    | _ => .inr none
  | .lrem =>
    match st.stack with
    | b :: a :: rest =>
      match a.asI64?, b.asI64? with
      | some va, some vb =>
        match jvmI64Rem va vb with
        | some res => .inl (some { st with pc := st.pc + 1, stack := .i64 res :: rest })
        | none => .inr none
      | _, _ => .inr none
    | _ => .inr none
  | .land =>
    match st.stack with
    | b :: a :: rest =>
      match a.asI64?, b.asI64? with
      | some va, some vb => .inl (some { st with pc := st.pc + 1, stack := .i64 (va &&& vb) :: rest })
      | _, _ => .inr none
    | _ => .inr none
  | .lor =>
    match st.stack with
    | b :: a :: rest =>
      match a.asI64?, b.asI64? with
      | some va, some vb => .inl (some { st with pc := st.pc + 1, stack := .i64 (va ||| vb) :: rest })
      | _, _ => .inr none
    | _ => .inr none
  | .lxor =>
    match st.stack with
    | b :: a :: rest =>
      match a.asI64?, b.asI64? with
      | some va, some vb => .inl (some { st with pc := st.pc + 1, stack := .i64 (va ^^^ vb) :: rest })
      | _, _ => .inr none
    | _ => .inr none
  | .lshl =>
    match st.stack with
    | b :: a :: rest =>
      match a.asI64?, b.asI32? with
      | some va, some vb => .inl (some { st with pc := st.pc + 1, stack := .i64 (va <<< (vb &&& 63).toUInt64) :: rest })
      | _, _ => .inr none
    | _ => .inr none
  | .lshr =>
    match st.stack with
    | b :: a :: rest =>
      match a.asI64?, b.asI32? with
      | some va, some vb =>
        let res := va.toBitVec.sshiftRight (vb &&& 63).toNat
        .inl (some { st with pc := st.pc + 1, stack := .i64 (UInt64.ofBitVec res) :: rest })
      | _, _ => .inr none
    | _ => .inr none
  | .lushr =>
    match st.stack with
    | b :: a :: rest =>
      match a.asI64?, b.asI32? with
      | some va, some vb => .inl (some { st with pc := st.pc + 1, stack := .i64 (va >>> (vb &&& 63).toUInt64) :: rest })
      | _, _ => .inr none
    | _ => .inr none
  | .fadd =>
    match st.stack with
    | b :: a :: rest =>
      match a.asF32?, b.asF32? with
      | some va, some vb => .inl (some { st with pc := st.pc + 1, stack := .f32 (va + vb) :: rest })
      | _, _ => .inr none
    | _ => .inr none
  | .fsub =>
    match st.stack with
    | b :: a :: rest =>
      match a.asF32?, b.asF32? with
      | some va, some vb => .inl (some { st with pc := st.pc + 1, stack := .f32 (va - vb) :: rest })
      | _, _ => .inr none
    | _ => .inr none
  | .fmul =>
    match st.stack with
    | b :: a :: rest =>
      match a.asF32?, b.asF32? with
      | some va, some vb => .inl (some { st with pc := st.pc + 1, stack := .f32 (va * vb) :: rest })
      | _, _ => .inr none
    | _ => .inr none
  | .fdiv =>
    match st.stack with
    | b :: a :: rest =>
      match a.asF32?, b.asF32? with
      | some va, some vb => .inl (some { st with pc := st.pc + 1, stack := .f32 (va / vb) :: rest })
      | _, _ => .inr none
    | _ => .inr none
  | .fneg =>
    match st.stack with
    | a :: rest =>
      match a.asF32? with
      | some va => .inl (some { st with pc := st.pc + 1, stack := .f32 (-va) :: rest })
      | none => .inr none
    | _ => .inr none
  | .fcmpg =>
    match st.stack with
    | b :: a :: rest =>
      match a.asF32?, b.asF32? with
      | some va, some vb =>
        let res : UInt32 :=
          if va < vb then 4294967295
          else if va == vb then 0
          else 1
        .inl (some { st with pc := st.pc + 1, stack := .i32 res :: rest })
      | _, _ => .inr none
    | _ => .inr none
  | .fcmpl =>
    match st.stack with
    | b :: a :: rest =>
      match a.asF32?, b.asF32? with
      | some va, some vb =>
        let res : UInt32 :=
          if vb < va then 1
          else if va == vb then 0
          else 4294967295
        .inl (some { st with pc := st.pc + 1, stack := .i32 res :: rest })
      | _, _ => .inr none
    | _ => .inr none
  | .dadd =>
    match st.stack with
    | b :: a :: rest =>
      match a.asF64?, b.asF64? with
      | some va, some vb => .inl (some { st with pc := st.pc + 1, stack := .f64 (va + vb) :: rest })
      | _, _ => .inr none
    | _ => .inr none
  | .dsub =>
    match st.stack with
    | b :: a :: rest =>
      match a.asF64?, b.asF64? with
      | some va, some vb => .inl (some { st with pc := st.pc + 1, stack := .f64 (va - vb) :: rest })
      | _, _ => .inr none
    | _ => .inr none
  | .dmul =>
    match st.stack with
    | b :: a :: rest =>
      match a.asF64?, b.asF64? with
      | some va, some vb => .inl (some { st with pc := st.pc + 1, stack := .f64 (va * vb) :: rest })
      | _, _ => .inr none
    | _ => .inr none
  | .ddiv =>
    match st.stack with
    | b :: a :: rest =>
      match a.asF64?, b.asF64? with
      | some va, some vb => .inl (some { st with pc := st.pc + 1, stack := .f64 (va / vb) :: rest })
      | _, _ => .inr none
    | _ => .inr none
  | .dneg =>
    match st.stack with
    | a :: rest =>
      match a.asF64? with
      | some va => .inl (some { st with pc := st.pc + 1, stack := .f64 (-va) :: rest })
      | none => .inr none
    | _ => .inr none
  | .dcmpg =>
    match st.stack with
    | b :: a :: rest =>
      match a.asF64?, b.asF64? with
      | some va, some vb =>
        let res : UInt32 :=
          if va < vb then 4294967295
          else if va == vb then 0
          else 1
        .inl (some { st with pc := st.pc + 1, stack := .i32 res :: rest })
      | _, _ => .inr none
    | _ => .inr none
  | .dcmpl =>
    match st.stack with
    | b :: a :: rest =>
      match a.asF64?, b.asF64? with
      | some va, some vb =>
        let res : UInt32 :=
          if vb < va then 1
          else if va == vb then 0
          else 4294967295
        .inl (some { st with pc := st.pc + 1, stack := .i32 res :: rest })
      | _, _ => .inr none
    | _ => .inr none
  | .i2l =>
    match st.stack with
    | a :: rest =>
      match a.asI32? with
      | some va =>
        .inl (some { st with pc := st.pc + 1, stack := .i64 (UInt64.ofBitVec (va.toBitVec.signExtend 64)) :: rest })
      | none => .inr none
    | _ => .inr none
  | .l2i =>
    match st.stack with
    | a :: rest =>
      match a.asI64? with
      | some va => .inl (some { st with pc := st.pc + 1, stack := .i32 va.toUInt32 :: rest })
      | none => .inr none
    | _ => .inr none
  | .i2b =>
    match st.stack with
    | a :: rest =>
      match a.asI32? with
      | some va =>
        let res := UInt32.ofBitVec ((va.toBitVec.setWidth 8).signExtend 32)
        .inl (some { st with pc := st.pc + 1, stack := .i32 res :: rest })
      | none => .inr none
    | _ => .inr none
  | .i2c =>
    match st.stack with
    | a :: rest =>
      match a.asI32? with
      | some va => .inl (some { st with pc := st.pc + 1, stack := .i32 (va &&& 0xFFFF) :: rest })
      | none => .inr none
    | _ => .inr none
  | .i2s =>
    match st.stack with
    | a :: rest =>
      match a.asI32? with
      | some va =>
        let res := UInt32.ofBitVec ((va.toBitVec.setWidth 16).signExtend 32)
        .inl (some { st with pc := st.pc + 1, stack := .i32 res :: rest })
      | none => .inr none
    | _ => .inr none
  | .i2f =>
    match st.stack with
    | a :: rest =>
      match a.asI32? with
      | some va => .inl (some { st with pc := st.pc + 1, stack := .f32 (i32ToFloat32 va) :: rest })
      | none => .inr none
    | _ => .inr none
  | .l2f =>
    match st.stack with
    | a :: rest =>
      match a.asI64? with
      | some va => .inl (some { st with pc := st.pc + 1, stack := .f32 (i64ToFloat32 va) :: rest })
      | none => .inr none
    | _ => .inr none
  | .f2i =>
    match st.stack with
    | a :: rest =>
      match a.asF32? with
      | some va => .inl (some { st with pc := st.pc + 1, stack := .i32 (float32ToI32 va) :: rest })
      | none => .inr none
    | _ => .inr none
  | .f2l =>
    match st.stack with
    | a :: rest =>
      match a.asF32? with
      | some va => .inl (some { st with pc := st.pc + 1, stack := .i64 (float32ToI64 va) :: rest })
      | none => .inr none
    | _ => .inr none
  | .i2d =>
    match st.stack with
    | a :: rest =>
      match a.asI32? with
      | some va => .inl (some { st with pc := st.pc + 1, stack := .f64 (i32ToFloat va) :: rest })
      | none => .inr none
    | _ => .inr none
  | .l2d =>
    match st.stack with
    | a :: rest =>
      match a.asI64? with
      | some va => .inl (some { st with pc := st.pc + 1, stack := .f64 (i64ToFloat va) :: rest })
      | none => .inr none
    | _ => .inr none
  | .d2i =>
    match st.stack with
    | a :: rest =>
      match a.asF64? with
      | some va => .inl (some { st with pc := st.pc + 1, stack := .i32 (floatToI32 va) :: rest })
      | none => .inr none
    | _ => .inr none
  | .d2l =>
    match st.stack with
    | a :: rest =>
      match a.asF64? with
      | some va => .inl (some { st with pc := st.pc + 1, stack := .i64 (floatToI64 va) :: rest })
      | none => .inr none
    | _ => .inr none
  | .f2d =>
    match st.stack with
    | a :: rest =>
      match a.asF32? with
      | some va => .inl (some { st with pc := st.pc + 1, stack := .f64 va.toFloat :: rest })
      | none => .inr none
    | _ => .inr none
  | .d2f =>
    match st.stack with
    | a :: rest =>
      match a.asF64? with
      | some va => .inl (some { st with pc := st.pc + 1, stack := .f32 va.toFloat32 :: rest })
      | none => .inr none
    | _ => .inr none
  | .lcmp =>
    match st.stack with
    | b :: a :: rest =>
      match a.asI64?, b.asI64? with
      | some va, some vb =>
        let res : UInt32 :=
          if va == vb then 0
          else if va.toBitVec.slt vb.toBitVec then (4294967295 : UInt32)
          else 1
        .inl (some { st with pc := st.pc + 1, stack := .i32 res :: rest })
      | _, _ => .inr none
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
      match lenVal.asI32? with
      | none => .inr none
      | some len =>
        if len.toBitVec.slt 0#32 then .inr none
        else
          let (addr, h') := st.jvmHeap.alloc (.objArray cls (Array.replicate len.toNat .null))
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
  | .saload => stepArrayLoad st 6
  | .faload => stepArrayLoad st 7
  | .aastore => stepArrayStore hooks st 0
  | .bastore => stepArrayStore hooks st 1
  | .castore => stepArrayStore hooks st 2
  | .iastore => stepArrayStore hooks st 3
  | .lastore => stepArrayStore hooks st 4
  | .dastore => stepArrayStore hooks st 5
  | .sastore => stepArrayStore hooks st 6
  | .fastore => stepArrayStore hooks st 7
  | .checkcast cls =>
    match st.stack with
    | v :: rest =>
      match evalCheckCast hooks st.jvmHeap cls v with
      | some v' => .inl (some { st with pc := st.pc + 1, stack := v' :: rest })
      | none => .inr none
    | _ => .inr none
  | .instanceof cls =>
    match st.stack with
    | v :: rest =>
      let res := evalInstanceOf hooks st.jvmHeap cls v
      .inl (some { st with pc := st.pc + 1, stack := .i32 (if res then 1 else 0) :: rest })
    | _ => .inr none
  | .invokevirtual cls method desc => stepInvokeVirtualGeneric hooks st cls method desc
  | .invokespecial cls method desc => stepInvokeSpecialGeneric hooks st cls method desc
  | .invokestatic cls method desc => stepInvokeStaticGeneric hooks st cls method desc
  | .invokeinterface cls method desc => stepInvokeInterfaceGeneric hooks st cls method desc
  | .invokedynamic bsmKind bsmArg desc =>
    if bsmKind == "makeConcatWithConstants" then
      match evalMakeConcatWithConstants bsmArg desc st.stack with
      | some (s, rest) => .inl (some { st with pc := st.pc + 1, stack := .str s :: rest })
      | none => .inr none
    else hooks.stepInvokeDynamic st bsmKind bsmArg desc
  | .getfield cls field desc =>
    match st.stack with
    | .heapRef addr :: rest =>
      match st.jvmHeap.get? addr with
      | some (.instance objCls fields) =>
        if objCls == cls || hooks.isSubtypeOf objCls cls then
          match (fields.find? (fun (f, _) => f == field)).map Prod.snd with
          | some v => .inl (some { st with pc := st.pc + 1, stack := v :: rest })
          | none => .inr none
        else .inr none
      | _ => hooks.stepGetField st cls field desc
    | _ => hooks.stepGetField st cls field desc
  | .putfield cls field desc =>
    match st.stack with
    | v :: .heapRef addr :: rest =>
      match st.jvmHeap.get? addr with
      | some obj@(.instance _objCls _) =>
        match obj.setField hooks.isSubtypeOf cls field v with
        | some obj' =>
          let h' := st.jvmHeap.set addr obj'
          .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
        | none => .inr none
      | _ => hooks.stepPutField st cls field desc
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
      match hooks.stepPutStatic st cls field desc with
      | .inl (some st') => .inl (some st')
      | .inl none => .inr none
      | .inr (some res) => .inr (some res)
      | .inr none =>
        .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := st.jvmHeap.setStatic cls field v })
    | _ => hooks.stepPutStatic st cls field desc
  | .ireturn =>
    match st.stack with
    | v :: _ => .inr (some (hooks.ireturnVal v))
    | _ => .inr none
  | .lreturn | .areturn | .freturn | .dreturn =>
    match st.stack with
    | v :: _ => .inr (some v)
    | _ => .inr none
  | .vreturn => .inr (some .unit)
  | _ => .inr none

/-- `Intrinsics.areEqual` on operands whose `equals` the generic model decides (`JvmVal.equalsModeled`). -/
theorem stepInstr_areEqual {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    {pc : Nat} {a b : JvmVal Ext} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    (ha : a.equalsModeled jh = true) (hb : b.equalsModeled jh = true) :
    stepInstr hooks
        (.invokestatic "kotlin/jvm/internal/Intrinsics" "areEqual" "(Ljava/lang/Object;Ljava/lang/Object;)Z")
        ⟨pc, b :: a :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .bool (JvmVal.beqVal hooks.beqExt a b) :: stkRest, locs, jh, hp⟩) := by
  have h : stepInstr hooks
        (.invokestatic "kotlin/jvm/internal/Intrinsics" "areEqual" "(Ljava/lang/Object;Ljava/lang/Object;)Z")
        ⟨pc, b :: a :: stkRest, locs, jh, hp⟩ =
      if (a.equalsModeled jh && b.equalsModeled jh) = true then
        .inl (some ⟨pc + 1, .bool (JvmVal.beqVal hooks.beqExt a b) :: stkRest, locs, jh, hp⟩)
      else hooks.stepInvokeStatic ⟨pc, b :: a :: stkRest, locs, jh, hp⟩
        "kotlin/jvm/internal/Intrinsics" "areEqual" "(Ljava/lang/Object;Ljava/lang/Object;)Z" := rfl
  rw [h, ha, hb]
  rfl

theorem stepInstr_aaload {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    {pc : Nat} {idx : UInt32} {addr : Nat} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    {cls : String} {elems : Array (JvmVal Ext)}
    (hget : jh.get? addr = some (.objArray cls elems))
    (hslt : idx.toBitVec.slt 0#32 = false)
    (hlt : idx.toNat < elems.size) :
    stepInstr hooks .aaload ⟨pc, .i32 idx :: .heapRef addr :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, elems[idx.toNat] :: stkRest, locs, jh, hp⟩) := by
  unfold stepInstr stepArrayLoad
  simp [hget, hslt, hlt]

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
  unfold stepInstr stepArrayLoad
  simp [hget, hslt, hlt]

theorem stepInstr_bastore {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    {pc : Nat} {v idx : UInt32} {addr : Nat} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    {elems : Array UInt8}
    (hget : jh.get? addr = some (.byteArray elems))
    (hslt : idx.toBitVec.slt 0#32 = false)
    (hlt : idx.toNat < elems.size) :
    stepInstr hooks .bastore ⟨pc, .i32 v :: .i32 idx :: .heapRef addr :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, stkRest, locs, jh.set addr (.byteArray (elems.set idx.toNat v.toUInt8 hlt)), hp⟩) := by
  unfold stepInstr stepArrayStore
  simp [hget, hslt, hlt]

theorem stepInstr_aastore {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    {pc : Nat} {v : JvmVal Ext} {idx : UInt32} {addr : Nat} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    {cls : String} {elems : Array (JvmVal Ext)}
    (hcompat : isArrayElemCompat hooks jh cls v = true)
    (hget : jh.get? addr = some (.objArray cls elems))
    (hslt : idx.toBitVec.slt 0#32 = false)
    (hlt : idx.toNat < elems.size) :
    stepInstr hooks .aastore ⟨pc, v :: .i32 idx :: .heapRef addr :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, stkRest, locs, jh.set addr (.objArray cls (elems.set idx.toNat v hlt)), hp⟩) := by
  unfold stepInstr stepArrayStore
  simp [hcompat, hget, hslt, hlt]

theorem stepInstr_newarray_byte {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    {pc : Nat} {n : UInt32} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    (hslt : n.toBitVec.slt 0#32 = false) :
    stepInstr hooks (.newarray "byte") ⟨pc, .i32 n :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .heapRef jh.objects.size :: stkRest, locs,
        (jh.alloc (.byteArray (Array.replicate n.toNat 0))).2, hp⟩) := by
  unfold stepInstr stepNewArray
  simp [hslt, JvmHeap.alloc]

theorem stepInstr_iaload {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    {pc : Nat} {idx : UInt32} {addr : Nat} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    {elems : Array UInt32}
    (hget : jh.get? addr = some (.intArray elems))
    (hslt : idx.toBitVec.slt 0#32 = false)
    (hlt : idx.toNat < elems.size) :
    stepInstr hooks .iaload ⟨pc, .i32 idx :: .heapRef addr :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 elems[idx.toNat] :: stkRest, locs, jh, hp⟩) := by
  unfold stepInstr stepArrayLoad
  simp [hget, hslt, hlt]

theorem stepInstr_iastore {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    {pc : Nat} {v idx : UInt32} {addr : Nat} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    {elems : Array UInt32}
    (hget : jh.get? addr = some (.intArray elems))
    (hslt : idx.toBitVec.slt 0#32 = false)
    (hlt : idx.toNat < elems.size) :
    stepInstr hooks .iastore ⟨pc, .i32 v :: .i32 idx :: .heapRef addr :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, stkRest, locs, jh.set addr (.intArray (elems.set idx.toNat v hlt)), hp⟩) := by
  unfold stepInstr stepArrayStore
  simp [hget, hslt, hlt]

theorem stepInstr_newarray_int {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    {pc : Nat} {n : UInt32} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    (hslt : n.toBitVec.slt 0#32 = false) :
    stepInstr hooks (.newarray "int") ⟨pc, .i32 n :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .heapRef jh.objects.size :: stkRest, locs,
        (jh.alloc (.intArray (Array.replicate n.toNat 0))).2, hp⟩) := by
  unfold stepInstr stepNewArray
  simp [hslt, JvmHeap.alloc]

theorem stepInstr_anewarray {Ext Heap : Type} (hooks : JvmHooks Ext Heap) (cls : String)
    {pc : Nat} {n : UInt32} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    (hslt : n.toBitVec.slt 0#32 = false) :
    stepInstr hooks (.anewarray cls) ⟨pc, .i32 n :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .heapRef jh.objects.size :: stkRest, locs,
        (jh.alloc (.objArray cls (Array.replicate n.toNat .null))).2, hp⟩) := by
  unfold stepInstr
  simp [hslt, JvmHeap.alloc]

theorem stepInvokeStatic_arraysFillAll_obj {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    {pc : Nat} {handler elem : JvmVal Ext} {addr : Nat} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    {cls : String} {elems : Array (JvmVal Ext)} {desc : String}
    (hcompat : isArrayElemCompat hooks jh cls elem = true)
    (hget : jh.get? addr = some (.objArray cls elems)) :
    stepInvokeStaticGeneric hooks
        ⟨pc, handler :: .i32 6 :: .i32 0 :: .i32 0 :: elem :: .heapRef addr :: stkRest, locs, jh, hp⟩
        "kotlin/collections/ArraysKt" "fill$default" desc =
      .inl (some ⟨pc + 1, stkRest, locs,
        jh.set addr (.objArray cls (Array.ofFn (n := elems.size) fun _ => elem)), hp⟩) := by
  simp +decide [stepInvokeStaticGeneric, stepFillRange, hcompat, hget]
  have hnn : ¬((elems.size : Int) < 0) := by omega
  simp [hnn]

theorem stepInvokeStatic_uarraysFillAll_byte {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    {pc : Nat} {handler : JvmVal Ext} {ev : UInt32} {addr : Nat} {stkRest : List (JvmVal Ext)}
    {locs : Nat → JvmVal Ext} {jh : JvmHeap Ext} {hp : Heap}
    {elems : Array UInt8} {desc : String}
    (hget : jh.get? addr = some (.byteArray elems)) :
    stepInvokeStaticGeneric hooks
        ⟨pc, handler :: .i32 6 :: .i32 0 :: .i32 0 :: .i32 ev :: .heapRef addr :: stkRest, locs, jh, hp⟩
        "kotlin/collections/unsigned/UArraysKt" "fill-WpHrYlw$default" desc =
      .inl (some ⟨pc + 1, stkRest, locs,
        jh.set addr (.byteArray (Array.ofFn (n := elems.size) fun _ => ev.toUInt8)), hp⟩) := by
  simp +decide [stepInvokeStaticGeneric, stepFillRange, hget]
  have hnn : ¬((elems.size : Int) < 0) := by omega
  simp [hnn]

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
  simp [stepInvokeStaticGeneric, stepCopyOfRange, hget, hn1, hn2, hn3, JvmHeap.alloc]

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
  simp [stepInvokeStaticGeneric, stepCopyOfRange, hget, hn1, hn2, hn3, JvmHeap.alloc]

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
  simp [stepInvokeStaticGeneric, hslt, JvmHeap.alloc]

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
  simp [stepInvokeStaticGeneric, hget, hslt, hlt]

def runJvm {Ext Heap : Type} (hooks : JvmHooks Ext Heap) :
    Nat → List JvmInstr → JvmState Ext Heap → Option (JvmVal Ext)
  | 0, _, _ => none
  | fuel + 1, prog, st =>
    match prog[st.pc]? with
    | none => none
    | some (.ifeq target) =>
      match st.stack with
      | v :: rest =>
        hooks.iteZero? v
          (runJvm hooks fuel prog { st with pc := target, stack := rest })
          (runJvm hooks fuel prog { st with pc := st.pc + 1, stack := rest })
      | _ => none
    | some (.ifne target) =>
      match st.stack with
      | v :: rest =>
        hooks.iteNonZero? v
          (runJvm hooks fuel prog { st with pc := target, stack := rest })
          (runJvm hooks fuel prog { st with pc := st.pc + 1, stack := rest })
      | _ => none
    | some (.iflt target) =>
      match st.stack with
      | v :: rest =>
        match v.asI32? with
        | some iv =>
          if iv.toBitVec.slt 0#32 then runJvm hooks fuel prog { st with pc := target, stack := rest }
          else runJvm hooks fuel prog { st with pc := st.pc + 1, stack := rest }
        | none => none
      | _ => none
    | some (.ifle target) =>
      match st.stack with
      | v :: rest =>
        match v.asI32? with
        | some iv =>
          if iv.toBitVec.sle 0#32 then runJvm hooks fuel prog { st with pc := target, stack := rest }
          else runJvm hooks fuel prog { st with pc := st.pc + 1, stack := rest }
        | none => none
      | _ => none
    | some (.ifgt target) =>
      match st.stack with
      | v :: rest =>
        match v.asI32? with
        | some iv =>
          if (0#32).slt iv.toBitVec then runJvm hooks fuel prog { st with pc := target, stack := rest }
          else runJvm hooks fuel prog { st with pc := st.pc + 1, stack := rest }
        | none => none
      | _ => none
    | some (.ifge target) =>
      match st.stack with
      | v :: rest =>
        match v.asI32? with
        | some iv =>
          if (0#32).sle iv.toBitVec then runJvm hooks fuel prog { st with pc := target, stack := rest }
          else runJvm hooks fuel prog { st with pc := st.pc + 1, stack := rest }
        | none => none
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
        match a.asI32?, b.asI32? with
        | some av, some bv =>
          if av == bv then runJvm hooks fuel prog { st with pc := target, stack := rest }
          else runJvm hooks fuel prog { st with pc := st.pc + 1, stack := rest }
        | _, _ => none
      | _ => none
    | some (.if_icmpne target) =>
      match st.stack with
      | b :: a :: rest =>
        match a.asI32?, b.asI32? with
        | some av, some bv =>
          if !(av == bv) then runJvm hooks fuel prog { st with pc := target, stack := rest }
          else runJvm hooks fuel prog { st with pc := st.pc + 1, stack := rest }
        | _, _ => none
      | _ => none
    | some (.if_icmplt target) =>
      match st.stack with
      | b :: a :: rest =>
        match a.asI32?, b.asI32? with
        | some av, some bv =>
          if av.toBitVec.slt bv.toBitVec then runJvm hooks fuel prog { st with pc := target, stack := rest }
          else runJvm hooks fuel prog { st with pc := st.pc + 1, stack := rest }
        | _, _ => none
      | _ => none
    | some (.if_icmpge target) =>
      match st.stack with
      | b :: a :: rest =>
        match a.asI32?, b.asI32? with
        | some av, some bv =>
          if bv.toBitVec.sle av.toBitVec then runJvm hooks fuel prog { st with pc := target, stack := rest }
          else runJvm hooks fuel prog { st with pc := st.pc + 1, stack := rest }
        | _, _ => none
      | _ => none
    | some (.if_icmpgt target) =>
      match st.stack with
      | b :: a :: rest =>
        match a.asI32?, b.asI32? with
        | some av, some bv =>
          if bv.toBitVec.slt av.toBitVec then runJvm hooks fuel prog { st with pc := target, stack := rest }
          else runJvm hooks fuel prog { st with pc := st.pc + 1, stack := rest }
        | _, _ => none
      | _ => none
    | some (.if_icmple target) =>
      match st.stack with
      | b :: a :: rest =>
        match a.asI32?, b.asI32? with
        | some av, some bv =>
          if av.toBitVec.sle bv.toBitVec then runJvm hooks fuel prog { st with pc := target, stack := rest }
          else runJvm hooks fuel prog { st with pc := st.pc + 1, stack := rest }
        | _, _ => none
      | _ => none
    | some (.if_acmpeq target) =>
      match st.stack with
      | b :: a :: rest =>
        match JvmVal.refEq? hooks.beqRefExt a b with
        | some true => runJvm hooks fuel prog { st with pc := target, stack := rest }
        | some false => runJvm hooks fuel prog { st with pc := st.pc + 1, stack := rest }
        | none => none
      | _ => none
    | some (.if_acmpne target) =>
      match st.stack with
      | b :: a :: rest =>
        match JvmVal.refEq? hooks.beqRefExt a b with
        | some true => runJvm hooks fuel prog { st with pc := st.pc + 1, stack := rest }
        | some false => runJvm hooks fuel prog { st with pc := target, stack := rest }
        | none => none
      | _ => none
    | some (.tableswitch low targets defaultTarget) =>
      match st.stack with
      | key :: rest =>
        match key.asI32? with
        | some kv =>
          let target := tableswitchTarget kv low targets defaultTarget
          runJvm hooks fuel prog { st with pc := target, stack := rest }
        | none => none
      | _ => none
    | some (.lookupswitch cases defaultTarget) =>
      match st.stack with
      | key :: rest =>
        match key.asI32? with
        | some kv =>
          let target := lookupswitchTarget kv cases defaultTarget
          runJvm hooks fuel prog { st with pc := target, stack := rest }
        | none => none
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
        match hooks.isZero? v with
        | some true => runJvmRes hooks fuel prog { st with pc := target, stack := rest }
        | some false => runJvmRes hooks fuel prog { st with pc := st.pc + 1, stack := rest }
        | none => none
      | _ => none
    | some (.ifne target) =>
      match st.stack with
      | v :: rest =>
        match hooks.isZero? v with
        | some true => runJvmRes hooks fuel prog { st with pc := st.pc + 1, stack := rest }
        | some false => runJvmRes hooks fuel prog { st with pc := target, stack := rest }
        | none => none
      | _ => none
    | some (.iflt target) =>
      match st.stack with
      | v :: rest =>
        match v.asI32? with
        | some iv =>
          if iv.toBitVec.slt 0#32 then runJvmRes hooks fuel prog { st with pc := target, stack := rest }
          else runJvmRes hooks fuel prog { st with pc := st.pc + 1, stack := rest }
        | none => none
      | _ => none
    | some (.ifle target) =>
      match st.stack with
      | v :: rest =>
        match v.asI32? with
        | some iv =>
          if iv.toBitVec.sle 0#32 then runJvmRes hooks fuel prog { st with pc := target, stack := rest }
          else runJvmRes hooks fuel prog { st with pc := st.pc + 1, stack := rest }
        | none => none
      | _ => none
    | some (.ifgt target) =>
      match st.stack with
      | v :: rest =>
        match v.asI32? with
        | some iv =>
          if (0#32).slt iv.toBitVec then runJvmRes hooks fuel prog { st with pc := target, stack := rest }
          else runJvmRes hooks fuel prog { st with pc := st.pc + 1, stack := rest }
        | none => none
      | _ => none
    | some (.ifge target) =>
      match st.stack with
      | v :: rest =>
        match v.asI32? with
        | some iv =>
          if (0#32).sle iv.toBitVec then runJvmRes hooks fuel prog { st with pc := target, stack := rest }
          else runJvmRes hooks fuel prog { st with pc := st.pc + 1, stack := rest }
        | none => none
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
        match a.asI32?, b.asI32? with
        | some av, some bv =>
          if av == bv then runJvmRes hooks fuel prog { st with pc := target, stack := rest }
          else runJvmRes hooks fuel prog { st with pc := st.pc + 1, stack := rest }
        | _, _ => none
      | _ => none
    | some (.if_icmpne target) =>
      match st.stack with
      | b :: a :: rest =>
        match a.asI32?, b.asI32? with
        | some av, some bv =>
          if !(av == bv) then runJvmRes hooks fuel prog { st with pc := target, stack := rest }
          else runJvmRes hooks fuel prog { st with pc := st.pc + 1, stack := rest }
        | _, _ => none
      | _ => none
    | some (.if_icmplt target) =>
      match st.stack with
      | b :: a :: rest =>
        match a.asI32?, b.asI32? with
        | some av, some bv =>
          if av.toBitVec.slt bv.toBitVec then runJvmRes hooks fuel prog { st with pc := target, stack := rest }
          else runJvmRes hooks fuel prog { st with pc := st.pc + 1, stack := rest }
        | _, _ => none
      | _ => none
    | some (.if_icmpge target) =>
      match st.stack with
      | b :: a :: rest =>
        match a.asI32?, b.asI32? with
        | some av, some bv =>
          if bv.toBitVec.sle av.toBitVec then runJvmRes hooks fuel prog { st with pc := target, stack := rest }
          else runJvmRes hooks fuel prog { st with pc := st.pc + 1, stack := rest }
        | _, _ => none
      | _ => none
    | some (.if_icmpgt target) =>
      match st.stack with
      | b :: a :: rest =>
        match a.asI32?, b.asI32? with
        | some av, some bv =>
          if bv.toBitVec.slt av.toBitVec then runJvmRes hooks fuel prog { st with pc := target, stack := rest }
          else runJvmRes hooks fuel prog { st with pc := st.pc + 1, stack := rest }
        | _, _ => none
      | _ => none
    | some (.if_icmple target) =>
      match st.stack with
      | b :: a :: rest =>
        match a.asI32?, b.asI32? with
        | some av, some bv =>
          if av.toBitVec.sle bv.toBitVec then runJvmRes hooks fuel prog { st with pc := target, stack := rest }
          else runJvmRes hooks fuel prog { st with pc := st.pc + 1, stack := rest }
        | _, _ => none
      | _ => none
    | some (.if_acmpeq target) =>
      match st.stack with
      | b :: a :: rest =>
        match JvmVal.refEq? hooks.beqRefExt a b with
        | some true => runJvmRes hooks fuel prog { st with pc := target, stack := rest }
        | some false => runJvmRes hooks fuel prog { st with pc := st.pc + 1, stack := rest }
        | none => none
      | _ => none
    | some (.if_acmpne target) =>
      match st.stack with
      | b :: a :: rest =>
        match JvmVal.refEq? hooks.beqRefExt a b with
        | some true => runJvmRes hooks fuel prog { st with pc := st.pc + 1, stack := rest }
        | some false => runJvmRes hooks fuel prog { st with pc := target, stack := rest }
        | none => none
      | _ => none
    | some (.tableswitch low targets defaultTarget) =>
      match st.stack with
      | key :: rest =>
        match key.asI32? with
        | some kv =>
          let target := tableswitchTarget kv low targets defaultTarget
          runJvmRes hooks fuel prog { st with pc := target, stack := rest }
        | none => none
      | _ => none
    | some (.lookupswitch cases defaultTarget) =>
      match st.stack with
      | key :: rest =>
        match key.asI32? with
        | some kv =>
          let target := lookupswitchTarget kv cases defaultTarget
          runJvmRes hooks fuel prog { st with pc := target, stack := rest }
        | none => none
      | _ => none
    | some instr =>
      match stepInstr hooks instr st with
      | .inl (some st') => runJvmRes hooks fuel prog st'
      | .inl none => none
      | .inr (some res) => some (res, st)
      | .inr none => none

end Jvm
