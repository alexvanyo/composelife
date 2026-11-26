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
import models.SerializersModel

namespace Serialization.JvmVerification

export Jvm (JvmInstr setLocal)

/-- Concrete payload values carried through `SurrogatingSerializer`. -/
inductive SerPayload where
  | long (v : UInt64)
  | float (v : Float32)
  | str (s : String)
  | obj (id : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Domain-specific JVM extension values for `:serialization`. -/
inductive SerExt where
  | primitiveKindLong
  | serialDescriptor (name : String) (orig : Option String)
  | floatArraySerializer
  | closedFloatRange (r : Model.ClosedFloatRangeModel)
  | rect (r : Model.RectModel)
  | boxedFloat (v : Float32)
  | boxedIntOffset (v : UInt64)
  | boxedOffset (v : UInt64)
  | encoder (id : Nat)
  | decoder (id : Nat)
  | surrogateSer (id : Nat) (descName : String)
  | fn1 (id : Nat)
  | payload (v : SerPayload)
  deriving DecidableEq, Repr, Inhabited

/-- Module heap tracking encoded outputs and decoder/lambda/serializer oracles. -/
structure SerHeap where
  encodedLong : Option UInt64 := none
  encodedFloatArray : Option (Array Float32) := none
  encodedSurrogate : Option SerPayload := none
  decodedLong : UInt64 := 0
  decodedFloatArray : Array Float32 := #[]
  decodedSurrogate : SerPayload := .obj 0
  fn1Eval : Nat → SerPayload → SerPayload := fun _ x => x

abbrev SerVal := Jvm.JvmVal SerExt
abbrev SerState := Jvm.JvmState SerExt SerHeap

def initSerJvmState (slots : List (Nat × SerVal))
    (hp : SerHeap := {}) (jh : Jvm.JvmHeap SerExt := {}) : SerState :=
  Jvm.initJvmState slots (.i32 0) hp jh

def packIntOffset (x y : Int32) : UInt64 := Model.packInts x y
def unpackIntOffsetX (v : UInt64) : Int32 := Model.unpackInt1 v
def unpackIntOffsetY (v : UInt64) : Int32 := Model.unpackInt2 v

/-- Non-recursive base hooks for `:serialization` leaf operations. -/
def serBaseHooks : Jvm.JvmHooks SerExt SerHeap where
  checkInstanceOf cls v :=
    match cls, v with
    | "kotlin/ranges/ClosedRange", .ext (.closedFloatRange _) => true
    | "java/lang/Number", .ext (.boxedFloat _) => true
    | "kotlinx/serialization/descriptors/PrimitiveKind", .ext .primitiveKindLong => true
    | "androidx/compose/ui/unit/IntOffset", .ext (.boxedIntOffset _) => true
    | "androidx/compose/ui/geometry/Offset", .ext (.boxedOffset _) => true
    | "androidx/compose/ui/geometry/Rect", .ext (.rect _) => true
    | "[F", .heapRef _ => true
    | _, _ => false
  checkCast cls v :=
    match cls, v with
    | "kotlin/ranges/ClosedRange", .ext (.closedFloatRange _) => some v
    | "java/lang/Number", .ext (.boxedFloat _) => some v
    | "kotlinx/serialization/descriptors/PrimitiveKind", .ext .primitiveKindLong => some v
    | "androidx/compose/ui/unit/IntOffset", .ext (.boxedIntOffset _) => some v
    | "androidx/compose/ui/geometry/Offset", .ext (.boxedOffset _) => some v
    | "androidx/compose/ui/geometry/Rect", .ext (.rect _) => some v
    | "[F", .heapRef _ => some v
    | _, _ => Jvm.defaultCheckCast (fun _ _ => none) cls v
  resolveStatic st cls field _desc :=
    match cls, field with
    | "kotlinx/serialization/descriptors/PrimitiveKind$LONG", "INSTANCE" =>
      some (.ext .primitiveKindLong)
    | _, _ => st.jvmHeap.getStatic? cls field
  stepNewClass st cls :=
    let (addr, h') := st.jvmHeap.alloc (.instance cls [])
    .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: st.stack, jvmHeap := h' })
  stepInvokeSpecial st cls method desc :=
    match cls, method, desc, st.stack with
    | "java/lang/Object", "<init>", "()V", _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := rest })
    | "com/alexvanyo/composelife/serialization/ClosedFloatRangeSerializer", "<init>", "()V", _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := rest })
    | "com/alexvanyo/composelife/serialization/IntOffsetSerializer", "<init>", "()V", _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := rest })
    | "com/alexvanyo/composelife/serialization/OffsetSerializer", "<init>", "()V", _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := rest })
    | "com/alexvanyo/composelife/serialization/RectSerializer", "<init>", "()V", _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := rest })
    | "androidx/compose/ui/geometry/Rect", "<init>", "(FFFF)V",
        b :: r :: t :: l :: .heapRef addr :: rest =>
      match l.asF32?, t.asF32?, r.asF32?, b.asF32? with
      | some vl, some vt, some vr, some vb =>
        let rectVal : SerVal := .ext (.rect { left := vl, top := vt, right := vr, bottom := vb })
        let stack' := rest.map fun x => match x with | .heapRef a => if a == addr then rectVal else x | _ => x
        .inl (some { st with pc := st.pc + 1, stack := stack' })
      | _, _, _, _ => .inr none
    | _, _, _, _ => .inr none
  stepInvokeStatic st cls method desc :=
    match cls, method, desc, st.stack with
    | "java/lang/Float", "intBitsToFloat", "(I)F", x :: rest =>
      match x.asI32? with
      | some bits => .inl (some { st with pc := st.pc + 1, stack := .f32 (Float32.ofBits bits) :: rest })
      | none => .inr none
    | "java/lang/Float", "floatToRawIntBits", "(F)I", x :: rest =>
      match x.asF32? with
      | some f => .inl (some { st with pc := st.pc + 1, stack := .i32 f.toBits :: rest })
      | none => .inr none
    | "kotlin/ranges/RangesKt", "rangeTo", "(FF)Lkotlin/ranges/ClosedFloatingPointRange;",
        hi :: lo :: rest =>
      match lo.asF32?, hi.asF32? with
      | some s, some e =>
        .inl (some { st with pc := st.pc + 1, stack := .ext (.closedFloatRange { start := s, endInclusive := e }) :: rest })
      | _, _ => .inr none
    | "kotlinx/serialization/descriptors/SerialDescriptorsKt", "PrimitiveSerialDescriptor",
        "(Ljava/lang/String;Lkotlinx/serialization/descriptors/PrimitiveKind;)Lkotlinx/serialization/descriptors/SerialDescriptor;",
        .ext .primitiveKindLong :: .str name :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .ext (.serialDescriptor name (some "LONG")) :: rest })
    | "kotlinx/serialization/descriptors/SerialDescriptorsKt", "SerialDescriptor",
        "(Ljava/lang/String;Lkotlinx/serialization/descriptors/SerialDescriptor;)Lkotlinx/serialization/descriptors/SerialDescriptor;",
        .ext (.serialDescriptor origName _) :: .str name :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .ext (.serialDescriptor name (some origName)) :: rest })
    | "kotlinx/serialization/builtins/BuiltinSerializersKt", "FloatArraySerializer",
        "()Lkotlinx/serialization/KSerializer;", rest =>
      .inl (some { st with pc := st.pc + 1, stack := .ext .floatArraySerializer :: rest })
    | "androidx/compose/ui/unit/IntOffset", "constructor-impl", "(J)J", _ =>
      .inl (some { st with pc := st.pc + 1 })
    | "androidx/compose/ui/unit/IntOffset", "getX-impl", "(J)I", v :: rest =>
      match v.asI64? with
      | some p => .inl (some { st with pc := st.pc + 1, stack := .i32 (unpackIntOffsetX p).toUInt32 :: rest })
      | none => .inr none
    | "androidx/compose/ui/unit/IntOffset", "getY-impl", "(J)I", v :: rest =>
      match v.asI64? with
      | some p => .inl (some { st with pc := st.pc + 1, stack := .i32 (unpackIntOffsetY p).toUInt32 :: rest })
      | none => .inr none
    | "androidx/compose/ui/unit/IntOffset", "box-impl", "(J)Landroidx/compose/ui/unit/IntOffset;", v :: rest =>
      match v.asI64? with
      | some p => .inl (some { st with pc := st.pc + 1, stack := .ext (.boxedIntOffset p) :: rest })
      | none => .inr none
    | "androidx/compose/ui/geometry/Offset", "constructor-impl", "(J)J", _ =>
      .inl (some { st with pc := st.pc + 1 })
    | "androidx/compose/ui/geometry/Offset", "box-impl", "(J)Landroidx/compose/ui/geometry/Offset;", v :: rest =>
      match v.asI64? with
      | some p => .inl (some { st with pc := st.pc + 1, stack := .ext (.boxedOffset p) :: rest })
      | none => .inr none
    | _, _, _, _ => .inr none
  stepInvokeVirtual st cls method desc :=
    match cls, method, desc, st.stack with
    | "java/lang/Number", "floatValue", "()F", .ext (.boxedFloat f) :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .f32 f :: rest })
    | "androidx/compose/ui/unit/IntOffset", "unbox-impl", "()J", .ext (.boxedIntOffset p) :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i64 p :: rest })
    | "androidx/compose/ui/geometry/Offset", "unbox-impl", "()J", .ext (.boxedOffset p) :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i64 p :: rest })
    | "androidx/compose/ui/geometry/Rect", "getLeft", "()F", .ext (.rect r) :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .f32 r.left :: rest })
    | "androidx/compose/ui/geometry/Rect", "getTop", "()F", .ext (.rect r) :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .f32 r.top :: rest })
    | "androidx/compose/ui/geometry/Rect", "getRight", "()F", .ext (.rect r) :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .f32 r.right :: rest })
    | "androidx/compose/ui/geometry/Rect", "getBottom", "()F", .ext (.rect r) :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .f32 r.bottom :: rest })
    | _, _, _, _ => .inr none
  stepInvokeInterface st cls method desc :=
    match cls, method, desc, st.stack with
    | "kotlinx/serialization/encoding/Decoder", "decodeLong", "()J", .ext (.decoder _) :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i64 st.heap.decodedLong :: rest })
    | "kotlinx/serialization/encoding/Encoder", "encodeLong", "(J)V", v :: .ext (.encoder _) :: rest =>
      match v.asI64? with
      | some l =>
        .inl (some { st with pc := st.pc + 1, stack := rest, heap := { st.heap with encodedLong := some l } })
      | none => .inr none
    | "kotlin/ranges/ClosedRange", "getStart", "()Ljava/lang/Comparable;", .ext (.closedFloatRange r) :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .ext (.boxedFloat r.start) :: rest })
    | "kotlin/ranges/ClosedRange", "getEndInclusive", "()Ljava/lang/Comparable;", .ext (.closedFloatRange r) :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .ext (.boxedFloat r.endInclusive) :: rest })
    | "kotlinx/serialization/KSerializer", "getDescriptor", "()Lkotlinx/serialization/descriptors/SerialDescriptor;",
        .ext .floatArraySerializer :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .ext (.serialDescriptor "kotlin.FloatArray" none) :: rest })
    | "kotlinx/serialization/KSerializer", "getDescriptor", "()Lkotlinx/serialization/descriptors/SerialDescriptor;",
        .ext (.surrogateSer _ descName) :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .ext (.serialDescriptor descName none) :: rest })
    | "kotlinx/serialization/KSerializer", "deserialize", "(Lkotlinx/serialization/encoding/Decoder;)Ljava/lang/Object;",
        .ext (.decoder _) :: .ext .floatArraySerializer :: rest =>
      let (addr, jh') := st.jvmHeap.alloc (.floatArray st.heap.decodedFloatArray)
      .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := jh' })
    | "kotlinx/serialization/KSerializer", "serialize", "(Lkotlinx/serialization/encoding/Encoder;Ljava/lang/Object;)V",
        .heapRef arrAddr :: .ext (.encoder _) :: .ext .floatArraySerializer :: rest =>
      match st.jvmHeap.get? arrAddr with
      | some (.floatArray elems) =>
        .inl (some { st with pc := st.pc + 1, stack := rest, heap := { st.heap with encodedFloatArray := some elems } })
      | _ => .inr none
    | "kotlinx/serialization/KSerializer", "deserialize", "(Lkotlinx/serialization/encoding/Decoder;)Ljava/lang/Object;",
        .ext (.decoder _) :: .ext (.surrogateSer _ _) :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .ext (.payload st.heap.decodedSurrogate) :: rest })
    | "kotlinx/serialization/KSerializer", "serialize", "(Lkotlinx/serialization/encoding/Encoder;Ljava/lang/Object;)V",
        .ext (.payload p) :: .ext (.encoder _) :: .ext (.surrogateSer _ _) :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := rest, heap := { st.heap with encodedSurrogate := some p } })
    | "kotlin/jvm/functions/Function1", "invoke", "(Ljava/lang/Object;)Ljava/lang/Object;",
        .ext (.payload p) :: .ext (.fn1 fid) :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .ext (.payload (st.heap.fn1Eval fid p)) :: rest })
    | _, _, _, _ => .inr none

/--
Hooks extending `serBaseHooks` with 1-level dispatch for erased `KSerializer` bridge methods
(`deserialize_1`, `serialize_1`) into their lifted target programs under `serBaseHooks`.
-/
def mkSerHooks (resolveProg : String → Option (List JvmInstr)) (subFuel : Nat) :
    Jvm.JvmHooks SerExt SerHeap :=
  { serBaseHooks with
    stepInvokeVirtual := fun st cls method desc =>
      match cls, method, desc, st.stack with
      | "com/alexvanyo/composelife/serialization/ClosedFloatRangeSerializer", "deserialize",
          "(Lkotlinx/serialization/encoding/Decoder;)Lkotlin/ranges/ClosedRange;",
          dec :: recv :: rest =>
        match resolveProg (cls ++ "." ++ method ++ ":" ++ desc) with
        | some prog =>
          match Jvm.runJvmRes serBaseHooks subFuel prog (initSerJvmState [(0, recv), (1, dec)] st.heap st.jvmHeap) with
          | some (retVal, endSt) =>
            .inl (some { st with pc := st.pc + 1, stack := retVal :: rest, heap := endSt.heap, jvmHeap := endSt.jvmHeap })
          | none => .inr none
        | none => .inr none
      | "com/alexvanyo/composelife/serialization/ClosedFloatRangeSerializer", "serialize",
          "(Lkotlinx/serialization/encoding/Encoder;Lkotlin/ranges/ClosedRange;)V",
          val :: enc :: recv :: rest =>
        match resolveProg (cls ++ "." ++ method ++ ":" ++ desc) with
        | some prog =>
          match Jvm.runJvmRes serBaseHooks subFuel prog (initSerJvmState [(0, recv), (1, enc), (2, val)] st.heap st.jvmHeap) with
          | some (_, endSt) =>
            .inl (some { st with pc := st.pc + 1, stack := rest, heap := endSt.heap, jvmHeap := endSt.jvmHeap })
          | none => .inr none
        | none => .inr none
      | "com/alexvanyo/composelife/serialization/IntOffsetSerializer", "deserialize-Bjo55l4",
          "(Lkotlinx/serialization/encoding/Decoder;)J",
          dec :: recv :: rest =>
        match resolveProg (cls ++ "." ++ method ++ ":" ++ desc) with
        | some prog =>
          match Jvm.runJvmRes serBaseHooks subFuel prog (initSerJvmState [(0, recv), (1, dec)] st.heap st.jvmHeap) with
          | some (retVal, endSt) =>
            .inl (some { st with pc := st.pc + 1, stack := retVal :: rest, heap := endSt.heap, jvmHeap := endSt.jvmHeap })
          | none => .inr none
        | none => .inr none
      | "com/alexvanyo/composelife/serialization/IntOffsetSerializer", "serialize-I_oMVgE",
          "(Lkotlinx/serialization/encoding/Encoder;J)V",
          val :: enc :: recv :: rest =>
        match resolveProg (cls ++ "." ++ method ++ ":" ++ desc) with
        | some prog =>
          match Jvm.runJvmRes serBaseHooks subFuel prog (initSerJvmState [(0, recv), (1, enc), (2, val)] st.heap st.jvmHeap) with
          | some (_, endSt) =>
            .inl (some { st with pc := st.pc + 1, stack := rest, heap := endSt.heap, jvmHeap := endSt.jvmHeap })
          | none => .inr none
        | none => .inr none
      | "com/alexvanyo/composelife/serialization/OffsetSerializer", "deserialize-tuRUvjQ",
          "(Lkotlinx/serialization/encoding/Decoder;)J",
          dec :: recv :: rest =>
        match resolveProg (cls ++ "." ++ method ++ ":" ++ desc) with
        | some prog =>
          match Jvm.runJvmRes serBaseHooks subFuel prog (initSerJvmState [(0, recv), (1, dec)] st.heap st.jvmHeap) with
          | some (retVal, endSt) =>
            .inl (some { st with pc := st.pc + 1, stack := retVal :: rest, heap := endSt.heap, jvmHeap := endSt.jvmHeap })
          | none => .inr none
        | none => .inr none
      | "com/alexvanyo/composelife/serialization/OffsetSerializer", "serialize-Uv8p0NA",
          "(Lkotlinx/serialization/encoding/Encoder;J)V",
          val :: enc :: recv :: rest =>
        match resolveProg (cls ++ "." ++ method ++ ":" ++ desc) with
        | some prog =>
          match Jvm.runJvmRes serBaseHooks subFuel prog (initSerJvmState [(0, recv), (1, enc), (2, val)] st.heap st.jvmHeap) with
          | some (_, endSt) =>
            .inl (some { st with pc := st.pc + 1, stack := rest, heap := endSt.heap, jvmHeap := endSt.jvmHeap })
          | none => .inr none
        | none => .inr none
      | "com/alexvanyo/composelife/serialization/RectSerializer", "deserialize",
          "(Lkotlinx/serialization/encoding/Decoder;)Landroidx/compose/ui/geometry/Rect;",
          dec :: recv :: rest =>
        match resolveProg (cls ++ "." ++ method ++ ":" ++ desc) with
        | some prog =>
          match Jvm.runJvmRes serBaseHooks subFuel prog (initSerJvmState [(0, recv), (1, dec)] st.heap st.jvmHeap) with
          | some (retVal, endSt) =>
            .inl (some { st with pc := st.pc + 1, stack := retVal :: rest, heap := endSt.heap, jvmHeap := endSt.jvmHeap })
          | none => .inr none
        | none => .inr none
      | "com/alexvanyo/composelife/serialization/RectSerializer", "serialize",
          "(Lkotlinx/serialization/encoding/Encoder;Landroidx/compose/ui/geometry/Rect;)V",
          val :: enc :: recv :: rest =>
        match resolveProg (cls ++ "." ++ method ++ ":" ++ desc) with
        | some prog =>
          match Jvm.runJvmRes serBaseHooks subFuel prog (initSerJvmState [(0, recv), (1, enc), (2, val)] st.heap st.jvmHeap) with
          | some (_, endSt) =>
            .inl (some { st with pc := st.pc + 1, stack := rest, heap := endSt.heap, jvmHeap := endSt.jvmHeap })
          | none => .inr none
        | none => .inr none
      | _, _, _, _ => serBaseHooks.stepInvokeVirtual st cls method desc }

end Serialization.JvmVerification
