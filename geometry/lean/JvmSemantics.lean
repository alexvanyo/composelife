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
import Geometry.LineSegment

namespace Geometry.JvmVerification

export Jvm (JvmInstr setLocal dedupJvmVals extractListArray?)

abbrev JvmVal := Jvm.JvmVal Empty
abbrev JvmState := Jvm.JvmState Empty Unit

namespace JvmVal
export Jvm.JvmVal (i32 i64 f32 f64 null heapRef pair boxedInt isNull asI32? asI64? asF32? asF64?)
end JvmVal

def initJvmState (slots : List (Nat × JvmVal))
    (jvmHeap : Jvm.JvmHeap Empty := {}) : JvmState :=
  Jvm.initJvmState slots (.i32 0) () jvmHeap

def packIntOffset (x y : Int32) : UInt64 :=
  (x.toUInt32.toUInt64 <<< 32) ||| y.toUInt32.toUInt64

def unpackIntOffsetX (packed : UInt64) : Int32 :=
  (packed >>> 32).toUInt32.toInt32

def unpackIntOffsetY (packed : UInt64) : Int32 :=
  packed.toUInt32.toInt32

def encodeCoordPairs (xs : Array (Int32 × Int32)) : Array JvmVal :=
  xs.map fun (x, y) => .pair (.boxedInt x.toUInt32) (.boxedInt y.toUInt32)

def decodeCoordPair : JvmVal → Option (Int32 × Int32)
  | .pair (.boxedInt x) (.boxedInt y) => some (x.toInt32, y.toInt32)
  | _ => none

def decodeCoordArray (elems : Array JvmVal) : Option (Array (Int32 × Int32)) :=
  elems.mapM decodeCoordPair

def stepIntOffsetStatic (st : JvmState) (cls method desc : String) :
    Option JvmState ⊕ Option JvmVal :=
  match cls, method, desc, st.stack with
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
    | some p => .inl (some { st with pc := st.pc + 1, stack := .boxedLong p :: rest })
    | none => .inr none
  | "androidx/compose/ui/unit/IntOffset", "plus-qkQi6aY", "(JJ)J", b :: a :: rest =>
    match a.asI64?, b.asI64? with
    | some pa, some pb =>
      let sum := packIntOffset (unpackIntOffsetX pa + unpackIntOffsetX pb) (unpackIntOffsetY pa + unpackIntOffsetY pb)
      .inl (some { st with pc := st.pc + 1, stack := .i64 sum :: rest })
    | _, _ => .inr none
  | "com/alexvanyo/composelife/geometry/IntOffset_jbKt", "IntOffset", "(II)J", y :: x :: rest =>
    match x.asI32?, y.asI32? with
    | some vx, some vy => .inl (some { st with pc := st.pc + 1, stack := .i64 (packIntOffset vx.toInt32 vy.toInt32) :: rest })
    | _, _ => .inr none
  | _, _, _, _ => .inr none

def geomHooks : Jvm.JvmHooks Empty Unit where
  checkInstanceOf cls v :=
    match cls, v with
    | "androidx/compose/ui/unit/IntOffset", .boxedLong _ => true
    | "java/lang/Object", .boxedLong _ => true
    | _, _ => false
  checkCast cls v :=
    match cls, v with
    | "androidx/compose/ui/unit/IntOffset", .boxedLong _ => some v
    | "java/lang/Object", .boxedLong _ => some v
    | _, _ => Jvm.defaultCheckCast (fun _ a => nomatch a) cls v
  stepInvokeVirtual st cls method desc :=
    match cls, method, desc, st.stack with
    | "androidx/compose/ui/unit/IntOffset", "unbox-impl", "()J", .boxedLong v :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i64 v :: rest })
    | _, _, _, _ => .inr none
  stepInvokeStatic st cls method desc :=
    match stepIntOffsetStatic st cls method desc with
    | .inl (some st') => .inl (some st')
    | _ =>
      match cls, method, desc, st.stack with
      | "java/lang/Float", "intBitsToFloat", "(I)F", x :: rest =>
        match x.asI32? with
        | some va => .inl (some { st with pc := st.pc + 1, stack := .f32 (Float32.ofBits va) :: rest })
        | none => .inr none
      | "java/lang/Math", "floor", "(D)D", x :: rest =>
        match x.asF64? with
        | some va => .inl (some { st with pc := st.pc + 1, stack := .f64 va.floor :: rest })
        | none => .inr none
      | "java/lang/Math", "signum", "(F)F", x :: rest =>
        match x.asF32? with
        | some va =>
          let s := if va.isNaN || va == 0.0 then va else if va < 0.0 then (-1.0 : Float32) else (1.0 : Float32)
          .inl (some { st with pc := st.pc + 1, stack := .f32 s :: rest })
        | none => .inr none
      | _, "f_Geometry_absFloat___closed__0", "()D", rest =>
        .inl (some { st with pc := st.pc + 1, stack := .f64 0.0 :: rest })
      | _, "f_Geometry_absFloat", "(D)D", x :: rest =>
        match x.asF64? with
        | some vx => .inl (some { st with pc := st.pc + 1, stack := .f64 (Geometry.absFloat vx) :: rest })
        | none => .inr none
      | _, "f_Geometry_absInt", "(I)I", x :: rest =>
        match x.asI32? with
        | some vx => .inl (some { st with pc := st.pc + 1, stack := .i32 (Geometry.absInt vx.toInt32) :: rest })
        | none => .inr none
      | _, "f_Geometry_rayMarchLoop___redArg-v0ARYG8",
          "(IDDDDIIIIIILjava/lang/Object;)Ljava/lang/Object;",
          .heapRef accAddr :: curY :: curX :: endY :: endX :: stepY :: stepX ::
            absDy :: absDx :: startY :: startX :: fuel :: rest =>
        match fuel.asI32?, startX.asF64?, startY.asF64?, absDx.asF64?, absDy.asF64?,
            stepX.asI32?, stepY.asI32?, endX.asI32?, endY.asI32?, curX.asI32?, curY.asI32?,
            st.jvmHeap.get? accAddr with
        | some vfuel, some vsx, some vsy, some vadx, some vady,
            some vstx, some vsty, some vex, some vey, some vcx, some vcy,
            some (.objArray cls elems) =>
          match decodeCoordArray elems with
          | some acc =>
            let out := Geometry.rayMarchLoop
              vfuel vsx vsy 0.0 0.0 vadx vady
              vstx.toInt32 vsty.toInt32 vex.toInt32 vey.toInt32
              vcx.toInt32 vcy.toInt32 acc
            let (outAddr, h') := st.jvmHeap.alloc (.objArray cls (encodeCoordPairs out))
            .inl (some { st with pc := st.pc + 1, stack := .heapRef outAddr :: rest, jvmHeap := h' })
          | none => .inr none
        | _, _, _, _, _, _, _, _, _, _, _, _ => .inr none
      | _, _, _, _ => .inr none

def stepInstr := Jvm.stepInstr geomHooks
def runJvm := Jvm.runJvm geomHooks
def runJvmRes := Jvm.runJvmRes geomHooks

end Geometry.JvmVerification
