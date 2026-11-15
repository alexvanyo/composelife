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

export Jvm (JvmInstr setLocal)

abbrev JvmVal := Jvm.JvmVal Empty
abbrev JvmState := Jvm.JvmState Empty Unit

namespace JvmVal
export Jvm.JvmVal (i32 i64 f64 null heapRef pair boxedInt isNull asI32 asI64 asF64)
end JvmVal

def initJvmState (slots : List (Nat × JvmVal))
    (jvmHeap : Jvm.JvmHeap Empty := {}) : JvmState :=
  Jvm.initJvmState slots (.i32 0) () jvmHeap

def encodeCoordPairs (xs : Array (Int32 × Int32)) : Array JvmVal :=
  xs.map fun (x, y) => .pair (.boxedInt x.toUInt32) (.boxedInt y.toUInt32)

def decodeCoordPair : JvmVal → Option (Int32 × Int32)
  | .pair (.boxedInt x) (.boxedInt y) => some (x.toInt32, y.toInt32)
  | _ => none

def decodeCoordArray (elems : Array JvmVal) : Option (Array (Int32 × Int32)) :=
  elems.mapM decodeCoordPair

def geomHooks : Jvm.JvmHooks Empty Unit where
  stepInvokeStatic st _cls method desc :=
    match method, desc, st.stack with
    | "f_Geometry_absFloat___closed__0", "()D", rest =>
      .inl (some { st with pc := st.pc + 1, stack := .f64 0.0 :: rest })
    | "f_Geometry_absFloat", "(D)D", x :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .f64 (Geometry.absFloat x.asF64) :: rest })
    | "f_Geometry_absInt", "(I)I", x :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 (Geometry.absInt x.asI32.toInt32) :: rest })
    | "f_Geometry_rayMarchLoop___redArg-v0ARYG8", "(IDDDDIIIIIILjava/lang/Object;)Ljava/lang/Object;",
        .heapRef accAddr :: curY :: curX :: endY :: endX :: stepY :: stepX ::
          absDy :: absDx :: startY :: startX :: fuel :: rest =>
      match st.jvmHeap.get? accAddr with
      | some (.objArray cls elems) =>
        match decodeCoordArray elems with
        | some acc =>
          let out := Geometry.rayMarchLoop
            fuel.asI32 startX.asF64 startY.asF64 0.0 0.0 absDx.asF64 absDy.asF64
            stepX.asI32.toInt32 stepY.asI32.toInt32 endX.asI32.toInt32 endY.asI32.toInt32
            curX.asI32.toInt32 curY.asI32.toInt32 acc
          let (outAddr, h') := st.jvmHeap.alloc (.objArray cls (encodeCoordPairs out))
          .inl (some { st with pc := st.pc + 1, stack := .heapRef outAddr :: rest, jvmHeap := h' })
        | none => .inr none
      | _ => .inr none
    | _, _, _ => .inr none

def stepInstr := Jvm.stepInstr geomHooks
def runJvm := Jvm.runJvm geomHooks
def runJvmRes := Jvm.runJvmRes geomHooks

end Geometry.JvmVerification
