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
import Geometry.LineSegment

namespace Geometry.JvmVerification

inductive JvmVal where
  | i32 (v : UInt32)
  | i64 (v : UInt64)
  | f64 (v : Float)
  deriving Repr, Inhabited

def JvmVal.asI32 : JvmVal → UInt32
  | .i32 v => v
  | .i64 v => v.toUInt32
  | .f64 _ => 0

def JvmVal.asF64 : JvmVal → Float
  | .f64 v => v
  | _ => 0.0

def JvmVal.ite (c : Bool) (t e : Option JvmVal) : Option JvmVal :=
  match t, e with
  | some (.i32 vt), some (.i32 ve) => some (.i32 (if c then vt else ve))
  | some (.i64 vt), some (.i64 ve) => some (.i64 (if c then vt else ve))
  | some (.f64 vt), some (.f64 ve) => some (.f64 (if c then vt else ve))
  | _, _ => none

inductive JvmInstr where
  | nop | dup | pop | swap | aconstNull | athrow
  | iconst (v : UInt32)
  | lconst (v : UInt64)
  | dconst0 | dconst1
  | ldcStr (s : String)
  | iload (idx : Nat)
  | lload (idx : Nat)
  | aload (idx : Nat)
  | dload (idx : Nat)
  | istore (idx : Nat)
  | lstore (idx : Nat)
  | astore (idx : Nat)
  | dstore (idx : Nat)
  | iadd | isub | imul | ineg | iand | ior | ixor | ishl | ishr | iushr
  | ladd | lsub | lmul | land | lor | lxor | lshl | lshr | lushr
  | dneg | dcmpg | dcmpl
  | i2l | l2i | i2b | lcmp
  | ifeq (target : Nat)
  | ifne (target : Nat)
  | iflt (target : Nat)
  | ifle (target : Nat)
  | ifgt (target : Nat)
  | ifge (target : Nat)
  | ifnull (target : Nat)
  | ifnonnull (target : Nat)
  | if_icmpeq (target : Nat)
  | if_icmpne (target : Nat)
  | if_icmplt (target : Nat)
  | goto (target : Nat)
  | newClass (cls : String)
  | checkcast (cls : String)
  | instanceof (cls : String)
  | invokevirtual (cls method desc : String)
  | invokespecial (cls method desc : String)
  | invokestatic (cls method desc : String)
  | invokeinterface (cls method desc : String)
  | getfield (cls field desc : String)
  | ireturn | lreturn | areturn | dreturn | vreturn
  deriving Repr, Inhabited

structure JvmState where
  pc : Nat
  stack : List JvmVal
  locals : Nat → JvmVal

def setLocal (locals : Nat → JvmVal) (idx : Nat) (v : JvmVal) : Nat → JvmVal :=
  fun i => if i = idx then v else locals i

def initJvmState (slots : List (Nat × JvmVal)) : JvmState where
  pc := 0
  stack := []
  locals := slots.foldl (fun loc (idx, v) => setLocal loc idx v) (fun _ => .i32 0)

def stepInstr (instr : JvmInstr) (st : JvmState) : Option JvmState ⊕ Option JvmVal :=
  match instr with
  | .nop => .inl (some { st with pc := st.pc + 1 })
  | .invokestatic "kotlin/UInt" "constructor-impl" "(I)I"
  | .invokestatic "kotlin/ULong" "constructor-impl" "(J)J" =>
    .inl (some { st with pc := st.pc + 1 })
  | .invokestatic _ "f_Geometry_absFloat___closed__0" "()D" =>
    .inl (some { st with pc := st.pc + 1, stack := .f64 0.0 :: st.stack })
  | .iconst v => .inl (some { st with pc := st.pc + 1, stack := .i32 v :: st.stack })
  | .dconst0 => .inl (some { st with pc := st.pc + 1, stack := .f64 0.0 :: st.stack })
  | .dconst1 => .inl (some { st with pc := st.pc + 1, stack := .f64 1.0 :: st.stack })
  | .iload idx | .dload idx =>
    .inl (some { st with pc := st.pc + 1, stack := st.locals idx :: st.stack })
  | .istore idx | .dstore idx =>
    match st.stack with
    | v :: rest => .inl (some { pc := st.pc + 1, stack := rest, locals := setLocal st.locals idx v })
    | _ => .inr none
  | .ineg =>
    match st.stack with
    | a :: rest => .inl (some { st with pc := st.pc + 1, stack := .i32 (-a.asI32) :: rest })
    | _ => .inr none
  | .dneg =>
    match st.stack with
    | a :: rest => .inl (some { st with pc := st.pc + 1, stack := .f64 (-a.asF64) :: rest })
    | _ => .inr none
  | .dcmpg | .dcmpl =>
    match st.stack with
    | b :: a :: rest =>
      let res : UInt32 :=
        if a.asF64 < b.asF64 then 4294967295
        else if a.asF64 == b.asF64 then 0
        else 1
      .inl (some { st with pc := st.pc + 1, stack := .i32 res :: rest })
    | _ => .inr none
  | .goto target => .inl (some { st with pc := target })
  | .ireturn | .dreturn =>
    match st.stack with
    | v :: _ => .inr (some v)
    | _ => .inr none
  | _ => .inr none

def runJvm : Nat → List JvmInstr → JvmState → Option JvmVal
  | 0, _, _ => none
  | fuel + 1, prog, st =>
    match prog[st.pc]? with
    | none => none
    | some (.iflt target) =>
      match st.stack with
      | v :: rest =>
        JvmVal.ite (v.asI32.toBitVec.slt 0#32)
          (runJvm fuel prog { st with pc := target, stack := rest })
          (runJvm fuel prog { st with pc := st.pc + 1, stack := rest })
      | _ => none
    | some (.ifeq target) =>
      match st.stack with
      | v :: rest =>
        JvmVal.ite (v.asI32 == 0)
          (runJvm fuel prog { st with pc := target, stack := rest })
          (runJvm fuel prog { st with pc := st.pc + 1, stack := rest })
      | _ => none
    | some (.ifne target) =>
      match st.stack with
      | v :: rest =>
        JvmVal.ite (!(v.asI32 == 0))
          (runJvm fuel prog { st with pc := target, stack := rest })
          (runJvm fuel prog { st with pc := st.pc + 1, stack := rest })
      | _ => none
    | some instr =>
      match stepInstr instr st with
      | .inl (some st') => runJvm fuel prog st'
      | .inl none => none
      | .inr res => res

end Geometry.JvmVerification
