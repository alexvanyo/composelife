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

namespace Jvm

/-- Generic JVM bytecode instruction AST shared across verified ComposeLife modules. -/
inductive JvmInstr where
  | nop | dup | pop | swap | aconstNull | athrow
  | iconst (v : UInt32)
  | lconst (v : UInt64)
  | fconst (bits : UInt32)
  | dconst (bits : UInt64)
  | dconst0 | dconst1
  | ldcStr (s : String)
  | iload (idx : Nat)
  | lload (idx : Nat)
  | aload (idx : Nat)
  | fload (idx : Nat)
  | dload (idx : Nat)
  | istore (idx : Nat)
  | lstore (idx : Nat)
  | astore (idx : Nat)
  | fstore (idx : Nat)
  | dstore (idx : Nat)
  | iinc (idx : Nat) (delta : Int32)
  | iadd | isub | imul | idiv | irem | ineg | iand | ior | ixor | ishl | ishr | iushr
  | ladd | lsub | lmul | ldiv | lrem | land | lor | lxor | lshl | lshr | lushr
  | fadd | fsub | fmul | fdiv | fneg | fcmpg | fcmpl
  | dadd | dsub | dmul | ddiv | dneg | dcmpg | dcmpl
  | i2l | l2i | i2b | i2c | i2s | i2f | l2f | f2i | f2l | i2d | l2d | d2i | d2l | f2d | d2f | lcmp
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
  | if_icmpge (target : Nat)
  | if_icmpgt (target : Nat)
  | if_icmple (target : Nat)
  | if_acmpeq (target : Nat)
  | if_acmpne (target : Nat)
  | goto (target : Nat)
  | tableswitch (low : Int32) (targets : List Nat) (defaultTarget : Nat)
  | lookupswitch (cases : List (Int32 × Nat)) (defaultTarget : Nat)
  | newClass (cls : String)
  | newarray (elemType : String)
  | anewarray (cls : String)
  | arraylength
  | aaload | aastore
  | baload | bastore
  | caload | castore
  | saload | sastore
  | iaload | iastore
  | laload | lastore
  | faload | fastore
  | daload | dastore
  | checkcast (cls : String)
  | instanceof (cls : String)
  | invokevirtual (cls method desc : String)
  | invokespecial (cls method desc : String)
  | invokestatic (cls method desc : String)
  | invokeinterface (cls method desc : String)
  | invokedynamic (bsmKind bsmArg desc : String)
  | getfield (cls field desc : String)
  | putfield (cls field desc : String)
  | getstatic (cls field desc : String)
  | putstatic (cls field desc : String)
  | ireturn | lreturn | areturn | freturn | dreturn | vreturn
  deriving Repr, Inhabited

end Jvm
