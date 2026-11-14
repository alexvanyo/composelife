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
import Algorithm.Basic
import Algorithm.BitComputation
import Algorithm.MacroCell
import Algorithm.MacroCellHash
import Algorithm.HashLife
import Algorithm.FlatHashLife
import Algorithm.SerialCore
import Algorithm.Life105
import Algorithm.Life106
import Algorithm.Plaintext
import Algorithm.RLE

namespace Algorithm.JvmVerification

inductive ArenaU32Field where
  | l4Buckets | l4Next
  | cellNw | cellNe | cellSw | cellSe | cellStepRes | cellBuckets | cellNext
  | remapL4 | remapCell
  deriving DecidableEq, Repr, Inhabited

inductive ArenaU64Field where
  | l4Nw | l4Ne | l4Sw | l4Se | l4StepRes | cellPop
  deriving DecidableEq, Repr, Inhabited

inductive ArenaU8Field where
  | l4HasRes | cellLevel
  deriving DecidableEq, Repr, Inhabited

inductive JvmVal where
  | i32 (v : UInt32)
  | i64 (v : UInt64)
  | null
  | unit
  | str (s : String)
  | allocRef (cls : String)
  | boxedInt (v : UInt32)
  | boxedUInt (v : UInt32)
  | boxedByte (v : UInt32)
  | boxedUByte (v : UInt32)
  | boxedLong (v : UInt64)
  | boxedULong (v : UInt64)
  | pair (fst snd : JvmVal)
  | mc (m : Algorithm.MacroCell)
  | stepPrep (p : Algorithm.StepPreparation)
  | stepQuad (q : Algorithm.StepQuadrants)
  | hlState (s : Algorithm.HashLifeStepState)
  | pruneThresh (p : Algorithm.PruneThresholds)
  | stepBatch (b : Algorithm.StepBatchResult)
  | rleStatus (s : Algorithm.RLEStatus)
  | arenaRef (id : Nat)
  | arenaU32Ref (id : Nat) (field : ArenaU32Field)
  | arenaU64Ref (id : Nat) (field : ArenaU64Field)
  | arenaU8Ref (id : Nat) (field : ArenaU8Field)
  | u64Ref (id : Nat)
  | asciiRef (id : Nat)
  | byteArr (b : ByteArray)
  | u32Arr (xs : Array UInt32)
  | strArr (xs : Array String)
  | strGrowBuf (b : Algorithm.GrowBuf String)
  | dagWriter (w : Algorithm.DagWriter)
  | cellFrames (fs : List Algorithm.CellFrame)
  | fnU64ToU32 (f : UInt64 → UInt32)
  | fnMcToU64 (f : Algorithm.MacroCell → UInt64)
  | fnMcToMc (f : Algorithm.MacroCell → Algorithm.MacroCell)
  | fnMcToOptMc (f : Algorithm.MacroCell → Option Algorithm.MacroCell)
  | fnHlToHl (f : Algorithm.HashLifeStepState → Algorithm.HashLifeStepState)
  deriving Inhabited

def JvmVal.isNull : JvmVal → Bool
  | .null => true
  | _ => false

def JvmVal.asI32 : JvmVal → UInt32
  | .i32 v => v
  | .i64 v => v.toUInt32
  | _ => 0

def JvmVal.asI64 : JvmVal → UInt64
  | .i64 v => v
  | .i32 v => v.toUInt64
  | _ => 0

def JvmVal.ite (c : Bool) (t e : Option JvmVal) : Option JvmVal :=
  match t, e with
  | some (.i32 vt), some (.i32 ve) => some (.i32 (if c then vt else ve))
  | some (.i64 vt), some (.i64 ve) => some (.i64 (if c then vt else ve))
  | _, _ => if c then t else e

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
  arenas : List Algorithm.FlatHashLifeArena := []
  u64Arrays : List (Array UInt64) := []
  asciiArrays : List Algorithm.AsciiBytes := []

def setLocal (locals : Nat → JvmVal) (idx : Nat) (v : JvmVal) : Nat → JvmVal :=
  fun i => if i = idx then v else locals i

def initJvmState (slots : List (Nat × JvmVal))
    (arenas : List Algorithm.FlatHashLifeArena := [])
    (u64Arrays : List (Array UInt64) := [])
    (asciiArrays : List Algorithm.AsciiBytes := []) : JvmState where
  pc := 0
  stack := []
  locals := slots.foldl (fun loc (idx, v) => setLocal loc idx v) (fun _ => .i32 0)
  arenas := arenas
  u64Arrays := u64Arrays
  asciiArrays := asciiArrays

def getArenaU32 (a : Algorithm.FlatHashLifeArena) : ArenaU32Field → Array UInt32
  | .l4Buckets => a.l4Buckets
  | .l4Next => a.l4Next
  | .cellNw => a.cellNw
  | .cellNe => a.cellNe
  | .cellSw => a.cellSw
  | .cellSe => a.cellSe
  | .cellStepRes => a.cellStepRes
  | .cellBuckets => a.cellBuckets
  | .cellNext => a.cellNext
  | .remapL4 => a.remapL4
  | .remapCell => a.remapCell

def setArenaU32 (a : Algorithm.FlatHashLifeArena) (f : ArenaU32Field) (arr : Array UInt32) :
    Algorithm.FlatHashLifeArena :=
  match f with
  | .l4Buckets => { a with l4Buckets := arr }
  | .l4Next => { a with l4Next := arr }
  | .cellNw => { a with cellNw := arr }
  | .cellNe => { a with cellNe := arr }
  | .cellSw => { a with cellSw := arr }
  | .cellSe => { a with cellSe := arr }
  | .cellStepRes => { a with cellStepRes := arr }
  | .cellBuckets => { a with cellBuckets := arr }
  | .cellNext => { a with cellNext := arr }
  | .remapL4 => { a with remapL4 := arr }
  | .remapCell => { a with remapCell := arr }

def getArenaU64 (a : Algorithm.FlatHashLifeArena) : ArenaU64Field → Array UInt64
  | .l4Nw => a.l4Nw
  | .l4Ne => a.l4Ne
  | .l4Sw => a.l4Sw
  | .l4Se => a.l4Se
  | .l4StepRes => a.l4StepRes
  | .cellPop => a.cellPop

def setArenaU64 (a : Algorithm.FlatHashLifeArena) (f : ArenaU64Field) (arr : Array UInt64) :
    Algorithm.FlatHashLifeArena :=
  match f with
  | .l4Nw => { a with l4Nw := arr }
  | .l4Ne => { a with l4Ne := arr }
  | .l4Sw => { a with l4Sw := arr }
  | .l4Se => { a with l4Se := arr }
  | .l4StepRes => { a with l4StepRes := arr }
  | .cellPop => { a with cellPop := arr }

def getArenaU8 (a : Algorithm.FlatHashLifeArena) : ArenaU8Field → Array UInt8
  | .l4HasRes => a.l4HasRes
  | .cellLevel => a.cellLevel

def setArenaU8 (a : Algorithm.FlatHashLifeArena) (f : ArenaU8Field) (arr : Array UInt8) :
    Algorithm.FlatHashLifeArena :=
  match f with
  | .l4HasRes => { a with l4HasRes := arr }
  | .cellLevel => { a with cellLevel := arr }

def updateArena (st : JvmState) (id : Nat) (f : Algorithm.FlatHashLifeArena → Algorithm.FlatHashLifeArena) :
    Option JvmState :=
  match st.arenas[id]? with
  | some a => some { st with pc := st.pc + 1, arenas := st.arenas.set id (f a) }
  | none => none

def stripMangle : String → String
  | "f_Algorithm_AsciiBytes_replicate___redArg-LMfZGw8" => "f_Algorithm_AsciiBytes_replicate___redArg"
  | "f_Algorithm_AsciiBytes_set___redArg-snO9OKE" => "f_Algorithm_AsciiBytes_set___redArg"
  | "f_Algorithm_AsciiBytes_toStringRange-BltQuoY" => "f_Algorithm_AsciiBytes_toStringRange"
  | "f_Algorithm_DagWriter_addLeaf-2TYgG_w" => "f_Algorithm_DagWriter_addLeaf"
  | "f_Algorithm_DagWriter_addNode-omp52vY" => "f_Algorithm_DagWriter_addNode"
  | "f_Algorithm_FlatHashLifeArena_centeredHorizontal-BltQuoY" => "f_Algorithm_FlatHashLifeArena_centeredHorizontal"
  | "f_Algorithm_FlatHashLifeArena_centeredSubSubnode-Qn1smSk" => "f_Algorithm_FlatHashLifeArena_centeredSubSubnode"
  | "f_Algorithm_FlatHashLifeArena_centeredSubnode-Qn1smSk" => "f_Algorithm_FlatHashLifeArena_centeredSubnode"
  | "f_Algorithm_FlatHashLifeArena_centeredVertical-BltQuoY" => "f_Algorithm_FlatHashLifeArena_centeredVertical"
  | "f_Algorithm_FlatHashLifeArena_combineQuadrants-t447iZE" => "f_Algorithm_FlatHashLifeArena_combineQuadrants"
  | "f_Algorithm_FlatHashLifeArena_copyCellFromLoop-sA3nruY" => "f_Algorithm_FlatHashLifeArena_copyCellFromLoop"
  | "f_Algorithm_FlatHashLifeArena_copyL4From-BzPDsQc" => "f_Algorithm_FlatHashLifeArena_copyL4From"
  | "f_Algorithm_FlatHashLifeArena_expandFrame-BltQuoY" => "f_Algorithm_FlatHashLifeArena_expandFrame"
  | "f_Algorithm_FlatHashLifeArena_expandFrameIfNeeded-BltQuoY" => "f_Algorithm_FlatHashLifeArena_expandFrameIfNeeded"
  | "f_Algorithm_FlatHashLifeArena_initRemapCellLoop-BltQuoY" => "f_Algorithm_FlatHashLifeArena_initRemapCellLoop"
  | "f_Algorithm_FlatHashLifeArena_initRemapL4Loop-BltQuoY" => "f_Algorithm_FlatHashLifeArena_initRemapL4Loop"
  | "f_Algorithm_FlatHashLifeArena_quadrantNE-Qn1smSk" => "f_Algorithm_FlatHashLifeArena_quadrantNE"
  | "f_Algorithm_FlatHashLifeArena_quadrantNW-Qn1smSk" => "f_Algorithm_FlatHashLifeArena_quadrantNW"
  | "f_Algorithm_FlatHashLifeArena_quadrantSE-Qn1smSk" => "f_Algorithm_FlatHashLifeArena_quadrantSE"
  | "f_Algorithm_FlatHashLifeArena_quadrantSW-Qn1smSk" => "f_Algorithm_FlatHashLifeArena_quadrantSW"
  | "f_Algorithm_FlatHashLifeArena_setCellStepRes-BltQuoY" => "f_Algorithm_FlatHashLifeArena_setCellStepRes"
  | "f_Algorithm_FlatHashLifeArena_setL4StepRes-c82oGLE" => "f_Algorithm_FlatHashLifeArena_setL4StepRes"
  | "f_Algorithm_FlatHashLifeArena_setRemapCell-BltQuoY" => "f_Algorithm_FlatHashLifeArena_setRemapCell"
  | "f_Algorithm_FlatHashLifeArena_setRemapL4-BltQuoY" => "f_Algorithm_FlatHashLifeArena_setRemapL4"
  | "f_Algorithm_FlatHashLifeArena_stepCellSerialLoop-7IvYBaQ" => "f_Algorithm_FlatHashLifeArena_stepCellSerialLoop"
  | "f_Algorithm_FlatHashLifeArena_stepLevel4-Qn1smSk" => "f_Algorithm_FlatHashLifeArena_stepLevel4"
  | "f_Algorithm_FlatHashLifeArena_stepLevel5-Qn1smSk" => "f_Algorithm_FlatHashLifeArena_stepLevel5"
  | "f_Algorithm_U64Buf_push-3yFGk1Y" => "f_Algorithm_U64Buf_push"
  | "f_Algorithm_cellBounds-iqUxbHk" => "f_Algorithm_cellBounds"
  | "f_Algorithm_cellBox-QwZRm1k" => "f_Algorithm_cellBox"
  | "f_Algorithm_cellNodeHash-bB1yPJE" => "f_Algorithm_cellNodeHash"
  | "f_Algorithm_cellToLeafBitUInt-feOb9K0" => "f_Algorithm_cellToLeafBitUInt"
  | "f_Algorithm_centeredSubSubnodeSizeCell-Qn1smSk" => "f_Algorithm_centeredSubSubnodeSizeCell"
  | "f_Algorithm_computeLeafNextGen8x8BranchUInt-VKZWuLQ" => "f_Algorithm_computeLeafNextGen8x8BranchUInt"
  | "f_Algorithm_computeLeafNextGen8x8FastUInt-VKZWuLQ" => "f_Algorithm_computeLeafNextGen8x8FastUInt"
  | "f_Algorithm_computeLevel4NextGen16x16WithUInt___at___00Algorithm_computeLevel4NextGen16x16UInt_spec__0-2jIhpxI" =>
      "f_Algorithm_computeLevel4NextGen16x16WithUInt___at___00Algorithm_computeLevel4NextGen16x16UInt_spec__0"
  | "f_Algorithm_computeLevel4NextGen16x16WithUInt___at___00Algorithm_stepLevel4NodeWith_spec__0-VRmNplQ" =>
      "f_Algorithm_computeLevel4NextGen16x16WithUInt___at___00Algorithm_stepLevel4NodeWith_spec__0"
  | "f_Algorithm_computeNextGen4x4BitwiseUInt-WZ4Q5Ns" => "f_Algorithm_computeNextGen4x4BitwiseUInt"
  | "f_Algorithm_computePruneThresholds-fMEO4hA" => "f_Algorithm_computePruneThresholds"
  | "f_Algorithm_copyAscii-G2O0Dqo" => "f_Algorithm_copyAscii"
  | "f_Algorithm_copyCellTryStep-BzPDsQc" => "f_Algorithm_copyCellTryStep"
  | "f_Algorithm_copyU64-5j98i2w" => "f_Algorithm_copyU64"
  | "f_Algorithm_decimalLength-WZ4Q5Ns" => "f_Algorithm_decimalLength"
  | "f_Algorithm_decodeCharAt-BltQuoY" => "f_Algorithm_decodeCharAt"
  | "f_Algorithm_emptyAtHeight-WZ4Q5Ns" => "f_Algorithm_emptyAtHeight"
  | "f_Algorithm_emptyMacroCellUInt32_loop-t3GQkyU" => "f_Algorithm_emptyMacroCellUInt32_loop"
  | "f_Algorithm_fillGrid___redArg-RyWfpmY" => "f_Algorithm_fillGrid___redArg"
  | "f_Algorithm_findLastLeafX-8GdB7C8" => "f_Algorithm_findLastLeafX"
  | "f_Algorithm_formatCoordLine-feOb9K0" => "f_Algorithm_formatCoordLine"
  | "f_Algorithm_getCellStepRes-Qn1smSk" => "f_Algorithm_getCellStepRes"
  | "f_Algorithm_getRemapCell-Qn1smSk" => "f_Algorithm_getRemapCell"
  | "f_Algorithm_gridRows-G2O0Dqo" => "f_Algorithm_gridRows"
  | "f_Algorithm_leafContains-fMEO4hA" => "f_Algorithm_leafContains"
  | "f_Algorithm_leafRowMask-kBM7J_4" => "f_Algorithm_leafRowMask"
  | "f_Algorithm_level4Hash-2jIhpxI" => "f_Algorithm_level4Hash"
  | "f_Algorithm_makeLevel4Node-2jIhpxI" => "f_Algorithm_makeLevel4Node"
  | "f_Algorithm_serializeLife105_loop-KYAPeRw" => "f_Algorithm_serializeLife105_loop"
  | "f_Algorithm_serializeLife106_loop-B2nq9is" => "f_Algorithm_serializeLife106_loop"
  | "f_Algorithm_serializePlaintext-thtwfAY" => "f_Algorithm_serializePlaintext"
  | "f_Algorithm_serializeRLE-thtwfAY" => "f_Algorithm_serializeRLE"
  | "f_Algorithm_stepNGenerationsWith-OzbTU-A" => "f_Algorithm_stepNGenerationsWith"
  | "f_instBEqOption_beq___at___00Algorithm_findLastLeafRow_spec__0-1A3ddvw" =>
      "f_instBEqOption_beq___at___00Algorithm_findLastLeafRow_spec__0"
  | s => s

def coerceInI32 (v lo hi : UInt32) : UInt32 :=
  if v.toBitVec.slt lo.toBitVec then lo
  else if hi.toBitVec.slt v.toBitVec then hi
  else v

def nlz32 (x : UInt32) : UInt32 :=
  if x == 0 then 32 else 31 - x.log2

def checkInstanceOf (cls : String) (v : JvmVal) : Bool :=
  match cls, v with
  | "com/alexvanyo/composelife/model/MacroCell$CellNode", .mc (.cellNode ..) => true
  | "com/alexvanyo/composelife/model/MacroCell$Level4Node", .mc (.level4Node ..) => true
  | "java/lang/Byte", .boxedByte _ => true
  | "java/lang/Integer", .boxedInt _ => true
  | "java/lang/Long", .boxedLong _ => true
  | "kotlin/UInt", .boxedUInt _ => true
  | _, _ => false

def checkCast (cls : String) (v : JvmVal) : Option JvmVal :=
  match cls, v with
  | _, .null => some .null
  | "com/alexvanyo/composelife/model/HashLifeStepState", .hlState _ => some v
  | "com/alexvanyo/composelife/model/MacroCell", .mc _ => some v
  | "com/alexvanyo/composelife/model/MacroCell$CellNode", .mc (.cellNode ..) => some v
  | "com/alexvanyo/composelife/model/MacroCell$Level4Node", .mc (.level4Node ..) => some v
  | "com/alexvanyo/composelife/model/RLEStatus", .rleStatus _ => some v
  | "java/lang/Integer", .boxedInt _ => some v
  | "java/lang/Number", .boxedInt _ => some v
  | "java/lang/Number", .boxedByte _ => some v
  | "java/lang/Number", .boxedLong _ => some v
  | "kotlin/Pair", .pair _ _ => some v
  | "kotlin/UByte", .boxedUByte _ => some v
  | "kotlin/UInt", .boxedUInt _ => some v
  | "kotlin/ULong", .boxedULong _ => some v
  | "kotlin/jvm/functions/Function1", .fnU64ToU32 _ => some v
  | "kotlin/jvm/functions/Function1", .fnMcToU64 _ => some v
  | "kotlin/jvm/functions/Function1", .fnMcToMc _ => some v
  | "kotlin/jvm/functions/Function1", .fnMcToOptMc _ => some v
  | "kotlin/jvm/functions/Function1", .fnHlToHl _ => some v
  | _, _ => none

def boxCellBox (b : Int32 × Int32 × Int32 × Int32) : JvmVal :=
  .pair (.boxedInt b.1.toUInt32)
    (.pair (.boxedInt b.2.1.toUInt32)
      (.pair (.boxedInt b.2.2.1.toUInt32) (.boxedInt b.2.2.2.toUInt32)))

def stepInvokeVirtual (st : JvmState) (cls method _desc : String) : Option JvmState ⊕ Option JvmVal :=
  match cls, method, st.stack with
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "canCopySubgraphFrom", .arenaRef srcId :: .arenaRef dstId :: rest =>
    match st.arenas[dstId]?, st.arenas[srcId]? with
    | some dst, some src =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 (if dst.canCopySubgraphFrom src then 1 else 0) :: rest })
    | _, _ => .inr none
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getCellCount-pVg5ArA", .arenaRef id :: rest =>
    match st.arenas[id]? with
    | some a => .inl (some { st with pc := st.pc + 1, stack := .i32 a.cellCount :: rest })
    | none => .inr none
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getCellMask-pVg5ArA", .arenaRef id :: rest =>
    match st.arenas[id]? with
    | some a => .inl (some { st with pc := st.pc + 1, stack := .i32 a.cellMask :: rest })
    | none => .inr none
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getL4Count-pVg5ArA", .arenaRef id :: rest =>
    match st.arenas[id]? with
    | some a => .inl (some { st with pc := st.pc + 1, stack := .i32 a.l4Count :: rest })
    | none => .inr none
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getOverflow-w2LRezQ", .arenaRef id :: rest =>
    match st.arenas[id]? with
    | some a => .inl (some { st with pc := st.pc + 1, stack := .i32 a.overflow.toInt8.toInt32.toUInt32 :: rest })
    | none => .inr none
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "setOverflow-7apg3OU", v :: .arenaRef id :: rest =>
    .inl (updateArena { st with stack := rest } id (fun a => { a with overflow := v.asI32.toUInt8 }))
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getCellLevel-TcUX1vc", .arenaRef id :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .arenaU8Ref id .cellLevel :: rest })
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getL4HasRes-TcUX1vc", .arenaRef id :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .arenaU8Ref id .l4HasRes :: rest })
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getCellNe--hP7Qyg", .arenaRef id :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .arenaU32Ref id .cellNe :: rest })
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getCellNext--hP7Qyg", .arenaRef id :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .arenaU32Ref id .cellNext :: rest })
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getCellNw--hP7Qyg", .arenaRef id :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .arenaU32Ref id .cellNw :: rest })
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getCellSe--hP7Qyg", .arenaRef id :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .arenaU32Ref id .cellSe :: rest })
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getCellStepRes--hP7Qyg", .arenaRef id :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .arenaU32Ref id .cellStepRes :: rest })
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getCellSw--hP7Qyg", .arenaRef id :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .arenaU32Ref id .cellSw :: rest })
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getL4Next--hP7Qyg", .arenaRef id :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .arenaU32Ref id .l4Next :: rest })
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getRemapCell--hP7Qyg", .arenaRef id :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .arenaU32Ref id .remapCell :: rest })
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getRemapL4--hP7Qyg", .arenaRef id :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .arenaU32Ref id .remapL4 :: rest })
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getCellPop-Y2RjT0g", .arenaRef id :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .arenaU64Ref id .cellPop :: rest })
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getL4Nw-Y2RjT0g", .arenaRef id :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .arenaU64Ref id .l4Nw :: rest })
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getL4Ne-Y2RjT0g", .arenaRef id :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .arenaU64Ref id .l4Ne :: rest })
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getL4Sw-Y2RjT0g", .arenaRef id :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .arenaU64Ref id .l4Sw :: rest })
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getL4Se-Y2RjT0g", .arenaRef id :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .arenaU64Ref id .l4Se :: rest })
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getL4StepRes-Y2RjT0g", .arenaRef id :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .arenaU64Ref id .l4StepRes :: rest })
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "internCellNode-gt5aIGQ",
      se :: sw :: ne :: nw :: lvl :: .arenaRef id :: rest =>
    match st.arenas[id]? with
    | some a =>
      let (resId, a') := a.internCellNode lvl.asI32.toUInt8 nw.asI32 ne.asI32 sw.asI32 se.asI32
      .inl (some { st with pc := st.pc + 1, stack := .i32 resId :: rest, arenas := st.arenas.set id a' })
    | none => .inr none
  | "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "internLevel4-PT-fW9Q",
      se :: sw :: ne :: nw :: .arenaRef id :: rest =>
    match st.arenas[id]? with
    | some a =>
      let (resId, a') := a.internLevel4 nw.asI64 ne.asI64 sw.asI64 se.asI64
      .inl (some { st with pc := st.pc + 1, stack := .i32 resId :: rest, arenas := st.arenas.set id a' })
    | none => .inr none
  | "com/alexvanyo/composelife/model/HashLifeStepState", "getMacroCell", .hlState s :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .mc s.macroCell :: rest })
  | "com/alexvanyo/composelife/model/HashLifeStepState", "getOffsetX", .hlState s :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .i32 s.offsetX.toUInt32 :: rest })
  | "com/alexvanyo/composelife/model/HashLifeStepState", "getOffsetY", .hlState s :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .i32 s.offsetY.toUInt32 :: rest })
  | "com/alexvanyo/composelife/model/StepPreparation", "getMacroCell", .stepPrep p :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .mc p.macroCell :: rest })
  | "com/alexvanyo/composelife/model/StepPreparation", "getOffsetDelta", .stepPrep p :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .i32 p.offsetDelta.toUInt32 :: rest })
  | "com/alexvanyo/composelife/model/MacroCell", "cellHashCode-pVg5ArA", .mc m :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .i32 m.cellHashCode :: rest })
  | "com/alexvanyo/composelife/model/MacroCell", "level-pVg5ArA", .mc m :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .i32 m.level :: rest })
  | "com/alexvanyo/composelife/model/MacroCell", "size-s-VKNKU", .mc m :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .i64 m.size :: rest })
  | "com/alexvanyo/composelife/model/MacroCell$CellNode", "getHash-pVg5ArA", .mc (.cellNode h _ _ _ _) :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .i32 h :: rest })
  | "com/alexvanyo/composelife/model/MacroCell$CellNode", "getNw", .mc (.cellNode _ nw _ _ _) :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .mc nw :: rest })
  | "com/alexvanyo/composelife/model/MacroCell$CellNode", "getNe", .mc (.cellNode _ _ ne _ _) :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .mc ne :: rest })
  | "com/alexvanyo/composelife/model/MacroCell$CellNode", "getSw", .mc (.cellNode _ _ _ sw _) :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .mc sw :: rest })
  | "com/alexvanyo/composelife/model/MacroCell$CellNode", "getSe", .mc (.cellNode _ _ _ _ se) :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .mc se :: rest })
  | "com/alexvanyo/composelife/model/MacroCell$Level4Node", "getHash-pVg5ArA", .mc (.level4Node h _ _ _ _) :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .i32 h :: rest })
  | "com/alexvanyo/composelife/model/MacroCell$Level4Node", "getNw-s-VKNKU", .mc (.level4Node _ nw _ _ _) :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .i64 nw :: rest })
  | "com/alexvanyo/composelife/model/MacroCell$Level4Node", "getNe-s-VKNKU", .mc (.level4Node _ _ ne _ _) :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .i64 ne :: rest })
  | "com/alexvanyo/composelife/model/MacroCell$Level4Node", "getSw-s-VKNKU", .mc (.level4Node _ _ _ sw _) :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .i64 sw :: rest })
  | "com/alexvanyo/composelife/model/MacroCell$Level4Node", "getSe-s-VKNKU", .mc (.level4Node _ _ _ _ se) :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .i64 se :: rest })
  | "java/lang/Integer", "intValue", .boxedInt v :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .i32 v :: rest })
  | "java/lang/Number", "byteValue", .boxedByte v :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .i32 (UInt32.ofBitVec ((v.toBitVec.setWidth 8).signExtend 32)) :: rest })
  | "java/lang/Number", "intValue", .boxedInt v :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .i32 v :: rest })
  | "java/lang/Number", "longValue", .boxedLong v :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .i64 v :: rest })
  | "kotlin/Pair", "getFirst", .pair a _ :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := a :: rest })
  | "kotlin/Pair", "getSecond", .pair _ b :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := b :: rest })
  | "kotlin/UByte", "unbox-impl", .boxedUByte v :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .i32 v :: rest })
  | "kotlin/UInt", "unbox-impl", .boxedUInt v :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .i32 v :: rest })
  | "kotlin/ULong", "unbox-impl", .boxedULong v :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .i64 v :: rest })
  | _, _, _ => .inr none

def stepInvokeSpecial (st : JvmState) (cls method _desc : String) : Option JvmState ⊕ Option JvmVal :=
  match cls, method, st.stack with
  | "kotlin/NoWhenBranchMatchedException", "<init>", .allocRef "kotlin/NoWhenBranchMatchedException" :: .allocRef "kotlin/NoWhenBranchMatchedException" :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .allocRef "kotlin/NoWhenBranchMatchedException" :: rest })
  | "kotlin/Pair", "<init>", b :: a :: .allocRef "kotlin/Pair" :: .allocRef "kotlin/Pair" :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .pair a b :: rest })
  | "com/alexvanyo/composelife/model/HashLifeStepState", "<init>",
      .mc m :: oy :: ox :: .allocRef "com/alexvanyo/composelife/model/HashLifeStepState" :: .allocRef "com/alexvanyo/composelife/model/HashLifeStepState" :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .hlState ⟨ox.asI32.toInt32, oy.asI32.toInt32, m⟩ :: rest })
  | "com/alexvanyo/composelife/model/MacroCell$CellNode", "<init>",
      .null :: .mc se :: .mc sw :: .mc ne :: .mc nw :: h :: .allocRef "com/alexvanyo/composelife/model/MacroCell$CellNode" :: .allocRef "com/alexvanyo/composelife/model/MacroCell$CellNode" :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .mc (.cellNode h.asI32 nw ne sw se) :: rest })
  | "com/alexvanyo/composelife/model/MacroCell$Level4Node", "<init>",
      .null :: se :: sw :: ne :: nw :: h :: .allocRef "com/alexvanyo/composelife/model/MacroCell$Level4Node" :: .allocRef "com/alexvanyo/composelife/model/MacroCell$Level4Node" :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .mc (.level4Node h.asI32 nw.asI64 ne.asI64 sw.asI64 se.asI64) :: rest })
  | "com/alexvanyo/composelife/model/PruneThresholds", "<init>",
      .null :: leaf :: mac :: .allocRef "com/alexvanyo/composelife/model/PruneThresholds" :: .allocRef "com/alexvanyo/composelife/model/PruneThresholds" :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .pruneThresh ⟨mac.asI64, leaf.asI64⟩ :: rest })
  | "com/alexvanyo/composelife/model/RLEStatus$InvalidHeader", "<init>",
      .str s :: .allocRef "com/alexvanyo/composelife/model/RLEStatus$InvalidHeader" :: .allocRef "com/alexvanyo/composelife/model/RLEStatus$InvalidHeader" :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .rleStatus (.invalidHeader s) :: rest })
  | "com/alexvanyo/composelife/model/StepBatchResult", "<init>",
      .pruneThresh pt :: .hlState hs :: .allocRef "com/alexvanyo/composelife/model/StepBatchResult" :: .allocRef "com/alexvanyo/composelife/model/StepBatchResult" :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .stepBatch ⟨hs, pt⟩ :: rest })
  | "com/alexvanyo/composelife/model/StepPreparation", "<init>",
      .mc m :: delta :: .allocRef "com/alexvanyo/composelife/model/StepPreparation" :: .allocRef "com/alexvanyo/composelife/model/StepPreparation" :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .stepPrep ⟨delta.asI32.toInt32, m⟩ :: rest })
  | "com/alexvanyo/composelife/model/StepQuadrants", "<init>",
      .mc qse :: .mc qsw :: .mc qne :: .mc qnw :: .allocRef "com/alexvanyo/composelife/model/StepQuadrants" :: .allocRef "com/alexvanyo/composelife/model/StepQuadrants" :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .stepQuad ⟨qnw, qne, qsw, qse⟩ :: rest })
  | _, _, _ => .inr none

def stepInvokeStatic (st : JvmState) (cls method desc : String) : Option JvmState ⊕ Option JvmVal :=
  match cls, method, desc, st.stack with
  | "kotlin/UInt", "constructor-impl", "(I)I", _
  | "kotlin/ULong", "constructor-impl", "(J)J", _
  | "kotlin/UByte", "constructor-impl", "(B)B", _
  | "kotlin/ULongArray", "constructor-impl", "([J)[J", _ =>
    .inl (some { st with pc := st.pc + 1 })
  | "kotlin/UInt", "box-impl", "(I)Lkotlin/UInt;", v :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .boxedUInt v.asI32 :: rest })
  | "kotlin/ULong", "box-impl", "(J)Lkotlin/ULong;", v :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .boxedULong v.asI64 :: rest })
  | "kotlin/UByte", "box-impl", "(B)Lkotlin/UByte;", v :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .boxedUByte v.asI32 :: rest })
  | "java/lang/Integer", "valueOf", "(I)Ljava/lang/Integer;", v :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .boxedInt v.asI32 :: rest })
  | "java/lang/Integer", "compareUnsigned", "(II)I", b :: a :: rest =>
    let va := a.asI32
    let vb := b.asI32
    let res : UInt32 := if va == vb then 0 else if va < vb then 4294967295 else 1
    .inl (some { st with pc := st.pc + 1, stack := .i32 res :: rest })
  | "java/lang/Integer", "divideUnsigned", "(II)I", b :: a :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .i32 (a.asI32 / b.asI32) :: rest })
  | "java/lang/Integer", "numberOfLeadingZeros", "(I)I", a :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .i32 (nlz32 a.asI32) :: rest })
  | "java/lang/Long", "compareUnsigned", "(JJ)I", b :: a :: rest =>
    let va := a.asI64
    let vb := b.asI64
    let res : UInt32 := if va == vb then 0 else if va < vb then 4294967295 else 1
    .inl (some { st with pc := st.pc + 1, stack := .i32 res :: rest })
  | "java/lang/Math", "max", "(II)I", b :: a :: rest =>
    let va := a.asI32
    let vb := b.asI32
    let res : UInt32 := if va.toBitVec.slt vb.toBitVec then vb else va
    .inl (some { st with pc := st.pc + 1, stack := .i32 res :: rest })
  | "kotlin/jvm/internal/Intrinsics", "compare", "(II)I", b :: a :: rest =>
    let va := a.asI32
    let vb := b.asI32
    let res : UInt32 := if va == vb then 0 else if va.toBitVec.slt vb.toBitVec then 4294967295 else 1
    .inl (some { st with pc := st.pc + 1, stack := .i32 res :: rest })
  | "kotlin/jvm/internal/Intrinsics", "checkNotNull", "(Ljava/lang/Object;Ljava/lang/String;)V",
      _msg :: obj :: rest =>
    if obj.isNull then .inr none
    else .inl (some { st with pc := st.pc + 1, stack := rest })
  | "kotlin/jvm/internal/Intrinsics", "checkNotNullParameter", "(Ljava/lang/Object;Ljava/lang/String;)V",
      _msg :: obj :: rest =>
    if obj.isNull then .inr none
    else .inl (some { st with pc := st.pc + 1, stack := rest })
  | "kotlin/jvm/internal/TypeIntrinsics", "beforeCheckcastToFunctionOfArity", "(Ljava/lang/Object;I)Ljava/lang/Object;",
      _arity :: fnObj :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := fnObj :: rest })
  | "kotlin/ranges/RangesKt", "coerceIn", "(III)I", hi :: lo :: v :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .i32 (coerceInI32 v.asI32 lo.asI32 hi.asI32) :: rest })
  | "kotlin/UIntArray", "get-pVg5ArA", "([II)I", idx :: .arenaU32Ref id f :: rest =>
    match st.arenas[id]? with
    | some a =>
      let val := (getArenaU32 a f)[idx.asI32.toNat]!
      .inl (some { st with pc := st.pc + 1, stack := .i32 val :: rest })
    | none => .inr none
  | "kotlin/UIntArray", "getSize-impl", "([I)I", .arenaU32Ref id f :: rest =>
    match st.arenas[id]? with
    | some a =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 (getArenaU32 a f).size.toUInt32 :: rest })
    | none => .inr none
  | "kotlin/UIntArray", "set-VXSXFK8", "([III)V", val :: idx :: .arenaU32Ref id f :: rest =>
    .inl (updateArena { st with stack := rest } id (fun a => setArenaU32 a f ((getArenaU32 a f).set! idx.asI32.toNat val.asI32)))
  | "kotlin/UByteArray", "get-w2LRezQ", "([BI)B", idx :: .arenaU8Ref id f :: rest =>
    match st.arenas[id]? with
    | some a =>
      let val := (getArenaU8 a f)[idx.asI32.toNat]!
      .inl (some { st with pc := st.pc + 1, stack := .i32 val.toInt8.toInt32.toUInt32 :: rest })
    | none => .inr none
  | "kotlin/UByteArray", "set-VurrAj0", "([BIB)V", val :: idx :: .arenaU8Ref id f :: rest =>
    .inl (updateArena { st with stack := rest } id (fun a => setArenaU8 a f ((getArenaU8 a f).set! idx.asI32.toNat val.asI32.toUInt8)))
  | "kotlin/ULongArray", "constructor-impl", "(I)[J", sz :: rest =>
    let newId := st.u64Arrays.length
    let arr := Array.replicate sz.asI32.toNat 0
    .inl (some { st with pc := st.pc + 1, stack := .u64Ref newId :: rest, u64Arrays := st.u64Arrays ++ [arr] })
  | "kotlin/ULongArray", "get-s-VKNKU", "([JI)J", idx :: .arenaU64Ref id f :: rest =>
    match st.arenas[id]? with
    | some a =>
      let val := (getArenaU64 a f)[idx.asI32.toNat]!
      .inl (some { st with pc := st.pc + 1, stack := .i64 val :: rest })
    | none => .inr none
  | "kotlin/ULongArray", "get-s-VKNKU", "([JI)J", idx :: .u64Ref id :: rest =>
    match st.u64Arrays[id]? with
    | some arr =>
      .inl (some { st with pc := st.pc + 1, stack := .i64 (arr[idx.asI32.toNat]!) :: rest })
    | none => .inr none
  | "kotlin/ULongArray", "getSize-impl", "([J)I", .u64Ref id :: rest =>
    match st.u64Arrays[id]? with
    | some arr =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 arr.size.toUInt32 :: rest })
    | none => .inr none
  | "kotlin/ULongArray", "set-k8EXiF4", "([JIJ)V", val :: idx :: .u64Ref id :: rest =>
    match st.u64Arrays[id]? with
    | some arr =>
      .inl (some { st with pc := st.pc + 1, stack := rest, u64Arrays := st.u64Arrays.set id (arr.set! idx.asI32.toNat val.asI64) })
    | none => .inr none
  | "kotlin/ULongArray", "set-k8EXiF4", "([JIJ)V", val :: idx :: .arenaU64Ref id f :: rest =>
    .inl (updateArena { st with stack := rest } id (fun a => setArenaU64 a f ((getArenaU64 a f).set! idx.asI32.toNat val.asI64)))
  | "kotlin/collections/ArraysKt", "copyOfRange", "([JII)[J", e :: s :: .u64Ref id :: rest =>
    match st.u64Arrays[id]? with
    | some arr =>
      let newId := st.u64Arrays.length
      let sub := arr.extract s.asI32.toNat e.asI32.toNat
      .inl (some { st with pc := st.pc + 1, stack := .u64Ref newId :: rest, u64Arrays := st.u64Arrays ++ [sub] })
    | none => .inr none
  | _, _, _, _ =>
    let baseMethod := stripMangle method
    match baseMethod, st.stack with
    | "f_Algorithm_computeNextGen4x4BitwiseUInt", w :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 (Algorithm.computeNextGen4x4BitwiseUInt w.asI32) :: rest })
    | "f_Algorithm_computeLeafNextGen8x8FastUInt", w :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 (Algorithm.computeLeafNextGen8x8FastUInt w.asI64) :: rest })
    | "f_Algorithm_computeLeafNextGen8x8BranchUInt", w :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 (Algorithm.computeLeafNextGen8x8BranchUInt w.asI64) :: rest })
    | "f_Algorithm_cellToLeafBitUInt", y :: x :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 (Algorithm.cellToLeafBitUInt x.asI32 y.asI32) :: rest })
    | "f_Algorithm_leafContains", y :: x :: leaf :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 (if Algorithm.leafContains leaf.asI64 x.asI32 y.asI32 then 1 else 0) :: rest })
    | "f_Algorithm_cellNodeHash", se :: sw :: ne :: nw :: lvl :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 (Algorithm.cellNodeHash lvl.asI32 nw.asI32 ne.asI32 sw.asI32 se.asI32) :: rest })
    | "f_Algorithm_level4Hash", se :: sw :: ne :: nw :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 (Algorithm.level4Hash nw.asI64 ne.asI64 sw.asI64 se.asI64) :: rest })
    | "f_Algorithm_makeLevel4Node", se :: sw :: ne :: nw :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .mc (Algorithm.makeLevel4Node nw.asI64 ne.asI64 sw.asI64 se.asI64) :: rest })
    | "f_Algorithm_makeCellNode", .mc se :: .mc sw :: .mc ne :: .mc nw :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .mc (Algorithm.makeCellNode nw ne sw se) :: rest })
    | "getEMPTY_LEVEL_4", rest =>
      .inl (some { st with pc := st.pc + 1, stack := .mc Algorithm.emptyLevel4 :: rest })
    | "f_Algorithm_MacroCell_cellEquals", .mc other :: .mc m :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 (if Algorithm.MacroCell.cellEquals m other then 1 else 0) :: rest })
    | "f_Algorithm_centeredSubnode", .mc m :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .mc (Algorithm.centeredSubnode m) :: rest })
    | "f_Algorithm_centeredHorizontalSubnode", .mc e :: .mc w :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .mc (Algorithm.centeredHorizontalSubnode w e) :: rest })
    | "f_Algorithm_centeredVerticalSubnode", .mc s :: .mc n :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .mc (Algorithm.centeredVerticalSubnode n s) :: rest })
    | "f_Algorithm_centeredSubSubnodeFast", .mc m :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .mc (Algorithm.centeredSubSubnodeFast m) :: rest })
    | "f_Algorithm_centeredSubSubnodeSizeFast", .mc m :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i64 (Algorithm.centeredSubSubnodeSizeFast m) :: rest })
    | "f_Algorithm_expandCentered", .mc m :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .mc (Algorithm.expandCentered m) :: rest })
    | "f_Algorithm_needToExpand", .mc m :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 (if Algorithm.needToExpand m then 1 else 0) :: rest })
    | "f_Algorithm_prepareStep", .mc m :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .stepPrep (Algorithm.prepareStep m) :: rest })
    | "f_Algorithm_stepNGenerationsWith", .fnHlToHl fn :: .hlState hs :: step :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .hlState (Algorithm.stepNGenerationsWith step.asI32 hs fn) :: rest })
    | "f_Algorithm_computePruneThresholds", leafKeep :: macKeep :: gens :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .pruneThresh (Algorithm.computePruneThresholds gens.asI64 macKeep.asI32 leafKeep.asI32) :: rest })
    | "f_Algorithm_computeLevel4NextGen16x16WithUInt___at___00Algorithm_computeLevel4NextGen16x16UInt_spec__0",
        se :: sw :: ne :: nw :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i64 (Algorithm.computeLevel4NextGen16x16UInt nw.asI64 ne.asI64 sw.asI64 se.asI64) :: rest })
    | "f_Algorithm_computeLevel4NextGen16x16WithUInt___at___00Algorithm_stepLevel4NodeWith_spec__0",
        se :: sw :: ne :: nw :: .fnU64ToU32 fn :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i64 (Algorithm.computeLevel4NextGen16x16WithUInt nw.asI64 ne.asI64 sw.asI64 se.asI64 fn) :: rest })
    | "f_Algorithm_emptyAtHeight", h :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .mc (Algorithm.emptyAtHeight h.asI32) :: rest })
    | "f_Algorithm_cellsToMacroCell___closed__0", rest =>
      .inl (some { st with pc := st.pc + 1, stack := .mc (Algorithm.emptyAtHeight 1) :: rest })
    | "f_Algorithm_cellsToMacroCell___closed__1", rest =>
      .inl (some { st with pc := st.pc + 1, stack := .pair (.boxedULong 2147483648) (.mc (Algorithm.emptyAtHeight 1)) :: rest })
    | "f_Algorithm_importsAsEmpty", .mc m :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 (if Algorithm.importsAsEmpty m then 1 else 0) :: rest })
    | "f_Algorithm_leafRowMask", i :: b :: r :: t :: l :: y0 :: x0 :: leaf :: rest =>
      let res := Algorithm.leafRowMask leaf.asI64 x0.asI64.toInt64 y0.asI64.toInt64
        l.asI64.toInt64 t.asI64.toInt64 r.asI64.toInt64 b.asI64.toInt64 i.asI32
      .inl (some { st with pc := st.pc + 1, stack := .i64 res :: rest })
    | "f_List_isEmpty___redArg", .cellFrames fs :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 (if fs.isEmpty then 1 else 0) :: rest })
    | "f_Algorithm_emptyMacroCellUInt32_loop", .mc curNode :: curLevel :: level :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .mc (Algorithm.emptyMacroCellUInt32.loop level.asI32 curLevel.asI32 curNode) :: rest })
    | "f_Algorithm_findLastLeafX___closed__0", rest =>
      .inl (some { st with pc := st.pc + 1, stack := .boxedUInt 0 :: rest })
    | "f_Algorithm_findLastLeafX___closed__1", rest =>
      .inl (some { st with pc := st.pc + 1, stack := .boxedUInt 1 :: rest })
    | "f_Algorithm_findLastLeafX___closed__2", rest =>
      .inl (some { st with pc := st.pc + 1, stack := .boxedUInt 2 :: rest })
    | "f_Algorithm_findLastLeafX___closed__3", rest =>
      .inl (some { st with pc := st.pc + 1, stack := .boxedUInt 3 :: rest })
    | "f_Algorithm_findLastLeafX___closed__4", rest =>
      .inl (some { st with pc := st.pc + 1, stack := .boxedUInt 4 :: rest })
    | "f_Algorithm_findLastLeafX___closed__5", rest =>
      .inl (some { st with pc := st.pc + 1, stack := .boxedUInt 5 :: rest })
    | "f_Algorithm_findLastLeafX___closed__6", rest =>
      .inl (some { st with pc := st.pc + 1, stack := .boxedUInt 6 :: rest })
    | "f_Algorithm_findLastLeafX___closed__7", rest =>
      .inl (some { st with pc := st.pc + 1, stack := .boxedUInt 7 :: rest })
    | "f_Algorithm_findLastLeafX", y :: leaf :: rest =>
      let res := match Algorithm.findLastLeafX leaf.asI64 y.asI32 with
        | some v => .boxedUInt v
        | none => .null
      .inl (some { st with pc := st.pc + 1, stack := res :: rest })
    | "f_instBEqOption_beq___at___00Algorithm_findLastLeafRow_spec__0", b :: a :: rest =>
      let optOf : JvmVal → Option UInt32
        | .null => none
        | .boxedUInt v => some v
        | .boxedInt v => some v
        | _ => none
      .inl (some { st with pc := st.pc + 1, stack := .i32 (if optOf a == optOf b then 1 else 0) :: rest })
    | "f_Algorithm_DagWriter_addLeaf", leaf :: .dagWriter w :: rest =>
      let r := w.addLeaf leaf.asI64
      .inl (some { st with pc := st.pc + 1, stack := .pair (.boxedUInt r.1) (.dagWriter r.2) :: rest })
    | "f_Algorithm_DagWriter_addNode", se :: sw :: ne :: nw :: lvl :: .dagWriter w :: rest =>
      let r := w.addNode lvl.asI32 nw.asI32 ne.asI32 sw.asI32 se.asI32
      .inl (some { st with pc := st.pc + 1, stack := .pair (.boxedUInt r.1) (.dagWriter r.2) :: rest })
    | "f_Algorithm_FlatHashLifeArena_centeredHorizontal", eId :: wId :: .arenaRef id :: rest =>
      match st.arenas[id]? with
      | some a =>
        let (r, a') := a.centeredHorizontal wId.asI32 eId.asI32
        .inl (some { st with pc := st.pc + 1, stack := .i32 r :: rest, arenas := st.arenas.set id a' })
      | none => .inr none
    | "f_Algorithm_FlatHashLifeArena_centeredVertical", sId :: nId :: .arenaRef id :: rest =>
      match st.arenas[id]? with
      | some a =>
        let (r, a') := a.centeredVertical nId.asI32 sId.asI32
        .inl (some { st with pc := st.pc + 1, stack := .i32 r :: rest, arenas := st.arenas.set id a' })
      | none => .inr none
    | "f_Algorithm_FlatHashLifeArena_centeredSubnode", nodeId :: .arenaRef id :: rest =>
      match st.arenas[id]? with
      | some a =>
        let (r, a') := a.centeredSubnode nodeId.asI32
        .inl (some { st with pc := st.pc + 1, stack := .i32 r :: rest, arenas := st.arenas.set id a' })
      | none => .inr none
    | "f_Algorithm_FlatHashLifeArena_centeredSubSubnode", nodeId :: .arenaRef id :: rest =>
      match st.arenas[id]? with
      | some a =>
        let (r, a') := a.centeredSubSubnode nodeId.asI32
        .inl (some { st with pc := st.pc + 1, stack := .i32 r :: rest, arenas := st.arenas.set id a' })
      | none => .inr none
    | "f_Algorithm_centeredSubSubnodeSizeCell", nodeId :: .arenaRef id :: rest =>
      match st.arenas[id]? with
      | some a =>
        .inl (some { st with pc := st.pc + 1, stack := .i64 (Algorithm.centeredSubSubnodeSizeCell a nodeId.asI32) :: rest })
      | none => .inr none
    | "f_Algorithm_FlatHashLifeArena_quadrantNW", nodeId :: .arenaRef id :: rest =>
      match st.arenas[id]? with
      | some a =>
        let (r, a') := a.quadrantNW nodeId.asI32
        .inl (some { st with pc := st.pc + 1, stack := .i32 r :: rest, arenas := st.arenas.set id a' })
      | none => .inr none
    | "f_Algorithm_FlatHashLifeArena_quadrantNE", nodeId :: .arenaRef id :: rest =>
      match st.arenas[id]? with
      | some a =>
        let (r, a') := a.quadrantNE nodeId.asI32
        .inl (some { st with pc := st.pc + 1, stack := .i32 r :: rest, arenas := st.arenas.set id a' })
      | none => .inr none
    | "f_Algorithm_FlatHashLifeArena_quadrantSW", nodeId :: .arenaRef id :: rest =>
      match st.arenas[id]? with
      | some a =>
        let (r, a') := a.quadrantSW nodeId.asI32
        .inl (some { st with pc := st.pc + 1, stack := .i32 r :: rest, arenas := st.arenas.set id a' })
      | none => .inr none
    | "f_Algorithm_FlatHashLifeArena_quadrantSE", nodeId :: .arenaRef id :: rest =>
      match st.arenas[id]? with
      | some a =>
        let (r, a') := a.quadrantSE nodeId.asI32
        .inl (some { st with pc := st.pc + 1, stack := .i32 r :: rest, arenas := st.arenas.set id a' })
      | none => .inr none
    | "f_Algorithm_FlatHashLifeArena_combineQuadrants", se :: sw :: ne :: nw :: lvl :: nodeId :: .arenaRef id :: rest =>
      match st.arenas[id]? with
      | some a =>
        let (r, a') := a.combineQuadrants nodeId.asI32 lvl.asI32.toUInt8 nw.asI32 ne.asI32 sw.asI32 se.asI32
        .inl (some { st with pc := st.pc + 1, stack := .i32 r :: rest, arenas := st.arenas.set id a' })
      | none => .inr none
    | "f_Algorithm_FlatHashLifeArena_stepLevel4", l4Id :: .arenaRef id :: rest =>
      match st.arenas[id]? with
      | some a =>
        let (r, a') := a.stepLevel4 l4Id.asI32
        .inl (some { st with pc := st.pc + 1, stack := .i64 r :: rest, arenas := st.arenas.set id a' })
      | none => .inr none
    | "f_Algorithm_FlatHashLifeArena_stepLevel5", nodeId :: .arenaRef id :: rest =>
      match st.arenas[id]? with
      | some a =>
        let (r, a') := a.stepLevel5 nodeId.asI32
        .inl (some { st with pc := st.pc + 1, stack := .i32 r :: rest, arenas := st.arenas.set id a' })
      | none => .inr none
    | "f_Algorithm_getCellStepRes", nodeId :: .arenaRef id :: rest =>
      match st.arenas[id]? with
      | some a =>
        .inl (some { st with pc := st.pc + 1, stack := .i32 (Algorithm.getCellStepRes a nodeId.asI32) :: rest })
      | none => .inr none
    | "f_Algorithm_getRemapCell", nodeId :: .arenaRef id :: rest =>
      match st.arenas[id]? with
      | some a =>
        .inl (some { st with pc := st.pc + 1, stack := .i32 (Algorithm.getRemapCell a nodeId.asI32) :: rest })
      | none => .inr none
    | "f_Algorithm_FlatHashLifeArena_setRemapL4", val :: idx :: .arenaRef id :: rest =>
      .inl (updateArena { st with stack := rest } id (fun a => a.setRemapL4 idx.asI32 val.asI32))
    | "f_Algorithm_FlatHashLifeArena_setRemapCell", val :: idx :: .arenaRef id :: rest =>
      .inl (updateArena { st with stack := rest } id (fun a => a.setRemapCell idx.asI32 val.asI32))
    | "f_Algorithm_FlatHashLifeArena_setCellStepRes", val :: idx :: .arenaRef id :: rest =>
      .inl (updateArena { st with stack := rest } id (fun a => a.setCellStepRes idx.asI32 val.asI32))
    | "f_Algorithm_FlatHashLifeArena_setL4StepRes", val :: idx :: .arenaRef id :: rest =>
      .inl (updateArena { st with stack := rest } id (fun a => a.setL4StepRes idx.asI32 val.asI64))
    | "f_Algorithm_FlatHashLifeArena_setOverflow", .arenaRef id :: rest =>
      .inl (updateArena { st with stack := rest } id (fun a => a.setOverflow))
    | "f_Algorithm_FlatHashLifeArena_expandFrame", base :: nodeId :: .arenaRef id :: rest =>
      .inl (updateArena { st with stack := rest } id (fun a => a.expandFrame nodeId.asI32 base.asI32))
    | "f_Algorithm_FlatHashLifeArena_expandFrameIfNeeded", base :: nodeId :: .arenaRef id :: rest =>
      .inl (updateArena { st with stack := rest } id (fun a => a.expandFrameIfNeeded nodeId.asI32 base.asI32))
    | "f_Algorithm_FlatHashLifeArena_stepCellSerialLoop", fuel :: limit :: sp :: .arenaRef id :: rest =>
      .inl (updateArena { st with stack := rest } id (fun a => a.stepCellSerialLoop sp.asI32 limit.asI32 fuel.asI32))
    | "f_Algorithm_FlatHashLifeArena_initRemapL4Loop", limit :: i :: .arenaRef id :: rest =>
      .inl (updateArena { st with stack := rest } id (fun a => a.initRemapL4Loop i.asI32 limit.asI32))
    | "f_Algorithm_FlatHashLifeArena_initRemapCellLoop", limit :: i :: .arenaRef id :: rest =>
      .inl (updateArena { st with stack := rest } id (fun a => a.initRemapCellLoop i.asI32 limit.asI32))
    | "f_Algorithm_FlatHashLifeArena_copyL4From", copyMemos :: l4Id :: .arenaRef srcId :: .arenaRef dstId :: rest =>
      match st.arenas[dstId]?, st.arenas[srcId]? with
      | some dst, some src =>
        let (r, dst') := dst.copyL4From src l4Id.asI32 (copyMemos.asI32 != 0)
        .inl (some { st with pc := st.pc + 1, stack := .i32 r :: rest, arenas := st.arenas.set dstId dst' })
      | _, _ => .inr none
    | "f_Algorithm_copyCellTryStep", copyMemos :: cellId :: .arenaRef srcId :: .arenaRef dstId :: rest =>
      match st.arenas[dstId]?, st.arenas[srcId]? with
      | some dst, some src =>
        let (r, dst') := Algorithm.copyCellTryStep dst src cellId.asI32 (copyMemos.asI32 != 0)
        .inl (some { st with pc := st.pc + 1, stack := .i32 r :: rest, arenas := st.arenas.set dstId dst' })
      | _, _ => .inr none
    | "f_Algorithm_FlatHashLifeArena_copyCellFromLoop", fuel :: sp :: stackBase :: copyMemos :: .arenaRef srcId :: .arenaRef dstId :: rest =>
      match st.arenas[dstId]?, st.arenas[srcId]? with
      | some dst, some src =>
        let dst' := dst.copyCellFromLoop src (copyMemos.asI32 != 0) stackBase.asI32 sp.asI32 fuel.asI32
        .inl (some { st with pc := st.pc + 1, stack := rest, arenas := st.arenas.set dstId dst' })
      | _, _ => .inr none
    | "f_Algorithm_GrowBuf_empty___redArg", .null :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .strGrowBuf Algorithm.GrowBuf.empty :: rest })
    | "f_Algorithm_GrowBuf_push___redArg", .str s :: .strGrowBuf b :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .strGrowBuf (b.push s) :: rest })
    | "f_Algorithm_GrowBuf_toArray___redArg", .strGrowBuf b :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .strArr b.toArray :: rest })
    | "f_Algorithm_U64Buf_push", x :: .u64Ref id :: rest =>
      match st.u64Arrays[id]? with
      | some arr =>
        let pushed := Algorithm.U64Buf.push arr x.asI64
        let newId := st.u64Arrays.length
        .inl (some { st with pc := st.pc + 1, stack := .u64Ref newId :: rest, u64Arrays := st.u64Arrays ++ [pushed] })
      | none => .inr none
    | "f_Algorithm_copyU64", .u64Ref dstId :: i :: n :: .u64Ref srcId :: rest =>
      match st.u64Arrays[srcId]?, st.u64Arrays[dstId]? with
      | some src, some dst =>
        let dst' := Algorithm.copyU64 src n.asI32 i.asI32 dst
        .inl (some { st with pc := st.pc + 1, stack := rest, u64Arrays := st.u64Arrays.set dstId dst' })
      | _, _ => .inr none
    | "f_Algorithm_AsciiBytes_replicate___redArg", v :: n :: rest =>
      let b := v.asI32.toUInt8
      if hb : b < 128 then
        let newId := st.asciiArrays.length
        let arr := Algorithm.AsciiBytes.replicate n.asI32 b hb
        .inl (some { st with pc := st.pc + 1, stack := .asciiRef newId :: rest, asciiArrays := st.asciiArrays ++ [arr] })
      else .inr none
    | "f_Algorithm_AsciiBytes_set___redArg", v :: i :: .asciiRef id :: rest =>
      let b := v.asI32.toUInt8
      match st.asciiArrays[id]? with
      | some g =>
        if hb : b < 128 then
          .inl (some { st with pc := st.pc + 1, stack := rest, asciiArrays := st.asciiArrays.set id (g.set i.asI32 b hb) })
        else .inr none
      | none => .inr none
    | "f_Algorithm_AsciiBytes_toStringRange", e :: s :: .asciiRef id :: rest =>
      match st.asciiArrays[id]? with
      | some g =>
        .inl (some { st with pc := st.pc + 1, stack := .str (g.toStringRange s.asI32 e.asI32) :: rest })
      | none => .inr none
    | "f_Algorithm_fillGrid___redArg", .asciiRef gId :: limit :: i :: alive :: h :: w :: minY :: minX :: .u64Ref cId :: rest =>
      let ab := alive.asI32.toUInt8
      match st.u64Arrays[cId]?, st.asciiArrays[gId]? with
      | some cells, some g =>
        if ha : ab < 128 then
          let g' := Algorithm.fillGrid cells minX.asI32.toInt32 minY.asI32.toInt32 w.asI32 h.asI32 ab ha i.asI32 limit.asI32 g
          .inl (some { st with pc := st.pc + 1, stack := rest, asciiArrays := st.asciiArrays.set gId g' })
        else .inr none
      | _, _ => .inr none
    | "f_Algorithm_gridRows", .strGrowBuf acc :: r :: h :: w :: .asciiRef gId :: rest =>
      match st.asciiArrays[gId]? with
      | some g =>
        .inl (some { st with pc := st.pc + 1, stack := .strGrowBuf (Algorithm.gridRows g w.asI32 h.asI32 r.asI32 acc) :: rest })
      | none => .inr none
    | "f_Algorithm_copyAscii", .asciiRef gId :: k :: n :: s :: .byteArr bytes :: rest =>
      match st.asciiArrays[gId]? with
      | some g =>
        let g' := Algorithm.copyAscii bytes s.asI32 n.asI32 k.asI32 g
        .inl (some { st with pc := st.pc + 1, stack := rest, asciiArrays := st.asciiArrays.set gId g' })
      | none => .inr none
    | "f_Algorithm_formatBlockHeader", y :: x :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .str (Algorithm.formatBlockHeader x.asI32.toInt32 y.asI32.toInt32) :: rest })
    | "f_Algorithm_formatCoordLine", y :: x :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .str (Algorithm.formatCoordLine x.asI32 y.asI32) :: rest })
    | "f_Algorithm_serializeLife105___closed__0", rest =>
      .inl (some { st with pc := st.pc + 1, stack := .strArr #[] :: rest })
    | "f_Algorithm_serializeLife105_loop", .strGrowBuf acc :: j :: .strArr block :: .u64Ref cId :: fuel :: rest =>
      match st.u64Arrays[cId]? with
      | some cells =>
        .inl (some { st with pc := st.pc + 1, stack := .strGrowBuf (Algorithm.serializeLife105.loop fuel.asI32 cells block j.asI32 acc) :: rest })
      | none => .inr none
    | "f_Algorithm_serializeLife106_loop", .strGrowBuf acc :: limit :: i :: .u64Ref cId :: rest =>
      match st.u64Arrays[cId]? with
      | some cells =>
        .inl (some { st with pc := st.pc + 1, stack := .strGrowBuf (Algorithm.serializeLife106.loop cells i.asI32 limit.asI32 acc) :: rest })
      | none => .inr none
    | "f_Algorithm_cellBounds", maxY :: minY :: maxX :: minX :: limit :: i :: .u64Ref cId :: rest =>
      match st.u64Arrays[cId]? with
      | some cells =>
        let b := Algorithm.cellBounds cells i.asI32 limit.asI32 minX.asI32.toInt32 maxX.asI32.toInt32 minY.asI32.toInt32 maxY.asI32.toInt32
        .inl (some { st with pc := st.pc + 1, stack := boxCellBox b :: rest })
      | none => .inr none
    | "f_Algorithm_cellBox", .u64Ref cId :: rest =>
      match st.u64Arrays[cId]? with
      | some cells =>
        .inl (some { st with pc := st.pc + 1, stack := boxCellBox (Algorithm.cellBox cells) :: rest })
      | none => .inr none
    | "f_Algorithm_decodeCharAt", limit :: p :: .byteArr bytes :: rest =>
      let r := Algorithm.decodeCharAt bytes p.asI32 limit.asI32
      .inl (some { st with pc := st.pc + 1, stack := .pair (.boxedUInt r.1) (.boxedUInt r.2) :: rest })
    | "f_Algorithm_serializePlaintext___closed__1", rest =>
      .inl (some { st with pc := st.pc + 1, stack := .strArr #["."] :: rest })
    | "f_Algorithm_serializePlaintext", maxY :: minY :: maxX :: minX :: .u64Ref cId :: rest =>
      match st.u64Arrays[cId]? with
      | some cells =>
        .inl (some { st with pc := st.pc + 1, stack := .strArr (Algorithm.serializePlaintext cells minX.asI32.toInt32 maxX.asI32.toInt32 minY.asI32.toInt32 maxY.asI32.toInt32) :: rest })
      | none => .inr none
    | "f_Algorithm_decimalLength", n :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 (Algorithm.decimalLength n.asI32) :: rest })
    | "f_Algorithm_serializeRLE", maxY :: minY :: maxX :: minX :: .u64Ref cId :: rest =>
      match st.u64Arrays[cId]? with
      | some cells =>
        .inl (some { st with pc := st.pc + 1, stack := .strArr (Algorithm.serializeRLE cells minX.asI32.toInt32 maxX.asI32.toInt32 minY.asI32.toInt32 maxY.asI32.toInt32) :: rest })
      | none => .inr none
    | _, _ => .inr none

def stepInvokeInterface (st : JvmState) (cls method _desc : String) : Option JvmState ⊕ Option JvmVal :=
  match cls, method, st.stack with
  | "kotlin/jvm/functions/Function1", "invoke", arg :: fn :: rest =>
    match fn, arg with
    | .fnU64ToU32 f, .boxedULong v =>
      .inl (some { st with pc := st.pc + 1, stack := .boxedUInt (f v) :: rest })
    | .fnU64ToU32 f, .i64 v =>
      .inl (some { st with pc := st.pc + 1, stack := .boxedUInt (f v) :: rest })
    | .fnMcToU64 f, .mc m =>
      .inl (some { st with pc := st.pc + 1, stack := .boxedULong (f m) :: rest })
    | .fnMcToMc f, .mc m =>
      .inl (some { st with pc := st.pc + 1, stack := .mc (f m) :: rest })
    | .fnMcToOptMc f, .mc m =>
      let res := match f m with | some c => .mc c | none => .null
      .inl (some { st with pc := st.pc + 1, stack := res :: rest })
    | .fnHlToHl f, .hlState hs =>
      .inl (some { st with pc := st.pc + 1, stack := .hlState (f hs) :: rest })
    | _, _ => .inr none
  | _, _, _ => .inr none

def stepInstr (instr : JvmInstr) (st : JvmState) : Option JvmState ⊕ Option JvmVal :=
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
  | .ldcStr s => .inl (some { st with pc := st.pc + 1, stack := .str s :: st.stack })
  | .iload idx | .lload idx | .aload idx =>
    .inl (some { st with pc := st.pc + 1, stack := st.locals idx :: st.stack })
  | .istore idx | .lstore idx | .astore idx =>
    match st.stack with
    | v :: rest => .inl (some { st with pc := st.pc + 1, stack := rest, locals := setLocal st.locals idx v })
    | _ => .inr none
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
  | .newClass cls => .inl (some { st with pc := st.pc + 1, stack := .allocRef cls :: st.stack })
  | .checkcast cls =>
    match st.stack with
    | v :: rest =>
      match checkCast cls v with
      | some v' => .inl (some { st with pc := st.pc + 1, stack := v' :: rest })
      | none => .inr none
    | _ => .inr none
  | .instanceof cls =>
    match st.stack with
    | v :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 (if checkInstanceOf cls v then 1 else 0) :: rest })
    | _ => .inr none
  | .invokevirtual cls method desc => stepInvokeVirtual st cls method desc
  | .invokespecial cls method desc => stepInvokeSpecial st cls method desc
  | .invokestatic cls method desc => stepInvokeStatic st cls method desc
  | .invokeinterface cls method desc => stepInvokeInterface st cls method desc
  | .ireturn | .lreturn | .areturn =>
    match st.stack with
    | v :: _ => .inr (some v)
    | _ => .inr none
  | .vreturn => .inr (some .unit)
  | _ => .inr none

def runJvm : Nat → List JvmInstr → JvmState → Option JvmVal
  | 0, _, _ => none
  | fuel + 1, prog, st =>
    match prog[st.pc]? with
    | none => none
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
    | some (.iflt target) =>
      match st.stack with
      | v :: rest =>
        JvmVal.ite (v.asI32.toBitVec.slt 0#32)
          (runJvm fuel prog { st with pc := target, stack := rest })
          (runJvm fuel prog { st with pc := st.pc + 1, stack := rest })
      | _ => none
    | some (.ifle target) =>
      match st.stack with
      | v :: rest =>
        JvmVal.ite (v.asI32.toBitVec.sle 0#32)
          (runJvm fuel prog { st with pc := target, stack := rest })
          (runJvm fuel prog { st with pc := st.pc + 1, stack := rest })
      | _ => none
    | some (.ifgt target) =>
      match st.stack with
      | v :: rest =>
        JvmVal.ite ((0#32).slt v.asI32.toBitVec)
          (runJvm fuel prog { st with pc := target, stack := rest })
          (runJvm fuel prog { st with pc := st.pc + 1, stack := rest })
      | _ => none
    | some (.ifge target) =>
      match st.stack with
      | v :: rest =>
        JvmVal.ite ((0#32).sle v.asI32.toBitVec)
          (runJvm fuel prog { st with pc := target, stack := rest })
          (runJvm fuel prog { st with pc := st.pc + 1, stack := rest })
      | _ => none
    | some (.ifnull target) =>
      match st.stack with
      | v :: rest =>
        if v.isNull then runJvm fuel prog { st with pc := target, stack := rest }
        else runJvm fuel prog { st with pc := st.pc + 1, stack := rest }
      | _ => none
    | some (.ifnonnull target) =>
      match st.stack with
      | v :: rest =>
        if !v.isNull then runJvm fuel prog { st with pc := target, stack := rest }
        else runJvm fuel prog { st with pc := st.pc + 1, stack := rest }
      | _ => none
    | some (.if_icmpeq target) =>
      match st.stack with
      | b :: a :: rest =>
        JvmVal.ite (a.asI32 == b.asI32)
          (runJvm fuel prog { st with pc := target, stack := rest })
          (runJvm fuel prog { st with pc := st.pc + 1, stack := rest })
      | _ => none
    | some (.if_icmpne target) =>
      match st.stack with
      | b :: a :: rest =>
        JvmVal.ite (!(a.asI32 == b.asI32))
          (runJvm fuel prog { st with pc := target, stack := rest })
          (runJvm fuel prog { st with pc := st.pc + 1, stack := rest })
      | _ => none
    | some (.if_icmplt target) =>
      match st.stack with
      | b :: a :: rest =>
        JvmVal.ite (a.asI32.toBitVec.slt b.asI32.toBitVec)
          (runJvm fuel prog { st with pc := target, stack := rest })
          (runJvm fuel prog { st with pc := st.pc + 1, stack := rest })
      | _ => none
    | some instr =>
      match stepInstr instr st with
      | .inl (some st') => runJvm fuel prog st'
      | .inl none => none
      | .inr res => res

def runJvmRes : Nat → List JvmInstr → JvmState → Option (JvmVal × JvmState)
  | 0, _, _ => none
  | fuel + 1, prog, st =>
    match prog[st.pc]? with
    | none => none
    | some (.ifeq target) =>
      match st.stack with
      | v :: rest =>
        if v.asI32 == 0 then runJvmRes fuel prog { st with pc := target, stack := rest }
        else runJvmRes fuel prog { st with pc := st.pc + 1, stack := rest }
      | _ => none
    | some (.ifne target) =>
      match st.stack with
      | v :: rest =>
        if !(v.asI32 == 0) then runJvmRes fuel prog { st with pc := target, stack := rest }
        else runJvmRes fuel prog { st with pc := st.pc + 1, stack := rest }
      | _ => none
    | some (.iflt target) =>
      match st.stack with
      | v :: rest =>
        if v.asI32.toBitVec.slt 0#32 then runJvmRes fuel prog { st with pc := target, stack := rest }
        else runJvmRes fuel prog { st with pc := st.pc + 1, stack := rest }
      | _ => none
    | some (.ifle target) =>
      match st.stack with
      | v :: rest =>
        if v.asI32.toBitVec.sle 0#32 then runJvmRes fuel prog { st with pc := target, stack := rest }
        else runJvmRes fuel prog { st with pc := st.pc + 1, stack := rest }
      | _ => none
    | some (.ifgt target) =>
      match st.stack with
      | v :: rest =>
        if (0#32).slt v.asI32.toBitVec then runJvmRes fuel prog { st with pc := target, stack := rest }
        else runJvmRes fuel prog { st with pc := st.pc + 1, stack := rest }
      | _ => none
    | some (.ifge target) =>
      match st.stack with
      | v :: rest =>
        if (0#32).sle v.asI32.toBitVec then runJvmRes fuel prog { st with pc := target, stack := rest }
        else runJvmRes fuel prog { st with pc := st.pc + 1, stack := rest }
      | _ => none
    | some (.ifnull target) =>
      match st.stack with
      | v :: rest =>
        if v.isNull then runJvmRes fuel prog { st with pc := target, stack := rest }
        else runJvmRes fuel prog { st with pc := st.pc + 1, stack := rest }
      | _ => none
    | some (.ifnonnull target) =>
      match st.stack with
      | v :: rest =>
        if !v.isNull then runJvmRes fuel prog { st with pc := target, stack := rest }
        else runJvmRes fuel prog { st with pc := st.pc + 1, stack := rest }
      | _ => none
    | some (.if_icmpeq target) =>
      match st.stack with
      | b :: a :: rest =>
        if a.asI32 == b.asI32 then runJvmRes fuel prog { st with pc := target, stack := rest }
        else runJvmRes fuel prog { st with pc := st.pc + 1, stack := rest }
      | _ => none
    | some (.if_icmpne target) =>
      match st.stack with
      | b :: a :: rest =>
        if !(a.asI32 == b.asI32) then runJvmRes fuel prog { st with pc := target, stack := rest }
        else runJvmRes fuel prog { st with pc := st.pc + 1, stack := rest }
      | _ => none
    | some (.if_icmplt target) =>
      match st.stack with
      | b :: a :: rest =>
        if a.asI32.toBitVec.slt b.asI32.toBitVec then runJvmRes fuel prog { st with pc := target, stack := rest }
        else runJvmRes fuel prog { st with pc := st.pc + 1, stack := rest }
      | _ => none
    | some instr =>
      match stepInstr instr st with
      | .inl (some st') => runJvmRes fuel prog st'
      | .inl none => none
      | .inr (some res) => some (res, st)
      | .inr none => none

end Algorithm.JvmVerification
